# Heap Expansion for the Verified Generational GC

The verified generational collector currently treats the major heap as one
fixed-size byte array. That made the first verified runtime integration
tractable, but it also explains the benchmark behavior seen with
minimum-to-run heap settings: when the configured major heap is just large
enough, promotion and major allocation repeatedly exhaust the free list, forcing
full collections much more often than stock OCaml.

This document reviews how stock OCaml 4.14 expands its major heap, how the
current verified collector represents heap memory and OCaml values, and what has
to change to support expansion without weakening the proofs. The recommendation
is to add a chunked, non-moving major heap. Existing major objects should keep
their addresses forever; expansion should only add fresh chunks and splice their
free space into the verified free list.

## Recommendation

Use a chunked, non-moving major heap, modeled after stock OCaml's heap chunks.
Do not resize or move one contiguous major array.

The key design choice is address stability. OCaml values store object addresses
directly in object fields, roots, stack slots, closures, and the remembered
slots scanned by minor collection. The current proofs also reason about object
identity by address. A moving or reallocating major heap would require a global
update of every major pointer, static root, minor root, forwarding target, and
remembered slot, plus a new proof that all aliases were rewritten correctly.
That would be a much larger collector redesign.

Instead, expansion should allocate a fresh major chunk, register that chunk with
the OCaml runtime's address classifier, initialize the chunk as one or more blue
free blocks, and insert those blocks into the verified free list. Existing
objects and roots are unchanged. The proof story then becomes an extension
theorem: adding a disjoint all-blue chunk preserves the live heap and only
increases available free space.

## Stock OCaml 4.14 model

Stock OCaml's major heap is already chunked.

- `caml_alloc_for_heap` allocates a page-rounded chunk and stores chunk metadata
  just before the heap payload.
- `caml_add_to_heap` registers the chunk's pages in the runtime page table with
  `In_heap`, inserts the chunk into the sorted `caml_heap_start` chain, and
  updates `stat_heap_wsz`, `stat_top_heap_wsz`, and `stat_heap_chunks`.
- `expand_heap` is called when `caml_fl_allocate` cannot satisfy a major
  allocation. It requests at least the allocation size plus `percent_free`
  overhead, clips the request by `caml_clip_heap_chunk_wsz`, initializes the
  chunk as one or more blue blocks, adds the chunk to the heap, and then lets
  `caml_fl_add_blocks` insert those blue blocks into the free-list structure.
- `caml_clip_heap_chunk_wsz` enforces both `Heap_chunk_min` and the configured
  major-heap increment. If `major_heap_increment > 1000`, it is interpreted as a
  word count; otherwise it is interpreted as a percentage of the current major
  heap.
- `Is_in_heap` is page-table based, not interval based. Adding a chunk updates
  the page table so pointer classification works for non-contiguous major
  addresses.
- Stock OCaml can also shrink chunks during compaction, but that is separable
  from expansion. The verified collector should first support grow-only chunks.

The current verified integration replaces most of this policy with a fixed heap
buffer and verified allocation from one free-list model. The expansion work
should restore the stock shape at the boundary while keeping allocation,
promotion, sweep, and coalescing inside the verified model.

## Current verified representation

The current F*/Pulse model has a deliberately simple heap abstraction:

- `GC.Spec.Base.heap_size` is one abstract byte length, and
  `GC.Spec.Base.heap` is a sequence of bytes whose length is exactly
  `heap_size`.
- `hp_addr` is a word-aligned offset below `heap_size`; `obj_addr` is an
  `hp_addr` at least one word past the header base.
- `GC.Spec.Fields.objects zero_addr g` enumerates the heap by reading headers
  linearly from `zero_addr` to `heap_size`. The model assumes a single dense
  object/free-block layout with no gaps.
- `GC.Spec.Fields.is_pointer` and related predicates classify major pointers by
  the single range `[zero_addr + mword, heap_size)`.
- The allocator, sweep, coalescing, major-GC invariants, and generational
  `major_heap_shape` are all parameterized by this single heap and use
  `heap_size / mword` as traversal or free-list fuel.
- The generational layer keeps the minor heap as a separate fixed array. It
  distinguishes minor offsets from major addresses by configuration facts such
  as `zero_addr >= minor_heap_size`.
- Promotion calls `GC.Spec.Allocator.alloc_spec major fp wosize`. If the free
  list cannot satisfy the request, the current specification returns `obj_out =
  0UL`, and the runtime reports out of memory rather than growing the heap.

The runtime bridge mirrors this fixed model. `alloc_gen.c` keeps a single
`major_heap` buffer and `major_heap_size_words`, initializes it as one blue
block, calls extracted verified allocation and collection code, and uses
whole-heap scans for major roots and remembered minor references. The
`runtime_gen.patch` redirects OCaml allocation paths to the verified bridge and
keeps runtime statistics in sync with the fixed verified heap.

## Design alternatives

| Design | Assessment |
| --- | --- |
| Reallocate one larger contiguous heap | Not recommended. Existing OCaml values are raw addresses; moving the base invalidates roots and fields unless every pointer is found and rewritten. It also breaks current address-identity proofs. |
| Reserve a huge virtual range and commit pages on demand | Possible but less portable and harder to align with stock OCaml. It preserves simple range checks only if the full reserved range is treated as the heap, but proofs would still need committed/uncommitted memory and page-touch invariants. |
| Let C manage expansion outside the verified model | Too weak. C could append free blocks, but the verified allocator and collector would not know the expanded heap shape, so the main correctness theorem would no longer cover major allocation after expansion. |
| Verified chunked major heap | Recommended. It preserves stable addresses, matches stock OCaml's chunked heap design, and admits a clean proof that fresh all-blue chunks do not affect existing live objects. |

## Proposed verified model

Introduce an explicit major-heap chunk model instead of one global byte
sequence.

```fstar
type chunk_id = nat

type heap_chunk = {
  base : U64.t;
  size : nat;  // bytes, word-aligned, >= 16
  bytes : seq U8.t { Seq.length bytes == size };
}

type major_heap = {
  chunks : seq heap_chunk;
}
```

Core invariants:

1. Chunk bases and sizes are word-aligned.
2. Each chunk has room for at least a header and one field.
3. Chunk address intervals are disjoint.
4. No chunk interval wraps around `2^64`.
5. Existing chunks are stable under expansion: their bases, sizes, and bytes are
   unchanged.
6. A valid major address belongs to exactly one chunk.
7. Reading or writing a word is defined only when the full word lies in one
   chunk.
8. Objects are dense within each chunk, but not across chunk boundaries.

This keeps the important local property from the current model: inside a chunk,
objects and free blocks are still a dense OCaml layout. Only the top-level heap
changes from "one dense interval" to "a sequence of dense intervals".

Useful derived definitions:

- `chunk_contains_addr : heap_chunk -> U64.t -> bool`
- `lookup_chunk : major_heap -> U64.t -> option chunk_id`
- `hp_addr_in : major_heap -> U64.t -> prop`
- `obj_addr_in : major_heap -> U64.t -> prop`
- `read_word_at : major_heap -> a:U64.t{hp_addr_in major a} -> U64.t`
- `write_word_at : major_heap -> a:U64.t{hp_addr_in major a} -> U64.t -> major_heap`
- `objects_in_chunk : heap_chunk -> seq obj_addr`
- `objects : major_heap -> seq obj_addr`, concatenating chunk-local object lists
- `is_major_pointer : major_heap -> U64.t -> bool`

The existing `heap` API can be preserved temporarily by adding a compatibility
layer for single-chunk heaps. That allows most refactoring to be staged: first
make the major collector polymorphic over a heap operations interface, then
instantiate it with single-chunk and chunked heaps.

## Free-list and sweep strategy

The free list can remain a global list of blue object addresses threaded through
field 0. Expansion adds one or more blue objects from the new chunk to the same
list.

For the first implementation, the simplest verified strategy is:

1. Allocate a new chunk whose payload is a dense sequence of blue free blocks.
   If the chunk is too large for one OCaml block header, split it into multiple
   maximum-size blue blocks, just as stock OCaml does.
2. Link those blue blocks together through their first fields.
3. Append or prepend that chain to the existing free list.
4. Prove `fl_valid`, `fl_chain_terminates`, and `chain_objects_blue` for the
   extended heap and new free-list head.

Prepending the fresh chain is easiest to verify because no existing free-list
links change. Appending may reduce fragmentation and better match address order,
but it requires traversing and updating the last old free block. A later
optimization can introduce address-ordered insertion once the grow-only proof is
in place.

Sweep coalescing should remain chunk-local. Adjacent free-object coalescing is
valid only when `next_in_mem` stays within the same chunk. Two chunks that happen
to be adjacent in virtual memory should still be treated as separate chunks
unless the runtime explicitly merges their chunk descriptors and the proof also
merges the model. This avoids depending on allocator accidents.

## Runtime integration

The C bridge should grow a verified-major-heap descriptor rather than replacing
the single `major_heap` pointer in place.

Implementation touch points:

- Replace `major_heap` and `major_heap_size_words` with a chunk table or linked
  list containing base pointer, byte size, and extracted-model chunk metadata.
- During initialization, allocate the initial chunk exactly as today, but expose
  it as `chunks[0]`.
- On major allocation failure, run a major collection first. If allocation still
  fails, call a new expansion path.
- The expansion path should:
  1. choose an expansion size using OCaml-like `major_heap_increment` and
     `percent_free` policy;
  2. allocate page-rounded memory, preferably through `caml_alloc_for_heap` or an
     equivalent bridge helper;
  3. register the chunk with `caml_page_table_add(In_heap, start, end)` so
     `Is_in_heap` and naked-pointer checks classify verified major objects
     correctly;
  4. call extracted verified initialization code that returns an updated
     `major_heap` descriptor and free-list head;
  5. update `stat_heap_wsz`, `stat_top_heap_wsz`, `stat_heap_chunks`, and the
     benchmark counters.
- Root scanning should not assume one interval. It should either iterate the
  verified chunk table or continue to scan roots independently and let the
  verified `is_major_pointer` predicate classify each value.
- Remembered scanning currently walks all major objects. It should iterate
  `objects_in_chunk` for each chunk.
- The minor/major distinction must stay unambiguous. A major chunk base must not
  overlap the minor heap's absolute address range, and no major chunk may use
  addresses that `to_minor_offset` would treat as minor offsets.
- The runtime patch must keep OCaml's write-barrier and initialization paths
  using the verified bridge. Any path that can allocate a major block must either
  call the verified expandable allocator or be explicitly outside the supported
  configuration.

The verified side should be the authority for whether expansion preserves
collector invariants. C should allocate raw memory and register pages, but the
transition from "new bytes" to "well-formed blue free blocks in the major heap"
should be represented by an extracted verified function with a strong
postcondition.

## Proof obligations

The main new theorem should be an extension lemma:

> If `major_heap_shape h fp` holds, and `c` is a fresh disjoint chunk initialized
> as a valid chain of blue free blocks, then `major_heap_shape (add_chunk h c)
> fp'` holds for the free-list head `fp'` produced by linking `c` into the free
> list. All previously allocated non-blue objects keep the same address, header,
> fields, color, graph edges, and reachability relationships.

The proof work decomposes as follows.

### Address and heap operation lemmas

- Disjoint chunks imply unique address ownership.
- Reads and writes in one chunk frame all other chunks.
- Adding a fresh chunk frames reads of all old addresses.
- `is_major_pointer` is monotonic under expansion: old major pointers remain
  major pointers.
- Fresh chunk addresses are not members of the old `objects` list.
- Object enumeration after expansion is old objects plus fresh blue objects.

These lemmas replace many current facts that follow trivially from
`addr < heap_size`.

### Object and graph lemmas

- Existing object headers and fields are unchanged by expansion.
- Existing no-scan objects still have no pointer fields.
- Existing graph vertices and edges are unchanged.
- Fresh blue free blocks are excluded from the live graph and from
  `no_pointer_to_blue` obligations except as non-targets.
- If a field pointed to a valid old major object before expansion, it still does
  after expansion.

The live-graph isomorphism proof for minor collection should then only need a
framing lemma: expansion does not change the source graph except by adding blue
free blocks that are not part of the live graph.

### Free-list and allocator lemmas

- Fresh blue-block chain is valid and terminating.
- Linking the fresh chain to the old free list preserves termination because the
  fresh addresses are disjoint from all old free-list addresses.
- Every address in the new chain is a valid object in the expanded heap.
- `chain_objects_blue` holds for the combined chain.
- Allocation from an old block frames the new chunks; allocation from a fresh
  block frames the old chunks.
- Allocator fuel should be based on a structural measure such as number of
  objects/free-list nodes, not `heap_size / mword` for one global heap.

The current allocator proofs already separate many facts through `.fsti`
interfaces. The new expansion lemmas should be isolated similarly, with a small
module dedicated to `add_chunk` and free-list linking.

### Sweep and coalescing lemmas

- Sweep iterates over all chunks.
- Sweep preserves chunk boundaries.
- Coalescing only combines adjacent free blocks within the same chunk.
- The sweep/coalesce equivalence theorem should be restated per chunk and then
  lifted to all chunks.
- Full major collection preserves the chunk table and only mutates bytes inside
  chunks.

Because expansion adds only blue free blocks, expansion itself should not need
to mark or sweep fresh chunks. The next major GC should handle them through the
ordinary chunk-aware sweep.

### Generational lemmas

- Promotion may allocate into any chunk.
- Forwarding maps should continue to map minor object addresses to absolute
  major object addresses; no `chunk_id` needs to appear in forwarded OCaml
  values.
- `minor_major_fields_no_blue` should use chunk-aware pointer classification and
  object membership.
- `major_minor_fields_no_infix_targets` and remembered scanning should quantify
  over all chunk-local major objects.
- The Cheney live-subgraph isomorphism should use the chunk-aware object set as
  the major part of the combined graph.
- Expansion after a failed promotion must preserve roots, remembered slots,
  already-copied major objects, and already-established forwarding information
  if it happens during minor collection.

That last point is important. The cleanest first implementation is:

1. Before starting minor collection, compute a conservative upper bound on the
   amount of major space that promotion could need from the current minor heap.
   A coarse bound based on the whole allocated minor region is acceptable for the
   first version.
2. If the current free list cannot provide that much space, run a major
   collection; if it still cannot, expand the major heap and link the fresh
   chunk into the free list.
3. Start Cheney promotion only after proving there is enough major capacity for
   the conservative bound, so the existing allocation-failure path is
   unreachable during the forwarding pass.

Supporting expansion in the middle of a partially built forwarding map is
possible, but it adds proof obligations about preserving partial copies and
forwarding-map consistency across expansion. Preflight expansion avoids that
complexity without requiring a transactional minor-collection attempt.

## Specification interface quality

The chunked design should expose enough in `.fsti` files for callers to reason
without unfolding implementation details.

Important public contracts:

- `add_chunk_preserves_old_reads`
- `add_chunk_preserves_old_objects`
- `add_chunk_objects`
- `add_chunk_preserves_graph_edges`
- `add_chunk_preserves_major_heap_shape`
- `fresh_chunk_chain_valid`
- `link_fresh_chain_preserves_fl_valid`
- `expand_or_collect_alloc_correct`

Avoid a weak interface that merely says expansion returns a well-formed heap.
Callers need the stronger frame properties connecting the expanded heap to the
old heap; otherwise promotion and graph-isomorphism proofs will not be able to
show that old live data was preserved.

## Staged migration plan

1. Add a pure chunk model next to the existing single-heap model. Prove address
   lookup, disjointness, read/write frame, and object-enumeration lemmas.
2. Add single-chunk compatibility lemmas showing the chunk model agrees with the
   current `heap` model when there is exactly one chunk.
3. Move major-only definitions behind chunk-aware interfaces:
   pointer classification, object enumeration, graph construction, and heap
   read/write.
4. Port allocator and free-list proofs. Keep the allocation algorithm first-fit
   and global; only its heap operations and fuel measure should change.
5. Add `init_fresh_chunk`, `link_fresh_chain`, and
   `add_chunk_preserves_major_heap_shape`.
6. Port sweep and coalescing to chunk-local traversal.
7. Port generational promotion, remembered scanning, and minor-collection
   correctness to the chunk-aware major heap.
8. Update extracted C and `alloc_gen.c` to carry chunk metadata, register pages,
   and retry allocation after expansion.
9. Re-enable benchmark heap calibration with an adaptive heap policy and compare
   GC counts against stock OCaml.

Each stage should keep a single-chunk configuration verifying. That prevents the
expansion refactor from invalidating the existing fixed-heap artifact before the
runtime path is ready.

## Heap sizing policy

The first verified expansion policy does not need to reproduce every detail of
OCaml's incremental major GC. It should, however, use the same shape:

- choose `request_words` from the failed allocation size;
- add free-space overhead using `percent_free`;
- clip by `major_heap_increment`;
- enforce a minimum chunk size;
- page-align the byte request;
- update statistics after successful expansion.

The proof only needs the resulting chunk to be large enough, word-aligned,
non-empty, disjoint, and below address-overflow limits. The exact policy can
remain a C-side calculation provided those facts are checked before calling the
verified `add_chunk` function.

## Risks and open questions

- **Pointer classification boundary:** the F* model must align with the runtime
  page table. If C registers a chunk as `In_heap`, the verified chunk descriptor
  must contain the same interval.
- **Fuel and termination:** many current proofs use `heap_size / mword`. Chunked
  proofs should use structural measures over chunk count, object count, or
  free-list chain length.
- **Large chunks:** OCaml headers have a maximum `wosize`. Expansion must split
  very large chunks into multiple blue blocks and prove the split is dense.
- **Expansion during collection:** grow before or after a collection attempt at
  first. Mid-promotion growth is a later optimization.
- **Shrinking:** do not implement initially. Returning chunks to the OS requires
  proving no roots or fields point into the removed chunk and unregistering the
  page-table interval.
- **Compaction:** out of scope. A compacting major heap would be a moving
  collector and requires a separate pointer-rewriting proof.
- **Multicore/concurrency:** the current integration is for OCaml 4.14 bytecode
  runtime behavior. If concurrent collectors or domains are introduced, chunk
  metadata updates need synchronization and proof support.

## Expected impact

Heap expansion should reduce the pathological full-major-GC counts seen with
minimum fixed heaps. The verified GC would be able to start near stock OCaml's
RSS footprint and grow when live data plus desired free space exceed the current
heap, instead of forcing repeated full collections against an artificially tight
major heap.

The expected benchmark improvement is not just avoiding out-of-memory failures.
It should also make the comparison fairer: stock OCaml's timings include an
adaptive major heap, while the current verified timings use a fixed major heap
chosen per benchmark. An expandable verified heap would let both runtimes report
time, allocation counts, minor collections, major collections, peak heap words,
heap chunks, and RSS under comparable adaptive policies.
