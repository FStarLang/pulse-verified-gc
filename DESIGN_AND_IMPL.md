# An Agentic Verified Generational Garbage Collector for OCaml 4

In previous posts, we have seen how agents using F* and Pulse can build a suite
of verified algorithms and data structures with functional correctness and
complexity proofs. Verified standalone algorithms are one thing. The more
interesting question is whether agents can help build, maintain, and integrate a
verified systems component whose specification has to match a real runtime.

This repository answers that question with a verified garbage collector for
OCaml 4.14. The project began from the shape of an earlier verified
mark-and-sweep collector for OCaml:


> Sheera Shamsu, Dipesh Kafle, Dhruv Maroo, Kartik Nagar, Karthikeyan Bhargavan & KC Sivaramakrishnan
> *"A Mechanically Verified Garbage Collector for OCaml"*
> Journal of Automated Reasoning **69**, 7 (2025).
> [DOI: 10.1007/s10817-025-09721-0](https://link.springer.com/article/10.1007/s10817-025-09721-0)
>
> Original source: <https://github.com/fplaunchpad/verified_ocaml_gc/>
>

But the code in this repository is not just a port. The development now contains
a shared OCaml-compatible heap model, a verified major-heap allocator, a
bounded-stack mark-and-sweep collector, a generational collector with a
Cheney-style copying minor collection, proof oriented specification tests
(SPOTs), extraction to C, and an OCaml runtime integration layer, all built
using the latest F* and Pulse infrastructure.

The result is intentionally both a research artifact and a codebase tour. This
document supersedes the other Markdown files in the repository: it explains how
the pieces fit together, which modules define the important contracts, how to
verify and extract them, how the OCaml integration works, what the current
benchmark data says, and what remains outside the verified boundary.

At a high level, the development proceeds in stages:

1. Build common infrastructure for OCaml values, headers, byte-addressed heaps,
   object enumeration, graph construction, DFS reachability, and Pulse heap
   ownership.
2. Verify a major-heap allocator over OCaml's blue free-list blocks.
3. Verify a stop-the-world mark-and-sweep major collector, including a bounded
   mark stack that can recover from overflow by rescanning the heap.
4. Add a nursery: a bump-pointer minor heap, promotion into the major heap, a
   forwarding map, remembered slots, root rewriting, and Cheney BFS.
5. Replace the older "five pillars" correctness condition for copying collection
   with a reachable-subgraph isomorphism, which states that the live graph before
   collection is isomorphic to the live graph after collection under the
   forwarding map.
6. Compose minor collection with the mark-and-sweep major collector into a
   verified generational `full_gc`.
7. Audit the public contracts with SPOTs: small proof-oriented tests that build a
   concrete heap and prove client-visible consequences.
8. Extract the verified code with KaRaMeL and connect it to the OCaml 4.14
   bytecode runtime.
9. Benchmark the end-to-end runtime against stock OCaml and use the results to
   guide the next round of optimizations.

In the general spirit of things, the development is a Ship of Theseus. The
starting point was the idea of a verified OCaml mark-and-sweep collector; the
current repository has replaced nearly every plank: the representation layer,
the proof organization, the allocation story, the collector algorithm, the
top-level correctness criterion, and the runtime integration are all different.

Agents were useful throughout: they could restructure proofs, search for missing
lemmas, split proof obligations, and carry local changes through verification.
But the project still required human judgment in exactly the places where formal
methods are most valuable: deciding what should be proved, recognizing when a
postcondition was too weak or too syntactic, choosing graph isomorphism as the
right abstraction for copying collection, and auditing the boundary between
verified code and the OCaml runtime.

```
                          +-------------------------------+
                          |        OCaml 4.14 runtime      |
                          | allocation, roots, ref_table   |
                          +---------------+---------------+
                                          |
                                          v
                          +-------------------------------+
                          |  C bridge: alloc_gen.c         |
                          | address translation, roots,    |
                          | remembered slots, GC triggers  |
                          +---------------+---------------+
                                          |
                                          v
+----------------+   +-------------------+-------------------+
| common/        |-->| mark-and-sweep/                       |
| heap, object,  |   | major allocator, bounded mark, sweep  |
| graph model    |   +-------------------+-------------------+
+----------------+                       |
        |                                v
        |                +---------------+-------------------+
        +--------------->| generational/                     |
                         | minor heap, Cheney promotion,     |
                         | remembered slots, full_gc         |
                         +---------------+-------------------+
                                         |
                                         v
                         +---------------+-------------------+
                         | spot/                             |
                         | concrete spec/contract audits     |
                         +-----------------------------------+
```

## Repository tour and build model

The active source tree is organized around verification layers rather than
around runtime files:

| Path | Role |
| --- | --- |
| `common/` | Shared F*/Pulse infrastructure: OCaml header layout, byte-addressed heap model, object predicates, field traversal, graph/reachability infrastructure, and low-level Pulse heap/stack ownership. |
| `mark-and-sweep/` | Major heap collector: free-list allocator, mark phase, bounded mark stack, sweep, coalescing, end-to-end major GC correctness, and extraction rules. |
| `generational/` | Generational collector: minor heap, promotion, Cheney BFS, remembered slots, root rewriting, combined graph/isomorphism proofs, Pulse implementation, extraction, snapshots, and OCaml integration. |
| `spot/` | Admit-free SPOT campaign that validates the generational contracts on a concrete three-object heap. |
| `generational/ocaml-integration/` | Patched OCaml 4.14 runtime, verified C bridge, tests, and benchmark data for the generational collector. |
| `mark-and-sweep/ocaml-integration/` | Runtime integration for the mark-and-sweep-only collector. |
| `snapshot` directories | Checked-in extracted C artifacts and support files used by integration builds. |
| `research/docs/` and older planning files | Historical proof notes and plans. They are useful archaeology, but this document is the current tour. |

The top-level `Makefile` is now the easiest entry point for the active verified
development. It scans dependencies from the generational implementation roots
and verifies common, mark-and-sweep, generational, and SPOT sources with the
right include paths:

```bash
make                  # verify active modules reachable from the root build
make common           # verify common sources
make mark-and-sweep   # verify common + mark-and-sweep
make generational     # verify common + mark-and-sweep + generational + SPOT
make extract          # extract mark-and-sweep and generational collectors
make clean
```

The top-level F* flags are worth knowing:

```make
--cache_checked_modules
--warn_error -321
--report_assumes warn
--already_cached 'Prims FStar Pulse PulseCore -GC'
--include common/spec --include common/lib --include common/impl
--include mark-and-sweep/spec --include mark-and-sweep/impl
--include generational/spec --include generational/impl
```

There are also local Makefiles when working inside a subsystem:

```bash
cd common && make verify-spec && make verify-impl
cd mark-and-sweep && make verify && make extract
cd generational && make verify && make extract && make snapshot
cd spot && make verify
```

As of this review, excluding bundled F*/KaRaMeL code and archived SPOT attempts,
the active `common`, `mark-and-sweep`, `generational`, and `spot` directories
contain 223 `.fst`/`.fsti` files and about 104k lines of F*/Pulse source. The
active development has no `admit()` calls. The only active top-level `assume`
declarations are two platform facts that connect Pulse's `size_t` representation
to 64-bit words in implementation heap modules:

```fstar
assume val platform_fits_u64 : squash SZ.fits_u64
```

Those assumptions appear in `common/impl/GC.Impl.Heap.fst` and
`generational/impl/GC.Gen.Impl.MinorHeap.fst`. They are part of the runtime
platform model, not collector-specific proof holes.

## OCaml heap layout invariant

Everything rests on matching OCaml's object representation. The shared header
module, `common/lib/GC.Lib.Header.fst`, defines the 64-bit header layout:

```fstar
/// Header layout (64-bit):
///   bits 0-7   : tag (8 bits)
///   bits 8-9   : color (2 bits: white=0, gray=1, black=2)
///   bits 10-63 : wosize (54 bits)

type color_sem =
  | White
  | Gray
  | Blue
  | Black

type header_sem = {
  wosize : w:uint_t 64{w < pow2 54};
  color  : color_sem;
  tag    : t:uint_t 64{t < 256};
}
```

The color names are semantic. `White`, `Gray`, and `Black` are the usual marking
colors. `Blue` is OCaml's free-list color: swept objects become blue blocks whose
body words are repurposed as allocator metadata.

The object model uses byte-addressed heaps. `common/spec/GC.Spec.Base.fsti`
abstracts over the concrete heap size and heap base:

```fstar
inline_for_extraction
let mword : U64.t = 8UL

val heap_size : n:pos{n % U64.v mword == 0 /\ n >= 16 /\ n < pow2 57}
val heap_size_u64 : n:U64.t{U64.v n == heap_size}

let heap = h:seq U8.t{Seq.length h == heap_size}

let hp_addr = a:U64.t{
  U64.v a < heap_size /\
  U64.v a % U64.v mword == 0
}

val zero_addr : a:hp_addr{U64.v a + U64.v mword < heap_size}
type obj_addr = a:hp_addr{U64.v a >= U64.v mword}
```

`hp_addr` is any word-aligned heap address. `obj_addr` is a value address, i.e.,
the address of the first field of an OCaml block, with the header one word before
it. `common/spec/GC.Spec.Heap.fsti` provides the arithmetic bridge:

```fstar
val hd_address (obj: obj_addr) : hp_addr
val hd_address_spec : (obj: obj_addr) ->
  Lemma (U64.v (hd_address obj) = U64.v obj - 8)

inline_for_extraction
val f_address (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : obj_addr
val f_address_spec : ... Lemma (U64.v (f_address h_addr) = U64.v h_addr + 8)
```

The heap itself is a sequence of bytes, with little-endian 64-bit read/write
operations. This is deliberately lower-level than a sequence of words: the same
specification must be extractable to C and must line up with OCaml's byte-level
runtime memory.

The object layer in `common/spec/GC.Spec.Object.fst` reads header fields from
the byte heap:

```fstar
let read_header (g: heap) (obj_addr: obj_addr) : GTot U64.t =
  read_word g (hd_address obj_addr)

let get_object_color (g: heap) (obj_addr: obj_addr) : GTot color =
  getColor (read_header g obj_addr)

let tag_of_object (obj_addr: obj_addr) (g: heap) : GTot U64.t =
  getTag (read_header g obj_addr)

let wosize_of_object (obj_addr: obj_addr) (g: heap) : GTot U64.t =
  getWosize (read_header g obj_addr)

let is_no_scan (h_addr: obj_addr) (g: heap) : GTot bool =
  U64.gte (tag_of_object h_addr g) no_scan_tag
```

`no_scan_tag` is crucial. OCaml objects with tags above the scan threshold
(strings, custom blocks, bigarrays, and related runtime data) contain raw data
rather than managed pointers. The collector must not trace them. That decision
appears in the graph bridge:

```fstar
let get_pointer_fields (g: heap) (h_addr: obj_addr) : GTot (seq vertex_id) =
  if not (object_fits_in_heap h_addr g) then Seq.empty
  else
    let ws = wosize_of_object h_addr g in
    if is_no_scan h_addr g || is_blue h_addr g then Seq.empty
    else get_pointer_fields_aux g h_addr 1UL ws
```

A free (blue) block is a vertex with no outgoing edges, and so is a no-scan
block.

#### Well-formedness

The main heap well-formedness predicate lives in
`common/spec/GC.Spec.Fields.fst`, in four named clauses.  Part 2 is the one
that matters for collection, and it reads like its English sentence:

> every non-free, scannable block's pointer-like fields point to a non-free
> real block.

What counts as *free* is a parameter, so the same definition serves the
stop-the-world collector and a sweep in progress:

```fstar
(* What counts as free for well-formedness. Physically free blocks are blue;
   a definition may also count blocks that are about to be freed. *)
type free_def = heap -> obj_addr -> GTot bool

let is_block (g: heap) (x: obj_addr) : GTot bool = Seq.mem x (objects zero_addr g)   (* a real block *)
let scannable (g: heap) (x: obj_addr) : GTot bool = not (is_no_scan x g)

let blocks_fit (g: heap) : prop =                                         (* part 1 *)
  forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==>
    U64.v (hd_address h) + 8 + U64.v (wosize_of_object h g) * 8 <= Seq.length g

let pointers_lead_to_non_free (free: free_def) (g: heap) : prop =          (* part 2 *)
  forall (src dst: obj_addr).
    is_block g src /\ not (free g src) /\ scannable g src /\ points_to g src dst ==>
    is_block g (resolve_object dst g) /\ not (free g (resolve_object dst g))

let interior_pointers_valid (free: free_def) (g: heap) : prop =            (* part 3, same sources *)
  forall (src dst: obj_addr).
    is_block g src /\ not (free g src) /\ scannable g src /\ points_to g src dst ==>
    infix_addr_wf g (objects zero_addr g) dst

let no_infix_block (g: heap) : prop =                                     (* part 4 *)
  forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(is_infix obj g)

let well_formed_heap_with (free: free_def) (g: heap) : prop =
  blocks_fit g /\ pointers_lead_to_non_free free g /\ interior_pointers_valid free g /\ no_infix_block g

let free_stw : free_def = fun g x -> is_blue x g
let well_formed_heap (g: heap) : prop = well_formed_heap_with free_stw g
```

In words:

1. **Blocks fit**: every block on the walk fits in the heap.
2. **Pointers lead to non-free blocks**: every non-free, scannable block's
   pointer-like fields point (after resolving an interior pointer to its
   enclosing closure) to a non-free real block.  At `free_stw`: nothing live
   points at a blue block.
3. **Interior pointers are valid**: an interior pointer out of a non-free,
   scannable block has a valid enclosing closure.
4. **No infix block**: the walk enumerates whole blocks; an infix header lives
   inside its closure, never on the walk.

Stop-the-world -- while the collector is idle or marking, and everywhere in
the mark-and-sweep proofs -- free means blue (`free_stw`).  A collector phase
that leaves dead blocks in place also counts the blocks it is about to free: a
sweep in progress counts the white blocks in front of its cursor, and the
generic theorems of the minor collection hold for any admissible definition of
free (see below).  A free block is garbage left in place: nothing constrains
its fields, and nothing reads them.  Free is a function of the heap, so a
block the allocator hands out stops being free as soon as its header is
written.  Proofs abbreviate "a non-free real block" as
`in_use free g x = is_block g x && not (free g x)`.

A *pointer* needs a scannable source: a no-scan block --- a `string`, a
`Bytes.t`, a `Bigarray` payload, a `Custom` block --- holds arbitrary bytes,
eight of which may spell an in-range address, so it has no pointers.  This
matches the collector, which never reads such a word, and
`get_pointer_fields`, which gives the block no edges.  `points_to` hides the
`wosize < 2^54` typing guard of the raw field search.

`well_formed_heap_with` and the two pointer clauses are `opaque_to_smt`;
clients cross the boundary with `wf_with_parts` (`wf_parts` for
`well_formed_heap`) and the intro/elim lemmas
(`pointers_lead_to_non_free_intro`/`_elim`,
`interior_pointers_valid_intro`/`_elim`, `points_to_target_not_free`).
Marking keeps `well_formed_heap` because it only recolours among white, grey
and black (`Mark.color_change_preserves_wf` requires a non-blue colour and a
non-blue object, so what is free is unchanged); the sweep proves it of its
result in `FusedSweep.End.sweep_post_wf`.

The graph given what counts as free
(`GC.Spec.HeapModel.create_graph_with free g`) has the vertices of
`create_graph g` but only the edges out of non-free blocks
(`create_graph_with_edge`); at `free_stw` it is `create_graph`
(`create_graph_with_stw`), so mark-and-sweep never sees the difference.

#### Interior (infix) pointers in major fields

The pointer clauses are stated on the **resolved** target, not on the raw
field value.  `resolve_object` is the identity on an ordinary pointer and maps
an interior pointer to the head of the closure that contains it.  So
`pointers_lead_to_non_free` says *the enclosing block of every pointer target
is a non-free block*, which is exactly OCaml's rule, and `interior_pointers_valid`
(`infix_addr_wf`) is the non-vacuous side condition that makes the mapping
well defined: an infix header carries the offset back to its parent, that
parent is itself an enumerated object, and it has `Closure_tag`.

This matters because **mutually recursive OCaml closures are represented with
interior pointers**: a single allocated block holds several code pointers, and
the fields that refer to the second and later functions point *into* the middle
of that block, at a header whose tag is `Infix_tag = 249`. An earlier version of
this development stated the pointer clause on the raw field value, which ---
combined with `no_infix_block` --- made `well_formed_heap` *unsatisfiable* for
any heap containing such a closure. The correctness theorem was sound but empty
on that class of heaps.

Consequences of the resolved formulation:

- `interior_pointers_valid` is load-bearing. The parent-closure machinery it
  guards (`parent_closure_addr_nat`, `infix_wf_elim`, `infix_wf_intro`,
  `infix_addr_wf`) does real work, and `resolve_object` is *not* the identity in
  general.
- The graph model resolves too. `GC.Spec.HeapGraph.get_pointer_fields_aux`
  emits `resolve_field g v` rather than `v`, so an edge from a source object
  always lands on an enumerated vertex, and `create_graph` is a graph over whole
  objects even when the heap uses interior pointers.
- The mark implementation resolves at the point of darkening.
  `check_and_darken_bounded` reads the target's header and, when the tag is
  `infix_tag`, darkens `v - wosize * 8` (the parent closure) instead. This is a
  real change in the extracted C, not a proof-only artefact.

##### Free-list cells

Both collectors handle interior pointers out of *live* objects in full
generality.  Free (blue) blocks are not constrained at all beyond their
free-list link: a blue block is free under every definition (`blue_is_free`),
and `GC.Spec.HeapGraph.get_pointer_fields` gives it no edges.  Nothing in the
collector reads such a word -- mark scans only grey objects, sweep and coalesce
read headers and colours, the generational pointer update skips blue objects,
and the allocator reads the header and field 0 -- so the coalescing pass leaves
the stale fields of dead objects in a merged block as they are rather than
zeroing them.  The link itself is covered by the free-list invariants
(`fl_valid`, `GC.Gen.FreeListShape.blue_link_fields_valid`).  A block the
allocator hands out has every field written before anything reads it:
promotion copies all of them (`copy_fields`), and a direct allocation is filled
by the runtime.

Infix addresses survive as **roots** for both collectors, and inside Cheney's
promotion machinery, which forwards an interior pointer as its closure's copy
plus the offset (`cheney_forward_one`).

Getting here removed two obstructions.  The first was the graph model:
`GC.Gen.CombinedGraph.classify_major_field` now resolves, returning
`MajorV (resolve_object v major)` whenever the resolved value is enumerated, so
an interior-pointer edge is no longer silently dropped;
`GC.Gen.ReachabilityBridge.major_edge_points_to` exposes the raw field value
alongside `dst == resolve_object raw major`.

##### End-to-end test

`generational/ocaml-integration/tests/infix_closures.ml` exercises all of this
against real OCaml code rather than a hand-built heap. It allocates mutually
recursive closures, confirms with `Obj` that a heap field genuinely holds an
interior pointer, checks every clause of `infix_addr_conds` numerically
(including `parent == h - wosize*8`), forces real collections by allocating,
and then verifies that a block reachable only through an interior pointer
survives mark and sweep with an unchanged heap shape. It runs as part of
`make -C generational/ocaml-integration test`, under both the verified runtime
and stock OCaml. Rebuilt against the pre-fix `check_and_darken_bounded` it fails
and then segfaults, so it is a genuine regression test and not a smoke test.

The heaps it builds hold interior pointers in major fields.  Since
`no_infix_field_targets` was dropped from the invariant, they are inside
`GC.Gen.HeapInvariant.major_heap_shape` and the composed `full_gc` theorem applies
to them: the generational reachability argument, not just the mark-and-sweep
proofs, covers what the test stresses.

The same module also states the no-scan invariant:

```fstar
let no_scan_invariant (g: heap) : prop =
  forall (src: obj_addr) (idx: nat).
    Seq.mem src (objects zero_addr g) /\
    is_no_scan src g /\
    ~(is_blue src g) /\
    idx < U64.v (wosize_of_object src g) ==>
      ~(is_pointer_field (read_word g field_addr))
```

This is the formal version of the runtime assumption that `no_scan` payload bytes
do not encode managed heap pointers that the collector should follow. The
invariant is restricted to non-blue objects because blue free-list blocks reuse
their body for allocator links.

The diagram below is the mental model for the major heap:

```
zero_addr
  |
  v
  +---------+---------+---------+-----+---------+---------+
  | header0 | field0  | field1  | ... | header1 | field0  |
  +---------+---------+---------+-----+---------+---------+
       ^        ^
       |        |
   hd_address  obj_addr / OCaml value pointer

header word:
  bits 63..10: wosize
  bits  9..8 : color (White, Gray, Blue, Black)
  bits  7..0 : tag
```

The graph model is built from this layout. `common/spec/GC.Spec.Graph.fst`
defines vertices, edges, well-formed graphs, successors, and reachability.
`common/spec/GC.Spec.HeapGraph.fst` bridges concrete fields to graph edges:

```fstar
let is_pointer_field (v: U64.t) : bool =
  U64.v v % U64.v mword = 0 &&
  U64.v v >= U64.v zero_addr + U64.v mword &&
  U64.v v < heap_size

let get_field (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) : GTot U64.t =
  let hd = hd_address obj in
  ...
  read_word g field_addr
```

For the major heap, graph vertices are object addresses and edges are pointer
fields between objects. That graph becomes the specification language for both
mark-and-sweep and generational correctness.

## The major heap allocator

The major heap allocator is a verified first-fit free-list allocator. Its pure
specification is `mark-and-sweep/spec/GC.Spec.Allocator.fsti`; its Pulse
implementation interface is `mark-and-sweep/impl/GC.Impl.Allocator.fsti`.

The allocator follows OCaml's convention that free blocks are blue objects and
the free-list link is stored in the first field of the free block:

```fstar
/// Algorithm (matches allocator.c):
/// 1. Walk the free list starting from fp
/// 2. For each blue (free) block, check if wosize >= requested
/// 3. If leftover >= 2: split -- create remainder block
/// 4. If leftover < 2: use entire block (no split)
/// 5. Write the allocated block's header: the phase's colour, the caller's tag
/// 6. Return (updated heap, new free pointer, allocated obj_addr)
```

The pure result type records exactly what changed:

```fstar
type alloc_result = {
  heap_out : heap;
  fp_out   : U64.t;
  obj_out  : U64.t;   // 0UL means out of memory
}
```

Like OCaml's `caml_alloc_shr (wosize, tag)`, the allocator takes the header
tag: the allocated block's header is written once, carrying `tag` (remainder
and fragment headers are blue with tag 0).  Mark-and-sweep callers and the C
bridge's `verified_allocate` pass 0; promotion passes the minor object's tag.

The header's colour comes from the collector's phase (`GC.Spec.Phase`), as
OCaml 4.14's `caml_allocation_color` decides it:

```fstar
type gc_phase = | Idle | Marking | Sweeping of U64.t    (* the sweep's cursor *)

let allocation_color (ph: gc_phase) (hd_addr: U64.t) : color =
  match ph with
  | Idle -> Header.White
  | Marking -> Header.Black
  | Sweeping c -> if U64.v hd_addr >= U64.v c then Header.Black else Header.White
```

`Marking` (4.14's `Phase_mark`) is the incremental marking phase:
`start_cycle` enters it and the mark slices run in it (M4 of the
incremental-mark plan, "The mark slice" below).

`alloc_search` takes the phase and writes `allocation_color` of the header
address it chose, once (`alloc_color`).  `alloc_spec g fp wz tag` is the
`Idle` instance -- the white allocator every stop-the-world proof uses -- and
the allocator over any phase is `GC.Spec.Allocator.Cursor.alloc_phase g fp ph
wz tag`: only the phase's colour rule enters it.  At `Idle` it is
`alloc_spec g fp wz tag` (`alloc_phase_idle`); the new head and object never
depend on the phase (`alloc_phase_fields`), and the heap is `alloc_spec`'s
with the new header recoloured (`alloc_phase_heap`) -- which is how every
idle-allocator fact holds at any phase (`GC.Spec.Allocator.Phase`, below).

The phase is the cursor alone, and allocation leaves it as it is.  During a
sweep the phase *record* also caches `swept_tail` and `last_fragment`
(below), functions of the heap and the cursor; an allocation that takes the
cached cell off the list moves the cache back, to the cell before it on the
list (`caml_fl_merge`).

The key implementation contract is intentionally simple: the Pulse allocator
returns a heap, a free-list head and an object that are exactly the pure
`alloc_phase` result, at the phase the record holds, and the record holds
that phase of the new heap.

```fstar
type phase_state = {            // GC.Impl.Allocator: the phase as C holds it
  ps_kind: U64.t;               // 0 idle, 1 sweeping, 2 marking
  ps_cursor: U64.t; ps_swept_tail: U64.t; ps_last_fragment: U64.t;
}
let phase_of (v: phase_state) : gc_phase =
  if v.ps_kind = 0UL then Idle
  else if v.ps_kind = 1UL then Sweeping v.ps_cursor
  else Marking

fn allocate (heap: heap_t) (fp_ref: R.ref U64.t) (phase: R.ref phase_state)
            (wosize: U64.t) (tag: U64.t{U64.v tag < 256})
  requires is_heap heap 's ** R.pts_to fp_ref 'fp ** is_phase phase 's 'ph **
           pure (U64.v wosize >= 1 /\ (Sweeping? 'ph ==> FLA.fl_ascending 's 'fp))
  returns obj: U64.t
  ensures exists* s2 fp2. is_heap heap s2 ** R.pts_to fp_ref fp2 ** is_phase phase s2 'ph **
    pure (let spec_res = AC.alloc_phase 's 'fp 'ph (U64.v wosize) tag in
          s2 == spec_res.heap_out /\
          fp2 == spec_res.fp_out /\
          obj == spec_res.obj_out)
```

`allocate` updates the free-list head in place, reads the phase once, computes the colour of the header address it
chose (white when idle; black while marking; while sweeping, black at or
above the cursor) and
writes the header once with it; while sweeping, an allocation that takes
`swept_tail`'s cell off the list stores the new `swept_tail` (one store, only
then).  At `Idle` the postcondition is `alloc_spec`'s (`alloc_phase_idle`, an
SMT pattern).

The phase predicate relates the stored record to the spec's phase *and the
heap*: `is_phase r g ph` says the record holds `ph`, and while sweeping its
cursor is a position of `g`'s walk and its caches are the ones derived from
`g` (`phase_rel`: the stored sweep state is `state_at g cursor`, below).  The
allocator keeps it: from an ascending free list (while sweeping), the cache it
moves back is the derived one of the heap the allocation leaves
(`GC.Spec.Allocator.Caches.alloc_caches`), so `is_phase phase 's ph` becomes
`is_phase phase s2 ph` -- the same phase.  What an allocation mid-sweep does to
the sweep phase (the new object a `new_block`, *fresh* until initialised) is a
lemma about the same `alloc_phase` (`GC.Spec.SweepPhase.Mutator.alloc_sweep_phase`,
below), not part of the contract: the allocator knows the phase record, not the
sweep's invariant, and its callers that need the invariant hold it beside.

The precondition asks nothing of the heap but, mid-sweep, an ascending list. The allocator only reads headers
and free-list links and checks every address it follows, so it does not need
pointer closure -- which matters during minor-to-major promotion, when the
major heap is temporarily not pointer-closed (fields may still hold old minor
pointers until the update pass rewrites them). The facts the callers need
afterwards (free-list validity, object bounds, ...) come from the allocator
lemmas about `alloc_spec`, under their own hypotheses.  (There used to be a
second function, `allocate_part1`, with the same body under `blocks_fit`
and the free-list facts; it is merged into this one.)

The allocator proof establishes the facts one expects from a systems allocator:

- the object returned on success came from a blue block;
- the returned object is fresh: it was not an allocated object before;
- the free list remains valid and terminating;
- split blocks are formed with valid headers and links;
- exact-fit and leftover-one cases consume the whole block safely;
- the heap shape facts needed by marking, sweeping, and promotion are preserved.

The initializer is also specified:

```fstar
fn init_heap (heap: heap_t)
  requires is_heap heap 's
  returns fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, fp) == SpecAlloc.init_heap_spec 's)
```

It creates one large blue block whose first field is `0`, the free-list
terminator.

## The mark-and-sweep collector

The mark-and-sweep collector is the major collector. Its pure proof lives mainly
under `mark-and-sweep/spec/`; its Pulse implementation lives under
`mark-and-sweep/impl/`.

The top-level Pulse interface in `mark-and-sweep/impl/GC.Impl.fsti` exposes a
single `collect` entry point:

```fstar
fn collect (heap: heap_t) (st: gray_stack) (fp: U64.t)
  requires is_heap heap 's ** is_gray_stack st 'st **
           pure (gc_precondition 's 'st fp (stack_capacity st))
  returns final_fp: U64.t
  ensures exists* s2 st2. is_heap heap s2 ** is_gray_stack st st2 **
          pure (SpecGCPost.gc_postcondition s2 /\
                SpecGCPost.full_gc_correctness 's s2 'st /\
                SpecGCPost.major_gc_live_subgraph_isomorphism 's s2 'st /\
                SpecGCPost.major_gc_unreachable_final_blue 's s2 'st)
```

The precondition packages all the shape facts needed by the collector:

```fstar
let gc_precondition (s: heap) (st: seq obj_addr)
                    (fp: U64.t) (cap: nat) : prop =
  SpecMarkBoundedInv.bounded_mark_inv s st cap /\
  SI.fp_valid fp s /\
  SpecMark.root_props s st /\
  SpecSweep.fp_in_heap fp s /\
  SpecMark.no_black_objects s /\
  SpecFields.no_scan_invariant s /\
  ... graph_wf/create_graph/root facts ...
```

The original mark-and-sweep theorem is expressed in
`mark-and-sweep/spec/GC.Spec.Correctness.fst` as five pillars:

```fstar
let full_gc_correctness (h_init h_final: heap) (roots: seq obj_addr) : prop =
  exists (h_mark: heap).
    let g_init = create_graph h_init in
    let g_final = create_graph h_final in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    // Pillar 1
    well_formed_heap h_final /\
    // Pillar 2
    (graph_wf g_init /\ is_vertex_set roots' /\ subset_vertices roots' g_init.vertices ==>
      forall x. mem_graph_vertex g_init x ==>
        (is_black x h_mark <==> Seq.mem x (reachable_set g_init roots'))) /\
    // Pillar 3
    (forall x. Seq.mem x g_final.vertices /\ is_black x h_mark ==>
      successors g_init x == successors g_final x) /\
    // Pillar 4
    (forall x. Seq.mem x g_final.vertices ==>
      (is_white x h_final \/ is_blue x h_final)) /\
    (forall x. Seq.mem x g_final.vertices /\ is_black x h_mark ==>
      is_white x h_final) /\
    // Pillar 5
    (forall x i. ... ==> get_field h_init x i == get_field h_final x i)
```

In prose:

1. **Heap integrity**: the final heap is well-formed.
2. **Reachability**: after marking, the black objects are exactly the objects
   reachable from the roots in the initial heap graph.
3. **Structure preservation**: live objects keep the same graph successors.
4. **State reset**: after sweeping, there are no gray or black objects; live
   objects are white and dead objects are blue/free.
5. **Data transparency**: fields of live objects are preserved.

The major collector also exports graph-isomorphism flavored consequences:
`major_gc_live_subgraph_isomorphism` and `major_gc_unreachable_final_blue`.
These are the bridge to the generational proof, where graph isomorphism becomes
the main correctness language.

### The sweep: one pass, eager merging, an ascending list kept across cycles

After marking completes there are no gray objects: black objects are the live
major-heap objects, while white objects are unreachable. The sweep turns black
survivors white, frees unreachable objects, and merges every run of adjacent
free blocks into one -- in a single pass, as OCaml 4.14's first-fit sweep does
it.

**The free list is ascending and kept across cycles.** The sweep edits it in
place rather than rebuilding it. It walks the heap upwards with a cursor, so the
list splits at the cursor: behind it the blocks already swept, ending at
`swept_tail`; in front of it the list as marking left it. The block after
`swept_tail` on the list is always the first list block at or above the
cursor, so appending a new free block costs one link write, and unlinking a
block that gets merged costs one.

The specification is `GC.Spec.FusedSweep`. Its state between steps (the
loop state of the pass; the incremental sweep's phase is only its cursor,
the rest being derived, below) is

```fstar
type sweep_state = {
  cursor: U64.t;         (* header of the next block to visit *)
  swept_tail: U64.t;     (* last list block behind the cursor, or 0 (the head) *)
  last_fragment: U64.t;  (* the header-only free block just behind the cursor, or 0 *)
}
```

and one step (`sweep_step`) reads the header at the cursor *in the current
heap*:

- **black**: a survivor; turn it white;
- **blue or white, previous block free** (`prev_free`: `last_fragment` is
  set, or `swept_tail`'s block ends at the cursor): grow the previous block
  over this one, unlinking this block if it was on the list; a header-only
  fragment that grows gains a link field and joins the list after
  `swept_tail`;
- **blue, previous not free**: leave it; a list block becomes `swept_tail`,
  a header-only one becomes `last_fragment`;
- **white, previous not free**: free it (blue header, tag 0); link it after
  `swept_tail` if it has room for a link, otherwise it is a fragment.

`fused_sweep_coalesce g fp` runs steps from `zero_addr` to the end of the heap.
Free blocks' bodies are left alone: a merged block's header records its full
size, so the object walk jumps over the stale words of the blocks it absorbed.

**The proof is a loop invariant on the step**, not a reduction to a two-pass
specification, and it is the one invariant of the incremental sweep
(`GC.Spec.SweepPhase.Intrinsic.sweep_inv_incremental`, below): it is about the
current heap and the cursor only, and holds in both modes.  Its clauses about
the walk and the list (`GC.Spec.FusedSweep.Inv`): behind the cursor no two free
blocks are adjacent; the free list from `fp` is exactly the heap's cells, in
ascending order (`GC.Spec.FreeList.Ascending.fl_ascending`); `swept_tail` and
`last_fragment` mean what they say (they are derived from the heap and the
cursor).  `GC.Spec.FusedSweep.Step` keeps it with one lemma per case of the
step, each concluding the invariant's clauses at the new cursor directly.

Stop-the-world, the end facts relate the result to the marked heap `g0`, so
the sweep keeps `sweep_inv_stw g0 g fp c`: the invariant, the walk of `g0`
reaches the cursor, `g` is `g0` from the cursor on (`front_unchanged`), every
block black in `g0` is still a block of `g` with the same size, tag and fields
(`marked_survive`), and every non-free block behind the cursor was black in
`g0` (`survivors_were_marked`).  `sweep_inv_stw_start` establishes it from the
heap marking left and the previous cycle's list, `sweep_inv_stw_step` keeps it
(only the extra clauses, from the step's frame), and
`GC.Spec.SweepPhase.Intrinsic.End.sweep_inv_stw_end` reads the
post-collection facts off it once the cursor reaches the end of the heap
(`GC.Spec.FusedSweep.End.sweep_post`; `fused_sweep_post` for the whole pass):
live objects unchanged and white, every dead block inside a free block, free
blocks holding only dead blocks, no adjacent free blocks, the walk dense, the
list exact and ascending, and -- from the mark postcondition's colour facts --
the heap well formed, with no pointer into a free block and every live
object's edges unchanged.

`GC.Impl.FusedSweepCoalesce.fused_sweep_coalesce` is the Pulse loop: the state
lives in references, the loop invariant is `sweep_inv_incremental` (with the
derived caches) plus "the rest of the pass computes the spec's result", and
each iteration is one `sweep_step_impl`, checked against the step equations
(`GC.Spec.FusedSweep.Step.step_eq_*`).  It needs the heap marking left
(`FusedSweep.End.marked`: no grey object, no black object pointing at a white
one).  `GC.Impl.collect_with_roots` calls it with the free list it was handed
and proves its postcondition with `GC.Spec.Correctness.gc_result_fused`, whose
`sweep_post` comes from `fused_sweep_post`; `gc_coalesce_source` records that
the result is exactly `fused_sweep_coalesce h_mark fp`.

Because the list is kept, the collector needs it ascending and exact on entry.
`gc_precondition_with_roots` asks for it, root darkening keeps it, and the
generational invariant `major_heap_shape` carries it: the allocator keeps it
(`GC.Spec.Allocator.Ascending`: a right-justified split keeps the remainder's
address, an exact fit unlinks the block from its unique predecessor), and so
do promotion and the pointer rewrite (`GC.Gen.FreeListAscending`). First-fit
on an ascending list prefers low addresses (OCaml's allocation policy 1).

### The sweep phase: the program between sweep steps (incremental sweep)

An incremental sweep runs the program between slices of `sweep_step`s
(`incremental-sweep-plan.md`). The phase is part of the collector's state:
`gen_heap_t.phase_ref`, which the Pulse allocator reads (above) and the
major collector's entry points (below) write. By default (`VERGC_MAJOR=stw`)
the bridge runs every major collection as `full_gc`, which runs the cycle to
its end, so between collections the phase is `Idle`; with
`VERGC_MAJOR=incremental` it runs the cycle -- marking, then the sweep -- in
slices between program steps
(`generational/ocaml-integration/verified_gc/OCAML_INTEGRATION.md`, "The
Major Mode": the trigger, the pacing, and how the bridge meets the trusted
obligations; below, "The bridge (M5)").

**Allocation at the sweep's phase** (`GC.Spec.Allocator.Cursor.alloc_phase`).
At `Sweeping c` the allocator colours by position: an object allocated in
front of the cursor (header at or above it) is black, so the sweep keeps it;
one behind it is white.  The block it hands back is a `new_block`
(`GC.Spec.SweepPhase.Mutator.alloc_phase_new_block`, from an exact ascending list
alone): not a non-free block before, of the requested size and tag, black at
or in front of the cursor and white behind it, so never pending free.

**The sweep's caches are derived, so the phase is the cursor.**
`swept_tail` (the last free-list cell behind the cursor) and `last_fragment`
(the cursor, when the block ending at it is a one-word free block) are
functions of the heap and the cursor:
`GC.Spec.SweepPhase.Intrinsic.last_cell_behind g c`, `frag_at g c`, and
`state_at g c` the sweep state with both.  So the spec's phase is
`Sweeping c` and the spec carries no cache: the clauses the stop-the-world
invariant states of the caches hold of the derived state at any position of
the walk -- `tail_ok_iff`, `frag_at_ok`, and `ends_free_derived` (the block
ending at `c` is free exactly when `prev_free g (state_at g c)`: a free block
ending there is a fragment, or a cell and then the last cell behind `c`; and
only one block of the walk ends at `c`).  A sweep step is the stop-the-world
step run from `state_at g c`, and the state it leaves is the derived one of
the new heap (`sweep_inv_incremental_step`).  The implementation stores the
caches in the phase record and updates them in place -- the sweep step, and the
allocator when it takes the cached cell off the list
(`GC.Impl.Allocator.allocate`; `alloc_choice` names the block first-fit takes
and its list predecessor) -- and its phase predicate says the
stored values are the derived ones (`is_phase`, above; kept by allocation,
`GC.Spec.Allocator.Caches.alloc_caches`, and by anything that keeps the walk and the
headers, `state_at_heads`).

**The invariant is intrinsic** (`GC.Spec.SweepPhase.Intrinsic`): it is about
the current heap and the cursor only, with no ghost heap.  During the
sweep, what counts as free is the blue blocks and the blocks *pending free*:

```fstar
(* white in front of the cursor: will be freed by this sweep *)
let pending_free (c: U64.t) (g: heap) (x: obj_addr) : GTot bool =
  is_block g x && is_white x g && U64.v x > U64.v c

let free_incremental (c: U64.t) : free_def =
  fun g x -> is_blue x g || pending_free c g x

let sweep_inv_incremental (g: heap) (fp: U64.t) (c: U64.t) : prop =
  let n = U64.v c in
  n % 8 == 0 /\ n <= heap_size /\ W.reaches g zero_addr n /\
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  well_formed_heap_with (free_incremental c) g /\
  behind_swept g n /\ front_unswept g n /\
  no_adjacent_free g n /\
  FLA.fl_ascending g fp
```

The blocks pending free -- white in front of the cursor (`x > cursor` on the
object address is "header at or above the cursor") -- are dead but not yet
freed.  So part 2 of well-formedness reads, mid-sweep: every block that is
neither blue nor pending free points only at blocks that are neither; the
fields of a block pending free are unconstrained (they may point into blocks
the sweep has already freed).  `free_incremental c` is an admissible
definition of free (`free_incremental_ok`: blue blocks are free, and it is
read off the walk and the headers).  Everything but well-formedness is
`sweep_shape`: facts about the walk, the headers and the free list, kept by
any change that keeps the walk and every header on it (`shape_transport`).
The step is proved directly on the invariant (`GC.Spec.FusedSweep.Step`):
behind the new cursor the block just swept is white or free, in front of it
nothing changed (and nothing is grey), and the blocks that are not free are
the same blocks with the same contents, so well-formedness carries over
(`wf_transport`).

- `sweep_inv_incremental_start`: the heap marking left satisfies it, with
  every white object pending free.
- `sweep_inv_incremental_step` (`FusedSweep.Step`): a step from `state_at g c`
  keeps it at the new cursor, leaving the derived state; it frees only blocks
  pending free (the non-free blocks are the same before and after, with the
  same size, tag and fields) and the pending-free set only shrinks.
  `sweep_inv_incremental_steps` is the same for up to `k` steps
  (`sweep_steps`, a slice).  That the blocks pending free are among the white
  objects marking left is a lemma (`pending_free_within_step`), not carried.
- `sweep_inv_incremental_end` (`.End`): at the end nothing is pending free,
  the heap is well formed and swept clean
  (`GC.Spec.SweepPhase.Util.swept_clean`); while the sweep runs the list is
  exact, so an allocation fails only when no free block anywhere is big
  enough (`Allocator.Oom.sweep_inv_incremental_oom_no_fit`, #29 mid-sweep).
- Stop-the-world the sweep keeps `sweep_inv_stw g0 g fp c` (above:
  `front_unchanged`, `marked_survive`, `survivors_were_marked` against the
  marked heap), and `sweep_inv_stw_end` gives `FusedSweep.End.sweep_post`
  (`fused_sweep_post` for the whole pass).

**The program's events keep it** (`GC.Spec.SweepPhase.Mutator`; promotion,
`GC.Gen.SweepPhase`), each leaving the pending-free set unchanged:

- allocation (`alloc_sweep_phase`): first-fit at `Sweeping c`; the phase stays
  `Sweeping c`.  A new object is never pending free (`new_block`, by
  `alloc_phase_new_block`: black in front of the cursor, white behind it).  Its fields are what the free block held,
  so the result is the invariant with the new object *fresh* (`fresh_ok`: the
  heap is well formed when the new object also counts as free,
  `free_or_uninitialised c obj`, so nothing points at it);
  writes into it keep it fresh (`fresh_write`), and once every field holds a
  storable value it closes (`fresh_close`).  The allocation-shape facts behind
  it (the block first-fit takes, the words it writes, its walk, cells and
  list) are `GC.Spec.Allocator.Shape`;
- a program write (`write_sweep_phase`) under
  `program_write (free_incremental c)`: a word of a non-free object that is
  not a closure, storing a value that is not a pointer or points (resolved)
  at a non-free object (`storable`);
- promotion (`promote_sweep_phase`): `promote_object` at the sweep's phase --
  the allocation with the nursery object's tag, the copy of its fields (which
  `minor_fields_ok`, from `minor_major_fields_not_free`, makes storable), and
  the close.

The `_shape` forms (`alloc_sweep_shape`, `body_write_shape`,
`promote_sweep_shape`) state the same about `sweep_shape` alone.

**A minor collection mid-sweep** (`GC.Gen.SweepPhase.Minor`) runs at the
sweep's phase, `Sweeping c` -- every promoted copy is allocated there, black
in front of the cursor and white behind it -- with the sweep's own definition
of free, `free_incremental c`, and the generic theorems
(`GC.Gen.CheneyGeneric`, "The minor collection, for any definition of free")
apply to it directly.  What they ask of the definition of free beyond
admissibility is that the allocator at the phase hands out no free block
(`allocations_not_free (Sweeping c) (free_incremental c)`), and that is
`allocation_color` at work (`free_incremental_allocations_not_free`): a copy
in front of the cursor is black, so not pending free, one behind it is not in
front of the cursor, and neither is blue.  A white copy in front of the cursor
would be pending free, and freed by the sweep while reachable.

- `sweep_collection_shape` (step B): the sweep phase, with the nursery's shape
  and `minor_major_fields_not_free (free_incremental c) minor g`, is
  `collection_shape_with (Sweeping c) (free_incremental c) minor g fp` (the
  free-list half from the exact ascending list alone,
  `PostCollectionShape.free_list_shape_of_ascending`);
- `minor_keeps_sweep_phase` (step C): for the collection at the sweep's phase,
  `collect_at c minor g fp roots = cheney_collect_spec_with (Sweeping c)
  (free_incremental c) minor g fp roots`, the result satisfies
  `sweep_inv_incremental` at the same cursor `c`, the pending-free set is the
  same, and the result keeps `collection_shape_with`.  Well-formedness is the
  generic theorem's (`cheney_collect_with_preserves_shape`); the shape is by
  induction over the promotions (`GC.Gen.Cheney.Induction.cheney_promote_keeps`),
  each a promotion at the phase (`promote_sweep_shape`), and the pointer update keeps
  the walk and every header.  Its two block-level facts are exported on their
  own, for the collection from `g` to `g'`:
  - `minor_keeps_pending_free`: `pending_free c g x <==> pending_free c g' x`
    (new objects are never pending free, existing headers do not change);
  - `minor_keeps_blocks`: every non-free block of `g` is a block of `g'` with
    the same header, and a non-free block of `g'` that was not one of `g` is a
    promoted copy (the image of a nursery object).

**Safety over the phase** (`GC.Gen.SweepPhase.Safety`) is stated on the
reachable graph, not on a heap the sweep started from.  In the sweep's graph
(`create_graph_with (free_incremental c) g`: a block pending free has no
edges) every object reachable from a non-free root is non-free -- a real
object that is neither blue nor pending free (`reachable_not_free`; over the
nursery's combined graph `reachable_not_free_combined`).  A sweep step frees
only blocks pending free, so it never frees a reachable one and leaves its
size, tag and fields alone (`step_keeps_reachable`; `steps_keep_reachable` for
a slice), and a minor collection in between keeps every non-free object
non-free (`minor_keeps_not_free`) and the pending-free set (step C).  The
slice lemmas are in `FusedSweep.Step`: `sweep_inv_incremental_steps` (and
`sweep_inv_stw_steps`), and `sweep_steps_done` (a budget of one step per heap
word finishes the sweep).

**Completeness over the phase** (`GC.Spec.SweepPhase.Completeness`, and
`GC.Gen.SweepPhase.Completeness` for the minor collection) is the incremental
counterpart of `major_gc_unreachable_final_blue`: *when the sweep ends, every
block that was dead when marking ended has been freed* -- it is no longer a
non-free block (merged into a free block, or a free block itself) -- unless its
address was handed out again since, in which case the block there is a new
object.  Objects that die during the sweep are floating garbage for the next
cycle and are not covered.  It is carried as an account of the non-free blocks,
`survivor_or_new g0 since g c`: every block not free for `free_incremental c`
was black in the marked heap `g0` (`survived_mark`) or its address is in
`since`, a ghost set of addresses allocated since marking ended.  The account
holds from the marked heap with nothing allocated (`survivor_or_new_start`,
needing only that nothing is grey), and every event keeps it:

- sweep steps and slices (`survivor_or_new_steps`, `survivor_or_new_slice`):
  a step never makes a block non-free;
- an allocation (`survivor_or_new_alloc`), with the new object added to
  `since` (`with_new`); it makes no other block non-free
  (`GC.Spec.SweepPhase.Mutator.alloc_in_use`);
- a write into the body of a non-blue block, i.e. a program write or the
  initialisation of a fresh object (`survivor_or_new_body_write`): it keeps
  the walk and every header;
- a minor collection (`GC.Gen.SweepPhase.Completeness.survivor_or_new_minor`),
  with its promoted copies added to `since` (`with_promoted`), from
  `minor_keeps_blocks`.

At the end nothing is pending free, so `freed_by_end` reads the account off
the blue blocks: every non-blue block is a survivor or new, and every object
white in the marked heap is `freed` or in `since`.  Marking leaves white
exactly the non-free objects unreachable from the roots
(`GC.Spec.Correctness.mark_post_white_iff_unreachable`, `dead_at_mark_white`),
which gives the reachability form `unreachable_freed_by_end` (under the same
graph hypotheses as the stop-the-world theorem, `roots_in_graph`).  At the
collector's phase, `phase_account` (the sweep phase and the account
mid-sweep; the end form when idle) is kept by `SL.phase_slice`
(`phase_account_slice`), so it composes with the `major_slice` contract
directly.  The "survivor or new" form was chosen over
a per-object "dead ones are pending free or freed" invariant because every
event already states what it does to the non-free blocks, and it says more:
the non-free blocks at the end are exactly accounted for.

`GC.SPOT.SweepPhasePendingFree` exercises all of it on a concrete heap: from
the two-block heap of `GC.SPOT.ConcreteMajorGen` it sweeps everything into one
free block, allocates `P` and `G` behind the cursor at the end of that sweep
phase (white), stores `G` into `P` (a program write), ends the phase and
starts the next one, and takes two steps: the free block at the start absorbs
`G`.  Then `P` is pending free, its field points at `G`, `G` is no longer an
object (its word lies inside the merged free block), and the heap is in the
sweep phase and in `collection_shape_with` with that non-empty pending-free
set; the minor collection at the sweep's phase keeps the sweep phase with `P`
still pending free.
`GC.SPOT.SweepPhaseFreedByEnd` continues it as a cycle for completeness: from
that marked heap, the two-step slice, a minor collection of an empty nursery,
and the rest of the sweep keep the account, and at the end both dead-at-mark
objects, `G` and `P`, are freed (`freed_by_end_spot`).
`GC.SPOT.IncrementalCycle.cycle_frees_dead` applies it to the Pulse entry
points: after `minor_collect`, `start_cycle`, a 64-word `major_slice` and
an unbounded one, every object white in the marked heap is freed.

#### The entry points

`GC.Gen.Impl` is the Pulse side, shaped like OCaml 4.14's major GC
(`runtime/major_gc.c`): a cycle starts idle right after a minor collection
(`start_cycle`, as 4.14's `start_cycle`) and runs in slices (`major_slice`, as
`caml_major_collection_slice`) until it is idle again; finishing a cycle
(4.14's `caml_finish_major_cycle`) is slices with an unbounded budget until
`major_slice` reports idle.  `start_cycle` darkens the roots and enters
`Marking`; the slices mark (4.14's `mark_slice`), hand over to the sweep when
nothing is grey, and sweep.  Both modes use the same entry points, all
extracted into `GC_Gen_Impl.{c,h}`: stop-the-world is `full_gc`, which is
`minor_collect`, `start_cycle` and slices until idle in one call.

**The collector's state** is one predicate, indexed by the phase
(`GC.Gen.Incremental.phase_shape`):

```fstar
let gc_state gh d b s fp ph : slprop =
  is_gen_heap gh d b s fp ** gen_phase gh s ph ** mark_state gh s ph **
  pure (GI.phase_shape ({ data = d; bump = b }) s fp ph)

phase_shape minor g fp Idle         = collection_heap_shape minor g fp
phase_shape minor g fp Marking      =
  collection_shape_with Marking free_stw minor g fp /\ marking_inv g (nursery_held minor)
phase_shape minor g fp (Sweeping c) =
  sweep_inv_incremental g fp c /\ minor_heap_shape minor /\
  minor_major_fields_not_free (free_incremental c) minor g
```

(`phase_shape` is opaque, with `phase_shape_idle` / `phase_shape_marking` /
`phase_shape_sweeping` to open it.)  `mark_state gh s ph` owns the persistent
mark state: the stack, the overflow flag, the partly scanned object and the
rescan cursor (below, "The mark slice").  `gen_phase gh s ph` is where the stored caches meet the heap:
the phase record holds `swept_tail` and `last_fragment` beside the cursor,
and `Alloc.is_phase` says they are `state_at s cursor`'s.  What counts as
free for a minor collection at a phase is `phase_free ph`: `free_stw` idle,
`free_incremental c` mid-sweep; the collection runs at that phase.

**A slice** is whole sweep steps until the swept blocks -- headers included --
add up to at least the budget in words, or the sweep is finished
(`GC.Spec.SweepPhase.Slice.sweep_slice`; it overshoots by at most one block,
as 4.14's `sweep_slice`). A slice is some number of steps (`slice_is_steps`),
so it keeps the sweep phase (`sweep_slice_phase`), and a budget of more words
than the heap has finishes it. `phase_slice g fp ph budget` is the slice at
the phase: nothing idle; mid-sweep the slice from `state_at g c`, the phase
it leaves its new cursor, and idle again once the cursor reaches the end. The
Pulse loop is `GC.Impl.FusedSweepCoalesce.sweep_slice_impl`, over the same
`sweep_step_impl` the stop-the-world pass runs, with step safety from
`FusedSweep.Step.sweep_inv_incremental_ready`.

| entry point | requires | ensures |
|---|---|---|
| `minor_collect gh roots .. slots ..` | `gc_state .. ph`, `minor_slots_ok ph` (the remembered set and roots for `phase_free ph`) | `minor_collect_with`'s contract at `ph` for `phase_free ph` (`minor_collect_post_with ph (phase_free ph) ..`), `gc_state` at the same phase `ph` (idle stays idle; mid-sweep the cursor and the pending-free set are kept, `GI.minor_keeps_phase_shape`); returns whether promotion succeeded |
| `start_cycle gh roots nroots` | `gc_state .. Idle`, `nursery_empty d b` (right after a minor collection), `start_cycle_pre s rs` (every root a darkenable major object; nothing about how many) | `start_cycle_post s rs s2`: the heap is the roots darkened (`GC.Gen.MarkPhase.Start.darkened`) and the roots are held (`MP.held_reached s2 (GMM.roots_held s2 rs)`); `gc_state` at `Marking`; nursery, free-list head and roots unchanged |
| `major_slice gh budget` | `gc_state .. ph` | `GI.major_slice_post s fp ph budget s2 fp2 ph2`: idle, nothing; marking, some mark moves (`S.mark_steps`), the free list untouched, still `Marking` or, with nothing grey, `Sweeping zero_addr`, and an unbounded budget finishes marking (`GI.mark_slice_post`); mid-sweep, `phase_slice`; `gc_state` at `ph2`; returns `Idle? ph2` |
| `modify_field ghr slot v` | `gc_state .. ph`, `GB.modify_ok ph minor s x slot v` (trusted: `slot` a body word of the non-free, scannable, non-closure block `x`, `v` storable there, and while marking a value the program holds) | `gc_state` at the same phase of `GB.modify_heap ph s slot v`; returns `GB.modify_records s slot v` (append the slot to the ref table); while marking, a write into a field the mark slice has scanned restarts the partly scanned object's scan (`MS.reset_cur`) |
| `initialize_field ghr slot v` | `is_gen_heap`, `gen_phase`, `mark_state` at `s`; `slot` a body word of a non-free block `x` of `s` (a block just allocated); while marking, `x` black and nothing non-free pointing into it (the part of `marking_fresh` the mark cache needs) | the same of `write_word s slot v`; returns `GB.initialize_records v` |
| `full_gc gh roots .. slots ..` | `gc_state .. Idle` and the stop-the-world minor-collection arguments (zeroed forwarding array, remembered set sound and covering, remembered targets among the roots, roots valid) | the stop-the-world contract (below): out of memory reported only for a concrete OOM, rewritten roots, `minor_reset`, `collection_heap_shape` restored, the end-to-end isomorphism, unreachable objects freed; `gc_state .. Idle`; returns whether promotion succeeded |

Major allocation, at either phase, is the allocator itself
(`GC.Impl.Allocator.allocate` on the heap's free-list head and phase record):
`AC.alloc_phase`'s result at the record's phase, which it keeps (the cached
`swept_tail` kept derived).  Mid-sweep, from the sweep phase and
`tag <> infix_tag`, `GC.Spec.SweepPhase.Mutator.alloc_sweep_phase` says what
that result is: either nothing changed or the object is a `new_block` and
`fresh_ok`.

The end of the sweep is the stop-the-world shape again
(`GI.sweep_end_shape`: `sweep_inv_incremental_end`'s swept-clean heap, the
free-list facts from the ascending list, no black or grey object, and with nothing
pending free the cross-generation condition is the idle one), so a new
cycle can follow. A full collection requested mid-sweep finishes the cycle
first (D4). `GC.SPOT.IncrementalCycle` checks that the contracts compose:
from `full_gc`'s precondition alone, `minor_collect`, `start_cycle`, a
64-word slice while marking and unbounded slices end idle in
`collection_heap_shape`, with nothing supplied in between.

**What the bridge supplies** (trusted, documented in the interface). Each
entry point is a separate C call, so `gc_state`'s pure half is re-supplied at
every call. It holds because every
collector call returns it and the program's events in between keep it:

- a block the program allocates mid-sweep is fresh; the runtime initialises
  every field with a storable value (an integer, or a pointer to a non-free
  object -- a reachable one) before the next collector call
  (`fresh_write`, `fresh_close`);
- every major-field write goes through the verified barrier
  (`modify_field` / `initialize_field`, "The write barrier" below) with its
  precondition `modify_ok` (a `program_write`; while marking, a value the
  program holds), and the bridge appends the slot to the ref table exactly
  when the barrier returns true; a write into a nursery object needs no
  barrier;
- nursery allocation keeps the nursery's shape and the cross-generation
  condition for `free_incremental c`;
- `minor_slots_ok`: the forwarding array zeroed, the remembered set sound and
  covering for the phase's definition of free (a slot may be listed more
  than once), the remembered targets among the roots, the roots valid and not free (never
  pending free);
- only the collector writes `phase_ref`.

The cycle's completeness theorem (below, "The cycle's theorems (M6)") takes
one more obligation as a hypothesis, nothing at runtime depends on it: while
marking, the program writes into an object it can reach a value it holds,
against the cycle's start (`MPC.cycle_write`), and the nursery holds only
such values.

### Bounded mark stack

The earlier verified mark-and-sweep design assumed an unbounded mark stack. That
is not realistic for a runtime collector. The bounded-stack development is in
`mark-and-sweep/spec/GC.Spec.MarkBounded.fsti`,
`mark-and-sweep/spec/GC.Spec.MarkBoundedInv.*`, and
`mark-and-sweep/impl/GC.Impl.MarkBounded.*`.

The key idea is simple: if the stack is full, still gray the child in the heap
but do not push it. Later, rescan the heap to find gray objects not currently on
the stack.

```fstar
let rec push_children_bounded
  (g: heap) (st: seq obj_addr) (obj: obj_addr)
  (i: U64.t{U64.v i >= 1}) (ws: U64.t) (cap: nat)
  : GTot (heap & seq obj_addr)
  =
    ...
    if is_white child g then
      let g' = makeGray child g in
      if Seq.length st < cap then
        (g', Seq.cons child st)
      else
        (g', st)  // overflow: child gray in heap, not on stack
```

The top-level bounded loop alternates between draining a bounded stack and
rescanning the heap:

```fstar
let rec rescan_heap (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : GTot (seq obj_addr) =
  ...
  if is_gray obj g && not (Seq.mem obj st) && Seq.length st < cap then
    Seq.cons obj st
  else
    st

let rec mark_bounded (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : GTot heap =
  let st = rescan_heap g (objects zero_addr g) Seq.empty cap in
  if Seq.length st = 0 then g
  else
    let inner_fuel = count_non_black g in
    let (g', _) = mark_inner_loop g st cap inner_fuel in
    mark_bounded g' cap (fuel - 1)
```

The proof challenge is that the old stack invariant said, roughly, "gray
objects are on the stack." Overflow intentionally violates that. The bounded
invariant instead separates what is needed for local stack processing from what
is recovered by heap rescanning:

```fstar
let bounded_stack_props (g: heap) (st: seq obj_addr) : prop =
  stack_elements_valid g st /\
  stack_points_to_gray g st /\
  stack_no_dups st
```

The theorem structure proves that bounded marking produces the same heap colors
as the unbounded mark, despite using a finite stack. The implementation then
uses the bounded variant in the top-level `collect` contract.

### Incremental marking

Incremental marking runs the mark step a few objects at a time with the
program running in between. The spec core (milestone M1 of the
incremental-mark plan) comes first; the `Marking` phase and black allocation
(M2), the verified write barrier (M3), the mark slices in Pulse (M4),
allocation while marking with the bridge that interleaves the slices with the
program (M5), and the cycle's completeness and safety theorems (M6) follow
below. The mark stack stays an
implementation cache: the spec state is the heap's colours alone.

**The step at any grey object** (`GC.Spec.MarkPhase.mark_step_at g x`):
blacken `x` and grey its white children, resolved through infix headers (a
no-scan object has none). The stop-the-world `GC.Spec.Mark.mark_step` is the
instance at the top of the stack (`mark_step_heap`), so the implementation's
step, whichever grey object it pops, is covered.

**Reachability through a predicate** (`GC.Spec.Graph.Within`). `reach_within e
p x y`: a path from `x` to `y` along the relation `e` whose every vertex
satisfies `p`. Generic in the relation, so it serves `graph_state` and a
relation read off the heap alike. Its lemmas are what colour and edge changes
need: a larger predicate and more edges keep paths (`reach_within_mono`); the
part of a path from any vertex on it is a path (`reach_within_suffix`); taking
`u` out of `p` breaks only paths through `u`, and each restarts after its last
visit at a successor of `u` (`reach_within_without`); deleting the edge `u ->
v` breaks only paths using it, and each restarts at `v`
(`reach_within_edge_removed`); and the general form, where every broken edge
ends at a vertex satisfying `q` (`reach_within_restart`).

**What the marker will reach.** `field_edge g x y`: `y` is what a pointer field
of the scannable object `x` points at, resolved (the edges of `create_graph`
are among these). `marker_will_reach g w`: `w` is reachable from a grey object
along a path of grey or white blocks. The marker will scan every object on such
a path. A path through a black object does not count: the marker never scans a
black object again, so a path "reachable from some grey object through
anything" can be cut for good by a single step. `GC.SPOT.MarkPhase` has the
counterexample: grey `G -> B`, black `B -> W`, `W` white; `W` is reachable from
`G`, but the step at `G` greys nothing (its only child is black) and leaves no
grey object, with `B -> W` still a black-to-white edge.

**The invariant, parameterised by what is held from outside.**

```fstar
let marking_inv (g: heap) (held: obj_addr -> prop) : prop =
  well_formed_heap g /\     (* free means blue: marking frees nothing *)
  weak_tri_color g /\       (* every white object a black one points at: marker_will_reach *)
  held_reached g held       (* every white object held from outside: marker_will_reach *)
```

`held w` says something outside the major heap points at `w` (resolved). The
generational layer will instantiate it with the program's roots and the
targets of the nursery's fields, so the mark-and-sweep spec stays independent
of the nursery and of the program.

- **Start** (`marking_inv_start`): no black object points at a white one (with
  no black object at all, `no_black_tri_color`), and every held object is
  darkened.
- **Step** (`marking_inv_step`): the step at any grey object keeps it.
  Greying `x`'s children keeps every grey-or-white path; blackening `x` breaks
  only paths through `x`, and each restarts at the child it went through,
  which the step has just greyed (`reach_within_without`). Nothing becomes
  white, and the walk, the edges and well-formedness are unchanged
  (`mark_step_at_objects`, `_wf`, `_dense`, `_blue`).
- **End** (`marking_done`): with no grey object the marker will reach nothing,
  so clause 1 is the strong tri-colour invariant and clause 2 says no held
  object is white: the heap is `FusedSweep.End.marked`, where the sweep
  starts. `marking_done_sweep_start` hands it to
  `sweep_inv_incremental_start` with the walk facts and the free list.
- **Other changes** (`marking_inv_change`): any heap change that keeps grey
  objects grey and grey-or-white blocks grey or white, makes no object white,
  greys the target of every edge between non-black blocks it cuts, and adds
  black-to-white edges only to objects the marker would already reach (and
  white held objects only among those held or reached before). Greying a white
  object, the barrier's darkening, is an instance (`marking_inv_grey`).

**Field writes** (`GC.Spec.MarkPhase.Mutator`, milestone M2a).  A write of
`v` into a body word `a` of a non-free, non-closure object `x` keeps the walk
and every header (`write_heads`) and well-formedness when `v` is storable
(`write_wf`); only `x`'s edges change.  Every other block keeps its edges
(`write_edges_other`); an edge of `x` afterwards is an old one or goes to
`v`'s target (`write_edges_new`); an old edge is kept or went to the old
value's target (`write_edges_old`).  Resolution of a pointer stored in a
non-free block survives because its header is a walk position or an infix
header inside a closure, never a body word of `x` (`target_header_away`).
From these, as an instance of `marking_inv_change`:

- `marking_write`: the invariant survives when the old value's target is not
  white and the new one's is not white, or held, or one the marker will reach
  (`target_ok`); `held` is unchanged.  Writing an immediate is the instance
  with no new target (`marking_write_immediate`).
- `marking_write_barrier`: 4.14's `caml_modify` while marking, `darken` (4.14's
  `caml_darken`) of the old value and then the write; the old value may be
  anything.  `GC.SPOT.MarkPhaseWrite` shows the darkening is what keeps it.
- `marking_load`: a field of a held object, loaded, may be held too.  That is
  why clause 2 stays true of the program's roots (the trusted obligation of the
  plan's option (a)): the program obtains pointers only by loading fields of
  objects it holds, or by allocating.

**The `Marking` phase** (M2b).  `gc_phase` has a `Marking` case, with black
allocation; the record's `ps_kind` is 2 (the C bridge's `vergc_sweeping()` is
`ps_kind == 1`, and `vergc_allocation_color` is black while marking).  At
`Marking`, `GC.Gen.Incremental.phase_shape` is the minor collection's shape at
`free_stw` (marking frees nothing) and `marking_inv g (GC.Gen.MarkPhase.Minor.nursery_held minor)`:
what the nursery's major pointers point at is held.  The program's roots are
the other half of `held`; they are not part of the collector's state
(`gc_state` has no roots), so the entry points that take roots will state
`held_reached` of them (the plan's option (a)).  `start_cycle` enters
`Marking` and `major_slice` marks there (M4, below).

**Allocation while marking** (`GC.Spec.MarkPhase.Alloc`, M2c).  A new
object is black, and its fields are what the free block held until the
runtime initialises them.  As the sweep's `fresh_ok`, the invariant then
holds with the object *fresh* (`marking_fresh g held obj`): well-formedness
counts it as free (`free_or_new obj`: nothing points at it, its fields are
unconstrained) and the weak tri-colour clause skips it as a source
(`fresh_tri_color`); being black, it lies on no path the marker follows, so
its fields do not affect what the marker will reach.

- `marking_alloc`: first-fit at `Marking` from an ascending list leaves the
  invariant with the new object fresh; it frees nothing (`keeps_blocks`:
  every non-free block keeps its header and fields), keeps the list
  ascending, and the new object was not a non-free block before.
- `marking_fresh_write`: writes into the fresh object's body keep it fresh.
- `marking_fresh_close`: once every field is storable and its target not
  white, held, or one the marker will reach (`fields_ok`; a value the program
  holds), `marking_inv` holds.
- For the minor collection's generic theorem, a block allocated at `Marking`
  is not free under `free_stw` (`GC.Gen.Promote.free_stw_allocations_not_free`,
  any phase: black is not blue).

The frame lemmas `keeps_blocks_resolve`/`_edges`/`_reach` are about any change
that keeps every non-free block, for any admissible definition of free.

**Minor collection while marking** (`GC.Gen.MarkPhase.Minor`, M2d).  At
`Marking` the collection runs with `free_stw`; its promoted copies are black.
Before it, `held` is the roots and the nursery's major pointers
(`marking_held minor g roots`); after it, with the nursery empty, the
rewritten roots (`roots_held g' roots'`).  `minor_keeps_marking_inv` is an
instance of `marking_inv_change`:

- every non-free block stays with its header (`old_block`) and its pointer
  fields -- the update rewrites only nursery pointers, which never look like
  major pointers (`old_pointer_field`) -- and their targets keep their
  resolution (`old_target`); so no edge between grey or white blocks is cut,
  and no colour changes;
- every other non-free block is a promoted copy, black (`new_block_black`,
  via the generic theorem at the definition of free "not black", whose
  allocations at `Marking` are not free);
- a black object's white target is one the marker would reach.  This is the
  invariant read as well-formedness: `GC.Spec.MarkPhase.unreached g` (free =
  blue, or white and not reached) is an admissible definition of free, and
  `marking_inv g held` makes `g` well formed for it (`marking_inv_unreached`)
  when the nursery's pointers are held.  The generic theorem keeps
  well-formedness for it (its allocations are black), and the pointer update
  at `free_stw` agrees with the one at `unreached g` on every block the
  latter keeps (`update_agrees`), so the heap after is well formed for
  `unreached g` (`unreached_wf_after`), which is the condition
  (`unreached_black_edge`).  This covers the copies' fields and the
  remembered slots without looking at them;
- a rewritten root is the old one, held before, or a forwarded copy, black
  (`rewritten_root`).

`GC.Gen.Incremental.minor_keeps_marking_shape` lifts it to `phase_shape` at
`Marking`, and `minor_collect` runs at `Marking`: `minor_slots_ok` asks, at
`Marking`, that the roots be held (`MP.held_reached s (GMM.roots_held s
rs)`), and `minor_collect` gives the same of the rewritten roots.

#### The write barrier (M3)

4.14's `caml_modify (fp, val)` for a major slot: `old = *fp; *fp = val;` while
marking, darken `old` (`caml_darken`); if `val` is a nursery block and `old`
was not, add `fp` to the ref table.  `caml_initialize` writes and remembers
the slot when `val` is young, without darkening.  Both are now verified, and
every phase's state is kept by them.

**The persistent mark state.**  `gen_heap_t` gains `mark_stack` (a
`gray_stack`) and `mark_overflow` (a `bool` reference), allocated once by the
bridge at heap set-up, empty with the flag down.  `GC.Gen.Impl.mark_state gh
s ph` owns them, and `gc_state` includes it.  Like the sweep's caches they are
an implementation cache of the heap's colours
(`GC.Gen.MarkState.mark_cache_ok`):

- while marking, every stack entry is a grey object, and while the flag is
  down every grey object is on the stack;
- at any other phase the stack is empty and the flag down (nothing is grey
  then either, but that is `phase_shape`'s).

Every entry point keeps it: outside marking it says nothing of the heap
(`mark_cache_off`), and a minor collection while marking keeps the grey
objects (`GC.Gen.MarkPhase.Minor.minor_keeps_greys`: an old non-free block
keeps its header, a new one is a black copy).  M4 extended the cache with the
partly scanned object and the rescan cursor, and the stack entries may be
black (below, "The mark slice").

**The spec** (`GC.Gen.Barrier`):

- `modify_ok ph minor g x a v` (the trusted program obligation):
  `SPM.program_write (phase_free ph) g x a v` (a body word of a non-free block
  that is not a closure, a storable value), `scannable g x`, and while marking
  `MM.target_ok g (nursery_held minor) v` -- the program holds `v`, so if it
  is white the marker will reach it (the roots obligation, option (a));
- `modify_heap ph g a v`: while marking `write_word (MM.darken g (read_word g
  a)) a v`, otherwise `write_word g a v`;
- `modify_records g a v = is_young v && not (is_young (read_word g a))`;
- `modify_phase_shape`: `phase_shape` is kept at every phase.  Idle it is a
  new lemma for `collection_heap_shape` (the stop-the-world code never had
  program events in its spec): `MM.write_wf` for well-formedness, the walk,
  the headers and the list from `SPI.body_write`, density from the walk, the
  colour facts from the headers; mid-sweep `SPM.write_sweep_phase`; while
  marking `MM.marking_write_barrier` and the minor collection's shape at
  `free_stw` across the darkening (greying a white block keeps the walk, the
  free-list cells and their links) and the write;
- `modify_ref_table` / `initialize_ref_table` (both from `write_ref_table`):
  if the table covered every nursery pointer of a non-free scannable block and
  named only fields of such blocks, then with the slot appended exactly when
  the barrier says so (`appended`) it still does, for the phase's definition
  of free.  The young-over-young case relies on the slot being in the table
  already (coverage); darkening touches no field.  So
  `RT.ref_table_covers_with` / `ref_table_sound_with`, which `minor_slots_ok`
  asks the bridge for, follow from "the bridge appends iff the barrier
  returned true", for the writes; what is left trusted is that every field
  of a block allocated in the major heap is initialised (through
  `caml_initialize`, or a raw store of a value that is not young) before the
  next minor collection, since a fresh block's garbage fields are not
  covered;
- `modify_mark_cache`: the darkened block is pushed, or the flag raised when
  the stack is full (whether or not there was a block to push: a raised flag
  only costs a rescan).

**The implementation** (`GC.Gen.Impl.Barrier`, extracted into
`GC_Gen_Impl.c`): `modify_field ghr slot v` and `initialize_field ghr slot v`
take the collector's record by reference (`ghr`, the bridge's
`&gc_gen_heap`), so the call copies one word.  `modify_field` reads the old
value and the phase record, and while marking (`ps_kind >= 2`, as
`phase_of`) calls the out-of-line `darken_via` (the stop-the-world mark's
`check_and_darken_bounded`, which resolves infix pointers, preceded by the
overflow flag update; `darken_spec_eq` says it is `MM.darken` with the push);
then it writes and returns `young v && not (young old)`.  The common path
(not marking) is about twenty instructions.

**The bridge and the runtime.**  The patched `caml_modify` writes a nursery
slot directly (no barrier is needed there, as 4.14), calls `modify_field` for
a slot of the verified major heap, and for any other slot (native code's
static data) keeps the stock logic without darkening (`vergc_modify` in
`alloc_gen.c`); it calls `add_to_ref_table` exactly when the barrier returns
true.  `caml_initialize` is the same with `initialize_field`, and
`caml_array_fill`'s copy of the barrier goes through `vergc_modify`.

**Cost.**  `caml_modify` was already an out-of-line call; the verified one
adds a range check and one more call.  On a loop that only stores into a
major array (native, 300M stores) it costs about 1-1.4 ns more per store than
stock's barrier (0.55 s -> 0.88 s storing immediates, 1.34 s -> 1.77 s
storing fresh young boxes); in bytecode about 10%.  On the mark benchmarks
it is within noise: binarytrees 16 (bytecode 8.49 s -> 8.47 s, native 7.14 s
-> 7.14 s), livemap 1000000 1 (12.75 -> 12.82 s, 11.87 -> 11.69 s),
livegraph 1000000 4 4 (3.69 -> 3.77 s, 2.26 -> 2.38 s; ranges overlap), where
the barrier is about 1% of the run (`perf`: `modify_field` 0.6-0.9%, as
stock's `caml_modify` was 0.8% of livemap).

**Left** (after M4): the allocation entry points that would carry
`marking_alloc`/`_fresh_*` to the implementation, with the generational
shape across a direct major allocation.

#### The mark slice (M4)

`start_cycle` darkens the roots onto the persistent mark stack and enters
`Marking`; `major_slice` at `Marking` is a **mark slice** (OCaml 4.14's
`mark_slice`): it scans about `budget` words and stops, and when nothing is
grey it starts the sweep.  The budget counts a header for each entry popped
and each block the rescan walks, and a word for each field scanned;
`UINT64_MAX` is unbounded.

**What a slice does to the heap** (`GC.Spec.MarkPhase.Slice`).  An object
larger than what is left of the budget is scanned in parts, so a slice is a
sequence of two kinds of moves on the colours:

- **scanning a field** (`grey_move`): the target of a field of a grey,
  scannable object is greyed if white (`MM.darken`); the object stays grey;
- **blackening** (`black_move`): a grey object whose fields are all *dark*
  (`fields_dark`: no field points at a white block), or that has no fields
  to scan, becomes black.

The marking invariant survives each move: scanning a field is greying a white
block (`MM.darken_inv`), and blackening an object whose fields are dark *is*
the stop-the-world step at it (`black_move_is_step`: `push_children` finds no
white child), which keeps it (`MP.marking_inv_step`).  `mark_steps g g'` is
any number of moves; it keeps `marking_inv` for every `held`
(`mark_steps_inv`), changes nothing but colours, only darkening them
(`darker`), and lowers `mark_weight` (two per white block, one per grey) at
every move that changes the heap.

Blackening asks that *every* field be dark, not only those scanned in the
slice that finishes the object.  A field scanned in an earlier slice may have
been overwritten since: the program may store a white object `w` that, once
the program drops its own reference, only the partly scanned object reaches
(through a field it has already scanned); blackening the object without
looking at that field again would leave a black-to-white edge to an object
nothing will mark.  The implementation keeps "the fields scanned so far are
dark" in its cache (`cur_ok`), and the **write barrier restarts the scan**
when the program writes into one of them (`MS.reset_cur`: two compares and a
store, only while marking).  4.14 does not need this because its marking is
snapshot-at-the-beginning and its partly scanned objects are black; ours is a
per-edge invariant with grey partly scanned objects.  A minor collection
keeps the scanned fields dark (`GMM.minor_keeps_field_dark`: a major pointer
field is unchanged, a rewritten one points at a black promoted copy).

**The mark cache** (`GC.Gen.MarkState`, `mark_cache_ok g ph st ov p`), while
marking:

- the stack holds grey or black blocks (`entry_ok`: a rescan may push an
  object already on the stack; the slice skips an entry no longer grey);
- the partly scanned object `p.cur` (0 for none) is a grey scannable block
  whose fields before `p.fld` are dark (`cur_ok`);
- the rescan cursor `p.rc` (0 for none) is the start of the heap or the
  header of a block that is not free (`rescan_at`: allocation and promotion
  split only free blocks, so this stays a position of the walk);
- every grey object is on the stack, or the partly scanned object, or the
  overflow flag is up, or a rescan is in progress and it lies after the
  cursor (`covered`).

With the stack empty, nothing partly scanned, no rescan and the flag down,
nothing is grey (`marking_cache_done`).  It is kept by the barrier's
darkening and write (with the restart), the initialisation of a fresh block,
a minor collection, root darkening (`GC.Gen.MarkSlice.mark_cache_start`: the
roots are pushed while the stack has room, and the flag goes up if it ends
full), and the slice's steps (`GC.Gen.MarkSlice`).

**The slice** (`GC.Gen.Impl.MarkSlice.mark_slice`, Pulse) repeats, while there
is budget:

- resume the partly scanned object: scan its fields from `p.fld` (each
  pushes the greyed target, or raises the flag when the stack is full --
  exactly then, not whenever the stack is full) and, if the budget covers the
  rest, blacken it; otherwise scan what the budget allows and leave it;
- pop an entry: a grey object with fields becomes the partly scanned object,
  one without (no-scan or empty) is blackened, a black one is skipped;
- with the stack empty and a rescan in progress, walk the blocks from the
  cursor pushing the grey ones, until (after at least one block) the stack is
  a quarter full (4.14's `redarken_chunk`) or the budget is spent, at a block
  that is not free, or the heap ends (then the rescan is over);
- with the stack empty and the flag up, start a rescan: flag down, cursor at
  the start of the heap -- a drop while the rescan runs raises the flag again,
  so the rescan restarts once it ends;
- otherwise marking is over.

**Termination.**  Every step lowers, lexicographically, the mark weight, the
flag, how far the rescan has to go, twice the stack plus the partly scanned
object, and the partly scanned object's fields left
(`GC.Gen.MarkSlice.slice_measure`), so the loop terminates whatever the
budget, and an unbounded slice (which never stops for budget) ends only when
marking is over.  That is what lets `full_gc` mark with one slice.

**The contract.**  `major_slice` at `Marking` ensures `GI.mark_slice_post`:
the heap is some mark moves away, the free list untouched, and the phase is
`Marking` or, with nothing grey, `Sweeping zero_addr`; an unbounded budget
leaves `Sweeping zero_addr`.  `GI.mark_steps_shape` keeps `phase_shape` at
`Marking` (the moves recolour among white, grey and black, so the walk, the
free list and the cross-generation condition are kept), `GI.mark_steps_roots`
keeps the roots held, and `GI.marking_done_shape` is the hand-over: with
nothing grey, `MP.marking_done_sweep_start` gives the sweep phase at the
first block, and what the nursery holds is not white, so not pending free.

**Stop-the-world** (`full_gc`) runs the same slices with no program between
them, and the strengthened invariant (`GC.Spec.MarkPhase.Stw`) recovers the
marked heap the end-to-end theorems start from (below, "How `full_gc`'s
contract is proved").

**Cost** (stop-the-world, before = the M3 runtime marking with
`mark_loop_bounded_flagged`, after = mark slices; user-space instructions and
cycles from `perf stat`, the machine loaded, wall-clock ranges overlapping):
binarytrees 16 bytecode 124.5G -> 127.0G instructions, 38.8G -> 36.6G cycles;
native 90.3G -> 86.4G, 29.9G -> 31.0G (on a quieter machine 6.42 s -> 6.40 s);
livemap 1000000 1 82.6G -> 83.1G, 60.7G -> 58.2G; livegraph 1000000 4 4
20.5G -> 21.0G, 18.9G -> 15.9G.  The first version of the slice cost about
twice the mark instructions (+15% on native binarytrees): every popped object
went through the partly-scanned cells and a second loop iteration, and every
field called the darkening and `is_full`.  The slice now scans and blackens a
popped object at once when the budget covers it, tests `is_pointer` before
calling the darkening, and has the darkening report a drop itself.

#### Allocation while marking, and the bridge (M5)

**Allocation while marking** (`GC.Gen.MarkPhase.Alloc`).  The bridge
allocates in the major heap with `GC.Impl.Allocator.allocate` at the
record's phase, whose postcondition is `AC.alloc_phase g fp ph wz tag`; at
`Marking` the new block is black.  `GC.Spec.MarkPhase.Alloc` said what that
does to the marking invariant; M5 carries it up to the collector's state
`GI.phase_shape ... Marking`, which also holds the generational shape
`collection_shape_with Marking free_stw` (left open in M2):

- `marking_alloc_shape`: from `phase_shape ... Marking`, either nothing
  changed or the new block, of the requested size and tag, is *fresh*:
  `fresh_shape minor g fp obj` -- the nursery's shape, the cross-generation
  condition, density, the ascending list, and `MPA.marking_fresh` (the
  marking invariant with `obj` black and its fields exempt: well-formedness
  counts it as free, the weak tri-colour clause skips it as a source);
- `fresh_shape_write`: writes into its body keep it fresh;
- `fresh_shape_close`: once its fields are storable and, if white, held
  (`MPA.fields_ok`), `phase_shape ... Marking` holds again;
- `alloc_mark_cache`, `fresh_mark_cache_write`: the mark cache is kept --
  the allocation splits only free blocks and keeps every non-free one with
  its header and fields (`MPA.alloc_in_use`,
  `GC.Gen.MarkState.mark_cache_keeps_blocks`), and the new block is black, so
  the grey objects, the stack's entries, the partly scanned object's dark
  fields and the rescan cursor are as they were.

The trusted part is the same "fresh block initialised before the next
collector call" obligation as at the other phases (GC.Gen.Impl's trust
boundary): the runtime initialises every field with a value it holds before
anything else touches the heap.  Until then the leftover fields bind nothing,
the remembered set's coverage included.

**The bridge.**  `VERGC_MAJOR=incremental` (OCAML_INTEGRATION.md, "The Major
Mode") follows 4.14: after each minor collection, at Idle `start_cycle` when
the trigger fires (the nursery is empty right then), otherwise one
`major_slice`.  The trigger matters only at Idle (space_overhead on an
estimate of the live words, a heap-fraction safety net, and a slow
minor-allocation clock); mid-cycle, memory pressure makes slices bigger, and
a cycle is finished at once only for a full collection, a failed allocation,
or a minor collection that might not find room to promote.  The pacing ports
`caml_major_collection_slice`: the share of the cycle a slice does is the
words allocated since the last slice over two thirds of the free memory when
the cycle started (capped at 0.3, with a backlog, smoothed over
`caml_major_window`), 40% of the cycle marking the words in use and 60%
sweeping the heap.  The live-words estimate needs the words the cycle
marked: the mark slice adds the size of every block it blackens to a counter
(`gen_heap_t.mark_words`, in `mark_state`, zeroed by `start_cycle`), an
unspecified number for the bridge -- nothing is claimed of it.

**Testing.**  `tests/incremental_mark.ml` mutates heavily while marking and
is compared with stock OCaml byte for byte under three pacings; with small
slices marking spans about a thousand slices with a minor collection, and
barrier calls, between each two (`VERGC_MAJOR_STATS`).  Disabling the
barrier's darkening in the bridge makes it fail.

**Measurements.**  stop-the-world against incremental on binarytrees 16/18, livemap and livegraph: OCAML_INTEGRATION.md, "The Major Mode", "Measurements".  The largest mark or sweep slice is 1-4 ms on binarytrees (stop-the-world collections: 45-495 ms), 14 ms on livemap (191 ms), 64 ms on livegraph (232 ms, few minor collections, so large slices); wall time +0-10% on binarytrees, +7-16% on livemap, +27-37% on livegraph (7 cycles against 4).

#### The cycle's theorems (M6)

Two statements about a whole incremental cycle -- `start_cycle`, mark
slices, the hand-over to the sweep, sweep slices, and the program's events
in between -- the incremental counterparts of the stop-the-world end-to-end
theorems.  Spec only: no entry point's contract changes.

**Completeness** (`GC.Spec.MarkPhase.Completeness`, and
`GC.Gen.MarkPhase.Completeness` for the generational events): *an object
unreachable from the roots when the cycle starts is freed by the end of the
sweep, unless its address was handed out again since* (an allocation, or a
minor collection's promotion).  The marking invariant is intrinsic and says
nothing about the heap marking started from, so completeness is carried
separately, as an **account** indexed by a ghost set `s` of addresses: those
reachable when the cycle started (`MPC.reachable g held`: along
`MP.field_edge` from what the roots hold), and those allocated or promoted
since.  While marking (`MPC.mark_account s g`):

- every grey or black object is in `s` (`dark_accounted`);
- the heap is well formed for the definition of free `unaccounted s` (blue,
  or white and outside `s`): a non-free block that is dark or in `s` points
  only at blocks that are dark or in `s`.  This is the closure of `s` under
  the heap's edges, stated as well-formedness so that the minor collection's
  generic theorem keeps it (as M2d's `MP.unreached`).

So an object outside `s` is never greyed: a mark step greys targets of
fields of grey objects (dark, so accounted), and the barrier greys the old
value of a field of the object the program writes, which the program can
reach (accounted).  Each event keeps the account, a per-event family like
the sweep's `survivor_or_new_*`:

| event | lemma | `s` afterwards |
|---|---|---|
| root darkening (`start_cycle`) | `GMC.cycle_start`, from `MPC.account_start` | the objects reachable from the roots in the heap `start_cycle` starts from (`GMC.reachable_at_start`) |
| mark moves (a mark slice) | `MPC.account_move`, `account_steps` | unchanged |
| the barrier write while marking | `MPC.account_barrier` (darken the old value, `account_darken`; then the write, `account_write`) | unchanged |
| allocation while marking | `MPC.account_alloc`, `account_fresh_write`, `account_fresh_close` | the new object added (`SPC.with_new`) |
| minor collection while marking | `GMC.account_minor` (`GMM.minor_keeps_wf_with`, the generalised `unreached_wf_after`) | the promoted copies added (`with_new_blocks`: the blocks that were not blocks before, black by `GMM.minor_new_block_black`) |
| hand-over (nothing grey) | `MPC.cycle_handover` | unchanged: every block not free at the start of the sweep is black, so in `s` |
| sweep slices | `MPC.cycle_sweep_slice` | unchanged |
| allocation / write mid-sweep | `MPC.cycle_sweep_alloc`, `cycle_sweep_write` | the new object added |
| minor collection mid-sweep | `GMC.sweep_minor` | the promoted copies added (`GSC.with_promoted`) |

At the collector's phase this is `MPC.cycle_account s g ph`: the mark account
while marking; mid-sweep `sweep_accounted` (every block not free for
`free_incremental c` is in `s` -- the sweep's `survivor_or_new` with the
survivors of marking folded into `s`); idle, every block that is not blue is
in `s`.  At the entry points: `GMC.cycle_slice` (any `major_slice`, from
`GI.major_slice_post`), `GMC.cycle_modify` (the barrier at every phase).
The theorem is the idle form (`MPC.cycle_complete`,
`GMC.cycle_frees_unreachable`): every address outside `s` -- unreachable
when the cycle started and not allocated or promoted since -- is freed
(`SPC.freed`: no block there, or a free block).

**The trusted obligation it adds.**  The account needs the program's writes
to stay inside `s`: `MPC.cycle_write s g x a v` -- `SPM.program_write` at
`unaccounted s` (the program writes a body word of an object it can reach,
and stores a value it holds: both in `s` or dark) and `x` scannable.  This
is the marking invariant's roots obligation (the plan's option (a)) read
against the cycle's start: OCaml's type safety -- the program obtains
pointers only from its roots, by loading fields of objects it holds
(`MPC.account_load`: a field of an accounted object is accounted), and by
allocating (added to `s`).  It is not in `GB.modify_ok`: the completeness
theorem takes it as a hypothesis (`GMC.modify_accounted`) of the writes it
covers, as it takes the nursery half for minor collections while marking
(`minor_major_fields_not_free (unaccounted s)`: what the nursery holds is
accounted for).  Nothing at runtime depends on it.

**Safety** (`GC.Gen.MarkPhase.Safety`), stated once for every phase
(`GI.phase_shape`, with `GI.phase_free ph`: blue idle or marking, blue or
pending free mid-sweep):

- `cycle_reachable_not_free`: every object reachable from the roots through
  the nursery and the major heap (the combined graph at `phase_free ph`) is
  a real block, not free at the phase -- the sweep's
  `reachable_not_free_combined` at every phase, via the generic
  `RBridge.reachable_not_free`.  The roots must be non-free at the phase;
  across the hand-over they are (`handover_roots`: with nothing grey every
  root is black, as the roots are held);
- the collector's own moves leave the blocks alone: root darkening is a
  recolouring (`start_keeps_blocks`), a major slice keeps every non-free
  block with its size, tag and fields and non-free at the phase it leaves,
  except the white blocks the hand-over finds (pending free: unreachable)
  (`cycle_slice_keeps`, from `MPC.mark_steps_keep_blocks` and
  `SL.sweep_slice_phase`), so a slice never changes a reachable object
  (`slice_keeps_reachable`); a minor collection while marking keeps every
  non-free block's header and its fields pointing into the major heap
  (`GMM.minor_keeps_block`, `GMM.minor_keeps_major_field`) and rewrites the
  nursery pointers through the forwarding map (the isomorphism of
  `minor_collect_post_with`);
- a program write through the barrier changes only the written word: every
  other non-free block keeps its size, tag and fields, stays non-free and
  does not become white (`modify_keeps_others`).

**The SPOT** (`GC.SPOT.IncrementalCycleTheorems`, on the heap of
`GC.SPOT.CycleHeap`: `A -> B`, `B`, `U -> A`, `C`, roots `[A; C]`, an empty
nursery, the idle state proved for it): `minor_collect` (the empty nursery
changes nothing), `start_cycle`, a 64-word slice, a barrier write of an
immediate into `A`'s field (cutting `A -> B`), and two unbounded slices to
`Idle`; then `U`, unreachable at the start, is freed, and `C` survives with
its size, tag and field.

**Not done**: an event-list theorem (induction over the program's and the
collector's events between collector calls, with the obligations as
hypotheses on the list).  It needs the nursery's own events (allocation and
writes into nursery objects, which the spec does not model as events) to
state the minor collection's obligation, so the per-event lemmas are
composed by hand, as the SPOT does.

## The minor collector

The generational collector adds a nursery. The nursery is modeled separately
from the major heap:

- Major heap: the OCaml-style heap from `common/`, with `zero_addr`,
  byte-addressed objects, colors, free-list blocks, and mark-and-sweep.
- Minor heap: a bump-pointer array of bytes with offset-based addresses.
- Promotion: live minor objects are copied into the major heap using the
  verified major allocator.
- Forwarding: a map records each minor object's new major address.
- Root rewriting: roots that pointed into the minor heap are rewritten to major
  addresses.
- Remembered slots: major fields that contain minor pointers are rewritten using
  the same forwarding map.

`generational/spec/GC.Gen.Base.fst` fixes the default verification constants:

```fstar
let minor_heap_size : n:pos{n % 8 == 0 /\ n >= 16 /\ n < pow2 57} = 2048
let minor_heap_size_u64 : n:U64.t{U64.v n == minor_heap_size} = 2048UL

let max_young_wosize : n:pos{n >= 1 /\ (n + 1) * 8 <= minor_heap_size} = 128
let max_young_wosize_u64 : n:U64.t{U64.v n == max_young_wosize} = 128UL

let minor_base_addr : U64.t = 0UL
```

The OCaml bridge overrides these runtime constants for a production-sized minor
heap, but the proofs are parameterized around the constraints that matter:
alignment, bounds, and disjointness from major addresses.

### Minor heap shape

The bump-pointer minor heap is specified in
`generational/spec/GC.Gen.MinorHeap.fst`. Allocation writes a header at the bump
pointer, returns the object address one word later, and advances the bump:

```fstar
let minor_alloc_spec (ms: minor_state)
                     (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                     (tag: nat{tag < 256 /\ tag <> 249})
  : Tot minor_alloc_result =
  if not (minor_can_alloc ms wosize) || U64.v ms.bump % 8 <> 0 then
    { ms_out = ms; obj_addr = 0UL }
  else
    let hdr = make_minor_header wosize tag in
    let new_bump = U64.v ms.bump + (wosize + 1) * 8 in
    let data' = minor_write_word ms.data ms.bump hdr in
    let obj_offset = U64.v ms.bump + 8 in
    { ms_out = { data = data'; bump = U64.uint_to_t new_bump };
      obj_addr = U64.uint_to_t obj_offset }
```

The generational heap invariant is centralized in
`generational/spec/GC.Gen.HeapInvariant.fst` (all three predicates are opaque,
with intro/elim lemmas in the interface):

```fstar
let major_heap_shape (major: heap) (fp: U64.t) : prop =
  well_formed_heap major /\
  AllocLemmas.fl_valid major fp heap_words /\
  AllocLemmas.fl_chain_terminates major fp heap_words /\
  free_list_exact major fp /\          // the free list is exactly the blue blocks
  FLA.fl_ascending major fp /\         // ... in address order
  FreeListShape.fp_pointer_or_zero fp /\
  FreeListShape.blue_link_fields_valid major /\
  heap_objects_dense major /\
  chain_objects_blue major fp /\
  Seq.length (objects zero_addr major) > 0 /\
  SweepInv.fp_valid fp major /\
  GC.Spec.FreeList.fp_in_heap fp major /\
  Mark.no_black_objects major /\
  SweepInv.no_gray_objects major

let minor_heap_shape (minor: minor_state) : prop =
  minor_wf minor /\
  minor_guards_complete minor /\
  minor_infix_wf minor

let collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop =
  major_heap_shape major fp /\
  minor_heap_shape minor /\
  minor_major_fields_no_blue minor major
```

`collection_heap_shape` is the stop-the-world invariant: `full_gc` requires it
and restores it.  Its generic form, for a definition of free, is
`collection_shape_with ph free` (below).  Interior (infix) pointers are allowed
in live fields of both heaps: the pointer clauses of `well_formed_heap` are
stated on the resolved target, and Cheney forwards an interior nursery
address to the corresponding interior address of the promoted closure
(`GC.Gen.CheneyBFS.fwd_covers_infix_fields`).  There is no no-scan clause:
the nursery scan window (`minor_scan_wosize`) is 0 on a no-scan block, and a
no-scan major block is not `scannable`, so nothing is assumed about raw data.

### Remembered slots

A generational collector must not scan the entire major heap on every minor
collection. Instead, the write barrier records major fields that may contain
minor pointers. The specification has no whole-heap scan of its own either: the
combined-graph reachability bridge (`GC.Gen.ReachabilityBridge`) uses the slot
coverage directly at a major-to-nursery edge, through the pure predicate
`major_fields_covered` ("every live nursery pointer stored in a scannable
non-blue major field is in the Cheney roots"), which
`MinorCollectForwarding.Helpers.major_fields_covered_from_slots` derives from
the two slot facts below.

The implementation does not rescan the major heap during minor collection. It
uses OCaml's `ref_table`, populated by `caml_modify`, as the concrete remembered
slot table. The proof obligation is therefore not merely that remembered slots
are well-formed, but that they cover all major-to-minor pointers relevant to the
collection:

```fstar
RT.ref_table_sound 's 'sl (SZ.v nslots) /\
RT.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots)
```

Those facts appear in the preconditions of `full_gc` and
`minor_collect_pre_idle`.  The slot predicates live in the spec module
`GC.Gen.RefTable` (`RT`), stated for any definition of free; the stop-the-world
forms above are their instances at `free_stw`:

```fstar
let ref_table_sound_with (free: free_def) (major_pre: heap)
                         (slots: seq U64.t) (n: nat) : prop =
  n <= Seq.length slots /\
  (forall (i: nat). i < n ==>
    (let addr = U64.v (Seq.index slots i) in
     addr < heap_size /\ addr % 8 == 0 /\
     (exists (obj: obj_addr) (j: nat).
       is_block major_pre obj /\ not (free major_pre obj) /\
       scannable major_pre obj /\
       j < U64.v (wosize_of_object obj major_pre) /\
       addr == U64.v obj + j * 8)))

let ref_table_sound (major_pre: heap) (slots: seq U64.t) (n: nat) : prop =
  ref_table_sound_with free_stw major_pre slots n
```

`ref_table_covers_with free` says every nursery pointer held by a field of a
non-free, scannable block is at a slot.  Soundness says every slot is a field
of a non-free, scannable block.  It holds because the table is emptied at
every minor collection and an entry is recorded only when the program writes a
field, so the object was reachable after the last minor collection; such an
object is never about to be freed, since marking starts right after a minor
collection and, under a deletion barrier, anything written during marking ends
black.

The slots need not be distinct.  `caml_modify` records a field again when it
goes from a nursery pointer to an immediate and back (the second write sees an
immediate old value), and nothing deduplicates the table.  Repeats are
harmless: the slot rewrite forwards a slot only if it holds a forwarded
nursery pointer, and the value it writes is a major address that is not one
(`fwd_targets_stable`), so every later occurrence of the same slot leaves it
alone.  `GC.Gen.TwoPassEquiv.rewrite_slots_iter_slot_effect` states this for an
arbitrary slot sequence; `spot/GC.SPOT.DuplicateSlot` runs `minor_collect`
with a table that lists the same field twice.

### Promotion and forwarding

Promotion is specified in `generational/spec/GC.Gen.Promote.fsti`. The central
abstraction is the forwarding map:

```fstar
/// A forwarding map records where each minor object was placed in the major heap.
/// It maps minor_obj_addr -> major_obj_addr (or 0 if not promoted).
let forwarding_map = U64.t -> GTot U64.t

let empty_forwarding : forwarding_map = fun _ -> 0UL

let extend_forwarding (fwd: forwarding_map) (minor_addr: U64.t) (major_addr: U64.t)
  : forwarding_map =
  fun a -> if a = minor_addr then major_addr else fwd a
```

`promote_object` copies one object.  Promotion is just allocation with the
minor object's tag, at the collector's phase, followed by the field copy; the
copy's header is written once, by the allocator, with the phase's colour:

```fstar
let promote_object (minor: minor_state) (major: heap) (obj: U64.t)
                   (fp: U64.t) (wosize: nat{wosize > 0}) (ph: gc_phase)
  : GTot promote_one_result =
  let alloc_res = AP.alloc_at ph major fp wosize (promoted_tag minor obj) in
  ...
  if new_addr = 0UL then { major_out = major; fp_out = fp; new_addr = 0UL }
  else
    let copied_major = copy_fields minor new_major obj new_addr 0 wosize in
    { major_out = copied_major; fp_out = new_fp; new_addr = new_addr }
```

The whole minor collection takes the phase: the Cheney state carries it
(`cs_phase`, fixed for the run), `cheney_promote ph minor major fp roots` and
`cheney_collect_spec_with ph free minor major fp roots` promote every copy at
`ph`, and the stop-the-world `cheney_collect_spec` is the `Idle` instance for
`free_stw`.  The lemmas about `promote_object` hold at any phase: the phase
changes nothing but the new header's colour (`AC.alloc_phase_heap`), so
`GC.Spec.Allocator.Phase` states the idle allocator's facts at any phase
(`alloc_at_*`, from `recoloured`: the same walk, sizes, tags, free blocks and
every other word), and `promote_object_recoloured` says the same of a whole
promotion.  At `Idle`, `AP.alloc_at Idle` is `alloc_spec` (an SMT pattern).

The major allocator is size-exact: the allocated header declares exactly the
requested `wosize` (`GC.Spec.Allocator.Props.alloc_spec_obj_wosize_exact_part1`; see
`docs/allocator-exactness.md`), so the copied fields fill the promoted object
and there is no extra word to account for.

### The pointer update, given what counts as free

The pointer update is a walk over the major heap's objects that rewrites the
nursery pointers held by a fixed set of objects:
`GC.Gen.Promote.update_walk major upd fwd` rewrites the fields of the objects
`x` with `upd x` (scannable ones) and never reads anything else.  The minor
collection runs it over the non-free blocks,
`update_pointers_with free major fwd = update_walk major (in_use free major) fwd`.
The stop-the-world update is the `free_stw` instance: `update_major_pointers
major fwd` is *defined* as `update_pointers_with free_stw major fwd`, so there
is one walk.  `GC.Gen.Cheney.cheney_collect_spec_with ph free minor major fp roots`
is the collection (at phase `ph`) whose pointer update is
`update_pointers_with free` over the promoted heap; at `Idle` and `free_stw`
it is `cheney_collect_spec` (`cheney_collect_spec_with_stw`).  The
`PromoteUpdate` lemmas and the free-list preservation lemmas are proved for the
walk over any set (`walk_ok`: its members are not free); a stop-the-world
caller applies them at `in_use free_stw`.

The implementation runs the update in two passes, over the promoted objects
(found through the forwarding array) and over the remembered slots.  Their
ghost specifications, and the array's representation of the forwarding map,
are in the spec module `GC.Gen.ForwardingArray` (`represents_fwd`,
`update_promoted_iter`, `rewrite_slots_iter`, `fwd_targets_stable`, ...); the
Pulse functions in `GC.Gen.Impl.UpdatePtrs` refine them.  The two passes are
proved equal to the walk
(`GC.Gen.TwoPassEquiv.promoted_plus_slots_eq_walk`), and at a Cheney result,
with the write barrier's guarantees stated for the same definition of free
(`GC.Gen.RefTable.ref_table_covers_with`, `ref_table_sound_with`: every slot is
a field of a non-free block), to the pointer update of
`cheney_collect_spec_with` (`GC.Gen.TwoPassEquiv.Collect.two_pass_implies_collect_with`).

### The minor collection, for any definition of free

The minor collection's theorems are stated for any definition of free the
caller supplies.  They assume three things of it, all true of `free_stw`:

```fstar
(* blue blocks are free, and what is free is read off walk membership and the
   block's header, so field writes do not change it *)
let blue_is_free (free: free_def) : prop =
  forall (g: heap) (x: obj_addr). is_block g x /\ is_blue x g ==> free g x
let free_is_determined_from_header (free: free_def) : prop =
  forall (g g': heap) (x: obj_addr).
    (is_block g x <==> is_block g' x) /\
    read_word g (hd_address x) == read_word g' (hd_address x) ==> free g x == free g' x
let free_def_ok (free: free_def) : prop = blue_is_free free /\ free_is_determined_from_header free

(* the blocks the allocator creates at the phase are not free (GC.Gen.Promote) *)
let allocations_not_free (ph: gc_phase) (free: free_def) : prop =
  forall (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t{U64.v tag < 256}) (x: obj_addr).
    AP.alloc_ok g fp /\
    (AP.alloc_at ph g fp wz tag).obj_out == x ==>
    not (free (AP.alloc_at ph g fp wz tag).heap_out x)
```

`free_stw_ok` and `free_stw_allocations_not_free ph` are the `free_stw`
instances (the allocator never writes a blue header, at any phase); mid-sweep
`free_incremental_allocations_not_free c` gives it for `free_incremental c`
at `Sweeping c` (a block in front of the cursor is black).  The third
assumption is a property of the definition of free and of the allocator at the
phase promotion runs at, not of a particular collection; the generic theorems
derive from it that no
promoted copy is free (`CheneyPreservation.Fields.cheney_promote_fwd_target_not_free`:
the copy is not free when it is allocated, and its header and walk membership
never change afterwards, so by `free_is_determined_from_header` it stays so).  It is
part of the shape (`major_shape_with`), so it does not appear in the
statements.  For a sweep in progress this is where the allocation colour
matters: the allocator at the sweeping phase colours a block in front of the
cursor black, so the sweep's definition of free, which counts the white
blocks in front of the cursor, has it at that phase.

`GC.Gen.HeapInvariant.collection_shape_with ph free minor major fp` is what a
minor collection at phase `ph` needs of the heaps:

- `major_shape_with ph free major fp`: `free_def_ok free`,
  `allocations_not_free ph free`, `well_formed_heap_with free major` (the walk clauses, and the pointer clauses
  of the non-free blocks), and the free-list facts of `major_heap_shape`
  (valid, terminating, exact, ascending, its link words, density,
  `chain_objects_blue`);
- the nursery's shape, as before;
- `minor_major_fields_not_free free`: a nursery field that looks like a major
  pointer targets a non-free block.

A free block is unconstrained: its fields may point anywhere, blue blocks
included, and the collection never reads them.  At `free_stw` this is
`collection_heap_shape` without its two colour facts
(`collection_heap_shape_as_free_stw`, `collection_heap_shape_of_free_stw`):
`well_formed_heap` *is* `well_formed_heap_with free_stw`.

`GC.Gen.CheneyGeneric` proves it is kept, event by event: promotion keeps every
non-free block non-free (`cheney_promote_keeps_in_use`, by
`free_is_determined_from_header`), makes the images of the promoted nursery objects
non-free blocks (`cheney_promote_image_not_free`, by `allocations_not_free`),
and keeps `well_formed_heap_with free` (`cheney_promote_preserves_wf_with`: an
old block is untouched, a promoted one holds its nursery source's fields); the
walk keeps what is free and keeps `well_formed_heap_with free` when every
forwarding target is a non-free block (`update_walk_keeps_in_use`,
`update_pointers_with_preserves_wf`, `cheney_promote_fwd_targets_not_free`).
With the free-list facts this gives `cheney_collect_with_preserves_shape`:
`collection_shape_with ph free` of the input implies `collection_shape_with ph
free` of `cheney_collect_spec_with ph free`'s result.  The
promotion lemmas only ask for the walk facts of the major heap (`blocks_fit`,
`no_infix_block`), not `well_formed_heap`.  The stop-the-world
`cheney_collect_preserves_collection_heap_shape` is the instance at `Idle`
and `free_stw`, plus the colour facts (no black, no gray objects).  These are not
carried through the Cheney run: `CheneyPreservation.cheney_collect_block_origin`
says a non-blue block of the result is an old non-blue block with the same
header (the frame facts `CheneyPreservation.Frame.cheney_promote_frame_old_header`
and `PromoteUpdate.update_walk_preserves_header`) or a promoted copy, which the idle
allocator wrote white: `cheney_promote_fwd_target_not_free` at the definition
"free means not white", which the allocator's white blocks satisfy.  So a
collection creates no grey or black block.

The reachable-subgraph isomorphism (`GC.Gen.MinorCollectForwarding`) is
stated and proved for any definition of free as well, over graphs in which a
free block stays a vertex but has no outgoing edges.  Mid-sweep the fields of
a block about to be freed may name blocks already merged into the free list,
so this is what keeps every edge pointing at a vertex.  The pre-collection
graph is `CombinedGraph.build_combined_graph minor major free` (only a
non-free major block has major-side edges; it is well formed for any heaps,
`build_combined_graph_wf`); the post-collection graph is
`HeapModel.create_graph_with free post`, well formed whenever
`well_formed_heap_with free post` holds
(`MinorCollectForwarding.Helpers.create_graph_with_wf`).  An edge of either
graph therefore leaves a non-free block (`CG.major_edge_elim`,
`Helpers.heap_graph_edge_to_pointer_field`), which is what most proofs used to
derive from reachability: the remembered-set bridge
(`ReachabilityBridge.reachability_bridge`) needs only the nursery's
well-formedness and the remembered set's coverage, and a major-to-major edge
survives the collection whether or not its source is reachable
(`Edges.combined_major_edge_forwarded`).  Facts about a reachable *vertex* (a
non-free block, so its image or its fields are what the theorems say) still
come from `ReachabilityBridge.reachable_not_free`: the roots are not free
(`roots_valid_with`), and a non-free block points only to non-free blocks
(`pointers_lead_to_non_free`, `minor_major_fields_not_free`).  The
stop-the-world theorems are the instances at `free_stw`
(`MinorCollectForwarding.stop_the_world_context` turns the stop-the-world
hypotheses into the generic ones), where the post-collection graph is
`HeapModel.create_graph` (`Helpers.result_post_stw`).

`minor_collect_with`'s contract is generic, isomorphism included:
`minor_collect_pre_with free minor s fp rs farr slots n` (the shape, the
write barrier's guarantees, the remembered
targets in the roots, valid non-free roots, all for `free`) and
`minor_collect_post_with free` (the heap is `cheney_collect_spec_with
free`'s, the shape for `free` is kept, and on success the result is a
reachable-subgraph isomorphism with the non-pointer fields preserved).
`minor_collect_pre_idle` / `minor_collect_post_idle` are the stop-the-world
instance with the colour facts of `collection_heap_shape`;
`full_gc` uses them.

### Cheney BFS

The copying collector is specified in `generational/spec/GC.Gen.Cheney.fst`.
Its state contains the major heap, free pointer, forwarding map, and BFS queue.

Forwarding a normal object promotes it, extends the forwarding map, and appends
the minor object address to the scan queue:

```fstar
let cheney_forward_normal (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : GTot cheney_state =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then cs
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then cs
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz Idle in
      if res.new_addr = 0UL then cs
      else
        { cs_major = res.major_out;
          cs_fp    = res.fp_out;
          cs_fwd   = extend_forwarding cs.cs_fwd addr res.new_addr;
          cs_queue = Seq.append cs.cs_queue (Seq.create 1 addr) }
```

Forwarding is infix-aware. If the address is a minor infix object, the collector
forwards the parent closure and derives the infix forwarding address by adding
the same interior offset to the forwarded parent:

```fstar
let cheney_forward_one (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : GTot cheney_state =
  if cs.cs_fwd addr <> 0UL then cs
  else if is_infix_in_minor minor addr then
    let parent = infix_parent minor addr in
    let cs' = cheney_forward_normal minor cs parent in
    if cs'.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      let delta = U64.v addr - U64.v parent in
      { cs' with cs_fwd = extend_forwarding cs'.cs_fwd addr
                             (U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta)) }
    else cs'
  else
    cheney_forward_normal minor cs addr
```

After roots are forwarded, the BFS loop scans the queue:

```fstar
let rec cheney_scan (minor: minor_state) (cs: cheney_state)
                    (scan: nat) (fuel: nat)
  : GTot cheney_state =
  if fuel = 0 || scan >= Seq.length cs.cs_queue then cs
  else
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan minor cs' (scan + 1) (fuel - 1)
```

The proof that this BFS forwards all reachable minor objects is factored into
`generational/spec/GC.Gen.CheneyBFS.fsti`. It states a familiar graph-theoretic
argument:

```fstar
let fwd_covers_roots (minor: minor_state) (fwd: forwarding_map) (roots: seq U64.t) : prop =
  forall r. Seq.mem r roots /\ Seq.mem r (minor_objects minor) /\
    minor_wosize minor r > 0 ==> fwd r <> 0UL

let fwd_closed (minor: minor_state) (fwd: forwarding_map) : prop =
  forall x y. Seq.mem x (minor_objects minor) /\
    fwd x <> 0UL /\
    Seq.mem y (minor_successors minor x) /\
    minor_wosize minor y > 0 ==> fwd y <> 0UL

let fwd_well_formed minor fwd roots =
  fwd_covers_roots minor fwd roots /\ fwd_closed minor fwd

val fwd_well_formed_covers_reachable :
  ... ensures forall x. Seq.mem x (minor_reachable minor roots) /\
    minor_wosize minor x > 0 ==> fwd x <> 0UL
```

The rest of the module proves that `forward_roots` establishes root coverage,
that each scan step preserves forwarding monotonicity, and that scanning the
queue establishes successor closure when promotion does not run out of memory.

### What a Cheney run keeps

Every fact about a run is an invariant of the Cheney state carried through
roots, scan, and the fields of each scanned object, one `cheney_forward_one`
at a time.  `GC.Gen.Cheney.Induction` does that induction once:

```fstar
let one_keeps (minor: minor_state) (inv: cheney_state -> prop) =
  cs: cheney_state -> addr: U64.t ->
  Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ inv cs)
        (ensures inv (cheney_forward_one minor cs addr))

val cheney_promote_induction
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps minor inv)
  (ph: gc_phase) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires alloc_ok major fp /\ inv (cheney_init ph major fp))
          (ensures (let cs = cheney_run ph minor major fp roots in
                    let prom = cheney_promote ph minor major fp roots in
                    alloc_ok cs.cs_major cs.cs_fp /\ inv cs /\
                    prom.major_final == cs.cs_major /\
                    prom.fp_final == cs.cs_fp /\ prom.fwd_map == cs.cs_fwd))

(* for an invariant p of the major heap and free pointer alone, the step is
   one successful promote_object at the run's phase; the infix and no-op
   cases are done here *)
val cheney_promote_keeps
  (minor: minor_state) (ph: gc_phase) (p: heap -> U64.t -> prop)
  (step: promote_keeps minor ph p)
  (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires alloc_ok major fp /\ p major fp)
          (ensures (let prom = cheney_promote ph minor major fp roots in
                    alloc_ok prom.major_final prom.fp_final /\
                    p prom.major_final prom.fp_final))
```

The run's phase is part of the state (`cs_phase`), fixed for the run: every
step keeps it (`cheney_forward_one_phase` and friends, SMT patterns), so a
step lemma about `cs` promotes at `cs.cs_phase`.

`alloc_ok` is the allocator's invariant (blocks fit, the free list is valid
and terminates), which every step needs and every step keeps, so the
combinator carries it; `cheney_promote_induction_plain` is the variant for an
invariant that needs nothing of the allocator, and the fields, roots and scan
levels are exported too.  An invariant that relates the run to its start
(an old block keeps its header, a forwarded address stays forwarded) is an
`inv` with the starting value as a parameter.

The modules, in dependency order:

| Module | What it says about the run |
| --- | --- |
| `GC.Gen.Cheney` | the definitions (`cheney_forward_{normal,one,fields,roots}`, `cheney_scan`, `cheney_promote`, `cheney_collect_spec(_with)`) and their unfolding lemmas |
| `GC.Gen.Cheney.Induction` | the induction above, and the allocator's invariant at each level |
| `GC.Gen.Cheney.Steps` | the heap invariants a run keeps (free chain blue, free-list shape, objects, density, no infix block, forwarding targets bounded and above `zero_addr`), at each level, and the frame of one promotion |
| `GC.Gen.CheneyPreservation.Frame` | old non-free blocks keep their header and fields |
| `GC.Gen.CheneyPreservation.Forwarding` | the forwarding targets are classified (an object, or an interior pointer of a promoted closure) |
| `GC.Gen.CheneyPreservation.Injectivity` | normal targets are pairwise distinct, not blue, and fresh |
| `GC.Gen.CheneyPreservation.NonBlueOrigin` | a new non-blue block is a forwarding target |
| `GC.Gen.CheneyPreservation.Fields` | a promoted copy holds its source's fields and tag, and is not free |
| `GC.Gen.CheneyFlComplete`, `GC.Gen.FreeListAscending` | the free list stays exact and ascending |
| `GC.Gen.CheneyBFS` | completeness: every reachable nursery object is forwarded unless the major heap ran out of room |
| `GC.Gen.CheneyGeneric` | the collection keeps `collection_shape_with ph free` |
| `GC.Gen.CheneyPreservation` | the stop-the-world instance (`cheney_collect_preserves_collection_heap_shape`, `cheney_collect_block_origin`) |

The run-level facts are kept out of `GC.Gen.Cheney.fsti` itself: its
definitions are what `GC.Gen.Impl.Cheney` refines, and extra vals there
disturb that proof.

## Reachable subgraph isomorphism

Mark-and-sweep can use the five pillars because it does not move live objects.
Copying collection does move objects: roots change, minor addresses disappear,
and major fields that pointed into the minor heap are rewritten. A field-by-field
"same address" preservation theorem would be the wrong abstraction.

The generational proof instead uses a reachable-subgraph isomorphism. The
combined pre-GC graph has tagged vertices:

```fstar
type combined_vertex =
  | MinorV : addr:U64.t -> combined_vertex
  | MajorV : addr:U64.t -> combined_vertex
```

The tags are necessary because minor offsets and major addresses are both
`U64.t`; as raw numbers they can overlap. A vertex's generation is part of its
identity.

`generational/spec/GC.Gen.CombinedGraph.fsti` defines the generic isomorphism:

```fstar
let fwd_morphism (fwd: forwarding_map) (v: combined_vertex) : GTot U64.t =
  match v with
  | MinorV addr -> fwd addr
  | MajorV addr -> addr

let reachable_subgraph_isomorphism
  (src_reachable: combined_vertex -> prop)
  (dst_reachable: U64.t -> prop)
  (src_edge: combined_vertex -> combined_vertex -> prop)
  (dst_edge: U64.t -> U64.t -> prop)
  (fwd: forwarding_map) : prop =
  (forall u. src_reachable u ==> dst_reachable (fwd_morphism fwd u)) /\
  (forall u v. src_reachable u /\ src_reachable v /\
    fwd_morphism fwd u == fwd_morphism fwd v ==> u == v) /\
  (forall w. dst_reachable w ==>
    exists u. src_reachable u /\ fwd_morphism fwd u == w) /\
  (forall u v. src_reachable u /\ src_reachable v ==>
    (src_edge u v <==>
     dst_edge (fwd_morphism fwd u) (fwd_morphism fwd v)))
```

This says:

1. Every reachable source vertex has a reachable image.
2. The image is injective on reachable source vertices.
3. Every reachable destination vertex comes from some source vertex.
4. Edges between reachable vertices are preserved and reflected.

This is a better GC correctness statement than "all fields are unchanged"
because it is representation-independent. It permits movement while ruling out
the errors a collector must not make: dropping live nodes, duplicating live
nodes, inventing reachable nodes, or changing the live pointer graph.

The top-level minor-collection correctness kernel in
`generational/spec/GC.Gen.MinorCollectForwarding.fsti` connects this abstract
isomorphism to the actual Cheney promotion result:

```fstar
let normal_result_reachable_subgraph_isomorphism_prop (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots: seq U64.t) (post_major: heap) (post_roots: seq U64.t) : prop =
  let prom = cheney_promote ph minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (normal_src_reachable ph minor major fp free roots)
    (result_post_reachable post_major free post_roots)
    (normal_src_edge ph minor major fp free roots)
    (result_post_edge post_major free)
    prom.fwd_map
```

The same interface also states non-pointer data preservation for the reachable
subgraph. Graph isomorphism preserves pointer structure; the non-pointer-field
theorem says copied scalar payloads are not lost.

That preservation is made explicit in
`generational/spec/GC.Gen.MinorCollectForwarding.NonPointerFields.fsti`. For a
reachable major source vertex, a field classified as `None` by
`classify_major_field` must have the same word after collection. For a reachable
minor source vertex, the corresponding field in the promoted image must contain
the original minor word:

```fstar
let normal_result_non_pointer_fields_preserved_prop (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (free: free_def)
  (roots: seq U64.t) (post_major: heap) : prop =
  let prom = cheney_promote ph minor major fp roots in
  forall (u: CG.combined_vertex).
    normal_src_reachable ph minor major fp free roots u ==>
    (match u with
    | CG.MajorV src ->
      is_val_addr src ==>
      forall (j:nat).
        j < U64.v (wosize_of_object (src <: obj_addr) major) /\
        CG.classify_major_field minor major
          (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
        read_word post_major (U64.uint_to_t (U64.v src + j * 8)) ==
        read_word major (U64.uint_to_t (U64.v src + j * 8))
    | CG.MinorV src ->
      let img = prom.fwd_map src in
      is_val_addr img ==>
      forall (j:nat).
        j < minor_wosize minor src /\
        CG.classify_minor_field minor major
          (minor_read_field minor src j) == None ==>
        read_word post_major (U64.uint_to_t (U64.v img + j * 8)) ==
        minor_read_field minor src j
    | _ -> True)
```

This is the generational counterpart of the mark-and-sweep "five pillars":

| Mark-and-sweep pillar | Generational analogue |
| --- | --- |
| Final heap well-formedness | `collection_heap_shape` preservation, followed by the major collector's `gc_postcondition`; `full_gc` restores `collection_heap_shape`. |
| Reachability-based survival | The isomorphism's totality and surjectivity over reachable source/destination vertices. |
| Successor preservation | The isomorphism's edge preservation/reflection clause. |
| Color reset | The post-minor heap shape plus the major collector's postcondition; after `full_gc`, final major objects satisfy the major GC color/free-list discipline. |
| Field data preservation | `normal_result_non_pointer_fields_preserved_prop` for scalar fields, together with isomorphism for pointer fields. |

Together with heap-invariant preservation, the isomorphism theorem subsumes the
old pillars in a moving-collector setting. It deliberately does not say "the
same address survives"; it says every live object has exactly one image, every
live edge is preserved under that image, every reachable post-GC object came from
one reachable pre-GC object, and every non-pointer payload word is preserved.
For mark-and-sweep, the forwarding morphism is essentially the identity, so this
collapses back to the original non-moving story. For minor collection, the same
statement allows minor addresses to disappear and be replaced by major
addresses.

### One isomorphism, end to end

`full_gc` runs a minor collection followed by a major one, and each phase proves
its own isomorphism. For a while the top-level postcondition simply exposed
both halves and left the caller to chain them:

* minor collection, from the combined pre-collection graph into the *post-minor*
  major heap, with `prom.fwd_map` as the morphism; and
* major collection, from the *post-darkening* heap into the final one, with the
  identity as the morphism.

That is not a chain a caller can actually close, for three reasons.

1. **Different vocabularies.** The minor half speaks
   `result_post_reachable` / `result_post_edge` (`∃ root. reachable`, raw
   `U64.t` addresses); the major half speaks `heap_reachable` / `heap_edge`
   (membership in the DFS `reachable_set`, with `graph_wf`, `is_vertex_set` and
   `subset_vertices` side conditions, over `obj_addr`).
2. **A third heap in the middle.** Root darkening runs between the two phases,
   so the heap the major collector starts from is not the heap the minor
   collector produced.
3. **A missing lemma.** Surjectivity of the composed morphism needs
   reachability transferred *backwards*: reachable in the final heap implies
   reachable in the post-minor heap. `major_gc_live_subgraph_isomorphism`'s
   edge clause is guarded on **both** endpoints already being live, so the
   obvious path induction is circular — the induction keeps meeting successors
   that are not yet known to be live.

All three are now handled inside the collector.

* `major_gc_live_subgraph_isomorphism` gained a **successor clause**: live
  objects have identical successor *lists* in the two heaps. That is strictly
  stronger than the guarded edge clause and breaks the circularity. The fact was
  already established inside `major_gc_live_subgraph_isomorphism_gen`'s proof
  and simply discarded.
* `GC.Impl.MarkBoundedRootLemmas` proves that root darkening preserves
  `create_graph` — it only recolours headers — by induction over the darkening
  prefix on top of `color_preserves_create_graph`.
* `GC.Gen.MajorReachabilityTransfer` proves the generic graph lemma by
  structural induction on the `reach` witness:

  > two graphs that agree on the successor lists of a successor-closed vertex
  > set have the same reachability and the same internal edges,

  instantiates it at the major collection, and composes the halves.

The result is a single conjunct in `full_gc`'s postcondition:

```fstar
let end_to_end_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (final_major: heap) (final_roots: seq U64.t) : prop =
  CG.reachable_subgraph_isomorphism
    (MCFH.normal_src_reachable Idle minor major fp free_stw roots)
    (MCFH.result_post_reachable final_major free_stw final_roots)
    (MinorFwd.normal_src_edge Idle minor major fp free_stw roots)
    (MCFH.result_post_edge final_major free_stw)
    (cheney_promote Idle minor major fp roots).fwd_map
```

The two intermediate isomorphisms are still exported, because they say things
the composition cannot: the minor step says *where* each survivor went, and the
major step says the survivors did not move again and are white.

## Generational GC

The top-level generational implementation is
`generational/impl/GC.Gen.Impl.fsti` and `.fst`. The main state is:

```fstar
noeq type gen_heap_t = {
  minor : minor_heap_t;
  major : heap_t;
  fp_ref : R.ref U64.t;    // major heap free-list head
  phase_ref : R.ref Alloc.phase_state;  // the major collector's phase
}

let gen_phase (gh: gen_heap_t) (g: heap_state) (ph: Ph.gc_phase) : slprop =
  Alloc.is_phase gh.phase_ref g ph

let is_gen_heap (gh: gen_heap_t) (d: minor_heap) (b: U64.t)
                (s: heap_state) (fp: U64.t) : slprop =
  is_minor gh.minor d b **
  is_heap gh.major s **
  R.pts_to gh.fp_ref fp
```

There is no generational allocation entry point: the runtime allocates small
objects in the minor heap (`GC.Gen.Impl.MinorHeap.minor_alloc` on `gh.minor`)
and the rest in the major heap (`GC.Impl.Allocator.allocate` on `gh.major`,
`gh.fp_ref` and `gh.phase_ref`), as the C bridge does.

The phase is a companion predicate rather than part of `is_gen_heap`: only the
allocator and the major collector read it.  It is indexed by the major heap, because
while sweeping it says the record's caches are the ones derived from that
heap (`Alloc.is_phase`); keeping them so across a major allocation needs the
free list ascending, hence `allocate`'s mid-sweep precondition.
`minor_collect_with` runs at any phase (`gen_phase gh 's 'ph` in,
`gen_phase gh s2 'ph` out), and so does `minor_collect`; `start_cycle` and
`full_gc` require `Ph.Idle`.  The entry points take the heap and the phase
together, with the collector's state at the phase, as `gc_state` (above).  Promotion (`promote_one`, through the Cheney functions) allocates
with `allocate` (on the same `fp_ref`), which keeps `is_phase` from the heap before to the
heap after (`GC.Spec.Allocator.Caches.alloc_caches`), and the copy of the fields
writes no header (`promote_heads`); the specification's run is at `'ph`
throughout, and the Cheney loops relate the heap and record they hold to the
specification's state by `Sim.impl_matches_spec_at ph ms ...`: the heap is the
specification's, its free list ascending, and the phase the run's.  At
`Idle` all of it is trivial, so the C is the same at every phase.  The C bridge allocates the phase record once, idle.

The allocation postcondition is intentionally weak at the top-level interface:
allocation is an operational service used by the runtime, and the deeper
allocator/minor-heap contracts carry the precise shape facts. The collection
entry points are much stronger.

### `minor_collect_with` and `minor_collect`

`minor_collect_with` is the verified minor collection, generic in the phase
and in what counts as free; `minor_collect` (below) is the entry point the C
bridge calls, its instance at the collector's phase.  `minor_collect_with`
takes roots, a forwarding array, a BFS queue, and remembered slots, and -- as
a ghost argument, erased in the C -- a definition of what counts as free in
the major heap:

```fstar
fn minor_collect_with (gh: gen_heap_t)
                      (roots: array U64.t) (nroots: SZ.t)
                      (fwd_arr: array U64.t)
                      (queue: larray U64.t FA.queue_size)
                      (slots: array U64.t) (nslots: SZ.t)
                      (#free: erased SpecFields.free_def)
```

The precondition (`minor_collect_pre_with ph free`, at the phase `'ph` the
allocator holds) is:

- `collection_shape_with ph free` for the minor and major heap (which includes
  `allocations_not_free ph free`: the blocks the allocator creates at `ph` are
  not free);
- root-array length consistency and a zeroed forwarding array of the expected size;
- remembered slot soundness and coverage for `free`
  (`ref_table_sound_with`, `ref_table_covers_with`); slots may repeat;
- the remembered targets are among the roots, and the roots are valid and not
  free (`remembered_targets_in_roots`, `roots_valid_with`).

The postcondition is `minor_collect_post_with ph free minor_st s fp rs ok d2 b2
s2 fp2 rs2`, in full:

```fstar
let prom = CheneySpec.cheney_promote ph minor_st s fp rs in
s2 == (CheneySpec.cheney_collect_spec_with ph free minor_st s fp rs).mc_major /\
fp2 == prom.fp_final /\
rs2 == PromoteSpec.rewrite_roots rs prom.fwd_map /\
U64.v b2 == 0 /\
({ data = d2; bump = b2 } <: minor_state) == minor_reset minor_st /\
GenInv.collection_shape_with ph free ({ data = d2; bump = b2 } <: minor_state) s2 fp2 /\
(not ok ==> CheneyBFS.cheney_oom ph minor_st s fp rs) /\
(ok ==>
  CheneyBFS.cheney_no_oom ph minor_st s fp rs /\
  MinorFwd.normal_result_reachable_subgraph_isomorphism_prop ph
    minor_st s fp free rs s2 (MCFH.resolve_roots s2 rs2) /\
  MinorFwd.normal_result_non_pointer_fields_preserved_prop ph
    minor_st s fp free rs s2)
```

Nothing is said of the forwarding array or the queue the call hands back:
no caller reads them.  The two-pass equation that the implementation
establishes along the way (`s2 == rewrite_slots_iter (update_promoted_iter
...)`) is internal to `minor_collect_with` too; `minor_collect_with_spec`
turns it into the equation with `cheney_collect_spec_with`.

The collection runs at the phase `'ph` the allocator holds (`gen_phase gh 's
'ph`), and every promoted copy is allocated there; it hands back the same
phase, `gen_phase gh s2 'ph`: the promotions keep the record's caches
derived, and the pointer update writes no header (`GC.Gen.SweptTail.
update_heads`, `GC.Gen.Impl.Promote.phase_heads`).

The stop-the-world contract is the instance at `free_stw`:
`minor_collect_pre_idle` (`collection_heap_shape`, the remembered set over the
whole heap, the root-set facts) and `minor_collect_post_idle`, which adds

```fstar
s2 == (CheneySpec.cheney_collect_spec minor_st s fp rs).mc_major /\
GenInv.collection_heap_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2
```

`minor_collect_idle_pre` / `minor_collect_idle_post` connect the two; `full_gc`
calls `minor_collect` idle (where `phase_free Idle == free_stw`) and uses them.
The
isomorphism is over the graphs given what counts as free
(`CG.build_combined_graph minor s free`, `HeapModel.create_graph_with free s2`);
at `free_stw` the latter is
`create_graph`, the graph the major collection's own isomorphism speaks of, which
is how `MajorReachabilityTransfer.end_to_end_isomorphism_intro` chains the two.

**`minor_collect`** is the entry point, in both modes: `minor_collect_with`
at the collector's phase, for the phase's definition of free
(`GI.phase_free`), stated over `gc_state`:

```fstar
fn minor_collect (gh: gen_heap_t) (roots: array U64.t) (nroots: SZ.t)
                 (fwd_arr: array U64.t) (queue: larray U64.t FA.queue_size)
                 (slots: array U64.t) (nslots: SZ.t)
  requires gc_state gh 'd 'b 's 'fp 'ph ** pts_to roots 'rs ** ... **
           pure (SZ.v nroots == Seq.length 'rs /\
                 minor_slots_ok 'ph ({ data = 'd; bump = 'b }) 's 'rs 'farr 'sl (SZ.v nslots))
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    gc_state gh d2 b2 s2 fp2 'ph ** pts_to roots rs2 ** ... **
    pure (minor_collect_post_with 'ph (GI.phase_free 'ph) ({ data = 'd; bump = 'b })
            's 'fp 'rs ok d2 b2 s2 fp2 rs2)
```

Idle the collector stays in the stop-the-world shape
(`cheney_collect_preserves_collection_heap_shape`); mid-sweep the sweep keeps
its cursor and the objects pending free (`GI.minor_keeps_phase_shape`).  The
C is `minor_collect_with`'s.

#### The contract of `minor_collect_with`

The postcondition is a set of properties of the result (the shape, the
isomorphism, the non-pointer fields) plus one equation,
`s2 == (cheney_collect_spec_with ph free ...).mc_major`.  The equation stays in
the contract.  `full_gc`'s major-phase helpers (`gen_gc_prepared_state`,
`gen_gc_major_precondition_elim`), `GC.Gen.MajorPrecondition` and the SPOT
postconditions (`GC.SPOT.Postconditions.minor_collect_full_post`,
`GC.SPOT.ConcreteFull`) are stated over `cheney_collect_spec`, and a Pulse
postcondition is the only way `full_gc` learns anything about `s2`: a separate
ghost lemma cannot recover the equation from a property-only contract.
Dropping it means restating those helpers and SPOTs in property form, which
is a larger change than the cleanup, so it was not done.

The equality is also the strongest operational statement: the imperative code
implements the pure full minor-collection spec, including promotion,
promoted-object field rewriting, remembered-slot rewriting, root rewriting, and
minor heap reset.

The `ok` flag captures promotion success. If the major heap does not have enough
space for all live minor objects, the isomorphism theorem is conditional on
`ok`; the OCaml bridge treats `ok = false` as fatal out-of-memory for the current
fixed-size heap.

### `full_gc`

The full generational GC composes the minor collection with a whole major
cycle, from the entry points above:

```fstar
fn full_gc (gh: gen_heap_t)
           (roots: array U64.t) (nroots: SZ.t)
           (fwd_arr: array U64.t)
           (queue: larray U64.t FA.queue_size)
           (slots: array U64.t) (nslots: SZ.t)
  requires gc_state gh 'd 'b 's 'fp Ph.Idle ** ...
  returns ok: bool
  ensures exists* d2 b2 s2 fp2 rs2 farr2 qv2.
    gc_state gh d2 b2 s2 fp2 Ph.Idle ** ...
```

Its body is `minor_collect`; then, unless promotion ran out of memory,
`start_cycle` (root darkening, the phase becomes `Marking`) and `major_slice`
with an unbounded budget until the collector is idle again -- one slice marks
(and hands over to the sweep), one sweeps:

```pulse
  let ok = minor_collect gh roots nroots fwd_arr queue slots nslots;
  if ok {
    start_cycle gh roots nroots;
    let mut busy = true;
    while (!busy) ... { let idle = major_slice gh 0xFFFFFFFFFFFFFFFFUL; busy := not idle; };
    ok
  } else { ok }
```

Its precondition speaks only about the state the caller can observe on entry --
the pre-minor heap, the nursery, and the arrays being passed in; the idle
`gc_state` carries the shape:

```fstar
gc_state gh 'd 'b 's 'fp Ph.Idle   (* GenInv.collection_heap_shape minor_st 's 'fp *)
MinorFwd.roots_valid_for_minor_collection minor_st 's 'rs /\
...
```

Nothing is asked of the mark stack any more: it is the collector's persistent
stack (`mark_state`), root darkening pushes onto it while it has room and
raises the overflow flag when it is full, and the mark slices then rescan.
(Before M4 the caller handed `full_gc` an empty gray stack able to hold every
root, `gen_gc_stack_budget`.)

The postcondition's definitions name the major collection's starting point
without any stack: `gen_gc_prepared_state minor major fp roots` is root
darkening of the post-minor heap into a stack with room for every root
(`prepared_cap roots = |roots| + 1`); its heap is the darkened heap, which does
not depend on the stack (`GC.Gen.MarkSlice.darken_roots_heap`), so it is the
heap `start_cycle` leaves; its stack names the root objects, each once.

### How `full_gc`'s contract is proved

The contract is `gen_gc`'s (the stop-the-world entry point before the
restructure), and the proof reuses its end lemmas unchanged.  What is new is
that marking runs in slices: the end lemmas need the marked heap of the
darkened one, `mark_post g0 g_mark roots fp` (black exactly when reachable
from the roots in `g0`, objects and fields unchanged), and a mark slice's
contract (`GI.mark_slice_post`) only says it made some mark moves.  No
program runs between `full_gc`'s slices, so the marking invariant holds with
its **stop-the-world strengthening** (`GC.Spec.MarkPhase.Stw`, mirroring the
sweep's `sweep_inv_stw`):

```fstar
let marking_inv_stw (g0 g: heap) (roots: seq obj_addr) : prop =
  colours_only_changed g0 g /\       (* g is g0 recoloured; no black-to-white edge *)
  dark_were_reachable g0 g roots /\  (* every grey or black object is reachable in g0 *)
  darkened_stay_dark g0 g            (* every object grey in g0 is grey or black *)
```

It holds at the darkened heap (`marking_inv_stw_start`), every mark move keeps
it (`marking_inv_stw_move`: a scanned field greys a child of a reachable grey
object; blackening an object whose fields are dark is the stop-the-world step
`mark_step_bounded` on a one-entry stack, whose lemmas apply), and with nothing
grey it is `mark_post` (`marking_inv_stw_done`, through
`MarkBoundedCorrectness.mark_post_from_bounded_mark`).

`GC.Spec.SweepPhase.Slice.phase_rest g fp ph` is what the rest of the sweep
leaves from the collector's phase: idle, `(g, fp)`; mid-sweep, the
stop-the-world pass `sweep_from g fp (state_at g c)`.  The loop invariant is

```fstar
gc_state gh d_mid b_mid s_i fp_i ph_i ** R.pts_to busy vb ** GR.pts_to gr n **
pure (vb == not (Ph.Idle? ph_i) /\ n == rank ph_i /\
      full_rest g0 droots fp_mid s_i fp_i ph_i)

full_rest g0 droots fp0 s fp ph =
  (Marking? ph ==> fp == fp0 /\ Stw.marking_inv_stw g0 s droots) /\
  (~(Marking? ph) ==> exists s_mark. mark_post g0 s_mark droots fp0 /\
                                     SL.phase_rest s fp ph == FS.fused_sweep_coalesce s_mark fp0)
```

with `g0`/`droots` the prepared heap and root objects (`gen_gc_prepared_*`).
`full_cycle_start` establishes it after `start_cycle`; `full_slice_step` keeps
it for an unbounded slice: from `Marking` the slice finishes marking
(`GI.unbounded`), so the heap it leaves is `mark_post` of `g0` and, at
`Sweeping zero_addr`, the rest of the sweep is all of it (`phase_rest_start`);
from `Sweeping` it finishes the sweep and keeps `phase_rest`
(`phase_rest_slice`).  The measure is `rank`: 2 at `Marking`, 1 at
`Sweeping`, 0 at `Idle`, and every unbounded slice lowers it.  At the exit the
heap and free-list head are exactly `fused_sweep_coalesce s_mark fp_mid` for a
`mark_post` of the darkened heap -- the situation `GC.Impl.collect` is in
after its fused sweep -- so `full_gc_major_post` applies the same lemmas
`gen_gc` did: `SpecGCPost.gc_result_fused` for the major theorems and
`MRT.end_to_end_isomorphism_intro` for the end-to-end isomorphism
(`full_gc_end` opens the existential).  `collection_heap_shape` of the result
is the idle `gc_state` the last slice leaves (`GI.sweep_end_shape`).

### Out-of-memory is a runtime fact, not a proof obligation

An intermediate version of this contract also required `cheney_no_oom` — "the
nursery's live set fits in the major free list".  That was indefensible.
`cheney_no_oom` is a statement about the outcome of the entire Cheney BFS; no
caller can discharge it without simulating the collector, and `full_gc` already
reports promotion failure through the `ok` component of its result.  Demanding
it up front made `full_gc` un-callable in exactly the situation its own return
type exists to describe.

The fix is to consume the flag instead of the predicate.  `GC.Gen.Impl.Cheney`
already proves `ok ==> cheney_no_oom` about its BFS loop; `minor_collect`
re-exports that, and `full_gc` branches on it (above): the cycle starts only
when `ok`; otherwise the post-minor heap is handed back untouched.

Skipping the major phase on the out-of-memory path is not merely convenient, it
is the only correct thing to do: when promotion fails, `rewrite_root` leaves the
unforwarded minor roots as nursery addresses, so the rewritten root set no longer
points into the major heap and mark-and-sweep has nothing meaningful to traverse.
The extracted C gains a single `if (ok) { ... } else { ... }` around the major
phase.  The OCaml bridge already treated `!ok` as fatal, so its behaviour is
unchanged; it now simply aborts without having run an unsound collection first.

Two postconditions moved under the `ok` guard as a result — `roots_match_stack`
(half of `gen_gc_roots_post`) and `gen_gc_unreachable_final_blue_post`, since only
the sweep makes unreachable objects blue.  The heap-shape postcondition did *not*
need guarding: `major_heap_shape` records both `no_black_objects` and
`no_gray_objects`, so the post-minor heap is white-or-blue everywhere and
satisfies `gc_postcondition` on its own
(`GC.Gen.MajorPrecondition.major_heap_shape_gc_postcondition`).

### What failure means

Reporting failure through a boolean is only honest if the boolean means
something.  `full_gc` therefore also carries a postcondition on the failure side:

```fstar
not ok ==> CheneyBFS.cheney_oom minor_st 's 'fp 'rs
```

`cheney_oom` is a *witness*, not a shrug.  Unfolded, it says: there is a state
`cs` that this collection passes through, and an address the collector was about
to forward there, whose promotion `promote_object` could not place because the
free list of `cs.cs_major` had no block big enough.  Two ingredients make it
meaningful:

- **The object.** `promote_fails_at minor cs addr` requires `addr` to be an
  allocated minor object of positive size that `cs` has not forwarded yet, and
  `(promote_object minor cs.cs_major addr cs.cs_fp wz).new_addr == 0UL`.  For an
  interior (infix) pointer it is the enclosing closure that did not fit, which is
  what `cheney_forward_one` actually tries to promote; that is the second
  disjunct of `promote_fails_for`.
- **The point in the run.** `cheney_attempts minor cs final addr` ties `cs` to
  this collection by the residual equation "finishing the collection from `cs`
  yields `final`", and pins `addr` as the *next* address the collector forwards
  there.  Its two disjuncts are the two loops that call `cheney_forward_one`:
  the root loop, about to forward `roots[ridx]`, and the field loop, about to
  forward field `fld` of the object being scanned.  Those residual equations are
  exactly what the loops already carry as invariants, so the witness costs one
  extra conjunct per loop and no new proof.

Note that `cheney_oom` is not the literal negation of `cheney_no_oom`, and is not
claimed to be.  `cheney_no_oom` is a property of the collection's *final*
forwarding map; deriving its negation from a single failed promotion would need a
monotonicity theorem about the first-fit free-list allocator — that an object the
allocator once refused is never accepted later.  The witness above says something
more direct, and more useful to a caller deciding what to do next: here is the
object that did not fit, and here is where it did not fit.

Both witness predicates (`cheney_oom_reaching`, `cheney_oom_fields`) are
`opaque_to_smt` and come with intro/elim lemmas, because they are carried through
four nested Pulse loop invariants where unfolding their existentials only slows
Z3 down.  The field loop carries the smaller, local `cheney_oom_fields` — phrased
in terms of the object being scanned — and converts it to the run-level witness
once, on the way out, where the enclosing scan step's residual equation is in
scope.  All of it is ghost: the extracted C is unchanged.

### The invariant is inductive: `full_gc` restores its own precondition

`full_gc` demands `GC.Gen.HeapInvariant.collection_heap_shape` of the heap it is
handed.  For a long time it promised nothing of the heap it returned, which made
that predicate an *assumption* rather than an invariant: a runtime driving a
second collection had no way to satisfy the precondition again.  It is now a
postcondition, and deliberately not behind a named wrapper — the `ensures`
names the very predicate the `requires` names, so the two can be read against
each other:

```fstar
  requires gc_state gh 'd 'b 's 'fp Ph.Idle ** ...
           (* GI.phase_shape at Idle: GenInv.collection_heap_shape minor_st 's 'fp *)
  ensures exists* d2 b2 s2 fp2 ... gc_state gh d2 b2 s2 fp2 Ph.Idle ** ... ** pure (
    let minor_st_out : minor_state = { data = d2; bump = b2 } in
    ...
    GenInv.collection_heap_shape minor_st_out s2 fp2 /\ ... )
```

The minor half is vacuous.  `minor_collect_with` finishes by calling
`minor_heap_reset`, which clears the nursery *bytes* as well as the bump pointer,
so the state it hands back is literally `GC.Gen.MinorHeap.minor_reset` — a fact
the implementation always had and simply never stated.  With it,
`collection_heap_shape_after_minor_reset` collapses the minor-side and
cross-generation conjuncts and reduces the whole obligation to
`major_heap_shape` of the major heap and free-list head.

That is fourteen conjuncts, and it is where the work is.
`GC.Gen.PostCollectionShape.major_gc_restores_major_heap_shape` proves them for
`fused_sweep_coalesce h_mark fp` under `GC.Spec.Correctness.mark_post` and an
exact, ascending input list, all read off the sweep's end lemma
(`GC.Spec.FusedSweep.End.sweep_post`):

| conjunct | supplied by |
| --- | --- |
| `well_formed_heap` | `FusedSweep.End.sweep_post_wf` |
| `fl_valid`, `fl_chain_terminates` | `FreeList.Ascending.fl_ascending_valid` |
| `free_list_exact` | `FreeList.Ascending.fl_ascending_exact` |
| `fl_ascending` | `sweep_post` (the sweep's invariant carries it) |
| `fp_pointer_or_zero`, `blue_link_fields_valid` | every link of an ascending list is null or a cell |
| `heap_objects_dense`, `objects` non-empty | `sweep_post`, from `GC.Spec.Walk.dense_of_reaches_end` |
| `chain_objects_blue` | `FreeList.Ascending.fl_ascending_avoids` |
| `fp_valid`, `fp_in_heap` | `GC.Gen.FreeListShape`, from `fl_valid` |
| `no_black_objects`, `no_gray_objects` | `FusedSweep.End.sweep_post_white_or_blue` |

**The free list is kept, so it must be invariant.**  The sweep needs the list
it is handed to be exact and ascending, which is why the shape invariant
carries `fl_ascending` and why every operation between collections must keep it:
allocation (`GC.Spec.Allocator.Ascending`), promotion and the pointer rewrite
(`GC.Gen.FreeListAscending`), and root darkening
(`GC.Impl.MarkBoundedPrecondition`).  An ascending list is acyclic and bounded
by the number of 8-aligned heap addresses, which discharges the allocator's two
entry conditions outright.

**Density is a statement about the walk.**  `heap_objects_dense` -- "the object
walk tiles the heap, never stopping because a block overruns" -- is equivalent
to the walk from `zero_addr` reaching the end of the heap
(`GC.Spec.Walk.walk_end`, `GC.Spec.Walk.reaches`).  The sweep's invariant says the
cursor is a position of the current heap's walk; at the end the cursor is the
end of the heap, so the result is dense.

The Pulse entry point `GC.Impl.collect_with_roots` does not expose the marked
heap, so it exposes `GC.Spec.Correctness.gc_coalesce_source` instead — "some
marked heap satisfying `mark_post` produced this result", and
`major_gc_restores_major_heap_shape_of_source` discharges that existential.
`full_gc` no longer goes through it: its heap is the end of the sweep phase,
and the idle `gc_state` the last slice leaves already carries
`collection_heap_shape`, proved from the sweep invariant at the end of the heap
(`GI.sweep_end_shape`, from `sweep_inv_incremental_end` and the same
free-list facts).  On the out-of-memory path nothing runs after the minor
collection, so the invariant is the post-minor one, which
`GC.Gen.CheneyPreservation.cheney_collect_preserves_collection_heap_shape`
already provides.

### Transporting the rest across the minor collection

Everything else the major phase needs is derived internally.
`GC.Gen.MajorPrecondition` does the work in two exported lemmas.  The first is
the one that used to be the caller's hardest obligation — conjunct 10 of
`darken_precondition`, that every **post-minor** root is a genuine non-blue major
object:

```fstar
val post_minor_roots_valid_for_darkening minor major fp roots
  : Lemma (requires
             GenInv.collection_heap_shape minor major fp /\
             MinorFwd.roots_valid_for_minor_collection minor major roots /\
             CheneyBFS.cheney_no_oom minor major fp roots)
          (ensures
             let result = Cheney.cheney_collect_spec minor major fp roots in
             forall (i: nat). i < Seq.length result.mc_roots ==>
               MBP.root_valid_for_darkening result.mc_major
                 (Seq.index result.mc_roots i))
```

This is really a theorem about minor collection, and its two cases are quite
different.  A **non-minor** root survives `rewrite_root` untouched, so it only
has to remain a non-blue object of the major heap, which Cheney's frame lemmas
give directly.  A **minor** root is forwarded — BFS coverage from `cheney_no_oom`
plus `minor_wosize > 0` (part of `roots_valid_for_minor_collection`) gives
`fwd r <> 0` — and its target is an ordinary object rather than an interior
pointer, because the source was a `minor_objects` member and therefore not an
infix sub-object.  Both cases then transport across `update_major_pointers`,
which preserves the object list and every header.

The second lemma assembles the whole entry condition:

```fstar
val darken_precondition_after_minor minor major fp roots cap
  : Lemma (requires
             GenInv.collection_heap_shape minor major fp /\
             MinorFwd.roots_valid_for_minor_collection minor major roots /\
             CheneyBFS.cheney_no_oom minor major fp roots /\
             Seq.length roots <= cap /\ cap > 0)
          (ensures
             let result = Cheney.cheney_collect_spec minor major fp roots in
             MBP.darken_precondition
               result.mc_major Seq.empty result.mc_roots result.mc_fp cap)
```

Note where the hypotheses live: the first two are already `full_gc` preconditions
for entirely independent reasons, the third is the runtime success flag, and the
last is about the spec-level stack that names the root objects
(`prepared_cap roots = |roots| + 1`), so it holds by construction.  There is no
`..._intro` counterpart any more — there is nothing left for a caller to
introduce.

One conjunct deserves a note.  With an empty stack, `gray_objects_on_stack`
reduces to "the major heap has no gray objects", which is a property of the
pre-minor heap that `full_gc` should not have to ask about separately.  It is
therefore folded into `GC.Gen.HeapInvariant.major_heap_shape` (as
`SweepInv.no_gray_objects`), where the rest of the major heap's well-formedness
already lives, and `GC.Gen.CheneyPreservation` re-establishes it after the
minor collection.

`GC.Impl.collect_with_roots` demands its precondition on the *post*-darkening
state.  That last step is also done inside the library:

```fstar
val gen_gc_major_precondition_elim minor major fp roots
  : Lemma (requires
             GenInv.collection_heap_shape minor major fp /\
             MinorFwd.roots_valid_for_minor_collection minor major roots /\
             CheneyBFS.cheney_no_oom minor major fp roots)
          (ensures
            MajorGC.gc_precondition_with_roots
              (fst prepared) (snd prepared) (snd prepared) result.mc_fp
              (prepared_cap result.mc_roots) /\
            roots_match_stack result.mc_roots (snd prepared))
```

`gen_gc_prepared_state` is still exported, because the postcondition talks about
the darkened heap:

```fstar
let gen_gc_prepared_state minor major fp roots =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  MarkBoundedImpl.darken_roots_bounded_spec result.mc_major Seq.empty result.mc_roots
    (prepared_cap result.mc_roots)
```

So callers do not have to pre-color roots, pre-seed the mark stack, or reason
about `darken_roots_bounded_spec` at all.

The effect on the concrete client is the honest measure of how much of the
collector's internal reasoning the old contract leaked: SPOT's hand-proof of the
entry condition went from ~374 lines of concrete case analysis over its three
objects to a two-line lemma invocation.

The postcondition is two facts about the returned state plus three named
bundles:

```fstar
minor_st_out == minor_reset minor_st /\
GenInv.collection_heap_shape minor_st_out s2 (fst res) /\
gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok /\
gen_gc_reachable_subgraph_isomorphism_post minor_st 's 'fp 'rs ok s2 rs2 /\
gen_gc_unreachable_final_blue_post minor_st 's 'fp 'rs ok s2
```

In prose, after a successful full generational collection:

- the nursery is reset -- not merely emptied, but zeroed;
- the whole shape invariant holds again, verbatim the predicate the
  precondition demands;
- roots have been rewritten consistently with minor forwarding;
- the post-minor reachable graph is preserved by the major collector;
- unreachable final major objects are blue/free.

There is deliberately no `gc_postcondition` conjunct here even though clients
want one.  It is a *consequence* of the shape invariant -- `well_formed_heap`
plus `no_black_objects` plus `no_gray_objects` gives "every object is white or
blue" by colour exhaustiveness -- so restating it would be redundant, and a
redundant conjunct is both an extra obligation inside `full_gc` and extra SMT
context at every call site.  `gen_gc_heap_shape_post` packages that consequence
for clients who want it without threading a free-list head, and
`gen_gc_heap_shape_post_intro` is the one-line derivation.

The final isomorphism story is compositional. Minor collection maps the original
combined minor+major reachable subgraph into the post-minor major heap. Major
collection then preserves the live major subgraph without moving objects and
turns unreachable objects blue.

## Auditing the specification with SPOTs

A verified implementation can still have an awkward or unusable top-level
contract. The SPOT campaign in `spot/` exists to test the proof surface from the
client's point of view.

SPOT stands for "small proof-oriented test." The goal is not to duplicate the
collector proof; it is to construct a small, concrete scenario and show that the
public preconditions can actually be established and the public postconditions
are strong enough to prove the expected facts.

The active `spot/` campaign is admit/assume-free and verifies locally with:

```bash
cd spot
make verify
```

The scenario is deliberately tiny:

- `A` is a reachable minor object.
- `B` is an unreachable minor object.
- `C` is a major object whose field 1 points to `A`.
- Roots before minor collection are `[C; A]`.
- The remembered slot table contains exactly `C.field1`.

The active modules are structured as follows:

| Module | Purpose |
| --- | --- |
| `GC.SPOT.Layout` | Names the concrete addresses: `A` and `B` are minor offsets (`8` and `24`) and proves basic distinctness/pointer facts. |
| `GC.SPOT.ConcreteMinor` | Constructs the two-object minor heap using the real minor allocation spec and packages `minor_heap_shape`. |
| `GC.SPOT.ConcreteMajor` | Constructs the major heap with `C` plus one blue free-list block and proves `major_heap_shape`. |
| `GC.SPOT.Preconditions` | Packages the real minor-collection and `full_gc` precondition bundles behind named predicates and elimination lemmas. |
| `GC.SPOT.Postconditions` | Packages the useful consequences of post-minor and post-full collection. |
| `GC.SPOT.ConcreteForwarding` | Proves that unreachable `B` keeps forwarding entry `0`. |
| `GC.SPOT.ConcreteScenarios` | Connects the concrete heaps, roots, slot table, and forwarding array to the real collection preconditions. |
| `GC.SPOT.ConcreteFull` | Connects post-minor facts to final `full_gc` postconditions. |
| `GC.SPOT.CallMinor` / `ConcreteCallMinor` | Pulse wrappers that call the real `minor_collect` (idle) and prove concrete consequences. |
| `GC.SPOT.CallFull` / `ConcreteCallFull` | Pulse wrappers that call the real `full_gc` (through `full_gc_from_shape`, which states it over the heap, the idle phase and `collection_heap_shape`, and returns the final free-list head beside the flag) and prove final survival facts. |
| `GC.SPOT.ThreeObjects` | The scenario layer: A is promoted, C.field1 is rewritten to A', B is not promoted, and C/A' survive full GC. |
| `GC.SPOT.InfixMajor` | A second, independent scenario: a ten-word major heap containing a genuine OCaml interior (infix) pointer. |
| `GC.SPOT.InfixPre` / `InfixPost` | Discharge `full_gc`'s precondition for that heap over an empty nursery, and read back its postcondition. |
| `GC.SPOT.InfixCall` | Pulse wrapper that calls the real `full_gc` on the infix heap. |

The main useful facts proved by the active SPOT are:

1. The real Pulse entry points `minor_collect` and `full_gc` are callable from
   concrete Pulse clients.
2. The concrete A/B/C heap satisfies the real collector preconditions.
3. The remembered table's single slot, C.field1, is enough to account for the
   major-to-minor edge.
4. A gets a nonzero promoted image A'.
5. C.field1 is rewritten from A to A' after minor collection.
6. B's forwarding entry remains zero, capturing that it was not promoted.
7. After the full generational collection, C and A' remain live in the final
   major heap, and C.field1 still points to A'.

The main concrete full-GC connector is
`GC.SPOT.ConcreteCallFull.call_concrete_gen_gc_spot`. It takes the actual linear
resources for the concrete heap, roots array, forwarding array, Cheney queue,
and remembered slot array (the mark stack is the collector's own). The pure
precondition for the scenario is proved inside
`GC.SPOT.ConcreteScenarios.spot_concrete_gen_gc_pre`, not assumed by the
caller.

This is a powerful audit because it checks both sides of a public formal
contract: the preconditions are not impossibly strong, and the postconditions
are not too weak for clients to use.

### The interior-pointer scenario

A second SPOT audits the relaxation of the major-heap invariant that admits
OCaml interior pointers. `GC.SPOT.InfixMajor` builds a ten-word major heap in
which a one-field object `Q` points *into the body* of a five-word closure `P`,
at an infix header. That target is never enumerated by `objects`, because its
header sits inside `P`'s body and the object walk steps over it.

The audit is two-sided, on one and the same heap:

* `spot_infix_violates_no_infix_field_targets` proves the heap **refutes**
  `GC.Spec.Fields.no_infix_field_targets`, the conjunct `major_heap_shape` used
  to carry. Under the old invariant this heap could not have been handed to the
  collector at all.
* `spot_infix_major_heap_shape` proves the heap **satisfies** every
  conjunct of the current `GC.Gen.HeapInvariant.major_heap_shape` — in
  particular `well_formed_heap` through the *resolved*-target formulation of
  the pointer clauses, with `resolve_object H == P` established from
  `GC.Spec.Object.infix_addr_conds`.

`GC.SPOT.InfixPre` discharges the remainder of `full_gc`'s precondition (empty
nursery, empty remembered table, single root `Q`) and proves the collection
cannot run out of memory. `GC.SPOT.InfixCall.call_gen_gc_infix` then calls the
real `full_gc` and proves that it succeeds, that `collection_heap_shape` holds
again of the state handed back, and that `Q` is still an enumerated object of
the post-collection heap. Interior pointers are therefore supported by the
shipped collector, not merely by an intermediate lemma.

## OCaml integration

The verified collector is integrated with the OCaml 4.14 bytecode runtime under
`generational/ocaml-integration/`. The most important file is
`generational/ocaml-integration/verified_gc/alloc_gen.c`, the C bridge between
OCaml and the extracted verified code.

The bridge provides:

```c
void *verified_allocate_minor(mlsize_t wosize, uint8_t tag);
void *verified_allocate(mlsize_t wosize, uint8_t tag);
extern uint64_t *vergc_minor_bump_ref;
extern uint8_t  *vergc_minor_base;
extern uint64_t  vergc_minor_size;
void verified_do_minor_gc(void);
CAMLprim value caml_trigger_verified_gc(value v);
```

It calls extracted functions from `GC_Gen_Impl.c`:

```c
minor_alloc(...)
allocate(...)
minor_collect(...)
start_cycle(...)   /* incremental */
major_slice(...)   /* incremental */
full_gc(...)       /* stop-the-world */
modify_field(...)      /* caml_modify, caml_array_fill */
initialize_field(...)  /* caml_initialize */
```

The bridge is deliberately outside the verified F*/Pulse boundary. Its job is to
connect two worlds that use different representations:

- OCaml values are absolute virtual addresses tagged as `value`.
- The verified major heap uses `U64.t` addresses relative to abstract
  `zero_addr`/`heap_size`.
- The verified minor heap uses offsets into a byte array.
- OCaml roots are discovered by `caml_do_roots`.
- OCaml remembered slots live in `Caml_state->_ref_table`.

### Major heap: the NULL-base trick

The major heap uses a clever trick to avoid translating every major pointer.
The bridge allocates a real major heap with `calloc`, sets `zero_addr` to its
absolute base address, sets `heap_size_u64` to the absolute end address, and then
sets the extracted heap's data pointer to `NULL`:

```c
uint8_t *major_base = (uint8_t *)calloc(1, major_bytes);

zero_addr = (uint64_t)(uintptr_t)major_base;
heap_size_u64 = (uint64_t)(uintptr_t)(major_base + major_bytes);

gc_gen_heap.major.data = NULL;
gc_gen_heap.major.size = major_bytes;
```

Then a verified "offset" is already the absolute address. A C access at
`major.data + offset` becomes `NULL + absolute_address`, i.e., the actual
virtual address. This eliminates a translation layer for major heap fields.

The bridge initializes the major heap as one big blue free block:

```c
uint64_t wosize = total_words_u64 - 1;
uint64_t blue_hdr = (wosize << 10) | (2ULL << 8) | 0ULL;
*(uint64_t *)major_base = blue_hdr;
*(uint64_t *)(major_base + 8) = 0;
uint64_t initial_fp = zero_addr + 8;
```

It also registers the major heap with OCaml's page table:

```c
caml_page_table_add(In_heap, major_base, major_base + major_bytes)
```

Without that registration, OCaml's write barrier would not recognize fields in
the verified major heap as major-heap slots.

### Minor heap: absolute pointers at the OCaml boundary, offsets in proofs

The minor heap uses a real data pointer:

```c
gc_gen_heap.minor.data = minor_data;
gc_gen_heap.minor.size = minor_sz;
gc_gen_heap.minor.bump_ref = bump_ref;
minor_base_addr = (uint64_t)(uintptr_t)minor_data;
```

The verified code reasons about minor offsets. OCaml sees absolute pointers.
The bridge translates roots that point into the minor heap:

```c
if (is_minor_absolute(root)) {
    translated = abs_to_minor_offset(root);
} else {
    translated = (uint64_t)(uintptr_t)root;
}

root_values[root_count] = translated;
root_locs[root_count] = root_ptr;
```

After collection, roots are written back to OCaml's actual root locations:

```c
*root_locs[i] = (value)(uintptr_t)rewritten;
```

The bridge does not eagerly scan the entire minor heap to translate every
absolute minor pointer into an offset before collection. Earlier versions had a
`translate_minor_fields` pass for that; it was unnecessary for correctness and
wasteful for performance, and has been removed.

Only values that cross the OCaml/verified boundary need up-front normalization:
root entries and remembered-slot targets are converted from absolute minor
pointers to minor offsets when they are placed in `root_values`. Everything else
is handled lazily by the verified collector itself. The extracted helper
`to_minor_offset_u64` uses the runtime `minor_base_addr` to turn an absolute
minor address into an offset when, and only when, such a value is read:

```fstar
inline_for_extraction
let to_minor_offset_u64 (v: U64.t) : Tot (r:U64.t{r == to_minor_offset v}) =
  let off = U64.sub_mod v minor_base_addr in
  if U64.lt off minor_heap_size_u64 && U64.eq (U64.rem v 8UL) 0UL
  then off
  else v
```

That helper is called in the live traversal path: `cheney_forward_fields`
normalizes each minor field as Cheney scans a promoted object, `update_one_field`
normalizes promoted major fields before looking them up in the forwarding array,
and `rewrite_one_slot` normalizes remembered-slot contents. This means dead
minor objects are never scanned just to translate their fields. The reachable
minor subgraph is discovered by the same BFS that proves forwarding coverage,
and major-to-minor edges are covered by the remembered table. Eagerly translating
the whole nursery would add an O(minor-heap) preprocessing pass without adding a
new invariant: the proof already accounts for exactly the live roots, live minor
edges, and remembered major slots that collection can observe.

The bridge also updates OCaml's domain state so that `Is_young` recognizes the
verified minor heap:

```c
Caml_state->_young_start = (value *)minor_data;
Caml_state->_young_end   = (value *)(minor_data + minor_sz);
Caml_state->_young_ptr   = Caml_state->_young_end;
```

### Remembered slots and write barrier compatibility

OCaml's `caml_modify` records major fields that receive young pointers in
`Caml_state->_ref_table`.  In this runtime the decision is the verified
barrier's (`modify_field` / `initialize_field`, above): the patched
`caml_modify` / `caml_initialize` call `add_to_ref_table` exactly when it
returns true, and the table itself, and its growth, stay stock's. The bridge
passes that table directly to `minor_collect`:

```c
struct caml_ref_table *tbl = Caml_state->_ref_table;
size_t n_slots = (size_t)(tbl->ptr - tbl->base);

promote_ok = minor_collect(gc_gen_heap, root_values,
                           (size_t)root_count, gc_fwd_arr,
                           gc_queue,
                           (uint64_t *)tbl->base, n_slots);
```

It also adds the minor targets of remembered slots to the minor root set before
collection:

```c
for (r = tbl->base; r < tbl->ptr; r++) {
    value v = (value)(uintptr_t)(**r);
    if (is_minor_absolute((value)v64)) {
        uint64_t off = v64 - (uint64_t)(uintptr_t)minor_base;
        root_values[root_count] = off;
        root_locs[root_count] = NULL;
        root_count++;
    }
}
```

This matches the verified precondition that remembered targets are included in
the root set.

### Full GC roots and the persistent mark stack

Stop-the-world, a major collection calls the extracted verified `full_gc`.
Incremental, a cycle starts right after a minor collection: `start_cycle`
darkens the roots that minor collection just rewrote (`root_values`, still
holding them), so the nursery is empty and the roots are post-minor, as
`start_cycle` asks.  The mark stack is the collector's own, allocated once at
heap set-up with the rest of the mark state (`gen_heap_t.mark_stack`,
`mark_overflow`, `mark_cur`, `mark_field`, `mark_rescan`, and the counter
`mark_words`):

```c
/* stw: do_full_gc_stw */
ok = full_gc(gc_gen_heap, roots_for_gc, root_count, gc_fwd_arr,
             gc_queue, (uint64_t *)tbl->base, n_slots);

/* incremental: do_minor_gc, at Idle when the trigger fires */
promoted = do_minor_gc_core();          /* minor_collect, roots rewritten in root_values */
start_cycle(gc_gen_heap, root_values, root_count);   /* the phase becomes Marking */
/* ... and after every later minor collection, until Idle: */
major_slice(gc_gen_heap, budget);       /* marks, then sweeps */
```

The verified protocol is:

1. `minor_collect` rewrites the roots array in place and rewrites the
   remembered major slots.
2. `start_cycle` darkens the rewritten post-minor roots (`darken_roots_bounded`:
   it greys the root objects and pushes them onto the persistent mark stack
   while it has room; the overflow flag goes up when the stack ends full) and
   enters `Marking`.
3. `major_slice` marks while marking (handing over to the sweep when nothing
   is grey), then sweeps, until the collector is idle; `full_gc` does all of
   it with unbounded budgets, the incremental bridge runs a paced slice after
   each minor collection, with the program running in between.

The capacity of the mark stack is `max(heap_bytes / 64, 4096)`, or
`VERGC_MARK_STACK` entries (a testing knob: `tests/gray_overflow.ml` runs with
3, so root darkening overflows and every slice rescans).

The bridge keeps the original `root_values[]` and `root_locs[]` outside the
verified stack. After the collection returns, `write_back_forwarded_roots()` uses the
original root values plus the forwarding array to update only real OCaml root
locations. Remembered-table entries have `root_locs[i] == NULL`; their owning
major slots have already been rewritten by verified code.

### GC triggers and OOM handling

Small allocation uses a minor-only bridge entry point. If the minor heap cannot
fit the object, the bridge runs minor collection and retries `minor_alloc`; it
does not fall back to the major heap for `Alloc_small_aux`:

```c
if (*gc_gen_heap.minor.bump_ref > minor_heap_size_u64 - needed) {
    do_minor_gc();
}

uint64_t result =
    minor_alloc(gc_gen_heap.minor, (uint64_t)wosize, (uint64_t)tag);
```

Shared/large allocation calls the verified major free-list allocator directly,
tries a full GC on failure, and finally raises a fatal runtime error if the
fixed-size heaps cannot satisfy the request. Promotion failure is also fatal:

```c
if (!promote_ok) {
    fatal_promotion_failed();
}
```

The current integration therefore demonstrates a fixed-size verified heap rather
than a fully expanding OCaml heap. Heap expansion is one of the natural next
steps.

### Extraction snapshots

The extraction target is configured in `generational/Makefile`. The extracted
bundle includes generational modules, mark-and-sweep implementation modules, and
common low-level modules:

```make
ALL_KRML_MODS = \
  GC.Gen.Impl GC.Gen.Impl.MinorHeap GC.Gen.Impl.Cheney \
  GC.Gen.Impl.Promote GC.Gen.Impl.UpdatePtrs \
  GC.Gen.Base \
  GC.Impl GC.Impl.Fields \
  GC.Impl.MarkBounded \
  GC.Impl.FusedSweepCoalesce GC.Impl.Allocator \
  GC.Impl.ArrayWord GC.Impl.Heap GC.Impl.Object GC.Impl.Stack \
  GC.Spec.ZeroAddr GC.Spec.Base GC.Spec.Heap GC.Spec.Object \
  GC.Lib.Header GC.Lib.Address
```

The `snapshot` target copies the generated C, headers, and minimal KaRaMeL
support into `generational/snapshot/` for the OCaml integration build. The C
bridge uses those extracted files rather than reimplementing the collector. The
extracted files are not patched after extraction: the snapshot is a packaging
step, not a source-rewriting step. Runtime-specific adaptation belongs in
`alloc_gen.c` and in the OCaml runtime patch described below.

### OCaml runtime patch

The integration does patch OCaml 4.14 itself, but that is separate from the
extracted verified C. `generational/ocaml-integration/patches/runtime_gen.patch`
modifies the runtime so bytecode programs call the verified collector:

- `runtime/Makefile` builds and links `verified_gc/libvergc_gen.a` into
  `ocamlrun`.
- `runtime/caml/domain_state.tbl` adds a temporary root slot used around
  allocation calls.
- `runtime/caml/memory.h` performs inline bump allocation for small minor
  objects when the verified minor heap has space, and falls back to
  `verified_allocate_minor` for heap initialization and collection.  That slow
  path collects and retries in the minor heap, matching stock OCaml's
  `Alloc_small` behavior rather than sending small objects to the major heap.
  The inline fast path writes the OCaml header itself; slow minor allocations
  reuse the extracted header unless reserved profinfo bits are enabled.
- `runtime/memory.c` routes `caml_alloc_shr_aux` through `verified_allocate`
  for major allocations, and `caml_modify` / `caml_initialize` through the
  verified barrier (`modify_field` / `initialize_field`) for a slot of the
  verified major heap; `runtime/array.c`'s `caml_array_fill` (which duplicates
  `caml_modify`'s logic) through the same.
- `runtime/interp.c` wraps allocation sites with `Setup_for_gc` /
  `Restore_after_gc` where verified allocation may trigger collection.
- `runtime/minor_gc.c` disables OCaml's stock minor collection entry points so
  the verified collector owns collection.

In short: the extracted collector snapshot is used as generated; the OCaml
runtime is patched to call it.

## Benchmarking

The integration tests use bytecode programs adapted from the Computer Language
Benchmarks Game:

```make
BENCHMARKS = binarytrees fasta quicksort fannkuchredux count_change nbodies spectralnorm mandelbrot
```

The test Makefile can run smoke tests with the verified generational runtime and
hyperfine benchmarks against stock OCaml:

```bash
cd generational/ocaml-integration/tests
make test
make benchmark   # or make bench-all
make bench-stats # just collect GC/RSS statistics
make bench-min-heaps # calibrate verified heap size from stock RSS
```

The fresh hyperfine run writes timing CSVs to `results/*.bench.csv`. `bench-all`
also emits companion `results/*.stats.csv` files with one row per runtime. These
stats files report the OCaml allocation metric (`total_allocated_words =
minor_words + major_words - promoted_words`), the component allocation-word
counters, minor/major/forced-major collection counts, heap/top-heap words, and
peak RSS in MiB from `/proc/self/status`.

The verified GC uses a fixed-size major heap configured by
`MIN_EXPANSION_WORDSIZE` plus a fixed minor heap. `make bench-min-heaps` measures
stock OCaml RSS for each benchmark, rounds that RSS up to the 1 MiB heap
granularity, and searches upward for the smallest verified major heap that runs
at or above that stock-RSS baseline. These calibrated sizes are sufficient to
run the benchmark, not necessarily the best performance point: smaller heaps can
substantially increase the number of full major sweeps. The tracked current
timing, stats, and heap-calibration snapshots are mirrored in:

- `generational/ocaml-integration/tests/results_final/`

The older `results_fastpath/`, `results_inline/`, and `results_wordlevel/`
directories are retained as comparison snapshots from earlier optimization
steps.

The default configured-heap timing run compares `verified-gen` with
`stock-ocaml`:

| Benchmark | verified-gen mean (s) | stock OCaml mean (s) | Ratio |
| --- | ---: | ---: | ---: |
| `binarytrees` | 15.685 ± 0.048 | 12.322 ± 0.060 | 1.27x |
| `count_change` | 0.371 ± 0.007 | 0.197 ± 0.004 | 1.88x |
| `fannkuchredux` | 68.934 ± 0.598 | 68.152 ± 0.116 | 1.01x |
| `fasta` | 3.619 ± 0.020 | 2.546 ± 0.008 | 1.42x |
| `mandelbrot` | 2.869 ± 0.008 | 1.843 ± 0.009 | 1.56x |
| `nbodies` | 0.711 ± 0.014 | 0.303 ± 0.005 | 2.34x |
| `quicksort` | 7.987 ± 0.064 | 7.772 ± 0.055 | 1.03x |
| `spectralnorm` | 3.325 ± 0.009 | 2.166 ± 0.016 | 1.54x |

The geometric-mean slowdown for this run is 1.45x, with a max slowdown of 2.34x
on `nbodies`. Compute-heavy benchmarks such as `fannkuchredux` and `quicksort`
are near parity, while allocation/runtime-sensitive cases still show the largest
overheads.

The current conclusion is therefore more nuanced than "within 2x." Some
microbenchmarks are near stock OCaml, and several are around 2x, but the
end-to-end runtime still pays overheads from the bridge, fixed-size heap policy,
root/remembered-slot handling, forwarding arrays, and less optimized allocation
paths. That is exactly why having the verification in place is valuable: future
optimization work can target these overheads without weakening the collector's
core invariants.

The stock-RSS-seeded heap calibration shows how conservative the current fixed
heap settings are:

| Benchmark | stock RSS (MiB) | calibrated verified major heap (MiB) | Heap / stock RSS | current configured heap (MiB) | Current / stock RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| `binarytrees` | 515.898 | 516.000 | 1.000x | 1024.000 | 1.985x |
| `count_change` | 31.992 | 32.000 | 1.000x | 152.588 | 4.770x |
| `fannkuchredux` | 2.395 | 3.000 | 1.253x | 256.000 | 106.889x |
| `fasta` | 24.023 | 25.000 | 1.041x | 1024.000 | 42.626x |
| `mandelbrot` | 4.465 | 5.000 | 1.120x | 256.000 | 57.335x |
| `nbodies` | 4.527 | 5.000 | 1.104x | 256.000 | 56.550x |
| `quicksort` | 41.008 | 42.000 | 1.024x | 61.035 | 1.488x |
| `spectralnorm` | 4.605 | 5.000 | 1.086x | 256.000 | 55.592x |

So the large RSS numbers in the default verified runs mostly reflect conservative
fixed-heap choices, not inherent live-set requirements. At the calibrated heaps,
the verified runtime still has its minor heap, runtime metadata, collector
auxiliary state, stack/code/data mappings, allocator metadata, page alignment,
and touched-page high-water effects. The `verified heap/RSS` column below is
therefore `configured verified major heap / whole-process peak RSS`, not two
measurements of the same thing. For example, `nbodies` reports `5/14.137`: the
verified major heap is 5 MiB, while the process peak RSS is 14.137 MiB after
including the rest of the runtime and collector footprint. The minimum-to-run
settings are useful for memory comparisons, while the larger configured heaps
keep the timing runs from being dominated by repeated full-heap sweeps.

A calibrated-heap hyperfine pass, using those minimum-to-run major heaps for the
verified runtime, combines timing with the allocation and GC counters below.
Columns with `stock/ver` list stock OCaml first and verified GC second. The
calibrated-heap timing and merged snapshots are in
`results_final/calibrated_heap.bench.csv` and
`results_final/combined_perf_stats.csv`.

| Benchmark | stock time (s) | verified @ calibrated heap (s) | slowdown | stock RSS (MiB) | verified heap/RSS (MiB) | total alloc words stock/ver | minor GCs stock/ver | major GCs stock/ver | forced major GCs stock/ver |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `binarytrees` | 12.225 +/- 0.036 | 18.383 +/- 0.252 | 1.50x | 515.898 | 516/528.449 | 1,993,131,309/1,993,131,309 | 7,647/7,604 | 87/58 | 1/0 |
| `count_change` | 0.198 +/- 0.001 | 0.422 +/- 0.004 | 2.14x | 31.992 | 32/44.793 | 23,166,011/23,166,011 | 91/88 | 7/9 | 0/0 |
| `fannkuchredux` | 68.012 +/- 0.130 | 70.017 +/- 0.173 | 1.03x | 2.395 | 3/2.500 | 5,840/5,840 | 0/0 | 0/0 | 0/0 |
| `fasta` | 2.548 +/- 0.004 | 2.922 +/- 0.022 | 1.15x | 24.023 | 25/36.691 | 207,824,073/207,824,073 | 785/783 | 1/111 | 0/0 |
| `mandelbrot` | 1.846 +/- 0.006 | 2.427 +/- 0.013 | 1.31x | 4.465 | 5/14.129 | 394,518,214/394,518,214 | 1,508/1,504 | 8/752 | 1/0 |
| `nbodies` | 0.303 +/- 0.005 | 0.489 +/- 0.008 | 1.61x | 4.527 | 5/14.137 | 106,007,085/106,007,085 | 405/404 | 2/202 | 0/0 |
| `quicksort` | 7.809 +/- 0.054 | 7.897 +/- 0.055 | 1.01x | 41.008 | 42/40.867 | 5,006,520/5,006,520 | 1/0 | 0/0 | 0/0 |
| `spectralnorm` | 2.199 +/- 0.037 | 2.947 +/- 0.018 | 1.34x | 4.605 | 5/14.145 | 400,043,844/400,043,844 | 1,528/1,525 | 7/762 | 1/0 |

The calibrated-heap geometric-mean slowdown is 1.35x, with a maximum of 2.14x
on `count_change`. The allocation-word totals match across the runtimes; the
main behavioral difference is the collection schedule. These calibrated heaps
are the smallest heaps found by the stock-RSS-seeded search, not
throughput-tuned heaps. For allocation-heavy benchmarks such as `nbodies`,
`spectralnorm`, `fasta`, and `mandelbrot`, a 5 MiB or 25 MiB verified major heap
leaves little slack after each batch of promotions. The verified runtime is
currently pinned to that fixed heap and uses stop-the-world full major
mark/sweep when it needs major space, while stock OCaml grows/tunes the major
heap and amortizes major work under its normal policy. That is why, for example,
`spectralnorm` has 762 verified major collections at the 5 MiB calibrated heap
but only 23 verified major collections at the earlier 256 MiB configured heap.

## Proof engineering notes

Several proof-engineering patterns recur across the repository.

### Keep pure specs and Pulse implementations connected by exact postconditions

The implementation contracts often say "the imperative result equals the pure
spec result." Examples include `allocate`, `minor_collect`, and the
lower-level update/heap operations. This pattern is extremely effective: prove
the algorithm once as a pure function, then prove the Pulse code refines it.

### Split heap shape into just enough pieces

The generational collector would be much harder to prove if every function
required the whole invariant. Instead, the development factors shape predicates:

- `blocks_fit` for object bounds (and `no_infix_block`: the walk facts are all
  promotion reads of the major heap);
- free-list validity and termination for allocation;
- `collection_shape_with ph free` for a minor collection at a phase, for any
  definition of free the allocator at the phase makes no block of, and
  `collection_heap_shape` for the stop-the-world collector;
- the major collector's own precondition, derived from the post-minor heap
  inside `full_gc` (`GC.Gen.MajorPrecondition`).

This factoring is why promotion can call the allocator in the middle of a
collection: `allocate` asks nothing of the heap, and the allocator lemmas need
only part 1 and the free-list facts.

### Hide large predicates from SMT and expose intro/elim lemmas

Many central predicates are marked `opaque_to_smt` and paired with intro/elim
lemmas. This prevents Z3 from unfolding a giant invariant everywhere and lets
proofs reveal exactly the part they need.

### Use graph abstractions aggressively

The project becomes tractable when heap operations are related to graph
operations:

- `HeapGraph.get_pointer_fields` explains how fields become successors.
- `HeapModel.create_graph` gives a graph for a heap (`create_graph_with free`
  keeps only the edges out of the non-free blocks).
- mark-and-sweep correctness is stated over reachability in that graph.
- generational correctness uses a combined graph and a forwarding morphism.

The graph layer is not decoration; it is the specification language that makes
collection correctness concise enough to use.

### Bounded resources require new invariants, not just extra code

The bounded mark stack is a good example. The implementation change is small:
skip a push on overflow and rescan later. The proof change is conceptual: the
old invariant "all gray objects are on the stack" is false. The bounded proof
uses a weaker local stack invariant plus a global rescan argument.

### Infix pointers force precision

OCaml infix objects are interior pointers into closures. A copying collector
must not copy an infix sub-object as if it were an independent object. The
collector forwards the parent and then maps the infix address by preserving the
offset. The heap invariants also rule out problematic field targets into minor
infix interiors. This is one of the places where matching the real OCaml runtime
matters.

### SPOTs are specification tests, not just demos

The `spot/` campaign found and fixed the shape of the public contracts. A
contract that cannot be instantiated on a three-object heap is probably not the
right contract. A postcondition that cannot prove "C.field1 now points to A'" is
not strong enough. The SPOTs turn those judgments into checked artifacts.

## What remains outside the verified boundary

The core collector algorithms and their F*/Pulse contracts are verified, but the
end-to-end system still has trusted or unverified components:

- the F* and Pulse toolchain;
- KaRaMeL extraction and the C compiler;
- the OCaml runtime patches;
- the C bridge in `alloc_gen.c`;
- platform assumptions such as `size_t` fitting in 64 bits;
- fixed-size heap allocation and fatal OOM policy;
- runtime constants that override proof defaults for realistic heap sizes.

This boundary is normal for a verified systems project, but it is important to
name it. The repository verifies the collector logic and the extracted entry
points' contracts; it does not verify the whole OCaml runtime.

## How to read or extend the repository

For a first pass through the code, read in this order:

1. `common/lib/GC.Lib.Header.fst` for OCaml headers and colors.
2. `common/spec/GC.Spec.Base.fsti`, `Heap.fsti`, and `Object.fsti` for heap and
   address basics.
3. `common/spec/GC.Spec.Fields.fst`, `Graph.fst`, `HeapGraph.fst`, and
   `HeapModel.fst` for object enumeration and heap graphs.
4. `mark-and-sweep/spec/GC.Spec.Allocator.fsti` and
   `mark-and-sweep/impl/GC.Impl.Allocator.fsti` for the major allocator.
5. `mark-and-sweep/spec/GC.Spec.Correctness.fst` and
   `mark-and-sweep/impl/GC.Impl.fsti` for major GC correctness.
6. `mark-and-sweep/spec/GC.Spec.MarkBounded.fsti` and
   `mark-and-sweep/impl/GC.Impl.MarkBounded.*` for bounded marking.
7. `generational/spec/GC.Gen.HeapInvariant.fst` for the generational invariant.
8. `generational/spec/GC.Gen.MinorHeap.fst`,
   `GC.Gen.Promote.fsti`, `GC.Gen.Cheney.fsti`, `GC.Gen.Cheney.Induction.fsti`,
   `GC.Gen.Cheney.Steps.fsti`, `GC.Gen.CheneyGeneric.fsti`, and
   `GC.Gen.CheneyBFS.fsti` for minor collection.
9. `generational/spec/GC.Gen.CombinedGraph.fsti` and
   `GC.Gen.MinorCollectForwarding.fsti` for isomorphism correctness.
10. `generational/impl/GC.Gen.Impl.fsti` for the public Pulse API.
11. `spot/GC.SPOT.*` for concrete client-side audits.
12. `generational/ocaml-integration/verified_gc/alloc_gen.c` for the runtime
    bridge.

When changing `common/`, re-verify downstream collectors. When changing
mark-and-sweep, re-verify generational. When changing a public generational
contract, re-run `spot` because the SPOTs are the best guard against unusable
specifications.

Useful targeted commands:

```bash
# Root closure verification
make

# Generational root verification
cd generational && make verify

# SPOT audit
cd spot && make verify

# Extract generational C
cd generational && make extract

# Create integration snapshot
cd generational && make snapshot
```

For stubborn F* goals, the local Makefiles show the tuning already used in the
project: `--retry 3` (a workaround for Z3 4.15.3 flakiness on trivial leaf
goals), a raised `smt.qi.eager_threshold` on individually opted-in modules,
higher `--z3rlimit`, `--z3refresh`, and `--query_stats` on modules that stress
the solver. When `--retry` isn't enough, the standard remedy in this codebase is
to lift the failing fact into a top-level helper lemma so it is proved in an
empty context; `GC.Spec.Base` collects the recurring ones (`heap_words`,
`mk_hp_addr`, `aligned_plus_mul8`).

## Looking ahead: incremental and concurrent GC

The current collector is generational but still stop-the-world at collection
boundaries. It sets the stage for incremental or concurrent verification in
several ways:

- The heap/object/header model already matches OCaml's runtime representation.
- The graph layer already separates semantic reachability from physical layout.
- The generational proof already handles moving collection via a forwarding
  morphism.
- Remembered slots and root rewriting are already explicit.
- The bounded mark stack already reasons about realistic resource limits.
- SPOTs provide a way to audit future public contracts with concrete scenarios.

An incremental collector would need to expose and preserve phase-indexed
invariants across mutator steps. A concurrent collector would need a verified
write barrier, atomic color/mark state, and a separation-logic story for sharing
heap ownership between collector and mutator. The tri-color invariant would move
from an internal mark-phase theorem to a continuously maintained global
invariant: no black object may point to a white object unless a barrier accounts
for it.

The present development is therefore not the end of the story. It is a verified
foundation: a code-grounded, extracted, integrated generational collector with
strong graph-based correctness theorems, realistic allocator and stack
constraints, concrete specification audits, and enough performance data to know
where the next engineering iteration should focus.
