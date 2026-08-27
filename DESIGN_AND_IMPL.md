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
   verified generational `gen_gc`.
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
                         | remembered slots, gen_gc          |
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
    if is_no_scan h_addr g then Seq.empty
    else get_pointer_fields_aux g h_addr 1UL ws
```

The main heap well-formedness predicate lives in
`common/spec/GC.Spec.Fields.fst`:

```fstar
let well_formed_heap (g: heap) : prop =
  well_formed_heap_part1 g /\
  well_formed_heap_part2 g /\
  well_formed_heap_part3 g /\
  well_formed_heap_part4 g
```

The four parts say:

1. Every enumerated object fits in the heap.
2. Every pointer field of every object points *into* another enumerated object:
   the target's enclosing block (`resolve_object`) is enumerated.
3. Infix objects are well-formed relative to their parent objects.
4. The enumerated object list excludes infix sub-objects as independent roots of
   the object traversal.

#### Interior (infix) pointers in major fields

Parts 2 and 3 are stated on the **resolved** target, not on the raw field value:

```fstar
let well_formed_heap_part2 (g: heap) : prop =
  forall (src dst: obj_addr).
    Seq.mem src (objects zero_addr g) /\
    exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst ==>
    Seq.mem (resolve_object dst g) (objects zero_addr g)
```

`resolve_object` is the identity on an ordinary pointer and maps an interior
pointer to the head of the closure that contains it. So part 2 says *the
enclosing block of every field target is an enumerated object*, which is exactly
OCaml's rule, and part 3 (`infix_wf`) is the non-vacuous side condition that
makes the mapping well defined: an infix header carries the offset back to its
parent, that parent is itself an enumerated object, and it has `Closure_tag`.

This matters because **mutually recursive OCaml closures are represented with
interior pointers**: a single allocated block holds several code pointers, and
the fields that refer to the second and later functions point *into* the middle
of that block, at a header whose tag is `Infix_tag = 249`. An earlier version of
this development stated part 2 on the raw field value, which — combined with
part 4 (no enumerated object is itself infix) — made `well_formed_heap`
*unsatisfiable* for any heap containing such a closure. The correctness theorem
was sound but empty on that class of heaps.

Two consequences of the resolved formulation:

- `well_formed_heap_part3` is now load-bearing. The parent-closure machinery it
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

##### Residual restriction: free-list cells only

Both collectors handle interior pointers out of *live* objects in full
generality.  The generational (Cheney) collector retains one narrow residual
restriction: a **blue** (free-list) cell may not hold an interior pointer.  This
is expressed by an explicit, opaque, **optional** predicate

```fstar
let blue_fields_non_infix (g: heap) : prop =
  forall (src dst: obj_addr).
    Seq.mem src (objects zero_addr g) /\ GC.Spec.Object.is_blue src g /\
    exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst ==>
    ~(is_infix dst g)
```

which appears as a conjunct of `GC.Gen.HeapInvariant.major_heap_shape` and
nowhere in `well_formed_heap`.  It is not a mutator-visible constraint: free-list
cells are owned by the allocator, their fields hold link words and stale data,
and no OCaml program can arrange for one to point into the interior of another.
It sits alongside the pre-existing `minor_fields_no_infix_targets` and
`major_minor_fields_no_infix_targets` clauses, which impose the same restriction
on *nursery*-directed pointers.

It is preserved across *minor* collection for free: the Cheney machinery already
proves raw `well_formed_heap_part2` for blue objects, which
`blue_fields_closed_implies_blue_fields_non_infix` converts.

Across a *major* collection it is not free, and it is worth being precise about
why it holds, because it would be false if the collector simply threaded dead
blocks onto the free list.  A dying object may hold interior pointers, and sweep
alone (`GC.Spec.Sweep.sweep_object`) rewrites only its link word -- the rest of
the corpse survives untouched.  What makes the clause true is the **coalescing
pass**: `GC.Spec.Coalesce.flush_blue` writes the blue header, sets the free-list
link, and then calls `Alloc.zero_fields` over every remaining field of the merged
block (extracted as `flush_blue_impl` / `zero_fields_loop`).  A blue cell
therefore has exactly one pointer-shaped field, its link, which is an object
address and never an interior one.

That is proved by `GC.Spec.Coalesce.coalesce_blue_fields_non_infix`, lifted by
`GC.Spec.Correctness.gc_blue_fields_non_infix_gen`, and carried through the
postconditions of `GC.Impl.collect_with_roots` and `GC.Gen.Impl.gen_gc`.  The
invariant is closed: what `major_heap_shape` demands on entry, `gen_gc`
re-establishes on exit, on both the normal and the out-of-memory path.  Note it is kept out of `gc_postcondition` on purpose --
that predicate is also asserted of the post-sweep, pre-coalesce heap, which does
not satisfy the clause.

Infix addresses survive as **roots** for both collectors, and inside Cheney's
promotion machinery, which is what `find_infix_parents` and
`synthesize_infix_forwarding` operate on in the extracted C.

Getting here removed two obstructions.  The first was the graph model:
`GC.Gen.CombinedGraph.classify_major_field` now resolves, returning
`MajorV (resolve_object v major)` whenever the resolved value is enumerated, so
an interior-pointer edge is no longer silently dropped;
`GC.Gen.ReachabilityBridge.major_edge_points_to` exposes the raw field value
alongside `dst == resolve_object raw major`.

The second was the allocator.  `GC.Gen.Promote.blue_fields_closed` is stated on
the *raw* field value of a free-list cell and is derived from part 2 by
`wfh_part2_implies_blue_fields_closed`, which needs a non-infix hypothesis for
exactly that step — but only over blue sources, which is what
`blue_fields_non_infix` supplies.  Deliberately keeping `blue_fields_closed`
raw is what makes this work: restating it in resolved form instead breaks
`promote_object_preserves_bfc_close`, which would then have to transport a
resolution across `copy_fields` on a block just carved off the free list.
`docs/infix-support-plan.md` §5 records the measurement.

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
`no_infix_field_targets` was narrowed to `blue_fields_non_infix`, they are inside
`GC.Gen.HeapInvariant.major_heap_shape` and the composed `gen_gc` theorem applies
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
/// 5. Recolor allocated block's header to White, tag 0
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

The key implementation contract is intentionally simple: the Pulse allocator
returns a heap that is exactly the pure `alloc_spec` result.

```fstar
fn allocate (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap 's)
  returns res: (U64.t & U64.t)
  ensures exists* s2. is_heap heap s2 **
    pure (let spec_res = SpecAlloc.alloc_spec 's fp (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fst res == spec_res.fp_out /\
          snd res == spec_res.obj_out)
```

There is also a weaker `allocate_part1` contract used during promotion:

```fstar
fn allocate_part1 (heap: heap_t) (fp: U64.t) (wosize: U64.t)
  requires is_heap heap 's **
           pure (SpecFields.well_formed_heap_part1 's /\
                 AllocLemmas.fl_valid 's fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's fp (heap_size / U64.v mword))
```

This weaker precondition is important. During minor-to-major promotion, the
major heap is temporarily not fully pointer-closed: fields may still contain old
minor pointers until the update pass rewrites them. The allocator does not need
pointer closure. It only reads headers and free-list links. Factoring the
contract this way lets promotion allocate into a temporarily intermediate major
heap without pretending the entire generational invariant already holds.

The allocator proof establishes the facts one expects from a systems allocator:

- the object returned on success came from a blue block;
- the returned object is fresh with respect to the allocated-object view;
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
  SpecMark.no_pointer_to_blue s /\
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

### Sweep and free-object coalescing

After marking completes there are no gray objects: black objects are the live
major-heap objects, while white objects are unreachable. The sweep phase resets
black survivors to white and turns unreachable objects into blue free blocks.
To reduce fragmentation, the implementation does not leave one free-list entry
per dead object. It coalesces adjacent blue objects into one larger blue block
and builds a fresh free list from those merged blocks.

The pure coalescing spec is `GC.Spec.Coalesce`. It walks the post-sweep object
list in address order and carries a pending blue run:

```fstar
let rec coalesce_aux (g0: heap) (g: heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (heap & U64.t)
```

`g0` is the frozen heap used for color and size decisions; `g` is the heap being
rewritten. A blue object extends the pending run by `wosize + 1` words, counting
the header. A white survivor ends the run: `flush_blue` writes one merged blue
header at the first object's header address, stores the previous free-list head
in field 1 when the merged block has room for a link, zeroes the remaining
payload words, and returns the first object of the run as the new free-list
head. A zero-word run is a no-op, and a one-word run can only be represented as
a header-only blue block because it has no field in which to store a free-list
link.

The Pulse implementation uses the fused entry point
`GC.Impl.FusedSweepCoalesce.fused_sweep_coalesce`, which performs sweep and
coalescing in one heap traversal. It keeps the same pending-run state
`(first_blue, run_words, fp)` but checks colors and sizes against the original
marked heap:

```fstar
let rec fused_aux (g0: heap) (g: heap) (objs: seq obj_addr)
    (fb: U64.t) (rw: nat) (fp: U64.t)
  : GTot (heap & U64.t) =
  if Seq.length objs = 0 then
    flush_blue g fb rw fp
  else if is_black (Seq.head objs) g0 then
    let (g', fp') = flush_blue g fb rw fp in
    fused_aux g0 (makeWhite (Seq.head objs) g') (Seq.tail objs) 0UL 0 fp'
  else
    fused_aux g0 g (Seq.tail objs) new_fb (rw + ws + 1) fp
```

So a live black object first flushes any preceding free run and is then whitened;
a non-black object is accumulated into the current free run without writing the
heap. The top-level fused pass starts with an empty free list (`fp = 0UL`), so
the final free list is a fresh list of the coalesced free runs rather than a
mutation of the pre-GC free list.

The proof deliberately separates the easy specification from the efficient
implementation. `GC.Spec.Coalesce` proves that coalescing only changes blue
regions: survivor headers and fields are preserved, the heap length and
well-formedness are preserved, all final objects are white or blue, and the
returned free-list head is either null or a valid object in the coalesced heap.
Those survivor-preservation lemmas are what let the end-to-end correctness proof
reuse the existing mark/sweep graph facts: live edges and scalar fields are
unchanged by coalescing because live objects are white after sweep, and
coalescing writes only the blue runs.

The key bridge theorem is
`GC.Spec.SweepCoalesce.fused_eq_sweep_coalesce`:

```fstar
let fused_eq_sweep_coalesce (g: heap) (fp: U64.t)
  : Lemma
    (requires well_formed_heap g /\
              SI.heap_objects_dense g /\
              SpecSweep.fp_in_heap fp g /\
              (forall x. Seq.mem x (objects zero_addr g) ==> ~(is_gray x g)))
    (ensures fused_sweep_coalesce g ==
             SpecCoalesce.coalesce (fst (SpecSweep.sweep g fp)))
```

Its induction relates two walks over the same dense object sequence: the fused
walk over the marked heap, and the standalone coalescing walk over the
post-sweep heap. The proof establishes that sweep preserves object order and
wosizes, that a pre-sweep black object corresponds exactly to a non-blue
post-sweep survivor, and that black-object headers, tags, and bodies agree
between the two heaps except for the color reset. For pending free runs,
`flush_blue` is deterministic: inside the run both sides write the same merged
blue header, link field, and zero padding; outside the run both sides preserve
the previous word reads. With those facts, the relational induction shows each
fused loop step matches the corresponding sweep-then-coalesce step.

Finally, `GC.Impl.collect_with_roots` calls the fused Pulse implementation but
then invokes `fused_eq_sweep_coalesce` to expose the result as the simpler
`coalesce (sweep ...)` specification. The end-to-end theorems
`gc_postcondition_gen`, `full_gc_correctness_through_coalesce_gen`,
`major_gc_live_subgraph_isomorphism_gen`, and
`major_gc_unreachable_final_blue_gen` therefore prove correctness of the actual
single-pass implementation while reasoning at the cleaner two-phase level.

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
`generational/spec/GC.Gen.HeapInvariant.fst`:

```fstar
let major_heap_shape (major: heap) (fp: U64.t) : prop =
  well_formed_heap major /\
  AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
  AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
  FreeListShape.fp_pointer_or_zero fp /\
  FreeListShape.blue_link_fields_valid major /\
  heap_objects_dense major /\
  chain_objects_blue major fp /\
  Seq.length (objects zero_addr major) > 0 /\
  SweepInv.fp_valid fp major /\
  Sweep.fp_in_heap fp major /\
  Mark.no_black_objects major /\
  Mark.no_pointer_to_blue major /\
  no_scan_invariant major

let minor_heap_shape (minor: minor_state) : prop =
  minor_wf minor /\
  minor_guards_complete minor /\
  minor_infix_wf minor /\
  minor_no_scan_invariant minor /\
  minor_fields_no_infix_targets minor

let collection_heap_shape (minor: minor_state) (major: heap) (fp: U64.t) : prop =
  major_heap_shape major fp /\
  minor_heap_shape minor /\
  minor_major_fields_no_blue minor major /\
  major_minor_fields_no_infix_targets minor major

let full_heap_shape (minor: minor_state) (major: heap) (fp: U64.t)
                    (st: seq obj_addr) (cap: nat) : prop =
  collection_heap_shape minor major fp /\
  major_stack_shape major st cap
```

`collection_heap_shape` is the pre-minor-collection invariant. `full_heap_shape`
adds the major mark-stack facts needed when a full generational cycle will run a
major collection after the minor collection.

Two infix-related clauses are easy to overlook:

- `minor_fields_no_infix_targets` says minor pointer fields do not point directly
  at minor infix sub-objects.
- `major_minor_fields_no_infix_targets` says major fields containing minor
  pointers also do not target minor infix sub-objects.

The collector itself can forward infix addresses, but the public heap-shape
invariant rules out the confusing case where regular object fields point at
minor infix interiors. This keeps the graph model clean.

### Remembered slots

A generational collector must not scan the entire major heap on every minor
collection. Instead, the write barrier records major fields that may contain
minor pointers. The pure remembered-set scan in
`generational/spec/GC.Gen.Remembered.fst` is the specification counterpart:

```fstar
let scan_object_for_minor_refs (major: heap) (obj: obj_addr)
  : GTot (seq remembered_ref) =
  if is_blue obj major || is_no_scan obj major then Seq.empty
  else
    let wz = U64.v (wosize_of_object obj major) in
    scan_object_fields major obj wz 0

let minor_roots_from_major (major: heap) : GTot (seq U64.t) =
  extract_targets (scan_major_for_minor_refs major) 0
```

The implementation does not rescan the major heap during minor collection. It
uses OCaml's `ref_table`, populated by `caml_modify`, as the concrete remembered
slot table. The proof obligation is therefore not merely that remembered slots
are well-formed, but that they cover all major-to-minor pointers relevant to the
collection:

```fstar
UpdatePtrs.ref_table_sound 's 'sl (SZ.v nslots) /\
UpdatePtrs.ref_table_covers_minor_ptrs 's 'sl (SZ.v nslots) /\
UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots) /\
MinorFwd.remembered_targets_in_roots 's 'rs 'sl (SZ.v nslots)
```

Those facts appear as preconditions of `minor_collect_full`.

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

`promote_object` copies one object:

```fstar
let promote_object (minor: minor_state) (major: heap) (obj: U64.t)
                   (fp: U64.t) (wosize: nat{wosize > 0})
  : GTot promote_one_result =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  ...
  if new_addr = 0UL then
    { major_out = major; fp_out = fp; new_addr = 0UL }
  else
    let copied_major = copy_fields minor new_major obj new_addr 0 wosize in
    let padded_major = zero_promote_padding copied_major new_addr wosize in
    let tag = minor_tag minor obj in
    let final_major = set_promoted_tag padded_major new_addr tag in
    { major_out = final_major; fp_out = new_fp; new_addr = new_addr }
```

The padding step is a subtle OCaml allocator detail. If the major allocator
returns a block one word larger than requested, that leftover word cannot form a
standalone free block. The promoted object consumes the whole block, and the
extra field is zeroed so the proof can show it is not a stale pointer.

Why can the allocator return a larger block? The major allocator is first-fit
over blue free-list blocks. When it finds a free block with `block_wz >=
requested_wz`, it computes `leftover = block_wz - requested_wz`. If `leftover >=
2`, it can split: one word becomes the remainder's header and at least one word
remains for the remainder's link field. If `leftover = 0`, the fit is exact. If
`leftover = 1`, however, splitting would create a "free block" with only enough
space for a header and no body word to hold the next free-list pointer. The
allocator therefore consumes the whole block and writes the allocated header
with `block_wz`, not `requested_wz`:

```fstar
if leftover >= 2 then
  // split: allocated header uses requested_wz,
  // remainder gets its own header and first-field free-list link
  ...
else
  // exact fit or leftover = 1: use whole block
  let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
  write_word g hd alloc_hdr
```

Promotion copies only the minor object's original `wosize` payload. If the
allocator consumed a `requested_wz + 1` block, the promoted major object has one
extra field. `zero_promote_padding` zeros exactly that padding field, preserving
the no-scan and non-pointer-field invariants.

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
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
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
let normal_result_reachable_subgraph_isomorphism_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap) (post_roots: seq U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  CG.reachable_subgraph_isomorphism
    (normal_src_reachable minor major fp roots)
    (result_post_reachable post_major post_roots)
    (normal_src_edge minor major fp roots)
    (result_post_edge post_major)
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
let normal_result_non_pointer_fields_preserved_prop
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap) : prop =
  let prom = cheney_promote minor major fp roots in
  forall (u: CG.combined_vertex).
    normal_src_reachable minor major fp roots u ==>
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
| Final heap well-formedness | `collection_heap_shape` / `full_heap_shape` preservation, followed by the major collector's `gc_postcondition`. |
| Reachability-based survival | The isomorphism's totality and surjectivity over reachable source/destination vertices. |
| Successor preservation | The isomorphism's edge preservation/reflection clause. |
| Color reset | The post-minor heap shape plus the major collector's postcondition; after full `gen_gc`, final major objects satisfy the major GC color/free-list discipline. |
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

`gen_gc` runs a minor collection followed by a major one, and each phase proves
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

The result is a single conjunct in `gen_gc`'s postcondition:

```fstar
let end_to_end_isomorphism
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (final_major: heap) (final_roots: seq U64.t) : prop =
  CG.reachable_subgraph_isomorphism
    (MinorFwd.normal_src_reachable minor major fp roots)
    (MCFH.result_post_reachable final_major final_roots)
    (MinorFwd.normal_src_edge minor major fp roots)
    (MCFH.result_post_edge final_major)
    (cheney_promote minor major fp roots).fwd_map
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
}

let is_gen_heap (gh: gen_heap_t) (d: minor_heap) (b: U64.t)
                (s: heap_state) (fp: U64.t) : slprop =
  is_minor gh.minor d b **
  is_heap gh.major s **
  R.pts_to gh.fp_ref fp
```

The allocation entry point routes small objects to the minor heap and large
objects to the major heap:

```fstar
fn gen_alloc (gh: gen_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (U64.v wosize > 0 /\
                 U64.v tag < 256 /\
                 SpecFields.well_formed_heap 's)
  returns obj: U64.t
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2
```

The allocation postcondition is intentionally weak at the top-level interface:
allocation is an operational service used by the runtime, and the deeper
allocator/minor-heap contracts carry the precise shape facts. The collection
entry points are much stronger.

### `minor_collect_full`

`minor_collect_full` is the verified minor-collection boundary used by the C
bridge. It takes roots, a forwarding array, a BFS queue, and remembered slots:

```fstar
fn minor_collect_full (gh: gen_heap_t)
                      (roots: array U64.t) (nroots: SZ.t)
                      (fwd_arr: array U64.t)
                      (queue: larray U64.t Cheney.queue_size)
                      (slots: array U64.t) (nslots: SZ.t)
```

The precondition includes:

- `collection_heap_shape` for the minor and major heap;
- root-array length consistency;
- a zeroed forwarding array of the expected size;
- remembered slot soundness, coverage, distinctness, and root inclusion;
- root validity and non-blue target facts.

The postcondition states, among other facts:

```fstar
s2 == UpdatePtrs.rewrite_slots_iter
        (UpdatePtrs.update_promoted_iter prom.major_final farr2 prom.fwd_map 0)
        prom.fwd_map 'sl (SZ.v nslots) 0 /\
fp2 == prom.fp_final /\
rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
U64.v b2 == 0 /\
UpdatePtrs.represents_fwd farr2 prom.fwd_map /\
SpecFields.well_formed_heap_part1 prom.major_final /\
s2 == (CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs).mc_major /\
GenInv.collection_heap_shape ({ data = d2; bump = b2 } <: minor_state) s2 fp2 /\
(ok ==>
  MinorFwd.normal_result_reachable_subgraph_isomorphism_prop
    minor_st 's 'fp 'rs s2 rs2 /\
  MinorFwd.normal_result_non_pointer_fields_preserved_prop
    minor_st 's 'fp 'rs s2)
```

The equality with `cheney_collect_spec` is the strongest operational statement:
the imperative code implements the pure full minor-collection spec, including
promotion, promoted-object field rewriting, remembered-slot rewriting, root
rewriting, and minor heap reset.

The `ok` flag captures promotion success. If the major heap does not have enough
space for all live minor objects, the isomorphism theorem is conditional on
`ok`; the OCaml bridge treats `ok = false` as fatal out-of-memory for the current
fixed-size heap.

### `gen_gc`

The full generational GC composes minor collection with the major
mark-and-sweep collector:

```fstar
fn gen_gc (gh: gen_heap_t)
          (roots: array U64.t) (nroots: SZ.t)
          (fwd_arr: array U64.t)
          (queue: larray U64.t Cheney.queue_size)
          (slots: array U64.t) (nslots: SZ.t)
          (st: gray_stack)
  ...
  returns res: (U64.t & bool)
```

Its precondition speaks only about the state the caller can observe on entry --
the pre-minor heap, the nursery, and the arrays being passed in:

```fstar
GenInv.collection_heap_shape minor_st 's 'fp /\
MinorFwd.roots_valid_for_minor_collection minor_st 's 'rs /\
gen_gc_stack_budget 'rs 'st (stack_capacity st) /\
...
```

`gen_gc_stack_budget` is the whole of what the caller owes the major phase.  It
mentions no heap at all:

```fstar
let gen_gc_stack_budget roots st cap =
  Seq.length st == 0 /\
  Seq.length roots <= cap /\
  cap > 0
```

  * `Seq.length st == 0` — the gray stack starts empty.  It is collector scratch
    space, not caller state, and both real clients (SPOT and the OCaml runtime
    bridge) already passed an empty one.  Pinning it collapses two conjuncts of
    `darken_precondition` (the stack is a subset of the roots; the stack has no
    duplicates and points only to gray objects) to nothing.
  * `Seq.length roots <= cap /\ cap > 0` — the sizing obligation, in the form a
    caller can actually check.  Darkening pushes every root onto the gray stack,
    so the stack must be able to hold them; `cap > 0` rules out the degenerate
    zero-capacity stack.

Both are decidable by inspection of the arguments being passed.  There is
deliberately nothing else.

### Out-of-memory is a runtime fact, not a proof obligation

An intermediate version of this contract also required `cheney_no_oom` — "the
nursery's live set fits in the major free list".  That was indefensible.
`cheney_no_oom` is a statement about the outcome of the entire Cheney BFS; no
caller can discharge it without simulating the collector, and `gen_gc` already
reports promotion failure through the `ok` component of its result.  Demanding
it up front made `gen_gc` un-callable in exactly the situation its own return
type exists to describe.

The fix is to consume the flag instead of the predicate.  `GC.Gen.Impl.Cheney`
already proves `ok ==> cheney_no_oom` about its BFS loop; `minor_collect_full`
now re-exports that, and `gen_gc` branches on it:

```pulse
  let ok = minor_collect_full gh roots nroots fwd_arr queue slots nslots;
  ...
  if ok {
    darken_roots_bounded gh.major st roots nroots (stack_capacity st);
    let final_fp = MajorGC.collect_with_roots gh.major st prepared_st fp_val;
    ...
  } else {
    // hand back the post-minor heap untouched
  }
```

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
something.  `gen_gc` therefore also carries a postcondition on the failure side:

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

### The invariant is inductive: `gen_gc` restores its own precondition

`gen_gc` demands `GC.Gen.HeapInvariant.collection_heap_shape` of the heap it is
handed.  For a long time it promised nothing of the heap it returned, which made
that predicate an *assumption* rather than an invariant: a runtime driving a
second collection had no way to satisfy the precondition again.  It is now a
postcondition, and deliberately not behind a named wrapper — the `ensures`
names the very predicate the `requires` names, so the two can be read against
each other:

```fstar
  requires ... pure (
    let minor_st : minor_state = { data = 'd; bump = 'b } in
    GenInv.collection_heap_shape minor_st 's 'fp /\ ... )
  ensures exists* d2 b2 s2 ... pure (
    let minor_st_out : minor_state = { data = d2; bump = b2 } in
    ...
    GenInv.collection_heap_shape minor_st_out s2 (fst res) /\ ... )
```

The minor half is vacuous.  `minor_collect_full` finishes by calling
`minor_heap_reset`, which clears the nursery *bytes* as well as the bump pointer,
so the state it hands back is literally `GC.Gen.MinorHeap.minor_reset` — a fact
the implementation always had and simply never stated.  With it,
`collection_heap_shape_after_minor_reset` collapses the minor-side and
cross-generation conjuncts and reduces the whole obligation to
`major_heap_shape` of the major heap and free-list head.

That is fifteen conjuncts, and it is where the work is.
`GC.Gen.PostCollectionShape.major_gc_restores_major_heap_shape` proves them for
`coalesce (sweep h_mark fp)` under nothing more than
`GC.Spec.Correctness.mark_post`:

| conjunct | supplied by |
| --- | --- |
| `well_formed_heap` | `GC.Spec.Coalesce.coalesce_preserves_wf` |
| `fl_valid` | `GC.Spec.Coalesce.Descending.coalesce_fl_entry` |
| `fl_chain_terminates` | `GC.Spec.Coalesce.Descending.coalesce_fl_entry` |
| `fp_pointer_or_zero` | `GC.Spec.Coalesce.Shape.coalesce_fp_pointer_or_zero` |
| `blue_link_fields_valid` | `GC.Spec.Coalesce.Shape.coalesce_blue_link_fields_valid` |
| `heap_objects_dense` | `GC.Spec.Coalesce.Dense.coalesce_dense` |
| `chain_objects_blue` | `GC.Spec.Coalesce.Shape.coalesce_chain_objects_blue` |
| `objects` non-empty | `GC.Spec.Coalesce.Dense.coalesce_dense` |
| `fp_valid` | `GC.Gen.FreeListShape`, from `fl_valid` |
| `fp_in_heap` | `GC.Gen.FreeListShape`, from `fp_valid` |
| `no_black_objects` | `GC.Spec.Coalesce.coalesce_all_white_or_blue` |
| `no_gray_objects` | `GC.Spec.Coalesce.coalesce_all_white_or_blue` |
| `no_pointer_to_blue` | `GC.Spec.Coalesce.Shape.coalesce_no_pointer_to_blue` |
| `no_scan_invariant` | `GC.Spec.Coalesce.Shape.coalesce_no_scan_invariant` |
| `blue_fields_non_infix` | `GC.Spec.Correctness.gc_blue_fields_non_infix_gen` |

Two of these deserve comment.

**The free list is earned, not inherited.**  Nothing about the *input* free list
is required, which at first looks too good.  The reason is that the coalescer
does not thread the sweep's list through at all: `coalesce` starts from a null
head and rebuilds the list from scratch, pushing each merged block onto the front
as the upward walk passes it.  Every link it writes therefore points back at a
block the walk has already left behind, so the list is *descending*, and a
descending list is trivially acyclic and bounded by the number of distinct
8-aligned heap addresses.  `GC.Spec.FreeList.Descending` states that property and
`GC.Spec.Coalesce.Descending` proves the coalescer maintains it, which discharges
the allocator's two entry conditions outright.

**Density needed a reformulation.**  `heap_objects_dense` — "the object walk
tiles the heap, never stopping because a block overruns" — is the one conjunct
that cannot transfer, because `heap_objects_dense_transfer` requires equal
wosizes everywhere and merging a free run is precisely a change of wosize.
Proving it directly founders on the fact that the pre- and post-coalesce walks
do not visit the same addresses, so a pointwise correspondence does not exist.
`GC.Spec.WalkEnd` removes the quantifier instead: `objects start g` is empty
exactly when the walk has run out of room or the block at `start` overruns, so
density is equivalent to the single scalar statement

```fstar
walk_end g zero_addr + 8 >= heap_size
```

where `walk_end` follows the same steps `objects` does and returns the address it
stops at.  `GC.Spec.Coalesce.Dense` then runs the coalescing walk once more and
shows the coalescer leaves that address alone — a merged block covers exactly the
addresses its constituents covered, and a survivor keeps its header, so the last
block still ends where it did.  The scalar invariant has the pleasant side effect
of *supplying* the "objects empty implies no room left" fact that a direct proof
would have had to assume.

The Pulse entry point `GC.Impl.collect_with_roots` does not expose the marked
heap, so it exposes `GC.Spec.Correctness.gc_coalesce_source` instead — "some
marked heap satisfying `mark_post` produced this result".
`major_gc_restores_major_heap_shape_of_source` discharges that existential, which
is what `gen_gc` actually calls.  On the out-of-memory path nothing runs after
the minor collection, so the invariant is the post-minor one, which
`GC.Gen.CheneyPreservation.cheney_collect_preserves_collection_heap_shape`
already provides.

All of it is ghost: the extracted C is byte-identical.

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

The second lemma assembles the whole entry condition:The second lemma assembles the whole entry condition:

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

Note where the hypotheses live: the first two are already `gen_gc` preconditions
for entirely independent reasons, the third is the runtime success flag, and the
last is `gen_gc_stack_budget`.  There is no `..._intro` counterpart any more —
there is nothing left for a caller to introduce.

One conjunct deserves a note.  With an empty stack, `gray_objects_on_stack`
reduces to "the major heap has no gray objects", which is a property of the
pre-minor heap that `gen_gc` should not have to ask about separately.  It is
therefore folded into `GC.Gen.HeapInvariant.major_heap_shape` (as
`SweepInv.no_gray_objects`), where the rest of the major heap's well-formedness
already lives, and `GC.Gen.CheneyPreservation` re-establishes it after the
minor collection.

`GC.Impl.collect_with_roots` demands its precondition on the *post*-darkening
state.  That last step is also done inside the library:

```fstar
val gen_gc_major_precondition_elim minor major fp roots st cap
  : Lemma (requires
             GenInv.collection_heap_shape minor major fp /\
             MinorFwd.roots_valid_for_minor_collection minor major roots /\
             CheneyBFS.cheney_no_oom minor major fp roots /\
             gen_gc_stack_budget roots st cap)
          (ensures
            MajorGC.gc_precondition_with_roots
              (fst prepared) (snd prepared) (snd prepared) result.mc_fp cap /\
            roots_match_stack result.mc_roots (snd prepared))
```

`gen_gc_prepared_state` is still exported, because the postcondition talks about
the darkened heap:

```fstar
let gen_gc_prepared_state minor major fp roots st cap =
  let result = CheneySpec.cheney_collect_spec minor major fp roots in
  MarkBoundedImpl.darken_roots_bounded_spec result.mc_major st result.mc_roots cap
```

So callers do not have to pre-color roots, pre-seed the mark stack, or reason
about `darken_roots_bounded_spec` at all.

The effect on the concrete client is the honest measure of how much of the
collector's internal reasoning the old contract leaked: SPOT's hand-proof of the
entry condition went from ~374 lines of concrete case analysis over its three
objects to a two-line lemma invocation.

Note also that `Seq.length 'st <= stack_capacity st` is not restated in the
precondition: it is recoverable from `is_gray_stack` via
`GC.Impl.Stack.stack_facts`.

The postcondition is two facts about the returned state plus three named
bundles:

```fstar
minor_st_out == minor_reset minor_st /\
GenInv.collection_heap_shape minor_st_out s2 (fst res) /\
gen_gc_roots_post minor_st 's 'fp 'rs rs2 ok 'st (stack_capacity st) /\
gen_gc_reachable_subgraph_isomorphism_post
  minor_st 's 'fp 'rs ok s2 rs2 'st (stack_capacity st) /\
gen_gc_unreachable_final_blue_post minor_st 's 'fp 'rs ok s2
  'st (stack_capacity st)
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
redundant conjunct is both an extra obligation inside `gen_gc` and extra SMT
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
| `GC.SPOT.Preconditions` | Packages the real `minor_collect_full` and `gen_gc` precondition bundles behind named predicates and elimination lemmas. |
| `GC.SPOT.Postconditions` | Packages the useful consequences of post-minor and post-full collection. |
| `GC.SPOT.ConcreteForwarding` | Proves that unreachable `B` keeps forwarding entry `0`. |
| `GC.SPOT.ConcreteScenarios` | Connects the concrete heaps, roots, slot table, and forwarding array to the real collection preconditions. |
| `GC.SPOT.ConcreteFull` | Connects post-minor facts to final `gen_gc` postconditions. |
| `GC.SPOT.CallMinor` / `ConcreteCallMinor` | Pulse wrappers that call the real `minor_collect_full` and prove concrete consequences. |
| `GC.SPOT.CallFull` / `ConcreteCallFull` | Pulse wrappers that call the real `gen_gc` and prove final survival facts. |
| `GC.SPOT.ThreeObjects` | The scenario layer: A is promoted, C.field1 is rewritten to A', B is not promoted, and C/A' survive full GC. |
| `GC.SPOT.InfixMajor` | A second, independent scenario: a ten-word major heap containing a genuine OCaml interior (infix) pointer. |
| `GC.SPOT.InfixPre` / `InfixPost` | Discharge `gen_gc`'s precondition for that heap over an empty nursery, and read back its postcondition. |
| `GC.SPOT.InfixCall` | Pulse wrapper that calls the real `gen_gc` on the infix heap. |

The main useful facts proved by the active SPOT are:

1. The real Pulse entry points `minor_collect_full` and `gen_gc` are callable from
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
remembered slot array, and an empty gray stack with capacity at least two. The
pure side condition that this empty stack is enough for the scenario is proved
inside `GC.SPOT.ConcreteScenarios.spot_concrete_gen_gc_pre_empty_stack`, not
assumed by the caller.

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
* `spot_infix_major_heap_shape` proves the heap **satisfies** all fifteen
  conjuncts of the current `GC.Gen.HeapInvariant.major_heap_shape` — in
  particular `well_formed_heap` through the *resolved*-target formulation of
  parts 2 and 3, with `resolve_object H == P` established from
  `GC.Spec.Object.infix_addr_conds`.

`GC.SPOT.InfixPre` discharges the remainder of `gen_gc`'s precondition (empty
nursery, empty remembered table, single root `Q`) and proves the collection
cannot run out of memory. `GC.SPOT.InfixCall.call_gen_gc_infix` then calls the
real `gen_gc` and proves that it succeeds, that `collection_heap_shape` holds
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
minor_collect_full(...)
gen_gc(...)
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
`translate_minor_fields` pass for that, and the helper is still extractable, but
the active bridge no longer calls it. It is unnecessary for correctness and
wasteful for performance.

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
`Caml_state->_ref_table`. The bridge passes that table directly to
`minor_collect_full`:

```c
struct caml_ref_table *tbl = Caml_state->_ref_table;
size_t n_slots = (size_t)(tbl->ptr - tbl->base);

promote_ok = minor_collect_full(gc_gen_heap, root_values,
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

### Full GC root and gray-stack layout

The full-GC bridge calls the extracted verified `gen_gc` entry point. The root
buffer and gray stack are separate allocations:

```c
uint64_t *gray_storage = calloc(gray_cap, sizeof(uint64_t));
uint64_t *roots_for_gc = calloc(root_count == 0 ? 1 : root_count, sizeof(uint64_t));
if (root_count > 0)
    memcpy(roots_for_gc, root_values, root_count * sizeof(uint64_t));
size_t gray_top = gray_cap;   // empty downward-growing stack

gray_stack_rec gc_stack = {
  .storage = gray_storage,
  .top = &gray_top,
  .cap = gray_cap
};

gen_gc(gc_gen_heap, roots_for_gc, root_count, gc_fwd_arr,
       gc_queue, (uint64_t *)tbl->base, n_slots, gc_stack);
```

The verified `gen_gc` protocol is:

1. `minor_collect_full` rewrites `roots_for_gc` in place and rewrites the
   remembered major slots.
2. `darken_roots_bounded` scans the rewritten post-minor roots, colors root
   objects, and pushes them onto the initially empty gray stack.
3. `collect_with_roots` runs the verified major collector over the prepared
   major heap and prepared gray stack.

The bridge keeps the original `root_values[]` and `root_locs[]` outside the
verified stack. After `gen_gc` returns, `write_back_forwarded_roots()` uses the
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
  GC.Impl.MarkBounded GC.Impl.Coalesce \
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
  for major allocations.
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
spec result." Examples include `allocate`, `minor_collect_full`, and the
lower-level update/heap operations. This pattern is extremely effective: prove
the algorithm once as a pure function, then prove the Pulse code refines it.

### Split heap shape into just enough pieces

The generational collector would be much harder to prove if every function
required `full_heap_shape`. Instead, the development factors shape predicates:

- `well_formed_heap_part1` for object bounds;
- free-list validity and termination for allocation;
- `collection_heap_shape` for minor collection;
- `major_stack_shape` for major marking;
- `full_heap_shape` only when the full generational cycle needs both.

This factoring is why `allocate_part1` can be used during promotion.

### Hide large predicates from SMT and expose intro/elim lemmas

Many central predicates are marked `opaque_to_smt` and paired with intro/elim
lemmas. This prevents Z3 from unfolding a giant invariant everywhere and lets
proofs reveal exactly the part they need.

### Use graph abstractions aggressively

The project becomes tractable when heap operations are related to graph
operations:

- `HeapGraph.get_pointer_fields` explains how fields become successors.
- `HeapModel.create_graph` gives a graph for a heap.
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
   `GC.Gen.Promote.fsti`, `GC.Gen.Cheney.fst`, and
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
