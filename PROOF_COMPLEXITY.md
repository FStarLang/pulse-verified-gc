# Proof Complexity

A map of the correctness proof: what it establishes, how it is put together, where the
effort actually goes, and what could be made smaller.

This is a companion to [`DESIGN_AND_IMPL.md`](DESIGN_AND_IMPL.md) (what the collector
does) and [`docs/bloat-analysis.md`](docs/bloat-analysis.md) (what has already been
trimmed and why). Where those documents describe the artefact, this one describes the
*argument* and its cost.

Every number below is measured against the tree as it stands. §9 says how to reproduce
them.

---

## 1. The shape of the thing

```
                             83,163 lines of F*/Pulse
                                       │
                                       ▼
                             1,987 lines of C (GC_Gen_Impl.c)
```

A 42:1 ratio of proof to product. That ratio is the subject of this document.

The development is four trees:

| tree | files | lines | role |
|---|---:|---:|---|
| `common/` | 19 | 7,269 | heap model, headers, object enumeration, graph & DFS, shared Pulse primitives |
| `mark-and-sweep/` | 63 | 29,691 | the major collector: mark, sweep, coalesce, allocator, free list |
| `generational/` | 93 | 40,278 | the minor collector: Cheney copying, promotion, remembered set, and the composition with the major collector |
| `spot/` | 28 | 5,925 | experimental single-object-tracing variant; not on the extraction path |

and within each, a spec/impl split:

| layer | lines | contents |
|---|---:|---|
| `*/spec/` | 65,142 | pure F\*: definitions, invariants, lemmas. No imperative code. |
| `*/impl/` + `common/lib/` | 12,096 | Pulse: the actual program, its loop invariants, and the lemmas that make them go through. |

**Zero `admit()`s. Two `assume`s**, both the same platform axiom
(`squash SZ.fits_u64`, at `common/impl/GC.Impl.Heap.fst:40` and
`generational/impl/GC.Gen.Impl.MinorHeap.fst:27`). The trusted base beyond that is two
`val`-only Pulse primitives, `read_u64_le`/`write_u64_le`
(`common/impl/GC.Impl.ArrayWord.fsti:64-82`), which are axiomatised against a pure
byte-sequence codec and extracted as a single machine load/store; and a handful of
*stated hypotheses* about the mutator that the GC cannot itself establish, chiefly
`minor_infix_wf` (`generational/spec/GC.Gen.MinorHeap.fsti:257-273`): that any infix
sub-object in the nursery encodes a real closure parent.

---

## 2. The main steps of the proof

### 2.1 Foundation: a heap is a sequence of bytes

```fstar
let heap = h:seq U8.t{Seq.length h == heap_size}      // GC.Spec.Base.fsti:47
```

There is no object datatype. An *object* is an address; its header is the 64-bit word at
`obj - 8`, laid out exactly as OCaml lays it out (`wosize:54 | color:2 | tag:8`). This
single decision is the root of a large fraction of everything that follows (§4.1).

On top of the byte sequence sit three layers, each of which must be built by hand
because none of it is given by the representation:

1. **Words.** `read_word`/`write_word` (`common/spec/GC.Spec.Heap.fst`) as a
   little-endian codec over eight `Seq.index`es, plus the bit-twiddling that extracts
   `getWosize`/`getColor`/`getTag` from a word (`common/lib/GC.Lib.Header.fst`).
2. **Objects.** `objects start g` (`common/spec/GC.Spec.Fields.fst:185`) walks the heap
   from `start`, reading each header's `wosize` to find the next object. It recurses on
   `decreases (Seq.length g - U64.v start)`.
3. **Well-formedness.** `well_formed_heap` (`Fields.fst:502-526`), a four-part
   conjunction, marked `[@@"opaque_to_smt"]`:
   - **part1** — every object's body fits inside the heap;
   - **part2** — pointer closure: every pointer field targets an enumerated object;
   - **part3** — `infix_wf`: interior closure pointers resolve to real parents;
   - **part4** — no enumerated object is itself an infix sub-object.

   Parts 3 and 4 exist only because OCaml closures (`Infix_tag = 249`) contain interior
   words that *look like* valid headers. They are not an abstraction; they are a
   faithfulness requirement.

### 2.2 Heap becomes graph

`create_graph` (`common/spec/GC.Spec.HeapModel.fst:77`) turns a well-formed heap into
a vertex/edge structure; `reach` (`GC.Spec.Graph.fst:187`) is an inductive witness type
for reachability, and `reachable_set g roots = dfs g roots empty_set`
(`GC.Spec.DFS.fst:965`), tied together by `reachable_set_correct` (`DFS.fst:981`) and
`reachable_successor_closed` (`DFS.fst:986`).

Everything above this line is representation; everything below is algorithm. The
correctness statement is phrased over the graph, so every algorithmic step must be
pushed back through `create_graph`.

### 2.3 The major collector: mark → sweep → coalesce

- **`mark`** (`GC.Spec.Mark.fsti:196`) = `mark_aux g st heap_words`: a fuel-indexed
  worklist that grays children and blackens parents.
- **`sweep`** (`GC.Spec.Sweep.fsti:77`): one linear walk; black → white (survives),
  white → blue and threaded onto the free list.
- **`coalesce`** (`GC.Spec.Coalesce.fst:123`): merge maximal runs of adjacent blue
  blocks.

The implementation fuses sweep and coalesce into one heap pass. `GC.Spec.SweepCoalesce*`
(≈2,300 lines across five modules) exists purely to prove
`fused_sweep_coalesce g == coalesce (fst (sweep g fp))`
(`fused_eq_sweep_coalesce`, `SweepCoalesce.fst:483`) so that the rest of the proof can keep using the clean
two-pass composition.

### 2.4 The top theorem, and its five pillars

`end_to_end_correctness` (`GC.Spec.Correctness.fsti:123`, proved at
`Correctness.fst:205`) establishes, for `h_mark = mark h_init st` and
`h_sweep = fst (sweep h_mark fp)`:

| # | pillar | statement |
|---|---|---|
| 1 | heap integrity | `well_formed_heap h_sweep` |
| 2 | reachability | `is_black x h_mark <==> Seq.mem x (reachable_set g_init roots')` |
| 3 | structure | `successors g_init x == successors g_sweep x` for survivors |
| 4 | state reset | every object is white or blue after sweep; survivors are white |
| 5 | data | every field of every survivor is byte-identical |

Pillar 2 is the theorem; pillars 1, 3, 4, 5 are what make it *mean* something (a
collector that zeroed the heap would satisfy 2 vacuously).

`full_gc_correctness` (`Correctness.fsti:74`) wraps this as
`exists h_mark. ...` and is kept opaque behind the interface. The header comment says
why (`Correctness.fsti:5-9`): *"clients cannot unfold `gc_postcondition` or
`full_gc_correctness`, preventing quantifier explosion in Pulse VCs."* Consumers use
named elimination lemmas (`full_gc_correctness_elim_wfh`, `..._elim_colors`, …). This is
a recurring pattern and a recurring tax (§4.4).

### 2.5 Two mark algorithms, one contract

The spec `mark` uses an unbounded worklist. The implementation cannot. `mark_bounded`
(`GC.Spec.MarkBounded.fsti:65-70`) models a fixed-capacity stack: on overflow it grays
the child in the heap but does not push it, and compensates with `rescan_heap`
(`MarkBounded.fsti:128-140`) — a second, outer loop that walks the heap looking for
stranded gray objects. Two nested fuel measures: inner `count_non_black g`, outer
rescan-round count.

Rather than reprove Pillar 2 for the bounded algorithm, the proof defines a shared
contract `mark_post` (`Correctness.fst:909`, an 11-conjunct `prop`) and proves both
`mark_satisfies_mark_post` and `mark_bounded_satisfies_mark_post`. Everything downstream
is generic over which marker ran. This is the single best structural decision in the
development.

### 2.6 The allocator and the free list

The free list is a singly-linked chain threaded through blue blocks, with three
invariants (`GC.Spec.FreeList.fst:117-131`):

- `fl_sound` — everything on the chain is blue;
- `fl_complete` — every blue block is on the chain;
- `fl_exact` — both, proved by `fl_exact_blue_blocks` (`GC.Spec.FreeList.Sweep.fst:320`).

`reachable_on_fl` is deliberately an *existential* over hop count, chosen so that no use
of the invariant needs a counting argument. The allocator's own bounded walk uses two
companions instead: `fl_valid` (fuel-indexed, `Allocator.Lemmas.Common.fst:15-26`) and
`fl_chain_terminates` (`Allocator.Lemmas.Chain.fst:71-80`) — the latter needed because
`fl_valid` is vacuously true past its fuel budget.

### 2.7 The minor collector

The nursery is a second byte sequence with a bump pointer
(`GC.Gen.MinorHeap.fsti:113-116`), using the same header encoding. Collection is Cheney
BFS over a `cheney_state` (`GC.Gen.Cheney.fsti:42-48`) carrying the major heap, the free
pointer, a forwarding map, and a queue:

1. `cheney_forward_roots` — forward every root;
2. `cheney_scan` — BFS drain, forwarding each scanned object's fields;
3. `update_major_pointers` — rewrite stale minor pointers in the major heap;
4. `rewrite_roots`; 5. `minor_reset`.

Forwarding is modelled *functionally* — `forwarding_map = U64.t -> GTot U64.t`
(`GC.Gen.Promote.fsti:38-46`) — rather than as an in-place header overwrite. The
implementation uses a real array, and `GC.Gen.Cheney.Sim`/`.SimOne` prove the array
simulates the map (which is what eliminated the last `assume_` in
`GC.Gen.Impl.Cheney.fst`).

`promote_object` (`Promote.fsti:96-114`) is `alloc_spec` → `copy_fields` →
`zero_promote_padding` → `set_promoted_tag`. **Promotion is an allocator client**, and
that is the hinge on which most of the generational proof's weight hangs (§5.2).

The generational theorem comes in two tiers:

- **`cheney_gc_correct`** (`CheneyCorrectness.fsti:154-197`) — unconditional: survival,
  `well_formed_heap_part1`, free-list re-validity, minor reset, roots rewritten. Holds
  *even under OOM*, because every forwarding step is either a success or a no-op.
- **`cheney_promotes_all_reachable`** (`CheneyCorrectness.fsti:217-234`) — conditional on
  `cheney_no_oom`: every reachable minor object was forwarded.

Note what is *not* preserved: full `well_formed_heap`. Pointer closure (part2) is broken
by promotion — a promoted object's fields still point into the nursery — and is only
restored by step 3 (`CheneyCorrectness.fsti:56-61`).

### 2.8 Composition

There is no single "minor-then-major" theorem in `generational/spec/`. The two halves
are:

- `GC.Gen.CheneyCorrectness` — the minor collector is correct;
- `GC.Gen.CheneyPreservation.*` (≈6,500 lines, 7 modules) — the minor collector leaves
  every conjunct of the *major* collector's precondition intact (`no_black_objects`,
  `gray_black_objects_on_stack`, `no_scan_invariant`, `blue_fields_closed`,
  `collection_heap_shape`, `no_pointer_to_blue`).

They are stitched together in Pulse, at `generational/impl/GC.Gen.Impl.fst:1146`, which
asserts `full_gc_correctness prepared_major s_final prepared_st` after running both
paths.

Because the minor collector *moves* objects, correctness also needs a graph-isomorphism
argument that mark-and-sweep never needs: `GC.Gen.CombinedGraph`
(tagged `MinorV`/`MajorV` vertices, because the two address spaces can numerically
collide — `CombinedGraph.fsti:14-19`) plus `GC.Gen.MinorCollectForwarding.*`
(~2,300 lines) prove `reachable_subgraph_isomorphism` with the forwarding map as the
morphism.

### 2.9 Down to Pulse

The Pulse layer's job is one thing, repeated: **each loop iteration corresponds to one
step of unrolling a pure recursive spec function.** The allocator's invariant is
literally

```
SA.alloc_search 's vhead vprev vcur (U64.v wz) (U64.v vfuel) == SA.alloc_spec 's fp (U64.v wosize)
```
(`mark-and-sweep/impl/GC.Impl.Allocator.fst:174-192`), and the Cheney scan loop's is
literally

```
cheney_scan minor_st cs_s (SZ.v sv) (fuel - SZ.v sv) == cheney_scan minor_st cs1 0 fuel
```
(`generational/impl/GC.Gen.Impl.Cheney.fst:660-684`).

Because the correspondence is exact, the imperative postconditions can be exact too. The
strongest is `minor_collect_full` (`GC.Gen.Impl.fsti:302-325`), which proves the
resulting C-visible byte sequence *equal* to `cheney_collect_spec`'s output.

---

## 3. Where the effort actually is

Wall-clock verification time per module (single module, cold cache, on an otherwise idle
128-core machine — see §9), against module size and configured rlimit. Rows are ordered by
the *original* cost, so that the three struck-through entries show where the effort used to
be; §6.4 explains what moved them.

| seconds | lines | rlimit | module |
|---:|---:|---|---|
| ~~802.6~~ → **32.9** | 835 | 30 + **fuel 8** (local) | `GC.Gen.Impl.MinorHeap` — see §6.4 |
| **577.8** | 1,637 | EAGER_QI | `GC.Gen.Cheney` |
| ~~413.9~~ → **71.5** | 2,109 | 25 (file) + **fuel 8** (local) | `GC.Impl.MarkBounded` — see §6.4 |
| **369.5** | **188** | EAGER_QI | `GC.Spec.Allocator` |
| 239.6 | 959 | EAGER_QI | `GC.Gen.Impl.Cheney` |
| 150.7 | 1,429 | EAGER_QI | `GC.Gen.CheneyPreservation.Forwarding` |
| 144.5 | 3,381 | EAGER_QI | `GC.Spec.Allocator.Lemmas.Part2` |
| 142.9 | 1,460 | — | `GC.Gen.MinorCollectForwarding` |
| 132.1 | 1,355 | — | `GC.Spec.MarkBoundedCorrectness` |
| 123.6 | 1,861 | 250 (local) | `GC.Gen.CheneyPreservation` |
| 111.0 | 3,700 | — | `GC.Spec.Mark` |
| 105.2 | 1,947 | EAGER_QI | `GC.Gen.TwoPassEquiv` |
| 93.3 | 2,687 | — | `GC.Spec.Coalesce` |
| 89.3 | 1,495 | — | `GC.Spec.Correctness` |
| 80.0 | 584 | 12 (file) + EAGER_QI | `GC.Impl.Allocator` |
| ~~73.4~~ → **17.4** | 570 | 12 + **fuel 8** (local) | `GC.Lib.Header` — see §6.4 |
| 72.5 | 1,171 | `z3refresh` | `GC.Gen.Impl` |
| 63.7 | 1,608 | — | `GC.Spec.Fields` |
| 20.5 | 1,060 | up to **1250** (local) | `GC.Spec.Sweep` |
| 12.2 | 998 | — | `GC.Spec.DFS` |

The rlimit column lists what is *in effect*. It used to list the `Makefile`'s blanket
overrides; §6.4 established that all of those were dead — in `GC.Impl.MarkBounded` and
`GC.Impl.Allocator` because a file-level `#set-options` supersedes the command line, and
elsewhere because no goal came near the budget — so they have been deleted and the column
now shows the file-level or local setting that actually binds.

`GC.Gen.Impl.MinorHeap` was missing from the first version of this table, and the reason is
worth recording as a hazard: it was confused with the *spec* module `GC.Gen.MinorHeap`
(24.9s), a different file. The implementation was the slowest module in the repository, at
802s, and nobody had noticed. It is now 32.9s; §6.4 has the diagnosis. Its cost was **not**
proof difficulty but silent fuel escalation, which is invisible in build output because the
proof still succeeds.

**Length and difficulty are close to uncorrelated — and the two extremes are nearly two
orders of magnitude apart in cost per line.** `GC.Spec.Allocator` is **188 lines and takes
six minutes**: 2.0 s/line. `GC.Spec.Mark` is the largest module in the repository at 3,700
lines and verifies in under two: 0.03 s/line. `GC.Spec.Allocator.Lemmas.Part2` is 3,381
lines and takes two and a half minutes — it is *long* because the same induction is
repeated for seven different invariants, not because any one of them is hard.

`GC.Spec.Allocator` deserves singling out. Its `.fst` is 188 lines containing fourteen
lemmas, five of whose bodies are literally `()` — the *step lemmas*
`alloc_search_fuel_0`, `alloc_search_invalid`, `alloc_search_advance`,
`alloc_search_found_head`, `alloc_search_found_prev` (`GC.Spec.Allocator.fst:48-68`).
They exist so the Pulse allocator loop can relate its state to one more unrolling of
`alloc_search` (defined in the 420-line `.fsti` at `:138`). Their proofs are no-ops; each
obligation is "unfold this fuel-indexed recursion one step over a byte-sequence heap and
match it against the stated equation", and this module is the third most expensive in the
repository. That is the clearest single measurement of where the difficulty lives: not in
the size of the proof, but in the density of what must hold at once.

**Obligation density, not proof length, is what costs.** The remaining slow modules are
the places where the most facts must hold simultaneously at a single program point:
`GC.Gen.Cheney` (BFS + allocator + infix forwarding + OOM + free-list invariants, all in
`cheney_forward_one`), `GC.Impl.MarkBounded` (a nine-conjunct loop invariant over a
bounded stack with two nested fuel measures), and `GC.Gen.Impl.Cheney` (a thirteen-conjunct
invariant with ten ghost existentials).

In-source rlimit distribution over 1,094 sites: min = 10, p50 = 20, p90 = 75, p99 = 250,
max = 1,250. The top of that distribution is instructive:

- **Every in-source rlimit above 400 is in `GC.Spec.Sweep.fst`** — nine sites from 500 to
  1,250, all clustered on proving that sweep leaves a survivor's pointer fields
  byte-identical (Pillars 3 and 5). That is a per-field quantifier chain whose SMT cost
  compounds with field count. Yet the module verifies in 20 seconds: high rlimit here
  buys headroom on a query that is wide but shallow.
- `GC.Impl.MarkBounded.fst` is the opposite: a file-wide override of **300** plus eight
  further local `#push-options` from 12 to 100. It is not hard in one place; it is hard
  everywhere.

Longest single definitions, as a proxy for "proofs that resisted decomposition":

| lines | definition |
|---:|---|
| 360 | `alloc_search_preserves_fl_valid_part1` (`Allocator.Lemmas.Part2.fst:935`) |
| 339 | `alloc_search_preserves_fl_chain_terminates_part1` (`Part2.fst:1306`) |
| 335 | `alloc_search_preserves_bfc` (`GC.Gen.PromoteUpdate.BlueAlloc.fst:147`) |
| 328 | `alloc_search_preserves_chain_avoids_other` (`Part2.fst:2165`) |
| 305 | `coalesce_aux_blue_field0_valid` (`Coalesce.fst:2034`) |
| 262 | `combined_proof` (`SweepCoalesce.Induction.fst:719`) |
| 250 | `derive_slots_scannable_in_major` (`GC.Gen.Impl.fst:480`) |
| 246 | `scan_loop` (`GC.Gen.Impl.Cheney.fst:609`) |

Six of the top eight are allocator-interaction proofs. **The allocator, not the collector,
owns the largest individual proof units in the development.**

---

## 4. Sources of complexity, ranked

### 4.1 The heap is a flat byte sequence, so there is no free framing

`is_heap h s = pts_to h.data s ** pure (SZ.v h.size == heap_size)`
(`common/impl/GC.Impl.Heap.fst:69-71`) owns the entire heap as one resource. Separation
logic therefore does *no* work: there is only one thing to frame around, so Pulse's frame
inference is trivial and every "writing here does not disturb there" fact must be proved
by hand, as a pure lemma about byte sequences.

The consequence is visible as a wall of names. `GC.Impl.MarkBounded.fst` alone contains
18 lemmas of the form `check_and_darken_bounded_spec_preserves_X` /
`darken_roots_bounded_spec_preserves_X` for
X ∈ {`wosize`, `objects`, `read_word`, `wf`, `density`, `bsp`, `bounded_mark_inv`,
`no_black`, `no_pointer_to_blue`, `no_scan_invariant`}, and 98 identifiers matching
`frame|preserves|unchanged`. Lines 1–1002 of that 2,104-line file are pure lemmas; the
16 actual `fn` definitions occupy lines 1003–2104. **Roughly half of the largest
implementation module is framing.**

Four further modules are 100% pure lemmas with no Pulse code at all —
`GC.Impl.Sweep.Lemmas`, `GC.Impl.Coalesce.Lemmas`, `GC.Impl.FusedSweepCoalesce.Lemmas`,
`GC.Impl.MarkBoundedRootLemmas` — 1,425 lines, ~12% of the implementation layer.

This is a *choice*, and a defensible one: it buys a C representation that is exactly a
`char*` with OCaml's layout, and it avoids per-cell separation logic entirely. But the
work does not disappear; it relocates.

### 4.2 `objects` recurses on a shape no combinator captures

`objects` decreases on `Seq.length g - U64.v start`. There is no library induction
principle for that, so **every** fact about the enumerated object list re-implements the
same `if next_start >= heap_size then ... else recurse` case split by hand:
`objects_separated`, `objects_addresses_gt_start`, `objects_is_vertex_set`,
`write_word_preserves_objects_aux` (rlimit 400), and a dozen more.

The cost is not just the duplication — it is that any change to `objects`' definition
invalidates dozens of separately-proved lemmas rather than one shared one.

### 4.3 Pillar 2 is a hand-built bidirectional simulation

`GC.Spec.Mark.fst:1841-3657` — **1,813 lines, 49% of the file** — is the black ⇔ reachable
proof, in 13 numbered sub-sections. The two directions share almost nothing:

- **Forward** (`reachable ⟹ black`, `Mark.fst:2210-2647`, ending at `black_reach_is_black` (`:2627`))
  is an induction over the `reach` *proof term* — the declarative side.
- **Backward** (`black ⟹ reachable`, `Mark.fst:3424-3656`, ending at
  `mark_black_is_reachable`, `:3631`) is a fuel-indexed invariant over `mark_aux`'s recursion,
  threading a stack-reachability invariant through every recursive call of
  `push_children` — the operational side.

One reasons about a witness type, the other about a recursive function. There is no
shared vocabulary, so the proof surface is doubled.

### 4.4 Opacity is necessary and it is a tax

`well_formed_heap`, `full_gc_correctness`, `mark_post`, `gc_postcondition`,
`minor_infix_wf`, `minor_guards_complete` are all `[@@"opaque_to_smt"]`. Without this,
Z3 drowns. With it, every consumer needs a one-line elimination lemma:
`wf_object_size_bound`, `wf_field_target_in_objects`, `mark_post_elim_*`,
`full_gc_correctness_elim_*`, and dozens of
``let foo x = reveal_opaque (`%well_formed_heap) well_formed_heap``.

None of these lemmas contain mathematics. They exist so that SMT contexts stay small.
The four-way split of `well_formed_heap` into `part1..part4` with per-part `wf_*`
extraction lemmas (`Fields.fst:592-670`) is the same idea: a quantifier-explosion
firewall.

### 4.5 The generational collector composes with, rather than replaces, the major one

`generational/` is 40,278 lines against `mark-and-sweep/`'s 29,691 — 1.36× — despite the
minor collector being conceptually the simpler algorithm. Five reasons, all real:

1. **Promotion allocates in a loop.** Mark-and-sweep never allocates during collection;
   sweep is one deterministic linear rebuild. The minor collector calls `alloc_spec` once
   per survivor — an unbounded, data-dependent number of times *within one collection* —
   and each call may split a free block. Every allocator invariant must then be threaded
   through the *rest* of the BFS. This spawns `CheneyPreservation.*`, `AllocProps`,
   `WriteBodyLemmas`, `Cheney.Dense`, `PromoteUpdate.BlueAlloc`/`.BlueProm`
   (1,564 lines for the split case alone) — none of which has any mark-and-sweep analogue.
2. **Two address spaces that can numerically collide.** Minor and major addresses are both
   raw `U64.t` and can be equal (`CombinedGraph.fsti:14-19`). Every single-heap predicate
   must be re-derived per generation and then reconciled through a tagged combined graph.
   Mark-and-sweep has one reachability development; generational needs three (minor-only
   `Reachability`, major via `common/spec`, and the tagged `CombinedGraph` union).
3. **Copying needs an isomorphism argument.** Mark-and-sweep never moves anything, so
   object identity is preserved trivially. A copying collector must prove the reachable
   subgraph before collection is isomorphic to the reachable subgraph after, with the
   forwarding map as the morphism — `CombinedGraph` + `MinorCollectForwarding.*`,
   ~3,400 lines. This is intrinsic to the algorithm.
4. **Infix objects are pervasive, not an edge case.** Because a copying collector must
   *relocate* interior pointers with arithmetic-preserving deltas, every forwarding
   operation has an infix branch, and every preservation lemma has an infix case.
   Mark-and-sweep only has to avoid *miscolouring* them.
5. **The adapter cost.** The minor collector must prove it leaves all six conjuncts of the
   major collector's precondition intact, so that the unmodified major collector still
   type-checks afterwards. That is a pure cost of composing two independently-designed
   collectors.

### 4.6 One loop shape, ten hand-written instances

Every nontrivial Pulse loop independently re-derives: a measure, a decrease proof, and an
invariant equating a partial unrolling of a pure recursive function to the current
concrete state. There are ten or so, with no shared combinator:

| loop | `exists*` vars | pure conjuncts |
|---|---:|---:|
| `Cheney.scan_loop` (`GC.Gen.Impl.Cheney.fst:660`) | 10 | 13 |
| allocator search (`GC.Impl.Allocator.fst:174`) | 6 | ~10 (branched) |
| `mark_inner_loop_impl` (`GC.Impl.MarkBounded.fst:1414`) | 4 | 9 |
| `rescan_heap_impl` (`GC.Impl.MarkBounded.fst:1898`) | 2 | 9 |
| `mark_loop_bounded` outer (`:2058`) | 4 | 8 |
| `UpdatePtrs` loops ×5 (`GC.Gen.Impl.UpdatePtrs.fst`) | 4–7 | 6–11 |

Most conjuncts are not new work — they are restatements of already-proved structural facts
(`well_formed_heap`, `heap_objects_dense`, array lengths) that must be re-asserted every
iteration because a `while` invariant offers no way to separate the part that changes from
the part that does not.

Termination is likewise hand-rolled, in three idioms:
- **real fuel that is also the OOM budget** — the allocator's `fuel_ref`, initialised to
  `heap_words`, whose exhaustion is an observable OOM;
- **a real array index** — Cheney's `scan`, the coalesce/rescan address walks;
- **a purely ghost potential function, erased before extraction** — `count_non_black` in a
  ghost ref for both mark loops. A reader of the generated C *cannot see* why
  `mark_loop_bounded` terminates; the measure exists only in the proof.

All three use the same `measure + (if !go then 1 else 0)` idiom for the final
"establish the postcondition, then stop" step.

### 4.7 Z3 4.15.3 instability, encoded in the build system

This is not proof complexity, but it dominates the experience of working on the proof.
The `Makefile` documents (lines 20–90) three workarounds, each with measurements:

- **`EAGER_QI`** (`smt.qi.eager_threshold 100`, default 10). At the default, a number of
  goals send Z3 into a search that **never terminates and never charges the rlimit** — so
  `--z3rlimit` cannot bound it. Z3 4.13.3 discharged the same goals in seconds. Measured:
  `GC.Spec.Allocator` >15 min → 81 s; `GC.Gen.CheneyPreservation.Forwarding` >90 min →
  3 m 13 s. It cannot be global: at the raised threshold, `GC.Spec.DFS` and `GC.Spec.Heap`
  hang instead. Fifteen modules opt in by name — and that list is, in effect, an empirical
  index of the hardest modules in the development.
- **`RETRY = --retry 3`.** Trivially true goals — nat-ness side conditions,
  `x % 8 == 0` alignment, `fuel - 1 >= 0` — *intermittently* exhaust the rlimit where an
  adjacent identical goal succeeds in milliseconds. A fresh solver clears them.
- **`Z3_TIMEOUT = 300000`.** A hard per-query wall clock, precisely because some searches
  never terminate and never charge the rlimit. The slowest *legitimate* query is well
  under 60 s.

The failure mode this produces is worth recording, because it is not a logic error and
does not look like one: during this session, `mark_inner_loop_backward_inv` began failing
*reproducibly* on `fuel - 1 >= 0` with "SMT query timed out" after an unrelated
`private let` was added earlier in the same module. Context bloat, nothing more. The fix
was to delete a redundant lemma.

---

## 5. The hardest parts, and why

### 5.1 `GC.Spec.Mark.fst` §5 — black ⇔ reachable (1,813 lines)

The hardest *mathematics*. Everything else in the development is invariant preservation:
"this operation does not break that property." Pillar 2 is the only place where a
genuinely new fact is established — that an imperative worklist traversal computes
exactly graph reachability. It requires two unrelated inductions (§4.3) and it is the one
part that would look the same in any verified tracing collector.

### 5.2 The allocator family (`Allocator.Lemmas.Part2`, `PromoteUpdate.BlueAlloc`)

The largest *bulk*, and the largest individual lemmas (four of the top five, §3).

`Part2.fst` is 3,381 lines and its header is candid: it proves `alloc_spec` preserves
`well_formed_heap_part1`, `fl_valid`, `fl_chain_terminates`, and framing. The structure
is a product:

```
2 (split vs. exact allocation)
  × 3 (target chain node / earlier node / later node)
    × 7 (part1, fl_valid, fl_chain_terminates, obj_not_in_chain,
         part4, new-objects-blue, no_black_objects)
```

≈ 30 named sub-lemmas, each an independently written induction over the *same*
`alloc_search` recursion, each with its own `#push-options`. Nothing here is deep. It is
long because the shared induction was never factored out.

`GC.Gen.PromoteUpdate.BlueAlloc`/`.BlueProm` (1,564 lines) is the same story for the
free-block *split* case under promotion, and contains the single longest lemma in the
repository.

### 5.3 `GC.Impl.MarkBounded.fst` — 512 s, file rlimit 25, plus 25 local overrides

The hardest *engineering*. It is where the most things must be true simultaneously: a
bounded stack whose overflow behaviour is semantically observable, two nested fuel
measures, a ghost termination witness, a nine-conjunct invariant of which four conjuncts
are themselves multi-clause spec predicates, and the entire framing burden of §4.1. Half
the file is lemmas that exist so the other half's loop invariants close.

The rlimit 300 this section originally reported was the `Makefile`'s, and §6.4 showed it
never applied: line 13 sets `--z3rlimit 25`, and everything after inherits that. The file
verifies identically with `--z3rlimit 1` on the command line. Its 25 local `#push-options`
blocks, ranging 10–100, are the settings that actually bind.

### 5.4 `GC.Gen.Cheney.fst` — 577 s, the slowest module in the repository

1,637 lines that verify in nearly ten minutes. This is the confluence point: BFS
traversal, allocator interaction, infix forwarding, OOM handling, and free-list
invariants all meet in `cheney_forward_one`/`cheney_forward_normal`. Every one of the
five generational complexity drivers (§4.5) is present in one module.

(This claim was false when first written — `GC.Gen.Impl.MinorHeap` was then 802 s, and had
been missed. It is true again now that §6.4 has brought that module down to 33 s. Unlike
MinorHeap's, this module's cost is real proof difficulty rather than fuel escalation.)

### 5.5 `GC.Gen.TwoPassEquiv.fst` (1,947 lines) — paying for a performance requirement

The reference spec `update_major_pointers` rescans the whole major heap. The
implementation scans only the just-promoted objects plus the remembered-set slots — which
is the entire point of a generational collector, since a full rescan would make minor GC
cost O(major heap). Proving these equal needs `ref_table_complete`,
`slots_pairwise_distinct`, `promoted_entries_disjoint`, `fwd_ptrs_classified`,
`heap_objects_dense`, a frame lemma and an effect-at-index lemma for each of the two
passes, and disjointness reasoning across them.

This is the clearest example in the development of a proof whose entire existence is
justified by a performance requirement, not by the correctness statement.

### 5.6 `GC.Spec.Sweep.fst`'s field-preservation chain — the rlimit ceiling

`sweep_aux_preserves_all_fields` at **rlimit 1,250**, built on
`sweep_aux_preserves_all_fields_range` (750) and `get_pointer_fields_aux_preserved` (500).
Three lemmas chained to establish one fact: sweep leaves a survivor's pointer fields
byte-identical. The cost is a per-field quantifier chain that compounds with field count.
Wide, not deep — hence a 20-second module with the highest rlimits in the repository.

---

## 6. What could be simplified

Ordered by (payoff ÷ risk). Each entry states its honest cost.

### 6.1 Merge the allocator's per-invariant inductions — **the single biggest lever**

**What.** Replace ~30 separate top-level lemmas in `Allocator.Lemmas.Part2.fst`, each
walking the `alloc_search` recursion for one invariant, with **one** induction proving the
conjunction. Same for `PromoteUpdate.BlueAlloc`.

**Payoff.** Plausibly cuts `Part2.fst` (3,381 lines) by more than half; ~2,000+ lines
across the two families. This is by far the largest reduction available that costs
nothing in functionality or performance.

**Cost.** A substantial one-time rewrite with real regression risk: a case silently missed
in the merged proof drops an invariant that only fails much later, in a different module.
The mitigation is the merge criterion already established in
[`docs/bloat-analysis.md` §4](docs/bloat-analysis.md), applied conservatively.

**Verdict.** Worth doing. Not a quick win.

### 6.2 Factor `objects`' recursion into a reusable induction principle

**What.** One well-founded-induction combinator over `heap_size - start`, parameterised by
the property, replacing ~15–20 hand-written mirrored recursions.

**Payoff.** Moderate line reduction; large reduction in the blast radius of any future
change to `objects`.

**Cost.** Higher-order lemmas over `GTot` predicates are awkward in F\* (universe and
decidability friction), and the combinator may need to be instantiated so specifically at
each site that the win evaporates.

**Verdict.** Worth prototyping on three lemmas before committing.

### 6.3 Package loop invariants as named `prop`s

**What.** `generational/impl/GC.Gen.Impl.fsti` already does this at the entry-point level
(`gen_gc_roots_post`, `gen_gc_heap_shape_post`, …). Extend it to loop invariants, so that
each `invariant` is one call plus the one or two genuinely loop-specific conjuncts.

**Payoff.** Makes the *actual* content of each loop visible rather than buried under
restated global well-formedness. Ergonomic, mostly.

**Cost.** Real, and already felt at the entry-point level: named props obscure *which*
conjunct is failing during proof development — the debugging experience gets worse
exactly when it matters most.

**Verdict.** Do it where the invariant is stable; leave it inline where it is still being
developed.

### 6.4 Extract the hard sub-goals out from under the blanket rlimits — **done**

**What was proposed.** `GC.Impl.MarkBounded.fst` carries a file-wide rlimit of 300 covering
2,104 lines, plus eight local overrides. Pull the specific hard steps into small, tightly
scoped modules with modest rlimits of their own.

**What measurement found.** The premise was wrong in an instructive way. Every blanket
`--z3rlimit` in the `Makefile` was **dead**, and removing all of them changed no
verification time by more than noise:

| module | blanket | measured without it | why it was dead |
|---|---|---|---|
| `GC.Impl.MarkBounded.fst` | 300 | passes at rlimit **1**, 411.9s (vs 412.1, 414.3) | superseded by `#set-options` on line 13 |
| `GC.Impl.Allocator.fst` | 100 | passes at rlimit **1**, 74.9s (vs 75.1) | superseded by `#set-options` on line 13 |
| `GC.Gen.Impl.fst` | 200 | 48.6s (vs 48.6s) | no goal exceeds the default of 5 |
| `GC.Lib.Header.fst` | 20 | 73.4s (vs 72.7s) | ditto |
| `GC.Gen.Impl.MinorHeap.fst` | 160 | 803.1s (vs 802.6s) | ditto |
| `GC.Gen.Impl.Cheney.fst` | 160 | 230.3s (vs 239.6s) | ditto |
| `GC.Gen.Impl.Promote.fst` | 160 | 18.5s | ditto |
| `GC.Gen.Impl.UpdatePtrs.fst` | 160 | 64.5s | ditto |

Two findings are worth keeping. First, **`#set-options` in a source file supersedes the
command line**, so a Makefile blanket is not merely redundant in those two files — it is
invisible. `GC.Impl.MarkBounded.fst` verifies unchanged with `--z3rlimit 1` on the command
line. Second, in the other six files the ambient budget was 30× larger than any goal
needed; `--query_stats` shows file-level goals consuming ~0.05 rlimit against a budget of
160.

So the stated payoff — "faster, more predictable incremental rebuilds" — was **not
delivered, and could not have been**. An unused budget costs nothing. The real payoff is
the one listed second: a local `#push-options "--z3rlimit 50"` inside a file-wide 300 reads
like a raise but is actually a *cut*, and no reader can tell without checking the build
system. All eight overrides are now gone.

**Where the time actually was.** Profiling for this exercise turned up something the
timing table in §3 had missed entirely: `generational/impl/GC.Gen.Impl.MinorHeap.fst` took
**802s**, making it the slowest module in the repository. It had been overlooked because of
a name collision — §3 timed the *spec* module `GC.Gen.MinorHeap` (24.9s), a different file.

All 28 of its failing goals were in one 30-line function, `minor_alloc`, and none of them
were rlimit-bound. Two goals — the body VC, and the `minor_heap_size` refinement from
`GC.Gen.Base` — discharge only at **fuel 8**. Left to discover that itself, F* escalates
`(2,1) → (2,2) → (4,2) → (8,2)`, and *each losing attempt runs the rlimit to exhaustion
before being abandoned*. The dead attempts, not the successful proof, were essentially the
entire runtime. Writing the winning setting down:

```fstar
#push-options "--z3rlimit 30 --fuel 8 --ifuel 2"
fn minor_alloc ...
```

takes the module from **802s to 32s**, a 25× speedup, with zero failing goals. This is the
genuine instance of the pattern §6.4 was reaching for, and it is a fuel problem rather than
an rlimit one.

**The same pathology, found repo-wide.** Since escalation leaves a signature in
`--query_stats` — a goal that *fails while consuming its entire rlimit*, repeatedly, at
rising fuel — the whole development was rebuilt under `OTHERFLAGS='--query_stats'` and the
66,448 resulting queries audited for it. Two more instances turned up, and both fixes are
one line:

| goal | wasted before | module: before → after |
|---|---|---|
| `GC.Gen.Impl.MinorHeap.minor_alloc` | 14 attempts, ~130 rlimit | 802s → **33s** (24×) |
| `GC.Impl.MarkBounded.rescan_heap_impl` | 9 attempts × rlimit 100 | 414s → **71s** (5.8×) |
| `GC.Lib.Header.get_tag_bound` | 8 attempts × rlimit 12 | 73s → **17s** (4.2×) |

`get_tag_bound` is worth dwelling on. It is a **one-line lemma** —
`logand_le #64 v 255` proving `get_tag v < 256` — and it was costing 56 seconds, because
proving it needs fuel 8 and F* had to discover that by exhausting rlimit 12 eight times
first. Nothing about the source suggests a problem; the lemma is correct, small, and
obviously true.

The remaining rlimit-exhausting failures in the audit (`alloc_from_block_split_normal`,
`scan_loop`, `promote_no_scan_new_object`, and about eight others) are a *different*
phenomenon and are deliberately left alone: they fail and then succeed **at the same fuel
setting**, which is Z3 4.15.3 nondeterminism rescued by `--retry 3`, not escalation. §4.7
covers that.

**The generalisable lesson.** Escalation is silent: a proof that needs high fuel still
*succeeds*, so nothing in the build output flags it, yet it can cost an order of magnitude.
It is also invisible in the source — none of the three sites looks expensive, and the
one-line `get_tag_bound` looks trivial. `--query_stats` plus a grep for goals that failed
while using their full rlimit is the cheapest audit in this repository, and it is worth
re-running after any Z3 upgrade, since which goals need which fuel is a solver-version
property. Note the token is `Query-stats`, hyphenated, and it is printed on stdout.

**Cost.** Three `#push-options` lines. No module boundaries were needed after all.

**Verdict.** Done, but for different reasons than predicted. The rlimit cleanup was
legibility only; the fuel fix was the win. Full clean verify: 13m23s → **12m36s** wall on
24 cores — the parallel critical path hides most of it, but the serial cost of these three
modules fell from 1,289s to 121s, which is what a developer re-checking one module feels.

### 6.5 A Pulse simulation combinator for "loop = unrolled pure twin"

**What.** One `while_simulates`-style schema capturing measure + decrease + unrolling
invariant, instantiated at the ~10 sites of §4.6.

**Payoff.** Several hundred lines of near-duplicated boilerplate; much smaller diffs at
each site.

**Cost.** The sites differ in kind — real fuel, ghost measure, array index — so this is
probably 2–3 variants, not one. Genuine Pulse-level design work.

**Verdict.** The most interesting item on the list, and the least certain.

### 6.6 Drop infix support in the nursery

**What.** Forbid large closures from being nursery-allocated, sending them straight to the
major heap. The infix branches in `cheney_forward_one`,
`CheneyPreservation.Forwarding`, and parts of `MinorHeap` then disappear.

**Payoff.** Moderate — roughly halves `CheneyPreservation.Forwarding`, touches `Fields`,
`Injectivity`, `NoBlue`.

**Cost.** Changes the runtime's allocation policy, not just its proof. This is a
*specification* change, and must be decided on runtime grounds.

**Verdict.** Listed for completeness. Not a proof-engineering decision.

### 6.7 Things that look like bloat and are not

Recorded so they are not re-nominated:

- **`well_formed_heap`'s four-way split with `wf_*` extraction lemmas (§4.4).** Standard
  practice for F\* developments at this scale. Removing it would regress verification
  times, not simplify anything.
- **The `CheneyPreservation` seven-module split.** The source states the reason outright
  (`CheneyPreservation.fsti:4-7`): *"Separated from GC.Gen.Cheney to avoid Z3 context
  pollution: adding val declarations to Cheney.fsti causes GC.Gen.Impl.Cheney.fst to fail
  verification."* Merging reintroduces exactly the problem the split solved. A genuine
  local optimum.
- **`SweepCoalesce`'s ~2,300-line fusion proof.** If the implementation must be
  single-pass, you need either this equivalence or an equally large direct proof of the
  fused pass's own five pillars. The current architecture — reuse `Sweep`'s and
  `Coalesce`'s already-proved pillars via an equivalence — is close to minimal.
- **`TwoPassEquiv`'s 1,947 lines.** Deleting it means giving up the remembered set and
  accepting O(major heap) minor collections. That is an algorithm decision, not cleanup.
- **`CombinedGraph` + `MinorCollectForwarding.*`, ~3,400 lines.** Intrinsic to proving a
  *copying* collector correct. Any comparable system needs an equivalent development.
- **`Cheney.Sim`, `Cheney.SimOne`, `CheneyBFS`, `Cheney.Dense`.** All confirmed
  load-bearing by dependency analysis. `Sim`/`SimOne` are what eliminated the last
  `assume_` in `GC.Gen.Impl.Cheney.fst`; `CheneyBFS` proves the no-OOM completeness
  property; `Cheney.Dense`'s `heap_objects_dense` is a precondition of `TwoPassEquiv`'s
  main theorem.
- **The `mark_post` abstraction.** Already the right call: it is why Pillar 2 is proved
  once rather than twice.

### 6.8 The lever nobody should pull

Replacing the flat byte-sequence heap with structural per-object ownership (sub-array
slices, or per-word fractional permissions) would let Pulse's frame inference discharge
most of the 35+ `_preserves_*` lemmas automatically — the single largest structural
saving available anywhere in the development (§4.1).

It would also ripple through every module in every tree, since `heap = seq U8.t` is shared
by spec and implementation alike, and would have to be re-justified against a C extraction
target that is a raw pointer with a fixed layout. That is precisely why the current design
avoids it. Recorded as the largest lever, at prohibitive cost.

### 6.9 Entry-contract hygiene — **done, with one residue**

**What was wrong.** `GC.Gen.Impl.fsti`'s `gen_gc` contract leaked four internal facts to
its callers:

1. `is_gray_stack`'s abstraction hid two of its own conjuncts — `Seq.length s <=
   stack_capacity st` and `stack_capacity st > 0` — so roughly a dozen sites restated
   them as preconditions.
2. `roots_valid_nonblue` was a strict consequence of the neighbouring
   `roots_valid_for_minor_collection`.
3. `gen_gc_major_precondition` was stated about the *post-darkening* state, forcing every
   caller to simulate `darken_roots_bounded_spec` before it could call the collector.
4. `major_field_zero_no_minor` demanded that no major object hold a minor pointer in
   field 0 — a hypothesis no real heap satisfies, since field 0 is a legitimate pointer
   slot; it was an artifact of the *generic* reachability bridge, not of write-back.

**What was done.**

- `GC.Impl.Stack.fsti` now exports a ghost `stack_facts` that recovers (1) from ownership
  of `is_gray_stack`, so the clauses can simply be dropped from client preconditions.
- `roots_valid_for_minor_collection_nonblue` derives (2) once; the conjunct was removed
  from eight contracts.
- `GC.Impl.MarkBoundedPrecondition` states the major-GC entry condition on the
  *pre-darkening* state (`darken_precondition`) and proves the transport lemma
  (`darken_establishes_precondition`) once, inside the library. `gen_gc`'s precondition is
  now a single application of it, discharged by `gen_gc_major_precondition_elim`.
- `major_field_zero_covered` replaces (4) with the satisfiable statement — field-0 minor
  pointers are permitted provided they are covered by the root set — and
  `reachability_bridge` was reproved against it.

All four are `prop`-level; the extracted C is byte-identical.

**Residue.** `major_heap_shape` (`GC.Gen.HeapInvariant.fst:29`) still has no
`no_gray_objects` conjunct, which is why `gray_objects_on_stack` survives as a caller
obligation even though every caller discharges it trivially (empty stack, no gray
objects). Adding the conjunct would remove the last non-derivable clause from the
major-GC entry contract. It touches an opaque predicate used throughout the generational
tree, so it is recorded here rather than done opportunistically.

---

## 7. Summary

| | |
|---|---|
| **Deepest mathematics** | `GC.Spec.Mark.fst` §5 — black ⇔ reachable, 1,813 lines, two unrelated inductions |
| **Largest bulk** | the allocator families — `Allocator.Lemmas.Part2` (3,381) + `PromoteUpdate.BlueAlloc`/`.BlueProm` (1,564); one induction shape × 7 invariants × 6 cases |
| **Hardest engineering** | `GC.Impl.MarkBounded.fst` — file rlimit 25 + 25 local overrides, 72 s, half the file is framing lemmas |
| **Slowest module** | `GC.Gen.Cheney.fst` — 577 s; every generational complexity driver meets in one file |
| **Most avoidable** | ~2,000 lines of repeated allocator inductions (§6.1) |
| **Cheapest win found** | three `#push-options` lines pinning fuel, worth 19 minutes of serial verification (§6.4) |
| **Least avoidable** | the copying-collector graph isomorphism (~3,400 lines) and the byte-sequence framing tax (§4.1) |

The honest summary is that the proof is roughly the size it has to be *given three
decisions*: a byte-exact OCaml-compatible heap layout (§4.1), a single-pass fused
implementation with a remembered set (§5.5, §6.7), and composition of a copying minor
collector with an unmodified in-place major collector (§4.5). Each of those is defensible
on its own terms, and each costs thousands of lines. What is genuinely *not* forced is the
repetition in the allocator proofs — that is the one place where a few thousand lines are
available for nothing but effort.

---

## 8. Related documents

- [`DESIGN_AND_IMPL.md`](DESIGN_AND_IMPL.md) — what the collector does and how it is built.
- [`docs/bloat-analysis.md`](docs/bloat-analysis.md) — the census, the merge criterion, and
  the record of what has already been trimmed (92,599 → 83,163 lines) and what was
  examined and deliberately kept.
- [`docs/dead-code-inventory.md`](docs/dead-code-inventory.md) — generated by
  `make depgraph-inventory`; currently 6 entries, all SMTPat/`squash` facts that must
  be retained.
- [`OPTIMIZATIONS.md`](OPTIMIZATIONS.md) — the performance decisions that several of the
  larger proofs (§5.5) exist to justify.

---

## 9. Reproducing the numbers

```bash
# Line counts per tree
for d in common mark-and-sweep generational spot; do
  find $d \( -name '*.fst' -o -name '*.fsti' \) | grep -v snapshot | xargs cat | wc -l
done

# rlimit distribution
grep -rho 'z3rlimit [0-9]*' --include='*.fst' --include='*.fsti' \
     common mark-and-sweep generational spot \
  | sed 's/.*z3rlimit //' | sort -n | uniq -c

# Proof gaps (expect: 0 admits, 2 assumes — both `squash SZ.fits_u64`)
grep -rn 'admit()' --include='*.fst' --include='*.fsti' common mark-and-sweep generational spot
grep -rEn '^\s*assume ' --include='*.fst' --include='*.fsti' common mark-and-sweep generational spot

# Per-module wall-clock (from the repository root; _cache/ is shared, so do not
# run this concurrently with a full `make`)
rm -f _cache/GC.Gen.Cheney.fst.checked
/usr/bin/time -f %e make _cache/GC.Gen.Cheney.fst.checked

# Dead-code inventory
make depgraph && make depgraph-inventory   # needs DEPGRAPH_OCAMLPATH set

# Full verification (~12-13 min on 24 cores) and extraction
make -k -j24 verify
make extract       # C output must match generational/snapshot/
                   # (modulo the 5-line KaRaMeL banner: path + version hash)

# Fuel-escalation audit (§6.4).  Rebuild everything with query stats, then look
# for goals that FAILED while consuming their whole rlimit -- that is F*
# escalating fuel, and each such attempt is wasted work.  Note the token is
# `Query-stats`, hyphenated, and it goes to stdout.
rm -rf _cache
make -k -j24 verify OTHERFLAGS='--query_stats' > /tmp/qs.log 2>&1
grep 'failed' /tmp/qs.log | sed 's/{reason-unknown=[^}]*}//' \
  | grep -oE 'Query-stats \([^,]+,[^)]*\).*rlimit ([0-9]+) \(used rlimit ([0-9.]+)' \
  | awk '{n=split($0,a,"rlimit "); if ((a[3]+0) >= (a[2]+0)*0.95) print}' \
  | grep -oE 'Query-stats \([^,]+' | sed 's/Query-stats (//' | sort | uniq -c | sort -rn

# A hit is real escalation only if the retries are at *rising* fuel; if the same
# goal fails and then succeeds at the SAME fuel, that is Z3 nondeterminism
# rescued by --retry (§4.7), and pinning fuel will not help.  Check with:
#   grep 'Query-stats (<name>,' /tmp/qs.log | grep -oE '(failed|succeeded) with fuel [0-9]+ and ifuel [0-9]+'

# Try one module with different flags, without disturbing the shared _cache:
tools/try-module.sh generational/impl/GC.Gen.Impl.MinorHeap.fst --query_stats
```

The per-module timings in §3 were taken cold (`.checked` removed first), one module at a
time, on an idle machine, with F\* nightly-2026-08-15 (commit `ae858ea`) and Z3 4.15.3.
They include dependency loading, so they measure *incremental rebuild cost after touching
that module*, which is the number that matters when working on the proof.
