# Plug-and-play verified GC components: interfaces and generic theorems

Design only. Nothing here is built. It is written against branch
`sheera/pages-incremental` at `94441bb4` (plan §30 committed), with main
at `5623c7f6`. Module names without a directory are in
`mark-and-sweep/spec/`; `GC.Gen.*` modules are in `generational/spec/`.

**Goal.** Build a collector from verified parts:
- an **allocator** (first-fit, pages, ...);
- a **minor collection** (Cheney promotion) over any allocator;
- a **major collection**, sequential or incremental, over any allocator and
  any sweep.

Each part is proved once against an **interface**. The correctness
theorems are stated over the interfaces, so they hold of every combination
of parts that meets them. A new allocator then costs its own contract and
nothing else.

**Where we start from.**
- `AllocIface` v2 is an allocator interface.
- `Pages.Promote` is a minor collection over any allocator.
- The page cycle (`Pages.Cycle`, `Pages.Cycle.Carried`) restates akhil's
  incremental-cycle theorems for pages, word for word.

The theorems exist twice: akhil's (`GC.Gen.Cycle`) for first-fit, ours
for pages. The incremental-cycle proofs are copies, specialised to each
allocator. This design makes them one proof, with two instances.

Contents:
1. The four interfaces
2. The generic theorems
3. What exists, what is missing
4. The page results as an instance; first-fit as an instance
5. Staged plan and estimates
6. Open questions

---

## 1. The four interfaces

Common vocabulary, all existing:
- `heap`, `obj_addr` and `objects zero_addr g` (`GC.Spec.Base`, `Heap`,
  `Fields`).
- `free_def`, what a collector counts as free; `in_use free g x`;
  `free_stw` (blue); `free_def_ok` (`GC.Spec.Fields`).
- `phase = Idle | Marking | Sweeping` (`AllocIface.phase`).
- `well_formed_heap_with free g`.

### 1.1 The allocator, `A`

The interface is v2's record (`AllocIface.allocator`) plus a tag, a split
invariant and a capacity condition. Call it v3, as in plan §22.3, but
narrower: the sweep's progress stays out of it (it belongs to the sweeper,
§1.4).

```
noeq type allocator3 = {
  ast     : Type0;                                   (* its own state *)
  shape   : phase -> heap -> ast -> prop;            (* its own structures; reads no field of a block in use *)
  alloc   : phase -> heap -> ast -> nat -> tag_t -> GTot (heap & ast & U64.t);
  unswept : ast -> hp_addr -> prop;                  (* decides the colour mid-sweep *)
  pending : ast -> hp_addr -> prop;                  (* words it must not touch *)
  room    : phase -> heap -> ast -> nat -> prop;     (* its capacity condition *)
}
```

**The contract, `allocator_ok3 a free`.** `free ph s` is what the collector
counts as free in that phase and state. For every `ph g s wz tag` with
`a.shape ph g s`, `well_formed_heap_with (free ph s) g` and
`tag <> infix_tag`, write `(g', s', o) = a.alloc ph g s wz tag`.

| | Clause | Meaning |
|---|---|---|
| A1 | **capacity, exactly** | `o <> 0 <==> a.room ph g s wz` |
| A2 | failure changes nothing | `o == 0 ==> g' == g /\ s' == s` |
| A3 | the object | `o` is an object of `g'` of wosize `wz`, tag `tag`, colour `colour_at a s ph o`, and was not in use in `g` |
| A4 | **only it comes into use** | `in_use (free ph s') g' y <==> in_use (free ph s) g y \/ y == o` |
| A5 | frame | `others_unchanged g g'`, and every `pending` word is unchanged |
| A6 | carved from free space | a word of `o`'s extent, or of a block free in `g'`, lay in a block free in `g` |
| A7 | the walk | `heap_objects_dense g'` (W, §22.3); optional per instance W+: `walk_end g' == walk_end g` |
| A8 | **the caller's writes** | every heap `g''` made from `g'` by writing `o`'s fields with storable values (`fields_written_with`) has `a.shape ph g'' s'` and `well_formed_heap_with (free ph s') g''` |
| A9 | phases | `shape Idle ==> shape Marking`; recolouring a block in use to any colour but blue keeps `shape Marking` (v2's `phase_ok`) |

**The colour rule** is v2's `colour_at`, unchanged:
- `Marking`: black;
- `Sweeping`: black if the header is in `unswept` memory, white otherwise;
- `Idle`: white.

It is what makes a new object survive the cycle it is born in (§2.3).

**Capacity, per allocator.** `room` is the allocator's own statement of
"there is space for this request". It is not a global "the heap is
full":
- fragmentation is the allocator's business;
- mid-sweep, only memory the allocator can see counts.

A1 is **both directions**: the allocator never fails when its condition
holds, and never succeeds when it does not. The second direction rules
out a degenerate `room = False` that would make A1 vacuous for failures.

| | First-fit (main) | Pages |
|---|---|---|
| `room ph g (fp, c) wz` | a blue block on the free list from `fp` that `alloc_search`'s fit test accepts for `wz` (to be stated with that test, including the split rule) | `~(Th.no_fit g st (wz + 1))`: for a small block, a free slot on a swept page of its class, or a `Free` page; for a large one, a listed block of at least `wz + 1` words, or `pages_for (wz + 1)` consecutive `Free` pages |
| Mid-sweep reading | the list is exact at every point of the sweep (`sweep_inv_incremental`), so the same predicate | only swept pages count: an unswept page's dead slots are not room until a sweep step reaches them |

What exists for A1 is in §3.1.

**Out of the allocator:**
- sweeping on demand (pages' `pool_find`, a sweep step before an
  allocation): that is the sweeper's step (§1.4), taken by the runtime
  before `alloc`;
- the retry policy after a failure (collect, then allocate again): that is
  the runtime's.

### 1.2 The mutator, `M`

The mutator is not verified. Its behaviour enters as **trusted premises**:
the hypotheses of the run's events. Everything the theorems conclude is
conditional on them. These are the obligations akhil's runs already state
(OCaml's type safety, and the runtime's write barrier). They are listed
here as one interface, so that each obligation is named once.

**Events:**

| Event | Phase | Parameters |
|---|---|---|
| `Alloc` | any | `wz`, `tag`; then the initialising writes of the new object's fields (`init_writes`) |
| `Write` | any | `x`, `a`, `v`: store `v` in the body word `a` of `x` |
| `Roots` | at the start of a cycle, and at a minor collection | the root set `rs`, given to the collector |

Reads are not events. They do not change the heap. What the program may
read is constrained by M2.

**Obligations, `mutator_ok`:**

| | Obligation | Where it is stated today |
|---|---|---|
| M1 | **only reachable objects are touched**: `Write` targets a block in use, not a closure's code pointer, inside its body | `SPM.program_write free g x a v`; `GB.modify_ok` while marking |
| M2 | **stored values are storable**: not a pointer, or a pointer to a block in use (through a valid interior pointer) | `field_ok_with free`, `SPM.storable free` |
| M3 | **snapshot discipline while marking**: a value stored, or used to initialise a new object, is in the snapshot (reachable at the start, or allocated since) | `MPC.cycle_write`, `SPM.fields_storable (outside_snapshot …)` |
| M4 | **the barrier**: an overwritten pointer field while marking greys the old target (SATB) | `MM.marking_write_barrier` inside `GB.modify_heap Ph.Marking` |
| M5 | **the nursery discipline**: every nursery pointer held in the major heap is recorded (the remembered set is sound and covers) | `ref_table_sound_with`, `ref_table_covers_with` (`GC.Gen.RefTable`) |
| M6 | **roots**: the roots given to a collection are valid (`roots_valid_for_minor_collection`, `mark_pre`), and the program holds nothing else | the `Minor` events' hypotheses, `MP.outside_refs_reached` |

M4 is the one obligation the runtime, not the program, discharges:
`caml_modify` runs the barrier. It is a premise because the barrier's C
code is not verified.

**What is trusted and what is checked.**
- The runs take M1–M6 as hypotheses (`squash` in each constructor).
- A theorem about a run never assumes more than these, plus the
  collector's own events.
- `Pages.Cycle.Carried` already carries the allocator's invariant itself;
  only M1–M6 and akhil's marking invariant remain hypotheses.
- The design keeps that split: the mutator interface is exactly the
  premises, and nothing about the allocator or the sweeper is a premise.

### 1.3 The minor collection, `N`

A promotion through **any allocator meeting a contract**. This already
exists as `Pages.Promote.tal` and `contract`. That contract is the minor
collection's view of A: one phase, one colour, one `free`:

```
noeq type tal (s: Type0) = { inv; alloc: heap -> s -> nat -> tag_t -> …; free: free_def; col: color }
contract a = free_def_ok a.free /\ (inv ==> well_formed_heap_with a.free) /\
             (inv /\ tag <> 249 ==> alloc_ok a …) /\ (update_walk keeps inv)
```

**The interface:**
- `collect a minor major st roots` (`Pages.Promote.collect`), giving the
  major heap, the allocator state, the reset nursery, the rewritten roots
  and the forwarding map;
- preconditions `L.cpre a minor g st` (the allocator's invariant and
  contract, the nursery's shape, `minor_major_fields_not_free a.free`), M5
  and M6.

**What it guarantees** (`Pages.Promote.Collect`, the facts of §22.5's table):

| | Guarantee | Today |
|---|---|---|
| N1 | the allocator's invariant after | `collect_inv` |
| N2 | blocks in use before keep their header and major pointers; the made blocks are exactly the copies | `collect_old`, `collect_new` |
| N3 | every forwarded pointer targets a block in use, through a valid interior pointer for infix | `fwd_targets` |
| N4 | made blocks have the allocator's colour (black while marking) | `alloc_ok`'s colour, at `mark_tal` |
| N5 | **marking**: the account and the marking invariant are kept (`account_minor`, `minor_keeps_marking_inv_with`) | `Pages.Promote.Mark` |
| N6 | **sweeping**: the account and its converse are kept, with the copies added to `since` | `Pages.Promote.Sweep`, `Promote.Idle` |
| N7 | the Pulse implementation computes `collect` | `Impl.Pages.Minor.minor_collect` (§30) |

**From A to N.** A `tal` is an `allocator3` frozen at one phase and state
kind: `alloc g st wz tag = a.alloc ph g st wz tag`, `free = free ph st`,
`col = colour_at`. This needs the colour to be uniform over the phase:
- it is in `Marking` and `Idle`;
- mid-sweep it is not, since `colour_at` reads `unswept`.

Pages' copies always land in swept memory, so `col = White` there
(`sw_tal`). A generic lemma `tal_of a ph` gives `contract (tal_of a ph)`
from `allocator_ok3` (A3, A4, A8; A1 is not needed). Mid-sweep it needs an
instance fact, "copies land in swept memory" (pages), or a `tal` whose
`col` is per object (first-fit, which can place a copy above its cursor).
See question Q2.

### 1.4 The major collection, `C`

Two forms over the same parts.

**Marking** is allocator-free:
- the mark state is akhil's `MP.marking_inv`, `scan_pos` and the grey
  stack;
- slices are `S.mark_steps`;
- the barrier is M4.

No interface is needed for it. It is one fixed component, `C.mark`, used
by both forms.

**The sweeper, `W`** (plan §22.2's record, unchanged in shape):

```
noeq type sweeper (a: allocator3) = {
  free_of   : a.ast -> free_def;                          (* free mid-sweep *)
  start     : heap -> a.ast -> a.ast;                     (* the hand-over *)
  step      : heap -> a.ast -> GTot (heap & a.ast);       (* one unit (pages: a page; first-fit: a block) *)
  done      : a.ast -> bool;
  sweep_inv : heap -> a.ast -> prop;                      (* the collector's sweeping state *)
}
```

A slice is a sequence of steps, and a budgeted slice is a prefix. So
slices need not be in the record.

**Its contract, `sweeper_ok a w`**, the clauses S1–S7 of §22.2:
- S1: `free_def_ok`;
- S2: `free_of` agrees with the colour rule;
- S3: start, from the marked heap;
- S4: a step keeps `sweep_inv`, the account `acct` and `reclaimed_was_dead`;
- S5: at `done`, the `Idle` shape, `well_formed_heap`, and `free_of`
  agreeing with `free_stw`;
- S6: the program's events and the minor collection do not move the sweep;
- S7: an unbounded sweep reaches `done` (liveness).

**Phases.** `Idle → (start, roots) Marking → (nothing grey) Sweeping →
(done) Idle`.
- The allocator sees only the phase (§1.1).
- The sweeper's progress lives in the allocator's state (§22.2's decision),
  so `unswept` and `free_of` read the same state.

**The two forms:**
- **Sequential** (stop-the-world): `collect_stw a w g st rs = sweep_all w
  (mark g rs) (w.start st)`. It has no program events.
- **Incremental**: a run `gcycle a w n g0 rs : heap -> a.ast -> phase ->
  (obj_addr -> prop) -> Type`. Its constructors are:
  - `Start`;
  - `MarkSlice`;
  - `Write` (M);
  - `Alloc` (A, then M's writes);
  - `Minor` (N at the current phase);
  - `Handover`;
  - `SweepStep` (W);
  - `End`;
  - `IdleMinor` (N after the sweep, as §29.1).

  The last index is `since`: the addresses handed out during the cycle,
  by `Alloc` or by `Minor`'s copies. It is the generic form of
  `Pages.Cycle.Carried.ccycle`. The allocator's and sweeper's invariants
  are **carried by the run**, not hypotheses of its events. Only M's
  obligations and akhil's marking invariant are hypotheses.

---

## 2. The generic theorems

Each is stated for any `a`, `w`, `n` meeting their contracts. Write
`reach0 x` for `GMC.reachable_at_start g0 rs x`. An object of `g0` that is
not `reach0` is **dead at the start**.

### 2.1 Allocation

**Theorem `alloc_correct`.** For `allocator_ok3 a free`, `a.shape ph g s`
and `well_formed_heap_with (free ph s) g`:
- the allocation succeeds exactly when `a.room ph g s wz` (A1);
- on success it meets A3–A8;
- on failure nothing changes.

**Corollaries, per instance:**
- first-fit after a full collection: a failure means no free block fits
  (akhil's `fused_oom_no_fit`), so `room` after `collect_stw` is
  "some block of the swept heap fits";
- pages: a failure means `Th.no_fit`, with only swept pages counted
  mid-sweep.

### 2.2 The sequential collection

**Theorem `gc_correct_generic a w`.** For `allocator_ok3`, `sweeper_ok`,
`a.shape Idle g st`, `well_formed_heap g` and `mark_pre g rs`, write
`(g', st') = collect_stw a w g st rs`.

- **Safety:**
  - `well_formed_heap g'`;
  - the mark is exact (`Corr.full_gc_correctness g g' rs`);
  - the survivors' subgraph is unchanged
    (`Corr.major_gc_live_subgraph_isomorphism`);
  - `a.shape Idle g' st'`: the allocator can run again;
  - no pointer to free memory.
- **Liveness:**
  - every word of a dead object lies in a block free in `g'`
    (`unreachable_reclaimed`);
  - **lossless**: a word lies in a free block of `g'` exactly when it lay
    in a dead object or a free block of `g`.

What is generic here is the shape of the statement. Each allocator adds
its own corollaries about its structures:
- `lists_sound` and `free_listed` for pages;
- `fl_sound` and `fls_complete` for first-fit.

These are instance theorems, not part of the generic one.

### 2.3 Incremental equivalence

The central theorem. A run `r : gcycle a w n g0 rs g st Idle since`
interleaves, in any order allowed by the phases:
- mutator events (meeting M1–M6);
- minor collections (N, at any phase);
- mark slices and sweep steps of any size.

**What "the same result" means.** The stop-the-world collection at the
cycle's start, `collect_stw a w g0 st0 rs`, frees exactly the dead objects
of `g0`. The incremental run cannot produce the same heap:
- the program has written fields;
- it has allocated, and promoted;
- the free structures differ (block order, page lists, coalescing).

So "same result" is about **which objects are freed and which survive**,
not about bytes. It is stated over addresses and over words.

Garbage created **during** the cycle is **not** freed by it, which is the
SATB snapshot's floating garbage. It comes in two kinds:
- (i) an object reachable at the start that the program drops during the
  cycle;
- (ii) an object allocated or promoted during the cycle (in `since`),
  reachable or not.

Both survive this cycle and are freed by the next one, if still
unreachable at its start. This is exactly what an STW collection at the
start would do to them: (i) was live at the start, and (ii) did not
exist.

**Theorem `incremental_equiv r`**, once the run is idle again:

| | Clause | Statement | Status for pages |
|---|---|---|---|
| E1 | **frees exactly the STW set** | `forall x. ~(since x) ==> (freed g x <==> (Seq.mem x (objects g0) /\ ~(reach0 x)) \/ ~(Seq.mem x (objects g0)))`. Equivalently, on the objects of `g0`: freed by the run ⇔ freed by `collect_stw` at `g0` | `cycle_addresses_lossless` gives `~since x ==> (reach0 x <==> ~freed g x)`; the link to `collect_stw`'s freed set (from `gc_correct_generic`'s exactness) is **missing** |
| E2 | **survival** | `reach0 x ==>` `x` is a block of `g` in use, at its `g0` size, and `~(since x)` | `cycle_survives` |
| E3 | **new objects survive** | `since x /\ Seq.mem x (objects g) ==> ~(is_blue x g)`: the floating garbage of kind (ii) is kept | **missing as a theorem**. It follows from the colour rule (S2, `colour_at`) and the account; it is not stated today, since the cycle theorems quantify over `~since x` |
| E4 | **word-lossless** | `forall p < heap_size. unreachable_covered g0 rs p <==> blue_covered g p \/ new_covered since g p` | `cycle_lossless` (pages: every word, the last included, by layout L1) |
| E5 | **safety, at every state** | every object the program can reach from its current roots is in use: M3 keeps what the program holds inside the snapshot, and the account keeps the snapshot in use | the account is `cycle_account` / `ccycle_inv`; the reachability statement "reachable from the current roots ⇒ in use" is **missing**, as a corollary of the account and M3/M6 |
| E6 | **the next cycle may start** | `a.shape Idle g st`, `well_formed_heap g` | `ccycle_correct` (pages) |

**Minor collections inside the cycle.**
- Nursery objects are outside the major heap. Their death is the minor
  collection's business: an unreachable nursery object is never copied.
- A copy is a new major block, so it enters `since` (`with_new_blocks`,
  `with_made`).
- So E1–E4 are about the major heap, and nursery garbage is reclaimed by
  the reset (N).

**Why E1 is the right "exactly".**
- The STW collection at `g0` frees `D = {x ∈ objects g0 | ~reach0 x}`.
- E1 says the incremental run frees exactly `D`, except at addresses it
  handed out again, where the old dead object's space now holds a new
  object (E4 accounts for those words as `new_covered`).
- Nothing reachable at the start is freed (E2), and nothing dead at the
  start is kept (E1, E4).

---

## 3. What exists, what is missing

### 3.1 Per interface

| Interface | Exists | Missing |
|---|---|---|
| **A** allocator | `AllocIface` v2: the record (state, `inv` per phase, `alloc` per phase, `unswept`, `pending`); `alloc_post_with`/`allocator_ok_with` (A2, A3 without tag, A5, A8 as "every write-out satisfies `inv`"); `colour_at`; `phase_ok` (A9). Pages instance: `Pages.Allocator.pages_allocator_ok`, `pages_allocator_sw_ok` (§21). Tag: `Pages.AllocTag.alloc_tag` (pages only) | the record with tag and `room` (`allocator3`); A1 in both directions (pages has failure ⇒ `no_fit`: `alloc_no_fit`; success ⇒ `~no_fit` is unproved; first-fit has failure ⇒ no fit on an exact list: `alloc_spec_oom_no_fit`, `sweep_inv_incremental_oom_no_fit`, not as an interface clause); A4 and A6 as clauses (pages has them per phase in `NewOnly`, `MidSweepAlloc.use_eq`, `Replace`; `Marking`'s A4 is done for the tagged allocator in `PromoteInst`/`Cycle.AllocTagged`); A7 at `Marking` for pages; the `shape`/well-formedness split (§22.3 change 2) |
| **M** mutator | every obligation, as hypotheses of akhil's runs and of `Pages.Cycle.Carried`: `GB.modify_ok`, `MPC.cycle_write`, `SPM.program_write`, `SPM.fields_storable`, `init_writes`, `roots_valid_for_minor_collection`, `outside_refs_reached`, RefTable soundness | one named interface `mutator_ok` collecting them; the statement that they are the **only** premises (a check that no run constructor takes anything else, except akhil's marking invariant) |
| **N** minor | `Pages.Promote` (`tal`, `contract`, `collect`), `Promote.Loop`, `.Collect`, `.Mark`, `.Sweep`, `.Idle`, `PromoteInst` (`mark_tal`, `sw_tal`), `Promote.Sim`, `TwoPass`; Pulse `Impl.Pages.Minor` equal to `collect` in every phase (§30) | `tal_of a ph` from `allocator3` (§1.3); N5/N6 stated over the generic account (today `Pages.Promote.Mark`/`Sweep` are stated over the page cycle's invariants); a first-fit `tal` |
| **W** sweeper | pages: `Pages.Allocator`'s sweep section (`sweep_start`, `sweep_step_inv`, `sweep_end`, `sweep_all_correct`), `MidSweepStep` (`sw_start`, `step_sw`, `sw_end`), `SweepAll.step`, `Incr.slice_from`; first-fit: akhil's `SL.phase_slice`, `phase_account_start/slice`, `freed_by_end` | the `sweeper` record and `sweeper_ok`; for pages, S3/S4's account clauses in the generic `acct` form (they exist inside `Pages.Cycle.Sweep`, specialised); for first-fit, the record over `(fp, c)` from akhil's lemmas |
| **C** major | marking: akhil's `MP`, `S.mark_steps`, `MM`, `GMC` (allocator-free, used read-only today); sequential: `GC.Impl.Correct.gc_correct` (first-fit), `Pages.GcCorrect.gc_correct_pages`/`gc_correct_gen` (pages); incremental: `GC.Gen.Cycle` (first-fit), `Pages.Cycle`, `Pages.Cycle.Carried`, `Pages.Cycle.Incr` (pages) | `col_shape` (§22.1: the collector's state without the free list); the generic run `gcycle`; the generic sequential `collect_stw` |

### 3.2 Per theorem

| Theorem | First-fit | Pages | Generic |
|---|---|---|---|
| `alloc_correct` (A1) | half: failure ⇒ no fit (`GC.Spec.Allocator.Oom`) | half: failure ⇒ `no_fit` (`alloc_no_fit`) | missing |
| `gc_correct_generic` | `GC.Impl.Correct.gc_correct` | `gc_correct_pages`, `gc_correct_gen` (any marked heap) | missing; `gc_correct_gen` is already generic in the mark |
| E1 (as "frees D") | `GC.Gen.Cycle.cycle_addresses_lossless` | `Pages.Cycle.cycle_addresses_lossless` | missing (both are copies of one proof); the link to `collect_stw` missing in both |
| E2 | `cycle_survives` | `cycle_survives` | missing |
| E3 | missing | missing | missing |
| E4 | `cycle_lossless` (walk-end form) | `cycle_lossless` (every word) | missing; §22.4's density form |
| E5 | account only (`major_cycle` invariants) | account only (`ccycle_inv`) | missing |
| E6 | (main's runs take `phase_shape` as hypotheses) | `ccycle_correct` | missing |
| Vacuity | SPOT runs (`MarkPhaseCycleAlloc`, `SweepPhaseCycleAlloc`, `SweepPhaseFreedByEnd`) | `Cycle.Vacuity`, `VacuityDark`, `CarriedVacuity`, `IdleVacuity`, `MinorVacuity{,2}`, `IncrVacuity`, `PulseVacuity` | through the instances |

### 3.3 akhil's lemmas used read-only

Already used unchanged by the page modules. The generic modules would use
the same ones:
- **Marking, allocator-free:**
  - `GC.Gen.MarkPhase.{Start,Safety,Completeness,Cycle,Walk}`;
  - `MPC.account_steps/barrier/alloc/fresh_close`;
  - `S.mark_steps_inv`, `MM.marking_write_barrier`, `MP.marking_inv`.
- **The sweep account, generic in `free`:**
  - `GC.Spec.SweepPhase.Completeness`: `survivor`, `with_new`,
    `reclaimed_was_dead`, `reclaimed_was_dead_transfer`, `idle_account`,
    `covered_at_idle`, `lossless_at_idle`, `survived_at_idle`, `freed`;
  - `SPM.program_write`, `storable`.
- **The minor collection:**
  - `GC.Gen.Promote` (the forwarding map, `update_pointers_with`,
    `rewrite_roots`);
  - `GC.Gen.CheneyGeneric` (`cheney_promote_fwd_targets_not_free`,
    `cheney_promote_preserves_wf_with`,
    `update_pointers_with_preserves_wf`);
  - `GC.Gen.Cheney.Sim`, `TwoPassEquiv`, `RefTable`, `ForwardingArray`,
    `PromoteUpdate.Aux`;
  - the Pulse `MinorHeap`, `UpdatePtrs`.
- **The cycle words:**
  - `GC.Gen.Cycle`'s private word lemmas (`parts`, `start_words`,
    `reach_words`, `handover_words`, `new_words`), copied into
    `Pages.Cycle` because they are private.
  - The generic cycle would own the one copy.

---

## 4. Instances

### 4.1 Pages: the existing results as corollaries

**The instance:**
- `A_pages`:
  - `ast = pstate`, `shape` = the page invariant without
    well-formedness (§22.3 change 2: `Scrub.core` with each phase's colour
    facts; today `PA.inv` includes well-formedness);
  - `alloc = AT.alloc_tag`, `unswept = MP.unswept`;
  - `pending = unswept`, `room = ~no_fit`.
- `W_pages`:
  - `free_of = MS.free_sw st.pm`, `start = StartSweep.start_sweep`;
  - `step` = `SweepAll.step` at the cursor's page, `done = all_swept`;
  - `sweep_inv = MS.pages_ok_sw` (with `map_ok` for the Pulse slice).
- `N_pages = Pages.Promote.collect` at `tal_of A_pages ph` (= `mark_tal`,
  `sw_tal`, `idle_tal`).

**The current theorems, kept as corollaries.** Every current statement
stays, with its name and module. Its proof becomes the generic theorem at
the instance:
- `Pages.Cycle.Carried.ccycle` maps into `gcycle A_pages W_pages N_pages`
  by a total `to_generic`, event for event. `ccycle` has the same
  constructors, with the allocator and sweeper invariants carried, as the
  generic run.
  - `ccycle_inv` and `ccycle_correct` are then the generic E-theorems and
    E6 at the instance.
  - `Pages.Cycle`'s `cycle_*` theorems follow through the existing
    `to_pcycle` in reverse. They are stated over `pcycle`, whose events
    take the invariants as hypotheses, so `pcycle` maps into `gcycle` by
    discharging nothing.
- `cycle_lossless`'s every-word form is the generic density form (§22.4)
  plus the instance fact of layout L1: the walk ends at `heap_size` in
  every page state (`TailWalk`). No weakening.
- `gc_correct_pages` is `gc_correct_generic` at the instance, plus the
  page corollaries (`lists_sound`, `free_listed`, `heap_classified`).
- `pages_allocator_ok` is `allocator_ok3` restricted to tag 0, minus A1
  and A6.
  - A5 at `pending = unswept` is v2's frame.
  - A3's tag is `AllocTagOk`.
  - A4 is `NewOnly`/`use_eq`/`PromoteInst`.
- The Pulse results (`Impl.Pages.*`) are unchanged: they compute the
  spec functions the instance is built from.

**What is new for pages:**
- A1's success direction (allocation succeeds ⇒ `~no_fit`): per path, from
  the path taken;
- A6 as one lemma over the paths;
- A7 at `Marking`;
- the `shape` split (does `Scrub.core` read live fields? `core_fill_objs`
  says no for dead ones; a per-write form for live ones is new, §22.3 F);
- S3/S4 in the generic `acct` form (the content exists in
  `Cycle.Sweep`).

### 4.2 First-fit, with akhil's modules unchanged

**The instance**, in new modules (`GC.Spec.FirstFit.*`), using only his
statements:
- `A_ff`:
  - `ast = U64.t & U64.t` (`fp` and the cursor `c`);
  - `shape Idle (fp, _) = fl_ascending g fp /\ alloc_ok g fp`;
  - `shape Sweeping (fp, c) = sweep_inv_incremental g fp c` (with the
    well-formedness part split off: `GenInv.major_shape_with` is opaque
    with `_intro`/`_elim`);
  - `alloc ph g (fp, c) wz tag = AP.alloc_at (to_gc_phase ph c) g fp wz
    tag`, `unswept (_, c) b = b >= c`;
  - `pending = the words of pending_free c blocks` (heap-dependent; §22.3
    change 3: `pending` takes the heap);
  - `room` = a fitting block on the list.
- `W_ff`:
  - `free_of (_, c) = free_incremental c`;
  - `start = (fp, sweep_start.cursor)`;
  - `step = SL.phase_slice` at budget 1, `done = sweep_done c`;
  - `sweep_inv = sweep_inv_incremental`.
- `N_ff` = `Pages.Promote.collect` at a first-fit `tal`, or akhil's
  `Promote` itself (see below).

**The clauses from his lemmas:**

| Clause | His lemma |
|---|---|
| A1 (failure) | `alloc_spec_oom_no_fit`, `sweep_inv_incremental_oom_no_fit` |
| A1 (success) | `alloc_at_obj_valid`, `Exact.reachable_valid_cell` (the cell found is on the list and fits) |
| A3 | `alloc_at_obj_in_objects`, `alloc_at_obj_wosize`, `alloc_phase_new_block`, `marking_alloc` (tag) |
| A4 | `Mut.alloc_in_use`, `alloc_keeps`; Marking/Idle through `alloc_at_recoloured` |
| A5 | `alloc_at_preserves_objects`, `others_unchanged` from `Allocator.Lemmas` |
| A6 | `Mut.alloc_carved` |
| A7, W+ | `MW.alloc_reaches`, `Mut.alloc_walk_end` |
| A8 | `MPA.marking_alloc`, `marking_fresh_write`, `marking_fresh_close`; `alloc_sweep_phase`, `fresh_write`, `fresh_close` |
| A9 | `recoloured_facts`, `recoloured_fl`, `recoloured_wf` (`Allocator.Phase`) |
| S1–S7 | `free_incremental_ok`; `pending_free` (S2); `phase_account_start` (S3); `phase_account_slice`, `GI.phase_slice_shape` (S4); `GI.sweep_end_shape`, `freed_by_end` (S5); `alloc_sweep_phase`, `write_sweep_phase` (S6); `GI.phase_slice_finishes` (S7) |
| N (marking) | `GMC.account_minor`, `GMM.minor_keeps_marking_inv_with`, `minor_keeps_block`, `minor_new_block_black`, `MW.minor_reaches` |
| N (sweeping) | `SPC.survivor_or_new_minor_made`, `reclaimed_was_dead_minor`, `GI.minor_keeps_phase_shape` |

**His theorems as corollaries.** A total `to_generic` from his run types
(`MC.marking`, `SC.cycle`, `GC.Gen.Cycle.major_cycle`) into `gcycle A_ff
W_ff N_ff` (§22.6). Then:
- each of his conclusions is the generic theorem applied to `to_generic
  r`, with his statement;
- his `cycle_lossless` (walk-end form) follows from the generic density
  form plus W+, which first-fit has;
- his modules are not edited; the map and the instance live in new
  modules.

**Two risks.**
1. **The minor event.** His `Minor` constructors run his `Promote`
   (`AP.alloc_at`), not `Pages.Promote.collect`.
   - So `N_ff` must be his promotion, with N1–N6 from his lemmas, as in
     the N rows of the table; the generic run takes `n` as a record (§22.5
     `minor_event`), not as `Pages.Promote` fixed.
   - Proving that his `Promote` equals `Pages.Promote.collect` at a
     first-fit `tal` would let both share one N. It is not needed for the
     theorems, and it is likely long (his promotion hard-wires
     `alloc_at`).
2. **The mid-sweep colour.** First-fit can place a promoted copy above its
   cursor (black) or below (white), so a uniform `tal.col` does not hold
   mid-sweep. Either `tal` gets a per-object colour, or the first-fit
   minor event stays his.

---

## 5. Staged plan

Estimates are in working days at the pace of plans §23–§30, each of which
took about one to two working days for 1,500–3,000 new lines. The rules
throughout:
- new modules only, akhil's read-only;
- no theorem weakened;
- seeds 0–2 without `--retry`, rlimit ≤ 40;
- a constructive witness per theorem.

| Stage | Content | New modules (est. lines) | Days |
|---|---|---|---|
| 0 | Agree this document, and §6's questions, with akhil | – | – |
| 1 | **A v3**: `allocator3`, `allocator_ok3`, `room`; generic `alloc_correct`; v3 ⇒ v2 lemma | `GC.Spec.AllocIface3` (~300) | 1 |
| 2 | **Pages A**: A1 success direction, A6 as one lemma, A7 at Marking, the `shape` split; `pages_allocator3_ok`; v2 statements as corollaries | `Pages.Allocator3` (+ helpers, ~900) | 3 |
| 3 | **W**: `sweeper`, `sweeper_ok`, generic `acct`; pages instance (S3/S4 from `Cycle.Sweep`) | `GC.Spec.Sweeper`, `Pages.Sweeper` (~800) | 3 |
| 4 | **N from A**: `tal_of`, N5/N6 over the generic account; pages instance from `Promote.Mark/Sweep/Idle` | `GC.Spec.Minor`, `Pages.MinorInst` (~600) | 2 |
| 5 | **M**: `mutator_ok`, one record of the obligations; check every run constructor takes only M and the marking invariant | `GC.Spec.Mutator` (~200) | 0.5 |
| 6 | **The generic run and E-theorems**: `col_shape`, `gcycle`, E1–E6 (E3, E5 and E1's link to `collect_stw` are new proofs; the word proofs moved here from `Pages.Cycle`) | `GC.Spec.Cycle.*` (~2,500) | 6 |
| 7 | **Pages as an instance**: `to_generic` for `ccycle` and `pcycle`; every current theorem re-proved as a corollary under its own name; witnesses carried over | `Pages.Cycle.Generic` (~700) | 2 |
| 8 | **The generic sequential collection**: `collect_stw`, `gc_correct_generic`; pages' `gc_correct_pages` as corollary | `GC.Spec.Stw` (~800) | 3 |
| 9 | **First-fit as an instance**: `A_ff`, `W_ff`, `N_ff` (his promotion), from his lemmas (§4.2's table); `to_generic` for his runs; his theorems as corollaries; witnesses via his SPOT runs | `GC.Spec.FirstFit.*` (~2,000) | 6 |
| 10 | Docs, audit (vacuity, rlimits, seeds), `gmake verify` | – | 1 |

**Total:** about 27 working days, and about 9,000 new lines. The ranges
that could move most:
- stage 6 (the density form of `reclaimed_was_dead_transfer` and
  `lossless_at_idle`, §22.4's risk);
- stage 9 (first-fit's heap-dependent `pending`, and the mid-sweep colour
  of copies).

**Order and checkpoints:**
- After stage 4, the pages instance of A, W and N exists.
- After stage 7, every page theorem is a corollary of a generic one: the
  first useful end point.
- Stage 9 is independent of stage 8, and can go first if first-fit
  matters more than the sequential theorem.

No implementation (Pulse, C) changes in any stage. The Pulse code already
computes the spec functions the pages instance is built from (`AllocInc`,
`SweepInc`, `Minor`).

---

## 6. Open questions

- **Q1. `room` in the record**, or a separate per-instance capacity
  lemma? In the record, A1 is checked once per instance. Outside it,
  allocators without a clean condition can still plug in.
- **Q2. The mid-sweep colour of a promoted copy** (§1.3, §4.2): a per-object
  colour in `tal`, or a minor-collection record per instance (§22.5's
  `minor_event`)? The record is the smaller change and lets first-fit keep
  his promotion.
- **Q3. E3 and E5**: state them as new generic theorems (recommended), or
  leave them implicit in the account?
- **Q4. The STW link in E1**: state it against `collect_stw` (needs stage
  8 first), or against the set `D` of dead objects of `g0` (no
  dependency)? Recommended: against `D` in stage 6, then a one-line
  corollary against `collect_stw` in stage 8.
- **Q5. Where the sweep's progress lives**: in the allocator's state
  (§22.2, assumed here), or in the phase (main's `Sweeping c`)? This is
  akhil's question 1a of §22.7, still open.
- **Q6. The marking invariant as a premise**: today akhil's
  `MP.marking_inv` is a hypothesis of each marking event, even in
  `Carried`. Carrying it (making the run prove it from M and the mark
  steps) would leave M as the only premise. That is worth doing, but it
  is a stage of its own (about 3 days), not in the plan above.
