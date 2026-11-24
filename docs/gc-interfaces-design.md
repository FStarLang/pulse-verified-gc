# Plug-and-play verified GC components: interfaces and generic theorems

Sections 1–6 are design only. Section 7 is built: the top-level
specification in F* (`GC.Spec.Top.*`), and its validation. They are written against branch
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
7. The top-level specification, formalised (`GC.Spec.Top.*`)

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

---

## 7. The top-level specification, formalised (`GC.Spec.Top.*`)

Specification stage. The top-level theorem `gc_correct` is a **proposition**:
it is stated and type-checked, not proved. Everything else listed below is
proved, with no admit and no assume, rlimit at most 40, and checked
without `--retry` at Z3 seeds 0, 1 and 2. akhil's modules are untouched.

### 7.1 Modules

| Module | Content | Proof status |
|---|---|---|
| `GC.Spec.Top.Heap` | The heap model: words, blocks (header wosize/tag/colour), values (bytes, major/young pointers, infix headers), `resolve`, `fields`, `outside_ref`, `reachable` (major), `yreachable` and `minor_live` (young), `fill`, `well_formed` (the walk tiles the heap) | definitions, plus `fields_of_spec` |
| `GC.Spec.Top.Iface` | Shared types (`phase`, `result`, `size_t`), the colour rule, and the components with their contracts: allocator, sweep, mark, minor collection, barrier | definitions |
| `GC.Spec.Top.Run` | Collector = `comps`; events; the semantics `step`; `mutator_ok`; runs; the conclusions (0)–(6); `gc_correct`, `gc_correct_local` | definitions; `hyps_of_ok`, `gc_correct_local_implies` proved |
| `GC.Spec.Top.Toy` | Bump allocator `toy` and its sweep `tsweep` | `toy_allocator_ok`, `toy_nontrivial`, `toy_room_capacity`, `toy_sweep_ok` |
| `GC.Spec.Top.ToyMark` | Mark `tmark` (grey outside refs; scan lowest grey) and barrier `tbarrier` | `toy_mark_ok`, `toy_barrier_ok` |
| `GC.Spec.Top.ToyMinor` | Minor collection `tminor`: promotes through `toy.alloc`, then forwards | `toy_minor_ok` |
| `GC.Spec.Top.ToyComps` | The toy collector `tc`; `reach_within`, an unreachability rule (reachability stays inside any set that holds outside_refs and is closed under edges) | `toy_components_ok : components_ok tc` |
| `GC.Spec.Top.Broken` | Nine broken components | each proved rejected (§7.5) |
| `GC.Spec.Top.Vacuity` | One run per style | every hypothesis proved (§7.6) |

### 7.2 The model

The specification is stated over an **abstract heap**, not the byte-level
heap of `GC.Spec.Base`. In it:

- A block at `o` has its header at word `o` and its fields at
  `o+1 .. o+wz`.
- The blocks tile `[0, size)`. This is "the heap walk reaches heap_size".
- Allocation status is not in the heap. It is the allocator's
  `free : state -> heap -> addr -> bool`.
- A pointer to an infix object is the address of its infix header inside
  the closure. `resolve` maps it to the closure.
- The nursery has the same shape and its own address space.

An instance over the byte-level heap (pages, first-fit) needs an
abstraction function, read from the heap walk. That function is not built
(gap G17).

### 7.3 The specification

**Shared types.**
- `phase pr = Idle | Marking | Sweeping of pr`, where `pr` is the sweep's
  progress.
- `result = Ok of addr | NoRoom`.
- `size_t`: wosize at least 1.
- A Fill is a `list value`.
- `colour_at`: Marking gives black; `Sweeping p` gives black if
  `unswept p o`, otherwise white; Idle gives white.

**Allocator** `{ state; init; inv; free; room; alloc }`.
`allocator_ok a` is the conjunction of:

| Clause | Statement |
|---|---|
| `init_at` (0) | The initial heap of `n` words is well formed, satisfies `inv Idle`, and has nothing in use |
| `alloc_at` / `alloc_post` | Given `inv ph h st`, `well_formed h` and `tag <> 249`. **NoRoom**: nothing changed, and `room = false`. **Ok o**: `room = true`; `o` is a block with header `(sz, tag, colour_at ph o)`; o's words were free; exactly `o` comes into use; every other in-use block is unchanged; `well_formed h'`; `inv` holds after Fill with any values of length `sz` |
| `free_hd_at` | Allocation status is read from the headers only (G4) |
| `inv_frame_at` | Writes to fields of in-use blocks, and recolouring in-use blocks while marking, keep `inv` and `free` (G4) |
| `inv_start_at` | `inv Idle` implies `inv Marking` |
| `free_white_at` | Free blocks are white, the model's blue (G5) |

`nontrivial a`: on some initial heap, some request has room. Each
allocator adds its own capacity lemma. The toy's is `toy_room_capacity`:
room holds exactly when the tail has `sz + 1` words.

**Sweep** `{ start; step; done }`, over a `sweep_kind = { progress;
unswept }` that it shares with the allocator. `sweep_ok` is:

- **start**: given `inv Marking`, well formed and nothing grey, it moves
  `inv` to `Sweeping p`, frees nothing, and every in-use block is unswept
  (G6).
- **step**: when not done:
  - `unswept` only shrinks, and strictly (a finite measure);
  - in the region swept, white becomes free and black becomes white with
    its contents unchanged;
  - outside the region nothing changes;
  - nothing comes into use and nothing free leaves it;
  - the free words grow by exactly the words of the white blocks swept,
    and `freed_words` is their count, `sum size (swept_words …)`;
  - `inv` holds at the new progress.
- **done**: `inv Idle`, no in-use block is unswept (pending is empty), and
  every block is white (G7).

**Mark** `{ mstart; mslice }`. It is allocator-free; its state is the
colours. `mark_ok` is:

- **start**: from an all-white well-formed heap, it changes only colours,
  darkens every `outside_ref`, and establishes `tricolour h (reachable w) ∅`.
- **slice**: when something is grey, it keeps `tricolour` (given `closed`)
  and changes only colours. It strictly decreases the measure: the
  white-live, then grey-live, objects below `size`, ordered
  lexicographically (G9).

`tricolour h snap allocd` is the snapshot invariant:
- every non-white block is in `snap ∪ allocd`;
- every `allocd` block is black;
- every white `snap` object is reached from a grey object through white
  objects (`grey_reached`).

From it, `mark_done` (nothing grey) gives black = `snap ∪ allocd` exactly.
The barrier, allocation and minor collections keep `tricolour`. That is a
conclusion of the theorem (6), not a clause of the mark.

**Minor collection** `{ collect }`, which returns `Done h st roots fwd` or
`OutOfRoom`. `minor_ok` says, under the allocator's invariant, a
well-formed heap, a well-formed nursery and `rem_covers` (every
old-to-young pointer is a remembered slot):

- **Done**:
  - `fwd` is defined on exactly the young blocks that are `minor_live`
    (reachable from the roots and the remembered slots), and is injective;
  - each copy lies on words that were free, has header
    `(wz, tag, colour_at)`, and holds the forwarded young fields;
  - in-use becomes old in-use plus the copies;
  - every old in-use block keeps its header, and its fields are equal up
    to `fwdv` (no-scan fields are not forwarded);
  - the roots are forwarded;
  - `inv` and `well_formed` hold.
- **OutOfRoom**: `oor_justified`. Some order of live young objects makes
  `A.alloc` refuse one (G3).

**Barrier** `{ bwrite; binit }`. `barrier_ok`:

- **write**: stores the value; blocks and other words are unchanged.
  While marking, the overwritten target goes from white to grey and no
  other colour changes; otherwise nothing is recoloured (G12). `rem` only
  grows, and an old-to-young store is remembered.
- **init** (Fill of a new major block): `fill`, with every young pointer
  of the Fill remembered (G10).

**Mutator** (trusted, `mutator_ok`):
- Every pointer value stored, used as a root, or put in a Fill resolves to
  an object **reachable now**: a major object in `reachable`, or a young
  one in `yreachable` (G1).
- Write targets are reachable blocks, with the field in range and not an
  infix header (G11).
- No infix header is stored, except a closure's own infix headers in its
  Fill.
- No-scan fields hold any bytes.
- Weak references, ephemerons, finalisers and `Obj.truncate` are not
  events of the model. There is one mutator thread: a run is one
  sequence.

**Runs.** A configuration holds:
- the world (major heap, nursery, roots, remembered set);
- the phase and the allocator's state;
- ghost bookkeeping kept by the semantics: `hs` (the heap at the cycle's
  start), `snap = reachable(s)`, `allocd` (allocated, or promoted, since
  `s`);
- `stopped`, set by OutOfRoom.

The events are:
- `EAlloc` (Alloc;Fill, atomic: the new object is pushed as a root, the
  register);
- `EYoungAlloc`, `EWrite`, `ERoots`, `EMinor`;
- `EStart`, `ESlice`, `EHandover`, `ESweep`, `EEnd`.

`enabled` makes:
- `ESlice` possible only when something is grey (G8);
- `EHandover` possible only at mark_done;
- `ESweep` possible only when not done, and `EEnd` only when done.

`Sequential` style forbids mutator events while a cycle runs.

**The theorem** (`conclusions`), for every run:

| | Clause | Where |
|---|---|---|
| (0) | Nothing is in use initially; the partition and `inv Idle` hold at 0 | `conclusions`, `concl_point` |
| (1a) | Every kept object (in use, and in `snap ∪ allocd`, or all of in use while idle) stays in use; its contents change only by the program's write to it, and up to `fwd` at a minor collection | `concl_step`, `contents_step` |
| (1b) | `reachable ⊆ kept`; no held pointer dangles; the heap and nursery are well formed; `inv` holds at every point | `concl_point` |
| (2) | `EAlloc` succeeds iff `room`; on success: a new block in use with header `(sz, tag, colour_at)` and fields `vs`, and nothing else comes into use; on failure: nothing changes | `alloc_step` |
| (3a) | At the end of cycle k, the words of every object in use at `s` and not in `snap_k` are free, or covered by an object of `allocd_k` | `concl_cycle` |
| (3b) | The survivors are exactly `snap_k ∪ allocd_k` | `concl_cycle` |
| (3c) | An object unreachable at any point of cycle k is not in use at some later point, by the end of cycle k+1 | `concl_two_cycles` |
| (3d) | A minor collection promotes only `minor_live` young objects (G2) | `concl_step` |
| (4) | The set freed in cycle k is `in_use(h_s) \ reachable(s)`, which is what a stop-the-world collection at `s` frees | `concl_cycle`, `stw_freed` |
| (5) | The partition (kept / pending / free, exactly one per word) holds at every point; words move from in use to free only by `ESweep`, and from free to in use only by `EAlloc` or `EMinor` | `partition`, `concl_step` |
| (6) | While marking, a slice strictly decreases the mark measure, and no other event increases it. While sweeping, a step strictly shrinks the unswept set, and no other event changes the progress. With `enabled` this gives: if slices keep being scheduled, the cycle completes, and it ends in `inv Idle` | `concl_step` |

`gc_correct c sty` is `components_ok c ==> forall runs. run_ok ==> conclusions`.
`components_ok` is `allocator_ok ∧ nontrivial ∧ sweep_ok ∧ mark_ok ∧
minor_ok ∧ barrier_ok`.

`gc_correct_local` needs the contracts only at the steps the run takes
(`run_hyps`). It is the stronger statement:
`gc_correct_local_implies : gc_correct_local c sty ==> gc_correct c sty`
is proved.

### 7.4 Satisfiable

**The toy instance.** Every contract is proved for a toy component, for
all inputs, not only on a run:

- **Allocator** (`toy`): bump allocation from a free tail; the sweep frees
  blocks by marking them dead.
  - `toy_allocator_ok`, `toy_nontrivial`, `toy_room_capacity`.
- **Sweep** (`tsweep`): progress `(p, e)` with `e` the cursor at the
  hand-over.
  - Objects allocated mid-sweep lie at or above `e`. So they are swept
    memory, and white.
  - `toy_sweep_ok`.
- **Mark** (`tmark`): `toy_mark_ok`. This is the full snapshot argument for
  the start and every slice.
- **Minor** (`tminor`): live set chosen classically, promotion through
  `toy.alloc`, then forwarding of every in-use pointer field. `toy_minor_ok`
  includes the OutOfRoom justification.
- **Barrier** (`tbarrier`): `toy_barrier_ok`.

**Pages and first-fit.** The table below records, per clause, the existing
lemmas that discharge it, or the nearest statement and what differs. All
are read-only; the names were checked with grep.

These gaps apply to many rows of both tables. The "close" notes in the
rows assume them.

- **Free is blue, not white.** Both allocators mark a free block **blue**.
  `free_white_at` reads the model's white as blue.
- **Unswept white blocks already count as free.** Both sweeps use a free
  predicate that includes them: pages `MidSweep.free_sw` (:68), first-fit
  `SweepPhase.Intrinsic.free_incremental` (:161). So their step lemmas say
  "the in-use set is unchanged", and this specification says "a step
  frees". This is gap G16, the largest.
- **No tag and no `room` in the old interface.** v2 (`AllocIface.alloc_post_with`)
  is stated per object (`~(live g x)`), not in words, and the tag is
  proved outside it.

**Pages** (`GC.Spec.Pages.*`):

| Clause | Existing lemma(s) | Status |
|---|---|---|
| `init_at` | `Allocator.init_inv` (:187), `Alloc.init_alloc_pre` (:408), `Init.init_pages_ok` (:296), `Init.init_all_blue` (:217) | close: "nothing in use" only through all-blue |
| NoRoom: nothing changed | `pages_allocator_ok` (Allocator.fsti:102), `alloc_post_with`'s `obj == 0` | exact |
| NoRoom: room false | `Allocator.alloc_no_fit` (fsti:114) to `Th.no_fit` | close: needs `wz+1 < pow2 54` |
| Ok: room true | only `RoomAfter.room_after` (one case) | **missing** |
| header (wz, tag, colour_at) | `pages_allocator_ok`, `alloc_post_new_old` (fsti:107); tag: `AllocTagOk.alloc_tag_marking` (:422), `alloc_tag_sweeping` (:469), `AllocTag.alloc_col_tag_wz` (:125) | exact, split across modules |
| o's words were free | `alloc_post_with` (`~live`); `Replace.replace_ok`/`replaces` (:418/:121) | close: per header, not per word |
| only o comes into use | `NewOnly.alloc_new_only` (:354, Idle), `MidSweepAlloc.use_eq` (:367), `AllocTagOk.r_in_use` (:96) | close: one lemma per phase |
| others unchanged | `others_unchanged` (AllocIface:81), `Th.alloc_ok` (:247) | exact |
| well formed after | `Replace.replace_ok`, `TailWalk.shape_walk_end` (:70) | close: walk end at Marking missing |
| inv after Fill | `alloc_post_with` (`fields_written_with`), `pages_allocator_sw_ok` (MidSweepAlloc:609) | exact (storable values) |
| `free_hd` | `MidSweep.free_sw_ok` (:71) | close |
| `inv_frame` | `phase_ok` (AllocIface:232); `Cycle.Write.write_idle` (:128), `write_mark_inv` (:185), `write_sw` (:288); `AllocTagOk.mark_inv_update` (:604), `sw_update` (:622) | close: per write, not relational |
| `inv_start` | `phase_ok` clause 1 (AllocIface:231) | exact |
| `free_white` | blue by construction | **missing** as a lemma |
| nontrivial / capacity | `Alloc.init_alloc_succeeds` (:436), `init_alloc_large_succeeds` (:447); capacity is the contrapositive of `alloc_no_fit` | close |
| sweep start | `StartSweep.start_ready` (:202), `SweepingStart.sweeping_at_start` (:101), `MidSweepStep.sw_start` (:586) | close: "frees nothing" false under `free_sw` (G16) |
| step: progress | `Allocator.sweep_step_inv` (fsti:172), `MidSweepStep.step_sw` (:450) | exact |
| step: white freed, black whitened | `SweepUnits.unit_ok` (:44), `Survive.black_survives` (:95), `dead_covered` (:266) | close: per unit, or at the end |
| step: outside unchanged | `step_sw` `use_kept` (:248), `Cycle.Sweep.step_acct` (:202) | close (`free_sw` form) |
| step: free words exactly, `freed_words` | `SweepPage.dead_count` (:123) counts slots only | **missing** |
| step: inv kept | `step_sw`, `Cycle.Sweep.step_acct` | exact |
| done | `MidSweepStep.sw_end` (:484), `Allocator.sweep_end` (fsti:181), `sweep_all_correct` (:189) | close: "all white" not stated |
| minor: promoted set | `Pages.Promote.collect` (:202) over `GC.Gen.CheneyBFS.cheney_promotes_all_reachable` | close: ⊇ only, not in the remembered-set form |
| minor: copies' colour | `Promote.Collect.collect_blocks` (:399), `Promote.Mark.m_new_black` (:113) | exact per `tal` |
| minor: others, inv | `Promote.Collect.collect_inv` (:362), `PromoteInst.mark_contract` (:69), `sw_contract` (:148), `Promote.Idle.idle_contract` (:167) | exact per phase |
| minor: OutOfRoom justified | — | **missing** |
| barrier: SATB | `Cycle.Write.barrier_mark_inv` (:245), `Cycle.State.darken_mark_inv` (:112) | exact |

**First-fit** (akhil's modules, read-only):

| Clause | Existing lemma(s) | Status |
|---|---|---|
| `init_at` | only the definition `Allocator.init_heap_spec` (fsti:295) | **missing** |
| NoRoom: nothing changed | `MarkPhase.Alloc.marking_alloc` (fsti:132), `SweepPhase.Mutator.alloc_sweep_phase` (:111) | exact |
| NoRoom: room false | `Allocator.Oom.alloc_spec_oom_no_fit` (:136), `sweep_inv_incremental_oom_no_fit` (:197), `fused_oom_no_fit` (:169) | exact |
| Ok: room true | `Allocator.Phase.alloc_at_obj_valid` (:174), `Exact.reachable_valid_cell` (:117) | close: derivable from `alloc_carved` |
| header | `Allocator.Phase.alloc_at_recoloured` (:152), `alloc_at_obj_wosize` (:208), `Mutator.alloc_phase_new_block` (:81) | exact |
| o's words were free | `Mutator.alloc_carved` / `carved_from` (:133) | exact while sweeping; other phases through `alloc_at_recoloured` |
| only o comes into use | `Mutator.alloc_in_use` (:239), `MarkPhase.Alloc.alloc_in_use` (:121) | exact |
| others unchanged | `Mutator.alloc_keeps` (:227), `Allocator.Phase.alloc_at_preserves_objects` (:181) | exact |
| well formed after | `Mutator.alloc_walk_end` (:257), `GC.Gen.MarkPhase.Walk.alloc_reaches` (:40) | exact |
| inv after Fill | `Mutator.fresh_write`/`fresh_close` (:181/:199), `MarkPhase.Alloc.marking_fresh_write`/`_close` | close: storable values only |
| `free_hd` | `SweepPhase.Intrinsic.free_incremental_ok` (:165) | close |
| `inv_frame` | `Mutator.write_sweep_phase` (:217), `MarkPhase.Mutator.marking_write` (:173), `Allocator.Phase.recoloured_*`, `GC.Gen.Barrier.modify_phase_shape` (:91) | close: storable values |
| `inv_start` | `GC.Gen.MarkPhase.Start.mark_start_shape` (:42) | close: after the roots are darkened |
| `free_white` | blue by definition | **missing** as a lemma |
| capacity | `Allocator.Exact.alloc_spec_fits_succeeds` (:824), `alloc_succeeds_when_a_block_fits` (:1053) | exact at Idle; other phases missing |
| sweep start | `Intrinsic.sweep_inv_incremental_start` (:475), `MarkPhase.marking_done_sweep_start` (:287), `Completeness.phase_account_start` (:409) | close (G16) |
| step: progress | `SweepPhase.Slice.sweep_slice_phase` (:89), `GC.Gen.Incremental.phase_slice_finishes` (:190) | close: strict only with a positive budget |
| step: black whitened | `Intrinsic.marked_survive`, `sweep_inv_stw` (:298/:312), `behind_swept` (:175) | close: stop-the-world relation |
| step: outside unchanged | `sweep_slice_phase` | close (G16) |
| step: free words exactly, `freed_words` | `Slice.swept_words` (:39) counts words visited | **missing** |
| step: inv kept | `sweep_slice_phase`, `Completeness.phase_account_slice` (:415), `GC.Gen.Incremental.phase_slice_shape` (:183) | exact |
| done | `Intrinsic.End.sweep_inv_incremental_end` (:34), `GC.Gen.Incremental.sweep_end_shape` (:115), `Completeness.freed_by_end` (:332) | exact (white or blue) |
| mark start | `GC.Gen.MarkPhase.Start.mark_start_shape` (:42), `darkened_roots_dark` (:50), `MarkPhase.Completeness.account_start` (:156) | exact |
| slice keeps inv, colours only | `MarkPhase.Slice.mark_steps_inv` (:176), `mark_steps_darker` (:213), `Completeness.account_steps` (:190) | exact |
| slice decreases the measure | `MarkPhase.Slice.mark_weight` (:228), `GC.Gen.MarkSlice.slice_measure_lt` (:234) | close: weight over all blocks, not live ones |
| done: black = snap ∪ allocd | `Completeness.account_marked` (:292), `cycle_complete` (:347); ⊇ via `GC.Gen.MarkPhase.Safety` | close |
| minor: promoted set | `GC.Gen.CheneyBFS.cheney_promotes_all_reachable` (:415), `MinorCollectForwarding.Edges.combined_reachable_minor_has_fwd` (:64) | close: ⊇ only |
| minor: copies' colour | `GC.Gen.MarkPhase.Minor.minor_new_block_black` (:140), `GC.Gen.Promote.promote_object_recoloured` (:164) | close: mid-sweep colour depends on position |
| minor: others, inv | `MarkPhase.Minor.minor_keeps_block` (:123), `minor_keeps_marking_inv_with` (:101), `Incremental.minor_keeps_phase_shape` (:198) | exact per phase |
| minor: OutOfRoom | `GC.Gen.Promote.promote_object_oom` (:134) | close |
| barrier: SATB | `MarkPhase.Mutator.marking_write_barrier` (:206) | exact (storable values) |
| barrier: remembered set | `GC.Gen.Barrier.write_ref_table` (:139), `modify_ref_table` (:153), `initialize_ref_table` (:176) | exact |

**Missing in both:**
- `freed_words`, and "the free words grow exactly";
- `free_white` as a lemma;
- the minor's "promoted ⊆ `minor_live`" in this form;
- "o's words were free", per word.

### 7.5 Strong enough: broken components

Each is proved to violate the specification (`GC.Spec.Top.Broken`), on a
concrete heap:

| Broken component | Rejected by | Lemma |
|---|---|---|
| Allocator handing out a block in use | `alloc_ok` (o's words were free) | `bad_inuse_rejected` |
| Allocator whose room is always false | `nontrivial` only: it **meets** `allocator_ok` (`bad_noroom_meets_allocator_ok`), so without `nontrivial` it would be accepted | `bad_noroom_rejected` |
| Sweep freeing a black object | `sweep_ok` (black stays in use) | `bad_black_rejected` |
| Sweep re-sweeping swept memory (frees the white survivors behind it) | `sweep_ok` (outside the region unchanged) | `bad_resweep_rejected` |
| Mutator setting a root to a garbage object | `mutator_ok` (`value_ok`: not reachable). The prompt's snapshot reading **accepts** it (`bad_root_accepted_by_snapshot_reading`, the garbage object being in the snapshot): gap G1 | `bad_root_rejected` |
| Minor collection skipping the remembered slots | `minor_ok` (exactly the live young objects) | `bad_norem_rejected` |
| Mark not greying old objects held only by young objects | `mark_ok` (outside_refs darkened) | `bad_roots_only_rejected` |
| Minor collection always reporting OutOfRoom | `minor_ok` (`oor_justified`): accepted by the prompt's "OutOfRoom: the run stops", gap G3 | `bad_oor_rejected` |
| Barrier not remembering a Fill's young pointers | `barrier_ok` (`binit`): gap G10 | `bad_init_rejected` |

### 7.6 Non-vacuity

`GC.Spec.Top.Vacuity` proves two concrete runs of the toy collector (heap of
12 words, nursery of 4), one per style. For each run it proves every
hypothesis of `gc_correct` and of `gc_correct_local`:

- `vacuity_sequential`: `components_ok tc ∧ run_ok tc Sequential … ∧ run_hyps …`.
- `vacuity_incremental`: the same for `Incremental`.

The two runs:
- **Shared prefix.**
  - A (root), B (A.0 = B) and C are allocated.
  - Young Y is allocated (Y.0 = A, then Y.0 = B).
  - The roots are cut to {A}.
- **Sequential.** A full cycle:
  - start;
  - two slices;
  - hand-over;
  - three sweep steps, in which C is freed;
  - end.

  Then a minor collection.
- **Incremental.** The same, with mutator events interleaved:
  - while marking: an allocation (D, black), and an overwrite of A.0 that
    goes through the barrier;
  - while sweeping: an allocation (E, white, at or above the hand-over
    cursor), a write, and a root change.

Each event's obligations (enabled, style, `mutator_ok`) are checked on the
concrete configurations with `assert_nbe`, which is normalisation by
evaluation. Plain `assert_norm` re-evaluates the heap closures once per use,
which is exponential in the number of mark slices (37 s for the hand-over,
then worse). Reachability witnesses are built as terms (`RBase`, `YRoot`).
The step contracts follow from `toy_components_ok` (`hyps_of_ok`).

The non-triviality lemmas are:
- `every_event_occurs`: all ten events occur in each run.
- `incremental_interleaves`: the mutator events of the incremental run
  happen during marking and during sweeping.
- `c_unreachable_at_start`: at the cycle's start there is a root; A and B
  are reachable (B only through a field and the young object); C is in use
  and unreachable.

**Pages.** No run, because there is no abstraction function from the
byte-level heap (G17). The existing page witnesses (`Cycle.CarriedVacuity`,
`MinorVacuity{,2}`, `IncrVacuity`) are runs of the byte-level cycle, not of
this specification.

### 7.7 Gaps found, and how the specification was changed

| | Gap in the specification as first written | Found by | Fix |
|---|---|---|---|
| G1 | `mutator_ok` allowed values in `snapshot_k ∪ allocated_k`. A program could then resurrect an object that was dropped during cycle k: it is unreachable at some point, but reachable at `s_{k+1}`, so (3c) is false. In Idle the clause was undefined (no snapshot). | broken mutator (5): the snapshot reading accepts it | Values, roots and targets must be **reachable now** (`value_ok`). This is what OCaml's type safety gives: a program holds no pointer to an unreachable object. |
| G2 | (3d) "never promotes an unreachable young object" is false for any remembered-set minor collection. A stale slot of a garbage major object keeps its young target alive. | writing (3d) against `minor_ok` | (3d) states: promotes only `minor_live` objects (reachable from roots ∪ remembered slots). Exact reachability would need the remembered set restricted to live objects, which no OCaml runtime does. |
| G3 | "OutOfRoom: the run stops" accepts a minor collection that always gives up | broken minor (8) | `oor_justified`: some order of live young objects makes `A.alloc` refuse one |
| G4 | `alloc_post` gives `inv` after the Fill, but nothing kept `inv` (or the in-use set) across the program's writes, the mark's recolouring or the minor collection's pointer rewrites | checking (1b)/(5) by hand | `inv_frame_at`, `inv_start_at`, `free_hd_at` |
| G5 | The mark is allocator-free. If a free block could be grey or black, `mark_done` would not give black = `snap ∪ allocd` | checking the mark's exactness | `free_white_at` (pages and first-fit: blue) |
| G6 | `sweep start` did not require every in-use object to be unswept. A pending object in "already swept" memory would never be freed, so (3a)/(3b) fail | checking (3b) | Clause added to `sweep_start_at` |
| G7 | `done ⇒ pending empty` does not give an all-white heap, which the next `mark_start` needs | checking cycle k+1 | `sweep_done_at` adds: every block white |
| G8 | A slice when nothing is grey, and a sweep step when done, were unconstrained | writing `enabled` | Only enabled when not done |
| G9 | "Each slice decreases a measure": a component-chosen measure says nothing if other events may increase it | writing (6) | Spec-defined measure (white-live, then grey-live, sets); (6) says no other event increases it |
| G10 | `barrier_ok` named only writes. The Fill of a new major object with young pointers (OCaml's `caml_initialize`) must also be remembered, or `rem_covers` fails at the next minor collection | broken barrier (9) | `binit` clause |
| G11 | `mutator_ok` did not stop a write over a closure's infix header, or the storing of one; either breaks `resolve` | writing `value_ok` | Excluded |
| G12 | "the overwritten value is darkened": blackening without scanning breaks the snapshot invariant | proving the toy mark | `darkened`: exactly white → grey |
| G13 | `alloc_ok`'s precondition "the partition" cannot be stated by the allocator, which does not see the snapshot | writing `alloc_at` | Dropped. The allocator's view of the partition (in use / free) is total by definition. |
| G14 | The prompt's "(6) if slices keep being scheduled" is a liveness property of infinite runs | writing (6) | Stated as strict decrease of finite measures plus non-increase by other events, plus `enabled` |
| G15 | The minor collection must not forward no-scan fields (bytes) | writing `minor_post` | `fwd_field` |

**Residual gaps** (not fixed in this stage):

- **G16 (partly fixed in §8.3; word level in §9.6). Allocation status mid-sweep.** Pages' `free_sw` and first-fit's
  `free_incremental` count unswept white blocks as free. Their step lemmas
  then say "the in-use set is unchanged". This specification's `free` is
  allocation status: a sweep step frees, and `freed_words` counts. To
  instantiate it, `free` must be "blue" for both, with their step lemmas
  restated. `freed_words`, and "free words grow exactly", are missing in
  both (§7.4 tables).
- **G17 (partly fixed in §8.2; the representation and its faithfulness in §9). No abstraction function** from the byte-level heap to this
  model. So neither pages nor first-fit is an instance yet, and there is no
  pages run here. The tables of §7.4 are the per-clause plan for those
  instances.
- **G18 (fixed in §8.1). `nontrivial` is weak.** It is one initial request. An allocator
  whose room holds only on the initial heap passes it. Only the
  per-allocator capacity lemma, which is not a generic clause, rules it
  out. A generic form would need "free space of its kind", which is per
  allocator by design.
- **G19. The mark and minor contracts are proved only for the toy.**
  akhil's mark and `Pages.Promote` meet them only "close" (§7.4: the ⊇
  direction of the promoted set, the measure over all blocks rather than
  live ones). The toy minor chooses its live set classically; it is a
  specification of Cheney's result, not of its scan.
- **G20. The theorem is not proved.** Clauses (1a)–(6) were checked by
  hand against the contracts while writing them; that check found G1–G15.
  The proof is the next stage.

### 7.8 How to check

**Trust.**
- No admit and no assume.
- The toy minor and some proofs use ulib's classical choice,
  `FStar.IndefiniteDescription`: `strong_excluded_middle` and
  `indefinite_description_ghost`. These are ghost functions.
- `assert_nbe` trusts F*'s normaliser, as `assert_norm` does.

The modules depend only on ulib. Each was checked from an empty cache,
without `--retry`, at `--z3seed 0`, `1` and `2`:

```
fstar.exe --cache_checked_modules --cache_dir <empty> --z3version 5.3.0 --z3seed N \
  --include mark-and-sweep/spec mark-and-sweep/spec/GC.Spec.Top.<M>.fst
```

| Module | Seed 0 | Seed 1 | Seed 2 |
|---|---|---|---|
| Heap, Iface, Run | 8 s | 7 s | 7 s |
| Toy | 101 s | 123 s | 99 s |
| ToyMark | 6 s | 6 s | 5 s |
| ToyMinor | 39 s | 35 s | 39 s |
| ToyComps | 1 s | 1 s | 1 s |
| Broken | 11 s | 12 s | 12 s |
| Vacuity | 8 s | 8 s | 9 s |

`GC.Spec.Top.Vacuity` and `GC.Spec.Top.Broken` are in `ROOT_MODULES`, so
`gmake verify` checks all nine. That is the only change outside the new
modules and this document.

---

## 8. G18, and the bridge to the byte-level heap (G17, G16): stage 2a

Specification work again: `gc_correct` is still not proved. The rules are
the same as in §7: no admit, no assume, rlimit at most 40, no `--retry`,
seeds 0–2 from empty caches. akhil's and the page modules are read-only.
Nothing is committed.

### 8.1 G18: non-triviality over every reachable state

**The change.**
- **A capacity condition per collector.** A collector `comps` now carries
  `fits : capacity k a.state`: the allocator's "enough free space of its
  kind" for a request of `sz` fields.
  - It is part of the specification, fixed per allocator, not chosen by
    the component:
    - first-fit: a free-list block of at least `sz + 1` words;
    - pages: a swept page of the class with a free slot, or an empty page,
      or a run of empty pages;
    - the toy: the free tail.
  - If each component chose its own condition, an allocator could declare
    "the initial heap" as its condition and pass.
- **`nontrivial c = fits_init c.a c.fits ∧ room_complete c`**:
  - `fits_init`: the condition holds on some initial heap, so it is not
    vacuous;
  - `room_complete`: for every style, every run allowed by `run_ok`, and
    every state of that run (through every event: allocations, the
    program's writes and root changes, mark slices, minor collections,
    sweep steps), room holds whenever the condition does.
- **Where it sits.** `nontrivial c` is a conjunct of `components_ok`. It is
  no longer in `run_hyps`, because it is not a correctness hypothesis.

**Validation.**

| | Result | Lemma |
|---|---|---|
| Toy | meets it: `toy_fits` is "a free block at the cursor reaching the end of the heap, with at least `sz + 1` words", and room holds whenever it does | `toy_collector_nontrivial`, `toy_fits_room`, `toy_fits_init` |
| Allocator with room only on the initial heap (`bad_once`) | meets `allocator_ok` (`bad_once_meets_allocator_ok`); passes the old check, room on some initial heap (`bad_once_initial_room`); **rejected**: a one-allocation run reaches a state where the tail has room for one field and the allocator refuses | `bad_once_rejected` |
| Allocator with room always false (`bad_noroom`) | rejected at the initial state of the empty run | `bad_noroom_rejected` |

**Residual.** The capacity condition is per allocator, so its adequacy is
reviewed, not checked. A collector could still declare a narrow condition.
What is checked is that room never fails while the declared condition
holds, in any reachable state.

### 8.2 The model gains `Blue`; the abstraction function (G17, 2a)

**Blue in the model.** The byte heap marks free blocks blue, and pages and
first-fit read free status from the header. The model's colours are now
`White | Grey | Black | Blue`, and the abstraction keeps blue. Clauses that
said "white" for free blocks now say "not grey or black" (`dark`):

- `free_white_at`: a free block is not dark, and a blue block is free.
- `inv_frame_rel`: a colour change is to a dark colour, while marking, on a
  block in use.
- `tricolour`: every dark block is in the snapshot or allocated.
- `mark_start_at`:
  - requires: no dark block, and every reachable object is a white block;
  - ensures: outside_refs become dark.
- `sweep_done_at`: no block is dark.

The toy keeps white free blocks; its invariant adds "never blue". Every
earlier result is re-proved unchanged, including the vacuity runs and all
the broken components.

**`GC.Spec.Top.Abs`** (`abs : heap -> mheap`):

- **Words and blocks.**
  - Model word `m` is the byte word at `zero_addr + 8m`. The model has
    `(heap_size - zero_addr)/8` words.
  - A block starts at `m` exactly when the heap walk from `zero_addr` lands
    there and can step (`GC.Spec.Walk.reaches`, `can_step`). These are
    total, so the model's header function is total.
- **Headers.** The decoded header: wosize, tag, colour (blue kept).
- **Values.**
  - an `is_pointer` word becomes a major pointer to the model address of
    that object's header;
  - a word whose low byte is the infix tag becomes `VInfix (wosize)`, its
    offset in words from the closure, as in OCaml's `Infix_offset`;
  - any other word becomes bytes.

The lemmas, all proved:

| Lemma | Statement |
|---|---|
| `abs_is_block` | a model block at `m` ⇔ `obj_of m ∈ objects zero_addr g` |
| `abs_header` | the model's wosize, tag and colour are the object's `wosize_of_object`, `tag_of_object`, `color_of_object` |
| `abs_blue` | model blue ⇔ `is_blue` |
| `abs_field` | field `i` of the model block is the abstraction of the byte word `i` past the object |
| `abs_tiled` | if the walk reaches `heap_size`, the model is tiled (blocks in bounds, every word covered, no overlap) |
| `abs_well_formed` | tiled, plus `no_infix_block`, gives `well_formed` |

For pages, the walk reaches `heap_size` in every page state
(`TailWalk.shape_walk_end`, from `pages_ok_sw`).

### 8.3 The page sweep with "free" meaning blue (G16, 2a)

**`GC.Spec.Top.PagesFree`**:

- `free_true = free_stw`: blue.
- **`step_frees_white`**:
  - **requires:** `pages_ok_sw g st`, and page `p` heads an unswept pool
    page or large run.
  - **ensures:** after `SweepAll.step g st p`, a block is in use (not blue)
    exactly when it was in use and was not a white block of the step's unit
    `[page_base p, page_base (p + span))`. Nothing else changes status.
  - This is the restatement. The page modules' `step_sw` says "the in-use
    set is unchanged" because `free_sw` counts unswept white blocks as free.
- **`freed_words_of g pm p`**: the words, headers included, of the white
  in-use blocks of the unit before the step. `freed_words_counts`: those
  blocks are exactly the ones the step frees.
- **`abs_in_use`**: through the abstraction, a model block is in use
  exactly when it is not blue.

The unit's facts (`MidSweepStep.swept_unit`) were needed and are not
exported by `step_sw`; they are only asserted inside `pool_step_sw` and
`run_step_sw`. `pool_unit` and `run_unit` derive them again with the same
steps from the same exported lemmas. The page modules are not edited.

**Facts learned from the page sweep:**
- **A step re-lays out free space inside its unit.** A dead slot merges
  with its filler, an empty page becomes one blue block, and a run's dead
  stretches coalesce. Its free-list links overwrite the first field of free
  blocks.
  - The sweep contract allows this: it constrains blocks in use and free
    words, not the shape of free blocks.
  - A word-level "free words grow exactly" lemma has to go through the
    tiling of both heaps (both walks reach `heap_size`). It is not done.
    Only the block-level form, `step_frees_white`, is.
- **Unswept is page-level** (`G.uw`). For pages, the model's
  `unswept p o` is "the page of `o` is unswept", with the page map as the
  sweep's progress.

### 8.4 Open for 2b, with a decision needed

**The instance shape (decision).** The specification's components act on
model heaps. The page functions act on byte heaps, and `abs` is not
invertible: it drops the non-offset bits of infix headers. Two ways
forward:

- **(a) Recommended. Make the specification generic in the heap type.**
  - A collector carries its own heap type `H` and `abs : H -> mheap`.
  - Its components act on `H`, and the mutator's writes and Fill are
    functions on `H` that commute with `abs`.
  - The contracts are stated through `abs`.
  - The toy instance is `H = mheap`, `abs = id`. Pages is `H = heap`, with
    the page functions as they are.
  - Cost: a refactor of `Iface` and `Run` and the toy proofs (about one
    day). Then the pages clauses follow §7.4's table.
- **(b) Keep the model heap and prove a simulation.** Byte-level page runs
  abstract to model runs that meet the contracts. The components on the
  model would only be relations, so the instance is not a component
  record. That is heavier, and it does not give a reusable pages
  component.

**Also open for 2b:**
- The pointer and edge correspondence through `abs` (`resolve` against
  `resolve_object`, `major_edge` against `points_to`). It needs
  `interior_pointers_valid`.
- The abstraction of the nursery and young pointers.
- The word-level freed-words lemma.
- The clause-by-clause pages instance.
- A pages run.

### 8.5 Files and checks (stage 2a)

- **New modules:**
  - `mark-and-sweep/spec/GC.Spec.Top.Abs.fst`
  - `mark-and-sweep/spec/GC.Spec.Top.PagesFree.fst`
- **Changed modules:** `GC.Spec.Top.{Heap,Iface,Run,Toy,ToyMark,ToyComps,Broken,Vacuity}`.
- **Checks:** every module checked from fresh caches at seeds 0, 1 and 2
  without `--retry`. The byte-level dependencies' `.checked` files were
  copied from the repository's `_cache`.

| Module | Seed 0 | Seed 1 | Seed 2 |
|---|---|---|---|
| Heap, Iface, Run | 5 s | 4 s | 5 s |
| Toy | 118 s | 119 s | 105 s |
| ToyMark, ToyMinor | 40 s | 43 s | 44 s |
| ToyComps, Broken | 25 s | 24 s | 24 s |
| Vacuity | 8 s | 7 s | 10 s |
| Abs | 6 s | 7 s | 7 s |
| PagesFree | 21 s | 20 s | 21 s |

`GC.Spec.Top.PagesFree`, which pulls in `Abs`, is added to `ROOT_MODULES`.

## 9. Generic in the heap: representation relations and faithfulness (stage 2b, first part)

The decision of §8.4 was option (a), adjusted to follow McCreight, Shao,
Lin and Li, "A General Framework for Certifying Garbage Collectors and
Their Mutators" (PLDI 2007). Each collector brings its own heap type. Its
link to the model is a **representation relation**, not a function, and
every contract is lifted through that relation. This section covers the
refactor and the faithfulness conditions. It stops at the checkpoint before
the clause-by-clause pages proofs.

### 9.1 The shape

- **`GC.Spec.Top.Rep`.** A collector's heaps are a major heap type `t` and a
  nursery type `yt`. Their `rep t yt` holds:
  - `repr m h`: model heap `m` represents concrete heap `h`; likewise
    `yrepr` for the nursery;
  - the instance's own **reads**: `rsize`, `rhd h o` (the header at `o`, if a
    block starts there) and `read h o i` (field `i` of the block at `o`);
    the same for the nursery;
  - its sizes (`size_ok`, `ysize_ok`), the words a field can hold
    (`storable`), and the largest young object (`ymax`);
  - the program's nursery operations `yinit`, `yalloc`, `ywrite` and
    `yreset`.
- **Lifting** (`lifted`, `forall_repr`, `forall_repr2`, `some_repr`, and
  `forall_views` in `Iface`). Each contract is a named model contract (a
  precondition on the model heap, a guarantee relating it to the next one)
  wrapped in one of these:
  - a **precondition** holds of `h` when some model heap representing it
    satisfies it;
  - a **guarantee** holds when every model heap that represents the input
    and satisfies the precondition has a represented successor related to
    it by the guarantee;
  - where the model step is a function (the Fill, a store into the
    nursery), the guarantee is that its result represents the output:
    `r.repr (fill m o vs) h'`.
- **`GC.Spec.Top.Iface`.** The components act on `t` (and the minor
  collection and mark on `cworld t yt`).
  - The allocator's `free`, `inv` and `room` read the concrete heap.
  - `in_use a st h m o` takes the model heap that represents `h`.
- **`GC.Spec.Top.Run`.** A configuration holds the concrete heaps.
  - `views x w`: a model world represents it.
  - The conclusions read one of them, `vw x` (chosen classically), and
    `concl_point` says one exists. By faithfulness all of them agree on
    blocks, headers and fields (`repr_agree`), and reachability reads
    nothing else.
  - The mutator's obligations hold of `vw x`: a precondition holds when
    some represented state satisfies it.
  - `components_ok` adds `faithful c.r`. `gc_correct_local` assumes it.

### 9.2 Faithfulness

`faithful r = rich r /\ faithful_major r /\ faithful_young r`. The
specification fixes it; the instance does not choose it.

- **What is read is the model.** If `repr m h`, then `m` has an admissible
  size and the instance's reads of `h` are those of `m` (`reads_model`):
  - the same size;
  - the same header at every address (so the same blocks);
  - the same value in every field.

  So two model heaps that represent one concrete heap agree on blocks,
  headers and fields (`repr_agree`). A relation can hide only what the
  instance's reads never show.
- **Nothing missing.** Every `representable` model heap represents some
  concrete heap. Such a heap is well formed, of an admissible size, with
  every block having a field and every field storable.
- **The nursery.** The reads condition holds for the nursery too, and the
  program's operations are the model's, lifted:
  - `yinit` represents `empty_heap n`;
  - `ywrite` represents `set_field`;
  - `yreset` represents the empty nursery;
  - `yalloc` returns an address with room (`young_free`) and a nursery
    represented by `young_alloc`. It fails only when `sz > ymax` or no
    address has room.
- **`rich`.** The instance stores at least what OCaml puts in a field:
  - every odd word (immediates, and infix headers);
  - a pointer to every block of the major heap and of the nursery;
  - at least one size of each heap, and `ymax ≥ 1`.

**Rejected.** Each of these representation relations relates every heap to
the empty heap:
- `Broken.bad_rep_rejected`, on the toy's heaps;
- `ByteRep.bad_byte_rep_rejected`, on the byte heap.

Both fail "nothing missing": a well-formed heap with one block is
represented by no heap. Under such a relation every lifted contract would
be about a heap with no block, and so would say nothing.

### 9.3 Instances

**The toy (`GC.Spec.Top.ToyRep`, `GC.Spec.Top.IdRep`).**
- The relation is equality, and the reads are the model's.
- The nursery allocates at the first address with room (`yfind`, which
  the runs compute).
- `toy_rep_faithful`.
- `IdRep`: for an equality relation, each lifted form is the model
  contract at the heap itself: `lifted_id`, `forall_repr_id`,
  `forall_repr2_id`, `some_repr_id`, `forall_views_id`, `alloc_fold_id`.
  The toy components keep their proofs on model heaps and are lifted by
  these lemmas. The broken components are rejected through them.

**The byte heap (`GC.Spec.Top.{Word,Abs,Young,ByteRep}`): `byte_rep_faithful`.**

- **Words (`Word`).** A 64-bit word is read as follows:
  - a major pointer when `is_pointer`; its model address is that of the
    object's header;
  - a young pointer when it is an aligned nursery offset past a header.
    `GC.Gen.Base` reads such words the same way (`to_minor_offset`,
    `is_minor_addr`; `absv_young`, `young_is_minor`);
  - otherwise a word of bytes, kept whole.

  On the words it produces, the reading has an inverse (`absv_concv`).
  Headers decode and encode exactly (`abs_hdr_enc`).
- **The major heap (`Abs`).**
  - `brepr m g`: `m` agrees with the heap read by the walk from
    `zero_addr`. Bytes below `zero_addr`, and the body of a header word,
    are not described.
  - Blocks are `objects zero_addr g` (`abs_is_block`).
  - Headers are `wosize_of_object`, `tag_of_object` and `color_of_object`
    (`abs_header`), and blue is `is_blue` (`abs_blue`).
  - Field `i` is the word at `obj + 8 i` (`abs_field`), and the reads are
    those of every represented heap (`brepr_reads`).
  - A model major pointer is exactly an `is_pointer` word (`absv_major`).
  - A pointer resolves the same way in both readings:
    `resolve_block_bytes` for a block, and `resolve_infix_bytes` for an
    infix header, which gives the same closure as
    `GC.Spec.Object.resolve_object`.
  - **Nothing missing.** `conc m` is the byte heap whose words are the
    model's (`Seq.init` over bytes), and `conc_repr` shows it represents
    `m`. The proof shows the walk lands exactly on the model's blocks
    (`rep_walk`, `rep_on_walk`).
- **The nursery (`Young`)** is GC.Gen.MinorHeap's `minor_state`.
  - A block starts where the walk from 0 to the bump pointer lands (`yat`).
  - `yrepr m ms`: that walk is well formed, and `m` agrees with the
    nursery's reading.
  - The operations:
    - `yinit` is `minor_init` of a zeroed nursery;
    - `yreset` is `minor_reset`;
    - `ywrite` is `minor_write_word` at the field;
    - `yalloc` bump-allocates a white header and the fields, for objects
      up to `max_young_wosize`.
  - Each operation is proved lifted (`yinit_ok'`, `ywrite_ok'`,
    `yalloc_free`, `yalloc_repr`, `yalloc_none`, `yreset_ok'`).
  - The walk's positions are exactly GC.Gen.MinorHeap's `minor_objects`,
    and the walk gives `minor_wf` (`young_objects`).
  - A young pointer resolves as `resolve_minor` does, through infix
    headers included (`young_resolve`).

### 9.4 Infix headers are words

Gap **G21** (fixed). The model had a value `VInfix k`, which was wrong in
two ways:
- the abstraction dropped the infix header's colour bits;
- reading a word by its bits misread OCaml integers whose low byte is 249
  (for example, the integer 124 is the word 249) as infix headers.

The fix: `value` is now `VInt | VPtr`, and an infix header is a word of
bytes (`VInt`). `resolve` reads a word as an infix header only when a
pointer points at it (`infix_hdr`), which is how OCaml reads it.
- `fill_ok` needs no closure clause.
- The write obligation is "not over a word that reads as an infix header".
- Nothing is dropped, so the byte reading is lossless on what it produces.

### 9.5 The mutator reads

`ERead p i` loads field `i` of the object `p` points to (major or young)
into a new root, through the instance's own `read` or `yread`.
- Obligation: the object is a block, reachable, and `i` is in range.
- Conclusion (`concl_step`): the value read is the model's field.
- Both vacuity runs contain a read (events 15 and 21), and
  `every_event_occurs` checks for it.

### 9.6 The word-level freed-words lemma

`PagesFree.step_frees_words`: `SweepAll.step` on an unswept pool page or
large run.
- Inside its unit, a byte is covered by a blue block after the step
  exactly when, before it, it was covered by a blue block (free) or a
  white block (freed).
- Outside the unit, the words are unchanged (`unit_step`).
- The proof uses, inside the unit:
  - the walk's covering and uniqueness (`cover_exists`, `cover_unique`);
  - every non-blue block after the step is a black block whitened in
    place;
  - every black block survives;
  - nothing is grey.

So the free words grow by exactly the words of the white blocks.
`freed_words_of` is the sum of the sizes of those blocks.

What remains for the instance (2b) is reindexing that sum. It must become
the model's `sum size (swept_words …)`, which is a sum over model
addresses rather than over the `objects` sequence.

### 9.7 Gaps found by the refactor

| | Gap | Fix |
|---|---|---|
| G21 | Infix headers as a separate value: lossy, and misreads integers (§9.4) | Infix headers are words |
| G22 | `EYoungAlloc o …` let the program choose the address. A bump nursery (OCaml's, GC.Gen.MinorHeap's) cannot place an object anywhere | The representation's `yalloc` chooses; it fails only without room |
| G23 | Contracts used model-heap equality (`h' == fill h o vs`, and the store fixing every word, header bodies included) | Functional steps: `repr (op m) h'`. The store fixes field words only |
| G24 | `init_at` for every size `n`; a byte heap has one size | `size_ok`/`ysize_ok`; `run_ok` requires them |
| G25 | The program could store any value, but a concrete heap holds words | `storable` in the mutator's obligations, with the `rich` lower bound |
| G26 | `oor_justified` folded `fill` on the model; with concrete heaps that is not a heap | `alloc_fold` goes through the relation (`some_model`, `some_heap`) |
| G27 | Nothing tied the model to the concrete heap a component returns | Every guarantee gives a represented successor; faithfulness ties the representation to the instance's reads |

**Residual.**
- GC.Gen.MinorHeap's `minor_alloc_spec` writes its header with
  `make_minor_header`, which its interface does not expose. `yalloc`
  writes the white header itself. That the two words are equal is not
  proved.
- The instance's reads are its own declaration. That they are the reads
  the verified implementation performs holds by construction for the byte
  heap (`read_word` at `obj + 8 i`; GC.Gen.MinorHeap's `minor_read_word`).
  It is not a theorem of the generic specification.

### 9.8 How this relates to McCreight et al. (PLDI 2007)

**Adopted:**
- **A representation relation** between the abstract state and each
  implementation's concrete state, which need not be a function (§9.1).
- **Abstract specifications of the operations.** The mutator's
  operations (allocate, read, write, root changes) and every collector
  component are specified on the abstract heap.
- **Lifting the contracts through the relation.** A precondition holds if
  some represented abstract state satisfies it. A guarantee holds if every
  represented abstract state has a represented successor related to it.
- **gcStep-style coercion.** A collector step (mark slice, sweep step,
  minor collection) may change the concrete heap freely. It is constrained
  only by a represented successor and the step's guarantee. The program
  sees the abstract state only (its reads are the model's).

**Beyond the paper's framework:**
- **Liveness.** The conclusions go past safety:
  - the partition of words (5);
  - what a cycle frees: exactly what a stop-the-world collection at its
    start frees (3a), (3b), (4);
  - anything unreachable during cycle k is freed by the end of cycle k+1
    (3c);
  - strictly decreasing measures for marking and sweeping (6);
  - non-triviality of allocation: room holds wherever the allocator's
    capacity condition does, in every state a run reaches.
- **A pluggable allocator.**
  - The allocator is a component with its own state and invariant.
  - Allocation status belongs to the allocator.
  - The sweep frees, and counts what it frees (`freed_words`).
  - The specification fixes a capacity condition per allocator.
- **Generational collection.** It has a nursery with its own
  representation and operations, a remembered set, and a write barrier
  (including the Fill of a new object). Promotion goes through the
  allocator, forwarding infix pointers, with `OutOfRoom` justified.
- **Incremental collection.** Snapshot-at-the-beginning marking with an
  allocation colour rule, and incremental sweeping. Allocation runs
  during both.
- **Faithfulness.** The paper takes the representation as given. Here
  every instance proves that its reads are the model's, that nothing
  representable is missing, and that its nursery operations are the
  model's. A degenerate relation is rejected (§9.2).

### 9.9 Files and checks

- **New modules** (`mark-and-sweep/spec/`): `GC.Spec.Top.Rep`, `IdRep`,
  `ToyRep`, `Word`, `Young`, `ByteRep`.
- **Rewritten:** `Abs` (the byte relation, reads, pointer correspondence,
  surjectivity).
- **Changed:** `Heap`, `Iface`, `Run`, `Toy`, `ToyMark`, `ToyMinor`,
  `ToyComps`, `Broken`, `Vacuity`, `PagesFree`.
- `ByteRep` is added to `ROOT_MODULES`.
- **Rules:** no admits and no `assume`; local rlimits ≤ 40.
- **Checks:** every module checked from a fresh cache (copied from the
  repository's `_cache`, without `GC.Spec.Top.*`) at seeds 0, 1 and 2,
  without `--retry`:

| Module | Seed 0 | Seed 1 | Seed 2 |
|---|---|---|---|
| Heap, Rep, Iface, Run, IdRep, ToyRep | 13 s | 13 s | 12 s |
| Toy | 87 s | 89 s | 88 s |
| ToyMark, ToyMinor, ToyComps | 40 s | 48 s | 39 s |
| Broken | 58 s | 56 s | 57 s |
| Vacuity | 11 s | 12 s | 11 s |
| Word, Abs | 24 s | 26 s | 23 s |
| Young | 49 s | 72 s | 54 s |
| ByteRep | 2 s | 2 s | 2 s |
| PagesFree | 22 s | 16 s | 22 s |

One seed-1 timeout, in `ToyMinor.ps_use` (a chain of equivalences made
heavier by the refactor), was found by these runs and fixed by stating the
links one by one.

## 10. The page allocator and sweep as an instance (stage 2b, second part)

The page allocator and page sweep of `GC.Spec.Pages.*` (incremental mode,
plan §28) are proved to meet every clause of the allocator and sweep
contracts, over the byte representation. The page modules are called
unchanged, and akhil's modules are not touched. Worktree `pgc-plug`, branch
`sheera/gc-plug`.

### 10.1 The components

- **Allocator** `PagesAlloc.pa`:
  - `alloc` is `AllocTag.alloc_tag` in the phase's colour, from the phase's
    page invariant `MidSweepAlloc.inv_sw`;
  - `free` is "blue", read from the header;
  - `room` is "`Alloc.alloc` succeeds";
  - the state is the page state plus the bytes below `zero_addr`;
  - the progress of the sweep is the page map and a cursor, and a model
    word is unswept when its page is (`Graft.uw`).
- **Bytes below `zero_addr`.** The representation does not read them, but
  the page invariants are stated on the whole heap. So the allocator keeps
  them in its state and runs on `set_low g lo` (`Top.Low`). The clauses
  that quantify over every represented heap (the invariant after the Fill,
  the frame) then need no byte-frame lemma for the page operations.
- **Sweep** `PagesSweep.psweep`:
  - `start` is `StartSweep.start_sweep`, with the cursor at 0;
  - a step sweeps the next unswept unit (pool page or large run) at or
    after the cursor, with `SweepAll.step`. This is `Incr.slice_from` with
    a budget of one unit;
  - `done` means every page is swept.

### 10.2 Clause by clause

| Clause | Proof | Page lemmas used |
|---|---|---|
| `init_at` | `PagesInst.init_ok` | `Alloc.init_alloc_pre`, `Init.init_all_blue`, `Cycle.State.ok_walk` |
| `free_hd_at` | `free_hd_ok` | (blue is read from the header) |
| `alloc_at`: room, header, colour | `PagesInst.alloc_m`, `PagesAllocOk.new_block`, `colour_ok` | `AllocTagOk.alloc_tag_marking`/`_sweeping`, `Promote.Idle.idle_sw`/`idle_is_sweeping`, `AllocTag.alloc_col_tag_wz` |
| o's words were free (per word) | `PagesAllocOk.words_free` | from tiling and `others_unchanged` |
| only o comes into use | `use_rel` | `NewOnly.new_only` (via `MidSweep.alloc_facts` mid-sweep), header rewrite at the same size |
| other blocks unchanged | `kept_block` | `others_unchanged` |
| well formed after | `wf_after` | the heap with the new fields cleared meets the invariant; `Fill.obj_same`, `Cycle.State.fill_back` |
| invariant after the Fill | `PagesAllocOk.fill_inv`, `PagesInst.fill_m` | `AllocTag.fields_written_away` of every phase |
| `inv_frame_at` | `PagesFrame.frame_ok` | `Cycle.Write.write_idle`/`write_mark_inv`/`write_sw`, `MarkPhase.mark_inv_recolour`, word by word |
| `inv_start_at`, `free_white_at` | `inv_start_ok`, `free_white_ok` | `AllocPhase.mc_of_ok` |
| sweep start | `PagesSweep.start_m` | `Allocator.start_ready`, `MidSweepStep.sw_start`/`start_unswept`, `Wf.wfh_old_parts_one`; tricolour from the model (`tri_of_dark`) |
| step: progress | `PagesStepOk.clause_progress` | `MidSweepStep.swept_unit` (`PagesFree.pool_unit`/`run_unit`) |
| step: white freed, black whitened, outside kept | `clause_blocks` | `PagesFree.step_frees_white`, `SweepUnits.unit_ok`, `MidSweepStep.unit_obj_out` |
| step: free words exactly | `clause_words` | `PagesFree.step_frees_words`, read in the model (`PagesStep.covered_iff`) |
| step: `freed_words` | `clause_freed` | `PagesFree.freed_words_of`, reindexed (`PagesFreed.freed_reindex`) |
| step: invariant, cursor | `clause_inv` | `MidSweepStep.step_sw`, `Incr.cursor_step` |
| sweep done | `PagesSweep.done_m` | `MidSweepStep.sw_end`, `Darken.idle_white` |
| capacity | `PagesFits.pfits_room`, `pfits_init` | `Allocator.alloc_no_fit`, `MidSweepAlloc.alloc_sw_ok` |

The results are `PagesFrame.pages_allocator_ok : allocator_ok byte_rep pa`,
`PagesStepOk.pages_sweep_ok : sweep_ok byte_rep psweep`, and
`PagesFits.pfits_room` / `pfits_init` (the two halves of `nontrivial` for
the allocator).

**The freed-words sum.** The page sweep counts freed words over the objects
of the walk, a sequence. The model counts them over addresses.
`PagesFreed.freed_reindex` proves the two are equal. The walk's objects are
distinct (`HeapModel.objects_is_vertex_set`), and each object is the block
at its model address. Summing over a distinct sequence equals summing an
indicator over addresses.

### 10.3 Gaps found, and how the specification was changed

| # | Gap | How it showed | Change |
|---|---|---|---|
| G28 | The frame relation and the Fill let the program store **any** value in a block in use. The pages invariant reads pointer fields (`no_pointer_to_blue`, `well_formed_heap`), so storing a pointer to a free block breaks it. `inv_frame` was false for pages. | `Cycle.Write` needs `program_write` (`storable` values) | `Iface.sound_value`: a stored major pointer resolves to a block the program may use (`live_target`). This is required in `inv_frame_rel` and for the Fill's values. The mutator's `value_ok` (reachable) implies it. |
| G29 | The program could write the fields of a closure. Pages forbids this (`program_write`: `~is_closure`). Infix headers live there. | `Cycle.Write` precondition | `Run.mutator_ok_w`: no write into a closure (OCaml closures are immutable). This replaces "the field written is not an infix header". `inv_frame_rel` asks the same. |
| G30 | Mid-sweep, the frame let the program write into a white block of an unswept page, which the sweep will free. Pages counts such a block as free (`free_sw`). | `Cycle.Write.write_sw` precondition | `live_target`: while sweeping, written blocks and pointer targets are not "white and unswept". `gc_correct` must show reachable objects are never such blocks. |
| G31 | The model's `resolve` accepted infix offsets `k = 1` and `k = wz`. The byte heap's `infix_addr_conds` rejects them: `k >= 2`, and the pointer is inside the closure. | pointer correspondence (`ByteFacts.ptr_resolve`) | `Heap.resolve`: `2 <= k < wz`. |
| G32 | The sweep's start assumed only "no grey block". The page sweep's mid-sweep invariant needs the mark's safety (`Mark.tri_color_invariant`: no black-to-white pointer). | `MidSweepStep.sw_start` precondition | `Iface.dark_closed` is added to `sweep_start_m`. It follows from tricolour plus closure at the end of marking. |
| G33 | The byte relation related many model heaps to one byte heap (`agree`), differing in words that are neither headers nor fields. Every lifted contract then had to be proved for each of them. | design of the run's components | `byte_rep` is now functional, model from concrete: `brepr m g = heq m (cabs g)`, with `cabs` the canonical reading, in which words outside fields read as 0. `Rep.representable` requires canonical heaps (`Rep.canonical`). The nursery is likewise (`Young.ycabs`). It is still a relation, and not invertible: the bytes below `zero_addr` are free. |
| G34 | The capacity condition is not vacuous only if there is a page. `n_pages` is a function of the abstract `heap_size`. | `pfits_init` | Stated under `n_pages > 0`, as the page modules' own witnesses assume their sizes (`big_enough`, `roomy`). |

### 10.4 Residuals

- **One unit per step.** A step sweeps one unit. Larger budgets (`Incr.slice_from` with `n > 1`) would need the clauses composed across units. That is not done.
- **The pages run is not built** (see 10.5).
- `gc_correct` is not proved (stage 3).

### 10.5 The pages run: what it needs

A run of `Run` needs a full `comps` record. For pages, the mark, the minor
collection and the barrier on the byte heap are not yet components.
Allocator and sweep are done. The run also needs every hypothesis at each
of its steps. What is missing:

- **Barrier on bytes.** A field write (plus darkening while marking, plus
  the remembered slot) and the Fill as byte writes, with
  `cabs (write g) = set_field (cabs g)` pointwise. Moderate.
- **Mark on bytes.** Recolour the headers to the colours the model mark
  chooses on the canonical reading. Its contract is then the toy's
  (`ToyMark`) moved through `heq`. The inductive predicates (`reach`,
  `wpath`) need transfer lemmas across pointwise-equal heaps.
  Alternatively: the page modules' own mark (`Pages.Cycle.Mark`), proved
  against the model tricolour. This is the user's choice.
- **Minor collection.** The page modules' promotion (`Pages.Promote.*`) as
  a component is a large instance of its own. The toy run collects with no
  young object reachable from roots or remembered slots. A minor collection
  that promotes nothing meets the contract at such a step, but that is a
  weak witness.
- **The run itself.** Page parameters and `heap_size` are abstract, so
  addresses and unit counts are not computable. Every event needs lemmas,
  under a size assumption like the page witnesses' `big_enough`. Because a
  step sweeps one unit, the number of `ESweep` events equals the number of
  units in use at hand-over. The run must fix it, for example by keeping
  every object in one pool page, which needs a class with enough slots: a
  further parameter assumption.

### 10.6 Files and checks

- **New modules** (`mark-and-sweep/spec/`): `GC.Spec.Top.Low`, `ByteFacts`,
  `PagesAlloc`, `PagesAllocOk`, `PagesInst`, `PagesFrame`, `PagesSweep`,
  `PagesStep`, `PagesFreed`, `PagesStepOk`, `PagesFits`.
- **Changed:** `Heap` (G31), `Rep` (`heq`, `canonical`, G33), `Abs` (`cabs`,
  functional `brepr`), `Young` (`ycabs`), `ByteRep` (canonical witness),
  `Iface` (G28, G30, G32), `Run` (G29), `Toy` (`tframe_gen`), `ToyMinor`,
  `Broken`, `Vacuity`.
- `PagesFrame`, `PagesStepOk` and `PagesFits` are added to `ROOT_MODULES`.
- **Rules:** no admits, no `assume`, local rlimits ≤ 40, akhil's modules
  untouched.
- **Checks:** fresh cache, seeds 0, 1 and 2, without `--retry`. See the
  table below.

| Module | Seed 0 | Seed 1 | Seed 2 |
|---|---|---|---|
| Heap | 2 s | 2 s | 2 s |
| Rep | 2 s | 2 s | 3 s |
| Word | 1 s | 2 s | 1 s |
| Abs | 23 s | 23 s | 23 s |
| Low | 3 s | 2 s | 2 s |
| ByteFacts | 8 s | 9 s | 9 s |
| Young | 50 s | 44 s | 55 s |
| ByteRep | 5 s | 5 s | 5 s |
| Iface | 2 s | 2 s | 2 s |
| IdRep | 1 s | 1 s | 1 s |
| ToyRep | 4 s | 5 s | 4 s |
| Toy | 93 s | 100 s | 87 s |
| ToyMark | 6 s | 6 s | 5 s |
| ToyMinor | 32 s | 35 s | 29 s |
| Run | 5 s | 5 s | 5 s |
| ToyComps | 2 s | 2 s | 2 s |
| Broken | 22 s | 22 s | 22 s |
| Vacuity | 12 s | 12 s | 11 s |
| PagesFree | 22 s | 22 s | 23 s |
| PagesAlloc | 4 s | 4 s | 3 s |
| PagesAllocOk | 32 s | 46 s | 70 s |
| PagesInst | 20 s | 24 s | 29 s |
| PagesFrame | 83 s | 79 s | 77 s |
| PagesSweep | 23 s | 24 s | 22 s |
| PagesStep | 34 s | 30 s | 29 s |
| PagesFreed | 3 s | 3 s | 3 s |
| PagesStepOk | 18 s | 16 s | 11 s |
| PagesFits | 2 s | 1 s | 2 s |

One seed-1 timeout (`PagesAllocOk.fill_written`) and one seed-2 timeout
(`PagesFreed.reindex`) were found by these runs and fixed by splitting the
steps; the table gives the times after the fix.

## 11. Stage 2b, part 3: the real components on the byte heap

The user's decisions (2026-11-22): the mark is akhil's incremental mark (the
one the pages-only cycle runs, `GC.Spec.Pages.Cycle.Mark`); the minor
collection is the generic promotion `GC.Spec.Pages.Promote` with its idle,
marking and sweeping instances; the barrier is akhil's write barrier.  None
depends on the allocator except the minor collection, which takes the
allocator's instance of the promotion.

### 11.1 The components

- **Barrier** (`GC.Spec.Top.ByteBarrier`, `byte_barrier_ok`): `bwrite` is
  `caml_modify` (akhil's `GB.modify_heap`): while marking the old value's
  target is darkened, then the word is written; the slot is remembered when
  the block is scannable and the value young.  `binit` writes the fields in
  order (`caml_initialize`).  `bwrite_marking_real`: wherever akhil's barrier
  runs (a body word of a scannable block in use, in a well-formed heap),
  `bwrite` is `GB.modify_heap`.  The proof reads the byte result as the toy
  barrier's model result (`GC.Spec.Top.ByteWrite`: a field write is
  `set_field`, a recolouring is `set_col`).
- **Mark** (`GC.Spec.Top.ByteMark`, `byte_mark_ok`): the start is akhil's
  root darkening (`MStart.darkened`) of the major pointers the model
  resolves, in the roots and in the nursery's fields; a slice takes the
  lowest grey block and makes akhil's moves on it (`S.scan_field` for each
  field, then `makeBlack`).  `bslice_moves`: under the slice's
  precondition, a slice is `S.mark_steps` from no partly scanned object back
  to none.  The proofs read the byte results as the toy mark's
  (`ToyMark.tmslice_with`, now stated for any grey block, and `tmstart`).
- **Minor collection** (`GC.Spec.Top.PagesMinor`, `PagesMinorOk.pages_minor_ok`):
  `Promote.promote` with the page allocator's instance for the phase
  (`PagesReplay.ptal`: `idle_tal`, `mark_tal`, `sw_tal`), on the page heap
  `gl h st`, forwarding the young pointers the model resolves among the
  roots and the remembered slots (`PagesLive.roots_of`).  It reports
  `OutOfRoom` exactly when the promotion refused a live object
  (`PromoteRun.wit`); otherwise it returns akhil's pointer update of the
  promoted heap (`Promote.collect`), the page state, the roots forwarded,
  and the forwarding map read on the model: the lookup in the list of
  promotions (young block, copy) the queue records (the contract asks for a
  total map; one computed from the promotion's ghost map would be ghost).
  - `PromoteRun` (any allocator of `Promote.contract`): along the loop the
    queue lists each forwarded object once, the heap and state are the
    replay of the queue's promotions, every queued object is live, and either
    some live object was refused after the first `k` promotions (`wit`) or
    every root and every field scanned is covered (`promote_done`).
  - `YoungInfix`: akhil's `minor_infix_wf` and `minor_wf` follow from the
    nursery's representation and the model conditions of G38.
  - `PromoteCopy`: `copy_fields` is the model's Fill of the copy with the
    young block's fields.
  - `Canon`: two byte heaps with the same tiled reading and the same low
    bytes are equal, so the page allocator does the same on every byte heap
    representing a model heap (what the contract's `alloc_fold` needs).
  - `PagesReplay`, `PagesQueue`: each promotion is an allocation of the page
    allocator component (`palloc`) and a Fill; `ri_step`, `ri_queue` carry,
    by the allocator contract at each allocation, the page invariant, the
    blocks in use (the old ones and the copies), the old blocks kept, each
    copy's header, colour, fields and free words, and the soundness of the
    nursery's major pointers.
  - `PagesOor`: a refused promotion after `k` queued ones makes the
    contract's `alloc_fold` over those young blocks and the refused one end
    in `None`: each byte heap `alloc_fold` picks has the replay's page heap
    (`Canon.same_gl`).  `PagesMinor.oor_ok` justifies `OutOfRoom`.
  - `PagesLive`: the roots are justified and liveness is closed under the
    fields the scan reads; `YoungInfix.young_resolve_back`: an address the
    bytes resolve to an object is one the model resolves.
  - `PromoteUpdate`, `PagesRw`: akhil's pointer update keeps blocks and
    headers and rewrites a field word exactly in a scannable block in use;
    the rewrite is the model's `fwdv` of the value when its young pointer
    was covered (`rw_ok`).
  - `PagesDone`, `PagesDone2`, `PagesMinorOk`: the `Done` post, clause by
    clause: the forwarding map is exactly the live young blocks, each once
    (completeness by induction on the model's tracing, from the closure of
    the promotion); the copies' headers, colours, free words and forwarded
    fields; the blocks in use; the old blocks' headers and, for those the
    program may use, forwarded fields (their young pointers are remembered
    slots, so roots); the roots; the page invariant after the update
    (`collect_inv`, read back from the instance); a well-formed reading.
- **The collector** (`GC.Spec.Top.PagesComps`): the record `pc` and
  `pages_components_ok : components_ok pc`, when there is a page
  (`n_pages > 0`, G34).

### 11.2 Gaps

- **G35 (barrier, darkening).** The contract's `darkened` is exact: only the
  model's `old_target` may turn grey.  akhil's `MM.darken` darkens through
  any word that looks like an infix header, which the model need not
  resolve (an int field with tag 249, a pointer into the middle of a block).
  The byte barrier darkens the block the model resolves the old value to;
  on akhil's heaps (his `modify_ok`) that is `MM.darken`'s target
  (`bwrite_marking_real`).
- **G36 (minor, young pointers into the major heap).** A promoted copy is a
  Fill of the allocator, whose invariant reads pointer fields (pages:
  `no_pointer_to_blue`).  `minor_pre` said nothing of the nursery's major
  pointers; it now requires them to be values the program may store
  (`young_sound`).  The promotion's own precondition is the same
  (`GenInv.minor_major_fields_not_free`).
- **G37 (minor, dead blocks).** `minor_post_done` asked every block in use
  to have its young pointers rewritten.  Mid-sweep the promotion (rightly)
  leaves the white blocks of unswept pages alone, which the sweep will free.
  The clause now asks it of the blocks the program may use
  (`live_target`); the other blocks in use keep their header.
- **G38 (minor, akhil's trust assumption on the nursery).** The promotion
  (like akhil's Cheney collection, and his pointer update, which it calls)
  assumes `minor_infix_wf`: every nursery word whose tag is the infix tag
  is the infix header of a closure.  Ordinary data breaks it: a field
  holding the OCaml int 124 is the word 249, which makes the next address
  look infix with offset 0; bytes past the bump pointer are not read by the
  model at all.  Two changes make it hold: (a) the nursery's representation
  records that the words past the bump pointer are zero (`Young.yok`; reset
  zeroes the nursery, allocation and writes stay below the bump pointer);
  (b) `minor_pre` requires that a young field reading as an infix header is
  one (`young_infix_ok`: in a closure, at its own offset, `2 <= k < wz`).
  (b) is akhil's assumption stated in the model; OCaml programs violate it,
  so the minor collection is proved only for nurseries without such words.
  Removing it needs a promotion and a pointer update that resolve only the
  addresses they follow.  **Decided (2026-11-22): removed, §12.**
- **G39 (minor, young pointers into major closures).** The promotion's
  precondition (akhil's `minor_major_fields_not_free`) takes each major
  pointer in a young field to be a block in use itself, not an interior
  pointer into a closure.  The model lets a young object point into a major
  closure (OCaml's mutually recursive closures do).  `young_sound` now also
  requires such pointers to be block starts.  Like G38(b), this is a
  restriction of the promotion, stated in the model.  **Decided
  (2026-11-22): removed, §12.**

### 11.3 Not done

- **The pages run** (both styles) is not built.  `pc` has every contract,
  so the run's hypotheses follow; what a run needs is the configurations
  themselves: with `heap_size` and the page parameters abstract, every
  allocation's address, every mark slice's grey block and every sweep
  step's unit is a symbolic computation through the page modules, about
  twenty events per style.
- **First-fit (2c)** is not started: its allocator and sweep as an instance
  over `byte_rep`, the minor collection with akhil's free-list allocator as
  a promotion allocator (`Promote.tal`, its `contract`), the same mark and
  barrier.
- G38(b) and G39: done in §12.

### 11.4 Checking

Every `GC.Spec.Top` module (47, in dependency order), each from a fresh
cache, without `--retry`, rlimits at most 40, no admits or assumes:

| Z3 seed | errors | warnings | total time | slowest module |
|---|---|---|---|---|
| 0 | 0 | 0 | 1313 s | `ByteMark`, 165 s |
| 1 | 0 | 0 | 1363 s | `ByteMark`, 142 s |
| 2 | 0 | 0 | 1374 s | `ByteMark`, 154 s |

### 11.5 Files

- **New** (`mark-and-sweep/spec/`): `GC.Spec.Top.ByteWrite`, `ByteBarrier`,
  `ByteMark`, `PromoteRun`, `YoungInfix`, `PromoteCopy`, `Canon`,
  `PagesReplay`, `PagesQueue`, `PagesOor`, `PagesLive`, `PagesMinor`,
  `PromoteUpdate`, `PagesFwd`, `PagesDone`, `PagesRw`, `PagesDone2`,
  `PagesMinorOk`, `PagesComps`.
- **Changed**: `Iface` (G36, G37, G38b, G39), `Young` (G38a), `ToyMark`
  (`tmslice_with_m`), `Broken` (the new preconditions on its witness),
  `PagesFrame` (`colorHeader_abs` moved to `ByteWrite`), `PagesSweep`
  (`resolve_cabs`, `field_to`, `field_model`, `target_model` moved to
  `ByteWrite`), `PagesStep` (opens `ByteWrite`), `Makefile`
  (`PagesComps` added to `ROOT_MODULES`).

## 12. Stage 2b, part 4: the promotion reads only what it follows

The user's decision (2026-11-22) on G38(b) and G39: replace akhil's two
assumptions on the nursery, in my promotion modules (akhil's read-only), by
conditions on what the collection follows; prove his imply mine; drop
`is_block` from `young_sound`; write the marking-phase lemma with the
nursery's references resolved; and witness both new cases.

### 12.1 What the collection reads

- It reads the word below an address only where it forwards that address:
  a root, or a value in a scanned field of a nursery object
  (`forward_one`).  An int is never aligned, so never forwarded; a major
  pointer is above the nursery, so never read as one of its addresses.
- It copies a major pointer, never follows it.  A copy is a Fill of the
  allocator, whose invariant asks of a field only what well-formedness
  does: the block it resolves to is in use, through a well-formed infix
  address (`I.field_ok_with`).

### 12.2 The conditions (`GC.Spec.Pages.Promote.Follow`)

- `infix_at ms a`: akhil's `minor_infix_wf` at one address.
- `follow_ok ms a`: if `a` reads as infix, `infix_at ms a`.
- `fields_follow ms`: every scanned field value of a nursery object is
  `follow_ok`; `roots_follow ms roots`: every root is.
- `major_targets un ms g`: every major pointer in a scanned nursery field
  resolves to a block in use for `un`, with a well-formed infix address.
- Bridges: `minor_infix_wf` gives `follow_ok` everywhere
  (`fields_of_infix_wf`, `roots_of_infix_wf`, `entries_of_infix_wf`);
  `minor_major_fields_not_free un` with well-formedness for `un` gives
  `major_targets un` (`targets_of_not_free`: a block in use is not infix,
  so resolves to itself).

### 12.3 The promotion

- `Loop`: `cpre_w a ms g0 st0 roots` and `ctx_w`, with the weak conditions.
  The loop keeps its own `finv`: the infix addresses it forwarded were
  followed safely (`entries_follow`, so the `entry` facts about an infix
  address need no global assumption), and its queue holds nursery objects.
  `copied_field_ok` shows a copied major pointer is `field_ok_with` and
  away from the new block through the block it resolves to
  (`old_target_wf`, `target_range`).  The loop lemmas take `follow_ok` of
  the address forwarded.
- `Collect`: `promoted_w`, `collect_inv_w`, `collect_blocks_w`,
  `collect_major_field_w`, `collect_target_w` from `cpre_w`; `new_src`,
  `promoted_wf_w`, `fwd_targets_w`, `infix_target_w` from the weak
  conditions.
- `Mark`: `mpre_mark_w` and the `_w` lemmas.  The marking invariant's
  lemma is one core, `m_keeps_marking_inv_core refs extra`, for any
  outside references `refs` holding the roots, `extra`, and what the
  nursery's major pointers resolve to (`nursery_in`).  Its instances:
  `m_keeps_marking_inv_r`, with `outside_refs_r` (the nursery's references
  resolved: an infix pointer into a major closure refers to the closure),
  and akhil's `m_keeps_marking_inv_with`, with his `outside_refs_of`
  (`nursery_in_raw`: under his condition a nursery major pointer is a
  block, so resolves to itself).
- `Idle`, `Sweep`: `ipre_w`/`i_facts_w`, `spre_w`/`s_facts_w`.
- Every earlier statement is kept with its signature, proved from the weak
  one through the bridges: `cpre`, `ctx`, `promote_step`,
  `forward_normal_keeps`, `forward_one_keeps`, `promote_linv`, `promoted`,
  `collect_*`, `infix_target`, `fwd_targets`, `promoted_wf`, `mpre_mark`,
  `m_*`, `i_facts`, `s_facts`.  The pages Pulse code and the cycle modules
  that use them (23 modules: `Promote.Sim`, `TwoPass`, `PulseVacuity`,
  `Cycle.*`, `GC.Impl.Pages.*`) are unchanged and verify.

### 12.4 The contract (`GC.Spec.Top.Iface`)

- `young_sound`: a major pointer in a young field is a value the program
  may store (resolves to a block it may use); `is_block` dropped (G39).
- `young_infix_ok` is gone.  In its place `young_follow_ok`: a young
  pointer in a young field whose target is a field word reading as an
  infix header is one the model resolves (`follow_at`).  It is about
  pointers only, and holds of every OCaml nursery: young pointers are never
  dangling.  A dangling young pointer to a word that is not infix-looking
  stays allowed, as before.  Stated at field words, so it is the same for
  every view of the nursery (`PagesMinor.yfollow_heq`).
- `minor_pre`: `... /\ young_sound /\ young_follow_ok` (was
  `young_infix_ok`).

### 12.5 The pages minor collection

- `YoungInfix.follow_one`: an address the model follows safely is one the
  bytes follow safely; `young_resolve_follow`: an address the bytes read
  as a genuine infix one (`infix_at`) is one the model resolves, to the
  block of its closure (`infix_closure`, `infix_model`).  The second is
  what `PagesRw.dangling` needs: a young pointer in an old block's
  remembered slot the model does not resolve has no entry, since an entry
  is only made for a followed address.
- `PagesLive.fields_follow_of`, `roots_follow_of`; `PagesMinor.mt_one`:
  a young field's major pointer resolves to a block in use for the
  instance (`ptr_resolve`, `live_in_use`); `ctx_start` gives `cpre_w`.
- `PromoteRun`: its state `sok` carries `entries_follow`; the loop lemmas
  take `follow_ok` of what they forward.
- `pages_minor_ok` and `pages_components_ok` verify under the new
  `minor_pre`.

### 12.6 Witnesses

- `GC.Spec.Pages.Promote.FollowWitness.accepted` (bytes, under
  `n_pages > 0`): a major heap with a closure `C` (wosize 3, tag 247) whose
  field 1 is an infix header of offset 2; a nursery with one object `A`
  (root) whose fields are the infix pointer `C + 16` and the word 249.
  `minor_wf`, `fields_follow`, `roots_follow` and
  `major_targets free_stw` hold; `minor_infix_wf` fails (at `A + 16`, which
  reads as infix with offset 0) and `minor_major_fields_not_free free_stw`
  fails (`C + 16` is infix, not in use).  The allocator's invariant is not
  part of it: the heap is built directly, not by the page allocator.
- `GC.Spec.Top.FollowWitness.accepted` (model): a world whose live young
  block holds `Major 2` (an infix pointer into the closure at 0) and
  `VInt 249`; `minor_pre` holds with the toy allocator; `Major 2` is not a
  block and `VInt 249` reads as an infix header outside a closure (what
  the earlier conditions rejected).

### 12.7 Checking

From a fresh cache per seed: the changed promotion modules (`Follow`,
`Loop`, `Collect`, `Mark`, `Sweep`, `Idle`), the byte witness, and all 49
`GC.Spec.Top` modules without `--retry` at the seed; the 23 unchanged
downstream modules (`Promote.Sim`, `TwoPass`, `PulseVacuity`, `Cycle.*`,
`GC.Impl.Pages.*`) with the repository's flags (`--retry 3`,
`--z3refresh` for the Pulse code).  Rlimits at most 40, no admits or
assumes.

| Z3 seed | modules | errors | warnings | total time | slowest |
|---|---|---|---|---|---|
| 0 | 78 | 0 | 0 | 2490 s | `ByteMark`, 185 s |
| 1 | 78 | 0 | 0 | 2558 s | `Promote.Loop`, 188 s |
| 2 | 78 | 0 | 0 | 2535 s | `ByteMark`, 189 s |

Two fixes came from the seeds: `Mark.cut_edge` (a lemma of the marking
invariant's proof moved to the top level: an address bound timed out in
the larger context at seed 1) and `PagesDone.roots_mem_l`/`roots_mem_r`
(the word built inside the helper); each module and its dependents were
rechecked at the three seeds.

### 12.8 Files

- **New**: `GC.Spec.Pages.Promote.Follow`, `GC.Spec.Pages.Promote.FollowWitness`,
  `GC.Spec.Top.FollowWitness`.
- **Changed**: `GC.Spec.Pages.Promote.Loop`, `Collect`, `Mark`, `Idle`,
  `Sweep`; `GC.Spec.Top.Iface`, `YoungInfix`, `PromoteRun`, `PagesLive`,
  `PagesMinor`, `PagesRw`, `PagesDone`, `PagesMinorOk`, `Broken`;
  `Makefile` (the two witnesses added to `ROOT_MODULES`).

## 13. Stage 2c: first-fit as a second full instance

The user's request (2026-11-22): first-fit as a second full instance on the
same byte representation, swapping only the allocator and the sweep, with
the same barrier, mark and minor collection.  akhil's first-fit allocator
and fused sweep are called read-only; every instance proof is in my modules.
The runs and `gc_correct` are not built yet.

### 13.1 The components

- **Allocator** `FFAlloc.ffa`:
  - the state is the free-list head and the bytes below `zero_addr`
    (`ffst = { fp; lo }`); the allocator runs on `gl h s = set_low h s.lo`,
    as pages does;
  - `alloc` is akhil's `Allocator.Phase.alloc_at` at the phase
    (`gph`: Idle, Marking, `Sweeping c`), whose colour is
    `Phase.allocation_color`: black while marking, black at or after the
    sweep's cursor and white before it mid-sweep, white idle;
  - `free` is blue, read from the header (`fffree`); `room` is "the
    allocation succeeds" (`ffroom`; the tag and phase play no part,
    `FFInst.search_obj`);
  - the invariant (`FFWrite.fshape`) is, while marking, akhil's
    well-formedness, a dense walk, an ascending free list (`mshape`);
    mid-sweep at `c`, akhil's `sweep_inv_incremental` (`sshape`); idle, his
    sweep invariant at a finished cursor (`ishape`).  Each also says the
    walk reaches the end and every block in use has a field (`nz`, G40);
  - `init` is one blue block from `zero_addr` to the end, its link null
    (`FFAlloc.init_heap`, G41).
- **Sweep** `FFSweep.ffsweep`:
  - the progress is akhil's cursor; a block is unswept when its header is
    at or after it (`ffunswept c o = pos o >= c`);
  - `start` is `FusedSweep.sweep_start` (cursor at `zero_addr`);
  - a step is one `FusedSweep.sweep_step` from the derived state
    (`SweepPhase.Intrinsic.state_at`): one block, freed when white,
    whitened when black, merged with a free neighbour when blue; the words
    freed are the white block's, header included (`ffw`);
  - `done` is `SweepPhase.Intrinsic.sweep_done` (`c + 8 >= heap_size`).
- **Capacity** `FFFits.fffits`: the invariant, and a free-list cell
  (`FreeList.fl_cell`) of at least `sz + 1` words, header included.
- **Mark and barrier**: the pages collector's, unchanged (`ByteMark.bmark`,
  `ByteBarrier.bbarrier`).
- **Minor collection** `FFMinor.ffminor`: the same generic promotion
  (`GC.Spec.Pages.Promote`) and pointer update, with first-fit's promotion
  allocator `FFPromote.fftal ph`:
  - its state is the free-list head, its invariant `fshape ph`, its free
    akhil's at the phase (`FFAllocOk.ffree_of`: blue; mid-sweep also the
    white blocks after the cursor, pending free), as in his own minor
    collections (`GC.Gen.SweepPhase.Minor`);
  - the colour of a copy depends on its address (`ffcol`, G44), and is
    the colour rule on either side of the cursor (`FFPromote.col_rule`).

### 13.2 Mid-sweep free, restated

akhil's step statement (`FusedSweep.Step.sweep_inv_incremental_step`)
counts white blocks after the cursor as free (`free_incremental`), so for
him a step changes no block in use.  The contract's free is blue only, so a
step frees the white block at the cursor.  `FFSweepOk` restates it, as
`PagesFree` did for pages:

- `bstep`: akhil's facts of one step (`can_sweep`, the in-use equality,
  `same_block`, pending only shrinks), the heap from the new cursor on
  unchanged (`FFStep.step_front`, re-derived from his exported per-case
  statements `step_eq_black`/`_blue`/`_white`/`_merge`, G42), the walk to
  the end, `nz` after;
- the model clauses on the canonical readings: the cursor's block is the
  only block of the region (`region_one`); a black block there becomes
  white with its contents (`black_m`); a white one leaves use
  (`white_m`); every other block in use keeps its block (`kept_m`);
  nothing comes into use (`used_after`);
- free words, by tiling both readings (`words_white`, `words_kept`,
  `words_back`).  The sweep merges adjacent free blocks, so a free block
  can disappear into a larger one; the contract counts free words, not
  free blocks, so the merge is allowed and the proofs are per word;
- `freed_words`: the white block's words at the cursor are the model's
  sum (`freed_cur`, an indicator summed by `PagesFreed.sum_ind`).

### 13.3 Clause by clause: pages and first-fit

| Clause | Pages (§10, §11) | First-fit (this section) |
|---|---|---|
| State, progress | page state + low bytes; page map and cursor, unswept by page (`Graft.uw`) | free-list head + low bytes; akhil's cursor, unswept at or after it |
| Invariant | page invariant of the phase (`MidSweepAlloc.inv_sw`) | `fshape`: akhil's well-formedness, walk and ascending list (marking), `sweep_inv_incremental` (mid-sweep; idle at a finished cursor); plus `nz` (G40) |
| `init_at` | `PagesInst.init_ok` (all blue pages) | `FFInit.init_ok` (one blue block, own init, G41) |
| `free_hd_at` | blue from the header | `FFInst.free_hd_ok`, the same |
| `alloc_at`: room, header, colour | `PagesInst.alloc_m`, `colour_ok` | `FFInst.alloc_m`; `FFAllocOk.new_block` (header in `colour_at`, `colour_eq`) |
| o's words were free | `PagesAllocOk.words_free` (generic, by tiling) | `FFAllocOk.words_free`, the same argument |
| only o comes into use | `use_rel` (`NewOnly.new_only`) | `FFAllocOk.use_rel`, from `FFBytes.new_ok` (`alloc_at_obj_ne_excl`, `only_new_is_obj_out`) |
| other blocks unchanged | `kept_block` | `FFAllocOk.kept_block` |
| well formed after | `wf_after` | `FFAllocOk.wf_after` |
| invariant after the Fill | `fill_inv`, every phase's `fields_written_away` | `FFInst.fill_inv`: `FFFill.marking_fill` (colour-blind, G43), `sweep_fill` (akhil's `alloc_sweep_phase`, `fresh_close`), idle at a finished cursor |
| `inv_frame_at` | `PagesFrame.frame_ok` (`Cycle.Write`) | `FFFrame.frame_ok`: `FFWrite.write_phase` (akhil's `write_sweep_phase`; colour-blind while marking, G43), `recolour_marking` (`recolour_one`) |
| `inv_start_at`, `free_white_at` | `inv_start_ok`, `free_white_ok` | `FFInst.inv_start_ok` (idle is a finished sweep, so the marking shape), `free_white_ok` |
| Capacity | a free page, or a page of the class with a slot, or a run; under `n_pages > 0` (G34) | a free-list cell of `>= sz + 1` words; `fffits_room` (akhil's `Exact.alloc_spec_fits_succeeds`, `fl_ascending_exact`); `fffits_init` with no assumption |
| Sweep start | `PagesSweep.start_m` (`sw_start`, tricolour from `dark_closed`) | `FFSweep.start_m` (`sweep_inv_incremental_start`, `noGreyObjects` and `tri_color_invariant` read from the model) |
| Step granularity | one unit (pool page or large run) | one block |
| Step: progress | `clause_progress` | `FFSweepOk.clause_rest` (the cursor's block, `oc_region`) |
| Step: white freed, black whitened, outside kept | `clause_blocks` (`PagesFree`) | `FFSweepOk.clause_blocks` (`blocks_m`: `white_m`, `black_m`, `kept_m`, `used_after`) |
| Step: free words exactly | `clause_words` | `FFSweepOk.clause_words` (`words_m`; merges allowed, per word) |
| Step: `freed_words` | `clause_freed` (`freed_reindex`) | `FFSweepOk.clause_freed` (`freed_cur`, one block) |
| Step: invariant | `clause_inv` | `clause_rest` (`bstep`: `sshape` at the new cursor) |
| Sweep done | `PagesSweep.done_m` | `FFSweep.done_m` (`sweep_inv_incremental_end`, `used_below` by `nz`) |
| Promotion allocator | `idle_tal`, `mark_tal`, `sw_tal pm0`; one colour per phase | `fftal ph`; colour per address (G44); `ff_contract` |
| Promotion: pointer update keeps the invariant | `AllocTagOk.mark_inv_update`, `sw_update` | `FFPromote.upd_inv` (`upd_heads`, restated for any set, G45; `upd_fl`; akhil's `shape_transport`) |
| Copies' colour | white mid-sweep (copies land in swept pages) | `col_rule`: black at or after the cursor, white before, as `colour_at` |
| `minor_ok` | `PagesMinorOk.pages_minor_ok` | `FFMinorOk.ff_minor_ok`: PagesReplay ... PagesMinorOk restated over first-fit (`FFReplay` ... `FFMinorOk`); `PagesLive`, `PagesFwd`, `PagesQueue.copies` shared |
| `live_target` mid-sweep | not white in an unswept page (`MidSweep.uw_same`) | not white at or after the cursor: akhil's `pending_free` exactly, on an aligned cursor |
| Mark, barrier | `byte_mark_ok`, `byte_barrier_ok` | the same lemmas |
| `components_ok` | `PagesComps.pages_components_ok`, under `n_pages > 0` | `FFComps.ff_components_ok`, unconditional |

### 13.4 Gaps found

| # | Gap | How it showed | Change |
|---|---|---|---|
| G40 | akhil's sweep steps only while `c + 8 < heap_size`, and is done after.  A block in use with no field whose header is the last word of the heap would never be swept: it stays black into the next cycle. | `FFSweep.done_m`: blocks in use must lie before a done cursor | The first-fit invariant carries `nz`: every block in use has a field.  The model's sizes are at least 1 (`size_t`, `young_ok`), and akhil's allocator rounds 0 up, so it holds throughout. |
| G41 | akhil's `init_heap_spec` places the free block at address 0; the representation starts at `zero_addr`. | `init_at` | First-fit uses its own initial heap (`FFAlloc.init_heap`), one blue block from `zero_addr`. |
| G42 | akhil proves that a step leaves the heap after the new cursor alone (`FusedSweep.Step.stepped`) but does not export it. | the model's frame of a step | Re-derived from his exported per-case statements (`FFStep`). |
| G43 | akhil's allocation lemma while marking (`GC.Gen.MarkPhase.Alloc.marking_alloc_shape`) asks for his generational marking shape (`GC.Gen.Incremental.phase_shape`, with the mark's scan position and the nursery); the allocator component's marking invariant is the heap's shape only (the mark's invariant belongs to the mark component). | `inv_frame_at`, the Fill while marking | Colour-blind restatements of the well-formedness part (`FFFill.marking_fill`, `FFWrite.write_marking`, `write_wf`). |
| G44 | The promotion's allocator (`Promote.tal`) had one colour for every copy.  First-fit mid-sweep colours a copy by its address (black at or after the cursor, white before it). | `FFPromote.fftal` | `tal.col` is a function of the address; the page instances are constant functions.  `Promote`, `Loop.copy_of`, `Collect.copies_in_use`, `collect_blocks` take the colour at the copy. |
| G45 | akhil's "the pointer update keeps the walk and every header" (`SweptTail.update_heads`) is stated only for the blocks in use; the promotion's contract asks it for any set the update may select (`walk_ok`). | `ff_contract` | His induction (`uop_heads`, `uwa_heads`) restated for any set in `FFPromote`. |

None needed a change to the top-level specification (`Iface`, `Run`).
The promotion's `tal` is mine; the change is a generalisation, and every
page instance and their dependents verify unchanged in substance.

### 13.5 Residuals

- One block per step; one step of akhil's sweep is one call of the
  component's `step`.
- The first-fit runs are not built; `gc_correct` is not proved.
- Non-vacuity at this stage is the allocator's side only
  (`FFComps.ff_nonvacuous`: the initial heap meets the invariant idle and
  while marking, the capacity condition holds for one field, and the
  allocation succeeds in both phases).  Witness runs with roots, reachable
  and unreachable blocks come with the runs.

### 13.6 Checking

From a fresh cache per seed, in dependency order (104 files): the changed
promotion modules (`Promote`, `PromoteInst`, `Follow`, `Loop`, `Collect`,
`Idle`, `Mark`, `Sweep`), the byte witness and all 70 `GC.Spec.Top`
modules (22 of them new, first-fit) without `--retry` at the seed; the 25
unchanged downstream modules (`Promote.Sim`, `TwoPass`, `PulseVacuity`,
`Cycle.*`, `GC.Impl.Pages.*`) with the repository's flags (`--retry 3`,
`--z3refresh` for the Pulse code).  Rlimits at most 40, no admits or
assumes.

| Z3 seed | files | errors | warnings | total time | slowest |
|---|---|---|---|---|---|
| 0 | 104 | 0 | 0 | 2305 s | `ByteMark`, 137 s |
| 1 | 104 | 0 | 0 | 2299 s | `ByteMark`, 133 s |
| 2 | 104 | 0 | 0 | 2413 s | `ByteMark`, 137 s |

One fix came from the seeds: in `PagesDone2.copy_field` (and the same in
`FFDone2`), an inner lemma about the young pointers of a copied field timed
out at seeds 1 and 2 in the proof's large context; it is now two top-level
lemmas (`cov_one`, `cov_all`).  The two modules and their dependents
(`PagesMinorOk`, `PagesComps`, `FFMinorOk`, `FFComps`) were rechecked on
each seed's cache at the three seeds, clean.

### 13.7 Files

- **New**: `GC.Spec.Top.FFAlloc`, `FFBytes`, `FFFill`, `FFAllocOk`,
  `FFInst`, `FFWrite`, `FFInit`, `FFFrame`, `FFStep`, `FFSweep`,
  `FFSweepOk`, `FFFits`, `FFPromote`, `FFReplay`, `FFQueue`, `FFOor`,
  `FFMinor`, `FFDone`, `FFRw`, `FFDone2`, `FFMinorOk`, `FFComps`.
- **Changed**: `GC.Spec.Pages.Promote` (`tal.col` per address, G44),
  `Promote.Loop`, `Promote.Collect`, `Promote.Idle`, `PromoteInst`;
  `GC.Spec.Top.PagesDone2` (`cov_one`, `cov_all`); `Makefile`
  (`FFComps` added to `ROOT_MODULES`); this document (§13).

## 14. Witness runs: the first-fit collector

The user's request (2026-11-23): witness runs for both instances, in both
styles, each from a heap built through the allocator, with roots, reachable
and unreachable objects, and every event: allocation with Fill, a young
allocation, writes through the barrier (one that darkens), a read, a root
change, mark slices, sweep steps, minor collections in every phase, a young
field holding an infix pointer into an old closure and one holding an
integer that reads as an infix header; every hypothesis shown to hold;
`gc_correct` not proved.  First-fit first, then pages.

This section covers first-fit: both runs are built and checked.  The
pages runs are not built yet (§14.7).

### 14.1 Why the runs are symbolic, and the hypothesis

Normalisation, as the toy runs use it (`assert_nbe`), cannot compute these
runs: the configuration is abstract.

- `heap_size` and `zero_addr` are `val`s of `GC.Spec.ZeroAddr`, supplied at
  link time.  This holds for both instances.
- The nursery's size (`GC.Gen.Base.minor_heap_size`) is abstract too.  So is
  the largest young object (`max_young_wosize`), known only to be at least 1.
- The page parameters are abstract (`GC.Spec.Pages.Params`), for pages only.

So the runs are symbolic.  Every heap of a run is a closed form relative to
`msize`, and every step is a lemma.  The runs hold under one explicit
hypothesis, a `requires` on every witness lemma (never an `assume`), in the
style of the page witness's `big_enough`:

- **`FFWState.ff_room`**: `32 <= msize /\ 4 <= ywords`.  That is room in the
  major heap for the objects the runs allocate (16 words below its top in the
  sequential run, 24 in the incremental one (§15), plus the free block), and room in the nursery for two one-field objects.

The real configuration meets it by orders of magnitude.  The extracted
defaults set `minor_heap_size_u64` to 2048 bytes (`ywords` = 256).  The OCaml
integration sizes the nursery from OCaml's minor heap and allocates the
major heap with `calloc` (`zero_addr` = its base, `heap_size_u64` = its end),
thousands of words.  Since `max_young_wosize >= 1` is all that is known, each
young object of the runs has one field.

### 14.2 Method: exact model heaps in closed form

At every step the run tracks a description `FFWStep.holds x d`.  It says the
configuration is not stopped, gives its phase, says the free list's head is
the bottom block, gives the model heap `FFWState.mk st` that the byte heap
represents (`brepr`), the nursery and the model nursery it represents, the
roots, and an empty remembered set.  `wd d` is then a world that represents
the configuration, and every world that does has the same reading
(`views_wd`).  So `vw x`, the world `run_ok` reads, has the same reachable
blocks and values (`RunFacts.wheq`, `mutator_wheq`).

`mk st` is a closed form over a small record: the free block's size, each
block's colour (`None` before it is allocated), the fields the program
writes, and the free block's link.  First-fit places each block at the top
of the free block at 0, so the blocks sit at fixed distances below the top
of the heap:

| block | model address | fields |
|---|---|---|
| A | `msize - 3` | 2 |
| B | `msize - 5` | 1 |
| C | `msize - 7` | 1 |
| K | `msize - 11` | 3; a closure (tag 247) whose second field is `infix_word 2` |
| D | `msize - 13` | 1 (incremental run only) |
| E | `msize - 15` | 1 (incremental run only) |

Each event is one lemma per kind of event (`FFWStep.step_*`).  Each turns the
component on the byte heap into a model update, given as a hypothesis the
equation between closed forms that each run proves (`FFWOps`, `FFWMark`).

- **Allocation with Fill**: akhil's search takes the head and splits it,
  right-justified (`FFWAlloc.ffalloc_head`, via `alloc_search_found_head`
  and `alloc_from_block_split_normal`).  The model is `FFWAlloc.split`, then
  the Fill (`ByteBarrier.binit_from_ok`).  The new block's colour is the
  colour rule at its address.
- **Writes**: `ByteBarrier.bwrite_cabs`, with the darkening (`tdark`).
- **The mark's start and slices**: `ByteMark.bstart_cabs` and
  `scan_obj_cabs` at the lowest grey block (`find_grey_low`), in closed
  form (`FFWMark.start_seq`, `start_inc`, `slice_A`, `slice_B`, `slice_K`).
- **Sweep steps** (`FFWSweep`), from akhil's step at the derived state
  (`state_at`).  The bottom free block is left alone (`sweep_head`).  A black
  block is whitened (`sweep_black`).  Garbage not after a free block is freed
  and linked after the bottom block (`sweep_white`: `last_cell_behind` is
  the bottom block, `frag_at` is 0).
- **Minor collections on the empty nursery** (`FFWMinor0.pcollect_empty`).
  The promotion forwards nothing.  akhil's pointer update with the empty map
  writes nothing (`update_object_pointers`, `update_walk_aux` by induction).
  The result is `Done`, with the same heap, free list and roots.  A reset
  nursery is the initial one (`yreset_yinit`).
- **Young allocation** (`Young.yalloc_repr`).  It is computed for the empty
  nursery (Y1 at 0) and after it (Y2 at 2) (`FFWYoung`).

A byte step that writes known words is the model update that changes those
words.  `FFWWords.heq_of_words` / `words_of_heq` give that a canonical,
representable model fixes every word from `zero_addr` on (`Abs.cword`), and
`FFWModel.write1_repr` is one word written.  Representability is preserved by
updates that keep the shape (`FFWModel.same_shape_ok`) and by the split
(`FFWAlloc.split_ok`).

### 14.3 The runs

**Sequential** (`GC.Spec.Top.FFWSeq`, 25 events):

| # | event | phase | what happens |
|---|---|---|---|
| 0-3 | `EAlloc` ×4 | idle | A `[1; 1]`, B `[1]`, C `[B]`, K `[1; infix_word 2; 1]` |
| 4 | `EWrite A.0 := B` | idle | through the barrier |
| 5 | `EWrite A.1 := K+2` | idle | an infix pointer into K |
| 6 | `ERoots [A]` | idle | root change |
| 7 | `ERead A.0` | idle | B read into a root: roots `[B; A]` |
| 8 | `EStart` | idle | A, B grey; snapshot {A, B, K}; C unreachable |
| 9 | `EMinor` | marking | empty nursery |
| 10-12 | `ESlice` ×3 | marking | B; A (greys K through the infix pointer); K |
| 13 | `EHandover` | marking | no grey |
| 14 | `ESweep` | sweeping | the free block |
| 15 | `EMinor` | sweeping | empty nursery |
| 16-19 | `ESweep` ×4 | sweeping | K whitened; C freed (linked after the free block); B, A whitened |
| 20 | `EEnd` | sweeping | the cursor at the end |
| 21 | `EYoungAlloc [K+2]` | idle | Y1: an infix pointer into the old closure K |
| 22 | `EYoungAlloc [infix_word 2]` | idle | Y2: an integer that reads as an infix header |
| 23 | `ERoots [A; Y1; Y2]` | idle | root change |
| 24 | `EMinor` | idle | Y1 and Y2 live |

**Incremental** (`GC.Spec.Top.FFWInc`): rebuilt with promoting minor
collections while marking and while sweeping, 34 events; the table is in
§15.2.

### 14.4 What is proved

Every statement below is under `ff_room` only.

- `FFWSeq.ff_vacuity_sequential`: `components_ok fc` (stage 2c), `run_ok fc
  Sequential msize ywords es_seq`, and `run_hyps fc msize ywords es_seq`.
  These are every hypothesis of `gc_correct` and `gc_correct_local`.
- `FFWInc.ff_vacuity_incremental`: the same for `Incremental` and `es_inc`. (§15)
- `RunFacts.run_hyps_of_ok`: the contracts give `run_hyps` for every run of
  every collector.
- Non-triviality, on `vw` of the configuration:
  - `seq_nontrivial` and `inc_nontrivial`: at the cycle's start, A is a root,
    and A, B and K are reachable; K is reachable only through A's infix
    pointer.  C is in use (not free for the allocator) and unreachable
    (`FFWStart.c_unreachable`, a closure argument).
  - `inc_darkens`: the write at 9 runs while marking, overwrites A.0 (B,
    white), and B is grey after it.
  - `inc_interleaves`: the program allocates, writes and allocates young
    objects while marking (8-11) and while sweeping (18-21), and changes the
    roots while sweeping (23); event numbers as in §15.2.
  - Minor collections run in each phase: sequential 9, 15, 24
    (`seq_minor_phases`); incremental 12 (marking), 22 (sweeping), 33
    (idle).
  - `seq_infix_cases` (at the last minor collection) and `inc_infix_cases`
    (at the collection while marking, 12): Y1 and Y2 are young-reachable
    from the roots.  Y1's field is `K+2`, which
    resolves to K, in use.  Y2's field is `infix_word 2`, which `infix_hdr`
    reads as an infix header.
  - `every_event` holds of both runs.

### 14.5 What the runs do not show

- **Sequential style and the barrier's darkening.**  In the sequential
  style the program runs only while idle (`style_ok`), so a write never
  happens while marking and the barrier never darkens.  Only the
  incremental run exercises the darkening.
- **Minor collections while marking and while sweeping run on the empty
  nursery** in the sequential run.  In the sequential style nothing is
  allocated young during a cycle.  The incremental run promotes live young
  objects in both phases (§15).
- **One allocation size per object, and no coalescing.**  The layout keeps
  garbage away from free blocks, so the sweep's coalescing case (a free
  block grown over the next one) is not exercised.

### 14.6 Checking

The new modules were checked in dependency order on each seed's cache from
the stage-2c sweep, at Z3 seeds 0, 1 and 2, without `--retry`.  Each new
module's `.checked` file was removed first; the modules they depend on are
unchanged since that sweep.  Rlimits are at most 40, with no admits and no
assumes.  Results are in §14.8.

### 14.7 Pages: not built

The pages runs need the same apparatus for the page allocator and the page
sweep:
- allocation into a pool page of a size class, or into a run of empty
  pages, with abstract `page_wsize`, `n_cls` and `cls`;
- the page sweep's units over a page or a run;
- a closed form of the heap over pages.

The witness `GC.Spec.Pages.Witness` (`big_enough`) gives the heap shape to
start from, not the steps.  This is at least the size of the first-fit work
(16 modules here) and is the next stage.

### 14.8 Files and results

- **New**: `GC.Spec.Top.FFWWords`, `FFWAlloc`, `FFWModel`, `FFWSweep`,
  `FFWMinor0`, `RunFacts`, `FFWState`, `FFWStep`, `FFWRun`, `FFWOps`,
  `FFWMark`, `FFWStart`, `FFWOk`, `FFWYoung`, `FFWSeq`, `FFWInc`.
- **Changed**: `Makefile` (`FFWInc` added to `ROOT_MODULES`); this document
  (§14).

| Z3 seed | modules | errors | warnings | total time | slowest |
|---|---|---|---|---|---|
| 0 | 16 | 0 | 0 | 499 s | `FFWSeq`, 96 s |
| 1 | 16 | 0 | 0 | 505 s | `FFWSeq`, 100 s |
| 2 | 16 | 0 | 0 | 497 s | `FFWSeq`, 101 s |

## 15. Witness runs: promotions inside the cycle (first-fit)

The user's request (2026-11-23): close the promotion gap of §14.5.  In the
incremental run, add a minor collection while marking and one while
sweeping, on a nursery holding live young objects.  Among them: Y1, an
infix pointer into the old closure K, and Y2, an integer that reads as an
infix header, both reachable from the roots.  Prove `minor_pre` there and
compute the result: `Done`, each live young object promoted once through
first-fit, the copies in the colour the colour rule gives, the young
pointers rewritten, and Y2's integer field unchanged.  If cheap, also add a
sweep step where garbage sits next to a free block (coalescing).

Both promoting collections are built and checked.  Coalescing is not
built (§15.5).  The hypothesis is still `ff_room` alone (§14.1): the run
now uses 24 words below the heap's top, and `32 <= msize` leaves the free
block at least 8 fields.

### 15.1 The layout

First-fit places each block at the top of the bottom free block.  Each
collection promotes two one-field objects, Y2 first (the queue order,
§15.3), so each adds two blocks below the earlier ones:

| block | model address | placed at | colour | field |
|---|---|---|---|---|
| D | `msize - 13` | 8, marking | black | B, later `K+2` |
| P1 (Y2's copy) | `msize - 15` | 12, marking | black | `infix_word 2` |
| P2 (Y1's copy) | `msize - 17` | 12, marking | black | `K+2` |
| E | `msize - 19` | 18, sweeping | white | A |
| P3 (Y2's copy) | `msize - 21` | 22, sweeping | white | `infix_word 2` |
| P4 (Y1's copy) | `msize - 23` | 22, sweeping | white | `K+2` |

The colours are the colour rule's (`colour_at`).  While marking a new block
is black.  While sweeping, a block below the cursor (`msize - 17` after the
sweep's first step) is white: the sweep has passed it, and it is in use.
So the sweep (24-30) visits P2, P1, D, K, C, B, A and never E, P3 or P4.

### 15.2 The run

`GC.Spec.Top.FFWInc`, 34 events:

| # | event | phase | what happens |
|---|---|---|---|
| 0-6 | as sequential 0-6 | idle | A, B, C, K; A.0 := B; A.1 := K+2; roots `[A]` |
| 7 | `EStart` | idle | A grey; A, B, K reachable, C unreachable |
| 8 | `EAlloc [B]` | marking | D, black |
| 9 | `EWrite A.0 := 1` | marking | the barrier darkens B, white to grey |
| 10 | `EYoungAlloc [K+2]` | marking | Y1 at young 0: an infix pointer into K |
| 11 | `EYoungAlloc [infix_word 2]` | marking | Y2 at young 2: an integer that reads as an infix header |
| 12 | `EMinor` | marking | **promotes** Y2 to P1, Y1 to P2; roots `[Y2; Y1; D; A]` become `[P1; P2; D; A]` |
| 13-15 | `ESlice` ×3 | marking | B; A (greys K); K |
| 16 | `EHandover` | marking | |
| 17 | `ESweep` | sweeping | the free block |
| 18 | `EAlloc [A]` | sweeping | E, white |
| 19 | `EWrite D.0 := K+2` | sweeping | no darkening |
| 20-21 | `EYoungAlloc` ×2 | sweeping | Y1, Y2 again (`[K+2]`, `[infix_word 2]`) |
| 22 | `EMinor` | sweeping | **promotes** Y2 to P3, Y1 to P4; roots rewritten |
| 23 | `ERoots [A; E]` | sweeping | P1-P4 and D now unreachable |
| 24-30 | `ESweep` ×7 | sweeping | P2, P1, D, K whitened; C freed; B, A whitened |
| 31 | `EEnd` | sweeping | |
| 32 | `ERead A.1` | idle | the infix pointer read into a root |
| 33 | `EMinor` | idle | empty nursery |

### 15.3 One promotion, computed

`GC.Spec.Top.FFWMinor2` computes the collection on a nursery holding
exactly Y1 and Y2 (`FFWYoung.ym2`), both live from the roots, over any
heap `m` whose bottom block is free with `f >= 7` fields (`pre2`, sealed).
The proof unfolds akhil's promotion step by step:

- **Roots.**  `forward_roots` forwards the roots in order.  With roots
  `Y2 :: Y1 :: rest`, and `rest` holding no young pointer
  (`no_young_roots`), the queue is `[Y2; Y1]` (`roots2`, `froots`).
- **Each object.**  `forward_one` → `forward_normal` → `promote_object`
  (`promo1`).  Each object is read through its own header, a normal
  one-field header; Y2's field is never read as a header.  The first-fit allocation takes the
  bottom block and splits it right-justified (`alloc1`, via
  `FWA.search_head` and `block_split`), in the colour `colour_at` gives.
  The one field is copied word for word (`promoted m f col v`).  Y2 goes to
  `f - 1` and Y1 to `f - 3` (`prom_first`, `prom_second`).
- **The scan.**  Both copies' fields are majors or integers: the scan
  forwards nothing and leaves the state alone (`scan_noop`, `scan2`).
- **No failure.**  The replay's `fails_at` is false at every point
  (`no_fail`), so `pcollect` is not `OutOfRoom` (`no_wit`).
- **Pointer update.**  akhil's `update_pointers_with` writes a field only
  when it holds a young pointer.  No major field does (`body_hv`), so the
  heap is unchanged (`upw_out`, `hv_promoted`).
- **The result** (`pcollect_two`): `Done h' st' rs fwd` with
  - `brepr (m2 ph v w m f) h'`, the heap with exactly the two copies added;
  - the free-list head unchanged;
  - `fwd == F.fwd_of [(0, f-3); (2, f-1)]`, so each live young object is
    forwarded once, to its copy;
  - `rs == map (fwdv …) roots`, and `roots_fwd` computes it to
    `P_Y2 :: P_Y1 :: rest`.

The copy of Y2 holds `infix_word 2`.  The promotion copies it as data, and
nothing rewrites it: it is an integer, not a pointer.  The copy of Y1 holds
`K+2`, unchanged: a major pointer stays as it is.

`step_minor2` turns this into the run's step: after `EMinor`, the
configuration is described again (`holds`) with the copies in the heap, the
nursery reset (`ms0`, the empty model nursery) and the rewritten roots.

### 15.4 `minor_pre`, and the allocator's invariant along the run

`minor_pre` asks for the allocator's invariant `fc.a.inv`.  The witness
runs of §14 never needed it: the run's step does not read it.
`GC.Spec.Top.FFWInv` follows it through the run, one event at a time,
from the components' contracts (`FFComps.ff_components_ok` →
`Run.hyps_of_ok`):

- start: `init_at` (`inv_init`);
- allocation with Fill: `alloc_at`, its post's last clause instantiated
  with the closed form after the Fill (`inv_alloc`, `post_fill`);
- write, mark start, mark slice: `inv_frame_at`, given `inv_frame_rel` on
  the closed forms (`inv_write`, `inv_start`, `inv_slice`; `rel_of` builds
  the relation from one changed word);
- hand-over, sweep step, end: `sweep_start_at`, `sweep_step_at`,
  `sweep_done_at` (`inv_handover`, `inv_sweep`, `inv_end`);
- minor collection: `minor_at`, given `minor_pre` and `Done`
  (`inv_minor`);
- reads, root changes and young allocations leave it alone (`inv_same`).

Each contract is used through a small lemma that is generic over the
allocator (`frame_use_g`, `sweep_use_g`, `done_use_g`, `rel_g`).  This keeps
first-fit's invariant out of the solver's context.

`mpre_d` proves `minor_pre` on the description's world `wd d`:
- the invariant;
- `well_formed`;
- `young_ok` and `young_follow_ok` of the two-object nursery (`ym2_ok`);
- `rem_covers`: no major field holds a young pointer;
- `young_sound`: Y1's `K+2` resolves to K, in use and, while sweeping, not
  white.

`minor_pre_heq` carries it to every world equal word for word.  So
`minor_pre_12` and `minor_pre_22` hold for every world representing the
configuration at 12 and 22.

**What is proved** (each under `ff_room`):

- `promoted_12`: `fc.n.collect` at 12 is `Done h' _ rs fwd` with
  `brepr (mk st10) h'`, `fwd 2 == Some P1`, `fwd 0 == Some P2`,
  `rs == [P1; P2; D; A]`, P1 and P2 black, P1's field `infix_word 2`
  and P2's field `K+2`.  It is never `OutOfRoom`.
- `promoted_22`: the same at 22 with P3, P4, both white, and
  `rs == P3 :: P4 :: E :: [P1; P2; D; A]`.
- `minor_pre_12`, `minor_pre_22`: as above.
- `ff_vacuity_incremental`, `inc_run_ok`, `inc_every_event`,
  `inc_nontrivial`, `inc_darkens`, `inc_interleaves` and `inc_infix_cases`
  (at 12: Y1 and Y2 young-reachable, Y1's field `K+2` resolving to K in
  use, Y2's field reading as an infix header).

`run_ok`'s minor step still asks nothing of the result.  The computed
result is proved as a separate statement about `fc.n.collect` at that
configuration, and the run's configuration after the step is that result
(`step_minor2`).

### 15.5 Coalescing: not built

In the layout, garbage never sits next to a free block.  C is freed with
K below it and B above it, both in use.  A coalescing step needs three
things:

- a layout change shared with the sequential run, which also fixes the
  first seven events;
- a model lemma for akhil's merge case of the sweep (the free block grown
  over the next one) in closed form, with its representability proof, as
  `FFWSweep.sweep_white` is for the case that does not coalesce;
- the free list's shape after the merge, carried through the later steps.

That is a stage of its own (the size of `FFWSweep`, plus a rework of the
first seven events), not cheap, so it is not built.

### 15.6 Files and results

- **New**: `GC.Spec.Top.FFWMinor2` (one promoting collection, computed),
  `GC.Spec.Top.FFWInv` (the allocator's invariant along a run;
  `minor_pre`).
- **Changed**:
  - `FFWState`: the new blocks E and P1-P4 and their positions, and the
    record fields `cp1`-`cp4`;
  - `FFWOps`: `promo_M`, `promo_S`, `two`, and `alloc_E` at its new
    address; `alloc_K` split into pointwise header and body lemmas (it
    failed at seed 1 once `mk` had more cases);
  - `FFWStep`: `wheq_sym`; `FFWSeq`: `seq_infix_cases` uses it (it failed
    at seed 1);
  - `FFWStart`: the copies are absent at the cycle's start;
  - `FFWInc`: rebuilt, 34 events;
  - this document: §14.1, §14.3, §14.4 and §14.5 updated, and §15 added.
- `FFWInc` is already in `ROOT_MODULES` and imports both new modules.

Checked without `--retry` at Z3 seeds 0, 1 and 2.  For each seed, the 17
witness modules `FFWWords` … `FFWInc`, plus `FFWrite`, were rechecked after
their dependencies, each from a removed `.checked` file.  The three seeds ran
in parallel, two jobs each, so the times are slower than a lone run.  Rlimits
are at most 40, with no admits and no assumes.

| Z3 seed | modules | errors | warnings | total time | slowest |
|---|---|---|---|---|---|
| 0 | 18 | 0 | 0 | 2069 s | `FFWInc`, 634 s |
| 1 | 18 | 0 | 0 | 2067 s | `FFWInc`, 628 s |
| 2 | 18 | 0 | 0 | 2071 s | `FFWInc`, 630 s |

The cherry-picked robustness commits (2c7b8918, d6aa4b11) change
`Pages.PoolInit`, `Frame`, `NewRun`, `SweepPage` and `SweepPools`.  The 139
modules that depend on them, spec and Impl, were rechecked at each seed
with the repository's flags (`--retry 3` for modules that are not mine, as
in the build).  All 139 are clean at seeds 0, 1 and 2.  The one warning is
the existing warning 328 in `Pages.SweepAll`.

---

## 16. Plan: proving `gc_correct` and `gc_correct_local` (design only)

This section plans the proof of the top-level theorem as it stands in
`GC.Spec.Top.Run` (`conclusions`, clauses (0)–(6) and the read clause)
over the interfaces of `GC.Spec.Top.Iface`.  No proof module is changed by
it.  It was written by checking each clause against the contracts, as §7.7
did; that check found six places where the statement cannot be proved as
it stands (§16.2).

### 16.1 Shape of the proof

**One proof, for the incremental style.**  `style_ok Incremental` is `True`
and `conclusions` does not mention the style, so `run_ok c Sequential ⇒
run_ok c Incremental` and the sequential theorem is a corollary
(`seq_of_inc`, a few lines).  A separate sequential proof would skip only
the barrier's darkening and allocation while marking; it would still need
minor collections inside the cycle with a non-empty nursery (young objects
allocated while idle survive into the cycle), so it is not worth having.

**`gc_correct_local` first.**  `gc_correct_local_implies` is proved, so the
work is `gc_correct_local`, once G48 (§16.2) is fixed.  Until it is,
`gc_correct` is proved from a core lemma whose hypotheses are `run_hyps`
plus one extra fact that `allocator_ok` supplies.

**Induction over the run.**  A run invariant `rinv x` is carried by
induction on `i` (`RunFacts.at_succ`).  Each event gets one step lemma:
`rinv x ∧ hyps_at c x e ∧ enabled ∧ mutator_ok ⇒ rinv x' ∧ concl_step x e x'`.
`concl_point` follows from `rinv`.  The cycle clauses (3a), (3b), (4) and
(3c) need a second induction over the indices of a cycle, with the start
configuration fixed (§16.5).

**Views.**  Every conclusion reads `vw x`, a world chosen by indefinite
description, and every contract hands back *some* model of the new heap.
The proof first shows that all the predicates involved are invariant under
`agree` (same blocks, headers and fields; `Rep.repr_agree`), so the choice
never matters.  `resolve` is: an infix header that resolves lies in a
closure's field, a field word.

### 16.2 Clauses that cannot be proved as stated

Each is a missing guarantee: some component that meets its contract, or
some run, makes the clause false.  Each fix is small and keeps the existing
instances' proofs in substance.

| # | Where | Why it fails | Proposed fix |
|---|---|---|---|
| G46 | (1b), (5) and every later point, through `minor_pre`'s `rem_covers` | `rem_covers` asks for every old-to-young pointer **of every block in use**.  A minor collection while sweeping rewrites only `live_target` blocks (G37) and empties the remembered set.  A pending block (white, unswept, garbage) that got a young pointer while idle keeps it, its slot is no longer remembered, and the next minor collection before the sweep reaches it has no precondition: the component may return anything. Run: idle write of a young pointer into A; drop A; start; mark; hand over; minor; minor. | `rem_covers` over `live_target` blocks only.  The promotion rewrites exactly those, and they are the only ones the program can reach.  Pages and first-fit already rewrite their own "in use" (`tal` in use), which is `live_target`; the change touches `PagesDone`/`FFDone`'s coverage step and `FFWInv.mpre_d`. |
| G47 | (1b) `reachable ⊆ kept`, (3c), T1 | `ERead` pushes field `i` as a root, also for a **no-scan** block.  No-scan fields hold any bytes, and the byte representation decodes words by their bits (`Abs.absv`), so a string can read as `VPtr (Major a)` with `a` free or garbage.  It becomes a root, so reachable, but it is not kept. | `mutator_ok` for `ERead` asks `scannable (tag_of …)`; a byte read is not a root (OCaml boxes a float it reads, and an int is not a pointer).  If byte reads should be observable for T1, add an event that records the value outside the roots.  The witness runs read only A (scannable), so they are unchanged. |
| G48 | `gc_correct_local` only: (2) "o is in use after", (5) at the last point | After `EAlloc`, the Fill changes the concrete heap.  "o is in use" needs `free_hd_at` at the **new** state `st'`.  `run_hyps` gives `free_hd_at` only at the states before each event, so after the run's last allocation nothing says the Fill kept o in use. | `hyps_at` for `EAlloc` also asks `forall h. free_hd_at r a st' h' h` at the allocator's result, or `run_hyps` asks the point hypotheses at `i ≤ length es`.  `hyps_of_ok` still proves it. |
| G49 | `inv` at every point (1b), after `EWrite` | `write_post` fixes the words that are fields; `inv_frame_rel` compares **every** word.  With a representation whose model is the heap itself (faithful, not canonical), a barrier may change a header word's body, and an allocator's `inv` may read it.  Both meet their contracts, and `inv` is lost. | `write_post`: every word other than `o+1+i` is unchanged (or `inv_frame_rel` compares field words only).  The byte barrier works on `cabs`, which is canonical, so this costs one lemma there and in the toy barrier. |
| G50 | `inv` (1b), (5), after `EStart` and `ESlice` | `mark_start_post` and `mark_slice_post` give `colours_only` and the tricolour invariant.  They allow any colour change of a block outside `snap ∪ allocd`, for example garbage white → blue.  `inv_frame_rel` allows only darkening of blocks in use.  For pages and first-fit, blue *is* free, so a block would leave use without the sweep, which breaks (5). | Both posts add "darken only": a block whose colour changes becomes grey or black.  akhil's mark, `ByteMark` and the toy mark only darken. |
| G51 | T1 only (not a clause) | (0)–(6) say nothing of young objects' contents across steps, or of a promoted copy's fields; the read clause gives the read, but nothing ties a copy to the object it replaces.  T1 needs both. | Prove T1 from the run invariant, which has the contracts (§16.7).  Optionally add a clause: at `Done`, each copy holds the forwarded young fields (it is in `minor_post_done`). |

No other clause looked unprovable.  Two points were checked and are
**fine**, because the argument is not obvious:
- *Tricolour across allocation.*  A path from a grey block through white
  ones could pass through a free block that allocation destroys.  It
  cannot: grey is in `snap ∪ allocd`, and that set is `closed`, so every
  white block on such a path is live and in use, and allocation leaves it
  alone.
- *`young_sound` while sweeping.*  A young object holding a pointer to a
  block the sweep is about to free would break it.  It cannot happen: a
  pointer stored before the cycle makes the target an `outside_ref` at the
  start (so in `snap`, black); one stored during the cycle was reachable,
  so kept.

### 16.3 The run invariant

`rinv x` is a conjunction of sealed parts (`opaque_to_smt`, one
introduction and one elimination lemma each, as in `FFWInv` and the
lessons of §14/§15).  Every part is stated on `vw x` and is
`agree`-invariant.

| Part | Content | Used for |
|---|---|---|
| R1 | `has_view x`, `well_formed`, `young_ok`, `c.a.inv x.ph x.w.cmaj x.ast` | (1b); every contract's precondition |
| R2 | `kept ⇒ live_target`.  While sweeping: in use and swept ⇒ live; not live and in use ⇒ white | (1a) at `EMinor`, (5), (3b) |
| R3 | `reachable ⊆ kept`; every pointer in a root or a pointer field of a kept block resolves (major: to a kept block; young: in the nursery); every major pointer in **any** young field resolves to a kept block | (1b), `young_sound`, `sound_value` for Fill and writes |
| R4 | Every young pointer in a field of a `live_target` block or of a young block resolves; `young_follow_ok`; `rem_covers` over `live_target` (G46) | `minor_pre`; no dangling pointer after the reset |
| R5 | Colours. Idle: no dark block. Marking: `tricolour (snap) (allocd)`, `closed (snap ∪ allocd)`, `snap ∪ allocd` in use. Sweeping: no grey block, a live unswept block is black | `mark_start_pre`, `mark_slice_pre`, `dark_closed` and `no_grey` at the hand-over, the sweep's preconditions |
| R6 | `snap ⊆ in use` at the start; `allocd` in use | (3b), (6) |

`partition` (5) is derived from R1, R2 and R6 and tiling: each word is
covered by exactly one block; a block is free or in use; in use is kept or
pending by R2.

### 16.4 Clause by clause

Sizes are new lines of F*; risk is the chance that the step needs a
reformulation or a long fight with the solver.

| Clause | Strategy | Invariants | Lemmas needed | Reused | Size | Risk |
|---|---|---|---|---|---|---|
| (0) | `init_at` at `n` (`run_ok` gives `size_ok`), `yinit_ok`; agree to `vw` | — | `init_view` | `RunFacts.at_zero`, `Rep.repr_agree` | 60 | low |
| (1a) | per event: `alloc_post` (`same_block`) + Fill disjoint from in-use words; `write_post`; `colours_only`; sweep post (black → white, same contents; outside the region unchanged); minor post on `live_target` (R2) | R1, R2 | `fill_disjoint`, `kept_live_target` | `FFWInv` step patterns (`*_use_g`) | 350 | low |
| (1b) | R1–R6 carried by the step lemmas; `concl_point` read off | all | one step lemma per event family (§16.6) | `ToyComps.reach_within`/`not_reachable` (reachability stays in a closed set); `RunFacts` `*_wheq` lemmas, restated for `agree` | 2200 | **high**: minor (G46), write (tricolour) |
| (2) | `alloc_post` + `binit_m` + `free_hd` at `st'` (G48) | R1, R3 (Fill values are `sound_value`) | `alloc_step_ok` | `FFWInv.inv_alloc`/`post_fill` shape | 250 | low |
| read | `faithful_major`/`faithful_young` `reads_model`; `mutator_ok` gives block and index | — | `read_ok` | — | 40 | low |
| (3a) | per-word induction from `s`: a word of a dead object is in that object (pending, header unchanged), or free, or covered by an allocated block in use | R2, R5, R6 | `dead_word_step` per event | pattern of `Pages.Cycle.cycle_lossless` / `words` (structure only) | 400 | medium |
| (3b) | ⇐: kept persists (1a); ⇒: at done nothing in use is unswept (`sweep_done`), swept in-use blocks are live (R2) | R2, R6 | `survivors` | `Pages.Cycle.cycle_survives` (structure) | 150 | low |
| (3c) | o unreachable at t: if not live in cycle k it is pending, freed by `j1`; if live, either it leaves use, or it stays in use and stays unreachable (no event adds an edge to an unreachable block: values are reachable now) and is pending in cycle k+1 | R3, plus (3a)/(4) | `unreachable_stays` (reach_within with the set "reachable now ∪ new"), `pending_freed` | `ToyComps.not_reachable` | 400 | medium (needs G47) |
| (3d) | `minor_post_done`'s first clause on `vw x` | R4 (`minor_pre`) | — | — | 30 | low |
| (4) | ⇐: not reachable at `s` ⇒ not in `snap` ⇒ pending ⇒ freed by its sweep step; ⇒: reachable at `s` ⇒ kept to `j+1` | R2, R6, (3a) induction | `freed_iff` | `Pages.Cycle.cycle_addresses_lossless` (structure) | 200 | low |
| (5) | partition from tiling + R2; moves: per event, from the posts (`inv_frame_m` gives `free` unchanged for write/mark; alloc/minor only add; sweep only frees) | R1, R2 | `word_xor` (free word xor in-use word, from tiling), per-event move lemmas | `PagesAllocOk` generic word lemmas (already allocator-free) | 400 | medium (needs G50, G49) |
| (6) | slice: contract; other events while marking: allocation and copies are black (`colour_at`), the barrier only greys a live white block, the rest keep colours; sweeping: contract, and `step` keeps `p` | R5, R6 | `no_increase_*` per event | — | 250 | low |

### 16.5 The cycle clauses

`concl_cycle` and `concl_two_cycles` are about indices of the run, not one
configuration.  They are proved by a second induction from `s` to `j`
with `x0 = at s` fixed, carrying the per-object statement
`dead_or_reused x0 x o`: o is in use at `s` and not in the snapshot, and
either o is pending with its header from `x0`, or each word of o in `x0` is
free or covered by an allocated block in use.  (3c) applies (3a)/(4) to the
two cycles and the "stays unreachable" lemma to the stretch between them.

### 16.6 Modules, order, and estimates

| # | Module (new) | Content | Lines | Risk |
|---|---|---|---|---|
| 0 | spec fixes in `Iface`, `Run` | G46, G47, G48, G49, G50; re-proofs in `ByteBarrier`, `ByteMark`, `ToyMark`, `ToyMinor`, `PagesDone`/`FFDone` (coverage step), `Broken`, `FFWInv.mpre_d`; recheck of every `GC.Spec.Top` module at 3 seeds | ±400 changed | medium: the minor chain is long (~2900 lines per instance), but only its use of `rem_covers` moves |
| 1 | `Top.Views` | `agree`-invariance of `resolve`, `reach`, `yreach`, `mlive`, `in_use`, `covers`, `kept`, `partition`; choice lemmas for `vw` | 400 | low |
| 2 | `Top.RInv` | R1–R6, sealed; `init` (0) | 300 | low |
| 3 | `Top.Words` | tiling ⇒ word xor; `fill_disjoint`; partition from R1/R2/R6 | 300 | low |
| 4 | `Top.StepMut` | `ERead`, `ERoots`, `EYoungAlloc`, `EWrite (Young)`; read clause | 350 | low |
| 5 | `Top.StepSweep` | `EHandover` (`dark_closed` from tricolour + no grey), `ESweep`, `EEnd` | 450 | medium |
| 6 | `Top.StepMark` | `EStart` (`mark_start_pre` from R5/`free_white`), `ESlice`; `inv_frame_rel` from darken-only | 400 | medium |
| 7 | `Top.StepAlloc` | `EAlloc`: (2), tricolour and closed with a new black block | 500 | medium |
| 8 | `Top.StepWrite` | `EWrite (Major)`: barrier, `wpath` surgery for the cut edge, closed, `rem_covers` | 600 | **high** |
| 9 | `Top.StepMinor` | `EMinor`: `minor_pre` from R1–R4; reachability after the reset (old young refs gone, copies new); R4 re-established (no young pointer left in a `live_target` block); tricolour with black copies | 700 | **high** |
| 10 | `Top.Point` | `concl_point`, `concl_step` assembled from 4–9 | 200 | low |
| 11 | `Top.Cycle` | (3a), (3b), (4) | 700 | medium |
| 12 | `Top.TwoCycles` | (3c) | 400 | medium |
| 13 | `Top.Correct` | `gc_correct_local`, `gc_correct`, `seq_of_inc`; corollaries for `tc`, pages (`pc`), first-fit (`fc`) | 150 | low |
| 14 | `Top.Stw` | T2 (§16.7) | 400 | medium |
| 15 | `Top.Transparent` | T1 (§16.7) | 700 | **high** (statement) |

**Order.**  0, then 1–3, then the step lemmas from the easy ones to the
hard ones (4, 5, 6, 7, 8, 9), each with its own clauses of `concl_step`,
then 10, 11, 12, 13.  T2 (14) needs only (4) and the measures; T1 (15)
needs the invariant and comes last.  Steps 8 and 9 are independent of each
other and of 11–12 once 1–3 exist.

**Totals.**  About 6 500 new lines and about 400 changed, roughly the size
of the first-fit instance (stage 2c).  Checking: the new modules are
small-context by design; the full 3-seed sweep of `GC.Spec.Top` after the
spec fixes is the long part (several hours of machine time, as in §13.6
and §15.6).

**Risks, and what limits them.**
- Quantifier load in R1–R6: seal each part, one elimination lemma per use
  (§14, lessons of `FFWInv`).
- `vw`'s choice: every lemma is about an arbitrary view that agrees; module
  1 isolates it.
- Minor step (9): the argument that no young pointer survives in a
  `live_target` block needs R4 to say "resolves", which needs every stored
  young value to have resolved (`value_ok`) and the nursery to change only
  by allocation in free space (`young_free`).  Both are in the contracts.
- Barrier step (8): the Yuasa argument on `wpath` is the one new
  graph-theoretic proof; `ToyMark.slice_path` is the nearest existing
  induction over `wpath`.

### 16.7 T1 and T2

Neither is defined in the specification yet; this is how each would be
stated and proved.

**T2: equivalence with stop-the-world at the cycle's start.**  For a cycle
`s..j` of a run, let `stw` be the run that stops at `s` and completes a
cycle with no other event: `EStart`, slices until `mark_done`,
`EHandover`, sweep steps until `done`, `EEnd`.
1. *It exists.*  (6) gives finite measures: a slice strictly decreases the
   white-then-grey live sets, and a sweep step strictly shrinks the
   unswept blocks below `size`.  A sweep that is not done always has an
   unswept block below `size`: otherwise `sweep_step_at`'s post (a region
   below `size`) could not hold.  So well-founded induction builds the
   event list.  This needs the contracts at those steps: from
   `components_ok` (`hyps_of_ok`).  Under `gc_correct_local` it is a
   hypothesis on the stop-the-world run.
2. *It frees the same objects.*  Apply (4) to both runs, which share the
   prefix up to `s`: each frees exactly `stw_freed (at s)`.
3. *Survivors.*  By (3b), the incremental run keeps `snap ∪ allocd` and
   the stop-the-world run keeps `snap` (`allocd` is empty: no allocation,
   and no minor collection, inside it).  The difference is exactly the
   floating garbage of kind (ii), §2.3; (3a) gives the word-level form.
Size about 400 lines, medium risk (the list construction under the
measure).

**T1: transparency.**  The collector is invisible to the program: every
read returns what it would return in a run without collection.
- *Statement.*  A reference semantics runs the mutator events on an
  unbounded store of objects named by allocation order, and ignores the
  collector events.  T1 says there is, at every point `i`, an injective
  map `ι_i` from the reference objects reachable at `i` to blocks
  (major or young).  Roots correspond through `ι_i`, the fields of every
  reachable object correspond (pointers through `ι_i`, with infix offsets
  kept, as `fwdv` keeps them), and every `ERead` returns the image of the
  reference read.  Allocation failures (`NoRoom`, `OutOfRoom`) are
  observable, so T1 is stated for runs where they do not happen, or the
  reference semantics fails at the same allocation.
- *Proof.*  A simulation along the run.  `ι` changes only at `EMinor`
  (composed with `fwd`) and at allocations (extended).  The invariant
  needs the contents of kept blocks ((1a)), of new blocks ((2)), of young
  objects (the `yrepr` contracts) and of copies (`minor_post_done`).  The
  last two are not in (0)–(6) (G51), so T1 is proved from the run
  invariant, not as a corollary of `conclusions`.  Reachable ⊆ kept (R3)
  keeps the domain of `ι` alive.  G47 must be fixed first: otherwise a byte
  read can name an object that is not in `ι`'s image.
- Size about 700 lines.  The risk is in the statement (choosing the
  reference semantics so it is obviously right), not in the proof.

### 16.8 What is reused, and what is not

- **The witness modules.**  `RunFacts` (`at_succ`, `exec_append`,
  `run_hyps_of_ok`, the `*_wheq` reachability lemmas) is used directly.
  `FFWInv`'s generic helpers (`frame_use_g`, `sweep_use_g`, `done_use_g`,
  `rel_g`) are the pattern for the allocator's invariant in every step
  lemma; they should move to a generic module.  After the proof, the
  witness runs give concrete instances of every conclusion: for example
  (3d) at event 12 of `FFWInc` must agree with `promoted_12`.  They must be
  rechecked after the spec fixes (G46, G48 and G50 change hypotheses they
  prove).
- **The page incremental-cycle theorems** (`Pages.Cycle`, `.Carried`,
  `.Sweep`, `.Write`): byte-level and page-specific, stated over the page
  state, not over the interfaces.  They cannot be applied to the generic
  proof.  What carries over is their structure: the account `ccycle_inv`
  is R2/R6 with the partition, `cycle_survives` is (3b),
  `cycle_addresses_lossless` is (4), `cycle_lossless`/`words` is (3a), and
  `Cycle.Write.barrier_mark_inv` is the write step's SATB argument.  After
  the proof, they are corollaries of `gc_correct` for the page instance up
  to G17's abstraction, which is a useful cross-check.
- **akhil's lemmas.**  None is needed by the generic proof: it is over the
  model, and his lemmas are already used, read-only, inside the instances'
  contract proofs (stages 2b and 2c).  They stay untouched.
- **The toy.**  `ToyComps.reach_within`/`not_reachable` (reachability stays
  inside a closed set holding the outside refs) is the tool for R3 and
  (3c); `ToyMark.slice_path` is the nearest existing induction over
  `wpath`.

### 16.9 The five fixes, applied

The fixes of §16.2 (G46–G50) are now in the specification, as proposed.
G51 is about T1 and needs no change to the specification.

| # | Change | Where |
|---|---|---|
| G46 | `rem_covers a ph st h w`: only the old-to-young pointers of `live_target` blocks must be remembered.  It now takes the phase. | `Iface.rem_covers`, `minor_pre` |
| G47 | `mutator_ok_w` for `ERead`: `ptr_field` of the block (a scannable block, the index in range) and the block reachable. | `Run.mutator_ok_w` |
| G48 | `hyps_at` for `EAlloc` with result `Ok o`: also `forall h2. free_hd_at r a st' h' h2` at the allocator's new state; `hyps_of_ok` proves it from `allocator_ok`. | `Run.hyps_at`, `hyps_of_ok` |
| G49 | `write_post`: every word other than `o+1+i` is unchanged.  The colour change of the darkened block is in the header (`darkened`), so it is unaffected. | `Iface.write_post` |
| G50 | New `darken_only h h'` (a block whose colour changes becomes grey or black), in `mark_start_post` and `mark_slice_post`. | `Iface` |

Proof changes they caused:

- `ToyMark`: the start and the slice give `darken_only`, from
  `start_colour` and `slice_colour`.  The byte mark reuses the toy's lemmas,
  so `ByteMark` needed nothing for it.  The toy barrier writes with
  `set_field`, which already leaves every other word alone, and the byte
  barrier goes through it.
- `PagesDone2.old_cov`, `FFDone2.old_cov`: the block is also
  `live_target`.  Their only caller, `old_field`, already had it.
- `Broken.rem_cov`, `FollowWitness.rem_ok`: idle, where `live_target` is
  in use.  `FFWInv.rem_heq` takes the phase and carries the colour too.
- `Vacuity.read_major_ok` and `FFWRun.ok_read` ask the read block to be
  scannable; the witness runs read field 0 of A, which is scannable.
  `ok_read`'s proof is split (`en_read`), as `ok_write` was.
- `ByteMark.yfield_intro`: the step's recursive call now comes before the
  sequence facts are in context.  Nothing in the lemma changed, but the
  old order timed out at seed 0 once `Iface` changed (`j < n - 1` from
  `j < n` and `j <> n - 1`).

Every broken component is still rejected: the contracts only got stronger
for components (G49, G50) or weaker on the minor collection's input (G46),
and no rejection used the clauses that changed.

**Checking.**  All 88 `GC.Spec.Top` modules were rechecked in dependency
order, each from a removed `.checked` file, without `--retry`, at Z3 seeds
0, 1 and 2 (the three seeds in parallel, two jobs each).  Rlimits are at
most 40, with no admits and no assumes.  No module outside `GC.Spec.Top`
depends on them.

| Z3 seed | modules | errors | warnings | slowest |
|---|---|---|---|---|
| 0 | 88 | 0 | 0 | `FFWInc`, 1039 s |
| 1 | 88 | 0 | 0 | `FFWInc`, 1055 s |
| 2 | 88 | 0 | 0 | `FFWInc`, 1065 s |

This covers the components' contracts (`ToyComps.toy_components_ok`,
`PagesComps.pages_components_ok`, `FFComps.ff_components_ok`), the nine
rejections (`Broken`), and every hypothesis of both theorems on the witness
runs (`Vacuity`, `FFWSeq`, `FFWInc`, with `FollowWitness`).

### 16.10 Checkpoint A: views, the run invariant, and the first step lemmas

Proved, with no admit or assume, rlimits at most 40:

| Module | Content |
|---|---|
| `Top.Views` | `agree`-invariance of blocks, headers, fields, `covers`, `resolve`, edges, `well_formed`, `young_ok`, in-use and free words, `live_target`, `sound_value`; of `reachable`, `yreachable`, `minor_live`, `value_ok` (worlds that agree, `wagree`); of `wpath`, `tricolour`, `closed` and the mark's measures.  `vw_agree`: every world that views `x` agrees with `vw x`. |
| `Top.Words` | Tiling: one block per word, so a word is free or in use, not both (`word_xor`).  The Fill and a store change only their block's fields.  `resolve_keep`: a pointer to a block that the next heap keeps resolves to it there.  `reach_within`.  The nursery's allocation and store keep every young pointer resolving. |
| `Top.RInv` | R1–R6 as six sealed parts (`r_heap`, `r_reach`, `r_res`, `r_young`, `r_col`, `r_live`), each moved between agreeing worlds; `rinv_init` gives (0) and the invariant of the initial configuration; `point_of_rinv` gives `concl_point` ((1b), the partition (5)). |
| `Top.StepBase` | What a step lemma proves (`step_out`: the invariant, every clause of `concl_step`, and `rback`, "no object in use becomes reachable", for (3c)), on the world the contract hands back; `step_out_intro` moves it to `vw x'`.  `heap_step`: the reachability parts of the invariant after any step that keeps the reachable blocks. |
| `Top.StepMut` | `ERead` (both kinds), `ERoots`, `EYoungAlloc`, `EWrite (Young _)`, and the read clause. |
| `Top.StepSweep` | `EHandover` (`dark_closed` from the tricolour invariant and no grey block), `ESweep`, `EEnd`. |
| `Top.StepMark` | `EStart`, `ESlice`, under the hypotheses of G52 below. |

The invariant differs from §16.3 in two details.  R3 asks every pointer of
a root, of a reachable block or of any young block to *resolve*; that its
target is kept follows (`point_of_rinv`).  R4 asks the young pointers of
`live_target` blocks to resolve and be remembered, which is what the minor
step needs.

**New gap G52.**  `darken_only h h'` quantifies over every address, also
past the heap's end.  Faithfulness fixes a model's headers below `size`
only, so a mark that meets its contract may give a model whose header past
the end changes colour (to grey).  `inv_frame_rel` then fails: it asks a
recoloured address to be a block in use.  So neither the start nor a slice
can be shown to keep the allocator's invariant.  Proposed fix: in
`darken_only`, `col_of h' o =!= col_of h o ==> is_block h o /\ dark (col_of
h' o)` ("a *block* whose colour changes", as §16.2 says).  The toy mark
recolours only blocks (a header that resolves, or the chosen grey block),
so the fix should cost a few lines in `ToyMark`, and `ByteMark` reuses it.
Until the fix is approved, `StepMark.start_step` and `slice_step` take the
missing guarantee as explicit hypotheses (`start_blocks_only`,
`slice_blocks_only`); with the fix they follow from the posts.

*Applied (approved after checkpoint A):* `darken_only` now reads
`col_of h' o =!= col_of h o ==> is_block h o /\ dark (col_of h' o)`.
`ToyMark` proves it with `start_darken` and `slice_darken` (a recoloured
address resolves, or is the grey block the slice scans), and `ByteMark`
reuses them.  The two hypotheses are gone: `start_step` and `slice_step`
assume only the step's contracts.

**Left.**  The step lemmas for `EAlloc`, `EWrite (Major _)` and `EMinor`
(checkpoint B), then `Point`, `Cycle`, `TwoCycles`, `Correct`, T2 and T1.
Checking the contracts against the invariant for those three found no
further gap: G48 gives allocation status after the Fill, G49 the barrier's
other words, G46 and R4 a minor collection's remembered set.

**Checking.**  The seven new modules were checked in dependency order, each
from a removed `.checked` file, without `--retry`, at Z3 seeds 0, 1 and 2.
No existing module changed.

| Module | lines | seed 0 | seed 1 | seed 2 |
|---|---|---|---|---|
| `Views` | 323 | 3 s | 3 s | 3 s |
| `Words` | 273 | 3 s | 2 s | 3 s |
| `RInv` | 323 | 4 s | 4 s | 4 s |
| `StepBase` | 392 | 6 s | 6 s | 6 s |
| `StepMut` | 368 | 50 s | 41 s | 47 s |
| `StepSweep` | 362 | 25 s | 24 s | 25 s |
| `StepMark` | 337 | 44 s | 46 s | 43 s |

### 16.11 Checkpoint B: allocation, the barrier write, the minor collection

Proved, with no admit or assume, rlimits at most 40.  Every step lemma has
the shape of §16.10 (`rinv x /\ hyps_at c x e /\ ... ==> rinv x' /\
concl_step x e x' /\ rback x x'`), with no hypothesis beyond the step's
contracts and the mutator's obligations.

| Module | Content |
|---|---|
| `Top.StepFacts` | What the three steps keep of a block in use: `keepsy` (same header, every field that is not a young pointer).  `resolve_keepy`: a pointer to such a block resolves as before.  `lpath_keepy`: paths from a live grey block through white ones survive when the live set is closed and kept.  `one_word_resolve`: a store into a field of a block that is not a closure leaves every resolution.  `copy_infix`: a forwarded infix pointer resolves to the copy. |
| `Top.StepAlloc` | `EAlloc`, clause (2).  No room: nothing changes.  Room: only `o` is new; it is kept (in use and allocated in the cycle) and coloured by `colour_at`, so each phase's colour invariant holds with `o` in `allocd`; the allocator's invariant after the Fill comes from the post with sound values (G48 gives allocation status after the Fill). |
| `Top.StepWrite` | `EWrite (Major _)`.  Resolution is unchanged, nothing new is reachable, `inv_frame_rel` holds (G49).  Snapshot-at-the-beginning (`w_lpath_rec`): along a path from a live grey block through white ones, each block is greyed by the barrier or still reached by such a path, because the only edge a store cuts leads to the block the barrier greys.  Clause (6): a greyed live block strictly decreases the measure. |
| `Top.StepMinor` | `EMinor`, clause (3d).  `minor_pre_of`: the precondition from the invariant.  Every young pointer of a root, of a block the program may use (remembered: `LRem`), or of a traced young object (`LStep`) is forwarded to a copy (`fv`), so after the reset none is left where the invariant looks.  Reachable after: reachable before, or a copy.  Out of room: the run stops. |

**Change to the invariant.**  R5 while marking is now stated over blocks
in use (`RInv.tri_iu`), with grey-to-white paths that start at a *live*
grey block (`lpath`).  The allocation's and the minor collection's
contracts leave the colours of free blocks open, so the all-blocks
`tricolour` could not be carried across them.  The two forms are
equivalent when free blocks are not dark (`tricolour_of_tri`,
`tri_of_tricolour`), and `free_white` (a hypothesis of every step) gives
that at the steps that need the full form (`ESlice`, `EHandover`).  This
is not a gap in the specification.

**Robustness.**  `ByteMark.young_intro` timed out at seeds 0 and 1 after
the G52 change, the same failure as `yfield_intro` in §16.9; the same
reordering fixed it (the recursive call first).

**No new gap.**

**Left.**  `Top.Point` (one step lemma per event, the induction over the
run, `concl_point` at every point), `Top.Cycle` ((3a), (3b), (4)),
`Top.TwoCycles` ((3c), from `rback`), `Top.Correct`, then T2 and T1.

**Checking.**  Everything that depends on `Iface` was rechecked at Z3
seeds 0, 1 and 2 without `--retry`, in dependency order from removed
`.checked` files: the 88 modules of §16.9 (toy, pages and first-fit
components, the broken components, the witness runs) and the eleven new
modules.  All are clean.  The slowest existing module is `FFWInc` (654 s,
654 s, 387 s).

| New module | lines | seed 0 | seed 1 | seed 2 |
|---|---|---|---|---|
| `Views` | 323 | 2 s | 2 s | 2 s |
| `Words` | 273 | 2 s | 2 s | 2 s |
| `RInv` | 410 | 3 s | 3 s | 3 s |
| `StepBase` | 392 | 3 s | 3 s | 3 s |
| `StepMut` | 368 | 29 s | 30 s | 33 s |
| `StepSweep` | 375 | 19 s | 19 s | 22 s |
| `StepMark` | 322 | 49 s | 51 s | 51 s |
| `StepFacts` | 211 | 5 s | 4 s | 4 s |
| `StepAlloc` | 632 | 122 s | 120 s | 114 s |
| `StepWrite` | 498 | 58 s | 53 s | 56 s |
| `StepMinor` | 754 | 27 s | 27 s | 27 s |

### 16.12 Checkpoint C: every point and every cycle

Proved, with no admit or assume, rlimits at most 40.

| Module | Content |
|---|---|
| `Top.Point` | `step_ok`: one lemma for every event, dispatching to the step lemmas.  `rinv_at`: the invariant at every point of a run, by induction from `rinv_init`.  `points_ok`: clause (0), `concl_point` at every point ((1b), (5)), `concl_step` at every step ((1a), (2), the read clause, (3d), (5), (6)).  Hypotheses: `faithful`, `run_ok`, `run_hyps` (sealed as `run_pre`). |
| `Top.Cycle` | `cycle_ok`: `concl_cycle` for every cycle `s..j` of such a run: (3a), (3b), (4). |

**The cycle argument.**  Inside a cycle the snapshot is fixed and the phase
is not idle (`in_cycle`); at its end the sweep is done, so a block in use
is live (`done_live`).
- (3b): in use at the end is live (`sweep_done` and R2), and live is in use
  (R6).  The end changes only the phase.
- (4): a snapshot object is live, so in use, throughout.  Conversely an
  object in use throughout and outside the snapshot is never allocated in
  the cycle (`never_allocd`: only blocks that were not in use are), so it
  is not live at the end, though in use: impossible, so it is freed.
- (3a): each word of such an object is, at every point, a word of the
  pending object, a free word, or a word of a block allocated in the cycle
  and in use (`word_ok`, `word_step`).  At the end the first is impossible.

**Change to the step lemmas.**  `concl_step` does not say what the cycle
argument needs of each step, so every step lemma now also proves `cyc`:
- the heap's size stays fixed;
- an allocated block was not in use before;
- a block that comes into use is allocated;
- a block that stays in use keeps its size;
- a block that leaves use leaves its words free.

It is a fifth sealed part of `step_out` (`cs_cyc`), moved to `vw x'` like
the others.  Each step proves it from the facts it already had (alloc:
`a_cyc`; sweep: `sw_cyc`, with the sweep post's "white becomes free";
minor: `n_cyc`; the others with `cyc_same`/`cyc_agree`).

**No new gap.**

**Left.**  `Top.TwoCycles` ((3c)): from (4) at the second cycle and
`rback` (an unreachable object in use stays unreachable), which every step
lemma proves.  `Top.Correct`: `gc_correct_local` (from `points_ok`,
`cycle_ok` and (3c)), `gc_correct` (by `gc_correct_local_implies`), for
both styles (the style is never used).

**Checking.**  The changed step modules and the two new modules, in
dependency order from removed `.checked` files, without `--retry`.  No
module outside the proof changed, so the 88 modules of §16.11 stand.

| Module | lines | seed 0 | seed 1 | seed 2 |
|---|---|---|---|---|
| `StepBase` | 446 | 4 s | 4 s | 4 s |
| `StepMut` | 369 | 32 s | 32 s | 32 s |
| `StepSweep` | 406 | 18 s | 18 s | 18 s |
| `StepMark` | 324 | 45 s | 46 s | 44 s |
| `StepAlloc` | 651 | 124 s | 118 s | 114 s |
| `StepWrite` | 502 | 59 s | 59 s | 59 s |
| `StepMinor` | 774 | 25 s | 25 s | 27 s |
| `Point` | 112 | 4 s | 4 s | 3 s |
| `Cycle` | 345 | 26 s | 28 s | 28 s |

(`Views`, `Words`, `RInv`, `StepFacts` are unchanged and were rechecked in
the same runs, 2-3 s each.)

### 16.13 Checkpoint D: two cycles, and the theorem

**`Top.TwoCycles` (66 lines): (3c).**  `unreach_at`: an object in use and
unreachable at `t` that stays in use through `t'` is unreachable at `t'`
(induction with `rback` from each step).  `two_obj`: either the object
leaves use somewhere in `(t, s2]`, or it is in use and unreachable at `s2`,
so in the stop-the-world set at `s2`, and by (4) of the cycle `s2..j2` it
leaves use at some `u + 1` with `s2 <= u <= j2`.  `two_cycles_ok` needs
only `j1 < s2`; the hypothesis that no cycle starts between the two is not
used.

**`Top.Correct` (63 lines): the theorem.**  `run_correct`: under
`faithful c.r /\ run_ok c sty n ny es /\ run_hyps c n ny es`,
`conclusions c n ny es` (from `points_ok`, `cycle_ok`, `two_cycles_ok`).
`gc_correct_local_ok c sty : Lemma (gc_correct_local c sty)` and
`gc_correct_ok c sty : Lemma (gc_correct_local c sty /\ gc_correct c sty)`
(the latter by `gc_correct_local_implies`), for every `c` and `sty`;
`gc_correct_both c` names both styles.  No hypotheses beyond the stated
ones: the lemmas have no `requires`, and the propositions carry their own
(`faithful c.r` for the local form, `components_ok c` for `gc_correct`).
The witness runs of `FFWSeq`/`FFWInc` (`ff_vacuity_sequential`,
`ff_vacuity_incremental`) meet these hypotheses, one run for each style.

**No new gap.**  No existing module changed.

**Checking.**  The two new modules, from removed `.checked` files, without
`--retry`, on the caches of §16.12:

| Module | lines | seed 0 | seed 1 | seed 2 |
|---|---|---|---|---|
| `TwoCycles` | 66 | 3 s | 4 s | 3 s |
| `Correct` | 63 | 4 s | 3 s | 4 s |

**Left.**  T1 and T2 (§16.7).

### 16.14 T2: equivalence with stop-the-world at the cycle's start

**Statement (`Top.Stw`, 70 lines, new).**  `stw_tail a b` is `EStart`,
`a` slices, `EHandover`, `b` sweep steps, `EEnd`.  `stw_run es s es'`:
`es' = take s es @ stw_tail a b` for some `a`, `b`.  `stw_equiv c n ny es
s j es'`, with `j' = last es'` and `x0 = at es s`:
- `is_cycle es' s j'`;
- the runs agree up to `s`;
- they free the same objects (`freed_in`);
- the stop-the-world run keeps exactly `reachable (wv x0)`;
- the incremental run keeps those and `allocd` at `j` (floating garbage
  of kind (ii)).

`t2 c sty`: under `components_ok c`, for every run `es` of style `sty`
and every cycle `s..j` of it, some `es'` with `stw_run`, `run_ok c sty`
and `stw_equiv`.  `t2_local c sty`: under `faithful c.r`, for runs `es`,
`es'` with `run_ok` and `run_hyps` (the contracts at the steps of both),
`stw_run` and a cycle `s..j` of `es`, `stw_equiv`.

**Proof.**
- `Top.RunApp` (140 lines): `es' = take s es @ tl` is `es` up to `s`
  and `exec (at es s) tl` after; `tail_ok` (each step's `run_ok` and
  `run_hyps` obligations) makes `es'` a run (`run_of_tail`).
- `Top.StwBuild` (268 lines): `stw_build`.  From an idle configuration
  with `rinv`, under the contracts, a whole cycle runs: slices while the
  mark is not done, each strictly decreasing `mm` (white, then grey, live
  objects below `size`, encoded as `white * (size+1) + grey`, from (6)'s
  `mark_decreases`); then sweep steps while the sweep is not done, each
  strictly decreasing the count of unswept addresses below `size` (from
  (6)'s region below `size`).  The size is fixed (`cyc`).  Counting is
  over props, with `strong_excluded_middle` (`cnt`).
- `Top.T2` (202 lines): the cycle of `es'`; the stop-the-world run
  allocates nothing (`stw_allocd`: slices, handover and sweep steps keep
  `allocd`); each cycle keeps its snapshot (= reachable at `s`) and its
  `allocd` ((3b), `keeps`); (4) on both runs, at the same `at s`.
  `t2_local_ok`, `t2_ok`, `t2_both`: no `requires`.

**No new gap.**  Nothing existing changed except the build roots
(`Top.Correct` and `Top.T2` added to `ROOT_MODULES`).

**Checking** (from removed `.checked` files, no `--retry`):

| Module | lines | seed 0 | seed 1 | seed 2 |
|---|---|---|---|---|
| `Stw` | 70 | 2 s | 2 s | 2 s |
| `RunApp` | 140 | 32 s | 15 s | 9 s |
| `StwBuild` | 268 | 33 s | 30 s | 31 s |
| `T2` | 202 | 34 s | 33 s | 34 s |

**The build.**  `Top.Correct` was not reachable from any root, so the
proof was not checked by `gmake verify`; it and `Top.T2` are now in
`ROOT_MODULES`.  `gmake -j6 verify` from an empty `_cache` in a scratch
worktree (default `--retry 3`, as CI): 506 cache files, 373 modules
verified, 0 errors, 59 min; then the four T2 modules on top, 32 s.

### 16.15 T1: the statement

`Top.Transp` (definitions only; typechecks at seeds 0, 1, 2; not
in `ROOT_MODULES` until approved).
- **Reference semantics.**  `rstore`: objects named by allocation order,
  never moved, freed or refused; `rval` = a word held as is, or `RPtr k d`
  (object `k`, infix offset `d`); `revent` = `RAlloc young tag vs`,
  `RWrite`, `RRead`, `RRoots`; `rstep`, `rat prog m`.
- **Renaming.**  `ι i : nat -> option ptr`.  `vcorr`: an integer is
  itself; a pointer is the renamed block's address plus the offset, and
  resolves to it; a no-scan word is held as is.  `scorr ι x r`: roots one
  by one; every *visible* block (reachable major, `yreachable` young: what
  the program may name) holds one reference object with the same tag,
  size and fields; every reachable reference object is in a visible
  block.  Visible is wider than reference-reachable: `value_ok` lets the
  program name a major object reachable only from a dropped young object,
  and the collector keeps it.
- **`transparent es prog ι`.**  At every point, `scorr` with the
  reference store after the program events so far (`mc`); every program
  event is the next reference event renamed (`ev_corr`) and legal
  (`rok`); every read value is the reference read, renamed.
- **Failures.**  The reference never fails.  `no_fail es`: no `EAlloc`
  of `es` returns `NoRoom` (a young allocation cannot fail in a run, it
  must be enabled; an `EMinor` that returns `OutOfRoom` ends the run).
  The replay may fail where `es` does not (other free space, other
  placement): it may stop just before a program event that is an
  allocation no collection can make room for (`stuck`):
  - (S1) a major allocation the allocator refuses right after a minor
    collection (the nursery is then empty) followed by a whole
    stop-the-world cycle (which then frees every object not reachable
    from the roots);
  - (S2) a young allocation with no room right after a minor collection
    (the nursery is then empty);
  - (S3) a minor collection that runs out of room right after a whole
    stop-the-world cycle.
- **`t1_local`** (part 1, contracts at the steps): every run with
  `no_fail` is `transparent` for some `prog` and `ι`.
- **`t1`** (both parts, under `components_ok`): part 1, and for every
  cycle `s..j`, `stw_replay`: `take s es @ stw_tail a b @ q`, where `q`
  is a list of chunks (`chunk`, `flat`): program events, minor
  collections, and whole stop-the-world cycles (`stw_tail`), so the
  replay may collect whenever it needs room.  The replay is a run with
  `no_fail`, `transparent` for the first `m` events of the same `prog`
  (`mc es s <= m`), and either `m` is all of them or the replay is
  `stuck` (S1-S3) on event `m`.

(Approved with the stop-the-world chunks and S1-S3, 2026-11-24; part 1
proved, §16.16; part 2 open, gap G53 in §16.17.)

### 16.16 T1, part 1: every run is transparent

**Statement change (approved).**  `stw_replay`'s `q` is now a list of
chunks: program events, minor collections and whole stop-the-world cycles
(`chunk`, `flat`).  `stuck` holds only after the strongest collection:
(S1) a major allocation refused right after a minor collection and a whole
cycle; (S2) a young allocation with no room right after a minor
collection; (S3) a minor collection out of room right after a whole cycle.

**Part 1 proved: `t1_local c sty` for every `c` and both styles
(`T1Run.t1_local_ok`, `t1_local_both`), no `requires`.**
- `TrRef` (91): the store's names are those below `next`; appending a
  program event; counting program events.
- `TrVis` (362): visible blocks hold the roots' targets and are closed
  under fields; any closed set holds them (`vis_sub`); the last clause of
  `scorr` follows from the others (`scorr_intro`); a renaming cut down to
  the visible blocks keeps `scorr` and has no stale names (`restrict`,
  built with `Seq.init_ghost`, `clean`).
- `TrGen` (242): one step in general: visible blocks move by `mu`, at
  most one new block takes the next name; if each block holds its object
  again, the roots correspond, the nursery points into the image and `mu`
  is injective, `scorr` holds after (`sim_gen`).  A pointer into a block
  that keeps its size, tag and closure words resolves the same way
  (`resolve_move`).
- `TrIP` (170): steps that leave visible blocks in place; naming the
  program's values (`trv`).
- `TrEvA`-`TrEvD` (214, 261, 338, 363): collector steps, reads, root
  changes, major and young writes, major and young allocations.  Each
  splits into a configuration lemma (the world facts, from the contracts
  and (1a)/(2)) and a world lemma (the reference side).
- `TrMinA`/`TrMinB` (178, 268): a minor collection: visible young blocks
  are traced (`ymlive`), so copied (minor_post_done, G51 used here, not
  through the conclusions); visible major blocks are kept with their young
  pointers forwarded; roots forwarded; the renaming follows `fwd`.  Out of
  room: nothing changes.
- `T1Run` (345): dispatch, the induction along the run (`tr_upto`, sealed
  per-point facts), `t1_run`, `t1_local_ok`.

**No new gap.**  No existing module changed.

**Checking** (from removed `.checked` files, no `--retry`):

| Module | seed 0 | seed 1 | seed 2 |
|---|---|---|---|
| `Transp` | 1 s | 2 s | 2 s |
| `TrRef` | 1 s | 1 s | 1 s |
| `TrVis` | 5 s | 5 s | 5 s |
| `TrGen` | 4 s | 4 s | 4 s |
| `TrIP` | 4 s | 7 s | 5 s |
| `TrEvA` | 50 s | 58 s | 11 s |
| `TrEvB` | 213 s | 208 s | 206 s |
| `TrEvC` | 149 s | 159 s | 164 s |
| `TrEvD` | 125 s | 126 s | 102 s |
| `TrMinA` | 6 s | 6 s | 6 s |
| `TrMinB` | 16 s | 28 s | 37 s |
| `T1Run` | 42 s | 25 s | 35 s |

**Left.**  Part 2 (`stw_replay` for every cycle, under `components_ok`):
build the replay chunk by chunk, keeping the correspondence with the same
reference program (the part 1 step lemmas apply to the replay's steps),
and show each allocation succeeds or the replay is `stuck`.  Then `t1`,
and `Top.T1` (or `T1Run`'s successor) into `ROOT_MODULES`.

### 16.17 Gap G53: the program may name what only dropped young objects reach

| Gap | Where | Problem | Proposed fix |
|---|---|---|---|
| G53 | T1 part 2 (`stw_replay`); `Run.value_ok`, `mutator_ok_w` | `value_ok` asks only `reachable`/`yreachable`, which start from `outside_ref`: that includes major objects pointed to by *any* young block, also one the program dropped.  So a run may drop every root to young `y` (pointing to major `o`) and later name `o` again (`ERoots [VPtr (Major o)]`), legally, if it runs no minor collection in between.  The stop-the-world replay may need one in between: its allocator may refuse where the run's did not (other placement), and (S1) asks for a minor collection before the last cycle.  That drops `y`; `o` is then not reachable in the replay, the program's event is not `mutator_ok` there, and it is no allocation, so the replay is neither complete nor `stuck`.  `stw_replay` fails for some components meeting `components_ok`. | (A) The program may use only what it reaches from its roots: `value_ok` (and the `reachable`/`yreachable` of `mutator_ok_w`) by a program reachability from the roots through fields, major and young (a subset of `reachable`); re-proofs where step lemmas unfold `value_ok`, witness runs rechecked.  (B) A fourth stop for the replay (S4): before a program event that names a block the replay's collections dropped.  (C) Part 2 only for programs that name objects they reach: a hypothesis that every reference event names reference-reachable objects (`rok` with `rreachable`). |

Part 1 is not affected: it already covers every visible block.
