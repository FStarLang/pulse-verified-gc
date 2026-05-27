# F*/Pulse assessment: finishing `minor_collect_full` and major-GC readiness

**Date:** 2026-05-20  
**Scope:** read-only expert assessment of the live F*/Pulse code around `minor_collect_full`.  
**Source focus:** `generational/impl/GC.Gen.Impl.fsti` and the proof dependencies it currently relies on.

## Executive summary

The cleanest, lowest-rlimit strengthening of `minor_collect_full` is **not** to inline the full major-GC precondition proof into the Pulse function. Instead, expose a small conditional postcondition that transfers a **post-minor spec-level major-GC precondition** through the already-intended equality between the concrete two-pass heap `s2` and `CheneySpec.cheney_collect_spec(...).mc_major`.

Concretely, the likely useful additional conjunct is:

```fstar
// with either ghost args #major_stack #cap, or a forall over them
UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots) ==>
  (let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
   MajorGC.gc_precondition res.mc_major major_stack res.mc_fp cap ==>
   MajorGC.gc_precondition s2 major_stack fp2 cap)
```

or, if the API should make pairwise distinctness a real caller obligation rather than a conditional:

```fstar
MajorGC.gc_precondition res.mc_major major_stack res.mc_fp cap ==>
MajorGC.gc_precondition s2 major_stack fp2 cap
```

under a new precondition `UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots)`.

If the intended requirement is instead stronger—**initial** `MajorGC.gc_precondition 's major_stack 'fp cap` implies post-minor `MajorGC.gc_precondition s2 major_stack fp2 cap`—then the current interface is missing essential semantic assumptions. That stronger theorem is likely false or at least unprovable from the current preconditions without additional no-OOM/completeness and minor-field closure assumptions. The current preconditions do not guarantee that every minor pointer copied into promoted objects is forwarded, nor that the post-minor heap satisfies full pointer closure.

Also, the current “strong correctness” path is not proof-complete: it depends on admits in `GC.Gen.TwoPassEquiv.fst` and on admits / a top-level `squash False` stop in `GC.Gen.CheneyPreservation.fst`. These are central blockers, not downstream symptoms.

## Current live interface shape

`minor_collect_full` is declared at `generational/impl/GC.Gen.Impl.fsti:223`. Its precondition owns the generational heap and the arrays (`roots`, `fwd_arr`, `queue`, `slots`) at `generational/impl/GC.Gen.Impl.fsti:228-233`.

The pure precondition already requires:

- full input major heap well-formedness, `SpecFields.well_formed_heap 's`, at `generational/impl/GC.Gen.Impl.fsti:233`;
- allocator/free-list/density/blue-chain conditions at `generational/impl/GC.Gen.Impl.fsti:234-237`;
- root and forwarding-array setup at `generational/impl/GC.Gen.Impl.fsti:238-240`;
- minor heap structural/infix/guard assumptions at `generational/impl/GC.Gen.Impl.fsti:241-243`;
- non-empty major object list at `generational/impl/GC.Gen.Impl.fsti:244`;
- slot validity/soundness/completeness at `generational/impl/GC.Gen.Impl.fsti:245-250`.

The postcondition currently states the final concrete heap is the two-pass heap:

- `s2 == rewrite_slots_iter (update_promoted_iter prom.major_final farr2 prom.fwd_map 0) ...` at `generational/impl/GC.Gen.Impl.fsti:261-264`;
- `fp2 == prom.fp_final` at `generational/impl/GC.Gen.Impl.fsti:266`;
- roots rewritten at `generational/impl/GC.Gen.Impl.fsti:268`;
- minor heap reset at `generational/impl/GC.Gen.Impl.fsti:270`;
- forwarding-array representation/validity at `generational/impl/GC.Gen.Impl.fsti:272-275`;
- only `SpecFields.well_formed_heap_part1 prom.major_final` exposed as structural preservation at `generational/impl/GC.Gen.Impl.fsti:277`;
- conditional equality to the full Cheney spec under slot distinctness at `generational/impl/GC.Gen.Impl.fsti:287-288`.

The explicit comment requesting the missing strengthening is at `generational/impl/GC.Gen.Impl.fsti:289-293`.

## What exact conjunct should be added?

### Recommended low-risk conjunct: transfer post-minor `gc_precondition` through concrete/spec equality

The major-GC entry predicate is defined in `mark-and-sweep/impl/GC.Impl.fsti:23-36`. It bundles:

- `SpecMarkBoundedInv.bounded_mark_inv s st cap`;
- `SI.fp_valid fp s`;
- `SpecMark.root_props s st`;
- `SpecSweep.fp_in_heap fp s`;
- `SpecMark.no_black_objects s`;
- `SpecMark.no_pointer_to_blue s`;
- `SpecFields.no_scan_invariant s`;
- gray/black objects are in the stack;
- graph well-formedness and root-subset conditions.

For `minor_collect_full`, add either ghost parameters:

```fstar
(#major_stack: erased (Seq.seq obj_addr)) (#cap: erased nat)
```

or a universal quantifier in the postcondition. The ghost-argument form is more caller-friendly and usually easier for Pulse VCs.

Suggested postcondition conjunct:

```fstar
(UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots) ==>
  (let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
   MajorGC.gc_precondition res.mc_major major_stack res.mc_fp cap ==>
   MajorGC.gc_precondition s2 major_stack fp2 cap))
```

This is the right first strengthening because the function already intends to prove:

```fstar
slots_pairwise_distinct ==> s2 == res.mc_major
```

at `generational/impl/GC.Gen.Impl.fsti:287-288`, and it already proves `fp2 == prom.fp_final` at `generational/impl/GC.Gen.Impl.fsti:266`; `cheney_collect_spec` uses `prom.fp_final` for `mc_fp` in `generational/spec/GC.Gen.Cheney.fsti:296-304`.

This conjunct gives a caller an immediately usable major-GC precondition on the **actual** concrete heap resource returned by `minor_collect_full`, without forcing the Pulse VC to re-prove all components of `gc_precondition`.

### Stronger but riskier conjunct: full post-minor well-formedness

If the user wants a heap-specific conjunct rather than the full major-GC bundle, the clean postcondition is:

```fstar
UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots) ==>
  (let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
   SpecFields.well_formed_heap res.mc_major ==>
   SpecFields.well_formed_heap s2)
```

or, with the well-formedness proven separately:

```fstar
UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots) ==>
  SpecFields.well_formed_heap s2
```

The second form is much stronger and requires a genuine theorem that Cheney collection restores full `well_formed_heap`. Existing live Cheney correctness exposes only part 1 unconditionally: `cheney_collect_preserves_wfh_part1` is documented at `generational/spec/GC.Gen.CheneyCorrectness.fsti:80-98`; `cheney_collect_preserves_wfh` in `GC.Gen.Cheney.fsti` also only ensures `well_formed_heap_part1` at `generational/spec/GC.Gen.Cheney.fsti:373-389`.

### Do not claim initial-to-post `gc_precondition` without more assumptions

A direct conjunct of the form

```fstar
MajorGC.gc_precondition 's major_stack 'fp cap ==>
MajorGC.gc_precondition s2 major_stack fp2 cap
```

is probably not valid from current assumptions alone. Reasons:

1. `gc_precondition` includes full `well_formed_heap`; current `minor_collect_full` only exposes `well_formed_heap_part1 prom.major_final` at `generational/impl/GC.Gen.Impl.fsti:277`.
2. Promoted objects can contain copied minor pointers. Unless all such minor targets are forwarded and rewritten, post-minor pointer closure may fail. The current `ok` return is not tied in the interface to `cheney_no_oom` or to complete forwarding.
3. The current ref-table covers pre-existing major fields (`ref_table_complete` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:349-371`), not arbitrary minor-object fields. Promoted-object fields are handled by BFS/update, but full closure needs no-OOM/reachability or an explicit pointer-closure-modulo-forwarding assumption.
4. `minor_collect_full` rewrites `roots`, but it does not rewrite a `gray_stack`. If the `major_stack` contains minor roots before collection, initial `gc_precondition 's major_stack 'fp cap` cannot even hold because stack elements must be major objects and gray. If the stack contains only existing major roots, same-stack preservation is plausible but needs color/header frame lemmas.

## Existing modules/lemmas that already prove parts of the desired result

### Phase-level implementation facts

`cheney_promote_phase` already returns strong post-promotion facts in `generational/impl/GC.Gen.Impl.Cheney.fst:811-827`:

- `ms2 == prom.major_final`;
- `fp2 == prom.fp_final`;
- `represents_fwd farr2 prom.fwd_map`;
- `well_formed_heap_part1 ms2`;
- `fl_valid ms2 fp2`;
- `fl_chain_terminates ms2 fp2`;
- `heap_objects_dense ms2`;
- `chain_objects_blue ms2 fp2`;
- non-empty objects list;
- forwarding-array length.

`minor_collect` exposes many of those facts in its public interface at `generational/impl/GC.Gen.Impl.fsti:201-208`, but `minor_collect_full` currently exposes only part1 plus the conditional full-spec equality.

### Cheney correctness and preservation

`GC.Gen.CheneyCorrectness.fsti` provides:

- object survival through full Cheney collection at `generational/spec/GC.Gen.CheneyCorrectness.fsti:58-75`;
- post-collection part1 at `generational/spec/GC.Gen.CheneyCorrectness.fsti:80-98`;
- minor reset at `generational/spec/GC.Gen.CheneyCorrectness.fsti:103-117`;
- root rewriting at `generational/spec/GC.Gen.CheneyCorrectness.fsti:122-137`;
- the composed `cheney_gc_correct` theorem bundling object survival, part1, `fl_valid`, `fl_chain_terminates`, reset, and root rewriting at `generational/spec/GC.Gen.CheneyCorrectness.fsti:146-190`.

`GC.Gen.CheneyEnd2End.fsti` provides `cheney_collect_no_black` at `generational/spec/GC.Gen.CheneyEnd2End.fsti:47-53`. This is directly relevant to the `no_black_objects` component of `MajorGC.gc_precondition`, but it depends on `GC.Gen.CheneyPreservation.cheney_promote_preserves_no_black`.

`GC.Gen.CheneyPreservation.fsti` declares key facts used by the current two-pass bridge:

- `cheney_promote_preserves_no_black` at `generational/spec/GC.Gen.CheneyPreservation.fsti:30-37`;
- `fwd_valid_or_infix` and `cheney_promote_fwd_valid_or_infix` at `generational/spec/GC.Gen.CheneyPreservation.fsti:59-74`;
- `cheney_promote_frame_old_fields` at `generational/spec/GC.Gen.CheneyPreservation.fsti:87-105`;
- `fwd_normal_injective` and `cheney_promote_fwd_normal_injective` at `generational/spec/GC.Gen.CheneyPreservation.fsti:116-128`;
- `cheney_promote_frame_old_header` at `generational/spec/GC.Gen.CheneyPreservation.fsti:141-155`;
- `cheney_promote_nonblue_origin` at `generational/spec/GC.Gen.CheneyPreservation.fsti:169-180`.

These are important, but their implementation has central admits; see blockers below.

### Pointer update / two-pass equivalence

`GC.Gen.Impl.UpdatePtrs.fsti` defines:

- `represents_fwd` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:28-31`;
- `valid_slot_addrs` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:110-116`;
- `slots_pairwise_distinct` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:118-123`;
- `rewrite_slots_iter` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:132-156`;
- `update_promoted_iter` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:194-221`;
- `ref_table_complete` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:349-371`;
- `ref_table_sound` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:378-390`;
- `fwd_targets_stable` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:399-405`;
- `fwd_ptrs_classified` at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:416-441`.

`GC.Gen.TwoPassEquiv.fsti` states the key theorem `promoted_plus_slots_eq_full_update` at `generational/spec/GC.Gen.TwoPassEquiv.fsti:152-184`:

```fstar
rewrite_slots_iter
  (update_promoted_iter prom.major_final farr prom.fwd_map 0)
  prom.fwd_map slots n 0
== update_major_pointers prom.major_final prom.fwd_map
```

under validity/disjointness/classification/ref-table assumptions.

`GC.Gen.Impl.fst` wraps and derives those assumptions in `two_pass_implies_full_update` at `generational/impl/GC.Gen.Impl.fst:577-614`. The implementation of `minor_collect_full` invokes the needed Cheney facts and the bridge at `generational/impl/GC.Gen.Impl.fst:818-835`.

### PromoteUpdate well-formedness support

For any path that proves full `well_formed_heap` of `cheney_collect_spec(...).mc_major`, the relevant existing support is in `GC.Gen.PromoteUpdate.fsti`:

- `update_major_pointers_preserves_objects` at `generational/spec/GC.Gen.PromoteUpdate.fsti:24-26`;
- `update_major_pointers_preserves_wfh_part1` at `generational/spec/GC.Gen.PromoteUpdate.fsti:32-35`;
- `update_major_pointers_preserves_wfh_part4` at `generational/spec/GC.Gen.PromoteUpdate.fsti:219-222`;
- `update_major_pointers_preserves_wfh_part3` at `generational/spec/GC.Gen.PromoteUpdate.fsti:224-227`;
- `update_major_pointers_preserves_wfh_part2` at `generational/spec/GC.Gen.PromoteUpdate.fsti:293-299`, requiring `pointer_closure_modulo_fwd`, `fwd_all_targets_valid`, `blue_fields_closed`, and `no_scan_invariant`.

Most of those preconditions currently exist for older `promote_all_spec` flows, not for `cheney_promote`; new Cheney analogs would be needed for a direct full-WFH theorem.

## Central blockers vs downstream symptoms

### Central blocker 1: `GC.Gen.TwoPassEquiv.fst` admits

Two admits are directly in the theorem path for `minor_collect_full`'s strong equality:

- `generational/spec/GC.Gen.TwoPassEquiv.fst:1313-1317` admits `non_promoted_non_slot_no_fwd`; the comments say the lemma is currently unused and was written for an older address-level `fwd_ptrs_classified`.
- `generational/spec/GC.Gen.TwoPassEquiv.fst:1483-1488` admits `fwd_ptrs_classified_at`; the comment says the current field-position formulation needs an additional field-membership precondition.

The second admit is central: `if_branch_addr_eq` calls `fwd_ptrs_classified_at` at `generational/spec/GC.Gen.TwoPassEquiv.fst:1603-1605`, and the final theorem calls `if_branch_addr_eq` at `generational/spec/GC.Gen.TwoPassEquiv.fst:1711-1714`.

Until this is fixed, the conditional equality at `generational/impl/GC.Gen.Impl.fsti:287-288` is not a completed proof foundation for additional major-GC readiness.

### Central blocker 2: `GC.Gen.CheneyPreservation.fst` admits and `__inj_stop`

`GC.Gen.CheneyPreservation.fst` contains:

- a top-level `let __inj_stop : squash False = admit ()` at `generational/spec/GC.Gen.CheneyPreservation.fst:1608-1610`;
- admitted `cheney_promote_frame_old_header` at `generational/spec/GC.Gen.CheneyPreservation.fst:2213-2229`;
- admitted `cheney_promote_nonblue_origin` at `generational/spec/GC.Gen.CheneyPreservation.fst:2242-2258`.

These are central because `minor_collect_full`'s bridge uses the corresponding exported facts:

- `derive_promoted_entries_disjoint` requires `CheneyPres.fwd_normal_injective` at `generational/impl/GC.Gen.Impl.fst:333-342` and uses it in the equal-target case at `generational/impl/GC.Gen.Impl.fst:373-389`.
- `derive_fwd_case_a` calls `cheney_promote_frame_old_header` and `cheney_promote_frame_old_fields` at `generational/impl/GC.Gen.Impl.fst:443-459`.
- `derive_fwd_case_b` calls `cheney_promote_nonblue_origin` at `generational/impl/GC.Gen.Impl.fst:496-500`.

The `__inj_stop` is especially risky: if a top-level `squash False` fact is in context, it can make later proofs vacuous. This should be treated as proof debt, not a harmless stop marker.

### Central blocker 3: full post-minor WFH/major-precondition theorem is not present

Existing live Cheney correctness only gives part1 and allocator/free-list survival, not full `well_formed_heap`. Evidence:

- `cheney_collect_preserves_wfh_part1` only ensures part1 at `generational/spec/GC.Gen.CheneyCorrectness.fsti:80-98`.
- `cheney_collect_preserves_wfh` in `GC.Gen.Cheney.fsti` is named broadly but only ensures part1 at `generational/spec/GC.Gen.Cheney.fsti:373-389`.
- `well_formed_heap` itself is full parts 1-4 at `common/spec/GC.Spec.Fields.fst:668-673`.

A proof of `MajorGC.gc_precondition s2 ...` from initial preconditions needs full WFH plus the other `gc_precondition` components. Those lemmas are not yet present for the Cheney/two-pass/ref-table path.

### Downstream symptoms

- `GC.Gen.Impl.fst` is large and expensive. In a read-only verification check, `GC.Gen.Impl.fsti` verified successfully, but `GC.Gen.Impl.fst` timed out after 180s under the top-level include flags and `--z3rlimit 200 --split_queries always --z3refresh`. This is a performance/modularity symptom, not the primary logical blocker.
- The platform `assume val platform_fits_u64` in `generational/impl/GC.Gen.Impl.MinorHeap.fst:26` is a TCB/platform assumption, but it is not central to the major-GC preservation proof.

## Modular completion plan

### Phase 0: Decide target strength

Ask the user to choose one of these precise contracts:

1. **Spec-transfer contract (recommended first):** if the caller can establish `MajorGC.gc_precondition` for `cheney_collect_spec(...).mc_major`, then `minor_collect_full` returns a concrete heap satisfying the same precondition. This is low-rlimit and follows from equality.
2. **Full post-minor WFH contract:** prove `slots_pairwise_distinct ==> SpecFields.well_formed_heap s2` under additional semantic assumptions.
3. **Initial-to-post preservation contract:** prove `MajorGC.gc_precondition 's st 'fp cap ==> MajorGC.gc_precondition s2 st fp2 cap`. This requires additional no-OOM/completeness and minor-field/pointer-closure assumptions and may require changing how roots/gray stack are modeled.

### Phase 1: Finish the current strong equality foundation

1. Fix `GC.Gen.CheneyPreservation.fst` before building more on top of it.
   - Split after `cheney_promote_frame_old_fields` into smaller modules, e.g.:
     - `GC.Gen.Cheney.Frame` for old field/header frame lemmas;
     - `GC.Gen.Cheney.Injectivity` for `fwd_normal_injective`;
     - `GC.Gen.Cheney.Origin` for `cheney_promote_nonblue_origin`.
   - Remove `__inj_stop` at `generational/spec/GC.Gen.CheneyPreservation.fst:1610`.
   - Prove `cheney_promote_frame_old_header` by mirroring the existing field-frame induction (`generational/spec/GC.Gen.CheneyPreservation.fst:1585-1605`) but using header-address frame lemmas.
   - Prove `cheney_promote_nonblue_origin` with an explicit BFS invariant: non-blue objects in the current heap are either pre-existing non-blue or forwarding targets.

2. Fix `GC.Gen.TwoPassEquiv.fst`.
   - Replace `fwd_ptrs_classified_at` with a field-position lemma:

     ```fstar
     val fwd_ptrs_classified_field_at
       (major fwd farr slots n obj j) : Lemma
       (requires fwd_ptrs_classified major fwd farr slots n /\
                 Seq.mem obj (objects zero_addr major) /\
                 is_blue obj major = false /\
                 is_no_scan obj major = false /\
                 j < U64.v (wosize_of_object obj major) /\
                 U64.v obj + j * 8 + 8 <= heap_size /\
                 let a = U64.v obj + j * 8 in
                 let field_val = to_minor_offset (read_word major (U64.uint_to_t a)) in
                 is_minor_pointer field_val /\ fwd field_val <> 0UL)
       (ensures (exists pi. pi < fwd_array_size /\ Seq.index farr pi == obj) \/
                (exists si. si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8))
     ```

   - Refactor `if_branch_addr_eq` so the caller supplies `(obj,j)` when proving field addresses, instead of deriving `(obj,j)` from arbitrary aligned address `a`.
   - Avoid address-level classification for headers. Headers can accidentally look like minor pointers (the existing comment at `generational/spec/GC.Gen.TwoPassEquiv.fst:1483-1488` already identifies this). Prove header/no-scan/blue/non-field preservation separately.
   - Keep `non_promoted_non_slot_no_fwd` deleted or private/unreferenced unless it is reformulated with field-membership assumptions.

3. Verify in order:
   - `generational/spec/GC.Gen.CheneyPreservation.fsti`
   - `generational/spec/GC.Gen.CheneyPreservation.fst`
   - `generational/spec/GC.Gen.TwoPassEquiv.fsti`
   - `generational/spec/GC.Gen.TwoPassEquiv.fst`
   - `generational/impl/GC.Gen.Impl.fsti`
   - `generational/impl/GC.Gen.Impl.fst`

### Phase 2: Add a low-rlimit congruence lemma for `gc_precondition`

Export a small equality/congruence lemma near the definition of `gc_precondition`, preferably from `mark-and-sweep/impl/GC.Impl.fsti` / `.fst` or a new pure bridge module that imports `GC.Impl`:

```fstar
val gc_precondition_congruent
  (s1 s2: heap) (st: Seq.seq obj_addr) (fp1 fp2: U64.t) (cap: nat)
  : Lemma
    (requires s1 == s2 /\ fp1 == fp2 /\ gc_precondition s1 st fp1 cap)
    (ensures  gc_precondition s2 st fp2 cap)
```

This lemma should be immediate by equality and should not unfold any major-GC internals. If F* unfolds the predicate too aggressively, make a wrapper predicate for the post-minor precondition and provide a congruence lemma for that wrapper.

### Phase 3: Strengthen `minor_collect_full` minimally

Add ghost arguments or a universal quantifier for `(major_stack, cap)`. Prefer ghost args if callers naturally have those values:

```pulse
fn minor_collect_full ...
  (#major_stack: erased (Seq.seq obj_addr)) (#cap: erased nat)
requires ...
ensures ... /\
  (UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots) ==>
   (let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
    MajorGC.gc_precondition res.mc_major (reveal major_stack) res.mc_fp (reveal cap) ==>
    MajorGC.gc_precondition s2 (reveal major_stack) fp2 (reveal cap)))
```

In the body, after the existing `two_pass_implies_full_update` call at `generational/impl/GC.Gen.Impl.fst:832-835`, call the congruence lemma with:

- `s1 = (CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs).mc_major`;
- `s2 = ms_final` / postcondition heap witness;
- `fp1 = res.mc_fp`;
- `fp2 = prom.fp_final`, using `cheney_collect_spec_unfold` if needed.

This should be a tiny proof obligation if the equality foundation is complete.

### Phase 4: If the user insists on initial-to-post preservation

Add a separate pure module, do not put this directly in `GC.Gen.Impl.fst`. Suggested module: `generational/spec/GC.Gen.CheneyMajorPreservation.fsti/.fst`.

Potential lemma boundary:

```fstar
val cheney_collect_preserves_gc_precondition
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr) (cap: nat)
  : Lemma
    (requires
      MajorGC.gc_precondition major st fp cap /\
      // existing minor/full-collection assumptions
      fl_valid major fp heap_fuel /\
      fl_chain_terminates major fp heap_fuel /\
      chain_objects_blue major fp /\
      heap_objects_dense major /\
      minor_wf minor /\
      minor_guards_complete minor /\
      minor_infix_wf minor /\
      // additional semantic assumptions needed for full WFH:
      CheneyBFS.cheney_no_oom minor major fp roots /\
      cheney_pointer_closure_modulo_fwd minor major fp roots /\
      cheney_promote_no_scan_ready minor major fp roots)
    (ensures
      let res = cheney_collect_spec minor major fp roots in
      MajorGC.gc_precondition res.mc_major st res.mc_fp cap)
```

Break that into smaller lemmas:

1. `cheney_collect_full_wfh`: full `well_formed_heap res.mc_major`.
2. `cheney_collect_preserves_no_black`: already exists as `cheney_collect_no_black` at `generational/spec/GC.Gen.CheneyEnd2End.fsti:47-53`.
3. `cheney_collect_preserves_no_pointer_to_blue`: new.
4. `cheney_collect_preserves_no_scan_invariant`: new Cheney analog of older `promote_all_preserves_no_scan_invariant` (`generational/spec/GC.Gen.Promote.fsti:741-754`).
5. `cheney_collect_preserves_stack_props` / bounded-stack properties for same stack, using header frame for pre-existing non-blue stack roots.
6. `cheney_collect_preserves_fp_valid_in_heap`: new; likely requires a reusable exported `fl_valid_implies_fp_in_heap` lemma, currently only in `mark-and-sweep/spec/GC.Test.Bridge.fst:1131-1142` and not in a core interface.
7. `cheney_collect_preserves_graph_preconditions`: either prove graph equality/extension facts or require graph conditions on the post-minor heap as current `gen_gc` does.

## Low-rlimit stabilization tactics

- Move pure bridge lemmas out of `generational/impl/GC.Gen.Impl.fst`. That file already has large Pulse VCs and helper lemmas mixed together; `two_pass_implies_full_update` at `generational/impl/GC.Gen.Impl.fst:577-614` is a good candidate for a pure spec module.
- Keep `--fuel 0 --ifuel 0` on congruence/transfer lemmas; they should rely on equality, not unfolding.
- Make large predicates opaque and provide `_at` instantiation lemmas, following the existing `fwd_targets_stable` pattern at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:399-405`.
- Avoid global quantified lemmas with broad triggers over `read_word` unless wrapped in explicit instantiation helpers. The current `fwd_ptrs_classified` has a pattern at `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:423-425`; use explicit field-at lemmas to avoid quantifier cascades.
- Use `--query_stats --split_queries always` to identify failures before changing rlimits. The implementation currently uses high local limits (`--z3rlimit 200` around the classification helpers at `generational/impl/GC.Gen.Impl.fst:403` and `generational/impl/GC.Gen.Impl.fst:525`); those should shrink after moving lemmas to pure modules.
- Verify `.fsti` before `.fst` for every changed module.

## Risks and open user decisions

1. **Same stack or rewritten roots?** `minor_collect_full` rewrites the `roots` array but does not rewrite a `gray_stack`. A postcondition on `MajorGC.gc_precondition s2 st fp2 cap` for the same `st` only makes sense if `st` already contains major-heap roots. If major-GC roots should be the rewritten `rs2`, the API should say so explicitly and probably return/prove a stack-building step after minor collection.

2. **OOM semantics.** The function returns `ok`, but the current interface does not expose `ok ==> cheney_no_oom` or any completeness theorem. Full WFH and immediate major-GC readiness may need to be guarded by `ok == true` or by an explicit no-OOM precondition.

3. **Slot distinctness.** The full-spec equality and any low-rlimit transfer from it are conditional on `UpdatePtrs.slots_pairwise_distinct 'sl (SZ.v nslots)`. If callers cannot guarantee distinct slots, either make the theorem robust to duplicates by proving idempotence/last-write safety, or deduplicate slots before calling.

4. **Initial-to-post preservation may be too strong.** Initial `MajorGC.gc_precondition` does not mention minor-heap pointer closure, forwarding completeness, or remembered-set completeness for minor-object fields. The safer first step is the post-minor spec-transfer contract.

5. **Do not build new facts on admitted foundations.** The `TwoPassEquiv` and `CheneyPreservation` admits are central. Adding more postconditions before removing them risks making the interface look complete while the proof remains unsound.

## Recommended immediate next action

1. First finish the existing strong equality proof by eliminating the central admits in `GC.Gen.TwoPassEquiv.fst` and `GC.Gen.CheneyPreservation.fst`.
2. Then add a tiny `gc_precondition_congruent` lemma.
3. Then strengthen `minor_collect_full` with the spec-transfer major-GC precondition conjunct under `slots_pairwise_distinct`.
4. Only after that, decide whether to attempt the stronger initial-to-post preservation theorem; if yes, add no-OOM and minor-pointer-closure assumptions explicitly rather than burying them in the Pulse proof.
