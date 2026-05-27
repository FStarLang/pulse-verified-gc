## Analysis of historical docs for `minor_collect_full` / major-GC composition

### Document Context
- **Date**: mixed/undated; current live code inspected on 2026-05-20 is primary.
- **Purpose**: extract only decisions/status relevant to finishing `minor_collect_full` proof and preserving major-GC preconditions/well-formedness across minor collection.
- **Status**: several docs are roadmap/historical and conflict with live code. Treat `generational/impl/GC.Gen.Impl.fsti`, `generational/impl/GC.Gen.Impl.fst`, `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti`, and `generational/spec/GC.Gen.TwoPassEquiv.fst` as current source of truth.

### Key Findings

1. **`minor_collect_full` is the current intended verified entry for minor GC + remembered-set rewriting**
   - **Current source**: `generational/impl/GC.Gen.Impl.fsti`, “Full minor collection with ref_table (full correctness)”, lines around 211–288; implementation in `GC.Gen.Impl.fst`, “minor_collect_full: includes ref_table rewriting for full correctness”, around 709–801.
   - It composes Cheney promotion, promoted-object pointer update, ref_table slot rewriting via `rewrite_heap_slots`, root rewriting/reset from `minor_collect`, and then proves conditional full `cheney_collect_spec` equivalence.
   - Important postcondition shape: if `UpdatePtrs.slots_pairwise_distinct 'sl nslots`, then `s2 == cheney_collect_spec(...).mc_major`.
   - Current preconditions include full `SpecFields.well_formed_heap 's`, allocator invariants, `minor_wf`, `minor_fields_wf`, `minor_infix_wf`, `valid_slot_addrs`, `ref_table_sound`, and `ref_table_complete` for the `cheney_promote` forwarding map.

2. **Major-GC composition requirement is explicitly recognized in live interface comments**
   - **Current source**: `generational/impl/GC.Gen.Impl.fsti`, comments around lines 290–293 state the need to show major-GC preconditions remain true after minor collection so major GC can run immediately; it is acceptable to require `MajorGC.gc_precondition` as a precondition of `minor_collect_full` too.
   - **Actionable implication**: finishing the proof should not only establish `part1`; it must preserve or re-establish the concrete preconditions consumed by `collect`/major GC: full heap well-formedness, no problematic colors/black objects as required, root/stack properties, allocator/free-list invariants, and graph/well-formed field closure over the post-minor heap.

3. **Current `minor_collect_full` postcondition still prominently exposes only `well_formed_heap_part1` for promotion; full WFH is conditional via equivalence/spec path**
   - **Current source**: `generational/impl/GC.Gen.Impl.fsti` around 275–288: postcondition records `SpecFields.well_formed_heap_part1 prom.major_final`, then conditional equality to `cheney_collect_spec(...).mc_major` under distinct slots.
   - **Historical support**: `END_TO_END_REVIEW.md`, §3.5 says the end-to-end theorem’s first property is post-minor major heap `well_formed_heap` before major GC, but its preconditions include several frame/closure conditions (`post_promote_pointer_closure`, major GC entry conditions).
   - **Actionable implication**: if the current blocker is “major-GC precondition preservation,” the proof likely needs a bridge from `s2 == cheney_collect_spec(...).mc_major` plus Cheney correctness lemmas to full `SpecFields.well_formed_heap s2` and major-GC entry invariants, or a stronger direct postcondition on `minor_collect_full`.

4. **Two-pass equivalence is the central proof obligation for full minor correctness with ref_table**
   - **Current source**: `generational/spec/GC.Gen.TwoPassEquiv.fst`, especially final theorem area around 1686–1690: `rewrite_slots_iter (update_promoted_iter prom.major_final farr prom.fwd_map 0) prom.fwd_map slots n 0 == update_major_pointers prom.major_final prom.fwd_map`.
   - **Current source**: `generational/impl/GC.Gen.Impl.fst` around 589–594 lists the needed equivalence assumptions: valid slots, pairwise distinct slots, `ref_table_sound`, `ref_table_complete`, `fwd_targets_stable`, `well_formed_heap_part1`, etc.; comments around 396–402 describe deriving `fwd_ptrs_classified` from frame + ref_table completeness/soundness + `represents_fwd`.
   - **Actionable implication**: `minor_collect_full`’s full-spec result depends on completing/using the two-pass theorem under precisely these derived conditions. The only caller-side condition intentionally left is `slots_pairwise_distinct`; all other conditions are intended to be derived internally from Cheney promotion and ref_table properties.

5. **Remembered-set/write-barrier correctness is a caller/mutator obligation, represented by `ref_table_complete` + `ref_table_sound`**
   - **Current source**: `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti`, “Rewrite heap slots (ref_table entries)” and definitions around 349–383.
   - `ref_table_complete`: every scannable, non-blue field in the original major heap holding a forwarded minor pointer appears in `slots[0..n)`.
   - `ref_table_sound`: every slot is a valid pointer-field slot in a non-blue, non-no-scan major object.
   - **Historical docs**:
     - `END_TO_END_REVIEW.md`, §3.4: remembered set/write barrier are mutator obligations; GC assumes complete roots/remembered set.
     - `PHASE2_PLAN.md`, D2: reuse OCaml `caml_ref_table`; trust OCaml `caml_modify` to record major→minor stores.
     - `OCAML_INTEGRATION.md`, “Inter-Generational Pointers”: bridge casts OCaml ref_table slots to `uint64_t*` and passes slot addresses to verified rewriting; LP64 static assert expected.
   - **Actionable implication**: do not try to prove `caml_modify` correctness in `minor_collect_full`; require/consume `ref_table_complete` and `ref_table_sound`, and document pairwise distinctness as caller obligation unless deduplication is added.

6. **`rewrite_heap_slots` is verified and intended to replace historical manual ref_table rewriting**
   - **Current source**: `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti`, lines around 160–164: `rewrite_heap_slots` reads each slot value and rewrites it via the forwarding map.
   - **Historical source**: `generational/PATCHES.md`, B9 says ref_table forwarding rewrite is DONE and verified; old manual loop replaced.
   - **Actionable implication**: if proof failure concerns remembered-set fields, focus on the specs/lemmas for `rewrite_slots_iter`, slot validity, and distinctness—not on bridge C logic.

7. **Infix/Cheney handling has evolved; newer docs/live code supersede older roadmap statements**
   - **Current sources**:
     - `OCAML_INTEGRATION.md`, “Infix Pointers” and “Infix and the TwoPassEquiv Theorem”: infix forwarding is handled on-demand in Cheney BFS; `update_promoted_iter` skips infix entries, while parent closure scan covers infix fields.
     - `generational/spec/GC.Gen.TwoPassEquiv.fst`, around 656–660: infix entries are skipped by `update_promoted_iter`.
   - **Historical conflict**:
     - `GENERATIONAL_PLAN.md` and earlier portions of `generational/PATCHES.md` describe no-infix assumptions, bridge infix parent injection, and synthetic forwarding as gaps/workarounds. These are likely superseded by current infix-aware BFS and TwoPassEquiv handling.
   - **Actionable implication**: proof obligations should distinguish real promoted entries from infix/interior entries. Scanning infix entries as objects is wrong because their wosize encodes offset-to-parent, not field count.

8. **Efficient two-pass minor collection intentionally avoids full `update_all_objects` / dense-heap requirement**
   - **Historical source**: `OCAML_INTEGRATION.md`, “Verification Boundary” and “Path to unification”: `update_all_objects` walks entire major heap and requires `heap_objects_dense`; bridge/current design uses `update_promoted_objects` plus ref_table slots.
   - **Current source**: `GC.Gen.Impl.fst` around 616–618: `minor_collect` uses `update_promoted_objects`; caller updates remembered-set slots separately. `minor_collect_full` adds the verified ref_table rewrite.
   - **Actionable implication**: do not regress to `update_all_objects` just to get an easier spec unless performance is irrelevant. The intended proof path is two-pass equivalence: promoted objects + remembered-set slots equals full `update_major_pointers`.

9. **OOM handling/status: `minor_collect_full` returns `ok: bool`; historical docs about bridge scans are superseded**
   - **Current source**: `GC.Gen.Impl.fsti` `minor_collect_full` returns `ok: bool`.
   - **Historical source**: `OCAML_INTEGRATION.md`, “OOM Handling” discusses earlier unverified bridge loops and proposed verified OOM detection. Later in the same doc, “Phase C” says bridge uses `minor_collect_full` and checks `ok`.
   - **Actionable implication**: current proof work should preserve the `ok`/OOM semantics through Cheney promotion and ensure no postcondition claims full collection correctness on failed promotion unless guarded appropriately.

10. **Older roadmap docs are useful for intent but not status**
   - `generational_gc.md`: initial task statement only; useful for high-level goal (generational collector with same end-to-end correctness), no current technical status.
   - `GENERATIONAL_PLAN.md`: aged roadmap; many items now superseded. It records why promotion temporarily weakens full WFH (minor addresses copied into major fields before rewrite), which remains conceptually important for proving intermediate states.
   - `PHASE2_PLAN.md`: useful for integration decisions (minor address translation, ref_table trust boundary), but statuses about missing snapshot/integration are stale.
   - `END_TO_END_REVIEW.md`: useful for correctness framing and trust boundary, but feature/status tables may predate `minor_collect_full` refinements.
   - `generational/PATCHES.md`: valuable historical record of eliminated C patches; trust newer “DONE/ELIMINATED” entries over earlier detailed patch descriptions in the same file.

### Critical Constraints for Finishing `minor_collect_full`

- **Slot distinctness**: current `minor_collect_full` only yields full `cheney_collect_spec` equality under `UpdatePtrs.slots_pairwise_distinct`. If OCaml ref_table may contain duplicate slots, either prove idempotence/last-write safety for duplicates or deduplicate/require distinctness in the bridge.
- **Ref_table completeness/soundness**: must remain explicit caller obligations; they model write-barrier correctness and valid field-slot addresses.
- **Infix classification**: forwarding array entries include normal objects and infix interior pointers; TwoPassEquiv must skip infix entries and rely on parent coverage.
- **Major-GC entry**: post-minor state must satisfy more than `part1` if immediately passed to major `collect`. Need full WFH/pointer closure and major-GC color/root/stack preconditions, or an explicit theorem composing `minor_collect_full` with major GC under preserved preconditions.
- **Intermediate WFH weakness**: after raw promotion/copy, major fields may still contain minor pointers; full well-formedness is restored only after promoted-object update + ref_table slot rewrite + root rewrite. Use phase-specific invariants rather than expecting full WFH mid-pipeline.

### Relevance Assessment

- **Most relevant/current**: live code interfaces in `generational/impl/GC.Gen.Impl.fsti`, `GC.Gen.Impl.UpdatePtrs.fsti`, implementation structure in `GC.Gen.Impl.fst`, and `GC.Gen.TwoPassEquiv.fst`.
- **Historically useful**: `OCAML_INTEGRATION.md` for architecture/infix/ref_table intent; `END_TO_END_REVIEW.md` for composition/trust-boundary framing; `generational/PATCHES.md` for why old bridge patches were eliminated.
- **Likely superseded**: `GENERATIONAL_PLAN.md`, `PHASE2_PLAN.md`, and `generational_gc.md` for implementation status; use only for original design intent and not as proof-status authority.
