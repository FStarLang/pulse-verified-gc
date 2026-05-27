# File map for `minor_collect_full`

## Implementation and interface files

- `generational/impl/GC.Gen.Impl.fsti:223-293` — interface declaration for `minor_collect_full`; shows the precondition bundle, the `slots`/`fwd_arr`/`queue` inputs, and the current comment about possibly requiring `MajorGC.gc_precondition` as a precondition.
- `generational/impl/GC.Gen.Impl.fst:709-775` — implementation and proof body for `minor_collect_full`; includes the phase sequence (`cheney_promote_phase`, `update_promoted_objects`, `rewrite_heap_slots`, `rewrite_roots_impl`) and the current two-pass/full-correctness theorem.
- `generational/impl/GC.Gen.Impl.fst:24-35` — module imports and aliases used by `minor_collect_full` (`GC.Gen.Cheney`, `GC.Gen.Impl.UpdatePtrs`, `GC.Gen.Promote`, `GC.Impl`, `GC.Spec.Correctness`, `GC.Spec.Mark`).
- `generational/impl/GC.Gen.Impl.fst:214-220` — helper lemma `cheney_collect_spec_unfold`, which relates `cheney_collect_spec` to promotion + root rewriting.
- `generational/impl/GC.Gen.Impl.fst:226-276` — helper lemmas around forwarding arrays and promotion invariants (`fwd_bounded_implies_valid_fwd_entries`, `derive_fwd_targets_stable`).
- `generational/impl/GC.Gen.Impl.fst:289-608` — helper lemmas used by the two-pass/full-correctness story, including `derive_promoted_entries_valid_from`, `derive_promoted_entries_disjoint`, and the equivalence lemmas around `rewrite_slots_iter` and `update_major_pointers`.
- `generational/impl/GC.Gen.Impl.fst:630-669` — earlier `minor_collect` lemma/postcondition slice; useful context for the `minor_collect_full` strengthening.
- `generational/impl/GC.Gen.Impl.fst:776-847` — executable body for `minor_collect_full`, including the postconditions about `update_promoted_iter`, `rewrite_slots_iter`, and `CheneySpec.cheney_collect_spec`.
- `generational/impl/GC.Gen.Impl.fst:863-936` — `gen_gc` implementation, which is the next-stage caller that requires the post-minor major-GC precondition.

## Modules mentioned or called from `minor_collect_full`

- `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:1-` — interface for update/rewrite helpers used by `minor_collect_full` (`update_promoted_iter`, `rewrite_slots_iter`, `represents_fwd`, `valid_fwd_entries`, `ref_table_sound`, `ref_table_complete`, `slots_pairwise_distinct`).
- `generational/impl/GC.Gen.Impl.UpdatePtrs.fst:1-` — implementation slice for pointer-update and slot-rewrite helpers.
- `generational/impl/GC.Gen.Impl.Cheney.fst:1-` — imperative Cheney BFS implementation used by `cheney_promote_phase` / `cheney_collect_spec`.
- `generational/impl/GC.Gen.Impl.Promote.fsti:1-` — interface for promotion helpers used in the proof (`rewrite_roots`, forwarding-map/spec exports).
- `generational/impl/GC.Gen.Impl.Promote.fst:1-` — implementation slice for promotion helpers.
- `generational/spec/GC.Gen.Cheney.fsti:1-` — spec interface for Cheney promotion / collection.
- `generational/spec/GC.Gen.Cheney.fst:1-` — spec implementation for Cheney promotion / collection; referenced via `CheneySpec`.
- `generational/spec/GC.Gen.Promote.fsti:1-` — spec interface for root rewriting and promotion-related predicates.
- `generational/spec/GC.Gen.Promote.fst:1-` — spec implementation for promotion-related predicates and root rewriting.
- `generational/spec/GC.Gen.TwoPassEquiv.fsti:1-` — theorem interface stating the equivalence between two-pass rewriting and `update_major_pointers`.
- `generational/spec/GC.Gen.TwoPassEquiv.fst:735-955` — lemmas for `rewrite_slots_iter` behavior used in the equivalence proof.
- `generational/spec/GC.Gen.TwoPassEquiv.fst:1352-1454` — lemmas for promoted-object update + slot rewrite interaction.
- `generational/spec/GC.Gen.TwoPassEquiv.fst:1585-1729` — main theorem slice showing the conditions under which `rewrite_slots_iter (update_promoted_iter ...)` matches `update_major_pointers`.
- `generational/spec/GC.Gen.CheneyPreservation.fsti:1-` — interface for Cheney-preservation facts referenced by the implementation.
- `generational/spec/GC.Gen.CheneyPreservation.fst:1609-2258` — preservation lemmas with current admits in the relevant proof slice.
- `generational/spec/GC.Gen.Allocator.fst:1-` — allocator/spec lemmas referenced indirectly through `GC.Spec.Allocator.Lemmas`.
- `generational/spec/GC.Gen.Allocator.fsti:1-` — allocator interface counterpart.
- `mark-and-sweep/impl/GC.Impl.fsti:31-57` — major-GC precondition/postcondition interface used by `minor_collect_full`/`gen_gc`.
- `mark-and-sweep/impl/GC.Impl.fst:45-81` — implementation of `gc_precondition` and major-GC result contract.
- `mark-and-sweep/spec/GC.Spec.Mark.fsti:254-256` — `no_black_objects` predicate, one of the major-GC preconditions.
- `mark-and-sweep/spec/GC.Spec.MarkBoundedInv.fsti:18-98` — bounded mark invariant interface used by `GC.Impl.gc_precondition`.
- `mark-and-sweep/spec/GC.Spec.Correctness.fsti:35-66` — `gc_postcondition` interface and its introduction/elimination lemmas.
- `mark-and-sweep/spec/GC.Spec.Correctness.fsti:1206-1215` — generalized postcondition bridge lemmas.
- `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.fsti:303-310` — allocator lemma interface preserving `no_black_objects`.
- `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.Core.fst:2375-2623` — allocator lemmas used as proof support for major-heap invariants.

## Major-GC precondition / postcondition modules

- `mark-and-sweep/impl/GC.Impl.fsti:31-57` — `gc_precondition` and `gc_postcondition` contract exposed to clients.
- `mark-and-sweep/impl/GC.Impl.fst:45-57` — concrete predicate bundle for `gc_precondition`.
- `mark-and-sweep/impl/GC.Impl.fst:70-80` — comments and signature for the full GC cycle that consumes the major-GC precondition after minor collection.
- `mark-and-sweep/spec/GC.Spec.Correctness.fsti:35-55` — abstract `gc_postcondition` predicate and intro/elim lemmas.
- `mark-and-sweep/spec/GC.Spec.Mark.fsti:743-745` — `no_black_objects`.
- `mark-and-sweep/spec/GC.Spec.MarkBoundedInv.fsti:18-98` — bounded mark invariant facts that feed the precondition.

## Allocator / free-list lemmas likely relevant to the proof slice

- `generational/impl/GC.Gen.Impl.fsti:104-136` — `AllocLemmas.fl_valid`, `fl_chain_terminates`, and `chain_objects_blue` requirements in the `minor_collect`/`minor_collect_full` preconditions.
- `generational/spec/GC.Gen.AllocProps.fst:1-` — generational allocator properties.
- `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.Core.fsti:1-` — interface for allocator lemmas used by the major heap invariants.
- `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.fsti:1-` — allocator lemma umbrella interface.
- `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.Core.fst:2375-2623` — preservation lemmas for `no_black_objects` under writes/allocation.
- `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.Part2.fst:3257-3507` — part-2 allocator lemmas and the `no_black_objects` preservation slices.
- `common/impl/GC.Impl.Heap.fst:39-40` — platform assumption (`platform_fits_u64`) used across heap code.

## Files with admit / assume / TODO in the relevant slice

- `generational/spec/GC.Gen.TwoPassEquiv.fst:1317` — `admit ()` in a slot-rewrite proof.
- `generational/spec/GC.Gen.TwoPassEquiv.fst:1487-1488` — `TODO` + `admit ()` for field-membership precondition in a rewrite lemma.
- `generational/spec/GC.Gen.CheneyPreservation.fst:1610` — `admit ()` at `__inj_stop`.
- `generational/spec/GC.Gen.CheneyPreservation.fst:2229` — `admit ()` in a preservation lemma.
- `generational/spec/GC.Gen.CheneyPreservation.fst:2258` — `admit ()` in a final preservation lemma.
- `generational/spec/GC.Gen.Promote.fst:1497-1500` — commentary about an `assume` for allocator padding obligations.
- `generational/impl/GC.Gen.Impl.MinorHeap.fst:26` — `assume val platform_fits_u64`.
- `common/impl/GC.Impl.Heap.fst:39-40` — `assume val platform_fits_u64` (shared TCB assumption).
- `generational/impl/GC.Gen.Impl.fsti:289-293` — comment noting the missing major-GC precondition preservation proof path.
- `generational/impl/GC.Gen.Impl.fst:817-876` — `gen_gc` precondition slice that explicitly requires `MajorGC.gc_precondition` on the post-minor heap.
- `generational/impl/GC.Gen.Impl.fst:908-936` — full-correctness path for `gen_gc`, including the major collection call.

## Build targets, verification commands, and include paths

- `generational/Makefile:1-31` — generational build root, F* executable variables, and include paths for `spec`, `impl`, `../common/spec`, `../common/lib`, `../common/impl`, `../mark-and-sweep/spec`, and `../mark-and-sweep/impl`.
- `generational/Makefile:52-61` — special verification target for `impl/GC.Gen.Impl.fst.checked` using `--z3rlimit 160`.
- `generational/Makefile:63-69` — generic `impl/%.checked` verification rule with `--split_queries always`.
- `generational/Makefile:84-88` — `verify` target for all generational `.fst/.fsti` modules.
- `generational/Makefile:108-156` — extraction targets and the module bundle list (`ALL_KRML_MODS` includes `GC.Gen.Impl`, `GC.Gen.Impl.MinorHeap`, `GC.Gen.Impl.Cheney`, `GC.Gen.Impl.Promote`, `GC.Gen.Impl.UpdatePtrs`, plus major-heap modules).
- `generational/Makefile:160-185` — snapshot target and vendored `krmllib` headers.
- `pulsegc.fst.config.json:1-10` — repo-wide F* config: `--report_assumes warn`, cached modules, and include dirs mirroring the build layout.
- `Makefile:1-77` — top-level unified build target that scans all sources with `fstar.exe --dep full` and includes the same project include roots.
- `mark-and-sweep/Makefile:1-31` — major-heap build targets and include paths; relevant because `generational/Makefile` depends on M&S modules.
- `mark-and-sweep/Makefile:135-141` — extraction rule for `FStar.Pervasives.Native` and krml output.
- `generational/ocaml-integration/verified_gc/Makefile:13-15` — C include paths for snapshot headers during runtime integration.
- `mark-and-sweep/ocaml-integration/verified_gc/Makefile:4` — companion C include paths for the M&S verified runtime.

## Existing logs, research docs, and proof notes

- `.atomic/todos/896a8f46.md:3-17` — research task record for `minor_collect_full` proof state.
- `.git/logs/HEAD:368-377` — commit-log entries mentioning `minor_collect_full` integration and strengthening.
- `.git/logs/refs/heads/ws_generational:30-36` — branch-local log entries for the same `minor_collect_full` work.
- `generational/ocaml-integration/verified_gc/OCAML_INTEGRATION.md:204` — API table entry documenting `minor_collect_full`.
- `generational/ocaml-integration/verified_gc/OCAML_INTEGRATION.md:1131-1147` — bridge notes showing `minor_collect_full` as the single verified call.
- `generational/ocaml-integration/verified_gc/OCAML_INTEGRATION.md:1199-1234` — Phase C completion notes for the unified `minor_collect_full` call.
- `generational/ocaml-integration/verified_gc/alloc_gen.c:297-320` — integration call site that invokes `minor_collect_full`.
- `generational/ocaml-integration/verified_gc/profiling_counters.h:35-38,75` — runtime profiling labels naming `minor_collect_full`.
- `PATCHES.md:246,300,401,483` — proof-development notes that mention `GC.Gen.Impl.UpdatePtrs`, `GC.Gen.Impl.Promote`, and related proof-state changes.

## Directory clusters to inspect together

- `generational/impl/` — implementation cluster for `GC.Gen.Impl`, `UpdatePtrs`, `Cheney`, `Promote`, and `MinorHeap`.
- `generational/spec/` — spec cluster for Cheney, Promote, TwoPassEquiv, CheneyPreservation, Allocator, and correctness lemmas.
- `mark-and-sweep/impl/` and `mark-and-sweep/spec/` — major-GC contract and allocator/free-list lemma cluster.
- `generational/ocaml-integration/verified_gc/` — runtime bridge, generated C, and integration docs/logs for the verified generational collector.
