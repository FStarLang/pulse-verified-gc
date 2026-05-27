## Analysis: `minor_collect_full` proof flow

### Overview
`minor_collect_full` is the top-level Pulse entry point for a Cheney minor collection that additionally rewrites a remembered-set/ref-table of major-heap slots. Its implementation first runs the same Cheney promotion and promoted-object update path as `minor_collect`, then calls `rewrite_heap_slots`, rewrites roots, resets the minor heap, and discharges a conditional equality to `cheney_collect_spec(...).mc_major` through the two-pass equivalence theorem.

### Entry Points
- `generational/impl/GC.Gen.Impl.fsti:223` - interface declaration for `minor_collect_full`.
- `generational/impl/GC.Gen.Impl.fst:717` - implementation of `minor_collect_full`.
- `generational/spec/GC.Gen.Cheney.fsti:280` - `cheney_promote` spec used to define the ghost promotion result.
- `generational/spec/GC.Gen.Cheney.fsti:296` - `cheney_collect_spec` full minor-collection spec.
- `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:132` - `rewrite_slots_iter`, the spec model for ref-table slot rewriting.
- `generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:194` - `update_promoted_iter`, the spec model for updating promoted objects only.
- `generational/spec/GC.Gen.TwoPassEquiv.fsti:166` - `promoted_plus_slots_eq_full_update`, the theorem relating two-pass update to full `update_major_pointers`.

### Interface shape and proof obligations

#### Preconditions (`generational/impl/GC.Gen.Impl.fsti:229-250`)
`minor_collect_full` requires ownership of the generational heap plus all arrays it mutates or reads: `is_gen_heap gh 'd 'b 's 'fp`, `pts_to roots 'rs`, `pts_to fwd_arr 'farr`, `pts_to queue 'qv`, and `pts_to slots 'sl` (`generational/impl/GC.Gen.Impl.fsti:229-233`). The pure precondition then bundles:

- Full major heap well-formedness: `SpecFields.well_formed_heap 's` (`generational/impl/GC.Gen.Impl.fsti:234`). This expands to parts 1-4 in `common/spec/GC.Spec.Fields.fst:669-673`.
- Allocator/free-list structure: `fl_valid`, `fl_chain_terminates`, `heap_objects_dense`, and `chain_objects_blue` (`generational/impl/GC.Gen.Impl.fsti:235-238`). `heap_objects_dense` is the linear object-walk density condition (`generational/spec/GC.Gen.Promote.fsti:761-768`); `chain_objects_blue` says every non-blue object is avoided by the free chain (`generational/spec/GC.Gen.Promote.fsti:955-958`).
- Root and forwarding-array setup: `nroots` equals root length, `farr` length equals `UpdatePtrs.fwd_array_size`, and every forwarding entry is initially zero (`generational/impl/GC.Gen.Impl.fsti:239-241`).
- Minor heap structure: `minor_wf`, `minor_guards_complete`, and `minor_infix_wf` on `{data='d; bump='b}` (`generational/impl/GC.Gen.Impl.fsti:242-244`).
- The major heap has at least one object (`generational/impl/GC.Gen.Impl.fsti:245`).
- Ref-table obligations: `nslots <= Seq.length 'sl`, `valid_slot_addrs 'sl nslots`, and `ref_table_sound 's 'sl nslots` (`generational/impl/GC.Gen.Impl.fsti:246-248`). `valid_slot_addrs` requires each listed slot to be word-aligned and inside the heap (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:110-116`).
- Ref-table completeness relative to the ghost promotion result: after defining `prom = cheney_promote ({data='d; bump='b}) 's 'fp 'rs`, the caller must prove `ref_table_complete 's prom.fwd_map 'sl nslots` (`generational/impl/GC.Gen.Impl.fsti:249-250`).

#### Postconditions (`generational/impl/GC.Gen.Impl.fsti:252-288`)
The function returns heap/root/fwd/queue ownership and the unchanged slots array (`generational/impl/GC.Gen.Impl.fsti:254-258`). The pure postcondition defines the same `minor_st` and `prom`, then states:

- The final major heap is exactly the two-pass result: first `UpdatePtrs.update_promoted_iter prom.major_final farr2 prom.fwd_map 0`, then `UpdatePtrs.rewrite_slots_iter ... prom.fwd_map 'sl nslots 0` (`generational/impl/GC.Gen.Impl.fsti:262-265`).
- The final free pointer is `prom.fp_final`, roots equal `PromoteSpec.rewrite_roots 'rs prom.fwd_map`, and the minor bump is reset to zero (`generational/impl/GC.Gen.Impl.fsti:267-272`).
- The final forwarding array represents the ghost forwarding map, contains valid entries, and preserves the fixed length (`generational/impl/GC.Gen.Impl.fsti:274-276`). `represents_fwd` means `farr[i] == fwd(uint_to_t (i*8))` for every forwarding index (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:28-31`).
- Promotion exposes only `well_formed_heap_part1 prom.major_final` directly in this interface (`generational/impl/GC.Gen.Impl.fsti:277`). Unlike `minor_collect`, the full interface does not also expose `fl_valid`, `fl_chain_terminates`, `heap_objects_dense`, `chain_objects_blue`, or object non-emptiness in its postcondition; those are present in the weaker `minor_collect` postcondition at `generational/impl/GC.Gen.Impl.fsti:198-206`.
- Strong correctness is conditional: if `UpdatePtrs.slots_pairwise_distinct 'sl nslots`, then `s2 == (CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs).mc_major` (`generational/impl/GC.Gen.Impl.fsti:278-288`). `slots_pairwise_distinct` requires no duplicate slot addresses among the first `n` entries (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:118-123`).

### Core implementation trace

#### 1. Promotion phase
The implementation unfolds `is_gen_heap`, then calls `cheney_promote_phase gh.minor gh.major gh.fp_ref fwd_arr queue roots nroots` (`generational/impl/GC.Gen.Impl.fst:777-780`). The ghost spec for this phase is `cheney_promote`: it starts from `{cs_major=major; cs_fp=fp; cs_fwd=empty_forwarding; cs_queue=Seq.empty}`, forwards roots, scans the queue for `cheney_fuel minor`, and returns `{major_final; fp_final; fwd_map}` (`generational/spec/GC.Gen.Cheney.fsti:280-290`). After the call, the implementation extracts ghost `ms_post`, `farr_post`, and `fp_post` from the heap, forwarding array, and fp reference (`generational/impl/GC.Gen.Impl.fst:782-785`).

#### 2. Promoted-object pointer update
Before calling `update_promoted_objects`, the implementation derives bounded forwarding and valid concrete forwarding entries: `cheney_promote_fwd_bounded` followed by `fwd_bounded_implies_valid_fwd_entries farr_post prom.fwd_map` (`generational/impl/GC.Gen.Impl.fst:788-792`). `fwd_bounded_implies_valid_fwd_entries` uses `fwd_bounded` plus `represents_fwd` to show every non-zero `farr[i]` is aligned and within heap bounds (`generational/impl/GC.Gen.Impl.fst:223-246`).

It then calls `update_promoted_objects gh.major fwd_arr #(hide prom.fwd_map)` (`generational/impl/GC.Gen.Impl.fst:794-795`). The interface says this loop iterates the forwarding array and updates only promoted objects (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:331-336`), and its spec model is `update_promoted_iter`: for each non-zero forwarding entry, it reads the promoted object's header, checks bounds, `wosize > 0`, `tag < no_scan_tag`, and `tag <> infix_tag`, then applies `PromoteSpec.update_object_pointers` to that object's fields (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:194-221`). The implementation then extracts `ms_updated` and `farr_post2` (`generational/impl/GC.Gen.Impl.fst:797-798`).

#### 3. Ref-table slot rewriting
`minor_collect_full` next calls `rewrite_heap_slots gh.major fwd_arr slots nslots #(hide prom.fwd_map)` (`generational/impl/GC.Gen.Impl.fst:801-802`). The spec of `rewrite_heap_slots` preserves `fwd_arr` and `slots` ownership and ensures the heap becomes `rewrite_slots_iter 'ms fwd 'sl n 0` (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:164-188`). `rewrite_slots_iter` traverses slots `[idx,n)`, skips invalid entries defensively, reads each listed heap word, converts it with `to_minor_offset`, and if it is a minor pointer with a non-zero forwarding target, writes that target into the slot (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:132-156`). The post-slot heap ghost is extracted as `ms_final` (`generational/impl/GC.Gen.Impl.fst:804-805`).

#### 4. Root rewrite and minor reset
The function extracts `farr_post3`, then calls `rewrite_roots_impl roots fwd_arr nroots #(hide prom.fwd_map)` (`generational/impl/GC.Gen.Impl.fst:808-810`). The root-rewrite interface guarantees `rs2 == PromoteSpec.rewrite_roots 'rs fwd` and leaves `fwd_arr` unchanged (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:49-66`). It then calls `minor_heap_reset gh.minor` (`generational/impl/GC.Gen.Impl.fst:813-814`) and finally folds `is_gen_heap gh _ 0UL _ _` (`generational/impl/GC.Gen.Impl.fst:834-835`).

#### 5. Deriving the final heap equality
The unconditional postcondition equality is the composed implementation spec: `s2 == rewrite_slots_iter (update_promoted_iter prom.major_final farr2 prom.fwd_map 0) prom.fwd_map 'sl nslots 0` (`generational/impl/GC.Gen.Impl.fst:757-761`). To prove the conditional full-spec equality, the implementation derives the hypotheses of `two_pass_implies_full_update` and calls it under `Classical.move_requires` (`generational/impl/GC.Gen.Impl.fst:816-832`).

`two_pass_implies_full_update` itself first derives `promoted_entries_valid_from`, `promoted_entries_disjoint`, and `fwd_ptrs_classified`, then invokes `TwoPass.promoted_plus_slots_eq_full_update`, and finally unfolds `cheney_collect_spec` (`generational/impl/GC.Gen.Impl.fst:588-614`). The unfold lemma states `cheney_collect_spec(...).mc_major == PromoteSpec.update_major_pointers prom.major_final prom.fwd_map`, with matching fp and roots (`generational/impl/GC.Gen.Impl.fst:213-220`). Thus the proof chain is:

1. implementation heap = `rewrite_slots_iter (update_promoted_iter prom.major_final farr prom.fwd 0) prom.fwd slots n 0`;
2. two-pass theorem = that expression equals `update_major_pointers prom.major_final prom.fwd_map` (`generational/spec/GC.Gen.TwoPassEquiv.fsti:166-191`);
3. unfold = `update_major_pointers prom.major_final prom.fwd_map` equals `cheney_collect_spec(...).mc_major` (`generational/impl/GC.Gen.Impl.fst:213-220`).

### Relationship of key specs

- `cheney_promote` is promotion only: root forwarding plus BFS scan; it returns `major_final`, `fp_final`, and `fwd_map` (`generational/spec/GC.Gen.Cheney.fsti:280-290`).
- `cheney_collect_spec` composes `cheney_promote` with `update_major_pointers`, `minor_reset`, and `rewrite_roots` (`generational/spec/GC.Gen.Cheney.fsti:296-304`). This is the full spec that updates all major-heap pointer fields via the forwarding map.
- `update_promoted_iter` is the implementation-aligned first pass: scan `fwd_arr`, find promoted objects, and update fields inside those objects only (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:194-221`).
- `rewrite_slots_iter` is the implementation-aligned second pass: scan caller-provided remembered-set slots and update those individual heap words (`generational/impl/GC.Gen.Impl.UpdatePtrs.fsti:132-156`).
- `promoted_plus_slots_eq_full_update` is the bridge: under validity/disjointness/classification/ref-table hypotheses, `rewrite_slots_iter (update_promoted_iter ...)` equals the full `update_major_pointers` used by `cheney_collect_spec` (`generational/spec/GC.Gen.TwoPassEquiv.fsti:166-191`).

### Major heap structural well-formedness exposed now

- `well_formed_heap_part1`: object body/header size bounds; defined at `common/spec/GC.Spec.Fields.fst:649-652`. This is required through full `well_formed_heap` in the precondition and explicitly returned for `prom.major_final` by `minor_collect_full` (`generational/impl/GC.Gen.Impl.fsti:234`, `generational/impl/GC.Gen.Impl.fsti:277`).
- `well_formed_heap_part2`: pointer fields target objects; defined at `common/spec/GC.Spec.Fields.fst:654-660`. It is included in the input `well_formed_heap` but not exposed for `prom.major_final` by `minor_collect_full`.
- `well_formed_heap_part3`: infix well-formedness over `objects zero_addr g`; defined at `common/spec/GC.Spec.Fields.fst:662-663`. It is included in the input `well_formed_heap` but not exposed for `prom.major_final` by `minor_collect_full`.
- `well_formed_heap_part4`: object list contains no infix objects; defined at `common/spec/GC.Spec.Fields.fst:665-666`. It is included in input `well_formed_heap`; the implementation derives `cheney_promote_preserves_wfh_part4` for the two-pass proof (`generational/impl/GC.Gen.Impl.fst:822-823`), but the interface does not return part4.
- Free-list/density/blue-chain conditions are preconditions of `minor_collect_full` (`generational/impl/GC.Gen.Impl.fsti:235-238`). They are preserved/exposed in `minor_collect` (`generational/impl/GC.Gen.Impl.fsti:200-206`), while `minor_collect_full` only exposes `well_formed_heap_part1` plus the conditional full heap equality (`generational/impl/GC.Gen.Impl.fsti:277-288`).

### Preservation lemmas and two-pass equivalence dependencies

The current bridge lemma `two_pass_implies_full_update` requires, for `prom = cheney_promote minor major_pre fp roots`, concrete forwarding representation/length, forwarding classification and injectivity, bounded forwarding, post-promotion part4, slot validity/distinctness/soundness/completeness, target stability, post-promotion part1/density/nonempty, input full well-formedness, minor infix/wf, `chain_objects_blue`, and allocator free-list validity/termination (`generational/impl/GC.Gen.Impl.fst:588-607`).

Inside the bridge, several obligations are derived rather than required from callers:

- `derive_promoted_entries_valid_from` converts `represents_fwd`, `fwd_valid_or_infix`, `fwd_bounded`, and `well_formed_heap_part1` into `promoted_entries_valid_from` (`generational/impl/GC.Gen.Impl.fst:289-326`).
- `derive_promoted_entries_disjoint` uses forwarding validity/injectivity, boundedness, and part1 to prove promoted body disjointness (`generational/impl/GC.Gen.Impl.fst:333-362`).
- `derive_fwd_targets_stable` uses `fwd_above_zero_addr` and `fwd_bounded` to prove forwarded targets are not themselves forwarded minor pointers (`generational/impl/GC.Gen.Impl.fst:250-281`).
- `derive_fwd_ptrs_classified` proves every forwarded minor pointer remaining in `prom.major_final` is accounted for either by a promoted-object entry in `farr` or by a ref-table slot (`generational/impl/GC.Gen.Impl.fst:523-571`). Its case split uses `derive_fwd_case_a` for pre-existing non-blue major objects and `derive_fwd_case_b` for newly promoted objects (`generational/impl/GC.Gen.Impl.fst:403-469`, `generational/impl/GC.Gen.Impl.fst:469-520`).

The implementation obtains the preservation facts immediately before calling the bridge: `cheney_promote_fwd_above_zero_addr`, `derive_fwd_targets_stable`, `cheney_promote_preserves_wfh_part4`, `cheney_promote_fwd_valid_or_infix`, `cheney_promote_fwd_normal_injective`, `cheney_promote_fwd_bounded`, and `cheney_promote_preserves_dense` (`generational/impl/GC.Gen.Impl.fst:818-829`). The final two-pass theorem then supplies equality to `update_major_pointers` (`generational/spec/GC.Gen.TwoPassEquiv.fsti:166-191`), and `cheney_collect_spec_unfold` supplies equality from `update_major_pointers` to `cheney_collect_spec(...).mc_major` (`generational/impl/GC.Gen.Impl.fst:213-220`).
