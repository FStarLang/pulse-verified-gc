# Dead-code inventory

**Generated** by `make depgraph && make depgraph-inventory` — do not edit by hand.

- Roots: `GC.Impl`, `GC.Impl.Allocator`, `GC.Impl.Mark`, `GC.Impl.MarkBounded`, `GC.Impl.Sweep`, `GC.Impl.Coalesce`, `GC.Impl.FusedSweepCoalesce`, `GC.Impl.Fields`, `GC.Impl.Closure`, `GC.Impl.Heap`, `GC.Impl.Object`, `GC.Impl.Stack`, `GC.Gen.Impl`, `GC.Gen.Impl.Cheney`, `GC.Gen.Impl.MinorHeap`, `GC.Gen.Impl.UpdatePtrs`, `GC.Gen.Impl.Promote`, `GC.Spec.Correctness`, `GC.Spec.MarkBoundedCorrectness`, `GC.Gen.CheneyCorrectness`, `GC.Impl.MarkBoundedRootLemmas`, `GC.Spec.FreeList.Sweep`, `GC.SPOT.CallFull`, `GC.SPOT.CallMinor`, `GC.SPOT.ConcreteCallFull`, `GC.SPOT.ConcreteCallMinor`, `GC.SPOT.ConcreteForwarding`, `GC.SPOT.ConcreteFull`, `GC.SPOT.ConcreteMajor`, `GC.SPOT.ConcreteMinor`, `GC.SPOT.ConcreteScenarios`, `GC.SPOT.ConcreteSetup`, `GC.SPOT.Layout`, `GC.SPOT.Postconditions`, `GC.SPOT.Preconditions`, `GC.SPOT.ThreeObjects`

- 151 modules, 3721 definitions, 1243 module edges
- **616 definitions (16%) are unreachable from the roots**
- 2 definitions are reachable only implicitly (SMT pattern / instance / axiom)

## Why this set is safe to delete

Reachability is computed transitively from the roots over every reference in the
`.checked` files, so the unreachable set is **closed**: if a definition is
referenced only by unreachable code, it is itself unreachable and already
appears below. Deleting the whole set therefore cannot strand a live definition,
and one pass reaches the fixpoint — no iterate-until-stable loop is needed.

Three caveats the graph *does* account for:

- **Pulse `fn` bodies.** Pulse type-checks its own definitions and hands F* an
  opaque `magic ()` stub, keeping the elaborated term in a serialised
  `sigmeta_extension_data` blob that is not an F* term. The graph would
  therefore miss every lemma invoked from a `fn` body. For those definitions
  only, the tool re-reads the body from the source and treats each identifier
  as a possible reference; this over-approximates, which is the safe direction.

- **SMT-pattern lemmas.** A lemma carrying `[SMTPat ...]` is used by Z3 without
  ever being named. These are classified *implicitly live*, not unreachable, and
  are excluded from the tables below.
- **Pattern-matched constructors.** `Pat_cons` heads are harvested separately,
  so a constructor that is only ever matched on is not mistaken for dead.

One caveat it does **not** account for: deleting a definition changes the SMT
context of every module that `open`s its module, which can perturb unrelated
proofs. That is why the plan below re-verifies after each phase.


## Removal plan

Phases are ordered by risk. Re-run the full build (`make -k -j24`), the SPOT
build (`make -C spot -j24`) and extraction (`make extract`, expecting a
byte-identical C snapshot) after **each** phase; bisect within a phase if a
proof breaks.

### Phase 1 — delete 9 entirely-dead modules (59 definitions)

Every definition in these modules is unreachable, so the whole `.fst`/`.fsti`
pair goes. Remove the files, then drop any mention of them from `Makefile`,
`*/Makefile` (verification lists, `EAGER_QI_CHECKED`, `EXTRACT_MODULES`) and
any `open`/`include` in surviving modules.

| Module | Defs | Area | Referenced in a Makefile |
| --- | ---: | --- | --- |
| `GC.Gen.PromoteUpdate.PromoteFields.Step` | 24 | generational | `Makefile`, `generational/Makefile` |
| `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres` | 8 | generational | `Makefile`, `generational/Makefile` |
| `GC.Gen.PromoteUpdate.PromoteFields.Frame` | 6 | generational | — |
| `GC.Gen.PromoteUpdate.PromoteFields.ReadOther` | 6 | generational | `Makefile`, `generational/Makefile` |
| `GC.Gen.PromoteUpdate.PromoteFields.ChainInv` | 4 | generational | — |
| `GC.Spec.Allocator.Lemmas.SearchBase` | 4 | mark-and-sweep | — |
| `GC.Gen.PromoteUpdate.PromoteFields` | 3 | generational | `Makefile`, `generational/Makefile` |
| `GC.Spec.Allocator.Lemmas.SearchChain` | 3 | mark-and-sweep | `Makefile`, `mark-and-sweep/Makefile` |
| `GC.Spec.Allocator.Lemmas.ObjNotInChain` | 1 | mark-and-sweep | — |

### Phase 2 — trim 55 partially-dead modules (557 definitions)

These modules keep some live definitions, so delete individual definitions
rather than files. Work highest-density first: a module that is 70% dead is
usually a proof scaffold whose intermediate lemmas were inlined or superseded.

| Module | Defs | Dead | % | Area |
| --- | ---: | ---: | ---: | --- |
| `GC.Spec.Heap` | 92 | 60 | 65 | common |
| `GC.Spec.Allocator.Lemmas.Core` | 79 | 56 | 70 | mark-and-sweep |
| `GC.Gen.Promote` | 130 | 50 | 38 | generational |
| `GC.Gen.MinorCollectForwarding` | 123 | 45 | 36 | generational |
| `GC.Spec.Allocator.Lemmas` | 59 | 25 | 42 | mark-and-sweep |
| `GC.Spec.Graph` | 100 | 24 | 24 | common |
| `GC.Spec.Allocator.Lemmas.Split` | 23 | 21 | 91 | mark-and-sweep |
| `GC.Spec.Fields` | 93 | 20 | 21 | common |
| `GC.Spec.Object` | 136 | 20 | 14 | common |
| `GC.Gen.Cheney.SimOne` | 34 | 15 | 44 | generational |
| `GC.Gen.PromoteUpdate.Header` | 22 | 15 | 68 | generational |
| `GC.Gen.PromoteUpdate` | 29 | 13 | 44 | generational |
| `GC.Lib.Header` | 84 | 11 | 13 | common |
| `GC.Lib.Address` | 15 | 10 | 66 | common |
| `GC.Spec.Mark` | 144 | 10 | 6 | mark-and-sweep |
| `GC.Impl.Sweep.Lemmas` | 43 | 9 | 20 | mark-and-sweep |
| `GC.Gen.Cheney.Sim` | 20 | 8 | 40 | generational |
| `GC.Gen.CombinedGraph` | 107 | 8 | 7 | generational |
| `GC.Gen.HeapInvariant` | 35 | 8 | 22 | generational |
| `GC.Spec.Allocator` | 40 | 8 | 20 | mark-and-sweep |
| `GC.Spec.Coalesce` | 68 | 8 | 11 | mark-and-sweep |
| `GC.Gen.Base` | 25 | 7 | 28 | generational |
| `GC.Spec.Allocator.Lemmas.Header` | 12 | 7 | 58 | mark-and-sweep |
| `GC.Spec.Allocator.Lemmas.Part2` | 56 | 7 | 12 | mark-and-sweep |
| `GC.Spec.FreeList` | 25 | 7 | 28 | mark-and-sweep |
| `GC.Spec.Sweep` | 56 | 7 | 12 | mark-and-sweep |
| `GC.Gen.CheneyPreservation.Forwarding` | 58 | 6 | 10 | generational |
| `GC.Spec.MarkBoundedInv` | 15 | 6 | 40 | mark-and-sweep |
| `GC.Gen.AllocProps` | 36 | 5 | 13 | generational |
| `GC.Spec.Allocator.Lemmas.Chain` | 48 | 5 | 10 | mark-and-sweep |
| `GC.Spec.Base` | 20 | 5 | 25 | common |
| `GC.Spec.MarkInv` | 18 | 5 | 27 | mark-and-sweep |
| `GC.Gen.MinorHeap` | 85 | 4 | 4 | generational |
| `GC.Gen.PromoteUpdate.Aux` | 9 | 4 | 44 | generational |
| `GC.Gen.PromoteUpdate.BlueProm` | 23 | 4 | 17 | generational |
| `GC.Spec.DFS` | 32 | 4 | 12 | common |
| `GC.Spec.MarkBounded` | 48 | 3 | 6 | mark-and-sweep |
| `GC.Spec.SweepCoalesce.Defs` | 5 | 3 | 60 | mark-and-sweep |
| `GC.Spec.SweepCoalesce.FlushAgree` | 11 | 3 | 27 | mark-and-sweep |
| `GC.Spec.SweepInv` | 44 | 3 | 6 | mark-and-sweep |
| `GC.Gen.MinorCollectForwarding.Helpers` | 29 | 2 | 6 | generational |
| `GC.Gen.TwoPassEquiv` | 42 | 2 | 4 | generational |
| `GC.Impl.FusedSweepCoalesce.Lemmas` | 14 | 2 | 14 | mark-and-sweep |
| `GC.Gen.Cheney` | 92 | 1 | 1 | generational |
| `GC.Gen.CheneyBFS` | 36 | 1 | 2 | generational |
| `GC.Gen.CheneyPreservation` | 65 | 1 | 1 | generational |
| `GC.Gen.CheneyPreservation.Fields` | 44 | 1 | 2 | generational |
| `GC.Gen.CheneyPreservation.Injectivity` | 44 | 1 | 2 | generational |
| `GC.Gen.MinorCollectForwarding.NormalEdges` | 14 | 1 | 7 | generational |
| `GC.Gen.PromoteUpdate.Field` | 9 | 1 | 11 | generational |
| `GC.Impl.Coalesce.Lemmas` | 19 | 1 | 5 | mark-and-sweep |
| `GC.Spec.HeapGraph` | 32 | 1 | 3 | common |
| `GC.Spec.HeapModel` | 5 | 1 | 20 | common |
| `GC.Spec.SweepCoalesce.Helpers` | 16 | 1 | 6 | mark-and-sweep |
| `GC.Spec.SweepCoalesce.Induction` | 22 | 1 | 4 | mark-and-sweep |

### Phase 3 — re-run and confirm the fixpoint

`make depgraph` again. The dead count should be 0; anything left is a
definition that only the deleted code kept alive and is safe to remove too.

## Full inventory

Every one of the 616 unreachable definitions, grouped by module.

<details>
<summary><code>GC.Gen.PromoteUpdate.PromoteFields.Step</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `chain_avoids_implies_not_in_fl_chain` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:31:8` |
| `copy_fields_preserves_chain_avoids_self` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:32:8` |
| `copy_fields_preserves_fl_chain_terminates` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:29:8` |
| `copy_fields_preserves_fl_valid_aux` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:28:8` |
| `copy_fields_preserves_objects_aux` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:27:8` |
| `copy_fields_preserves_wfh_part1` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:30:8` |
| `fields_match_minor_elim` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:71:8` |
| `gt_mul8_step` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:44:8` |
| `index_ne_gives_lt` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:57:8` |
| `mk_hp_addr` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:65:8` |
| `promote_object_chain_avoids_self` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:479:8` |
| `promote_object_wosize_preserved` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:288:0` |
| `promote_object_wosize_self` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:397:8` |
| `promote_object_wosize_self_full` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:592:8` |
| `promote_step_chain_forall` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:241:8` |
| `promote_step_chain_k` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:433:8` |
| `promote_step_chain_one_k` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:639:8` |
| `promote_step_establish_chain_all` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:709:8` |
| `promote_step_fields_forall` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:134:8` |
| `promote_step_one_field_other` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:92:8` |
| `promote_step_preserves_basic` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:197:8` |
| `promote_step_preserves_invariant` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:747:0` |
| `set_promoted_tag_preserves_wosize_self` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:574:8` |
| `set_tag_preserves_read_at_obj_step` | let | `GC.Gen.PromoteUpdate.PromoteFields.Step.fst:458:8` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.PromoteFields.FieldsPres</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `chain_all_inv_extend_skip` | let | `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:28:8` |
| `distinct_live_set` | let | `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fsti:19:0` |
| `fields_match_minor_extend_zero` | let rec | `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:66:8` |
| `fwd_zero_from` | let | `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:110:0` |
| `ne_idx_gives_lt` | let | `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:21:8` |
| `promote_all_aux_preserves_fields` | let rec | `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:117:8` |
| `promote_all_preserves_fields` | let | `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:165:0` |
| `promote_all_step_case` | let | `GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:89:8` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.PromoteFields.Frame</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `copy_fields_preserves_fl_chain_terminates` | let | `GC.Gen.PromoteUpdate.PromoteFields.Frame.fst:23:8` |
| `copy_fields_preserves_fl_valid_aux` | let | `GC.Gen.PromoteUpdate.PromoteFields.Frame.fst:22:8` |
| `copy_fields_preserves_wfh_part1` | let | `GC.Gen.PromoteUpdate.PromoteFields.Frame.fst:21:8` |
| `promote_all_aux_read_other` | let rec | `GC.Gen.PromoteUpdate.PromoteFields.Frame.fst:65:8` |
| `promote_all_read_other` | let | `GC.Gen.PromoteUpdate.PromoteFields.Frame.fst:107:0` |
| `promote_step_frame_preconditions` | let | `GC.Gen.PromoteUpdate.PromoteFields.Frame.fst:29:8` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.PromoteFields.ReadOther</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `mk_hp_addr` | let | `GC.Gen.PromoteUpdate.PromoteFields.ReadOther.fst:214:8` |
| `other_ranges_disjoint` | let | `GC.Gen.PromoteUpdate.PromoteFields.ReadOther.fst:26:8` |
| `promote_object_preserves_chain_avoids` | let | `GC.Gen.PromoteUpdate.PromoteFields.ReadOther.fst:155:0` |
| `promote_object_preserves_one_field` | let | `GC.Gen.PromoteUpdate.PromoteFields.ReadOther.fst:220:0` |
| `promote_object_read_other` | let | `GC.Gen.PromoteUpdate.PromoteFields.ReadOther.fst:45:0` |
| `promote_transfer_read` | let | `GC.Gen.PromoteUpdate.PromoteFields.ReadOther.fst:116:8` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.PromoteFields.ChainInv</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `chain_all_inv` | let | `GC.Gen.PromoteUpdate.PromoteFields.ChainInv.fst:18:0` |
| `chain_all_inv_elim` | let | `GC.Gen.PromoteUpdate.PromoteFields.ChainInv.fst:41:0` |
| `chain_all_inv_elim_at` | let | `GC.Gen.PromoteUpdate.PromoteFields.ChainInv.fst:59:0` |
| `chain_all_inv_intro` | let | `GC.Gen.PromoteUpdate.PromoteFields.ChainInv.fst:28:0` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas.SearchBase</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_exact_fl_transfer_pre` | let | `GC.Spec.Allocator.Lemmas.SearchBase.fst:202:0` |
| `alloc_from_block_objects_facts` | let | `GC.Spec.Allocator.Lemmas.SearchBase.fst:61:0` |
| `alloc_split_fl_transfer_pre` | let | `GC.Spec.Allocator.Lemmas.SearchBase.fst:109:0` |
| `next_fp_in_objects` | let | `GC.Spec.Allocator.Lemmas.SearchBase.fst:24:0` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.PromoteFields</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `distinct_live_set` | let | `GC.Gen.PromoteUpdate.PromoteFields.fsti:25:0` |
| `promote_all_preserves_fields` | let | `GC.Gen.PromoteUpdate.PromoteFields.fst:26:0` |
| `promote_all_read_other` | let | `GC.Gen.PromoteUpdate.PromoteFields.fst:37:0` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas.SearchChain</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `aligned_distinct` | let | `GC.Spec.Allocator.Lemmas.SearchChain.fst:32:8` |
| `alloc_search_preserves_fl_chain_terminates` | let rec | `GC.Spec.Allocator.Lemmas.SearchChain.fst:48:8` |
| `alloc_spec_preserves_fl_chain_terminates` | let | `GC.Spec.Allocator.Lemmas.SearchChain.fst:401:0` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas.ObjNotInChain</code> — **entire module is dead**</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_spec_obj_not_in_chain` | let | `GC.Spec.Allocator.Lemmas.ObjNotInChain.fst:23:0` |

</details>

<details>
<summary><code>GC.Spec.Heap</code> — 60/92 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `Mkobject_l` | datacon | `GC.Spec.Heap.fsti:194:5` |
| `children` | let | `GC.Spec.Heap.fst:955:0` |
| `children_of` | let | `GC.Spec.Heap.fst:950:0` |
| `children_of_fields` | let rec | `GC.Spec.Heap.fst:942:0` |
| `entry_check` | let | `GC.Spec.Heap.fsti:336:0` |
| `entry_check_at` | let | `GC.Spec.Heap.fsti:346:0` |
| `entry_check_field_upd` | let | `GC.Spec.Heap.fst:864:0` |
| `field_index_step` | let | `GC.Spec.Heap.fst:294:8` |
| `for_all_seq_upd` | let rec | `GC.Spec.Heap.fst:842:0` |
| `heap_l` | let | `GC.Spec.Heap.fsti:386:5` |
| `heap_l_domain` | let | `GC.Spec.Heap.fst:655:0` |
| `lookup` | let | `GC.Spec.Heap.fst:649:0` |
| `make_header_word` | let | `GC.Spec.Heap.fst:663:0` |
| `object_l` | type | `GC.Spec.Heap.fsti:194:5` |
| `pack` | let | `GC.Spec.Heap.fst:723:0` |
| `pointer_closed` | let | `GC.Spec.Heap.fst:559:0` |
| `pointer_closed_ext` | let | `GC.Spec.Heap.fst:555:0` |
| `pointer_closed_ext_cons` | let | `GC.Spec.Heap.fst:568:0` |
| `pointer_closed_ext_eq` | let | `GC.Spec.Heap.fst:563:0` |
| `pointer_closed_ext_find_check` | let rec | `GC.Spec.Heap.fst:828:0` |
| `pointer_closed_ext_nil` | let | `GC.Spec.Heap.fst:574:0` |
| `pointer_closed_ext_replace` | let rec | `GC.Spec.Heap.fst:778:0` |
| `pointer_closed_ext_update` | let rec | `GC.Spec.Heap.fst:762:0` |
| `pointer_closed_from_universal` | let rec | `GC.Spec.Heap.fst:581:0` |
| `pointer_closed_from_universal_0` | let | `GC.Spec.Heap.fst:622:0` |
| `pointer_closed_implies_unpack` | let | `GC.Spec.Heap.fst:643:0` |
| `read_fields` | let rec | `GC.Spec.Heap.fst:301:0` |
| `read_fields_index` | let rec | `GC.Spec.Heap.fst:348:0` |
| `read_fields_succeeds` | let rec | `GC.Spec.Heap.fst:332:0` |
| `replace_range` | let | `GC.Spec.Heap.fst:148:0` |
| `unpack` | let | `GC.Spec.Heap.fst:637:0` |
| `unpack_color_total` | let | `GC.Spec.Heap.fst:324:0` |
| `unpack_object` | let | `GC.Spec.Heap.fst:374:0` |
| `unpack_object_addr` | let | `GC.Spec.Heap.fst:426:0` |
| `unpack_object_color` | let | `GC.Spec.Heap.fst:446:0` |
| `unpack_object_fields` | let | `GC.Spec.Heap.fst:453:0` |
| `unpack_object_succeeds` | let | `GC.Spec.Heap.fst:404:0` |
| `unpack_object_tag` | let | `GC.Spec.Heap.fst:439:0` |
| `unpack_object_wz` | let | `GC.Spec.Heap.fst:432:0` |
| `unpack_objects` | let rec | `GC.Spec.Heap.fst:463:0` |
| `unpack_objects_cons` | let | `GC.Spec.Heap.fst:498:0` |
| `unpack_objects_empty_overflow` | let | `GC.Spec.Heap.fst:487:0` |
| `unpack_objects_empty_start` | let | `GC.Spec.Heap.fst:481:0` |
| `unpack_objects_head` | let | `GC.Spec.Heap.fst:524:0` |
| `unpack_objects_mem_tail` | let | `GC.Spec.Heap.fst:543:0` |
| `unpack_objects_singleton` | let | `GC.Spec.Heap.fst:512:0` |
| `update_color_l` | let | `GC.Spec.Heap.fst:810:0` |
| `update_color_l_preserves_domain` | let | `GC.Spec.Heap.fst:820:0` |
| `update_color_preserves_closed` | let | `GC.Spec.Heap.fst:792:0` |
| `update_entry` | let rec | `GC.Spec.Heap.fst:735:0` |
| `update_entry_preserves_addrs` | let rec | `GC.Spec.Heap.fst:744:0` |
| `update_field_l` | let | `GC.Spec.Heap.fst:910:0` |
| `update_field_l_preserves_domain` | let | `GC.Spec.Heap.fst:927:0` |
| `update_field_preserves_closed` | let | `GC.Spec.Heap.fst:885:0` |
| `valid_field_value` | let | `GC.Spec.Heap.fsti:434:0` |
| `write_field` | let | `GC.Spec.Heap.fst:673:0` |
| `write_fields` | let rec | `GC.Spec.Heap.fst:682:0` |
| `write_object` | let | `GC.Spec.Heap.fst:695:0` |
| `write_objects` | let rec | `GC.Spec.Heap.fst:706:0` |
| `zero_heap` | let | `GC.Spec.Heap.fst:720:0` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas.Core</code> — 56/79 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_exact_fl_transfer_pre` | let | `GC.Spec.Allocator.Lemmas.Core.fst:405:0` |
| `alloc_from_block_objects_facts` | let | `GC.Spec.Allocator.Lemmas.Core.fst:44:0` |
| `alloc_from_block_preserves_no_black` | let | `GC.Spec.Allocator.Lemmas.Core.fst:947:8` |
| `alloc_from_block_preserves_wf` | let | `GC.Spec.Allocator.Lemmas.Core.fst:37:0` |
| `alloc_search_preserves_fl_valid` | let rec | `GC.Spec.Allocator.Lemmas.Core.fst:447:0` |
| `alloc_search_preserves_no_black` | let rec | `GC.Spec.Allocator.Lemmas.Core.fst:1050:0` |
| `alloc_search_preserves_objects` | let rec | `GC.Spec.Allocator.Lemmas.Core.fst:201:0` |
| `alloc_search_preserves_wf` | let rec | `GC.Spec.Allocator.Lemmas.Core.fst:47:0` |
| `alloc_spec_obj_not_in_chain` | let | `GC.Spec.Allocator.Lemmas.Core.fst:1171:0` |
| `alloc_spec_preserves_fl_chain_terminates` | let | `GC.Spec.Allocator.Lemmas.Core.fst:840:0` |
| `alloc_spec_preserves_fl_valid` | let | `GC.Spec.Allocator.Lemmas.Core.fst:806:0` |
| `alloc_spec_preserves_no_black` | let | `GC.Spec.Allocator.Lemmas.Core.fst:1148:0` |
| `alloc_spec_preserves_objects` | let | `GC.Spec.Allocator.Lemmas.Core.fst:845:0` |
| `alloc_spec_preserves_wf` | let | `GC.Spec.Allocator.Lemmas.Core.fst:166:0` |
| `alloc_split_fl_transfer_pre` | let | `GC.Spec.Allocator.Lemmas.Core.fst:404:0` |
| `chain_avoids_prev` | let | `GC.Spec.Allocator.Lemmas.Core.fst:824:0` |
| `chain_avoids_strengthen` | let | `GC.Spec.Allocator.Lemmas.Core.fst:821:0` |
| `chain_avoids_transfer_excl` | let | `GC.Spec.Allocator.Lemmas.Core.fst:1168:0` |
| `chain_avoids_unfold_step` | let | `GC.Spec.Allocator.Lemmas.Core.fst:815:0` |
| `chain_avoids_unfold_steps` | let | `GC.Spec.Allocator.Lemmas.Core.fst:1170:0` |
| `chain_avoids_weaken` | let | `GC.Spec.Allocator.Lemmas.Core.fst:820:0` |
| `field_write_preserves_no_black` | let | `GC.Spec.Allocator.Lemmas.Core.fst:912:8` |
| `first_hit` | let | `GC.Spec.Allocator.Lemmas.Core.fsti:227:0` |
| `first_hit_spec` | let | `GC.Spec.Allocator.Lemmas.Core.fst:822:0` |
| `fl_chain_2cycle_not_terminates` | let | `GC.Spec.Allocator.Lemmas.Core.fst:191:0` |
| `fl_chain_kcycle_not_terminates` | let | `GC.Spec.Allocator.Lemmas.Core.fst:190:0` |
| `fl_chain_no_early_repeat` | let | `GC.Spec.Allocator.Lemmas.Core.fst:828:0` |
| `fl_chain_predecessor_not_in_suffix_b` | let | `GC.Spec.Allocator.Lemmas.Core.fst:826:0` |
| `fl_chain_terminates_splice` | let | `GC.Spec.Allocator.Lemmas.Core.fst:192:0` |
| `fl_chain_terminates_transfer` | let | `GC.Spec.Allocator.Lemmas.Core.fst:178:0` |
| `fl_chain_terminates_transfer_excl` | let | `GC.Spec.Allocator.Lemmas.Core.fst:827:0` |
| `fl_chain_terminates_unfold_steps` | let | `GC.Spec.Allocator.Lemmas.Core.fst:189:0` |
| `fl_chain_terminates_weaken` | let | `GC.Spec.Allocator.Lemmas.Core.fst:179:0` |
| `fl_valid_any_fuel` | let | `GC.Spec.Allocator.Lemmas.Core.fst:177:0` |
| `fl_valid_field_write` | let | `GC.Spec.Allocator.Lemmas.Core.fst:193:0` |
| `fl_valid_field_write_tail` | let | `GC.Spec.Allocator.Lemmas.Core.fst:194:0` |
| `fl_valid_next` | let | `GC.Spec.Allocator.Lemmas.Core.fsti:46:0` |
| `fl_valid_transfer` | let | `GC.Spec.Allocator.Lemmas.Core.fst:175:0` |
| `fl_valid_weaken` | let | `GC.Spec.Allocator.Lemmas.Core.fsti:84:0` |
| `make_header_color_blue` | let | `GC.Spec.Allocator.Lemmas.Core.fst:898:0` |
| `make_header_color_white` | let | `GC.Spec.Allocator.Lemmas.Core.fst:889:8` |
| `make_header_getTag` | let | `GC.Spec.Allocator.Lemmas.Core.fst:36:0` |
| `next_fp_in_objects` | let | `GC.Spec.Allocator.Lemmas.Core.fst:43:0` |
| `next_fp_ne_rem_obj` | let | `GC.Spec.Allocator.Lemmas.Core.fst:415:8` |
| `not_in_fl_chain_b` | let | `GC.Spec.Allocator.Lemmas.Core.fsti:238:0` |
| `not_in_fl_chain_b_is_chain_avoids` | let | `GC.Spec.Allocator.Lemmas.Core.fst:825:0` |
| `walk_chain` | let | `GC.Spec.Allocator.Lemmas.Core.fsti:125:0` |
| `walk_chain_append` | let | `GC.Spec.Allocator.Lemmas.Core.fst:188:0` |
| `walk_chain_one_step` | let | `GC.Spec.Allocator.Lemmas.Core.fst:823:0` |
| `walk_chain_valid` | let | `GC.Spec.Allocator.Lemmas.Core.fsti:128:0` |
| `walk_chain_valid_at` | let | `GC.Spec.Allocator.Lemmas.Core.fst:186:0` |
| `walk_chain_valid_prefix` | let | `GC.Spec.Allocator.Lemmas.Core.fst:185:0` |
| `walk_chain_valid_preserved` | let | `GC.Spec.Allocator.Lemmas.Core.fst:829:0` |
| `walk_chain_valid_snoc` | let | `GC.Spec.Allocator.Lemmas.Core.fst:187:0` |
| `walk_chain_valid_zero` | let | `GC.Spec.Allocator.Lemmas.Core.fst:184:0` |
| `walk_chain_zero` | let | `GC.Spec.Allocator.Lemmas.Core.fst:183:0` |

</details>

<details>
<summary><code>GC.Gen.Promote</code> — 50/130 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `copy_fields_preserves_alloc_invariants` | let | `GC.Gen.Promote.fst:1097:0` |
| `copy_fields_preserves_chain_avoids_self` | let | `GC.Gen.Promote.fst:1041:8` |
| `copy_fields_preserves_fl_chain_terminates` | let | `GC.Gen.Promote.fst:1040:8` |
| `copy_fields_preserves_fl_valid_aux` | let | `GC.Gen.Promote.fst:1039:8` |
| `copy_fields_preserves_objects` | let | `GC.Gen.Promote.fst:1045:0` |
| `dec_nat` | let | `GC.Gen.Promote.fst:39:8` |
| `dst_field_addr` | let | `GC.Gen.Promote.fsti:568:0` |
| `fields_match_minor` | let rec | `GC.Gen.Promote.fsti:867:0` |
| `fields_match_minor_elim_helper` | let rec | `GC.Gen.Promote.fst:2212:0` |
| `fields_match_minor_elim_lemma` | let | `GC.Gen.Promote.fst:2235:0` |
| `fields_match_minor_empty` | let | `GC.Gen.Promote.fst:2185:0` |
| `fields_match_minor_extend` | let | `GC.Gen.Promote.fst:2192:0` |
| `fields_match_minor_frame` | let rec | `GC.Gen.Promote.fst:2313:0` |
| `fields_match_minor_intro` | let rec | `GC.Gen.Promote.fst:2270:0` |
| `fields_match_minor_intro_by_proof` | let rec | `GC.Gen.Promote.fst:2337:0` |
| `fields_match_minor_intro_flat` | let rec | `GC.Gen.Promote.fst:2292:0` |
| `fields_match_minor_weaken` | let rec | `GC.Gen.Promote.fst:2256:0` |
| `fwd_all_targets_valid` | let | `GC.Gen.Promote.fsti:834:0` |
| `fwd_targets_in_objects` | let | `GC.Gen.Promote.fsti:824:0` |
| `live_set_no_infix` | let | `GC.Gen.Promote.fsti:742:0` |
| `lt_of_ne_pred` | let | `GC.Gen.Promote.fst:30:8` |
| `minor_collect_all_spec` | let | `GC.Gen.Promote.fsti:1011:0` |
| `minor_collect_resets_minor` | let | `GC.Gen.Promote.fst:786:0` |
| `minor_collect_rewrites_roots` | let | `GC.Gen.Promote.fst:791:0` |
| `minor_collect_spec` | let | `GC.Gen.Promote.fsti:519:0` |
| `minor_collect_spec_unfold` | let | `GC.Gen.Promote.fst:777:0` |
| `not_in_fl_chain` | let | `GC.Gen.Promote.fst:1025:0` |
| `pointer_closure_modulo_fwd` | let | `GC.Gen.Promote.fsti:842:0` |
| `promote_all_aux` | let rec | `GC.Gen.Promote.fsti:296:0` |
| `promote_all_aux_base` | let | `GC.Gen.Promote.fst:665:0` |
| `promote_all_aux_oom` | let | `GC.Gen.Promote.fst:699:0` |
| `promote_all_aux_preserves_no_scan_invariant` | let rec | `GC.Gen.Promote.fst:2104:8` |
| `promote_all_aux_preserves_objects` | let rec | `GC.Gen.Promote.fst:1163:0` |
| `promote_all_aux_preserves_wfh_part1` | let rec | `GC.Gen.Promote.fst:1236:0` |
| `promote_all_aux_preserves_wfh_part4` | let rec | `GC.Gen.Promote.fst:1380:0` |
| `promote_all_aux_skip` | let | `GC.Gen.Promote.fst:690:0` |
| `promote_all_aux_step` | let | `GC.Gen.Promote.fst:673:0` |
| `promote_all_preserves_no_scan_invariant` | let | `GC.Gen.Promote.fst:2168:0` |
| `promote_all_preserves_objects` | let | `GC.Gen.Promote.fst:1223:0` |
| `promote_all_preserves_wfh_part1` | let | `GC.Gen.Promote.fst:1284:0` |
| `promote_all_preserves_wfh_part4` | let | `GC.Gen.Promote.fst:1439:0` |
| `promote_all_spec` | let | `GC.Gen.Promote.fsti:317:0` |
| `promote_object_preserves_allocated_avoid_chain` | let | `GC.Gen.Promote.fst:1925:8` |
| `promote_object_preserves_objects` | let | `GC.Gen.Promote.fst:1058:0` |
| `write_body_preserves_chain_avoids_self` | let | `GC.Gen.Promote.fst:1035:8` |
| `write_body_preserves_fl_chain_terminates` | let | `GC.Gen.Promote.fst:1034:8` |
| `write_body_preserves_fl_valid_aux` | let | `GC.Gen.Promote.fst:1032:8` |
| `write_body_preserves_not_in_fl_chain` | let | `GC.Gen.Promote.fst:1033:8` |
| `write_body_preserves_objects` | let | `GC.Gen.Promote.fst:1031:8` |
| `zero_promote_padding_frame'` | let | `GC.Gen.Promote.fst:194:0` |

</details>

<details>
<summary><code>GC.Gen.MinorCollectForwarding</code> — 45/123 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `combined_major_minor_edge_forwarded` | let | `GC.Gen.MinorCollectForwarding.fst:63:0` |
| `combined_minor_reachable_in_live_set` | let | `GC.Gen.MinorCollectForwarding.fsti:224:0` |
| `combined_minor_reachable_in_minor_reachable` | let | `GC.Gen.MinorCollectForwarding.fsti:229:0` |
| `combined_reachable_images_valid_or_infix` | let | `GC.Gen.MinorCollectForwarding.fst:59:0` |
| `combined_reachable_images_valid_or_infix_from_slots` | let | `GC.Gen.MinorCollectForwarding.fst:60:0` |
| `combined_reachable_images_valid_or_infix_prop` | let | `GC.Gen.MinorCollectForwarding.fsti:278:0` |
| `combined_reachable_images_valid_or_infix_remembered_imp` | let | `GC.Gen.MinorCollectForwarding.fst:2062:8` |
| `combined_reachable_images_valid_or_infix_reuse` | let | `GC.Gen.MinorCollectForwarding.fst:1917:8` |
| `combined_reachable_images_valid_or_infix_reuse_from_slots` | let | `GC.Gen.MinorCollectForwarding.fst:1935:8` |
| `combined_reachable_images_valid_or_infix_slots_imp` | let | `GC.Gen.MinorCollectForwarding.fst:1957:8` |
| `combined_reachable_major_edge_forwarded` | let | `GC.Gen.MinorCollectForwarding.fst:61:0` |
| `combined_reachable_normal_edges_forwarded_from_slots` | let | `GC.Gen.MinorCollectForwarding.fst:1042:8` |
| `combined_reachable_normal_edges_forwarded_prop` | let | `GC.Gen.MinorCollectForwarding.fsti:559:0` |
| `combined_reachable_normal_edges_forwarded_slots_imp` | let | `GC.Gen.MinorCollectForwarding.fst:1986:8` |
| `header_eq_preserves_wosize_no_scan` | let | `GC.Gen.MinorCollectForwarding.fst:56:0` |
| `heap_field_points_to_graph_edge` | let | `GC.Gen.MinorCollectForwarding.fst:51:0` |
| `heap_graph_edge_to_pointer_field` | let | `GC.Gen.MinorCollectForwarding.fst:52:0` |
| `minor_collect_full_forwarding_kernel` | let | `GC.Gen.MinorCollectForwarding.fsti:1043:0` |
| `minor_collect_full_forwarding_kernel_intro` | let | `GC.Gen.MinorCollectForwarding.fst:2088:0` |
| `minor_source_edge_not_no_scan` | let | `GC.Gen.MinorCollectForwarding.fst:71:0` |
| `normal_image_edges_are_post_edges` | let | `GC.Gen.MinorCollectForwarding.fst:1012:0` |
| `normal_image_edges_are_post_edges_prop` | let | `GC.Gen.MinorCollectForwarding.fsti:779:0` |
| `normal_image_kernel_props_slots_imp` | let | `GC.Gen.MinorCollectForwarding.fst:2014:8` |
| `normal_image_vertices_are_post_vertices` | let | `GC.Gen.MinorCollectForwarding.fst:326:0` |
| `normal_image_vertices_are_post_vertices_prop` | let | `GC.Gen.MinorCollectForwarding.fsti:721:0` |
| `normal_post_image_reachable` | let | `GC.Gen.MinorCollectForwarding.fsti:951:0` |
| `normal_post_image_reachable_subgraph_isomorphism` | let | `GC.Gen.MinorCollectForwarding.fst:1641:0` |
| `normal_post_image_reachable_subgraph_isomorphism_prop` | let | `GC.Gen.MinorCollectForwarding.fsti:957:0` |
| `promoted_minor_major_edge_forwarded` | let | `GC.Gen.MinorCollectForwarding.fst:65:0` |
| `promoted_minor_major_field_preserved` | let | `GC.Gen.MinorCollectForwarding.fst:64:0` |
| `promoted_minor_minor_edge_forwarded` | let | `GC.Gen.MinorCollectForwarding.fst:67:0` |
| `promoted_minor_minor_field_forwarded` | let | `GC.Gen.MinorCollectForwarding.fst:66:0` |
| `reachable_subgraph_isomorphism` | let | `GC.Gen.MinorCollectForwarding.fsti:218:0` |
| `ready_image_edge` | let | `GC.Gen.MinorCollectForwarding.fsti:674:0` |
| `ready_image_reachable_is_post_reachable_all` | let | `GC.Gen.MinorCollectForwarding.fst:1291:0` |
| `ready_image_reachable_is_post_reachable_prop` | let | `GC.Gen.MinorCollectForwarding.fsti:865:0` |
| `ready_image_reachable_subgraph_isomorphism` | let | `GC.Gen.MinorCollectForwarding.fst:1332:0` |
| `ready_image_reachable_subgraph_isomorphism_prop` | let | `GC.Gen.MinorCollectForwarding.fsti:683:0` |
| `ready_src_edge` | let | `GC.Gen.MinorCollectForwarding.fsti:667:0` |
| `ready_src_reach_normal_src_reachable` | let | `GC.Gen.MinorCollectForwarding.fst:1313:8` |
| `remembered_slot_targets` | let | `GC.Gen.MinorCollectForwarding.fsti:61:0` |
| `remembered_slot_targets_from` | let | `GC.Gen.MinorCollectForwarding.fst:47:0` |
| `remembered_slot_targets_zero` | let | `GC.Gen.MinorCollectForwarding.fst:2174:0` |
| `roots_with_remembered` | let | `GC.Gen.MinorCollectForwarding.fsti:65:0` |
| `update_preserves_major_target_field` | let | `GC.Gen.MinorCollectForwarding.fst:50:0` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas</code> — 25/59 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_from_block_objects_facts` | let | `GC.Spec.Allocator.Lemmas.fst:33:0` |
| `alloc_from_block_preserves_wf` | let | `GC.Spec.Allocator.Lemmas.fst:30:0` |
| `alloc_spec_obj_not_in_chain` | let | `GC.Spec.Allocator.Lemmas.fst:64:0` |
| `alloc_spec_preserves_fl_chain_terminates` | let | `GC.Spec.Allocator.Lemmas.fst:59:0` |
| `alloc_spec_preserves_fl_valid` | let | `GC.Spec.Allocator.Lemmas.fst:51:0` |
| `alloc_spec_preserves_no_black` | let | `GC.Spec.Allocator.Lemmas.fst:62:0` |
| `alloc_spec_preserves_objects` | let | `GC.Spec.Allocator.Lemmas.fst:60:0` |
| `alloc_spec_preserves_wf` | let | `GC.Spec.Allocator.Lemmas.fst:34:0` |
| `alloc_spec_read_body` | let | `GC.Spec.Allocator.Lemmas.fst:74:0` |
| `alloc_spec_read_field_gt0` | let | `GC.Spec.Allocator.Lemmas.fst:78:0` |
| `chain_avoids_weaken` | let | `GC.Spec.Allocator.Lemmas.fst:56:0` |
| `first_hit` | let | `GC.Spec.Allocator.Lemmas.fsti:272:0` |
| `first_hit_spec` | let | `GC.Spec.Allocator.Lemmas.fst:57:0` |
| `fl_chain_kcycle_not_terminates` | let | `GC.Spec.Allocator.Lemmas.fst:50:0` |
| `fl_chain_predecessor_not_in_suffix_b` | let | `GC.Spec.Allocator.Lemmas.fst:58:0` |
| `fl_chain_terminates_unfold_steps` | let | `GC.Spec.Allocator.Lemmas.fst:49:0` |
| `fl_valid_weaken` | let | `GC.Spec.Allocator.Lemmas.fst:40:0` |
| `make_header_getTag` | let | `GC.Spec.Allocator.Lemmas.fst:29:0` |
| `not_in_fl_chain_b` | let | `GC.Spec.Allocator.Lemmas.fsti:283:0` |
| `walk_chain` | let | `GC.Spec.Allocator.Lemmas.fsti:170:0` |
| `walk_chain_append` | let | `GC.Spec.Allocator.Lemmas.fst:48:0` |
| `walk_chain_valid` | let | `GC.Spec.Allocator.Lemmas.fsti:173:0` |
| `walk_chain_valid_at` | let | `GC.Spec.Allocator.Lemmas.fst:46:0` |
| `walk_chain_valid_prefix` | let | `GC.Spec.Allocator.Lemmas.fst:45:0` |
| `walk_chain_valid_snoc` | let | `GC.Spec.Allocator.Lemmas.fst:47:0` |

</details>

<details>
<summary><code>GC.Spec.Graph</code> — 24/100 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `count` | let rec | `GC.Spec.Graph.fst:45:0` |
| `count_not_mem` | let rec | `GC.Spec.Graph.fst:51:0` |
| `forest_edge_property` | let rec | `GC.Spec.Graph.fst:837:0` |
| `forest_vertices` | let | `GC.Spec.Graph.fst:798:0` |
| `is_immediate_child` | let | `GC.Spec.Graph.fst:802:0` |
| `is_parent_of` | let rec | `GC.Spec.Graph.fst:809:0` |
| `is_parent_of_list` | let rec | `GC.Spec.Graph.fst:827:0` |
| `is_parent_of_list_imm` | let rec | `GC.Spec.Graph.fst:818:0` |
| `is_vertex_set_count` | let rec | `GC.Spec.Graph.fst:94:0` |
| `reach_subgraph` | let | `GC.Spec.Graph.fst:326:0` |
| `reach_subgraph_witness` | let rec | `GC.Spec.Graph.fst:305:0` |
| `reachable_from` | let | `GC.Spec.Graph.fst:363:0` |
| `reachable_from_set` | let | `GC.Spec.Graph.fst:369:0` |
| `reachfunc` | let | `GC.Spec.Graph.fst:233:0` |
| `remove_lemma_subset` | let | `GC.Spec.Graph.fst:744:0` |
| `roots_reachable` | let | `GC.Spec.Graph.fst:372:0` |
| `tree_edge_property` | let | `GC.Spec.Graph.fst:833:0` |
| `tree_successor_closed` | let | `GC.Spec.Graph.fst:853:0` |
| `tree_vertices` | let rec | `GC.Spec.Graph.fst:788:0` |
| `tree_vertices_list` | let rec | `GC.Spec.Graph.fst:793:0` |
| `union_vertex_sets` | let rec | `GC.Spec.Graph.fst:698:0` |
| `union_vertex_sets_mem_lemma` | let | `GC.Spec.Graph.fst:750:0` |
| `vertices_in_path` | let rec | `GC.Spec.Graph.fst:347:0` |
| `wf_graph` | let | `GC.Spec.Graph.fst:124:5` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas.Split</code> — 21/23 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_exact_preserves_wf` | let | `GC.Spec.Allocator.Lemmas.Split.fst:46:0` |
| `alloc_from_block_preserves_wf` | let | `GC.Spec.Allocator.Lemmas.Split.fst:1480:0` |
| `alloc_split_facts` | let | `GC.Spec.Allocator.Lemmas.Split.fst:813:0` |
| `alloc_split_g3_agrees` | let | `GC.Spec.Allocator.Lemmas.Split.fst:768:0` |
| `alloc_split_old_in_new` | let | `GC.Spec.Allocator.Lemmas.Split.fst:908:0` |
| `alloc_split_pre` | let | `GC.Spec.Allocator.Lemmas.Split.fsti:19:0` |
| `alloc_split_preserves_wf` | let | `GC.Spec.Allocator.Lemmas.Split.fst:1413:0` |
| `alloc_split_rem_in_objects` | let | `GC.Spec.Allocator.Lemmas.Split.fst:948:0` |
| `alloc_split_wf_part1` | let | `GC.Spec.Allocator.Lemmas.Split.fst:997:0` |
| `alloc_split_wf_part2_obj` | let | `GC.Spec.Allocator.Lemmas.Split.fst:1071:0` |
| `alloc_split_wf_part2_other` | let | `GC.Spec.Allocator.Lemmas.Split.fst:1257:0` |
| `alloc_split_wf_part2_rem` | let | `GC.Spec.Allocator.Lemmas.Split.fst:1231:0` |
| `alloc_split_wf_part2_rem_aux` | let rec | `GC.Spec.Allocator.Lemmas.Split.fst:1132:0` |
| `alloc_split_wf_part4` | let | `GC.Spec.Allocator.Lemmas.Split.fst:1341:0` |
| `field_addr_shift` | let | `GC.Spec.Allocator.Lemmas.Split.fst:36:8` |
| `ne_of_plus_pos` | let | `GC.Spec.Allocator.Lemmas.Split.fst:765:8` |
| `split_new_mem_in_old_or_rem` | let rec | `GC.Spec.Allocator.Lemmas.Split.fst:577:0` |
| `split_next_hd_objects_eq` | let | `GC.Spec.Allocator.Lemmas.Split.fst:197:0` |
| `split_next_hd_objects_eq_part1` | let | `GC.Spec.Allocator.Lemmas.Split.fst:252:0` |
| `split_old_mem_in_new` | let rec | `GC.Spec.Allocator.Lemmas.Split.fst:394:0` |
| `u64_ne_zero` | let | `GC.Spec.Allocator.Lemmas.Split.fst:28:8` |

</details>

<details>
<summary><code>GC.Spec.Fields</code> — 20/93 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `allocated_blocks` | let | `GC.Spec.Fields.fst:369:0` |
| `black_blocks` | let | `GC.Spec.Fields.fst:628:0` |
| `color_partition` | let | `GC.Spec.Fields.fst:1228:0` |
| `exists_field_checked_eq_unchecked` | let rec | `GC.Spec.Fields.fst:220:0` |
| `exists_field_pointing_to` | let rec | `GC.Spec.Fields.fst:196:0` |
| `field_address` | let | `GC.Spec.Fields.fst:55:0` |
| `gray_blocks` | let | `GC.Spec.Fields.fst:632:0` |
| `is_pointer_to_object` | let | `GC.Spec.Fields.fst:274:0` |
| `is_pointer_to_object_implies_exists_field` | let | `GC.Spec.Fields.fst:280:0` |
| `is_valid_header` | let | `GC.Spec.Fields.fst:1004:0` |
| `no_gray_equiv` | let | `GC.Spec.Fields.fst:652:0` |
| `no_scan_invariant_intro_singleton` | let | `GC.Spec.Fields.fst:784:0` |
| `no_scan_invariant_intro_vacuous` | let | `GC.Spec.Fields.fst:778:0` |
| `objects_addresses_ge_8` | let | `GC.Spec.Fields.fst:462:0` |
| `seq_filter_empty_implies_not_f` | let rec | `GC.Spec.Fields.fst:586:0` |
| `seq_filter_not_f_implies_empty` | let rec | `GC.Spec.Fields.fst:611:0` |
| `seq_filter_partition_3` | let rec | `GC.Spec.Fields.fst:1151:0` |
| `seq_filter_partition_4` | let rec | `GC.Spec.Fields.fst:1195:0` |
| `white_blocks` | let | `GC.Spec.Fields.fst:636:0` |
| `write_word_preserves_objects_from` | let | `GC.Spec.Fields.fst:1422:0` |

</details>

<details>
<summary><code>GC.Spec.Object</code> — 20/136 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `allocated_blocks` | let | `GC.Spec.Object.fst:679:0` |
| `colorHeader_preserves_tag` | let | `GC.Spec.Object.fst:246:0` |
| `color_mask` | let | `GC.Spec.Object.fst:37:0` |
| `color_shift` | let | `GC.Spec.Object.fst:38:0` |
| `exists_field_pointing_to` | let rec | `GC.Spec.Object.fst:539:0` |
| `field_address` | let | `GC.Spec.Object.fst:60:0` |
| `field_offset` | let | `GC.Spec.Object.fst:55:0` |
| `field_offset_bound` | let | `GC.Spec.Object.fst:47:8` |
| `getColor_setColor_packed` | let | `GC.Spec.Object.fst:159:0` |
| `hp_to_obj` | let | `GC.Spec.Object.fst:684:0` |
| `is_pointer_field` | let | `GC.Spec.Object.fst:529:0` |
| `is_pointer_to_object` | let | `GC.Spec.Object.fst:564:0` |
| `makeHeader_eq_colorHeader` | let | `GC.Spec.Object.fst:254:0` |
| `noGreyObjects_aux` | let rec | `GC.Spec.Object.fst:1086:0` |
| `objects_addr_not_in_rest` | let | `GC.Spec.Object.fst:742:0` |
| `objects_addresses_ge_8` | let | `GC.Spec.Object.fst:789:0` |
| `objects_addresses_gt_start` | let rec | `GC.Spec.Object.fst:689:0` |
| `white_black_disjoint` | let | `GC.Spec.Object.fst:425:0` |
| `white_gray_disjoint` | let | `GC.Spec.Object.fst:421:0` |
| `wosize_fits_field_index` | let | `GC.Spec.Object.fst:533:0` |

</details>

<details>
<summary><code>GC.Gen.Cheney.SimOne</code> — 15/34 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `cheney_forward_one_queue_bound` | let | `GC.Gen.Cheney.SimOne.fst:113:0` |
| `count_unforwarded_bound` | let rec | `GC.Gen.Cheney.SimOne.fst:266:8` |
| `forward_fields_bfs_inv_aux` | let rec | `GC.Gen.Cheney.SimOne.fst:557:8` |
| `forward_fields_preserves_bfs_inv` | let | `GC.Gen.Cheney.SimOne.fst:572:0` |
| `forward_fields_preserves_queue_valid` | let | `GC.Gen.Cheney.SimOne.fst:192:0` |
| `forward_fields_qv_aux` | let rec | `GC.Gen.Cheney.SimOne.fst:175:8` |
| `forward_roots_bfs_inv_aux` | let rec | `GC.Gen.Cheney.SimOne.fst:578:8` |
| `forward_roots_preserves_bfs_inv` | let | `GC.Gen.Cheney.SimOne.fst:593:0` |
| `forward_roots_preserves_queue_valid` | let | `GC.Gen.Cheney.SimOne.fst:215:0` |
| `forward_roots_qv_aux` | let rec | `GC.Gen.Cheney.SimOne.fst:198:8` |
| `fwd_one_preserves_queue_valid` | let | `GC.Gen.Cheney.SimOne.fst:58:0` |
| `scan_bfs_inv_aux` | let rec | `GC.Gen.Cheney.SimOne.fst:599:8` |
| `scan_preserves_bfs_inv` | let | `GC.Gen.Cheney.SimOne.fst:615:0` |
| `scan_preserves_queue_valid` | let | `GC.Gen.Cheney.SimOne.fst:239:0` |
| `scan_qv_aux` | let rec | `GC.Gen.Cheney.SimOne.fst:221:8` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.Header</code> — 15/22 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `chain_avoids_implies_not_in_fl_chain` | let | `GC.Gen.PromoteUpdate.Header.fst:31:8` |
| `copy_fields_preserves_chain_avoids_self` | let | `GC.Gen.PromoteUpdate.Header.fst:32:8` |
| `copy_fields_preserves_fl_chain_terminates` | let | `GC.Gen.PromoteUpdate.Header.fst:29:8` |
| `copy_fields_preserves_fl_valid_aux` | let | `GC.Gen.PromoteUpdate.Header.fst:28:8` |
| `copy_fields_preserves_objects_aux` | let | `GC.Gen.PromoteUpdate.Header.fst:27:8` |
| `copy_fields_preserves_wfh_part1` | let | `GC.Gen.PromoteUpdate.Header.fst:30:8` |
| `fwd_all_implies_positional` | let | `GC.Gen.PromoteUpdate.Header.fst:365:0` |
| `minor_collect_preserves_reachable` | let | `GC.Gen.PromoteUpdate.Header.fst:465:0` |
| `promote_all_adds_promoted` | let | `GC.Gen.PromoteUpdate.Header.fst:448:0` |
| `promote_all_aux_adds_promoted` | let rec | `GC.Gen.PromoteUpdate.Header.fst:372:0` |
| `promote_all_fwd_all_targets_valid` | let | `GC.Gen.PromoteUpdate.Header.fst:436:0` |
| `promote_object_adds_new_addr` | let | `GC.Gen.PromoteUpdate.Header.fst:327:8` |
| `set_promoted_tag_preserves_objects` | let | `GC.Gen.PromoteUpdate.Header.fst:307:8` |
| `set_promoted_tag_preserves_objects_aux` | let rec | `GC.Gen.PromoteUpdate.Header.fst:272:8` |
| `set_promoted_tag_preserves_objects_mem` | let | `GC.Gen.PromoteUpdate.Header.fst:315:8` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate</code> — 13/29 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `distinct_live_set` | let | `GC.Gen.PromoteUpdate.fsti:303:0` |
| `minor_collect_all_spec_unfold` | let | `GC.Gen.PromoteUpdate.fst:121:0` |
| `minor_collect_preserves_reachable` | let | `GC.Gen.PromoteUpdate.fst:91:0` |
| `promote_all_adds_promoted` | let | `GC.Gen.PromoteUpdate.fst:88:0` |
| `promote_all_fwd_all_targets_valid` | let | `GC.Gen.PromoteUpdate.fst:85:0` |
| `promote_all_preserves_blue_fields_closed` | let | `GC.Gen.PromoteUpdate.fst:118:0` |
| `promote_all_preserves_fields` | let | `GC.Gen.PromoteUpdate.fst:104:0` |
| `promote_all_read_other` | let | `GC.Gen.PromoteUpdate.fst:107:0` |
| `update_all_objects_aux_done` | let | `GC.Gen.PromoteUpdate.fst:45:0` |
| `update_all_objects_aux_skip_blue` | let | `GC.Gen.PromoteUpdate.fst:39:0` |
| `update_all_objects_aux_skip_no_scan` | let | `GC.Gen.PromoteUpdate.fst:42:0` |
| `update_all_objects_aux_step` | let | `GC.Gen.PromoteUpdate.fst:36:0` |
| `update_major_pointers_preserves_wfh_part2` | let | `GC.Gen.PromoteUpdate.fst:99:0` |

</details>

<details>
<summary><code>GC.Lib.Header</code> — 11/84 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `getColor64_setColor64` | let | `GC.Lib.Header.fst:591:0` |
| `get_color64` | let | `GC.Lib.Header.fst:564:0` |
| `pack_unpack_header` | let | `GC.Lib.Header.fst:499:0` |
| `pack_unpack_header64` | let | `GC.Lib.Header.fst:604:0` |
| `setColor64_preserves_tag` | let | `GC.Lib.Header.fst:600:0` |
| `setColor64_preserves_wosize` | let | `GC.Lib.Header.fst:596:0` |
| `set_color_sem_color` | let | `GC.Lib.Header.fst:150:0` |
| `set_color_sem_preserves_tag` | let | `GC.Lib.Header.fst:158:0` |
| `set_color_sem_preserves_wosize` | let | `GC.Lib.Header.fst:154:0` |
| `unpack_get_color` | let | `GC.Lib.Header.fst:375:0` |
| `unpack_header64` | let | `GC.Lib.Header.fst:577:0` |

</details>

<details>
<summary><code>GC.Lib.Address</code> — 10/15 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `aligned_separation` | let | `GC.Lib.Address.fst:111:0` |
| `field_addr_aligned` | let | `GC.Lib.Address.fst:117:0` |
| `field_addr_aligned_heap` | let | `GC.Lib.Address.fst:123:0` |
| `field_addr_value` | let | `GC.Lib.Address.fst:36:0` |
| `field_after_header` | let | `GC.Lib.Address.fst:42:0` |
| `field_disjoint_from_other` | let | `GC.Lib.Address.fst:84:0` |
| `field_header_separated` | let | `GC.Lib.Address.fst:54:0` |
| `field_neq_header` | let | `GC.Lib.Address.fst:48:0` |
| `field_other_header_separated` | let | `GC.Lib.Address.fst:72:0` |
| `field_separated_from_addr` | let | `GC.Lib.Address.fst:129:0` |

</details>

<details>
<summary><code>GC.Spec.Mark</code> — 10/144 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `mark_aux_preserves_black` | let rec | `GC.Spec.Mark.fst:916:0` |
| `mark_aux_preserves_objects_gt0` | let | `GC.Spec.Mark.fst:2163:0` |
| `mark_black_iff_reachable` | let | `GC.Spec.Mark.fst:1029:0` |
| `mark_preserves_no_blue` | let | `GC.Spec.Mark.fst:2467:0` |
| `mark_step_makes_one_black` | let | `GC.Spec.Mark.fst:938:0` |
| `mark_step_preserves_black` | let | `GC.Spec.Mark.fst:886:0` |
| `no_blue_objects` | let | `GC.Spec.Mark.fsti:259:0` |
| `non_black_count_makeBlack_other` | let rec | `GC.Spec.Mark.fst:959:0` |
| `non_black_count_unfold` | let | `GC.Spec.Mark.fst:978:0` |
| `stack_to_vertices` | let | `GC.Spec.Mark.fst:1022:0` |

</details>

<details>
<summary><code>GC.Impl.Sweep.Lemmas</code> — 9/43 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `density_next_bridge` | let | `GC.Impl.Sweep.Lemmas.fst:175:0` |
| `derive_objects_nonempty_bridge` | let | `GC.Impl.Sweep.Lemmas.fst:207:0` |
| `headers_preserved_before_spec_write` | let | `GC.Impl.Sweep.Lemmas.fst:357:0` |
| `is_black_bridge` | let | `GC.Impl.Sweep.Lemmas.fst:462:0` |
| `sweep_black_preserves` | let | `GC.Impl.Sweep.Lemmas.fst:432:0` |
| `sweep_black_whiteness` | let | `GC.Impl.Sweep.Lemmas.fst:621:0` |
| `sweep_else_contradiction` | let | `GC.Impl.Sweep.Lemmas.fst:677:0` |
| `sweep_loop_next_bridge` | let | `GC.Impl.Sweep.Lemmas.fst:228:0` |
| `sweep_object_black_eq` | let | `GC.Impl.Sweep.Lemmas.fst:647:0` |

</details>

<details>
<summary><code>GC.Gen.Cheney.Sim</code> — 8/20 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `cheney_forward_fields_queue_valid` | let | `GC.Gen.Cheney.Sim.fst:186:0` |
| `cheney_forward_one_queue_bound` | let | `GC.Gen.Cheney.Sim.fst:174:0` |
| `cheney_forward_one_queue_valid` | let | `GC.Gen.Cheney.Sim.fst:163:0` |
| `cheney_forward_roots_queue_bound` | let | `GC.Gen.Cheney.Sim.fst:225:0` |
| `cheney_forward_roots_queue_valid` | let | `GC.Gen.Cheney.Sim.fst:197:0` |
| `cheney_scan_queue_bound` | let | `GC.Gen.Cheney.Sim.fst:237:0` |
| `cheney_scan_queue_valid` | let | `GC.Gen.Cheney.Sim.fst:208:0` |
| `minor_object_passes_guards` | let | `GC.Gen.Cheney.Sim.fst:129:0` |

</details>

<details>
<summary><code>GC.Gen.CombinedGraph</code> — 8/107 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `classify_roots_impl` | let | `GC.Gen.CombinedGraph.fst:1209:0` |
| `cv_eqtype` | let | `GC.Gen.CombinedGraph.fst:24:0` |
| `gc_morphism` | let | `GC.Gen.CombinedGraph.fst:1114:0` |
| `gc_morphism_major` | let | `GC.Gen.CombinedGraph.fst:1129:0` |
| `gc_morphism_minor_fwd` | let | `GC.Gen.CombinedGraph.fst:1119:0` |
| `gc_morphism_minor_stay` | let | `GC.Gen.CombinedGraph.fst:1124:0` |
| `major_field_edges_elim` | let rec | `GC.Gen.CombinedGraph.fst:834:8` |
| `minor_field_edges_elim` | let rec | `GC.Gen.CombinedGraph.fst:814:8` |

</details>

<details>
<summary><code>GC.Gen.HeapInvariant</code> — 8/35 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `full_heap_shape` | let | `GC.Gen.HeapInvariant.fst:101:0` |
| `full_heap_shape_elim` | let | `GC.Gen.HeapInvariant.fst:294:0` |
| `full_heap_shape_intro` | let | `GC.Gen.HeapInvariant.fst:302:0` |
| `major_stack_shape` | let | `GC.Gen.HeapInvariant.fst:84:0` |
| `major_stack_shape_elim` | let | `GC.Gen.HeapInvariant.fst:254:0` |
| `major_stack_shape_intro` | let | `GC.Gen.HeapInvariant.fst:265:0` |
| `minor_major_fields_no_blue_empty` | let | `GC.Gen.HeapInvariant.fst:474:0` |
| `minor_major_fields_no_blue_intro` | let | `GC.Gen.HeapInvariant.fst:170:0` |

</details>

<details>
<summary><code>GC.Spec.Allocator</code> — 8/40 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_exact_heap` | let | `GC.Spec.Allocator.fsti:440:0` |
| `alloc_exact_length` | let | `GC.Spec.Allocator.fst:405:0` |
| `alloc_exact_pre` | let | `GC.Spec.Allocator.fsti:435:0` |
| `alloc_exact_read_hd` | let | `GC.Spec.Allocator.fst:377:0` |
| `alloc_exact_read_other` | let | `GC.Spec.Allocator.fst:391:0` |
| `alloc_split_normal_length` | let | `GC.Spec.Allocator.fst:231:0` |
| `alloc_split_normal_read_hd` | let | `GC.Spec.Allocator.fst:253:0` |
| `make_header_eq_impl` | let | `GC.Spec.Allocator.fst:43:0` |

</details>

<details>
<summary><code>GC.Spec.Coalesce</code> — 8/68 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `coalesce_aux_empty` | let | `GC.Spec.Coalesce.fst:127:0` |
| `coalesce_aux_fp_in_walk` | let rec | `GC.Spec.Coalesce.fst:2974:0` |
| `coalesce_aux_white_step_fst` | let | `GC.Spec.Coalesce.fst:134:0` |
| `coalesce_fp_valid` | let | `GC.Spec.Coalesce.fst:2922:0` |
| `flush_blue_fb_in_walk` | let | `GC.Spec.Coalesce.fst:2940:8` |
| `flush_blue_snd_cases` | let | `GC.Spec.Coalesce.fst:2933:8` |
| `flush_blue_wosize_spec` | let | `GC.Spec.Coalesce.fst:486:0` |
| `flush_preserves_later_white_headers` | let | `GC.Spec.Coalesce.fst:1051:8` |

</details>

<details>
<summary><code>GC.Gen.Base</code> — 7/25 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `is_major_addr` | let | `GC.Gen.Base.fsti:137:0` |
| `is_minor_addr_from_object_addr` | let | `GC.Gen.Base.fst:65:0` |
| `minor_base_ok` | let | `GC.Gen.Base.fst:43:0` |
| `minor_hp_addr` | let | `GC.Gen.Base.fsti:91:0` |
| `minor_major_disjoint` | let | `GC.Gen.Base.fst:86:0` |
| `minor_obj_addr` | let | `GC.Gen.Base.fsti:98:0` |
| `small_wosize_fits` | let | `GC.Gen.Base.fst:32:0` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas.Header</code> — 7/12 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `efptu_congruence` | let rec | `GC.Spec.Allocator.Lemmas.Header.fst:128:0` |
| `efptu_monotone` | let rec | `GC.Spec.Allocator.Lemmas.Header.fst:150:0` |
| `header_write_doesnt_change_other_fields` | let | `GC.Spec.Allocator.Lemmas.Header.fst:270:0` |
| `header_write_doesnt_change_own_fields` | let | `GC.Spec.Allocator.Lemmas.Header.fst:252:0` |
| `header_write_doesnt_change_own_fields_aux` | let | `GC.Spec.Allocator.Lemmas.Header.fst:226:8` |
| `mul_cong` | let | `GC.Spec.Allocator.Lemmas.Header.fst:221:8` |
| `mul_mod_add_mod_helper` | let | `GC.Spec.Allocator.Lemmas.Header.fst:202:8` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas.Part2</code> — 7/56 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_from_block_read_body` | let | `GC.Spec.Allocator.Lemmas.Part2.fst:2019:8` |
| `alloc_search_read_body` | let rec | `GC.Spec.Allocator.Lemmas.Part2.fst:2142:8` |
| `alloc_search_read_field_gt0` | let rec | `GC.Spec.Allocator.Lemmas.Part2.fst:3034:8` |
| `alloc_spec_read_body` | let | `GC.Spec.Allocator.Lemmas.Part2.fst:2237:0` |
| `alloc_spec_read_field_gt0` | let | `GC.Spec.Allocator.Lemmas.Part2.fst:3137:0` |
| `u64_lt_of_ge_ne` | let | `GC.Spec.Allocator.Lemmas.Part2.fst:49:8` |
| `u64_v_ne` | let | `GC.Spec.Allocator.Lemmas.Part2.fst:42:8` |

</details>

<details>
<summary><code>GC.Spec.FreeList</code> — 7/25 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `fl_exact_elim_complete` | let | `GC.Spec.FreeList.fst:183:0` |
| `fl_exact_elim_sound` | let | `GC.Spec.FreeList.fst:178:0` |
| `fl_node_is_obj_addr` | let | `GC.Spec.FreeList.fst:43:0` |
| `fl_sound_not_blue` | let | `GC.Spec.FreeList.fst:191:0` |
| `on_fl_monotone` | let rec | `GC.Spec.FreeList.fst:71:0` |
| `on_fl_write_outside` | let rec | `GC.Spec.FreeList.fst:203:0` |
| `reachable_write_outside` | let | `GC.Spec.FreeList.fst:227:0` |

</details>

<details>
<summary><code>GC.Spec.Sweep</code> — 7/56 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `free_list_props` | let | `GC.Spec.Sweep.fsti:43:0` |
| `free_list_valid` | let rec | `GC.Spec.Sweep.fsti:25:0` |
| `sweep_aux_step` | let | `GC.Spec.Sweep.fst:227:0` |
| `sweep_aux_white_stays` | let rec | `GC.Spec.Sweep.fst:406:0` |
| `sweep_final_colors` | let | `GC.Spec.Sweep.fst:650:0` |
| `sweep_no_gray_or_black` | let | `GC.Spec.Sweep.fst:665:0` |
| `sweep_object_preserves_objects_from` | let | `GC.Spec.Sweep.fst:164:0` |

</details>

<details>
<summary><code>GC.Gen.CheneyPreservation.Forwarding</code> — 6/58 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `add_mul_le_chain` | let | `GC.Gen.CheneyPreservation.Forwarding.fst:118:0` |
| `cfn_infix_ready_post` | let | `GC.Gen.CheneyPreservation.Forwarding.fst:774:0` |
| `cfn_infix_ready_pre` | let | `GC.Gen.CheneyPreservation.Forwarding.fst:762:0` |
| `eq_add_mul_bound` | let | `GC.Gen.CheneyPreservation.Forwarding.fst:123:0` |
| `le_plus_trans` | let | `GC.Gen.CheneyPreservation.Forwarding.fst:98:0` |
| `le_trans_nat_pf` | let | `GC.Gen.CheneyPreservation.Forwarding.fst:133:0` |

</details>

<details>
<summary><code>GC.Spec.MarkBoundedInv</code> — 6/15 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `bounded_mark_inv_from_full` | let | `GC.Spec.MarkBoundedInv.fst:36:0` |
| `bounded_mark_inv_rescan` | let | `GC.Spec.MarkBoundedInv.fst:136:0` |
| `bounded_mark_inv_rescan_complete` | let | `GC.Spec.MarkBoundedInv.fst:146:0` |
| `bounded_mark_inv_step` | let | `GC.Spec.MarkBoundedInv.fst:84:0` |
| `bounded_mark_inv_step_decreases` | let | `GC.Spec.MarkBoundedInv.fst:127:0` |
| `bounded_mark_inv_step_preserves_objects` | let | `GC.Spec.MarkBoundedInv.fst:117:0` |

</details>

<details>
<summary><code>GC.Gen.AllocProps</code> — 5/36 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_search_obj_in_objects_pre` | let rec | `GC.Gen.AllocProps.fst:102:0` |
| `alloc_search_obj_wosize` | let rec | `GC.Gen.AllocProps.fst:400:0` |
| `alloc_spec_obj_in_objects` | let | `GC.Gen.AllocProps.fst:144:0` |
| `alloc_spec_obj_wosize` | let | `GC.Gen.AllocProps.fst:474:0` |
| `write_prev_preserves_not_blue` | let | `GC.Gen.AllocProps.fst:964:0` |

</details>

<details>
<summary><code>GC.Spec.Allocator.Lemmas.Chain</code> — 5/48 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `alloc_search_fuel_irrelevant` | let rec | `GC.Spec.Allocator.Lemmas.Chain.fst:1286:0` |
| `alloc_spec_fuel_irrelevant` | let | `GC.Spec.Allocator.Lemmas.Chain.fst:1328:0` |
| `fl_chain_terminates_splice` | let rec | `GC.Spec.Allocator.Lemmas.Chain.fst:393:0` |
| `fl_valid_field_write` | let rec | `GC.Spec.Allocator.Lemmas.Chain.fst:475:0` |
| `fl_valid_field_write_tail` | let rec | `GC.Spec.Allocator.Lemmas.Chain.fst:556:0` |

</details>

<details>
<summary><code>GC.Spec.Base</code> — 5/20 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `heap_fp_pair` | let | `GC.Spec.Base.fsti:117:0` |
| `hp_addr_32` | let | `GC.Spec.Base.fsti:59:0` |
| `mult_mword_aligned` | let | `GC.Spec.Base.fst:63:0` |
| `stack_heap_pair` | let | `GC.Spec.Base.fsti:114:0` |
| `sum_of_aligned_is_aligned` | let | `GC.Spec.Base.fst:59:0` |

</details>

<details>
<summary><code>GC.Spec.MarkInv</code> — 5/18 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `mark_inv_intro` | let | `GC.Spec.MarkInv.fst:21:0` |
| `mark_inv_noGreyObjects` | let | `GC.Spec.MarkInv.fst:80:0` |
| `mark_inv_no_gray` | let | `GC.Spec.MarkInv.fst:76:0` |
| `mark_inv_step_preserves_objects` | let | `GC.Spec.MarkInv.fst:54:0` |
| `push_children_stack_monotone` | let | `GC.Spec.MarkInv.fst:73:0` |

</details>

<details>
<summary><code>GC.Gen.MinorHeap</code> — 4/85 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `minor_chain_valid_unfold` | let | `GC.Gen.MinorHeap.fst:279:0` |
| `minor_heap_size_bound` | let | `GC.Gen.MinorHeap.fsti:177:0` |
| `minor_objects_zero_bump` | let | `GC.Gen.MinorHeap.fst:1236:0` |
| `minor_pow2_bound` | let | `GC.Gen.MinorHeap.fst:274:0` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.Aux</code> — 4/9 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `update_all_objects_aux_done` | let | `GC.Gen.PromoteUpdate.Aux.fst:187:0` |
| `update_all_objects_aux_skip_blue` | let | `GC.Gen.PromoteUpdate.Aux.fst:168:0` |
| `update_all_objects_aux_skip_no_scan` | let | `GC.Gen.PromoteUpdate.Aux.fst:177:0` |
| `update_all_objects_aux_step` | let | `GC.Gen.PromoteUpdate.Aux.fst:155:0` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.BlueProm</code> — 4/23 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `bfc_one_field` | let | `GC.Gen.PromoteUpdate.BlueProm.fst:243:8` |
| `minor_collect_all_spec_unfold` | let | `GC.Gen.PromoteUpdate.BlueProm.fst:856:0` |
| `promote_all_aux_preserves_bfc` | let rec | `GC.Gen.PromoteUpdate.BlueProm.fst:795:8` |
| `promote_all_preserves_blue_fields_closed` | let | `GC.Gen.PromoteUpdate.BlueProm.fst:841:0` |

</details>

<details>
<summary><code>GC.Spec.DFS</code> — 4/32 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `dfs_body_length` | let | `GC.Spec.DFS.fst:279:0` |
| `dfs_body_visited_grows` | let | `GC.Spec.DFS.fst:292:0` |
| `is_reachable_via_forest` | let | `GC.Spec.DFS.fst:1036:0` |
| `successor_reachable` | let | `GC.Spec.DFS.fst:593:0` |

</details>

<details>
<summary><code>GC.Spec.MarkBounded</code> — 3/48 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `bounded_from_full` | let | `GC.Spec.MarkBounded.fst:35:0` |
| `mark_bounded_count_decreases` | let rec | `GC.Spec.MarkBounded.fst:906:0` |
| `mark_inner_loop_drains` | let rec | `GC.Spec.MarkBounded.fst:831:0` |

</details>

<details>
<summary><code>GC.Spec.SweepCoalesce.Defs</code> — 3/5 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `fused_aux_black_step` | let | `GC.Spec.SweepCoalesce.Defs.fst:62:0` |
| `fused_aux_empty` | let | `GC.Spec.SweepCoalesce.Defs.fst:57:0` |
| `fused_aux_nonblack_step` | let | `GC.Spec.SweepCoalesce.Defs.fst:74:0` |

</details>

<details>
<summary><code>GC.Spec.SweepCoalesce.FlushAgree</code> — 3/11 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `aligned_neq_disjoint` | let | `GC.Spec.SweepCoalesce.FlushAgree.fst:103:8` |
| `write_word_agree_at` | let | `GC.Spec.SweepCoalesce.FlushAgree.fst:114:8` |
| `zero_fields_agree_pair` | let rec | `GC.Spec.SweepCoalesce.FlushAgree.fst:139:8` |

</details>

<details>
<summary><code>GC.Spec.SweepInv</code> — 3/44 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `fp_valid_intro` | let | `GC.Spec.SweepInv.fst:33:0` |
| `headers_preserved_before_weaken` | let | `GC.Spec.SweepInv.fst:321:0` |
| `objects_white_before_all` | let | `GC.Spec.SweepInv.fst:397:0` |

</details>

<details>
<summary><code>GC.Gen.MinorCollectForwarding.Helpers</code> — 2/29 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `remembered_slot_targets_from_zero` | let | `GC.Gen.MinorCollectForwarding.Helpers.fst:51:0` |
| `roots_with_remembered` | let | `GC.Gen.MinorCollectForwarding.Helpers.fsti:64:0` |

</details>

<details>
<summary><code>GC.Gen.TwoPassEquiv</code> — 2/42 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `heap_read_word_extensional` | let | `GC.Gen.TwoPassEquiv.fst:45:0` |
| `update_major_pointers_rewrites_fwd_field` | let | `GC.Gen.TwoPassEquiv.fst:1618:0` |

</details>

<details>
<summary><code>GC.Impl.FusedSweepCoalesce.Lemmas</code> — 2/14 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `flush_blue_length` | let | `GC.Impl.FusedSweepCoalesce.Lemmas.fst:325:0` |
| `run_words_fits` | let | `GC.Impl.FusedSweepCoalesce.Lemmas.fst:108:8` |

</details>

<details>
<summary><code>GC.Gen.Cheney</code> — 1/92 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `cheney_collect_preserves_wfh` | let | `GC.Gen.Cheney.fst:982:0` |

</details>

<details>
<summary><code>GC.Gen.CheneyBFS</code> — 1/36 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `forward_roots_fwd_monotone` | let rec | `GC.Gen.CheneyBFS.fst:128:0` |

</details>

<details>
<summary><code>GC.Gen.CheneyPreservation</code> — 1/65 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `fwd_noninfix_target_exists` | let | `GC.Gen.CheneyPreservation.fst:1430:8` |

</details>

<details>
<summary><code>GC.Gen.CheneyPreservation.Fields</code> — 1/44 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `infix_fwd_ready_pre_intro` | let | `GC.Gen.CheneyPreservation.Fields.fst:81:8` |

</details>

<details>
<summary><code>GC.Gen.CheneyPreservation.Injectivity</code> — 1/44 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `cheney_scan_preserves_wfh_part4_local` | let rec | `GC.Gen.CheneyPreservation.Injectivity.fst:272:8` |

</details>

<details>
<summary><code>GC.Gen.MinorCollectForwarding.NormalEdges</code> — 1/14 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `combined_reachable_normal_edges_forwarded_prop` | let | `GC.Gen.MinorCollectForwarding.NormalEdges.fsti:102:0` |

</details>

<details>
<summary><code>GC.Gen.PromoteUpdate.Field</code> — 1/9 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `update_major_pointers_preserves_wfh_part2` | let | `GC.Gen.PromoteUpdate.Field.fst:385:0` |

</details>

<details>
<summary><code>GC.Impl.Coalesce.Lemmas</code> — 1/19 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `run_words_fits` | let | `GC.Impl.Coalesce.Lemmas.fst:71:0` |

</details>

<details>
<summary><code>GC.Spec.HeapGraph</code> — 1/32 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `object_fits_in_heap_intro` | let | `GC.Spec.HeapGraph.fst:101:0` |

</details>

<details>
<summary><code>GC.Spec.HeapModel</code> — 1/5 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `field_reads_equal` | let | `GC.Spec.HeapModel.fst:90:0` |

</details>

<details>
<summary><code>GC.Spec.SweepCoalesce.Helpers</code> — 1/16 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `makeWhite_white_noop` | let | `GC.Spec.SweepCoalesce.Helpers.fst:285:0` |

</details>

<details>
<summary><code>GC.Spec.SweepCoalesce.Induction</code> — 1/22 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `flush_pair_above` | let | `GC.Spec.SweepCoalesce.Induction.fst:221:8` |

</details>

