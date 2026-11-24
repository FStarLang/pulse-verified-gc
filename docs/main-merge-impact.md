# Impact of the incremental-GC merge on our branches

Assessment only (2026-11-16). No branch was rebased and no code was changed.

- **New main:** `origin/main` = `5623c7f6` (PR #52, `akhil/incremental-mark`, which
  also merges `akhil/incremental-sweep`, `akhil/minor-refactor` and
  `akhil/sweep-refactor`).
- **Old base:** `1ecb0004`, the base of all five of our branches. Main is
  146 commits ahead of it, across 381 files (+48k/−39k lines).

Method:
- I diffed each branch's own changes against main's.
- I scanned each branch for references to modules or names that main deleted.
- I applied each branch's diff to a scratch checkout of main with
  `git apply --3way` (the local git 2.24 has no `merge-tree --write-tree`),
  then reset that checkout.
- I lax-checked the size-lists core modules against main and ran a full SMT
  check of `FreeLists`. Both used a scratch cache.

---

## 1. What main now contains that we depend on

### Sweep: still fused with coalescing, now one in-place, cursor-driven pass
- **Definition:** `GC.Spec.FusedSweep.fused_sweep_coalesce g fp = sweep_from g fp sweep_start`.
  - It takes the existing free-list head `fp` and edits the list in place.
  - The list is kept across collections and stays in address order.
  - The state is `{cursor; swept_tail; last_fragment}`.
  - A step handles four cases: black, merge into the previous block, blue, white (`FusedSweep.Step`).
- **Deleted:** `GC.Spec.Sweep`, `GC.Spec.Coalesce.*`, `GC.Spec.SweepCoalesce.*`,
  `GC.Spec.FreeList.Sweep`, `GC.Spec.FreeList.Descending`, `GC.Spec.HeapAgree`,
  `GC.Impl.Coalesce*` and `GC.Impl.FusedSweepCoalesce.Lemmas`.
  - The old two-pass `coalesce (sweep …)` and its bridge are gone.
  - `HeapAgree` was not replaced. The implementation now equals
    `fused_sweep_coalesce` exactly, so agreement up to free contents is no longer needed.
- **Statements:**
  - `SweepPhase.Intrinsic.End.fused_sweep_post` (opaque `sweep_post`): the
    result is dense, black objects survive as white, every non-black block is
    blue, no two blue blocks are adjacent, dead blocks are covered by blue
    ones, and the list satisfies `fl_ascending`.
  - `FusedSweep.Lossless.fused_sweep_lossless` is the old
    `coalesce_correct`, restated against `g0`.
- **Impl:** `GC.Impl.FusedSweepCoalesce` has the precondition
  `sweep_pre 's fp /\ marked 's` and returns `== FS.fused_sweep_coalesce 's fp`.
  It also adds an incremental `sweep_slice_impl`.

### Heap walk: `WalkEnd` is gone, replaced by `Walk`
- `GC.Spec.Walk` is phrased in walk positions: `bsize`, `bnext`, `can_step`,
  `reaches g a b`, and frame lemmas (`walk_frame_from`, `walk_write`, `walk_congr`, `walk_merge`).
- `walk_end` keeps its name and role.
- The other old names have no one-to-one rename:

  | Old (`WalkEnd`) | New (`Walk`) |
  |---|---|
  | `walk_end_step`, `walk_head`, `walk_end_empty` | `reaches_unfold`/`reaches_step`, `objects_mem_iff`, the `can_step` guard |
  | `dense_from_walk_end` | `dense_of_reaches_end` |
  | `walk_end_of_dense` | `reaches_end_of_dense` |

- Extents (`in_extent`, `blue_covered`, `adjacent`) are in `FusedSweep.Lossless`.

### Allocator and free list: one address-ordered list, no size segregation
- **List:** `GC.Spec.FreeList.Ascending.fl_ascending g fp` holds: the list is exact
  and ascending, and allocation is first-fit with right-justified splits.
  - Nothing in `common/` or `mark-and-sweep/` is size-classed.
- **Allocation by phase:** `GC.Spec.Allocator.Cursor.alloc_phase g fp ph wz tag`.
  - It is the first-fit allocator with only the header colour depending on the phase.
  - At `Idle` it equals `alloc_spec` (`alloc_phase_idle`).
- **Sweep caches:** `GC.Spec.Allocator.Caches` treats the sweep's `swept_tail` and
  `last_fragment` as caches derived from the heap and cursor. Allocation keeps
  them derived; when it takes the cell `swept_tail` points at, `swept_tail`
  moves back to the predecessor, as `caml_fl_merge` does.
- **Impl:** `GC.Impl.Allocator.allocate heap fp_ref phase wosize tag` returns
  `== AC.alloc_phase 's 'fp 'ph wosize tag`.
  - It requires `fl_ascending` only while sweeping.
  - It no longer requires `well_formed_heap`.
  - `phase_state` is a 4-word record: kind, cursor, swept_tail, last_fragment.

### Well-formedness was restructured (affects every proof that touches `well_formed_heap`)
- **Parameterised by a free definition:** `well_formed_heap_with (free: free_def)`.
  - `free_def = heap -> obj_addr -> GTot bool`.
  - `well_formed_heap` is the instance at `free_stw` (free means blue).
  - The sweep phase uses `free_incremental c` (blue, or white in front of the cursor).
- **`no_pointer_to_blue` is retired** (`da17c9fb`). It is now part of
  `well_formed_heap` (`pointers_lead_to_non_free`). Deleted with it:
  - `Mark.no_pointer_to_blue` and its intro;
  - `Correctness.mark_post_elim_no_pointer_to_blue`;
  - `fields_constrained`, `well_formed_heap_part1..4`, `wfh_part*`,
    `wf_field_target_*` and `wf_resolve_identity`.

### Minor collection
- **When it runs:** at any phase. `minor_collect_with ph free` promotes through
  `alloc_at ph`, so promoted copies get the phase's allocation colour:
  - Idle: white.
  - Marking: black, and the marking invariant is kept at the same scan position.
  - Sweeping c: black in front of the cursor, white behind it.
- **`GC.Gen.CheneyGeneric`** proves the collection keeps the heap's shape for any
  admissible `free_def`. The stop-the-world theorem is its instance at `free_stw`.
- **Other new modules:**
  - `GC.Gen.RefTable` replaces `GC.Gen.Remembered`: a slot array that the barrier fills.
  - `GC.Gen.ForwardingArray`.
  - `GC.Gen.FreeListAscending` and `GC.Gen.SweptTail`: promotion keeps the list ascending and the caches derived.

### `gc_correct`
- **Statement unchanged:** `GC.Impl.Correct.gc_correct` still requires
  `gc_precondition_with_roots /\ collect_post` and ensures `gc_safe /\ gc_live`.
- **Changed underneath:**
  - `gc_coalesce_source` and `source_at` add `fl_ascending h_init fp`, and use
    equality with `fused_sweep_coalesce` instead of `heaps_agree_mod_free`.
  - `coalescing_lossless` is stated with `LS.sweep_lossless`.
  - `heap_partitioned` uses `W.walk_end`.
- Our `gc_correct_pages` was written to compare with this statement, and the comparison still holds.

### How marks are represented
- **Header colours only:** the 2-bit field, with White 0, Gray 1, Blue 2, Black 3.
  There is no bitmap anywhere in main.
- **The mark state is the heap's colours** (`GC.Gen.MarkState`). The mark stack,
  the overflow flag, the scan position `{cur; fld}` and the rescan cursor are
  implementation caches related to it by `mark_cache_ok`.
- Nothing is abstracted over the mark store.

### Phases and allocation colour in the incremental collector
- **Phases:** `GC.Spec.Phase.gc_phase = Idle | Marking | Sweeping of cursor`.
- **Allocation colour** (`allocation_color`, OCaml 4.14's rule):
  - Idle: White.
  - Marking: Black.
  - `Sweeping c`: Black if the header address is at or above `c`, White below it.
- **Barrier:** a deletion barrier with snapshot-at-the-beginning proofs.
  - `caml_modify` darkens the old value while marking (`GC.Gen.Barrier`, `GC.Gen.Impl.Barrier.modify_field`).
  - `MarkPhase.Alloc` exempts the fields of fresh black objects until they are initialised.
  - The program's own obligation, `modify_ok`, is trusted.
- **Runs:** `GC.Gen.MarkPhase.Cycle`, `GC.Gen.SweepPhase.Cycle` and
  `GC.Gen.Cycle` compose the whole incremental cycle, and it is lossless.
- **Extraction:** the collector is extracted
  (`start_cycle`, `mark_slice_at`, `major_slice`, `modify_field`) and used by
  the runtime under `VERGC_MAJOR=incremental`. Stop-the-world is still the default.

---

## 2. Our branches, in stacking order

| Branch | Stacks on | Own commits | Textual conflicts | Semantic breakage | Verdict |
|---|---|---|---|---|---|
| `unsupported-weak-finalise-roots` (#45) | `1ecb0004` | 1 | 3 files | C only | **Rebase**, small |
| `size-lists` (#46) | `1ecb0004` | 1 | ~15 files, plus generated snapshot C | Built on deleted modules | **Redo**; the core spec carries over |
| `object-table` (#48, on hold) | `size-lists` | 3 | ~15 files | Sweep half built on deleted modules | **Redo the sweep half** on main |
| `pages-allocator` | `size-lists` | 25 | `Makefile`, `MarkInv` (3-way resolves both) | ~20 of 95 Pages files | **Rebase**, medium |
| `pages-parallel` | `pages-allocator` at `3bc6b042` | 13 | `Makefile`, docs | 3 files | **Rebase** after `pages-allocator`, small |

### #45 `sheera/unsupported-weak-finalise-roots`: rebase, small
- **Conflicts** are in `README.md`, `tests/Makefile` and `verified_gc/alloc_gen.c`.
  `runtime_gen.patch`, `expected-failures.txt` and `known-issues.md` apply cleanly.
- **README and tests/Makefile:** main added `obj_truncate`, `explicit_major`,
  `incremental_sweep`, `write_barrier`, `incremental_mark` and `mark_scanned_writes` in
  the same places. Keep both sets.
- **`alloc_gen.c`:**
  - **Gray-stack hunk:** our hunk sized the gray stack from `root_count` because of
    `gen_gc_stack_budget`. Main replaced that code: `start_cycle` darkens roots
    onto a persistent mark stack and raises the overflow flag when they do not
    fit. Drop our gray-stack hunk.
  - **Root buffer:** main still has fixed `root_values[MAX_ROOTS]` and
    `root_locs[MAX_ROOTS]` arrays. Re-port the growth (issue #41) onto them.
    The `memcpy` into `roots_for_gc` and the `start_cycle(…, root_count)` call already take a dynamic count.
- **New check:** run `deep_stack` and `unsupported_features` also under
  `VERGC_MAJOR=incremental`, so roots are taken mid-cycle.
- **Effort:** about half a day.

### #46 `sheera/size-lists`: cannot be rebased; redo on main's code
**Why it cannot be rebased:**
- Its proof is a layer over modules main deleted: `SweepCoalesce.Lists`,
  `SweepCoalesce.ListsRel`, `CollectLists`, `HeapAgree.Lists` and
  `Allocator.Lists`, built on `Coalesce*`, `SweepCoalesce*`, `Sweep`,
  `HeapAgree`, `FreeList.Descending` and `WalkEnd`.
- Its impl edits (`FusedSweepCoalesce*`, `Allocator`, `Impl.Correct`,
  `Gen.Impl*`) are against code main rewrote.
- Its design assumes a list rebuilt from scratch by each sweep. Main keeps one
  ascending list, edited in place by an incremental sweep, with cursor-derived
  `swept_tail`/`last_fragment` caches and a phase-dependent colour.

**What a redo on main means:**
- Per-class ascending lists.
- Per-class `swept_tail` caches in `Allocator.Caches` and in the sweep state.
- Restating `SweepPhase.Intrinsic`'s invariant and `fused_sweep_post` for n lists.
- The minor-collection lemmas (`FreeListAscending`, `SweptTail`) for n lists.
- In effect a new PR. The page allocator replaces size lists for small objects
  anyway, so I would close #46 as superseded unless the stop-the-world
  performance case for it still matters on its own.

**What carries over:** the spec core,
`GC.Spec.SizeClass`, `GC.Spec.FreeLists` and `GC.Spec.FreeLists.Push`.
- `SizeClass` and `FreeLists` lax-check against main unchanged.
- `FreeLists.Push` has one broken name, `well_formed_heap_part1` / `wfh_part1_obj_bound`; main's
  equivalent is in `blocks_fit` / `wf_parts`.
- `FreeLists` also verifies on main with full SMT (note at the end).

**Can the large-object area still reuse it? Yes.**
- The page proofs use only the spec core: `FLs.fl_state`, `fls_head`, `fls_set`,
  `fls_empty`, `fls_valid`/`fls_sound`/`fls_terminates`, `chain_class`,
  `SC.n_lists`/`size_class`, `Push.terminates_with_room`, and singular
  `GC.Spec.FreeList`, which main still has with the same names.
- None of #46's sweep or collect modules are used. Stage 3 already settled
  that the run sweep does not use `Coalesce*`, `SweepCoalesce*` or `HeapAgree`
  (plan §7, §11).
- **Proposal:** move these three modules into the `pages-allocator` branch as
  its first commit, with the `Push` fix. The branch then no longer stacks on #46.

### #48 `sheera/object-table` (on hold): redo the sweep half when resumed
- **Part A's spec half** (`GC.Spec.ObjectTable*`) depends on the deleted
  `Coalesce`, `Coalesce.Dense`, `HeapAgree`, `Sweep` and `WalkEnd` for
  "exact after the sweep".
- **On main, that proof should get shorter.**
  `sweep_post` gives density, blue coverage and no adjacent blue blocks
  directly against `fused_sweep_coalesce`.
- **But "after the sweep" now means at the `Sweeping → Idle` transition** of an
  incremental sweep. The table has to stay weakly sound through
  `sweep_slice_impl`, minor collections that run mid-sweep, and allocation in
  front of the cursor.
- **The impl half** (`FusedSweepCoalesce`, `Allocator`, `Gen.Impl.Cheney`/`Promote`)
  must be redone against main's new `allocate` (phase, tag) and the sliced sweep.
- **Decision (b)** (weak always, exact after the sweep; intern.c re-tiles) is
  unaffected.
- **Re-stack** on main directly, not on #46.
- **Effort:** comparable to the original part A impl work. Keep it on hold until the pages rebase lands.

### `sheera/pages-allocator`: rebase, medium
**Textual:**
- `git apply --3way` of the whole branch onto main succeeded.
- `Makefile` (`ROOT_MODULES`; main also dropped `GC.Spec.FreeList.Sweep` from
  that list) and `MarkInv` (our `mark_inv_intro`) merged automatically.
- Nearly all of the branch is new `GC.Spec.Pages*`, `GC.Impl.Pages*` and `pages-c/` files.

**Semantic (found by scanning names; nothing built yet):**
1. **`WalkEnd` → `Walk`** in `Pages.{Darken, Inv, Partition, Shape, Vacuity, Walk}`.
   - Uses: `walk_end` (same name), `walk_end_step` ×4, `walk_head` ×2, `walk_end_empty` ×1.
   - These become `reaches_*` / `objects_mem_iff`.
   - Plan §12 already flagged `Pages.Walk`, `Shape` and `Inv`.
2. **`GC.Spec.Coalesce.Correct`** in `Pages.Survive`. Use `FusedSweep.Lossless`'s
   `survives`/extent vocabulary, or a local copy of the definition used.
3. **`no_pointer_to_blue` retired.** It is used ~35 times across `Pages.{Fill,
   Large, Replace, Step, SweepAll, Init, Inv, GcCorrect, ParMark.*}`. It is L10 of `pages_ok`.
   - Our proofs already prove it, so the work is re-plumbing, not new proof.
   - L10 is dropped from `pages_ok` as a separate conjunct, and each
     "`well_formed_heap g'` and `no_pointer_to_blue g'`" pair becomes a
     `well_formed_heap g'` proof through main's `wf_parts` /
     `pointers_lead_to_non_free free_stw`.
   - `GcCorrect` loses its use of `Corr.mark_post_elim_no_pointer_to_blue`.
4. **Old well-formedness parts:** `fields_constrained` ×14,
   `well_formed_heap_part1..4`, `wfh_part4`, `wf_field_target_*`,
   `wf_after`, `wf_resolve_identity`. About 19 of 95 Pages files touch 1–4 of these.
   - Under the vacuity and no-weakening rules, `Pages.Theorems`, `pages_ok`
     (apart from L10 being absorbed) and `gc_correct_pages` must keep their meaning.
   - Each vacuity witness must be re-run.
5. **The three #46 modules** are carried in, as above.
6. **`pages-c`:** regenerate the extracted C and rerun `bench`. Main changed
   `GC.Impl.Heap`/`Object`, and the speed rule (≤5% of the prototype) must be re-shown.

**Effort:** 2–4 days, mostly items 3 and 4.

**Not a rebase issue, but it changes stage-4 item 1 and 5b.** Item 1 was "instantiate
`AllocIface.allocator` with #46's allocator". It becomes: instantiate it with
main's `alloc_phase`. See §3 for the colour rule this needs.

### `sheera/pages-parallel`: rebase after `pages-allocator`, small
- **Base:** it forked from `pages-allocator` at `3bc6b042`, so it lacks that branch's last three
  commits (`75e5df92` roots greyed before the mark, `54bc3abe` vacuity
  witnesses, `10e4e630` docs).
- **Rebasing** onto the rebased `pages-allocator` brings them in. Expect
  conflicts in `Makefile`, `docs/` and possibly the vacuity modules.
- **Semantic:**
  - `WalkEnd` in `Pages.ParMark.Marked` (1 file).
  - `no_pointer_to_blue` in `ParMark.Heap` and `ParMark.Marked`.
  - `with_marks` and the chunked sweep do not touch anything main changed.
- **Effort:** about 1 day after `pages-allocator`.

---

## 3. How the page allocator plugs into main's incremental collector

**Main has no allocator interface to instantiate.**
- The allocator is hard-wired. The run types name the first-fit allocator directly:
  - `GC.Gen.MarkPhase.Cycle`: `AC.alloc_phase g fp Ph.Marking …`.
  - `GC.Gen.SweepPhase.Cycle`: `… (Sweeping c) …`.
  - `GC.Gen.Cycle` composes the two.
- Promotion calls `AP.alloc_at ph`.
- `gen_heap_t` holds `fp` and `phase_ref : R.ref Alloc.phase_state`.
- The sweep is also specific to the single address-ordered list. Its
  invariant is "white in front of the cursor is pending free", over one cursor.

**There are two real hooks, and both are already generic:**
- **`free_def`:** `well_formed_heap_with free`, and `GC.Gen.CheneyGeneric` is generic
  over it. The page sweep's mid-sweep notion, "white in an unswept page", is
  exactly a `free_def`. Plan §7.1's per-page invariant is main's
  `free_incremental c` with "in front of the cursor" replaced by "in an unswept page".
- **The marking side:** `marking_inv`, the deletion barrier, `MarkPhase.Alloc`
  and `scan_pos` depend on neither the allocator nor the list.

**So "plugging in" is work on main's side, and it is stage 5b:**
1. **Generalise the run types** (`MarkPhase.Cycle`, `SweepPhase.Cycle`, `Gen.Cycle`,
   `Promote`) from `AC.alloc_phase` to our `GC.Spec.AllocIface.allocator`
   record, plus a small **sweeper** record (start, step, done, `free_def`).
   Main's first-fit allocator with `FusedSweep` becomes instance 1, and pages becomes
   instance 2. Instance 1 is the retargeted item 1. Proving main's own cycle
   theorem through the interface is the evidence the interface is not vacuous.
2. **Generalise `AllocIface`'s colour rule.** Ours is `Sweeping → White` with no
   cursor. Main's is `Sweeping c → Black iff hd ≥ c`. The common rule is
   "black if the address is unswept, else white", using the record's own
   `unswept` field:
   - for main, `unswept a ⟺ a ≥ c`;
   - for pages, the allocator never allocates into unswept memory, so the rule always gives white, which is what we prove today.

   `AllocIface.phase` gains no cursor; the cursor stays inside main's instance's state.
3. **`Impl`:** `gen_heap_t`'s `fp`/`phase_ref` become the allocator's state.
   This is the threading of the page state through `gen_gc` that 5b already planned.

**Mark representation:** main marks in headers.
- **Sequential page collector:** it also marks in headers today. Its mark and the incremental mark meet without change.
- **Bitmap:** a bitmap could be used, but not by instantiation. Main's mark-phase
  predicates read header colours. The route is the one in the
  parallel design (§ "With the incremental collector"):
  - restate `marking_inv` over `with_marks h bm`;
  - the barrier sets bits;
  - a fresh object's colour becomes "white plus a bit".
- **Recommendation:** keep header colours for the incremental collector and use the
  bitmap only in the stop-the-world parallel mark (M2). Revisit if two sweeps (bitmap and header) cost too much. The merge does not force this decision, but 5b should record it.

---

## 4. Rebase plan

**General rules:**
- "Full verify" means a clean build in a scratch worktree with
  `FSTAR_HOME=~/Documents/pulse-verified-gc-new/fstar`, `RETRY=" "` (no
  `--retry`), no `--admit_except`, and no `CACHE_DIR` override. Use `gmake`.
- Each step also reruns that branch's own checks (C tests, vacuity witnesses, bench).
- Before starting, keep the old tips under backup refs, e.g. `git branch
  backup/<name> <name>`. Every step is a force-push, so it is yours to do.

**Steps:**
0. **Baseline.** Verify `origin/main` from clean, and run the OCaml
   integration tests (stop-the-world and `VERGC_MAJOR=incremental`) against
   `ci/expected-failures.txt` and `ci/expected-failures-incremental.txt`.
   Then any later failure is ours.
1. **#45:** `git rebase origin/main` (1 commit).
   - Resolve README and tests/Makefile by keeping both sets.
   - In `alloc_gen.c`, drop the gray-cap hunk and re-port root-buffer growth onto `root_values`/`root_locs`.
   - Verify: full build, the C tests in both modes, the testsuite with both
     expected-failure lists, and `deep_stack`/`unsupported_features` under `incremental` too.
   - Independent of the pages branches; it can land first.
2. **#46:** do not rebase.
   - Close it as superseded, or mark it "to redo on main", whichever you prefer.
   - Its spec core moves into step 3.
3. **`pages-allocator`:** `git rebase --onto origin/main sheera/size-lists sheera/pages-allocator`,
   with a new first commit holding `SizeClass`, `FreeLists`, `FreeLists.Push` (with the `Push` fix)
   and their `Makefile` entries.
   - Expected textual conflicts: `Makefile`, and possibly `MarkInv` on the stage-4 commit.
   - **Commit granularity:** fixing the semantic breakage in each of the 25
     commits is costly, because stage-1 commits already use `WalkEnd` and
     `no_pointer_to_blue`. Choose one of:
     - **(a)** Rebase textually, then add one "port to main" commit:
       `WalkEnd → Walk`, `Coalesce.Correct`, L10 absorbed into
       `well_formed_heap`, new well-formedness names. Intermediate commits will not build.
     - **(b)** Squash the branch into its stages (1, 2, 3, 4, 5a, efficiency
       pass) and port each. Every commit builds, at the cost of history.

     I recommend (a) unless you want every commit to build.
   - Verify: full build; `Pages.Theorems` statements byte-identical to before;
     `gc_correct_pages` unchanged in meaning; vacuity witnesses re-run;
     regenerate `pages-c`, its directed test, and `bench` within 5%.
4. **`pages-parallel`:** `git rebase --onto <new pages-allocator> 3bc6b042 sheera/pages-parallel`.
   - Expected conflicts: `Makefile`, `docs/`, vacuity modules.
   - Port `ParMark.Marked`/`ParMark.Heap` (`WalkEnd`, `no_pointer_to_blue`).
   - Verify: full build, the parallel differential test, `pbench`, and the vacuity audit (§11.8).
5. **#48 `object-table`:** stays on hold. When resumed, re-stack it on main (or on
   the rebased pages, if the table should cover pages) and redo the sweep half against `FusedSweep`/`sweep_slice_impl`.
6. **After the rebase, not part of it:**
   - Stage-4 item 1, retargeted: the `AllocIface` colour rule and main's allocator as instance 1.
   - Then 5b: the run types over the interface and the page state in `gen_gc`.

---

*Note on the size-lists core check:* this was run in a scratch checkout of main with a scratch cache.
- `GC.Spec.FreeLists` (#46's file, unchanged) verifies with full SMT, without `--retry`.
- Its dependencies were loaded from main's sources, not re-verified.
- `SizeClass` and `FreeLists` lax-check.
- `FreeLists.Push` fails only on the name `well_formed_heap_part1`.
- No Pages module was built against main; the breakage in §2 comes from scanning names.
