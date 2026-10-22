# Parallel sweep, Phase 1: model, statement, attack, and proof

Branch `sheera/parallel-sweep`, from `fork/main` `0ce5e09`, with `origin/main` `f594eff` merged in (PRs #25, #26, #28). Context: `spike/parallel/SPIKE.md` on `sheera/spike-parallel`.

**Status.**

- **Stage A:** the model and theorem are written.
- **Stage B:** no counterexample. 10,750 (heap, boundary list) pairs were tested, from 17 hand-built and 862 generated heaps. All four deliberately broken variants were caught.
- **Stage C:** `sweep_par_correct` is proved, with no `admit` or `assume` (§6). The model, the theorem and every `val` are unchanged. The proof uses only `valid_bounds`; the rest of `fused_pre` is not needed.
- **Pulse, one segment:** the specification of `sweep_segment` is written and reviewed (§7). Locality, that a segment depends only on its own bytes, is tested and proved (§7). `sweep_segment` is implemented and proved against that specification, on range versions of the heap operations (§7).
- **Extraction to C (§9, Stage 1):** `prepass`, `sweep_segment`, `merge` and `sweep_par_seq` extract to C with Custard. Run one piece at a time, they give the same heap and head as the extracted `fused_sweep_coalesce` on 4,408 heaps for k = 1, 2, 4 and 8.
- **From theorem to running code:** the pre-pass, the merge, the joining lemma and a sequential driver are specified and approved (§8). All four are now implemented and proved, with no `admit` or `assume`. `sweep_par_seq` has `fused_sweep_coalesce`'s own postcondition, so the whole chain is checked end to end in one thread. No specification, model, theorem or `val` was changed.

Everything is new, under `parallel-sweep/`, apart from `GC.Spec.Coalesce.Correct` and `mark-and-sweep/NOTES.md`, merged in from `sheera/coalesce-exact`. The directory is left out of the root build.

| File | Contents |
|---|---|
| `parallel-sweep/spec/GC.Spec.SweepPar.Exec.fst` | Executable twins of the ghost sweep spec, each proven equal to the original. |
| `parallel-sweep/spec/GC.Spec.SweepPar.fst` | The model `sweep_par`, the proof, the theorem, and two non-vacuity lemmas. |
| `parallel-sweep/spec/GC.Spec.SweepPar.Vacuity.fst` | A satisfying call for every proof lemma's precondition. |
| `parallel-sweep/spec/GC.Spec.SweepPar.Local.fst` | Locality: one segment depends only on its own bytes (§7). |
| `parallel-sweep/spec/GC.Spec.SweepPar.Mutants.fst` | Four wrong merge and link steps. Used only by the tests. |
| `parallel-sweep/test/` | The OCaml driver, the build script, the runner, and the `GC.Spec.ZeroAddr` realisation. |
| `parallel-sweep/impl/GC.Impl.SweepSegment.fsti` | The Pulse specification of one segment, `sweep_segment` (§7). |
| `parallel-sweep/impl/GC.Impl.SweepSegment.fst` | Its implementation and proof (§7). |
| `parallel-sweep/impl/GC.Impl.HeapRange.fst` | `read_word`, `write_word`, whitening and `flush_blue` on one range `[lo, hi)` (§7). |
| `parallel-sweep/spec/GC.Spec.SweepPar.SegLoop.fst` | The loop invariant of `sweep_segment` and one lemma per case of its body (§7). |
| `parallel-sweep/impl/GC.Impl.SweepPar.fsti` | The Pulse specifications of the pre-pass, the merge, and a sequential driver (§8). |
| `parallel-sweep/impl/GC.Impl.SweepPar.fst` | Their implementation: `prepass` and `merge` call the two modules below, and `sweep_par_seq` is proved here (§8). |
| `parallel-sweep/spec/GC.Spec.SweepPar.Join.fsti` | The joining lemma, stated (§8). |
| `parallel-sweep/spec/GC.Spec.SweepPar.Join.fst` | Its proof, and its non-vacuity witnesses (§8). |
| `parallel-sweep/impl/GC.Impl.SweepPar.Prepass.fst` | The pre-pass, implemented and proved (§8). |
| `parallel-sweep/impl/GC.Impl.SweepPar.Merge.fst` | The merge, implemented and proved (§8). |
| `parallel-sweep/c/sweep_par_ctest.c` | The extracted C, run piece by piece against the extracted `fused_sweep_coalesce` (§9). |
| `parallel-sweep/Makefile` | `make verify` (now including every module above), `make test`, `make extract` and `make ctest` (§9). |

Toolchain: only the pinned `./fstar` (F* `nightly-2026-10-17`, `f43a1127`, Z3 5.3.0), with the repo's own F* flags. The OCaml side uses opam switch `fstar-gc` (OCaml 4.14.0).

---

## 1. The model

`bs` is a `list nat`, `[zero_addr; b1; ...; bk; heap_size]`.

- It includes both endpoints.
- Every interior `bi` is a walk position.
- The list is strictly increasing.

Segment `i` covers the objects whose headers lie in `[b_i, b_{i+1})`.

```
valid_bounds g bs =
  bs = zero_addr :: rest, and along rest:
    prev < b, b < heap_size, b % 8 = 0, walk_visits g zero_addr b    (interior)
    the last element is exactly heap_size
```

`walk_visits` is `GC.Spec.Coalesce.Correct.walk_visits` (merged from `sheera/coalesce-exact`). That one is `GTot`, so `valid_bounds` calls its executable twin `walk_visits_x`, whose type states it equals the original (see §3).

**Stage 1: segments, in parallel (`sweep_segment`, `seg_aux`).**

- Each segment walks its own objects from its own start (`seg_objects`: the walk `objects` does, stopped at `hi`). It reads colours and sizes from the frozen input heap, as `fused_aux` does.
- It runs `fused_aux`'s steps unchanged, with three differences:
  - **Leading run.** The free objects before the segment's first survivor build up into `lead`. At that survivor nothing is flushed; the survivor is whitened.
  - **Trailing run.** The run pending at the end of the segment is returned as `trail`, unflushed.
  - **No survivor.** The segment returns `all_free = true`, and `lead` is the whole segment.
- **Interior runs** are flushed with the real `flush_blue`, against a local free list that starts at the placeholder `0UL`. The segment reports `first_link`, the first block it linked, whose link word therefore holds `0UL`. It also reports `local_head`. A flush linked a block exactly when `flush_blue` returned something other than the `fp` it was given; in that case it returned the block.
- Each segment writes into its own copy of the heap. `splice_all` keeps only the bytes of `[b_i, b_{i+1})` from segment `i`'s copy. A write outside a segment's own range would therefore be lost, and the comparison would show it.

**Stage 2: merge and link, sequential, left to right (`link_all`).**

It carries a pending run `carry` (initially empty) and a global head `fp` (initially `0UL`). For each segment:

- **All free:** `carry := join carry lead`, and nothing is flushed. This chaining is what lets a run span any number of segments.
- **Otherwise:**
  - flush `join carry lead` as **one** run with `flush_blue` and `fp`, giving `fp1`;
  - if the segment linked anything, patch `first_link`'s link word (field 1, via `set_field`) to `fp1`, and set `fp := local_head`; otherwise `fp := fp1`;
  - set `carry := trail`.

At the end, flush `carry`.

```
sweep_par bs g =
  let rs = sweep_all g (segments bs) in
  link_all (splice_all g rs) no_run 0UL rs
```

`run`, `extend`, and `join` are `fused_aux`'s `(fb, rw)` pair and its accumulate step: `fb` is taken from the first non-empty piece, and `rw` is the sum.

**Guards.** `sweep_par` is total on every `list nat`, so it has three runtime guards. Each should be dead whenever `valid_bounds g bs` holds; showing that is part of the proof.

- `sweep_all` skips a pair that is not an aligned, in-range, non-empty segment.
- `patch_link` does nothing unless `first_link` is an aligned `obj_addr` with room for field 1. That always holds, because `flush_blue` only links such blocks.
- The link detection `fp' <> fp` relies on a linked block never equalling the current head. The head is either `0UL` or an earlier, lower block.

## 2. The statement

```fstar
(* The precondition of the extracted fused_sweep_coalesce,
   mark-and-sweep/impl/GC.Impl.FusedSweepCoalesce.fsti, copied. *)
let fused_pre (g: heap) : prop =
  well_formed_heap g /\
  Seq.length (objects zero_addr g) > 0 /\
  SI.heap_objects_dense g /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_gray x g))

val sweep_par_correct (bs: list nat) (g: heap)
  : Lemma (requires fused_pre g /\ valid_bounds g bs)
          (ensures sweep_par bs g == Defs.fused_sweep_coalesce g)

let sweep_par_correct bs g = (* proved; see §6 *)
```

The equality is on the pair, so it covers both the heap and the free-list head.

`make verify` checks all four modules. With `--report_assumes warn`, none reports an `admit` or `assume`. The GC modules the proof adds as dependencies (`GC.Spec.Coalesce.Correct`, `GC.Spec.SweepCoalesce.Induction`, `.Helpers`, `.FlushAgree`) contain none either.

**Non-vacuity.**

- **The theorem covers every heap the sequential pass runs on.** `whole_heap_bounds_valid g : Lemma (valid_bounds g [zero_addr; heap_size])` is proved for every `g`. So the hypotheses are exactly as satisfiable as `fused_pre`, which is the precondition the shipped collector is already called under.
- **`valid_bounds` is not trivially true.** `invalid_bounds_rejected` proves that `[]`, `[zero_addr]`, `[heap_size]`, and a repeated boundary are all rejected.
- **The hypotheses are not trivially contradictory.** A scratch lemma `fused_pre g /\ valid_bounds g bs ==> False` fails to verify. On its own this is weak evidence, since SMT failing to find a proof does not show consistency.
- **Concrete witnesses with many segments.** Stage B builds 879 concrete heaps that satisfy the executable part of `fused_pre`. For each it runs `valid_bounds` and gets `true` on 10,750 boundary lists, with up to 34 segments.
- **The conclusion is not trivially true.** `sweep_par` never calls `fused_sweep_coalesce`. The four mutants below change it slightly, and the tests show the equality then fails.

## 3. How it was tested (Stage B)

### Running the spec itself

`fused_sweep_coalesce` and everything under it are `GTot`, so F* extraction would erase them. `GC.Spec.SweepPar.Exec` therefore gives each one a `Tot` twin, built from the same `Tot` primitives (`read_word`, `write_word`, `getColor`, `getWosize`, `colorHeader`, `makeHeader`). The twin's return type states that it equals the original:

```fstar
let flush_blue_x g fb rw fp : r:(heap & U64.t){r == SpecCoalesce.flush_blue g fb rw fp} = ...
let fused_sweep_coalesce_x g : r:(heap & U64.t){r == Defs.fused_sweep_coalesce g} = ...
```

The same is done for `is_black`, `wosize_of_object`, `makeWhite`, `set_field`, `zero_fields`, `objects`, and `fused_aux`. These equalities are proved; they are small bridges, not part of the theorem. As a result, the extracted `fused_sweep_coalesce_x` computes exactly the spec's value, and `sweep_par` is itself built from those twins. The test therefore compares the stated function with the spec, not with a hand translation of either.

### Extraction and build

`make test` does the following:

1. Verifies the four modules, which writes their `.checked` files. Custard, F*'s extractor, reads every module it extracts from its `.checked` file, so these must exist first.
2. Extracts with Custard (`--codegen OCaml --custard_split`). Custard compiles the whole program reachable from its roots: the three modules, plus the spec functions the driver calls directly. It writes 13 `.ml` files, one per F* module: 8 GC modules, and the 5 F* library modules the program reaches (`FStar.Seq.Base`, for instance, compiled to lists). `--custard_no_unfold GC.Spec.Base.heap` keeps the `heap` type under its own name, since the driver's types use it.
3. Compiles them against the F* OCaml runtime. The shipped `.cmx` files were built with OCaml 5.3, so `test/build.sh` compiles the runtime's own `.ml` sources, only the reachable ones Custard did not write itself (`Prims`, `FStar_List_Tot_Base`, `FStar_UInt8`/`32`/`64`). It fails if any `Obj.magic ()` remains in the extracted GC code, which would mean a value Custard erased is still used.
4. Runs `test/run.sh`, which runs 19 jobs in parallel.

One item is supplied by hand, and it is fixed by the F* sources.

- **`GC.Spec.ZeroAddr`** is an interface whose implementation is C. `test/GC_Spec_ZeroAddr.ml` sets `zero_addr = 2048` and `heap_size_u64 = 2048 + 8 * PS_WORDS`, which satisfies every requirement in the `.fsti` (including `zero_addr >= 2048`). It also defines `heap_size`, which `GC.Spec.Base.heap_size` refers to: the `.fsti` defines it as `U64.v heap_size_u64` but marks it `noextract`, so the realisation repeats that definition.

### Each (heap, bs) pair

The driver `test/sweep_par_test.ml` builds a heap byte by byte, little-endian as `write_word` lays words out, using the extracted `makeHeader`. It reads every header back with the extracted `read_word`. Then:

1. **Precondition.** It checks the executable part of `fused_pre`:
   - the object list is non-empty;
   - every object fits in the heap (part 1);
   - no object has the infix tag (part 4);
   - every field of a scannable object that `is_pointer_field` accepts is an enumerated object (parts 2 and 3, in the form the generator guarantees);
   - density: every successor with room for a header is enumerated;
   - no object is gray.
2. **Boundaries.** It requires the extracted `valid_bounds g bs` to be `true`. It also checks that `valid_bounds` rejects every non-walk-position boundary, an out-of-order list, a repeated boundary, and lists missing an endpoint: 8,938 rejections in all.
3. **The comparison.** It compares `sweep_par bs g` with `fused_sweep_coalesce_x g`, every byte of the heap plus the free-list head. On the first difference it prints the heap layout, `bs`, both heads, and the first differing word, then stops with exit 1.
4. **Mutants.** It checks that mutant 0 equals `sweep_par`, then runs mutants 1 to 4 and counts the pairs each one gets wrong.

5. **Locality of one segment.** For each distinct segment `[lo, hi)` of the heap, it runs the model's `sweep_segment g lo hi`. It then runs it again on three copies of `g` whose bytes outside `[lo, hi)` are changed:
   - every outside byte random;
   - every outside byte flipped (`255 - b`), so every one differs;
   - the 16 bytes on each side of the segment random, plus 1 in 64 elsewhere.

   The bytes it leaves in `[lo, hi)`, and every other output, must be unchanged. It also checks that the model writes nothing outside `[lo, hi)`. The changes come from a separate random generator, so the heaps and boundary lists are the same as before. A wrong function is caught: widening the segment by one word, in a scratch copy of the driver, made the first hand-built case fail at once.

### Heaps

**Generated (862 heaps).**

- **Sizes:** 2 to 96 words after `zero_addr`, under 18 fixed seeds.
- **Colours:** per heap, the probability of black is drawn from {0, .1, .3, .5, .7, .9, 1}. The other objects are white or blue.
- **Wosizes:** weighted toward 0, 1, and 2, with some up to 13.
- **Tags:** 0, 1, 2, or 252 (no-scan).
- **Fields:** odd non-pointers, `0`, or pointers to real objects. No-scan objects get random bytes.
- **Boundary lists:** every subset of the interior walk positions when there are at most 6. Otherwise every singleton, the full set, every pair (on heaps with at most 10 positions), and 24 random subsets of varying density.

**Hand-built (17 heaps, `PS_WORDS=40`).** Each heap is padded to 40 words with one trailing object. Each is checked with its own `bs` and with every set of up to 2 walk positions.

| Case | Layout (`B` black, `W` white, `U` blue, digit = wosize, `|` = boundary) |
|---|---|
| run crossing one boundary | `B1 W1 W2 \| W1 U2 B1 …` |
| run crossing several boundaries | `B1 W1 \| W2 \| U1 W0 \| W1 \| W1 B2 …` |
| wosize-0 fragment ending a segment | `B1 W0 \| B1 W2 B1 …` |
| wosize-0 fragment starting a segment | `B1 \| W0 B1 W1 B1 …` |
| wosize-0 fragments on both sides (merge to rw = 2, linked) | `B1 W0 \| W0 B1 …` |
| wosize-0 fragment alone in a segment | `B1 \| W0 \| B1 W3 …` |
| interior fragment only, no link in the segment | `B1 \| B1 W0 B1 \| W1 …` |
| segment entirely free | `B1 \| W1 U2 W0 \| B1 …` |
| several consecutive all-free segments | `B2 W1 \| W1 \| U0 \| W3 \| W1 \| B1 …` |
| boundary at the first object's successor | `W1 \| B1 W1 B1 …` |
| boundary at the last object (free, and live) | `B1 W1 B1 W2 \| W…` / `\| B…` |
| heap entirely free, many segments | `W1 \| W0 \| U2 \| W1 \| W0 W…` |
| heap entirely live, many segments | `B1 \| B0 \| B2 \| B1 B…` |
| interior runs in every segment (chained patches) | three segments, each with internal runs |
| first segment has no links, later ones do | `B1 B1 \| B1 W1 B1 W1 B1 …` |
| trailing unenumerated wosize-0 header as a boundary | the last heap word is a wosize-0 header, which is a walk position that `objects` skips |

A boundary at the first object is always present, since `bs` starts at `zero_addr`. The cases above put the *next* boundary right after it.

### Coverage, read off the segment outputs (whole run)

| Shape | Count |
|---|---|
| (heap, bs) pairs / heaps | 10,750 / 879 |
| segments (max per bs) | 36,189 (34) |
| runs crossing exactly 1 boundary | 2,611 |
| runs crossing at least 2 boundaries | 2,265 |
| all-free segments | 15,828 |
| wosize-0 fragment as a segment's leading or trailing run | 3,428 |
| first-link patches (with a non-zero head) | 1,829 (583) |
| boundary right after the first object / at the last object | 4,171 / 4,133 |
| boundary at an unenumerated trailing wosize-0 header | 1,283 |
| locality: distinct segments / changed heaps / outside bytes changed | 10,900 / 32,700 / 48,783,185 |

### The tests can see bugs

Each mutant in `GC.Spec.SweepPar.Mutants` breaks one thing the statement depends on. Every one was caught:

| Mutant | Fault | Pairs where it differs |
|---|---|---|
| m1 `no_chain` | an all-free segment ends the carried run | 3,805 |
| m2 `no_merge` | trailing and leading runs at a boundary are flushed as two runs | 1,101 |
| m3 `no_patch` | the first linked block keeps the placeholder `0UL` | 838 |
| m4 `old_head` | the patch uses the head from before the boundary run's flush | 734 |

### Reproducing

```
cd parallel-sweep
make verify     # the four modules and the Pulse interface, about 35 s
make test       # verify, extract, build, run all 19 jobs; about 8 min on 8 cores
```

Each job's log is in `parallel-sweep/_build/logs/`. Every log must end with an `ok:` line.

## 4. Counterexamples

**None.** On every pair, `sweep_par bs g` and `fused_sweep_coalesce g` gave the same heap, byte for byte, and the same free-list head. The theorem was not changed at any point.

## 5. What this does not show

- **It is testing, not proof.** Heaps had at most 96 words past `zero_addr`. The size limit comes from cost: F*'s OCaml `Seq` is a list, and every access walks past the 2048-byte prefix, at about 85 ms per pair.
- **Parts 2 and 3 of `well_formed_heap`** were checked only in the form the generator produces (pointer fields point to enumerated objects). Arbitrary heaps meeting the opaque predicate were not enumerated. The sweep never reads fields, so this restricts which heaps were tried, not what was observed.
- **The 2048-byte prefix below `zero_addr`** is always zero, and `zero_addr` is fixed at 2048.
- **Trusted for the test:** Custard's OCaml extraction, including the F* library modules it compiles (list-based `Seq`); the runtime's `.ml` sources compiled here (`Prims`, `Stdint` `UInt64`); and `GC_Spec_ZeroAddr.ml`, including the `heap_size` definition it repeats.
- **Parallelism is modelled, not run.** The segments are evaluated one after another, each against the input heap; disjointness is modelled by `splice`.

## 6. The proof

All of it is in `GC.Spec.SweepPar.fst`, between the model and the statement, in eight parts. It works on the ghost side: the `_x` twins' types already state equality with the ghost functions.

**The sequential pass, cut at boundaries.** `fsteps` is `fused_aux` without its final flush, and returns the heap, the pending run and the head. `fused_aux_append` shows that `fused_aux` over `a ++ b` is `fused_aux` over `b`, started from the state `fsteps` gives after `a`. `objects_seg_split` and `objects_seg_last` show that the walk from a boundary is that segment's `seg_objects` followed by the walk from the next boundary.

**One segment** (`segment_correct`). The sequential pass enters segment [lo, hi) with a heap `h`, a carried run `c0` ending at `lo`, and a head `p0`. The segment starts from the input `g`, no run, and `0UL`. Each object is one step on both sides:

- **Lead phase** (`lead_phase`): neither side writes, and the sequential run is `join c0 lead`.
- **First survivor**, header at `e` (`lead_black`): the sequential pass flushes `join c0 lead` with `p0`, giving `(h1, f1)`. The segment flushes nothing, and both whiten.
- **Seen phase** (`seen_phase`, with steps `seen_free` and `seen_black`): both sides take the same steps. From `e` up, their heaps agree word for word, except the segment's first linked block `a`. Its link word holds `f1` sequentially and `0UL` in the segment. Below `e`, the sequential heap is `h1` and the segment's is `g`.

Every write lands at or above `wlo`, the pending run's first word, or the cursor when there is no run. So facts below `wlo` persist, and the link word at `a` keeps `f1` for the rest of the segment.

**One merge-and-link step** (`link_step`). `link_inv` relates the two sides at a boundary `b`:

- the sequential heap is still the input from `b` up;
- the link heap equals the sequential heap below `b`, and the spliced segments from `b` up;
- the carried runs and heads are equal.

`link_step` takes it from `b` to the next boundary. For a segment with a survivor, the edge run is flushed on both sides with the same head, and the flushes agree below `e`. Patching `a` with the head that flush returns restores the one differing word. An all-free segment writes nothing on either side.

**Two segments, then any number.** `sweep_par_two` applies `link_step` twice from `link_start`, then `link_base`. In `link_base`, the heaps agree on every word, so the final flushes agree. `link_correct` is the same argument by induction over the boundary list, and `sweep_par_correct` calls it from `link_start`.

**The guards in §1 are dead.** `sweep_all`'s guard holds by `bounds_next`. `patch_link`'s guard holds because `a` is a linked block below `hi` (`seen_post`). The link test `fp' <> fp` only matters before the first link, when `fp` is `0UL` and a linked block is at least 8.

**Reused from `GC.Spec.Coalesce.Correct`:** `walk_visits`, `walk_visits_above`, `walk_visits_prefix`, `walk_visits_next_bound`. Its step lemmas (`white_inv_step_blue`, `_flush`, and the other invariants' steps) are about `coalesce_aux` and its invariants, not `fused_aux`, so they do not apply. The flush facts come from `GC.Spec.Coalesce` (`flush_blue_preserves_outside`, `flush_blue_header_spec`, `flush_blue_field1_spec`) and from `GC.Spec.SweepCoalesce` (`flush_blue_inside_agree`, `zero_fields_read_within`, `flush_blue_snd_heap_independent`, `heaps_word_agree_implies_equal`). `flush_zero_word` re-proves a fact both modules prove only privately.

**Vacuity.** `GC.Spec.SweepPar.Vacuity` calls every proof lemma on arguments that meet its precondition: small constant runs for the flush facts, and the whole heap as one segment from `zero_addr` for the segment and link lemmas. A few witnesses need a heap shape, and are guarded by it: `heap_size >= 32`, a non-empty walk, or the first object ending inside the heap. `link_step_free` and `link_step_used` are each called in their own case of `link_step`. The witness file shows that, on every heap, one of the two preconditions holds. That each holds on some heap is shown by the tests (15,828 all-free segments, and many with a survivor), not by a formal witness.

**Proof check:** about 27 s for `GC.Spec.SweepPar`. It verifies again from scratch with `--z3seed 7`. The largest rlimit is 80, and no query needed splitting.

- **Toolchain notes from this session:**
  - The root `Makefile` needs GNU make 4 (`gmake`); macOS `make` 3.81 stops with "multiple target patterns".
  - The shared `_cache` held a `GC.Spec.Coalesce` checked file from another branch. `gmake _cache/GC.Spec.SweepCoalesce.Defs.fst.checked` rebuilt it for `fork/main`.
  - After merging `origin/main`, the shared `_cache` was stale for the spec modules it changed (`GC.Spec.Object`, `GC.Spec.Allocator`, and those above them). `make verify` still passed, re-checking them in memory, but did not write `GC.Spec.SweepPar.Vacuity`'s checked file. Rebuilding the 23 GC modules the parallel-sweep files depend on through the root `Makefile` (`gmake _cache/<module>.checked`) fixed it. After the merge, `make test`'s 19 logs are byte-for-byte identical to the ones before it.

## 7. The Pulse specification of one segment

`parallel-sweep/impl/GC.Impl.SweepSegment.fsti` is the interface. The implementation and its proof are in `GC.Impl.SweepSegment.fst` (see "The implementation, proved" below). `make verify` checks both.

The OCaml runtime owns the worker threads, and each worker calls `sweep_segment` on its own segment. The merge-and-link step (`link_all`) stays sequential and is not part of this function.

### The heap representation, and owning one range

The function reuses `GC.Impl.Heap`, as `fused_sweep_coalesce` does. A `heap_t` is a byte array `data`, and its contents are a spec `heap`, so model and implementation talk about the same bytes. The sequential pass holds `is_heap heap s`, which is a full `pts_to` on the whole array.

A segment instead holds

```fstar
let is_heap_range (h: heap_t) (lo hi: nat) (s: Seq.seq U8.t) : slprop =
  pts_to_range h.data lo hi s
```

`pts_to_range` is Pulse's standard permission for a sub-range of an array. It answers the question of whether owning one range is hard: it is not.

- `pts_to_range_intro` and `pts_to_range_split` cut a whole-array `pts_to` into one `pts_to_range` per segment, and `pts_to_range_join` puts them back. So `[lo, hi)` ranges that tile the heap can be handed out and collected again.
- `pts_to_range_index` and `pts_to_range_upd` read and write one byte inside the range.
- `pts_to_range` is `is_send`, so Pulse lets it move to another thread.

Owning `[lo, hi)` gives no access at all to any byte outside it. That is what makes running segments at the same time sound: two workers' permissions cover disjoint bytes, so neither can read what the other writes.

The cost is in the implementation, not the specification. `read_word`, `write_word` and `flush_blue_impl` take the whole-heap `is_heap`, so the implementation will need versions of them that work on `is_heap_range`.

### The signature

```fstar
fn sweep_segment
  (heap: heap_t)
  (lo: hp_addr)
  (hi: U64.t{U64.v lo < U64.v hi /\ U64.v hi <= heap_size})
  (#g: erased heap_state)
  (#bs: erased (list nat))
  requires is_heap_range heap (U64.v lo) (U64.v hi)
             (Seq.slice g (U64.v lo) (U64.v hi)) **
           pure (SP.fused_pre g /\
                 SP.valid_bounds g bs /\
                 List.Tot.memP (U64.v lo, U64.v hi) (SP.segments bs))
  returns r: seg_result
  ensures exists* s.
    is_heap_range heap (U64.v lo) (U64.v hi) s **
    pure (s == Seq.slice (SP.sweep_segment g lo (U64.v hi)).SP.sheap
                         (U64.v lo) (U64.v hi) /\
          result_matches r (SP.sweep_segment g lo (U64.v hi)))
```

`SP` is `GC.Spec.SweepPar`. The model's function is called exactly as `sweep_all` calls it: `sweep_segment g (U64.uint_to_t lo) hi`.

**Arguments.**

- `heap`, `lo` and `hi` are the only runtime arguments. `lo` is an `hp_addr`: word-aligned, and below `heap_size`. `hi` may equal `heap_size`, so it is a plain `U64.t`. The refinement `lo < hi <= heap_size` is erased in C, but it lets the signature take `Seq.slice` of `g` from `lo` to `hi`.
- `g` is ghost: the whole heap as it was before any worker started. Every worker is given the same `g`. Since it is ghost, sharing it costs nothing at run time and gives no access to memory. The model sweeps every segment against this one input heap, so the specification needs it too.
- `bs` is ghost: the boundary list the runtime chose.

**Precondition, part by part.**

1. **`is_heap_range heap lo hi (Seq.slice g lo hi)`.** The worker owns the bytes `[lo, hi)`, and nothing else, and they hold `g`'s bytes there. The rest of the heap belongs to other workers. This is the condition that makes parallel calls sound.
2. **`SP.fused_pre g`.** The heap is one the sequential pass may run on. It is the precondition of the shipped `fused_sweep_coalesce`, the same one the theorem assumes (§2). The proof of `sweep_par_correct` did not need it, but the implementation may: `fused_sweep_coalesce`'s own proof uses its density and well-formedness to keep each run inside the heap. Requiring it costs the caller nothing, since the runtime only sweeps where the sequential pass would.
3. **`SP.valid_bounds g bs /\ List.Tot.memP (lo, hi) (SP.segments bs)`.** `lo` and `hi` are two consecutive boundaries of a valid boundary list for `g`, so `[lo, hi)` is one of the segments the model sweeps. In particular, both are walk positions, or `zero_addr` and `heap_size`, so every object whose header lies in `[lo, hi)` ends at or before `hi`. That is why the segment needs no byte outside its range. This is stated through the model's own `valid_bounds` and `segments`, not a new predicate, so the result plugs straight into `sweep_all`.

**Postcondition, part by part.**

1. **`is_heap_range heap lo hi s`.** The worker gives back ownership of `[lo, hi)`, and of nothing else. The runtime can join the ranges back into the whole heap.
2. **`s == Seq.slice (SP.sweep_segment g lo hi).sheap lo hi`.** The bytes of the segment are those of the model's segment copy of the heap, restricted to `[lo, hi)`. These are exactly the bytes `splice` keeps from that copy. The model's copy outside `[lo, hi)` is not mentioned, because no worker owns it and `splice` discards it. So joining all workers' ranges gives the model's `splice_all g rs`, byte for byte.
3. **`result_matches r (SP.sweep_segment g lo hi)`.** Every returned value equals the model's.

### The returned record

`seg_out` holds a whole heap and uses `nat` and `option`, which the C extraction cannot take (`EXTRACTION_SKILL.md`: no `option` in return types, and records are flat structs of machine types). So the values other than the heap go in one flat record:

```fstar
noeq type seg_result = {
  all_free   : bool;
  lead_fb    : U64.t;  lead_rw  : U64.t;
  trail_fb   : U64.t;  trail_rw : U64.t;
  has_link   : bool;   first_link : U64.t;
  local_head : U64.t;
}
```

`result_matches r o` says, field by field:

- `all_free`, `local_head`, `lead.fb` and `trail.fb` are equal.
- `lead.rw` and `trail.rw` are equal as numbers (`U64.v r.lead_rw == o.lead.rw`). A run has at most `heap_size / 8` words, so a `U64.t` holds it.
- `first_link = None` gives `has_link = false` and `first_link = 0UL`. `Some a` gives `has_link = true` and `first_link = a`. Fixing the `None` case to `0UL` makes the record a function of the model's output, with no unspecified field.

### What the implementation and its proof will need

These are the obligations the specification creates. All are now met; see "The implementation, proved" below.

- **Locality: done.** The implementation sees only `[lo, hi)`, but the model's `sweep_segment` takes the whole heap. So the proof needs the model's result to depend only on the bytes in `[lo, hi)`. This was first tested (§3, item 5: no difference in 32,700 runs), then proved; see below.
- **Range versions** of `read_word`, `write_word`, `makeWhite`, and `flush_blue_impl`, working on `is_heap_range`.
- **From `segments bs` to walk facts.** `bounds_next` and `walk_step` in `GC.Spec.SweepPar` already turn precondition 3 into local facts: `lo < hi`, `hi` is a walk position or `heap_size`, and the walk from `lo` lands on `hi` (`reach`).
- **Joining.** A lemma that the workers' ranges, joined left to right, equal `splice_all g rs`. The sequential `link_all` then runs on the whole heap as before.

The precondition is satisfiable for every heap the sequential pass runs on: `bs = [zero_addr; heap_size]` is valid (`whole_heap_bounds_valid`), and `(zero_addr, heap_size)` is its only segment. That is the whole heap as one segment. A formal witness is left for the proof stage.

### The implementation, proved

`GC.Impl.SweepSegment.fst` implements `sweep_segment` against the interface above, unchanged, with no `admit` or `assume`.

**Range operations** (`GC.Impl.HeapRange`). `heap_range h lo hi g` is `is_heap_range h lo hi (Seq.slice g lo hi)`: the range holds the bytes `[lo, hi)` of a ghost whole heap `g`. Each operation is stated against that ghost heap. If all its writes land in `[lo, hi)`, the range afterwards holds the bytes of the spec operation's result.

- `read_word_r` gives `read_word g a`, and `write_word_r` leaves the range holding `write_word g a v`, for a word inside `[lo, hi)`.
- `makeWhite_r` writes the header the sequential pass writes, and leaves `makeWhite obj g`. Its bridge, `whiten_header`, needs only that the object is black, not `well_formed_heap`.
- `zero_fields_r` and `flush_blue_r` port `GC.Impl.Coalesce`'s code line for line, and reuse its lemmas (`flush_blue_impl_wz0`, `_wz1`, `_wz_ge2`, `zero_fields_step`). `flush_blue_r` requires the run's words to lie in `[lo, hi)`.

So the whole-heap spec lemmas apply unchanged, and the proof only has to show that addresses lie in the range. A word is read and written as 8 bytes (`pts_to_range_index`, `pts_to_range_upd`). `GC.Impl.ArrayWord`'s single-load primitives take a whole array, so using them on a range would need a new assumed primitive. Whether the C compiler merges the 8 byte accesses into one is not checked.

**The loop** keeps the model's `seg_aux` state as machine values: the cursor, the segment's copy of the heap (ghost), whether a survivor has been seen, the two runs as first block and U64 word count, the local head, and the first link as a flag and a value. `GC.Spec.SweepPar.SegLoop.loop_inv` says the following:

- running `seg_aux` from that state over the rest of the segment gives `sweep_segment g lo hi`;
- the copy still equals `g` from the cursor up;
- the cursor is a walk position with `reach g c hi`;
- the pending run ends at the cursor, inside `[lo, c)`.

`loop_inv` is opaque to SMT. The Pulse proof carries it as one fact, and one lemma per case of the loop body takes it one object further: `loop_free`, `loop_black_first`, `loop_black_seen`. `loop_head` reads the header, `loop_more` decides the loop test, and `loop_exit` turns the final state into the model's output. `loop_entry` gets `reach g lo hi` from `valid_bounds` and segment membership (`seg_mem_reach`).

- **Every access is in range.** The header read and the whitening write are at the cursor, which is below `hi`. The flushed run ends at the cursor. `lo` and `hi` are consecutive boundaries, so no object crosses `hi` (`seg_step`).
- **`fused_pre` is not used.** Only `valid_bounds` and segment membership are.

**Non-vacuity.** `seg_witness` calls the loop lemmas in the order the loop does, from the entry state of the whole heap as one segment. The entry and the first header need nothing of the heap. Each later case is guarded by the heap shape that leads to it. `range_witness` does the same for `HeapRange`'s pure lemmas. Two mutations of `sweep_segment` fail to verify: a free object that does not grow the current run, and a first link that is never recorded.

**Proof check:** about 15 s for the three modules, with the default rlimit everywhere. They also verify with `--retry` off on `--z3seed 7`.

### Locality, proved

`GC.Spec.SweepPar.Local` proves, with no `admit` or `assume`:

```fstar
let sweep_segment_local (g1 g2: heap) (lo: hp_addr) (hi: nat)
  : Lemma (requires U64.v lo <= hi /\ hi <= heap_size /\ hi % 8 == 0 /\
                    Seq.slice g1 (U64.v lo) hi == Seq.slice g2 (U64.v lo) hi)
          (ensures (let o1 = sweep_segment g1 lo hi in
                    let o2 = sweep_segment g2 lo hi in
                    Seq.slice o1.sheap (U64.v lo) hi == Seq.slice o2.sheap (U64.v lo) hi /\
                    o1.all_free == o2.all_free /\ o1.lead == o2.lead /\
                    o1.trail == o2.trail /\ o1.first_link == o2.first_link /\
                    o1.local_head == o2.local_head))
```

In words: if two heaps have the same bytes in `[lo, hi)`, then one segment gives the same bytes in `[lo, hi)` and the same other outputs on both.

**The hypothesis is weaker than the Pulse precondition.** It needs only that `hi` is word-aligned and in the heap. It does not need `fused_pre`, or that `lo` and `hi` are walk positions. So it applies to every call the precondition allows.

**Why it holds.** The proof follows `seg_aux` step by step, keeping the two runs' current heaps in agreement on `[lo, hi)`.

- **Reads.** A segment reads only object headers, and every one lies in `[lo, hi)`: the walk (`seg_objects`), the colour and size tests on the input heap, and `makeWhite`'s re-read of the header it rewrites. `seg_objects_agree` shows the two walks list the same objects, each with its header in `[lo, hi)`. That needs `hi` word-aligned, so that a header that starts below `hi` also ends at or below it.
- **Writes.** `makeWhite` and all of `flush_blue` (header, link word, `zero_fields`) write the same value at the same address in both runs. The values depend only on the run, the head and the header just read, which are equal in both runs. Writing the same word to both heaps keeps them in agreement on any range, wherever the word lands (`write_agree`). So no fact about where a flush writes is needed for this lemma.

The parts: `agree` (byte-wise agreement on a range) and its conversions to and from `Seq.slice` equality; `read_agree`; `write_agree`; `makeWhite_agree`; `zero_fields_agree`; `flush_agree`; `seg_objects_agree`; `seg_aux_agree`, by induction on the object list; and the lemma.

**Non-vacuity.** `local_witness` calls the lemma on a heap `g` and the same heap with one word below `zero_addr` overwritten. These are two different heaps meeting the hypothesis, with `[zero_addr, heap_size)` as the segment. Every other lemma in the module is called on the way, on arguments meeting its precondition.

**Proof check:** about 15 s. It also verifies with `--retry` off on `--z3seed` 0 and 7. The largest rlimit is 60.

## 8. From the theorem to running code

The theorem is about the model: `sweep_par bs g == fused_sweep_coalesce g`. Running code needs four more pieces. Each is specified below, and each is now implemented and proved; the notes under each item say where and how. `make verify` checks them all.

```
 heap g ──► prepass ──► bounds b0 < b1 < … < bn-1
                │
                ▼
   sweep_segment [b0,b1)   sweep_segment [b1,b2)   …      (workers; one record each)
                │
                ▼  ranges put back together  =  splice_all g rs     (joining lemma)
                │
              merge ──► final heap, free-list head  =  sweep_par bs g
                                                    =  fused_sweep_coalesce g
```

In the parallel collector, the OCaml runtime does the middle step on its worker threads: it hands each worker its range and gathers them back. `sweep_par_seq` does all of it in one thread, in Pulse, which shows the pieces fit together.

### 1. The pre-pass: `prepass` (`GC.Impl.SweepPar`)

```fstar
fn prepass (heap: heap_t) (k: SZ.t{SZ.v k >= 1}) (bounds: A.array U64.t)
  (#g: erased heap_state) (#s0: erased (Seq.seq U64.t))
  requires is_heap heap g ** A.pts_to bounds s0 ** pure (A.length bounds == SZ.v k + 1)
  returns n: SZ.t
  ensures exists* s. is_heap heap g ** A.pts_to bounds s **
    pure (Seq.length s == SZ.v k + 1 /\ 2 <= SZ.v n /\ SZ.v n <= SZ.v k + 1 /\
          SP.valid_bounds g (bounds_list s (SZ.v n)))
```

- **What it does:** it chooses at most `k` segments and writes their `n` boundaries into the caller's array `bounds`. `bounds_list s n` reads the first `n` entries as the model's `list nat`.
- **Precondition:** the caller owns the heap and an array with room for `k + 1` boundaries. The pre-pass does not need `fused_pre`: `valid_bounds` is meaningful on any heap.
- **Postcondition:**
  - The heap is unchanged (`is_heap heap g`, the same `g`). The pre-pass only reads.
  - The first `n` entries are a valid boundary list for `g`. So they start at `zero_addr`, end at `heap_size`, increase strictly, and every one in between is a header the sequential walk lands on. This is exactly the theorem's hypothesis.
- **Not specified:** how evenly the boundaries are spread. That affects speed, not correctness. A pre-pass that always returns `[zero_addr; heap_size]` meets the specification.
- **Implemented and proved** in `GC.Impl.SweepPar.Prepass`, with the interface's signature, with no `admit` or `assume`. Why it is a separate module is explained under item 4 below.
  - **Work.** An object counts 1, plus its wosize if it is white or blue. The sweep reads every header, and it also flushes free objects, which zeroes their fields. A first walk from `zero_addr` (`total_work`) adds up the heap's total work `W`, which is at most the heap's size in words.
  - **Cuts.** A second walk cuts at the first object start whose work before it reaches the next share's target, `floor(i * W / k)` for `i = 1 .. k - 1`. Every cut is an object start, so the heap size need not divide by `k`, and segments differ in size. An object that passes several targets gives one cut, and every target it passes is skipped. So a heap with fewer objects than `k` gets fewer segments. The target is kept as a quotient and remainder (`advance`), so `i * W` is never formed and nothing overflows. These counters are `SZ.t`, because `SZ.sizet_to_uint64` only gives `v k % pow2 64`.
  - **The proof.** The boundaries written so far form a `prefix_ok`: they start at `zero_addr`, increase strictly, and each later one passes `bounds_from`'s check (`cut_ok`). `visits_step` shows that one step of the walk from a visited position lands on a visited position. `prefix_close` turns a good prefix with `heap_size` appended into `valid_bounds` of `bounds_list`. The counter `n` never passes the share index `i`, which is at most `k`, so the closing `heap_size` always fits.
  - **Not proved: how even the segments are.** The specification does not state it, so the code above follows the rule, but nothing checks the rule.
  - **Non-vacuity.** `prepass_witness` calls every pure lemma on arguments meeting its precondition: the one-entry prefix on any heap, and a first cut on heaps whose first object ends inside the heap. Writing a cut one word past the object start makes the proof fail.
  - **Proof check:** about 25 s, with the default rlimit everywhere. It also verifies with `--retry` off on `--z3seed 7`.
- **A cost to keep in mind.** A header cannot be recognised from its bytes alone, so the only way to find walk positions is to walk from `zero_addr`. The pre-pass is therefore a sequential walk over every header. It does no writes and reads one word per object, so it is cheaper than the sweep, but it is still linear in the number of objects. Spreading the boundaries well needs that walk, or positions recorded earlier (during marking or allocation, for example). That is a design question for the implementation, not for this specification.

### 2. The merge: `merge` (`GC.Impl.SweepPar`)

```fstar
fn merge (heap: heap_t) (results: A.array seg_result) (m: SZ.t)
  (#g: erased heap_state) (#bs: erased (list nat))
  (#rs: erased (Seq.seq seg_result)) (#p: perm)
  requires is_heap heap (SP.splice_all g (SP.sweep_all g (SP.segments bs))) **
           A.pts_to results #p rs **
           pure (SP.fused_pre g /\ SP.valid_bounds g bs /\
                 results_match rs (SZ.v m) (SP.sweep_all g (SP.segments bs)))
  returns fp: U64.t
  ensures exists* h. is_heap heap h ** A.pts_to results #p rs **
    pure ((h, fp) == SP.sweep_par bs g)
```

- **What it does:** the model's `link_all`. Left to right, it chains the free runs across segment boundaries, flushes each one, patches each segment's first linked block, and threads the free-list head.
- **Precondition:**
  - **The heap** is the whole heap after all workers have finished. It is stated as the model's `splice_all g rs`: the input heap with each segment's range replaced by that worker's bytes. The joining lemma (below) is what shows the workers' output is this.
  - **`results`** holds the workers' `m` records, in segment order. `results_match` says that record `i` matches the model's output for segment `i` (`result_matches`, from §7), and that there are exactly as many records as segments. The merge only reads them, so any fraction `p` of permission is enough.
  - **`fused_pre g` and `valid_bounds g bs`.** The model's merge is defined for any heap, but its implementation, like `fused_sweep_coalesce`'s, will need to know the runs stay inside the heap.
- **No boundaries needed.** `link_all` uses only the records and the heap, never `lo` or `hi`, so the merge takes no boundary array. `bs` is ghost.
- **Postcondition:** the final heap and the returned head are the pair the model's `sweep_par bs g` returns. With `sweep_par_correct`, that is the pair `fused_sweep_coalesce g` returns.
- **Implemented and proved** in `GC.Impl.SweepPar.Merge`, with the interface's signature, with no `admit` or `assume`. It follows `link_all` record by record, and flushes with the shipped `GC.Impl.Coalesce.flush_blue_impl`.
  - **Every flushed run lies in the heap.** `flush_blue_impl` requires it. The proof derives it from each segment's own output: `GC.Spec.SweepPar.SegLoop.seg_geom` shows that a leading run starts at its segment's first object and ends by `hi`, and that a trailing run lies in `[lo, hi)`. It runs the segment loop's lemmas to the end (`seg_geom_from`), which needed one more fact in the loop invariant: before the first survivor, the leading run ends at the cursor. `bounds_chain` collects this for every segment of a valid `bs`, with each segment starting where the last ended. The carried run then always ends by the next segment's start, and a joined run by that segment's end.
  - **The patch keeps the model's own guard**, checked at run time (`patch`). Proving the guard dead in the merge, as the model's proof does, would need facts about where segments link. The guard costs four comparisons per segment.
  - **`fused_pre` is not used.**
  - **The invariant.** `merge_inv` is opaque to SMT and says three things: linking the remaining records from the current state gives `sweep_par bs g`, the remaining segments chain, and the carry ends by the next start. One lemma per case moves it: `merge_free`, `merge_used`, and `merge_exit` for the final flush.
  - **Non-vacuity.** `merge_witness` calls every lemma in the order merge does, on the whole heap as one segment, with the record built from the model's output. Two mutations fail to verify: patching with the head from before the flush (the model's mutant m4), and ending the carried run at an all-free segment (m1).
  - **Proof check:** about 17 s, with the default rlimit everywhere. It also verifies with `--retry` off on `--z3seed 7`.

### 3. The joining lemma: `join_correct` (`GC.Spec.SweepPar.Join`)

```fstar
let rec seg_bytes (rs: list SP.seg) : seq U8.t =
  match rs with
  | [] -> Seq.empty
  | r :: rest -> Seq.append (Seq.slice r.out.sheap r.lo r.hi) (seg_bytes rest)

val join_correct (g: heap) (bs: list nat)
  : Lemma (requires SP.valid_bounds g bs)
          (ensures (let rs = SP.sweep_all g (SP.segments bs) in
                    Seq.append (Seq.slice g 0 zero_addr) (seg_bytes rs) == SP.splice_all g rs))
```

- **What it says:** take the heap's bytes below `zero_addr`, then each segment's range `[lo, hi)` of that segment's copy, in order. The result is the model's spliced heap.
- **Why these pieces:** each piece is what one worker holds when it finishes. `sweep_segment`'s postcondition gives exactly `Seq.slice (sweep_segment g lo hi).sheap lo hi`, which is `r.out.sheap` for that segment in `sweep_all`. The bytes below `zero_addr` belong to no segment. Nobody writes them, so the caller keeps them as they are in `g`.
- **Why it should hold:** under `valid_bounds`, the segments start at `zero_addr`, end at `heap_size`, and touch with no gap or overlap. `splice_all` replaces each range in turn, and the ranges are disjoint, so each byte is replaced once, by its own segment. This is pure reasoning about sequences: it does not use locality or anything about the sweep.
- **How it connects to Pulse:** `pts_to_range_join` turns two adjacent ranges into one range holding the two sequences appended. Joining the range below `zero_addr` with each worker's range in turn, then `pts_to_range_elim`, gives `is_heap` holding exactly this left-hand side. So the lemma is what turns "the workers finished" into the merge's precondition.
- **Proved** in `GC.Spec.SweepPar.Join.fst`, with no `admit` or `assume`. `tiles lo0 rs` says the segments cover `[lo0, heap_size)` with no gap or overlap. `bounds_tile` shows that `valid_bounds` gives `tiles zero_addr` for `sweep_all g (segments bs)`, so none of `sweep_all`'s pairs is skipped. `splice_tiles` shows, by induction on the list and for any starting heap, that splicing a tiling equals the heap's bytes below `lo0` followed by `seg_bytes`. Its one step, `splice_prefix`, says that after splicing `[lo, hi)`, the bytes `[0, hi)` are the base's `[0, lo)` then the source's `[lo, hi)`.
- **Non-vacuity.** `join_witness` calls `join_correct` on every heap with the whole heap as one segment, which reaches every helper and both cases of `splice_tiles`. `join_witness_two` calls it with two segments, guarded by `valid_bounds`; that reaches `bounds_tile`'s recursive case. Deleting the `splice_prefix` call makes the proof fail, so the lemma is not proved trivially.
- **Proof check:** about 2 s. It also verifies with `--retry` off on `--z3seed 7`. The largest rlimit is 20.

### 4. A sequential driver: `sweep_par_seq` (`GC.Impl.SweepPar`)

```fstar
fn sweep_par_seq (heap: heap_t) (k: SZ.t{SZ.v k >= 1})
  (bounds: A.array U64.t) (results: A.array seg_result)
  (#g: erased heap_state) (#b0: erased (Seq.seq U64.t)) (#r0: erased (Seq.seq seg_result))
  requires is_heap heap g ** A.pts_to bounds b0 ** A.pts_to results r0 **
           pure (A.length bounds == SZ.v k + 1 /\ A.length results == SZ.v k /\ SP.fused_pre g)
  returns fp: U64.t
  ensures exists* h b r. is_heap heap h ** A.pts_to bounds b ** A.pts_to results r **
    pure ((h, fp) == Defs.fused_sweep_coalesce g)
```

- **What it does:**
  1. `prepass` into `bounds`.
  2. Split the heap into the range below `zero_addr` and one range per segment.
  3. Call `sweep_segment` on each segment in order, storing record `i` in `results[i]`.
  4. Join the ranges back into the whole heap.
  5. Call `merge`.
- **Precondition:**
  - The same heap condition as the shipped `fused_sweep_coalesce`: `is_heap heap g` and `fused_pre g`.
  - Two caller-provided buffers: room for `k + 1` boundaries and `k` records. This follows `GC.Impl.Stack`, whose storage the caller also provides.
- **Postcondition:** the heap and the returned free-list head are exactly what `fused_sweep_coalesce g` gives. That is the shipped function's own postcondition, so `sweep_par_seq` can stand in for it. The buffers are handed back, with unspecified contents.
- **Implemented and proved** in `GC.Impl.SweepPar.fst`, with no `admit` or `assume`.
  - **Separate modules.** `prepass` and `merge` live in `GC.Impl.SweepPar.Prepass` and `.Merge`, with the interface's signatures copied, and `GC.Impl.SweepPar.fst` defines each by calling them. Once `GC.Impl.SweepPar.fst` exists, F* requires every `val` of the interface to be defined. Keeping them separate let each step be verified and committed without stubbing the others with `admit`. `bounds_list` and `results_match` are repeated there word for word, and SMT equates them with the interface's by unfolding.
  - **The ranges.** After `prepass`, the heap is cut into `[0, zero_addr)` and `[zero_addr, heap_size)`. For segment `j` (`sweep_one`), the unswept part is cut at the segment's end, `sweep_segment` runs on the segment's range alone, and the range is joined onto the swept part. The swept part then holds `done_bytes g all j`: the bytes below `zero_addr`, then each swept segment's range. After the last segment, `done_end` uses `join_correct` to turn that into `splice_all g rs`. That is `merge`'s precondition, and `sweep_par_correct` finishes the proof.
  - **The boundary array.** `seg_facts` shows that pair `j` of `bounds_list s n` is a segment of the list, aligned and in range. It also shows that `sweep_all` gives exactly that segment at index `j`, so record `j` matches `results_match`. `ends` shows that the first boundary is `zero_addr` and the last `heap_size`.
  - **Non-vacuity.** `driver_witness` calls every pure lemma with the boundary array `[zero_addr; heap_size]`, and with three boundaries when the heap has a walk position. Two mutations fail to verify: dropping the call to `sweep_par_correct`, and storing every record at index 0.
  - **Proof check:** about 18 s, with the default rlimit apart from `--fuel 3` in the witness. Every module in `make verify` also verifies from scratch with `--retry` off on `--z3seed 7`, about 2 min.
- **Why it is useful:** it is the whole chain (`prepass`, `sweep_segment`, `join_correct`, `merge` and `sweep_par_correct`) checked end to end in one thread. Once it is proved, the only unverified part of the parallel collector is the runtime's thread handling. That handling must give each worker its own range, `bs` and `g`, and must join the ranges only after every worker has finished.

### What is left, in order

All four are done. Steps 1, 2 and 3 are below; the fourth, the sequential driver, is above.

1. ~~Prove `join_correct`.~~ Done.
2. ~~Implement and prove `sweep_segment`, using locality (§7) and range versions of `read_word`, `write_word`, `makeWhite` and `flush_blue_impl`.~~ Done; it did not need locality (§7).
3. ~~Implement and prove `prepass` and `merge`.~~ Done.
4. ~~Implement and prove `sweep_par_seq` from the three pieces.~~ Done.

What remains is outside Pulse: the OCaml runtime's thread handling, which must give each worker its own range, `bs` and `g`, and join the ranges only after every worker has finished. Neither the balance of the pre-pass's segments nor the speed of the byte-wise range access (§7) has been measured.

## 9. Extraction to C, and the threads that will run it

### Stage 1: extraction

**Build.** `make extract` writes `_build/extract/`, and `make ctest` compiles it and runs the test. Both are in `parallel-sweep/Makefile`. They use the Custard setup of `origin/main`'s `generational/Makefile`:

- `--codegen KrmlC --custard_split` writes one `Custard.krml`;
- krml runs with `-skip-compilation -skip-linking -warn-error -2-9-15`, the same three-bundle layout, and `-no-prefix` on every GC module;
- the code goes into one translation unit, `GC_SweepPar.{c,h}`, in place of `GC_Gen_Impl.{c,h}`.

The roots differ from `generational/Makefile` in one way: each function is named with `--custard_entry`, not its module with `--custard_entry_module` (finding 1). The roots are `GC.Impl.SweepPar.prepass`, `.merge`, `.sweep_par_seq`, `GC.Impl.SweepSegment.sweep_segment`, and `GC.Impl.FusedSweepCoalesce.fused_sweep_coalesce`. The C test links against `generational/snapshot/compat.c` as it is, which supplies `zero_addr`, `heap_size_u64`, `read_u64_le`, `write_u64_le` and `FStar_UInt64_ne`.

`make verify` now also checks the three interfaces, `GC.Spec.SweepPar.Join.fsti`, `GC.Impl.SweepSegment.fsti` and `GC.Impl.SweepPar.fsti`. Before, it checked each `.fst` with its interface in memory and never wrote the interfaces' `.checked` files. So `GC.Impl.SweepPar.Merge` and `GC.Impl.SweepPar` were checked but not cached (warning 247), and Custard could not read them. No F* source changed.

**The generated C signatures** (`_build/extract/GC_SweepPar.h`):

```c
typedef struct heap_t_s { uint8_t *data; size_t size; } heap_t;

typedef struct seg_result_s {
  bool all_free;
  uint64_t lead_fb;  uint64_t lead_rw;
  uint64_t trail_fb; uint64_t trail_rw;
  bool has_link;     uint64_t first_link;
  uint64_t local_head;
} seg_result;

size_t     prepass0(heap_t heap, size_t k, uint64_t *bounds);
uint64_t   merge0(heap_t heap, seg_result *results, size_t m);
seg_result sweep_segment(heap_t heap, uint64_t lo, uint64_t hi);
uint64_t   sweep_par_seq(heap_t heap, size_t k, uint64_t *bounds, seg_result *results);
seg_result sweep_one(heap_t heap, uint64_t lo, uint64_t hi);
uint64_t   fused_sweep_coalesce(heap_t heap);
```

- These are the names as first extracted. Stage 3 drops `-no-prefix` on two modules, so `heap_t` becomes `GC_Impl_Heap_heap_t`; nothing else in the list changes.
- Every ghost argument (`g`, `bs`, `rs`, `p`) and every refinement is erased. `seg_result` is the flat record of §7, field for field.
- `prepass0` and `merge0` are `GC.Impl.SweepPar.prepass` and `.merge`, the functions with the interface's specifications (finding 2).
- `sweep_one` is a helper of `sweep_par_seq` that is not in the interface (finding 3).
- `krmlinit_globals()` copies `zero_addr` and `heap_size_u64` into the copies the code reads (`zero_addr1`, `heap_size_u640`). The caller sets the two externs first, as the generational bridge does.

**What a worker runs.** `sweep_segment` calls only `read_word_r`, `write_word_r`, `getWosize`, `getTag`, `makeHeader`, `makeWhite_r`, `flush_blue_r` and `zero_fields_r`. Besides the heap, it reads two globals, `heap_size_u640` and the constant `blue`, and writes none. It allocates nothing and calls no library function. The one exit path is `makeHeader`'s default case for a colour outside the four-value enum, which no caller reaches. A word in a range is still accessed as 8 bytes (§7). At `-O2`, Apple clang 12 leaves 19 single-byte moves in `sweep_segment`'s assembly, so it does not merge them all. The cost was not measured.

**Findings from extraction.**

1. **Rooting `GC.Impl.SweepPar` as a module gives C that does not compile.** `--custard_entry_module GC.Impl.SweepPar`, as `generational/Makefile` roots its modules, also roots `bounds_list`. That is a specification helper defined in `GC.Impl.SweepPar.fsti` and not marked `noextract`. Custard compiles it, with `Seq.slice` on F*'s list-based `Seq`. krml then rejects three of the resulting definitions:

   ```
   Cannot re-check FStar.Seq.Base.tl__uint64_t as valid Low* and will not extract it.
   Warning 4: in top-level declaration FStar.Seq.Base.tl__uint64_t, in file GC_SweepPar: Malformed input:
   subtype mismatch:
     Custard_Prims_list__uint64_t (a.k.a. Custard_Prims_list__uint64_t) vs:
     Custard_Prims_list__any (a.k.a. Custard_Prims_list__any)
   ```

   The same happens for `FStar.Seq.Base.hd__uint64_t` and `GC.Impl.SweepPar.bounds_list`. krml keeps `FStar_Seq_Base_slice___uint64_t`, which calls the two dropped functions, so clang stops with `implicit declaration of function 'FStar_Seq_Base_tl__uint64_t'`. Nothing at run time calls this code. Naming the five functions as roots leaves `bounds_list` out, and the C compiles with no warnings. The other fix would be `noextract` on `bounds_list`, which would change the interface, so it was not made.
2. **`prepass0` and `merge0`.** `GC.Impl.SweepPar.Prepass.prepass` and `GC.Impl.SweepPar.prepass` share a name, and so do the two `merge`s. With both modules in one bundle and `-no-prefix`, krml gives the plain name to the private one (`static prepass`) and suffixes the public one. Taking `-no-prefix` off the Prepass and Merge modules did not change this. Callers use `prepass0` and `merge0`.
3. **`sweep_one` is public.** It is defined in `GC.Impl.SweepPar.fst` and is not in the interface. Custard does not make such definitions `static`; `generational/Makefile` notes the same.
4. **Stale checked files in the shared `_cache`.** `GC.Impl.Fields`, `GC.Impl.Coalesce.Lemmas` and `GC.Impl.FusedSweepCoalesce.Lemmas` were stale (warning 241), so Custard re-checked them in memory. Each was rebuilt through the root `Makefile` (`gmake _cache/<module>.checked`). After that, extraction prints no warning apart from those below.
5. **krml warning 17, three times.** `GC.Spec.Base.zero_addr`, `GC.Spec.Base.heap_size_u64` and `GC.Impl.Heap.zero_addr` become globals set in `krmlinit_globals`. The generational extraction does the same.

**The test** (`c/sweep_par_ctest.c`). For each heap, every k in {1, 2, 4, 8}, and each of the runs below on a fresh copy of the heap, the heap must equal what `fused_sweep_coalesce` gives on its own copy, every byte including those below `zero_addr`, and so must the free-list head:

- **pieces, in order:** `prepass0(k)`, then `sweep_segment(bounds[i], bounds[i+1])` for `i = 0 .. n-2`, then `merge0(results, n-1)`;
- **pieces, in reverse order:** the same, with the segments swept last to first. Threads may finish in any order, and this checks the result does not depend on it;
- **`sweep_par_seq(k)`:** the extracted single-thread driver.

It also checks that `prepass0` returns `2 <= n <= k + 1`, starting at `zero_addr` and ending at `heap_size`.

The heaps follow `test/sweep_par_test.ml`'s generator, so they meet the executable part of `fused_pre`. Objects tile `[zero_addr, heap_size)`, none is gray or has the infix tag, and a scannable field is odd, `0`, or an enumerated object. The bytes below `zero_addr` are random. `zero_addr` is 2048 or 4104. There are four shapes, in equal numbers:

- **mixed:** colours drawn as in the OCaml generator;
- **front-packed:** live objects at the front and one free block to the end of the heap, the shape Spike 3 found after promotion;
- **all free;**
- **all live.**

| Heaps | Words after `zero_addr` | Count |
|---|---|---|
| small | 2 to 96 | 4,000 |
| medium | 100 to 20,099 | 400 |
| large | 1,048,576 (8 MB) | 8 |

**Result.**

```
heaps: 4408 (mixed 1102, front-packed 1102, all-free 1102, all-live 1102)
(heap, k) runs: 17632, pieces: 48073, at most 8 per run, 5664 runs with fewer than k
control (last piece unswept): caught in 17409 of 17632 runs
ok: pieces (in order and reversed) and sweep_par_seq equal fused_sweep_coalesce, heap and head, k = 1, 2, 4, 8
```

There is no difference on any run. Runs with fewer than k pieces are heaps with fewer objects than k, where the pre-pass makes fewer cuts (§8).

**The test can see a missing piece.** In the control, the last segment is never swept and its record is left zeroed. The test fails unless that is caught at least once, and it is caught in 17,409 of 17,632 runs. In the other 223, leaving that segment unswept happens to give the right heap and head.

**Reproducing.**

```
cd parallel-sweep
make ctest      # verify, extract, compile with -Wall -Wextra, run; about 16 s once verified
```

**Trusted for this test:** Custard and krml; `compat.c`'s word access and externs; and the C compiler (Apple clang 12.0.0, x86_64).

### Stage 2: the threads (design only, not wired in)

`parallel-sweep/c/par_sweep.c`, 64 lines, is the C that runs the pieces on threads. Stage 3 wires it into the collector. In Stage 2 it was compiled once with `cc -c -O2 -Wall -Wextra -Wpedantic -std=c11` against the Stage 1 headers, with no warnings, but not linked or run.

It has two entry points. Both are called only from the thread that runs the collector, never at the same time:

- `par_sweep_init(nthreads)` starts the pool once, for example at collector start-up, and returns the number of workers started.
- `par_sweep(h, k)` is one sweep. It has `fused_sweep_coalesce(h)`'s meaning and returns the free-list head.

The main thread runs `prepass0`, publishes the pieces, sleeps until the last one is done, then runs `merge0`. A worker takes the next unclaimed piece, sweeps it without the lock, stores its record, and takes another. There may be more pieces than workers. The main thread does not sweep. A worker calls only `sweep_segment` and the pthread functions on lines 21 to 31.

#### Every line, and what it must guarantee

**Declarations.**

| Line | Code | Must guarantee |
|---|---|---|
| 3-4 | `#include <pthread.h>`, `<signal.h>` | Mutex, condition variables, threads, signal masks. Nothing from `caml/`. |
| 5 | `#include "GC_SweepPar.h"` | The extracted `heap_t`, `seg_result`, `sweep_segment`, `prepass0`, `merge0`, `sweep_par_seq`, unchanged. |
| 7 | `MAX_PIECES 64` | An upper bound on pieces. It sizes the two arrays, and line 54 keeps `k` within it. |
| 9 | `mu` | Guards `heap`, `npieces`, `next`, `unfinished` and `results`, and `bounds` while a sweep is running. |
| 10 | `work` | Idle workers wait on it for pieces. |
| 11 | `done` | The main thread waits on it for the last piece. |
| 12 | `nworkers` | The number of threads started. Written by `par_sweep_init` and read by `par_sweep`, both on the collector's thread. Also set to 0 in a forked child by `forget_workers` (line 35), which runs on the child's only thread. |
| 13 | `heap` (`GC_Impl_Heap_heap_t`) | The current sweep's heap. Written by the main thread under `mu` (line 58), read by workers under `mu` (line 25). |
| 14 | `bounds[MAX_PIECES + 1]` | Room for `k + 1` boundaries. Written only by `prepass0` (line 56), on the main thread, between sweeps. Read by workers only under `mu` (line 26), during a sweep. |
| 15 | `results[MAX_PIECES]` | One slot per piece. Slot `i` is written only by the worker that took piece `i`, under `mu` (line 30). Read by `merge0` after the sweep (line 63). |
| 16 | `npieces, next, unfinished` | The hand-out state, all zero at start. Under `mu`, always `next <= npieces` and `unfinished >= npieces - next`. `unfinished` counts the pieces of this sweep whose record is not yet stored. Between sweeps, `next == npieces` and `unfinished == 0`. |

**`worker`, lines 18-33.**

| Line | Code | Must guarantee |
|---|---|---|
| 20 | `(void)unused;` | No argument is used. Everything comes through the shared state, under `mu`. |
| 21 | `pthread_mutex_lock(&mu);` | A worker holds `mu` whenever it is not inside `sweep_segment`. |
| 22 | `for (;;)` | Workers never exit. They live until the process ends. |
| 23 | `while (next == npieces) pthread_cond_wait(&work, &mu);` | With no piece left, sleep. The `while` re-checks after spurious wake-ups, and when a broadcast wakes more workers than there are pieces. |
| 24 | `size_t i = next++;` | **Each piece goes to exactly one worker.** Pieces are taken only here, under `mu`, by incrementing `next`. Line 23 ensures `next < npieces`, so `i` is a piece of this sweep and `next` never exceeds `npieces`. |
| 25 | `GC_Impl_Heap_heap_t h = heap;` | The worker copies the heap handle under `mu`. It never reads the shared `heap` again for this piece. |
| 26 | `uint64_t lo = bounds[i], hi = bounds[i + 1];` | Piece `i` is the segment between consecutive boundaries. Since `i + 1 <= npieces = n - 1`, both entries are among the `n` that `prepass0` wrote this sweep. They are read under `mu`, which orders them after `prepass0`'s writes. |
| 27 | `pthread_mutex_unlock(&mu);` | Pieces are swept without the lock, so they run at the same time. |
| 28 | `seg_result r = sweep_segment(h, lo, hi);` | The only work done outside the lock. It is the extracted, proved `sweep_segment`. Its precondition holds as in `sweep_par_seq`: `(lo, hi)` is a segment of a valid boundary list for the heap, and the bytes `[lo, hi)` are still the input heap's, because no other piece touches them. It reads and writes only `[lo, hi)`, plus the read-only globals `heap_size_u640` and `blue` (Stage 1). It calls no OCaml runtime function and does not allocate. It returns, because its loop has a `decreases` clause. Distinct `i` give disjoint ranges, since the boundaries strictly increase. |
| 29 | `pthread_mutex_lock(&mu);` | Orders all of this piece's heap writes before anything the main thread does after it next takes `mu`. |
| 30 | `results[i] = r;` | Slot `i` gets piece `i`'s record. Only this worker took `i` (line 24), so no other thread writes the slot. |
| 31 | `if (--unfinished == 0) pthread_cond_signal(&done);` | **A piece is counted as finished only after its sweep has returned and its record is stored.** The last one wakes the main thread. Signalling under `mu` means the wake-up cannot be lost: the main thread checks `unfinished` under `mu` before it waits (line 61). |

**`par_sweep_init`, lines 35-50.**

| Line | Code | Must guarantee |
|---|---|---|
| 35 | `static void forget_workers(void) { nworkers = 0; }` | The child handler for `fork`. A child process has only the thread that called `fork`; the workers are not copied. Setting `nworkers` to 0 sends the child's `par_sweep` down line 55 to `sweep_par_seq`, on its own thread. That path never touches `mu`, `work`, `done` or the hand-out state, so it does not matter what state `fork` left them in. |
| 39 | `pthread_atfork(NULL, NULL, forget_workers);` | Registers that handler, before any worker exists. It then runs in every child, as `fork` returns there. `par_sweep_init` is called once, so the handler is registered once. Registering it twice would still be harmless. |
| 40-42 | `sigfillset`; `pthread_sigmask(SIG_BLOCK, &all, &old)` | Block every signal on the calling thread while threads are created. New threads inherit the mask, so **no asynchronous signal is delivered to a worker**. The OCaml runtime's handlers would otherwise run on a worker and touch runtime state. |
| 43 | `for (; nworkers < nthreads; nworkers++)` | Start up to `nthreads` workers. On return, `nworkers` is the number actually started. |
| 44-45 | `pthread_create(&t, NULL, worker, NULL)`; stop on failure | A failure leaves fewer workers, possibly none. Line 55 handles none. |
| 46 | `pthread_detach(t);` | Workers are never joined. |
| 48 | `pthread_sigmask(SIG_SETMASK, &old, NULL);` | The calling thread's signal mask is restored. The program sees no change. |
| 49 | `return nworkers;` | The number of workers started, for the caller to report. Added in Stage 3. |

**`par_sweep`, lines 52-64.**

| Line | Code | Must guarantee |
|---|---|---|
| 54 | `k = k < 1 ? 1 : k > MAX_PIECES ? MAX_PIECES : k;` | `prepass0`'s `k >= 1`. Also `k + 1 <= MAX_PIECES + 1` boundaries and `n - 1 <= k <= MAX_PIECES` records, so both arrays are big enough. |
| 55 | `if (nworkers == 0) return sweep_par_seq(h, k, bounds, results);` | With no worker, nobody would sweep and line 61 would wait forever. Instead, run the verified single-thread driver. |
| 56 | `size_t n = prepass0(h, k, bounds);` | Runs on the main thread, between sweeps, when no worker reads `bounds` (`next == npieces`). Gives `2 <= n <= k + 1` valid boundaries, so `n - 1 >= 1` pieces. |
| 57 | `pthread_mutex_lock(&mu);` | Orders `prepass0`'s writes to `bounds` before any worker's read at line 26. |
| 58 | `heap = h;` | Publishes the heap. |
| 59 | `npieces = n - 1; next = 0; unfinished = n - 1;` | Publishes this sweep's pieces `0 .. n-2`, none taken and none finished. The last sweep ended with `unfinished == 0`, so no worker is still inside an old piece. |
| 60 | `pthread_cond_broadcast(&work);` | Wakes every idle worker. A worker not yet waiting sees `next < npieces` at line 23 and does not wait. |
| 61 | `while (unfinished > 0) pthread_cond_wait(&done, &mu);` | **Merge only after every piece has finished.** The loop exits only when `unfinished == 0`, that is after `n - 1` decrements, one per piece at line 31. The `while` covers spurious wake-ups. |
| 62 | `pthread_mutex_unlock(&mu);` | At this point `next == npieces` and `unfinished == 0`, the between-sweeps state that lines 56 and 59 rely on next time. |
| 63 | `return merge0(h, results, n - 1);` | Runs on the main thread after every worker's heap writes and record stores, which are ordered before it by `mu` (lines 29 and 61). Its precondition is `merge`'s: the heap is the spliced heap and the records match, in segment order. |

#### Why the three properties hold

- **Every piece is swept.** `nworkers >= 1` here, by line 55. A worker loops while `next < npieces` (lines 23-24), so all `n - 1` pieces are taken. Each one returns (line 28) and is counted (line 31).
- **Each piece is swept by exactly one worker.** A piece is taken only at line 24, under `mu`, by `i = next++`. So the indices handed out in one sweep are `0, 1, ..., n - 2`, each once. Line 23 stops `next` before `npieces`.
- **Merge runs only after all pieces have finished.** Line 61 leaves its loop only when `unfinished == 0`. `unfinished` starts at `n - 1` (line 59) and drops only at line 31, after a sweep has returned and its record is stored. The mutex orders those writes before line 63.

**No data race.** Every shared variable other than the heap is read and written only under `mu`, apart from two cases: `bounds`, written by `prepass0` while no worker can read it, and `results`, read by `merge0` after the last worker has stored its record. On the heap, workers access disjoint byte ranges `[b_i, b_{i+1})`. C11 treats each byte as its own memory location, so two workers never touch the same one. No worker touches the bytes below `zero_addr`. The main thread touches the heap only before line 57 (`prepass0`) and after line 61 (`merge0`).

**How this relates to the proof.** `sweep_par_seq` is proved, and it makes these same calls: `prepass`, then `sweep_segment` on each segment, then `merge`. The arguments are the same, and so is the boundary array. `par_sweep` changes only the order of the `sweep_segment` calls and which thread runs each one. The argument that this keeps the result is that each call owns, and touches, only its own range (its `pts_to_range` precondition). That argument is not checked by F*: this C file is trusted. Stage 1's reverse-order run tests one other order.

#### Assumptions the caller must meet

These are the same as for calling the extracted `fused_sweep_coalesce`, plus two about the pool:

- `fused_pre` holds for the heap, the mutator is stopped, and `h.size == heap_size`.
- `zero_addr` and `heap_size_u64` are set, `krmlinit_globals()` has run, and neither changes during a sweep.
- `par_sweep_init` returns before the first `par_sweep`. Neither is called while a `par_sweep` is running.

#### Open points for review

- **The array lengths are larger than the specifications state.** `prepass`'s and `sweep_par_seq`'s Pulse preconditions require `bounds` to have exactly `k + 1` entries, and `sweep_par_seq` requires `results` to have exactly `k`. Here they are `MAX_PIECES + 1` and `MAX_PIECES`. The C receives only a pointer, and the proof bounds every write by `k`, so this is believed harmless. It is not what was proved.
- **`fork`: fixed after review.** Without lines 35 and 39, a child process would have no workers but keep `nworkers > 0`, so its first `par_sweep` would wait forever.
- **Return values that are not checked:** `pthread_mutex_lock`, `pthread_cond_wait` and `pthread_sigmask`. On default mutexes these fail only on misuse.
- **Synchronous signals** (`SIGSEGV`, `SIGBUS`) cannot be blocked. If `sweep_segment` faulted, the OCaml runtime's handler would run on a worker. The proof rules out a fault when the preconditions hold.
- **The main thread idles** during the sweep. Letting it take pieces too would add about 5 lines.
- **Choosing `k` and `nthreads`.** Some multiple of the thread count gives balance, and `MAX_PIECES` caps it. Not measured.
- **Portability.** On Linux, `-std=c11` needs `_POSIX_C_SOURCE` for `pthread_sigmask` and `sigset_t`. Checked only on macOS 15.7.9, x86_64.
- **Not done:** wiring into `collect_with_roots`, the `runtime_gen.patch` and `verified_gc/Makefile` changes Spike 3 lists, ThreadSanitizer, and programs that use the `threads` library.

### Stage 3: wired into the verified collector

#### The setting

The parallel sweep is off unless an environment variable turns it on, read once at heap set-up, like `MIN_EXPANSION_WORDSIZE`:

| Variable | Meaning |
|---|---|
| `VERGC_PAR_SWEEP_THREADS=n` | Start `n` worker threads, and sweep in parallel. Unset or `0`: the sequential `fused_sweep_coalesce`, as before. |
| `VERGC_PAR_SWEEP_K=k` | At most `k` pieces per sweep. The default is `4n`, and the pool caps it at 64. |

#### What changed, and why each change is there

| File | Change |
|---|---|
| `generational/snapshot/GC_Gen_Impl.c` | **Two hand-added lines in extracted code**, both marked `HAND-ADDED`. One is a global function pointer `vergc_sweep_hook`, `NULL` by default. The other is in `collect_with_roots`: if the hook is set, call it with the heap and the sequential `fused_sweep_coalesce`, in place of `fused_sweep_coalesce(heap)`. |
| `generational/ocaml-integration/verified_gc/par_sweep_bridge.c` | New. Reads the two variables. If on, it initialises the parallel sweep's globals, starts the pool, and installs the hook. The hook calls `par_sweep`. |
| `generational/ocaml-integration/verified_gc/alloc_gen.c` | One call, `vergc_par_sweep_setup()`, in `ensure_heap`, after `zero_addr`, `heap_size_u64` and `krmlinit_globals()` are set. |
| `generational/ocaml-integration/verified_gc/Makefile` | Compiles `parallel-sweep/snapshot/*.c`, `parallel-sweep/c/par_sweep.c` and the bridge into both `libvergc_gen.a` and `libvergc_gen_native.a`. `runtime_gen.patch` already copies every member of those archives into `libcamlrun.a` and `libasmrun.a`, so the patch is unchanged. |
| `parallel-sweep/snapshot/` | New. The extracted C from `make snapshot`, committed so the runtime builds without F*, as `generational/snapshot` is. |
| `parallel-sweep/Makefile` | `make snapshot`. `GC.Spec.Base` and `GC.Impl.Heap` no longer get `-no-prefix`. |
| `parallel-sweep/c/par_sweep.c` | The heap type is renamed (see below), and `par_sweep_init` returns the number of workers started (line 49). |

**Why the hook is in extracted code.** The sweep is called from inside the extracted collector: `gen_gc` calls `collect_with_roots`, which calls `fused_sweep_coalesce`, a `static` function in the same file. No C outside `GC_Gen_Impl.c` can replace that call. The alternative is to change `GC.Gen.Impl` in F* to call an assumed `val` with `fused_sweep_coalesce`'s specification. That would add a trusted `val` to the verified collector and require regenerating the whole snapshot, so it was not done. The hand edit is two lines. Its correctness rests on `par_sweep` having `fused_sweep_coalesce`'s result on every heap that satisfies `fused_sweep_coalesce`'s precondition. That precondition is what the verified `mark_loop_bounded` establishes at that point.

**Regenerating the snapshot drops the hook**, since the snapshot is regenerated wholesale and has had no hand patches until now. That cannot go unnoticed: the bridge refers to `vergc_sweep_hook`, so without the hook the runtime fails to link. Until the hook moves into F*, it has to be re-applied after every regeneration.

**Two extractions in one runtime.** Linking the parallel sweep's extracted C next to the generational collector's gave four duplicate symbols: `zero_addr0`, `zero_addr1`, `heap_size_u640` and `krmlinit_globals`. Both extractions name their copies of `zero_addr` and `heap_size_u64` this way.

- Without `-no-prefix` on `GC.Spec.Base` and `GC.Impl.Heap`, krml names them `GC_Spec_Base_zero_addr`, `GC_Spec_Base_heap_size_u64` and `GC_Impl_Heap_zero_addr`.
- The heap type becomes `GC_Impl_Heap_heap_t`. It has the same two fields as the generational `heap_t`. The bridge declares the generational `heap_t` itself and copies the two fields across.
- `krmlinit_globals` is renamed at compile time, with `-Dkrmlinit_globals=sweep_par_krmlinit_globals`.
- The parallel sweep's objects are compiled with `-fno-common`. Otherwise Apple clang 12 emits its two globals as common symbols, which the macOS linker does not pull out of an archive, and `ocamlrun` failed to link with `Undefined symbols: _GC_Spec_Base_zero_addr`.

The C test (`make ctest`) passes unchanged after the renaming.

**The two copies of `zero_addr`.** The parallel sweep reads its own copies, set by `sweep_par_krmlinit_globals()` from the same `zero_addr` and `heap_size_u64` externs the generational collector reads. The bridge calls it once, at set-up. The major heap never grows: `alloc_gen.c` allocates it once in `ensure_heap`. So the copies stay equal.

**With the setting off,** behaviour is unchanged: the hook stays `NULL`, and `collect_with_roots` calls `fused_sweep_coalesce` as before. `make test` and `make test-native` pass, as they did on the same tree before the change. The generational snapshot's own `make -C generational/snapshot test` passes too.

#### The test build

`parallel-sweep/rt/build.sh check` builds a test runtime, out of tree under `parallel-sweep/_build/rt/check/`. It then rebuilds the tree's runtimes as the default build. The test runtime is the same collector with the bridge compiled with `-DVERGC_PAR_SWEEP_CHECK`. At every major collection, that bridge:

1. copies the heap `[zero_addr, heap_size)` aside;
2. runs the collector's own sequential `fused_sweep_coalesce` (passed in through the hook), and keeps its heap and head;
3. puts the copy back, and runs `par_sweep` on it;
4. aborts unless the heap is equal byte for byte and the head is equal;
5. prints at exit: `par-sweep check: N collections, heap and head equal to the sequential sweep, W workers, k K`. `W` is the number of workers actually started.

The heap left in place is the parallel sweep's.

**The check is live.** With `VERGC_PAR_SWEEP_CHECK_CONTROL=1`, the test bridge flips one heap byte after the parallel sweep. On `infix_closures`, the run aborts at the first collection:

```
par-sweep check: collection 1 DIFFERS: head 140461321732104 vs sequential 140461321732104, first differing byte at offset 1200000 of 2400000
```

`parallel-sweep/rt/run.sh byte|native VARIANT THREADS [K]` runs each program on the test runtime with the setting on, and on the tree's default runtime with it off. It requires, for each program:

- both runs exit 0;
- the same stdout, with heap addresses masked;
- the summary line, with at least one collection compared.

For native code, it links each program twice with the stock `ocamlopt`, once against each `libasmrun.a`, using `-I` as `make test-native` does.

The programs and heap sizes are Spike 3's, chosen to force major collections. `nursery_no_scan_interior` is left out because it does no major collection at any size tried. `fasta` is bytecode only, for the reason Spike 3 gives.

| Program | Major heap (words), args | Collections compared |
|---|---|---|
| `infix_closures` | 300000 | 54 |
| `no_scan` | 4000000 | 22 |
| `make_vect_barrier` | 4000000 | 2 |
| `alloc_exact_promotion` | 4194304, `4194304` | 3 |
| `fasta` (bytecode only) | 300000, `100000` | 31 |
| `count_change` | 2000000, `100` | 2 |
| `binarytrees` | 1000000, `10` | 34 |

The counts are the same in bytecode and native, and for every number of workers and every k below.

#### Step 1: one worker

`run.sh byte check 1 K` and `run.sh native check 1 K`, for K = 1, 4 (the default) and 64:

| | k = 1 | k = 4 | k = 64 |
|---|---|---|---|
| bytecode (148 collections) | ok | ok | ok |
| native (117 collections) | ok | ok | ok |

At every collection, the heap and the free-list head were equal to the sequential sweep's, and every program's output was the default runtime's. In each run the summary reports `1 workers`, so the pool started and `par_sweep` took the threaded path, not the `sweep_par_seq` fallback.

#### Step 2: 2, 4 and 8 workers

The same runs, with 2, 4 and 8 workers:

| Workers | k | bytecode (148 collections) | native (117 collections) |
|---|---|---|---|
| 2 | 8 (default), 64 | ok | ok |
| 4 | 16 (default), 64 | ok | ok |
| 8 | 32 (default), 64 | ok | ok |
| 8 | 1, 2 (fewer pieces than workers) | ok | ok |

At every collection, the heap and the free-list head were equal to the sequential sweep's, and every program's output was the default runtime's. Every summary reports the requested number of workers started.

Not shown by this step: how the pieces were spread over the workers. The test bridge cannot see which thread swept which piece without instrumenting `par_sweep.c`, and that was not done. Step 4's ThreadSanitizer runs show heap accesses from the worker threads.
