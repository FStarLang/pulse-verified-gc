# Parallel sweep, Phase 1: model, statement, attack, and proof

Branch `sheera/parallel-sweep`, from `fork/main` `0ce5e09`. Context: `spike/parallel/SPIKE.md` on `sheera/spike-parallel`.

**Status.**

- **Stage A:** the model and theorem are written.
- **Stage B:** no counterexample. 10,750 (heap, boundary list) pairs were tested, from 17 hand-built and 862 generated heaps. All four deliberately broken variants were caught.
- **Stage C:** `sweep_par_correct` is proved, with no `admit` or `assume` (§6). The model, the theorem and every `val` are unchanged. The proof uses only `valid_bounds`; the rest of `fused_pre` is not needed.

Everything is new, under `parallel-sweep/`, apart from `GC.Spec.Coalesce.Correct` and `mark-and-sweep/NOTES.md`, merged in from `sheera/coalesce-exact`. The directory is left out of the root build.

| File | Contents |
|---|---|
| `parallel-sweep/spec/GC.Spec.SweepPar.Exec.fst` | Executable twins of the ghost sweep spec, each proven equal to the original. |
| `parallel-sweep/spec/GC.Spec.SweepPar.fst` | The model `sweep_par`, the proof, the theorem, and two non-vacuity lemmas. |
| `parallel-sweep/spec/GC.Spec.SweepPar.Vacuity.fst` | A satisfying call for every proof lemma's precondition. |
| `parallel-sweep/spec/GC.Spec.SweepPar.Mutants.fst` | Four wrong merge and link steps. Used only by the tests. |
| `parallel-sweep/test/` | The OCaml driver, the build script, the runner, and the `GC.Spec.ZeroAddr` realisation. |
| `parallel-sweep/Makefile` | `make verify` and `make test`. |

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
make verify     # the four modules, about 35 s
make test       # verify, extract, build, run all 19 jobs; about 6 min on 8 cores
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
