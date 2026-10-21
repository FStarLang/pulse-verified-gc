# Parallel sweep, Phase 1: model, statement, attack, and proof

Branch `sheera/parallel-sweep`, from `fork/main` `0ce5e09`, with `origin/main` `f594eff` merged in (PRs #25, #26, #28). Context: `spike/parallel/SPIKE.md` on `sheera/spike-parallel`.

**Status.**

- **Stage A:** the model and theorem are written.
- **Stage B:** no counterexample. 10,750 (heap, boundary list) pairs were tested, from 17 hand-built and 862 generated heaps. All four deliberately broken variants were caught.
- **Stage C:** `sweep_par_correct` is proved, with no `admit` or `assume` (§6). The model, the theorem and every `val` are unchanged. The proof uses only `valid_bounds`; the rest of `fused_pre` is not needed.
- **Pulse, one segment:** the specification of `sweep_segment` is written and type-checks (§7). It is not implemented or proved yet. It is waiting for review.

Everything is new, under `parallel-sweep/`, apart from `GC.Spec.Coalesce.Correct` and `mark-and-sweep/NOTES.md`, merged in from `sheera/coalesce-exact`. The directory is left out of the root build.

| File | Contents |
|---|---|
| `parallel-sweep/spec/GC.Spec.SweepPar.Exec.fst` | Executable twins of the ghost sweep spec, each proven equal to the original. |
| `parallel-sweep/spec/GC.Spec.SweepPar.fst` | The model `sweep_par`, the proof, the theorem, and two non-vacuity lemmas. |
| `parallel-sweep/spec/GC.Spec.SweepPar.Vacuity.fst` | A satisfying call for every proof lemma's precondition. |
| `parallel-sweep/spec/GC.Spec.SweepPar.Local.fst` | Locality: one segment depends only on its own bytes (§7). |
| `parallel-sweep/spec/GC.Spec.SweepPar.Mutants.fst` | Four wrong merge and link steps. Used only by the tests. |
| `parallel-sweep/test/` | The OCaml driver, the build script, the runner, and the `GC.Spec.ZeroAddr` realisation. |
| `parallel-sweep/impl/GC.Impl.SweepSegment.fsti` | The Pulse specification of one segment, `sweep_segment` (§7). No implementation yet. |
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

`parallel-sweep/impl/GC.Impl.SweepSegment.fsti`. It is specification only: no body and no proof. `make verify` type-checks it.

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

Nothing below is done yet. These are the obligations the specification creates.

- **Locality: done.** The implementation sees only `[lo, hi)`, but the model's `sweep_segment` takes the whole heap. So the proof needs the model's result to depend only on the bytes in `[lo, hi)`. This was first tested (§3, item 5: no difference in 32,700 runs), then proved; see below.
- **Range versions** of `read_word`, `write_word`, `makeWhite`, and `flush_blue_impl`, working on `is_heap_range`.
- **From `segments bs` to walk facts.** `bounds_next` and `walk_step` in `GC.Spec.SweepPar` already turn precondition 3 into local facts: `lo < hi`, `hi` is a walk position or `heap_size`, and the walk from `lo` lands on `hi` (`reach`).
- **Joining.** A lemma that the workers' ranges, joined left to right, equal `splice_all g rs`. The sequential `link_all` then runs on the whole heap as before.

The precondition is satisfiable for every heap the sequential pass runs on: `bs = [zero_addr; heap_size]` is valid (`whole_heap_bounds_valid`), and `(zero_addr, heap_size)` is its only segment. That is the whole heap as one segment. A formal witness is left for the proof stage.

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
