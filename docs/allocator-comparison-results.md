# Allocator comparison: results of the measurement

This note reports the measurement planned in section 6 of
`docs/allocator-comparison.md`. It compares A, the size lists with the
object-start table, against B, the OCaml 5-style pages by size class. The
prototypes are unverified C, built for measurement only.

**Verdict.** As measured, B does not meet the decision rule, so the rule keeps
A.

- **Correctness:** every check that ran passed, for both allocators, in all
  three sweep modes.
- **Incremental pauses:** B's longest pause is clearly shorter.
- **Sequential run time:** B is 5.2% slower than A on binarytrees 16, just
  over the 5% limit.
- **Parallel sweep:** at 4 threads, B is slower than A on livemap.
- **Memory:** B needs more than 10% more heap than A on two programs, which
  the note treats as a warning sign.

**Two more variants, B2 and B3 (section 9), do not change the verdict.**
- **B2 fixes binarytrees.** B2 is OCaml 5's allocator as it is: its classes
  under 128 words, and an exact-size area for larger blocks. On binarytrees
  it needs no more heap than A, and its mark is as fast as A's.
- **B3 has smaller pages**, which cut minilight's extra heap by half. At
  8 KB, though, binarytrees needs 23 to 31% more heap.
- **Every variant fails the parallel condition on livemap.**
- **B2 and B3 at 16 KB are within 5% of A's run time on every program.** So
  they fail only that parallel condition. These run times are medians of 3,
  with 5 more interleaved rounds on the two programs the medians left
  unclear.
- **The other timings are weaker evidence:** most are the mean of 2 runs on
  a noisy machine, not the median of 3.

## 1. What was built

The code is on branch `sheera/alloc-pages-proto`, taken from
`origin/sheera/object-table` at `39930322`. Nothing has been committed.

- **The hook.** `verified_gc/proto/hook_snapshot.py` writes
  `GC_Gen_Impl_proto.c`, a copy of the extracted code. In that copy,
  `allocate` and the sweep step of the major collection call the prototype,
  and the mark has timers. The verified functions stay under new names,
  `vergc_lists_allocate` and `vergc_verified_fused_sweep`. The snapshot itself
  is unchanged. `make PROTO=A|B` builds the hooked runtime, and a plain `make`
  builds A as it stands.
- **B** (`proto/alloc_pages.c`), as designed in the note:
  - pages of 4096 words (32 KB) from `zero_addr`, with a side page map;
  - the 40 size classes of section 3.1;
  - blue filler headers after each rounded-up object and at each page's tail,
    and a blue block over the unused pages at the end of the heap, so the
    heap stays tiled;
  - large objects in large-object pages: first fit, carved from the right,
    with coalescing that stops at the edge of the run.

  B has three sweeps:
  - **sequential:** in address order;
  - **parallel:** by pages;
  - **incremental:** page by page. An allocation first sweeps one unswept page
    of its class, as OCaml 5's `pool_find` does.
- **A's baselines** (`proto/sweep_lists.c`):
  - **Sequential:** the verified `fused_sweep_coalesce` itself.
  - **Parallel:** a sweep over the 17 lists, cut at entries of the
    object-start table. Each piece is a fused sweep with its own lists. A
    join, in address order, merges free runs that cross a cut, repairs the
    table entries, and splices the lists in the order the sequential sweep
    pushes them. The result is therefore identical, word for word, to the
    sequential sweep's, and the check build compares it that way.
  - **Incremental:** the fused sweep's loop made resumable at a cursor. An
    allocation that finds nothing while a sweep is open sweeps one more slice
    and retries.
- **Shared by both allocators** (`proto/proto_common.c`):
  - one `pthread` pool, started once;
  - 8 chunks per thread, taken dynamically from a shared counter;
  - slices of 4096 words for both incremental sweeps;
  - the same pacing: before each minor collection, sweep until the swept
    fraction is at least min(1, 4 × promoted / heap);
  - timers using `clock_gettime`.

  A pause is the sweep work done inside one stop: a minor collection, a
  direct major allocation, or a full collection. Each pause is one of three
  kinds: a burst (the slices before a minor collection), an allocation that
  had to sweep, or a full collection finishing an open sweep.
- **Not built:** the per-object intern change of section 4.4. B was measured
  without it.

### 1.1 One fairness adjustment

The bridge starts a major collection when the words promoted since the last
one exceed half the heap, and it counts the words requested. B uses more words
than are requested, because objects are rounded up to their size class, so
this trigger let B fill the heap: it ran out of memory on binarytrees 14 at
16M words. For B only, the trigger is scaled by B's measured ratio of used
words to requested words, which is 1.09 on binarytrees 18
(`VERGC_CONSUMED` in `alloc_gen.c`). For A the ratio is 1, so A is unchanged.

## 2. Correctness

All checks were run after the machine restarted, on the final code.

### 2.1 The same survivors as the verified sweep, at every collection

The check builds (`A-check`, `B-check`) do the following at every major
collection:

1. Copy the heap after the mark.
2. Run the verified `fused_sweep_coalesce` on the copy; its result is the
   oracle.
3. Compare the prototype's result with the oracle:
   - **Eager sweeps:** after the sweep, the surviving headers and the contents
     of every survivor must equal the oracle's. For A's parallel sweep, the
     whole heap, the 17 lists and the table must also be identical.
   - **Incremental sweeps:** at each unit of sweep (a slice for A, a page or
     large run for B), every survivor in it must come out white and
     unchanged, and every dead block must be covered by a blue block.
   - **When an incremental sweep closes:** the blocks that are not blue must
     be exactly the oracle's survivors plus the blocks allocated since the
     sweep started.
4. B's invariant checker also runs after every collection. It checks the
   page map, the lists, the unused end of the heap and the free-page hint.
   A's own `-DVGC_CHECK_ALLOC` checker is on in `A-check`.

| Build | Mode | Passed | Not run |
|---|---|---|---|
| B-check | seq | hamming, livemap, livegraph, minilight, bdd, fft, bt16 (1.25×), markbench (0.25×) | bt18 |
| B-check | par (4 threads) | the same 8 | bt18 |
| B-check | incremental | hamming, livemap, livegraph (1.25×), minilight, bdd, fft, bt16 (1.25×), markbench (0.25×) | bt18 |
| A-check | seq | the same 8 | bt18 |
| A-check | par (4 threads) | the same 8 | bt18 |
| A-check | incremental | hamming, livemap, livegraph, minilight, bdd, fft, bt16 (1.25×), markbench (0.25×) | bt18 |

Programs run at their usual heap unless a scale is shown. bt16 runs at 1.25×
because B does not complete at the usual heap (section 4). markbench runs at
0.25× to keep the copying check affordable.

**Checks that were skipped, and why.**
- **binarytrees 18, every build and mode.** The check pass ran it at 0.5× the
  usual heap (268M words). That is below the smallest heap of both
  allocators: A needs 269M and B needs 301M. B's sequential and parallel
  checks ran for 1.9 and 1.4 hours and then ran out of memory. That was an
  error in the test setup, not a failure of the sweep. A run at a heap that
  fits (0.6×) would take about 2 to 3 hours per mode per allocator, so on the
  user's instruction it was stopped (incremental) or not started (A). The
  sweep code is the same for every program, and bt16, which has the same
  allocation pattern, passed in every mode.
- **B incremental on livegraph at the usual heap.** It ran out of memory
  (section 4.1) and was checked at 1.25× instead.

**One checker fix.** The closing check first rejected B's incremental sweep on
minilight with "a survivor's header changed". The program runs while an
incremental sweep is open, and `Lazy.force` turns a `Lazy_tag` (246) block
into a `Forward_tag` (250) block in place. The check now allows exactly that
one change. The rerun passed all 1,110 collections. Any other header change
still fails.

**Control mutants.** Each mode has a deliberately wrong sweep
(`VERGC_PROTO_CHECK_CONTROL=1`). Each was run on livegraph, and the check
rejected every one. A's sequential sweep has no mutant, because it is the
verified sweep itself.

| Mutant | Rejected with |
|---|---|
| B seq/par: the last slot of every page is never looked at | survivor header differs from the verified sweep's |
| B incremental: the same | a blue slot is on no list (invariant checker) |
| A par: a free run crossing a cut stays split in two | header differs from the verified sweep's |
| A incremental: the cycle's first black block stays black | a survivor is not white after its sweep |

### 2.2 `make test` and `make test-native`

All six combinations pass: A-check and B-check, each in seq, par and
incremental. The tests run in a copy of `tests/` (`tools/proto-maketest.sh`).

### 2.3 The OCaml testsuite

| Runtime | Passed | Failed | New failures |
|---|---|---|---|
| A as it stands | 2,925 | 62 (all expected) | 0 |
| B, seq | 2,923 | 64 (62 expected) | 2, both timeouts; they pass on rerun |

Both of B's extra failures were `tests/regression/pr9853/compaction_corner_case`
(native and bytecode), which timed out while a check pass ran on the same
machine. The test calls `Gc.compact` 25,001 times. Under that load it took
279 s on A and 297 s on B, against a limit of 300 s. Of B's 296 s spent in
full collections, the sweep was 2.3 s. Rerun alone, both tests pass (4 min
39 s for the pair). So B adds no new failures.

The testsuite was run with B in sequential mode only. The parallel and
incremental modes were covered by `make test` and the oracle checks, not by
the testsuite.

### 2.4 Output

Every run in the timing campaign compared its standard output with stock
OCaml's, by SHA-256, and every successful run matched. Two caveats:
- markbench prints its own seconds per collection; that line is masked before
  comparing.
- bdd and fft print nothing, so for them the comparison only confirms an
  empty output and a clean exit.

## 3. Method

- **Machine:** an Intel i5-1038NG7 laptop (4 cores, 8 threads, 16 GB),
  macOS.
- **Programs:** all bytecode. The note also asked for native code where
  earlier notes used it, and for hamming at 8M words; neither was run.
- **Runs:** median of 3. The 11 configurations run interleaved within each
  round, and each run waits for a 1-minute load below 2, for up to 2 minutes.
  The note asked for hyperfine with at least 5 runs; the user's instruction
  was the median of 3.
- **Noise:**
  - **The livemap round that was redone.** One round of livemap ran with a
    1-minute load of 2.3 to 8.1 because of some other activity on the
    machine. Those 11 runs were set aside (tag `final-noisy`) and the round
    was rerun on a quiet machine.
  - **Uneven rounds.** The third round ran 13 to 20% faster than the others
    on markbench, minilight, bdd, fft and livegraph, and slower on bt18. All
    configurations ran in every round, so medians stay comparable, but a
    difference of a few percent between configurations is near the noise.
    Runs within a round were tight: bt16 base was 13.84 to 13.89 s, and B was
    14.57 to 14.71 s.
- **Builds:**
  - `base` is A as it stands, with no hooks.
  - `A` and `B` are the hooked builds. Their sequential modes carry the same
    timers and hook calls.
  - The `A:seq` build's run time is within 1.6% of `base` on every program
    except hamming, which runs for 0.3 s.
- **No `sample`, `lldb` or attaching tool was used.** All numbers come from
  timers inside the runtime and the bench script's wall clock.

Raw data, in `generational/ocaml-integration/_build/proto-results/`:
- the runs: `runs.jsonl` (tags `final`, `final-lg125`, `check` and
  `control`);
- the smallest-heap searches: `minheap.jsonl`;
- the logs: `logs/`.

The tables come from `tools/proto-bench.py summary final`.

## 4. Smallest heap

The smallest heap each program completes in, sequential sweep, in words.
Bisection is to 2%. When a program fails at its usual heap, the search grows
upward by a quarter.

| Program | A | B | B vs A |
|---|---|---|---|
| hamming | 4,489,216 | 4,550,656 | +1.4% |
| binarytrees 16 | 67,108,864 | 73,400,320 | +9.4% |
| binarytrees 18 | 269,484,032 | 300,941,312 | **+11.7%** |
| livemap | 16,502,784 | 17,793,024 | +7.8% |
| livegraph | 16,039,936 | 16,039,936 | 0 |
| markbench | 104,302,080 | 104,302,080 | 0 |
| minilight | 446,464 | 569,344 | **+27.5%** |
| bdd | 1,903,104 | 2,006,784 | +5.4% |
| fft | 15,373,056 | 15,373,056 | 0 |

B never fits in a smaller heap than A. It needs more on six of the nine
programs. On two of them it needs more than the 10% that section 6.3 calls a
warning sign. binarytrees 16 does not complete with B at its usual heap of
64M words. The cost comes from rounding up to size classes: on binarytrees
18, B uses 1.09 words for each word requested.

### 4.1 The incremental sweep needs more heap with B

| livegraph, smallest heap | A | B |
|---|---|---|
| Sequential | 16,039,936 | 16,039,936 |
| Incremental | 16,039,936 | 17,039,360 (+6.2%) |

With B, livegraph runs out of memory in incremental mode at its usual heap
(16,777,216 words). With A it completes. The two allocators find memory
differently while a sweep is open:
- **A** finds a free block only behind the sweep cursor, and the unused
  space is at the end of the heap. So it reuses all the garbage before it
  grows.
- **B** follows the note (section 4.2) and OCaml 5. An allocation first
  sweeps the unswept pages of its class that had a free slot, then takes a
  fresh page before sweeping the remaining pages. In mid-cycle, newly
  promoted objects and not-yet-swept garbage take space at the same time.

The incremental table in section 6 therefore also has livegraph at 1.25× for
both allocators.

## 5. Sequential sweep: run time and collection time

Medians of 3. The heap is the program's usual one, except for bt16 (1.25×).
"A run" is `base`. "vs A:seq" compares B with the hooked A build, which
carries the same hooks and timers. Collection time is the minor collections
plus the full collections, from the runtime's timers. Mark and sweep times
are the median per major collection.

| Program | heap (M words) | A run s | B run s | B vs A | B vs A:seq | A coll s | B coll s | A majors | B majors | A mark ms | B mark ms | A sweep ms | B sweep ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| hamming | 16 | 0.34 | 0.26 | −21.8% | −17.8% | 0.20 | 0.14 | 1 | 1 | 20.05 | 16.28 | 4.32 | 2.46 |
| bt16 | 80 | 13.86 | 14.58 | **+5.2%** | +3.8% | 11.92 | 12.73 | 47 | 51 | 24.33 | 40.53 | 24.33 | 3.37 |
| bt18 | 512 | 61.27 | 62.81 | +2.5% | +3.5% | 50.84 | 54.26 | 33 | 36 | 95.39 | 161.38 | 132.11 | 23.04 |
| livemap | 24 | 8.93 | 8.11 | −9.2% | −9.4% | 3.89 | 3.21 | 14 | 14 | 37.78 | 66.42 | 16.87 | 10.78 |
| livegraph | 16 | 5.05 | 4.70 | −6.9% | −8.0% | 1.48 | 1.20 | 4 | 4 | 230.80 | 218.56 | 20.98 | 14.87 |
| markbench | 405 | 14.22 | 14.01 | −1.5% | −2.8% | 13.87 | 13.49 | 5 | 5 | 2378.62 | 2349.14 | 112.92 | 62.80 |
| minilight | 4 | 18.94 | 19.43 | +2.6% | +1.0% | 6.99 | 7.02 | 987 | 1110 | 1.01 | 1.09 | 0.42 | 0.23 |
| bdd | 9 | 37.03 | 35.86 | −3.2% | −0.6% | 5.21 | 5.04 | 320 | 329 | 3.25 | 3.16 | 0.66 | 0.33 |
| fft | 111 | 17.37 | 15.83 | −8.8% | −7.8% | 9.49 | 8.25 | 33 | 33 | 16.31 | 16.71 | 14.17 | 8.63 |

The hamming run is 0.3 s, too short to rank the allocators, and `A:seq` is
itself 4.9% faster than `base` there.

What the table shows:
- **B's sweep is 1.4 to 7 times faster** per collection: 3.4 against 24.3 ms
  on bt16, and 23 against 132 ms on bt18. A walks every header and merges
  runs; B looks at one header per slot.
- **On binarytrees, B loses more elsewhere than its sweep saves.** Per run on
  bt18:

  | bt18, ms per run | A | B | B vs A |
  |---|---|---|---|
  | Minor collections | 43,000 | 47,000 | +10% |
  | Mark | 3,400 | 6,300 | +85% |
  | Sweep | 4,600 | 760 | −84% |

  On bt16, the minor collections are again +10% and the mark +80%.
  - The minor collections promote into B's allocator, which writes a filler
    header after each rounded-up object and sometimes refills a page.
  - The mark is slower on bt16, bt18 and livemap, but not on livegraph,
    markbench or the Sandmark programs. This matches risk 5 of the note
    (locality): a promoted tree is split across pages by size.
- **B makes more major collections** on bt16 (51 against 47), bt18 (36
  against 33), minilight (1110 against 987) and bdd (329 against 320). Its
  scaled trigger counts the rounded-up words.

**Against the rule** (at most 5% slower than A on every program): bt16 is
+5.2% against `base`, with the three runs tightly grouped. It is +3.8% against
the hooked `A:seq`. bt18 is +2.5% and +3.5%. B is faster on six programs, by
up to 9%.

## 6. Parallel sweep: sweep time at 1, 2 and 4 threads

Median sweep time per major collection, in ms. "Speedup" is each allocator's
sequential sweep divided by its 4-thread sweep. "Balance" is the slowest
thread's time over the mean. "A4 / B4" above 1 means B is faster at 4 threads.

| Program | A seq | A 1 | A 2 | A 4 | A 4 speedup | A 4 balance | B seq | B 1 | B 2 | B 4 | B 4 speedup | B 4 balance | A4 / B4 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| hamming | 4.316 | 4.572 | 3.127 | 1.836 | 2.35× | 1.15 | 2.462 | 2.387 | 1.854 | 1.392 | 1.77× | 1.05 | 1.32× |
| bt16 | 24.326 | 24.733 | 12.385 | 7.236 | 3.36× | 1.11 | 3.372 | 3.586 | 2.925 | 2.693 | 1.25× | 1.04 | 2.69× |
| bt18 | 132.108 | 140.426 | 70.829 | 43.662 | 3.03× | 1.12 | 23.042 | 24.250 | 19.333 | 18.381 | 1.25× | 1.04 | **2.38×** |
| livemap | 16.866 | 16.854 | 9.318 | 5.278 | 3.20× | 1.12 | 10.778 | 10.851 | 6.276 | 6.358 | 1.70× | 1.02 | **0.83×** |
| livegraph | 20.978 | 21.672 | 11.586 | 6.493 | 3.23× | 1.05 | 14.870 | 15.077 | 8.588 | 5.309 | 2.80× | 1.03 | 1.22× |
| markbench | 112.915 | 111.438 | 62.490 | 43.105 | 2.62× | 1.03 | 62.805 | 63.623 | 43.938 | 40.391 | 1.55× | 1.01 | 1.07× |
| minilight | 0.425 | 0.455 | 0.378 | 0.267 | 1.59× | 1.52 | 0.227 | 0.228 | 0.189 | 0.190 | 1.19× | 1.63 | 1.41× |
| bdd | 0.659 | 0.722 | 0.654 | 0.446 | 1.48× | 2.01 | 0.327 | 0.327 | 0.254 | 0.231 | 1.42× | 1.64 | 1.93× |
| fft | 14.167 | 14.646 | 9.398 | 5.762 | 2.46× | 1.25 | 8.629 | 8.753 | 5.617 | 5.274 | 1.64× | 1.04 | 1.09× |

- **A's parallel sweep scales well:** 2.5 to 3.4 times faster at 4 threads on
  the larger heaps. The join, which repeats the sequential result word for
  word, costs little.
- **B's barely scales:** 1.25 times faster on binarytrees, with balanced
  threads (balance 1.04), and the serial join is a few list splices. This is
  probably because B's sequential sweep already runs near the memory bandwidth
  of this machine: it reads one header per slot in a streaming pass, so more
  threads gain little. That explanation was not measured.
- **At 4 threads B is still faster on most programs,** 2.4 times on bt18,
  because its sequential sweep is so much faster. On livemap, though, A at 4
  threads beats B at 4 threads, 5.3 against 6.4 ms.

**Against the rule** (B clearly faster at 4 threads, for example at least 1.3
times on bt18 and livemap): bt18 meets it (2.38×), livemap does not (0.83×).

## 7. Incremental sweep: pauses

A pause is the sweep work inside one stop. Times are in ms, medians of 3:
- **max:** the longest pause;
- **p99:** the 99th percentile;
- **total:** the sum of all pauses;
- **burst max** and **alloc max:** the longest pause of each kind;
- **finishes:** full collections that had to close an open sweep.

| Program | A max | A p99 | A total | A burst max | A alloc max | A finishes | A run s | B max | B p99 | B total | B burst max | B alloc max | B finishes | B run s |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| hamming | 0.476 | 0.476 | 0.6 | 0.476 | 0.007 | 0 | 0.30 | 0.300 | 0.300 | 2.4 | 0.300 | 0.003 | 0 | 0.26 |
| bt16 | 18.468 | 1.438 | 1248.1 | 1.751 | 18.468 | 0 | 14.21 | 0.410 | 0.215 | 305.7 | 0.410 | 0.032 | 0 | 14.94 |
| bt18 | 92.188 | 1.210 | 5021.5 | 2.032 | 92.187 | 0 | 61.78 | 0.564 | 0.206 | 1235.7 | 0.564 | 0.020 | 0 | 63.84 |
| livemap | 2.393 | 2.140 | 241.5 | 2.393 | 0.013 | 0 | 9.04 | 1.381 | 1.095 | 154.5 | 1.381 | 0.005 | 0 | 8.25 |
| livegraph | 2.878 | 2.823 | 73.3 | 2.878 | 0.007 | 0 | 5.00 | out of memory | | | | | | |
| livegraph (1.25×) | 1.894 | 1.884 | 46.1 | 1.894 | 0.007 | 0 | 4.10 | 1.511 | 1.341 | 31.6 | 1.511 | 0.003 | 0 | 3.90 |
| markbench | 120.151 | 120.151 | 467.0 | 0.000 | 0.000 | 4 | 14.68 | 66.776 | 66.776 | 248.3 | 0.000 | 0.000 | 4 | 14.10 |
| minilight | 2.576 | 0.771 | 560.0 | 2.576 | 0.041 | 0 | 19.08 | 0.467 | 0.207 | 367.1 | 0.467 | 0.085 | 0 | 19.30 |
| bdd | 2.216 | 1.036 | 253.9 | 2.216 | 0.015 | 0 | 36.13 | 0.413 | 0.165 | 153.9 | 0.413 | 0.008 | 0 | 35.72 |
| fft | 2.991 | 1.519 | 554.1 | 2.991 | 0.024 | 0 | 17.57 | 0.610 | 0.280 | 321.7 | 0.610 | 0.008 | 0 | 15.91 |

- **B's longest pause is shorter on every program,** from 1.3 times
  (livegraph at 1.25×) to 160 times (bt18).
  On binarytrees A's longest pause is an allocation that sweeps until it
  finds a fit: 92 ms on bt18. B's allocation sweeps at most a page of its
  class before it takes a fresh page, so its longest pause there is 0.56 ms.
- **markbench is dominated by its four full collections.** Each closes the
  open sweep in one go: 120 ms on A, 67 ms on B. Neither allocator bounds
  this pause.
- **The cost is memory:** B's incremental mode needs more heap on livegraph
  (section 4.1).

**Against the rule** (B's longest pause clearly shorter): met.

## 8. Against the decision rule

| Condition (section 6.3) | Result |
|---|---|
| 1. Every correctness check passes | Met, for every check that ran. The bt18 oracle checks were not run (section 2.1) |
| 2. B's sequential run time at most 5% above A's on every program | **Not met, narrowly:** bt16 is +5.2% against A as it stands (+3.8% against the hooked A). All other programs are within +2.6% of A or faster |
| 3. B's 4-thread sweep clearly faster than A's (≥ 1.3× on bt18 and livemap) | **Not met:** 2.38× on bt18, but 0.83× on livemap |
| 4. B's longest incremental pause clearly shorter | Met: 1.3 to 160 times shorter |
| Warning: smallest heap more than 10% above A's | **Present:** bt18 +11.7% and minilight +27.5%. B's incremental mode also needs 6% more heap on livegraph |

So by the note's rule, A stays. B's sequential sweep is 1.4 to 7 times faster
and its pauses are much shorter. But in this prototype those gains come with
slower minor collections and marking on binarytrees, more memory, and a
parallel sweep that hardly scales.

The note suggests what to measure next before deciding, without changing the
rule:
- tune the size classes to cut rounding, for example a class at 129;
- find the cause of B's slower mark on binarytrees and livemap;
- build the per-object intern change.

## 9. Two more page allocators: B2 and B3

After the measurement above, two variants of B were built and measured the
same way, alongside A and B.

### 9.1 What was built

Both are build-time variants of `proto/alloc_pages.c`
(`-DVERGC_B_VARIANT=2|3`), built by `tools/proto-build.sh B2|B3-8K|B3-16K|B3-32K`.

- **B2, OCaml 5 as it is:**
  - **Classes:** OCaml 5's 32 classes from `runtime/caml/sizeclasses.h`, for
    blocks of up to 128 words including the header. As in OCaml 5
    (`shared_heap.c`, `whsize <= SIZECLASS_MAX`), a block of 129 words or more
    is large.
  - **Pages:** 32 KB (OCaml 5's `POOL_WSIZE`, 4096 words). Each page starts
    with OCaml 5's 4-word pool header and the class's wastage, as a blue
    filler. As in B, the page's metadata itself is in a side page map.
  - **The large-object area:** large blocks are carved at their exact size
    from free blocks on one first-fit list, carved from the right. This is A's
    allocator for these sizes, since A keeps every free block of more than 16
    words on its list 0. The sweep merges neighbouring free blocks, as A's
    does, and a new run of pages joins a swept run next to it. A whole free
    page inside a run goes back to the free pages, which is what freeing a
    large block does in OCaml 5.
  - **One difference from OCaml 5:** OCaml 5 gives each large block its own
    `malloc`. Here, large blocks come from pages of the one tiled heap that
    the verified collector works on.
- **B3, tuned:** as B2, except for three things.
  - **Classes:** exact classes for 1 to 16 words, then classes about 12%
    apart: 18, 20, 22, 25, 28, 31, 35, 39, 44, 49, 55, 62, 69, 77, 86, 96, 108,
    121 and 128. There are 35 in all.
  - **Page choice:** each class allocates from its lowest-address page that
    has a free slot, found with one bitmap per class.
  - **Page size:** a build parameter (`PG_WORDS_CFG`), measured at 8, 16 and
    32 KB (`B3-8K`, `B3-16K`, `B3-32K`).
- **Unchanged from B:**
  - the three sweeps;
  - the incremental allocation's one-page sweep, as in OCaml 5's `pool_find`;
  - the collection trigger, scaled by the measured ratio of slot words to
    requested words, which is close to 1 for B2 and B3.

Two defects were found while measuring. Both were fixed, and every check was
rerun after the fixes.
- **A race in the parallel sweep (correctness).**
  - **The cause:** a thread found where its chunk started by skipping a
    large run's continuation pages. Meanwhile, another thread could split that
    run by returning whole pages. So a block could be swept twice, and a
    survivor freed.
  - **How it was found:** the oracle check reported "survivor counts differ"
    on `B3-16K` parallel, bdd.
  - **The fix:** all chunk bounds are now fixed before the threads start.
    B uses the same code, so B's parallel checks were rerun too.
- **A slow large-object list (speed only).**
  - **The cause:** the large list also held free pieces of under 128 words,
    such as the end of a page too short for another block. No request in
    the large-object area is that small, so each first-fit search walked past
    them.
  - **The effect:** `B3-8K` ran binarytrees 16 for over 10 minutes instead of
    15 s.
  - **The fix:** such pieces now stay blue blocks that are on no list, until
    the sweep merges them with their neighbours. Placement is unchanged,
    because an unlisted piece could never have been chosen.

### 9.2 Correctness

The checks were the same as in section 2, for `B2`, `B3-8K`, `B3-16K` and
`B3-32K` in all three sweep modes.

- **Oracle checks** (every sweep compared with the verified sweep, at every
  collection), with these heaps:
  - hamming, livemap, minilight, bdd and fft at their usual heap;
  - livegraph at its usual heap, or at 1.25× in incremental mode;
  - binarytrees 16 at 1.25×, except `B3-8K` at 1.5×, since it does not run at
    1.25× (section 9.3);
  - markbench at 0.25×.

  All 96 runs passed. So did B's 8 parallel runs, redone with the race fix.
- **`make test` and `make test-native`:** passed for each of the four
  variants in each mode, and for B's parallel mode after the fix.
- **Control mutants:**
  - B's mutant (the last slot of every page is never looked at) was run on
    livegraph for the four variants in the three modes, 12 runs. The check
    rejected every one.
  - A new mutant for the large-object area keeps the first block of every
    large run, even when it is dead (`VERGC_PROTO_CHECK_CONTROL=2`).
    **Correction (2026-11-08): this mutant never ran here.**
    `proto_common.c` read the variable as a boolean, so 2 became 1, and the
    4 runs reported here (binarytrees 16, sequential) ran the pool mutant
    instead.
    - With the parsing fixed, B2 on binarytrees 16 at 1.25× completes in all
      three modes and the check reports nothing.
    - That mutant never fires. B2 carves large blocks from the right, so a
      run's first block is its blue left-over piece (at least 97 words on
      binarytrees, whose large blocks are all 129 words), and the mutant
      only acts on a first block that is not blue.
    - **The mutant now keeps the run's first block that is not blue, even
      when it is dead,** and prints a line the first time it does.
      - It fired, and the check rejected it, on binarytrees 16 (1.25×),
        bdd and fft, in each of the three modes: 9 runs.
      - The kept blocks were 129, 16,385 and 524,289 words.
      - Sequential and parallel runs failed with "a block the verified
        sweep frees survives". Incremental runs failed with "a dead block is
        not covered by a blue block after its sweep".
      - On livemap, minilight and markbench (0.25×, sequential) it never
        fired: no large block died there. Those runs test nothing.
- **Not run:**
  - the binarytrees 18 oracle checks, as in section 2.1;
  - the OCaml testsuite, for B2 and B3.

### 9.3 Smallest heap

Sequential sweep, bisection to 2%, as in section 4. A is in words, the others
relative to A. Bold marks more than 10% above A.

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 4,489,216 | +1.4% | +1.4% | +1.4% | +1.4% | +2.7% |
| binarytrees 16 | 67,108,864 | +9.4% | 0 | **+30.9%** | 0 | 0 |
| binarytrees 18 | 269,484,032 | **+11.7%** | 0 | **+23.3%** | +1.5% | 0 |
| livemap | 16,502,784 | +7.8% | +7.8% | +6.7% | +6.7% | +7.8% |
| livegraph | 16,039,936 | 0 | 0 | 0 | 0 | +1.5% |
| markbench | 104,302,080 | 0 | 0 | 0 | 0 | 0 |
| minilight | 446,464 | **+27.5%** | **+27.5%** | **+13.8%** | **+13.8%** | **+27.5%** |
| bdd | 1,903,104 | +5.4% | +5.4% | +1.8% | +3.6% | +5.4% |
| fft | 15,373,056 | 0 | 0 | 0 | 0 | 0 |

The incremental sweep on livegraph needs 17,039,360 words (+6.2%) with every
B variant, as with B (section 4.1).

- **B2 removes B's cost on binarytrees.** Both binarytrees programs fit in
  A's heap. Their 129-word arrays now sit in the large-object area at their
  exact size, where B rounded them up to 141 words.
- **B2 does not help minilight** (+27.5%, as B), bdd or livemap. The cost
  there is pages that are only partly used (section 9.4), and B2 keeps B's
  32 KB pages.
- **B3's smaller pages help where pages are partly used:** minilight goes
  from +27.5% to +13.8%, and bdd from +5.4% to +1.8%.
- **`B3-8K` loses heavily on binarytrees** (+31% and +23%). The large-object
  area grows a page at a time. A page of 1024 words holds 7 of the 129-word
  arrays, and the 121 words left over are too few for another (section
  9.4). This comes from how the prototype grows its large-object area, not
  from small pages as such. It was not fixed.

### 9.4 Where the extra memory goes

The breakdown is taken at the collection with the most pages in use, right
after its sweep, at the heap used for timing (`VERGC_PROTO_MEM=1`, one run).
Each cell gives three numbers, as a percentage of that variant's live words
at that point:
- **rounding inside slots:** the words a live block's slot has beyond the
  block;
- **partly used pages:** the free slots in class pages, plus each page's
  header and tail fillers;
- **the large-object area:** its free words.

The "live" column is B2's live data. The other variants' points can fall at a
different collection: bdd's live data is 1.42M words for B and B2 and 1.20M
for B3.

| Program | live (M words) | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 3.21 | 0.0 / 12.9 / 0.1 | 0.0 / 12.9 / 0.1 | 0.0 / 11.4 / 0.0 | 0.0 / 11.9 / 0.0 | 0.0 / 13.3 / 0.1 |
| binarytrees 16 | 33.39 | 9.0 / 0.5 / 0.0 | 0.0 / 0.2 / 2.4 | 0.0 / 0.1 / 13.0 | 0.0 / 0.1 / 5.7 | 0.0 / 0.3 / 2.4 |
| binarytrees 18 | 136.44 | 9.0 / 0.3 / 0.0 | 0.0 / 0.1 / 2.4 | 0.0 / 0.0 / 13.0 | 0.0 / 0.0 / 5.7 | 0.0 / 0.1 / 2.4 |
| livemap | 12.74 | 0.0 / 53.7 / 0.0 | 0.0 / 53.7 / 0.0 | 0.0 / 50.8 / 0.0 | 0.0 / 52.0 / 0.0 | 0.0 / 53.8 / 0.0 |
| livegraph | 11.61 | 0.0 / 40.1 / 0.0 | 0.0 / 40.2 / 0.0 | 0.0 / 40.1 / 0.0 | 0.0 / 40.2 / 0.0 | 0.0 / 40.4 / 0.0 |
| markbench | 102.11 | 0.0 / 0.1 / 1.0 | 0.0 / 0.3 / 0.0 | 0.0 / 0.8 / 0.0 | 0.0 / 0.3 / 0.0 | 0.0 / 0.3 / 0.0 |
| minilight | 0.43 | 1.5 / 19.8 / 0.9 | 1.4 / 19.0 / 0.8 | 0.0 / 6.9 / 0.1 | 0.0 / 11.4 / 0.4 | 0.0 / 20.4 / 0.8 |
| bdd | 1.42 | 0.0 / 6.2 / 1.0 | 0.0 / 6.0 / 0.4 | 0.0 / 2.2 / 0.2 | 0.0 / 4.2 / 0.3 | 0.0 / 8.3 / 0.5 |
| fft | 14.69 | 0.0 / 5.7 / 0.1 | 0.0 / 5.5 / 0.1 | 0.0 / 4.9 / 0.0 | 0.0 / 4.9 / 0.1 | 0.0 / 4.8 / 0.1 |

- **Rounding matters only in B, on binarytrees:** 9% of live words, from the
  129-word arrays in 141-word slots. With B2's classes the arrays are large,
  and with B3's exact small classes nothing else rounds. Rounding is 1.4% on
  minilight with B and B2, and none with B3.
- **Partly used pages are where most of the space goes**, for every variant:
  - **livemap and livegraph, 40 to 54%:** most of this is garbage the sweep
    has just freed, which A also has at that point as free blocks. A can give
    a free block to a request of any size, and merges it with its
    neighbours. A free slot can only take a block of its class. That is the
    7.8% more heap on livemap.
  - **minilight:** the live data is small (0.43M words) and spread over many
    classes, so each class's last page is mostly empty. Smaller pages cut
    this from 20% at 32 KB to 11% at 16 KB and 7% at 8 KB. This is the
    smallest heap's 27.5% falling to 13.8%.
- **The large-object area costs B2, and B3 at 32 KB, 2.4% on binarytrees.**
  The cost rises as the page shrinks: 5.7% at 16 KB and 13% at 8 KB. Each is
  the space a page leaves over after whole 129-word arrays: 97 words of
  4096, 113 of 2048 and 121 of 1024. Elsewhere the area costs at most 1%.

### 9.5 Why B's mark was about 80% slower on binarytrees, and B2

binarytrees allocates, for each tree node, a 129-word array whose 128 fields
all point to the same `Some 0` block. The mark reads every one of those
arrays. Where the arrays live decides the mark's speed. How they are rounded
does not.

- **B-129**, a diagnostic build of B whose class 141 becomes 129, removes
  the rounding. Its live words per 4 KB page match B2's (500), and its
  pointer-distance distribution is the same, yet it marks as slowly as B.
- **B2 and B3 put the arrays in the large-object area,** and their mark is as
  fast as A's, or faster (section 9.7).

Median mark per collection on binarytrees 16, in ms. Single runs from three
probes, all taken while check runs loaded the machine:

| Probe | A | B | B-129 | B2 |
|---|---|---|---|---|
| memory probe 1 | 32.0 | 47.3 | 50.8 | 30.2 |
| memory probe 2 (`mem4`) | 50.2 | 67.2 | 85.9 | 48.0 |
| mark-order replay (`dfs4`) | 47.1 | 58.2 | 54.0 | 26.3 |

So the cause is placing the arrays in class pages, and B2 fixes it. The exact
mechanism was not found. Two locality measures came out the same for B-129
and B2, so they do not explain the difference:
- **the distance of each pointer from its block:** about 25% within 256 KB
  for B, B-129 and B2, against 36% for A;
- **a replay of the order in which the mark reads blocks,** a depth-first
  walk of the black blocks after the mark: 94.9% of visits jump 4 KB or more
  for both, and 14.7% miss a 256-entry model of the data TLB.

No further diagnostics were built. The replay is in `proto_common.c` and runs
only with `VERGC_PROTO_MEM`.

### 9.6 Timing method, and how much to trust it

**Most numbers below are the mean of 2 runs, not the median of 3.** The
campaign was stopped after its second round. A third run was then added for
`base`, A, B2 and `B3-16K` only (marked §, see below). Otherwise the method
is section 3's, with these differences:
- **Configurations:** 31, each run interleaved within a round:
  - `base`;
  - for each of A, B, B2, `B3-8K`, `B3-16K` and `B3-32K`: `seq`, `par` at 1,
    2 and 4 threads, and `incremental`.
- **Heaps:** each program at its usual heap, and binarytrees 16 at 1.25×,
  as in sections 5 to 7. Two extra sets:
  - binarytrees 16 at 1.5× for every configuration, because `B3-8K` does not
    fit at 1.25×;
  - livegraph at 1.25× for the incremental configurations, because no B
    variant fits livegraph's usual heap in incremental mode.
- **The wait for a quiet machine:** each run waits, for up to 2 minutes, for
  the 1-minute load average to fall below 3 instead of 2.
  - **Why:** a video wallpaper extension and the window server kept the load
    near 2.5. At a limit of 2, every run waited the full 2 minutes, which made
    a round about 12 hours long.
  - **The first start was discarded:** it had run 68 runs with the old limit.
    Its runs were removed, and the campaign was restarted with the new
    limit.
  - **Setting it:** `VERGC_BENCH_LOAD` in `tools/proto-bench.py`.
- **Raw data:** tags `final3`, `final3-bt15` and `final3-lg125` in
  `runs.jsonl`. The tables come from `tools/proto-bench.py table TAG A B B2
  B3-8K B3-16K B3-32K`. With 2 runs, the script's median is their mean.

**The noise is large, so treat a difference of under about 10% on one
program as unresolved.**
- **Round 1 had long disturbed stretches.** For the same configuration,
  runs there were 10 to 50% slower than in round 2: on livemap, minilight,
  bdd and the binarytrees 16 1.5× set. One bdd run was 4 times slower:
  `B2:seq`, 128 s against 36 s.
- **Round 2 was quiet, except on bdd.** Even there, `base` took 9.2 and
  11.0 s on livemap in its two runs, and 45.2 and 30.7 s on bdd.
- **Steady across both rounds:** the mark and sweep medians on binarytrees,
  and the binarytrees 16 run times at 1.25×.

**A third run, for `base`, A, B2 and `B3-16K`.** After the two rounds, these
four were run once more, on a quieter machine: each run waited for a load
below 2, and the runs started at loads of 1.5 to 2.2.
- **What was rerun:**
  - every configuration of the four whose two runs differed by more than
    20%, on any number in the tables (44 configurations);
  - every sequential run time of the four (`base` and `seq`) not already
    covered, so that condition 2 rests on medians of 3 throughout.
- **Those cells are the median of 3 and are marked §.** In the run-time
  table, a § after the program's name means `base` is a median of 3 there.
  That is the case on every program, so the B, `B3-8K` and `B3-32K`
  columns, still means of 2, are compared with `base`'s median of 3.
- **† marks a remaining pair** that differs by more than 20%, in B, `B3-8K`
  or `B3-32K` only.
- **Two programs were then settled with 5 more interleaved rounds** (tag
  `settle3`), because their medians of 3 still did not decide condition 2:
  bdd and binarytrees 16 at 1.5×. Section 9.7 gives the results.
- **The machine's speed changed between sessions.** In the `settle3`
  rounds, every build ran bdd in about 44 s and binarytrees 16 at 1.5× in
  about 15 s, against about 31 s and 11 to 13 s earlier. Each round runs
  the four builds back to back, so the comparison within a round still
  holds.
- **Raw data:** the third runs carry the same tags as the first two. The
  tables come from `logs/sec9tables.py` under `_build/proto-results`, and
  the cells that were rerun are listed in `logs/rerun3-cells.json`.

### 9.7 Sequential sweep: run time and collection time

The columns are the hooked builds' `seq` configurations. A is `A:seq`.

**Run time, s (vs `base`)**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming § | 0.32 (+2.0%) § | 0.26 (-17.4%) | 0.27 (-11.6%) § | 0.26 (-14.7%) | 0.26 (-15.5%) § | 0.26 (-15.9%) |
| binarytrees 16 (1.25×) § | 13.89 (+1.6%) § | 14.19 (+3.8%) | 12.99 (-5.0%) § | fail | 13.07 (-4.4%) § | 12.89 (-5.7%) |
| binarytrees 16 (1.5×) § | 11.89 (+3.8%) § | 12.73 (+11.1%) | 10.83 (-5.5%) § | 12.26 (+7.0%) | 12.95 (+13.0%) § | 11.64 (+1.6%) |
| binarytrees 18 § | 59.21 (+0.2%) § | 66.43 (+12.5%) | 57.28 (-3.0%) § | 62.85 (+6.4%) | 57.34 (-2.9%) § | 66.41 (+12.4%) |
| livemap § | 7.89 (-14.7%) § | 8.10 (-12.3%) | 7.68 (-16.9%) § | 7.85 (-15.0%) | 7.97 (-13.8%) § | 9.06 (-2.0%) † |
| livegraph § | 4.73 (-1.7%) § | 4.44 (-7.6%) | 4.59 (-4.7%) § | 4.46 (-7.3%) | 4.57 (-5.0%) § | 4.50 (-6.4%) |
| markbench § | 14.34 (-0.3%) § | 12.94 (-10.0%) | 13.68 (-4.8%) § | 13.79 (-4.0%) | 13.92 (-3.2%) § | 13.04 (-9.3%) |
| minilight § | 16.27 (-11.0%) § | 17.21 (-5.8%) | 16.42 (-10.2%) § | 17.28 (-5.5%) | 16.40 (-10.3%) § | 20.39 (+11.5%) † |
| bdd § | 31.26 (-1.8%) § | 33.87 (+6.4%) | 35.98 (+13.0%) § | 33.63 (+5.6%) † | 34.76 (+9.1%) § | 31.98 (+0.4%) |
| fft § | 14.88 (-8.5%) § | 13.68 (-15.9%) † | 13.56 (-16.6%) § | 13.86 (-14.8%) | 13.74 (-15.5%) § | 13.65 (-16.1%) |

**Run time on the two unsettled programs, 5 more interleaved rounds
(`settle3`): median of 5, s, and the median over the rounds of each round's
ratio to `base` and to `A:seq`**

| Program | `base` | A | B2 | `B3-16K` |
|---|---|---|---|---|
| bdd | 44.89 | 43.87 (−2.5%) | 44.61 (−0.8%; A +2.0%) | 43.48 (−3.9%; A −1.2%) |
| binarytrees 16 (1.5×) | 15.11 | 15.23 (+1.0%) | 14.48 (−4.0%; A −5.0%) | 14.77 (−2.0%; A −3.0%) |

In all 10 rounds, every run was within 5% of its round's `base` run, except
one `B3-16K` bdd run of 46.2 s (+29%), which started at a load of 2.5.

**Collection time, s**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 0.19 § | 0.13 | 0.14 § | 0.14 | 0.14 § | 0.14 |
| binarytrees 16 (1.25×) | 11.82 § | 12.37 | 11.13 § | fail | 11.24 § | 11.10 |
| binarytrees 16 (1.5×) | 10.08 § | 11.07 | 9.26 § | 10.60 | 11.10 § | 10.01 |
| binarytrees 18 | 49.81 § | 57.08 | 48.79 § | 54.01 | 48.86 § | 56.77 |
| livemap | 3.37 § | 3.15 | 2.91 § | 3.17 | 3.16 § | 3.60 |
| livegraph | 1.36 § | 1.15 | 1.17 § | 1.15 | 1.18 § | 1.14 |
| markbench | 13.82 § | 12.46 | 13.22 § | 13.31 | 13.41 § | 12.58 |
| minilight | 5.58 § | 6.02 | 5.73 § | 6.14 | 5.75 § | 6.81 |
| bdd | 4.06 § | 4.26 | 4.80 § | 4.37 | 4.57 § | 4.00 |
| fft | 7.92 § | 6.84 | 6.84 § | 7.06 | 7.06 § | 6.85 |

**Major collections**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 1 § | 1 | 1 § | 1 | 1 § | 1 |
| binarytrees 16 (1.25×) | 47 § | 51 | 47 § | fail | 47 § | 47 |
| binarytrees 16 (1.5×) | 39 § | 42 | 39 § | 39 | 39 § | 39 |
| binarytrees 18 | 33 § | 36 | 33 § | 33 | 33 § | 33 |
| livemap | 14 § | 14 | 14 § | 14 | 14 § | 14 |
| livegraph | 4 § | 4 | 4 § | 4 | 4 § | 4 |
| markbench | 5 § | 5 | 5 § | 5 | 5 § | 5 |
| minilight | 987 § | 1,110 | 1,110 § | 1,110 | 1,110 § | 1,110 |
| bdd | 320 § | 329 | 329 § | 322 | 322 § | 322 |
| fft | 33 § | 33 | 33 § | 33 | 33 § | 33 |

**Mark, ms: median per collection**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 20.52 § | 17.55 | 18.03 § | 17.98 | 18.26 § | 17.68 |
| binarytrees 16 (1.25×) | 23.20 § | 38.08 | 22.23 § | fail | 22.90 § | 22.77 |
| binarytrees 16 (1.5×) | 21.79 § | 36.87 | 20.96 § | 22.83 | 22.95 § | 21.43 |
| binarytrees 18 | 92.05 § | 169.32 | 90.47 § | 102.49 | 92.84 § | 104.00 |
| livemap | 36.42 § | 64.57 | 63.53 § | 65.35 | 65.63 § | 67.96 |
| livegraph | 216.74 § | 205.58 | 207.35 § | 204.53 | 210.40 § | 202.36 |
| markbench | 2,353.82 § | 2,173.31 | 2,294.79 § | 2,250.28 | 2,316.29 § | 2,187.37 |
| minilight | 0.92 § | 1.00 | 1.01 § | 1.01 | 1.01 § | 1.17 |
| bdd | 2.88 § | 2.66 | 2.83 § | 3.10 | 2.89 § | 3.11 |
| fft | 14.70 § | 15.21 | 15.21 § | 14.53 | 14.84 § | 14.69 |

**Sweep, ms: median per collection**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 4.023 § | 2.499 | 2.319 § | 2.867 | 2.568 § | 2.966 |
| binarytrees 16 (1.25×) | 23.261 § | 3.582 | 18.445 § | fail | 19.524 § | 18.697 |
| binarytrees 16 (1.5×) | 26.179 § | 3.837 | 20.393 § | 22.933 | 21.152 § | 19.752 |
| binarytrees 18 | 128.222 § | 25.065 | 111.680 § | 125.113 | 111.773 § | 111.944 |
| livemap | 15.371 § | 11.056 | 9.933 § | 10.875 | 11.140 § | 12.590 |
| livegraph | 19.972 § | 16.064 | 15.094 § | 14.595 | 15.239 § | 14.512 |
| markbench | 109.813 § | 56.438 | 60.946 § | 58.751 | 61.015 § | 56.320 |
| minilight | 0.404 § | 0.227 | 0.228 § | 0.216 | 0.217 § | 0.252 |
| bdd | 0.592 § | 0.296 | 0.318 § | 0.310 | 0.297 § | 0.346 |
| fft | 13.547 § | 7.355 | 7.224 § | 7.357 | 7.380 § | 7.067 |


- **B2 and `B3-16K` are within 5% of A on every program.** This settles
  condition 2 for them:
  - **Their worst case against `base`** (A as it stands) is −0.8% for B2 on
    bdd, and −2.0% for `B3-16K` on binarytrees 16 at 1.5×. That is the median of 3
    on eight programs, and the `settle3` rounds on bdd and on binarytrees 16
    at 1.5×.
  - **Their worst case against the hooked `A:seq`** is +2.0%, for B2 on bdd
    (`settle3`). Next are +1.0% for `B3-16K` on livemap and +0.9% for both
    on minilight (16.42 and 16.40 s, against 16.27).
  - **The earlier readings were noise:**
    - **minilight:** `B3-16K`'s +14.9% came from one 23.4 s run.
    - **bdd:** B2's +116% came from one 128 s run, and the medians of 3
      (+13.0% and +9.1%) mix runs from different rounds, on a program
      where `base` itself took 30.7 to 45.2 s.
    - **binarytrees 16 at 1.5×:** `B3-16K`'s +13.0% came from the machine
      flipping between about 11 and 13 s for every build.

    Within the interleaved `settle3` rounds, none of these appears.
- **Binarytrees, B2 and B3 against B:**
  - **Run time:** at 1.25×, B2, `B3-16K` and `B3-32K` take 4 to 6% less time
    than `base`. B takes 4% more.
  - **Mark:** 22 to 23 ms per collection on binarytrees 16, the same as A's
    23 ms. B's is 38 ms.
  - **Majors:** B2 and B3 make as many major collections as A: 47 on
    binarytrees 16, 33 on binarytrees 18.
- **binarytrees 18:**
  - **B2 and `B3-16K`:** −3.0% and −2.9% against `base`, on the median of
    3. B2's third run took 47.8 s. The incremental reruns made at about the
    same time also ran binarytrees 18 in about 49 s, so the machine was
    faster then. The median does not use that run.
  - **`B3-32K`:** about 12% slower than `base` in both its runs (65.7 and
    67.1 s, against 59.3, 59.1 and 58.1 s). Its mark (104 ms) and its
    collection time are higher than B2's. This difference from B2 was not
    investigated.
- **B2 and B3 lose most of B's sweep speed on binarytrees.** Each 129-word
  array is now a block in the large-object area, so the sweep reads every
  array's header and merges free runs, as A does. That takes 18.4 to 19.5 ms
  on binarytrees 16, against B's 3.6 and A's 23.3. On the other programs,
  the variants' sweeps are as fast as B's.
- **Still unsettled, for the variants that were not rerun:** `B3-32K` on
  minilight (+11.5%, †) and `B3-8K` on bdd (+5.6%, †).
- **Elsewhere,** every B variant is as fast as `base` or faster, as B was in
  section 5.
- **B's slower mark on livemap remains** with B2 and B3: 64 to 68 ms,
  against A's 36. livemap has no large objects, so moving large objects does
  not change it.

### 9.8 Parallel sweep

**Parallel sweep, 1 thread, ms: median per collection**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 4.710 | 2.303 | 2.373 | 2.452 | 2.651 | 2.282 |
| binarytrees 16 (1.25×) | 24.443 | 3.354 | 18.317 | fail | 19.204 | 18.968 |
| binarytrees 16 (1.5×) | 25.614 | 3.623 | 19.730 | 22.752 | 21.050 | 19.937 |
| binarytrees 18 | 131.051 | 25.537 | 113.243 | 126.720 | 112.400 | 127.029 |
| livemap | 16.601 § | 11.162 | 10.675 § | 11.966 | 10.802 | 11.267 |
| livegraph | 22.434 § | 14.142 | 14.776 | 15.530 | 14.335 | 15.242 |
| markbench | 99.490 | 55.813 | 56.193 | 57.870 | 56.287 | 56.112 |
| minilight | 0.445 | 0.222 | 0.228 | 0.216 | 0.227 | 0.238 |
| bdd | 0.679 | 0.322 | 0.306 | 0.299 | 0.296 | 0.346 |
| fft | 14.083 | 7.028 | 7.037 | 7.515 | 7.459 | 7.383 |

**Parallel sweep, 2 threads, ms: median per collection**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 2.931 § | 1.651 | 1.853 | 2.194 | 1.482 § | 1.579 |
| binarytrees 16 (1.25×) | 13.021 | 2.774 | 9.389 | fail | 10.418 | 10.278 |
| binarytrees 16 (1.5×) | 12.622 | 3.231 | 10.021 | 12.011 | 10.386 | 10.239 |
| binarytrees 18 | 72.191 | 19.474 | 56.207 | 64.871 | 59.412 | 53.459 |
| livemap | 9.052 § | 6.943 | 6.494 | 7.688 | 6.441 | 6.838 |
| livegraph | 10.339 § | 7.919 | 7.813 | 8.787 | 7.838 | 8.024 |
| markbench | 55.504 | 39.429 | 35.737 § | 39.636 | 35.629 § | 40.345 |
| minilight | 0.382 | 0.197 | 0.195 | 0.199 | 0.195 | 0.199 |
| bdd | 0.659 | 0.261 | 0.258 | 0.253 | 0.256 | 0.270 |
| fft | 7.839 | 4.737 | 4.747 | 4.758 | 4.796 | 4.793 |

**Parallel sweep, 4 threads, ms: median per collection**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 1.585 | 1.831 | 1.620 | 1.534 | 1.505 | 1.647 |
| binarytrees 16 (1.25×) | 7.744 | 2.700 | 5.316 | fail | 5.607 | 5.512 |
| binarytrees 16 (1.5×) | 7.919 | 2.844 | 5.557 | 6.456 | 5.874 | 5.591 |
| binarytrees 18 | 43.787 | 18.965 | 30.336 | 36.317 | 32.008 | 28.361 |
| livemap | 6.209 | 5.860 | 6.140 | 6.104 | 6.164 | 6.251 |
| livegraph | 5.972 § | 5.713 | 5.288 § | 5.696 | 5.594 | 5.758 |
| markbench | 36.377 § | 40.178 | 34.993 § | 41.340 | 35.068 § | 40.166 |
| minilight | 0.292 § | 0.191 | 0.202 § | 0.186 | 0.190 | 0.194 |
| bdd | 0.440 | 0.239 | 0.229 | 0.228 | 0.234 | 0.233 |
| fft | 4.783 | 4.361 | 4.521 | 4.517 | 4.392 | 4.457 |

**Parallel speedup at 4 threads (own sequential sweep / 4 threads)**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 2.54× | 1.36× | 1.43× | 1.87× | 1.71× | 1.80× |
| binarytrees 16 (1.25×) | 3.00× | 1.33× | 3.47× | fail | 3.48× | 3.39× |
| binarytrees 16 (1.5×) | 3.31× | 1.35× | 3.67× | 3.55× | 3.60× | 3.53× |
| binarytrees 18 | 2.93× | 1.32× | 3.68× | 3.44× | 3.49× | 3.95× |
| livemap | 2.48× | 1.89× | 1.62× | 1.78× | 1.81× | 2.01× |
| livegraph | 3.34× | 2.81× | 2.85× | 2.56× | 2.72× | 2.52× |
| markbench | 3.02× | 1.40× | 1.74× | 1.42× | 1.74× | 1.40× |
| minilight | 1.38× | 1.19× | 1.13× | 1.16× | 1.15× | 1.30× |
| bdd | 1.35× | 1.24× | 1.39× | 1.36× | 1.27× | 1.48× |
| fft | 2.83× | 1.69× | 1.60× | 1.63× | 1.68× | 1.59× |


- **On binarytrees, B2 and B3 scale like A,** 3.4 to 4.0 times at 4 threads.
  Their sweep there is mostly the large-object area's runs. B, which sweeps
  only class pages there, scales 1.3 times.
- **At 4 threads, A's sweep on binarytrees 18 is 1.21 to 1.54 times slower
  than the variants'.** That is less than B's 2.31, because the variants'
  sequential sweep there is slower.
- **On livemap, every variant is level with A at 4 threads:** 0.99 to 1.06,
  and 0.96 to 1.06 in round 2. Section 6 found 0.83 for B, so this ratio
  moves by about 20% between campaigns. The 4-thread cells on binarytrees 18
  and livemap were not rerun, because their two runs agreed within 20%.

### 9.9 Incremental sweep: pauses

As in section 7. livegraph at its usual heap fails for every B variant, so it
also has a row at 1.25×.

**Incremental, longest pause, ms**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 0.476 | 0.246 | 0.325 | 0.323 | 0.204 § | 0.276 |
| binarytrees 16 (1.25×) | 16.227 | 0.617 | 0.787 | fail | 0.800 § | 0.909 |
| binarytrees 16 (1.5×) | 15.196 § | 0.469 | 0.669 | 0.769 | 0.726 | 0.770 |
| binarytrees 18 | 100.495 § | 0.975 | 1.048 § | 0.909 | 6.573 § | 1.675 |
| livemap | 2.059 | 1.464 | 1.085 § | 1.188 | 0.973 § | 1.055 |
| livegraph (1×) | 2.926 § | fail | fail | fail | fail | fail |
| livegraph (1.25×) | 2.431 | 1.545 | 1.841 | 1.868 | 1.699 § | 1.740 |
| markbench | 108.543 | 60.337 | 58.518 | 64.830 | 59.097 | 58.254 |
| minilight | 1.136 § | 0.254 | 0.228 § | 0.374 | 0.502 § | 0.327 |
| bdd | 1.315 | 1.489 | 0.195 § | 0.230 | 0.291 § | 0.203 |
| fft | 1.615 § | 0.445 | 0.451 | 0.534 | 0.483 | 0.566 |

**Incremental, 99th percentile pause, ms**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 0.476 | 0.246 | 0.325 | 0.323 | 0.204 § | 0.276 |
| binarytrees 16 (1.25×) | 1.020 | 0.193 | 0.516 | fail | 0.534 § | 0.526 |
| binarytrees 16 (1.5×) | 0.880 § | 0.162 | 0.453 | 0.512 | 0.480 | 0.456 |
| binarytrees 18 | 0.995 § | 0.189 | 0.500 § | 0.522 | 0.495 § | 0.568 |
| livemap | 1.829 | 1.200 | 0.994 § | 1.095 | 0.923 § | 0.902 |
| livegraph (1×) | 2.425 § | fail | fail | fail | fail | fail |
| livegraph (1.25×) | 2.287 | 1.443 | 1.462 | 1.633 | 1.432 § | 1.552 |
| markbench | 108.543 | 60.337 | 58.518 | 64.830 | 59.097 | 58.254 |
| minilight | 0.543 § | 0.137 | 0.127 § | 0.153 | 0.115 § | 0.140 |
| bdd | 0.895 | 0.485 | 0.112 § | 0.115 | 0.099 § | 0.088 |
| fft | 1.317 § | 0.161 | 0.151 | 0.190 | 0.157 | 0.158 |

**Incremental, total pause, ms**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 0.6 | 2.3 | 2.3 | 2.6 | 2.2 § | 2.2 |
| binarytrees 16 (1.25×) | 1,215.5 | 297.6 | 880.7 | fail | 928.2 § | 881.2 |
| binarytrees 16 (1.5×) | 1,054.0 § | 256.0 | 781.0 | 921.5 | 819.9 | 779.4 |
| binarytrees 18 | 5,104.8 § | 1,265.8 | 3,516.5 § | 4,216.0 | 3,912.2 § | 3,691.5 |
| livemap | 222.2 | 169.9 | 141.6 § | 169.7 | 147.1 § | 138.6 |
| livegraph (1×) | 68.5 § | fail | fail | fail | fail | fail |
| livegraph (1.25×) | 50.4 | 34.3 | 34.7 | 39.1 | 34.3 § | 36.1 |
| markbench | 416.2 | 231.2 | 228.6 | 236.8 | 227.9 | 222.8 |
| minilight | 467.3 § | 315.0 | 292.9 § | 362.2 | 298.5 § | 319.4 |
| bdd | 225.0 | 257.8 | 130.9 § | 147.3 | 132.3 § | 132.1 |
| fft | 493.5 § | 271.5 | 266.6 | 323.5 | 285.7 | 272.0 |

**Incremental, run time, s**

| Program | A | B | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|---|---|
| hamming | 0.30 | 0.25 | 0.25 | 0.26 | 0.26 § | 0.26 |
| binarytrees 16 (1.25×) | 13.89 | 14.34 | 12.90 | fail | 13.14 § | 13.06 |
| binarytrees 16 (1.5×) | 11.69 § | 12.88 | 11.77 | 12.28 | 11.96 | 11.77 |
| binarytrees 18 | 60.45 § | 65.89 | 55.61 § | 59.00 | 61.45 § | 59.93 |
| livemap | 8.61 | 9.39 | 7.93 § | 8.22 | 8.10 § | 7.72 |
| livegraph (1×) | 5.00 § | fail | fail | fail | fail | fail |
| livegraph (1.25×) | 4.40 | 4.23 | 4.22 | 4.28 | 4.03 § | 4.19 |
| markbench | 13.36 | 13.25 | 13.19 | 13.44 | 13.10 | 12.92 |
| minilight | 15.83 § | 17.33 | 16.50 § | 17.67 | 15.66 § | 17.39 |
| bdd | 32.47 | 90.84 | 31.67 § | 30.95 | 29.97 § | 32.51 |
| fft | 15.13 § | 12.97 | 13.24 | 13.94 | 13.40 | 13.63 |


- **Every variant's longest pause is shorter than A's, on every program,**
  except for B on bdd: 2.73 ms and 0.25 ms in its two runs, against A's
  1.3.
  - **B2's minilight outlier did not recur.** Its runs took 6.07, 0.23 and
    0.21 ms, so the median is 0.23 ms, against A's 1.1.
- **The binarytrees pauses stay under 2 ms** for every variant, against
  A's 15 to 100 ms.
  - The one exception is `B3-16K` on binarytrees 18: 6.6, 8.9 and 1.0 ms in
    its three runs, a median of 6.6 ms.
  - The variants' total pause there is about three times B's, because the
    sweep now walks the large-object area block by block.
- **markbench is again bounded by its four full collections:** 58 to 65 ms
  for the variants, against A's 109.

### 9.10 Against the decision rule

The same rule as section 8 (section 6.3 of the note). For B2 and `B3-16K`,
condition 2 rests on medians of 3, and on the 5 `settle3` rounds for bdd and
binarytrees 16 at 1.5×. Everything else is the mean of 2 runs, with round 2
alone in brackets where the two disagree.

| Condition | B2 | `B3-8K` | `B3-16K` | `B3-32K` |
|---|---|---|---|---|
| 1. Correctness checks pass | Met | Met | Met | Met |
| 2. Run time at most 5% above `base` on every program | **Met:** at most −0.8% (bdd); at most +2.0% against `A:seq` | **Not met:** binarytrees 16 does not fit at 1.25×; bt18 +6.4% (−0.4%); bt16 at 1.5× +7.0% (−0.8%) | **Met:** at most −2.0% (bt16 at 1.5×); at most +1.0% against `A:seq` | **Not met:** bt18 +12.4%, in both runs; minilight +11.5% (+7.6%) |
| 3. 4-thread sweep ≥ 1.3× A's on bt18 and livemap | **Not met:** bt18 1.44×, livemap 1.01× | **Not met:** 1.21×, 1.02× | **Not met:** 1.37×, 1.01× | **Not met:** 1.54×, 0.99× |
| 4. Longest incremental pause clearly shorter | Met | Met | Met | Met |
| Warning: smallest heap > 10% above A's | minilight +27.5% | bt16 +31%, bt18 +23%, minilight +13.8% | minilight +13.8% | minilight +27.5% |

**No variant meets the rule, so A stays.**
- **B2 and `B3-16K` fail only condition 3,** the parallel sweep on livemap.
  They meet conditions 1, 2 and 4, so their run time is within 5% of A's on
  every program.
- **What B2 fixes.** B2, OCaml 5 as it is, removes B's problems on
  binarytrees: the 9% rounding, the extra heap, the slower mark and the
  extra collections.
- **What B2 does not fix:**
  - **The parallel sweep on livemap** (condition 3) is no faster than A's,
    for any variant.
  - **minilight still needs 27.5% more heap** than A. Its live data is small
    and spread across many classes, which leaves most class pages partly
    used.
- **What B3's smaller pages do:**
  - **They help minilight and bdd:** at 8 and 16 KB, minilight needs 13.8%
    more heap than A.
  - **At 8 KB they cost binarytrees heavily,** through the prototype's
    one-page large-object runs.
- **The best compromise measured is `B3-16K`.** It fails condition 3 on
  livemap and leaves the minilight warning (+13.8% heap, against B2's
  +27.5%).
