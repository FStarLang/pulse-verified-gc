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
