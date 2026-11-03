# Parallel mark, prototype 2: established designs

Branch `sheera/parallel-mark-proto2` (from `sheera/parallel-mark-proto`, with
`origin/main` merged for PR #40's rescan skip). An **unverified** C prototype,
for measurement only. It marks the verified GC's heap in parallel the way
established collectors do, so that it can be compared with the sequential
verified mark and with our ownership design (prototype 1, `par_mark.c`).

**Status: partial measurement.** The checks are complete (§3). The timing ran
on binarytrees 16 (3 runs per configuration, plus profiles) and binarytrees 18
(2 runs) before the machine kept going to sleep. It was on battery, with Low
Power Mode on, so the CPU was throttled. livemap, livegraph and the four
Sandmark programs are not timed yet; §6 gives the command. All numbers below
were taken under the same throttled conditions. Comparisons between variants
should hold, but absolute times will be lower, and the speed-ups may differ,
on mains power.

## 1. Summary

- **Fastest: AS** (header CAS, Chase-Lev work stealing). At 4 threads its mark
  is **2.7× faster than the sequential mark on binarytrees 16 (11.0 ms against
  30.0 ms per collection) and 2.85× faster on binarytrees 18 (35.8 against
  102.3 ms)**. At 8 threads (4 cores, hyper-threaded) it reaches 3.5×.
- **Against O**, the tuned ownership variant: O is slower than the sequential
  mark at every thread count, 0.36× at 4 threads. AS is about 7× faster than O
  at 4 threads (6.8–7.6×), and 15–18× faster at 8. O's workers are idle 44–66% of the time.
  The address range that owns most of the live tree does most of the work,
  and the others wait on messages.
- **The cost of B against A (verifiability)**: with the bitmap, the mark is
  about **15–17% slower** at equal load balancing and thread count. Mark
  ratios B/A on binarytrees 18: 1.16–1.18 for P and 1.13–1.17 for S at k = 1–4,
  and 1.25–1.33 at k = 8. On binarytrees 16 they range from 0.97 to 1.36, and
  that benchmark's noise (§4) is of the same size. For a whole collection on
  binarytrees 18 the cost is **1–9%**, because the sweep, which B does from the bitmap, costs the
  same as the verified sweep (ratio 0.97–1.02) and dominates. So BS at 4 threads
  marks binarytrees 18 2.4× faster than the sequential mark, against AS's 2.85×.
- **Work stealing beats packets**, for A and for B, at every thread count. At
  k = 1 the packet variants are the slowest new ones (0.5–0.6× the sequential
  mark).
- **Where the time goes**: the new variants spend 91–100% of worker time
  scanning. Idle, steal and packet-pool time are each under 5%, even at 8
  threads. CAS failures are 0–4 per million claims (B: almost all from a
  neighbouring bit in the same 32-bit word). The limit is the scan itself:
  memory bandwidth, and from 4 to 8 threads hyper-threads sharing cores. With
  one thread every new variant is slower than the sequential mark (0.5–0.8×).
  That is the cost of range entries and the deque or packet operations against
  the verified mark's tight gray-stack loop.
- **Whole collections** gain less: at most 1.6×. The sweep is sequential and
  takes 23 of 72 ms (binarytrees 16) and 141 of 244 ms (binarytrees 18) per
  collection. A parallel sweep (`sheera/parallel-sweep`) is the next bottleneck.

## 2. The prototype

`generational/ocaml-integration/verified_gc/par_mark2.c` (new). Selected with
`VGC_PAR_MARK=k VGC_PAR_VARIANT=AP|AS|BP|BS`; with `VGC_PAR_VARIANT` unset,
`VGC_PAR_MARK` runs `par_mark.c` as before (O), and with neither set,
`gen_gc` runs unchanged.

- **Marking as in OCaml 5** (Sivaramakrishnan et al., ICFP 2020;
  `runtime/major_gc.c`). There is no grey colour: an object is grey by being on
  a mark stack. A mark stack entry is a field range, packed into one word (first
  field's address in the low 48 bits, length in the high 16). That makes a
  Chase-Lev slot one atomic word. OCaml 5's `(start, end)` is the same range,
  and the object itself is not needed. An object is claimed, then pushed as one
  range. When a range of more than CHUNK fields (default 256) is popped, the
  rest is pushed back before scanning, so other workers can take a large
  object's fields. This matters on binarytrees 16, where entries average 65
  fields. Claims are exclusive (CAS), so marking is never repeated; the
  idempotence the design allows is not needed.
- **Claiming.** A: one 64-bit CAS on the header, white to black. B: a side bitmap,
  one bit per heap word, set with a 32-bit CAS loop; the mark never writes a
  header. B tests the bit at `v − 8` before reading the header. Only object
  headers' bits are ever set, so a set bit means marked, and an infix pointer
  (whose `v − 8` is never set) goes on to be resolved. Without this test, B was
  twice as slow as A: every pointer to a marked object read the header and then
  the bitmap. B's sweep (`vergc_par2_sweep`) is `fused_sweep_coalesce` with the
  mark read from the bitmap and each bit cleared as it is read. It writes no
  header for a live object, since the header is already white.
- **Load balancing.** P: Ossia et al. (PLDI 2002): an input and an output packet
  per worker (PKT = 256 entries), and one locked pool of full packets. Full
  outputs are published; an idle worker takes from the pool. One addition: when
  some worker is idle and the pool is empty, a worker publishes the older half
  of its entries. Without it, a deep structure stays on one worker. S: Flood
  et al. (2001), on Chase-Lev deques in the C11 form of Lê et al. (PPoPP 2013),
  with seq_cst operations instead of fences, so that TSan sees the ordering.
  A thief takes one entry from a random victim's top. Deques grow; old arrays
  are freed after the join.
- **Termination: `work_in_flight`**, counting the workers that hold work plus,
  for P, the packets in the pool. A worker holds one count while it has entries
  or is scanning. Publishing adds 1 under the pool lock; taking a packet takes
  over its count. A thief adds 1 before it steals, and gives it back if the
  steal fails. So a 0 means no entry exists anywhere and no worker is scanning:
  a 0 is final. The main thread gives each worker its initial count when it
  hands out the roots. A first version let each worker count its own deque at
  thread start; a thief that emptied the deque first made that count leak, and
  the round never ended (found at once at k = 4).
- **Threads**: k started for each collection and joined.

`par_mark.c` changes:

- It calls `par_mark2.c` when the variant is set.
- Its timed sequential path now follows PR #40's `mark_loop_bounded_flagged`
  with `ov = false`, exactly as `gen_gc`: there is no rescan unless the gray
  stack overflowed.
- It times the minor collection, the sweep and (from `alloc_gen.c`) the whole
  `do_full_gc`.
- The check covers B (§3).

## 3. Checks

| Check | Runs | Result |
|---|---|---|
| Header check at every collection (`VGC_PAR_MARK_CHECK`, `tests/parmark2_check.sh`), 11 programs × AP AS BP BS × k = 1, 2, 4, 8 × {default, CHUNK = PKT = 4, CHUNK = PKT = 1} | 528 | all pass |
| The same for B after the bitmap-first test was added | 264 | all pass |
| The same, Sandmark markbench, minilight, bdd, fft × all five variants × k = 4, 8 | 40 | all pass |
| O (tuned) under `parmark_check.sh`, k = 1, 2, 4, 8 | 40 | all pass |
| ThreadSanitizer (`parmark_build_tsan.sh`), with the header check: AP AS BP BS, 6 programs × k = 2, 4, 8 × 2 settings, and B again after the change | 144 + 72 | no report |
| ThreadSanitizer, O, 10 programs × k = 2, 4, 8 | 30 | no report |

For B, the check rebuilds headers from the bitmap. It requires that the mark
wrote no header, and that the number of set bits equals the number of marked
headers. It also checks the sweep: from the pre-mark headers and the bitmap,
`vergc_par2_sweep` must leave the heap, byte for byte, and the free pointer that
the verified sweep leaves from the sequential mark's headers, with the bitmap
clear afterwards.

**Negative controls**, both caught on every variant:

1. `VGC_PAR_MARK_CHECK_CONTROL=1` flips one mark (for B, a bitmap bit) before
   the comparison. AP, AS, BP, BS and O all abort at the first collection with
   "1 of 9003 headers differ".
2. `VGC_PAR_RACE_CONTROL=1` makes the claim a plain read-modify-write (for O,
   the counter read plain). TSan reports the race on every variant (4–8
   warnings). For B the plain read-modify-write also loses bits set by other
   workers in the same word, and the header check catches the missed marks as
   well.

## 4. Results

binarytrees 16 (3 runs) and 18 (2 runs), median; mark and whole collection
(`do_full_gc`: roots, minor, mark, sweep) in ms per collection, speed-up over
the sequential mark in brackets. The sequential mark is `gen_gc`'s, with PR
#40's rescan skip. Machine: Intel i5-1038NG7, 4 cores / 8 hyper-threads, 16 GB,
macOS, on battery with Low Power Mode on. Each run started with the 1-minute
load at most 8; the idle desktop sits near 4. Noise: on binarytrees 16 the
sequential mark ranged from 29.6 to 39.2 ms and AS at k = 4 from 9.1 to 12.3 ms.
binarytrees 18 is tighter, within 3%.

**Mark.**

binarytrees 16, sequential 30.0 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 52.0 (0.58) | 23.3 (1.29) | 12.3 (2.44) | 12.2 (2.45) |
| **AS** | 36.5 (0.82) | 18.9 (1.58) | **11.0 (2.72)** | 8.5 (3.51) |
| BP | 58.5 (0.51) | 29.0 (1.03) | 14.3 (2.09) | 12.8 (2.34) |
| BS | 49.5 (0.61) | 19.6 (1.52) | 10.7 (2.79) | 10.0 (3.01) |
| O | 85.2 (0.35) | 82.4 (0.36) | 84.1 (0.36) | 123.6 (0.24) |

binarytrees 18, sequential 102.3 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 183.6 (0.56) | 91.7 (1.12) | 48.2 (2.12) | 33.1 (3.08) |
| **AS** | 138.1 (0.74) | 67.0 (1.53) | **35.8 (2.85)** | 28.9 (3.54) |
| BP | 214.6 (0.48) | 108.3 (0.94) | 55.7 (1.84) | 44.1 (2.32) |
| BS | 159.6 (0.64) | 75.7 (1.35) | 42.1 (2.43) | 36.2 (2.82) |
| O | 305.1 (0.34) | 305.3 (0.33) | 244.2 (0.42) | 518.4 (0.20) |

**Whole collection.**

binarytrees 16, sequential 72.0 ms, of which the sweep is 23:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 91.3 (0.79) | 59.7 (1.21) | 49.5 (1.45) | 54.6 (1.32) |
| AS | 73.8 (0.97) | 58.4 (1.23) | 48.5 (1.48) | 44.9 (1.60) |
| BP | 94.9 (0.76) | 67.4 (1.07) | 50.7 (1.42) | 48.5 (1.48) |
| BS | 86.0 (0.84) | 56.1 (1.28) | 44.5 (1.62) | 45.8 (1.57) |
| O | 145.2 (0.50) | 143.0 (0.50) | 148.4 (0.48) | 185.2 (0.39) |

binarytrees 18, sequential 244.3 ms, of which the sweep is 141:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 331.3 (0.74) | 234.2 (1.04) | 191.1 (1.28) | 171.5 (1.42) |
| AS | 279.3 (0.87) | 208.0 (1.17) | 175.0 (1.40) | 169.0 (1.45) |
| BP | 349.9 (0.70) | 246.3 (0.99) | 192.9 (1.27) | 187.5 (1.30) |
| BS | 300.3 (0.81) | 212.7 (1.15) | 179.3 (1.36) | 179.1 (1.36) |
| O | 575.8 (0.42) | 578.3 (0.42) | 516.6 (0.47) | 830.6 (0.29) |

**Where parallel time goes** (binarytrees 16, one run each with
`VGC_PAR_PROF=1`, rdtsc). The figures are percentages of summed worker time.
"Pool" is time in packet-pool operations, including lock waits; for O it is
lock and counter time.

| config | mark ms | idle | steal | pool (lock wait) | scan | CAS fail / M claims | steals / coll | packets published / coll (shares) | lock contended | thread start + join ms / coll |
|---|---|---|---|---|---|---|---|---|---|---|
| AP k2 | 26.2 | 0 | – | 1 (0) | 99 | 0 | – | 627 (4) | 0% | 0.17 |
| AP k4 | 14.6 | 0 | – | 1 (0) | 99 | 0 | – | 638 (20) | 2% | 0.22 |
| AP k8 | 18.7 | 3 | – | 5 (5) | 91 | 0 | – | 660 (47) | 4% | 1.59 |
| AS k2 | 22.4 | 0 | 0 | – | 100 | 0 | 15 | – | – | 0.22 |
| AS k4 | 8.8 | 0 | 0 | – | 100 | 0 | 57 | – | – | 0.21 |
| AS k8 | 8.1 | 2 | 0 | – | 98 | 0 | 148 | – | – | 1.04 |
| BP k4 | 16.2 | 0 | – | 1 (0) | 99 | 2 | – | 640 (21) | 1% | 0.20 |
| BP k8 | 12.1 | 1 | – | 2 (2) | 97 | 4 | – | 663 (50) | 4% | 0.84 |
| BS k4 | 9.8 | 0 | 0 | – | 100 | 1 | 56 | – | – | 0.21 |
| BS k8 | 8.5 | 1 | 0 | – | 99 | 2 | 157 | – | – | 0.42 |
| O k2 | 77.4 | 44 | – | 0 | 56 | – | – | 466 messages | 1% | 0.14 |
| O k4 | 81.6 | 58 | – | 0 | 42 | – | – | 1401 messages | 1% | 0.19 |
| O k8 | 143.5 | 66 | – | 0 | 34 | – | – | 3426 messages | 1% | 1.00 |

Steals are rare (one per 5,000 claims at k = 4), because one stolen range can
hold a large part of the tree. The cost per collection of starting and joining
threads is 0.2 ms at k ≤ 4 and about 1 ms at k = 8. That is small next to a
10–100 ms mark, but it would dominate on programs with sub-millisecond marks.

## 5. Sandmark

Selection, build and run status are in
`generational/ocaml-integration/tests/sandmark/README.md`. That file has every
executable in Sandmark's `run_config.json` and `run_config_byte.json`, each
either selected or excluded with a reason, and the Sandmark commit used. In
short:

- **Builds and runs on our 4.14 bytecode runtime: 108 benchmark/parameter
  pairs.** Standard library only, or the compiler's own `unix`/`str` (loaded
  dynamically; that works). Same output as the stock runtime.
- **Excluded**:
  - needing opam packages: zarith, lwt, yojson, decompress, irmin, owl, and
    the application benchmarks (coq, menhir, alt-ergo, frama-c, ...);
  - Domain, domainslib or effects;
  - `capi`, which has its own C stubs;
  - `fannkuchredux`, which raised `Invalid_argument` on the stock runtime too.
- **Fail on the verified runtime itself, before any parallel mark** (worth
  issues of their own):
  - `stacks` (floats), `lazylist` and `finalise` stop with "root overflow":
    more than `MAX_ROOTS` = 2^18 roots in `alloc_gen.c`;
  - `zdd` runs out of memory at every heap tried up to 671M words, against a
    stock peak of 21M;
  - `hamming` runs about 500× slower than on stock (150 s against 0.3 s).
- **Timed (pending, §6)**: with a heap 4× the live peak, almost every
  Sandmark program spends well under 1% of its time in the mark, so a parallel
  mark cannot change it measurably. Selected are the programs whose sequential
  mark is at least 1% of the run and which do at least 3 major collections:
  `markbench` (Sandmark's own mark benchmark: about 2.8 s per mark; 87% of the
  run), `minilight`, `bdd`, `fft`. All four pass the header check on all five
  variants.

## 6. What remains, and how to finish

Not measured: binarytrees 18's third run and its profiles; livemap; livegraph;
markbench, minilight, bdd and fft. On mains power, with Low Power Mode off and
the machine left alone (about 6 hours):

```
cd generational/ocaml-integration/tests
caffeinate -dims ./parmark2_matrix.sh results_parmark2/matrix 1 bt18
caffeinate -dims ./parmark2_matrix.sh results_parmark2/matrix 3 livemap livegraph sm:markbench sm:minilight sm:bdd sm:fft
python3 parmark2_summarize.py results_parmark2/matrix.jsonl
python3 parmark2_summarize.py --prof results_parmark2/matrix.prof.jsonl
```

The results already collected (`results_parmark2/*.jsonl`, not committed) are
appended to, not replaced. For numbers on mains power, rerun bt16 and bt18 as
well, into a fresh prefix.

## 7. Files

| File | |
|---|---|
| `verified_gc/par_mark2.c` | new: AP, AS, BP, BS; bitmap sweep; statistics and profile |
| `verified_gc/par_mark.c` | dispatch to `par_mark2.c`; PR #40's sequential mark in the timed path; collection timing; check of B's marks and sweep |
| `verified_gc/alloc_gen.c` | times `do_full_gc` |
| `verified_gc/Makefile`, `parmark_build_tsan.sh` | build `par_mark2.c` |
| `tests/parmark2_check.sh` | the header check over the variants, k and stress settings |
| `tests/parmark2_bench.sh`, `parmark2_matrix.sh`, `parmark2_summarize.py` | timing runs (JSON lines), the matrix, the tables |
| `tests/sandmark/build.sh`, `benchmarks.txt`, `README.md` | Sandmark build, list, selection |
| `.gitignore` | `tests/sandmark/bin/` |
