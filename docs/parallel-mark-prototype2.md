# Parallel mark, prototype 2: established designs

Branch `sheera/parallel-mark-proto2` (from `sheera/parallel-mark-proto`, with
`origin/main` merged for PR #40's rescan skip). An **unverified** C prototype,
for measurement only. It marks the verified GC's heap in parallel the way
established collectors do, so that it can be compared with the sequential
verified mark and with our ownership design (prototype 1, `par_mark.c`).

**Status: measured.** The checks are complete (§3), and so is the timing
matrix: 8 programs × 21 configurations × 3 runs, plus one profiled run per
variant at k = 2, 4, 8. It ran in two sessions:

- **On battery, with Low Power Mode on**: binarytrees 16 (3 runs and the
  profiles) and binarytrees 18 runs 1 and 2 (§4).
- **On mains power, with the machine kept awake**: binarytrees 18 run 3 and
  its profiles; livemap, livegraph, and the Sandmark programs markbench,
  minilight, bdd and fft, all 3 runs and the profiles (§5).

Numbers from the two sessions are not mixed: every table says which session it
comes from. Mains power did not make binarytrees 18 faster. Its third run was
about 25% *slower* than runs 1 and 2 for every configuration (sequential mark
127.7 against 102.3 ms), while the speed-ups stayed within 0.25 (§5.1). The
cause is not known. binarytrees 16 was not rerun on mains power.

## 1. Summary

The conclusions from binarytrees (the first four points below) hold on
binarytrees 18 on mains power. They do **not** all hold on the other programs.
On livegraph and markbench, packets beat work stealing by a wide margin, and
the bitmap costs nothing (§5).

On binarytrees:

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

On the other programs (mains power, §5):

- **O is slower than the sequential mark everywhere**: on all 8 programs, at
  every k. Its best is 0.99× (markbench, k = 4); on livegraph at k = 8 it is
  0.08×. This conclusion holds without exception.
- **Packets win on livegraph and markbench.** At 4 threads, BP marks livegraph
  4.4× faster than the sequential mark (AS: 2.6×) and markbench 7.9× faster
  (AS: 2.85×). At 8 threads BP reaches 4.8× and 10.9×. AP and BP are faster
  than the sequential mark even with **one** thread: 1.1–1.2× on livegraph,
  about 2× on markbench. With one thread there is no contention, so the gain
  comes from scanning in a different order. A worker pops from its input packet
  and pushes onto its output packet, so children wait until the input packet
  is empty: the order is breadth-first in batches of 256 entries. The
  sequential mark and the deques go depth first. Why this helps is not
  measured yet (probably cache misses that can overlap; §7).
- **Work stealing wins on bdd**, where packets collapse at k ≥ 4: the pool
  lock takes 30–58% of worker time (19–34% of lock acquisitions contended), and
  AP at k = 8 is 0.55× the sequential mark (AS: 1.75×). On livemap, minilight
  and fft, S and P are within 25% of each other, with no consistent winner.
- **The cost of B against A depends on the program.** B/A mark ratios on mains
  power at k = 1–8: binarytrees 18 1.14–1.25, livemap 1.06–1.24, minilight
  1.04–1.14, bdd 0.95–1.05, fft 1.50–1.62 at k ≤ 4 and 1.02–1.15 at k = 8,
  livegraph 0.83–1.05, markbench 0.79–1.04. So B is between 21% faster and
  62% slower. On livegraph and markbench, where packets are fastest, it is not
  slower.
- **Whole collections** gain much more where the sweep is small. BP at k = 8:
  3.5× on livegraph, 7.8× on markbench. markbench's run time falls from
  13.5 s to 3.4 s. On minilight, bdd and fft the gain is at most 1.25×,
  because the mark is under half of a collection there (fft: 14 of 49 ms; the
  rest is the sweep, the minor collection and roots), and the run time does
  not change.
- **The best variant is not the same everywhere.** At k = 4, the fastest mark
  is BP on livegraph and markbench, AS on binarytrees and bdd, AP on livemap,
  and AS or AP on fft and minilight (within 5%). BS, the variant chosen for
  `docs/parallel-gc-combined-design.md`, is never the fastest at k = 4. It is
  within 25% of the best on binarytrees 18, minilight and bdd, 1.3× slower
  than the best on livemap and 1.5× on fft, and 1.6× and 2.5× slower than BP
  on livegraph and markbench.

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

## 4. Results on battery: binarytrees 16 and 18

binarytrees 16 (3 runs) and 18 (runs 1 and 2), median; mark and whole collection
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

## 5. Results on mains power

Machine as in §4, on mains power, with the machine kept awake. The 1-minute
load at the start of a run was 1.8–8.0. Medians as in §4; the sequential mark
had no gray-stack overflow, and so no rescan, on any of these programs.

### 5.1 binarytrees 18, run 3

One run. Compared with runs 1 and 2 on battery (§4), every configuration is
slower by about the same factor: the sequential mark by 25% (127.7 against
102.3 ms), AS at k = 4 by 19%, the run as a whole by 23% (69.2 against
56.4 s). The speed-ups agree with §4 to within 0.25 (AS at k = 4: 2.99 against
2.85; AP at k = 4: 2.36 against 2.12). B/A mark ratios are 1.14–1.25, as on
battery. The slow-down is not explained. The load at the start of each run
was 1.9–7.3, against 2.3–5.1 on battery.

**Mark.**

binarytrees 18, sequential 127.7 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 222.3 (0.57) | 105.3 (1.21) | 54.2 (2.36) | 40.5 (3.15) |
| AS | 167.3 (0.76) | 81.4 (1.57) | **42.7 (2.99)** | **35.1 (3.63)** |
| BP | 253.9 (0.50) | 125.3 (1.02) | 67.5 (1.89) | 50.8 (2.52) |
| BS | 191.9 (0.67) | 94.7 (1.35) | 51.9 (2.46) | 43.0 (2.97) |
| O | 390.3 (0.33) | 386.9 (0.33) | 307.1 (0.42) | 522.7 (0.24) |

**Whole collection.**

binarytrees 18, sequential 283.2 ms, of which the sweep is 153.8:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 382.3 (0.74) | 257.9 (1.10) | 205.8 (1.38) | 192.0 (1.48) |
| AS | 320.5 (0.88) | 233.9 (1.21) | **195.9 (1.45)** | **189.6 (1.49)** |
| BP | 408.3 (0.69) | 276.9 (1.02) | 229.9 (1.23) | 202.3 (1.40) |
| BS | 344.0 (0.82) | 247.0 (1.15) | 205.5 (1.38) | 193.7 (1.46) |
| O | 696.7 (0.41) | 687.9 (0.41) | 621.0 (0.46) | 823.7 (0.34) |

### 5.2 livemap, livegraph and Sandmark

3 runs each. Mark and whole collection in ms per collection, speed-up over
the sequential mark in brackets; the fastest variant at k = 4 and at k = 8 in
bold. Spread of the mark across the 3 runs: within 5% for 88 of the 126
configurations and within 10% for 112. The widest: O at k = 8 on markbench and
minilight (89% and 85%), the sequential mark on markbench (2171–2804 ms; the
median, 2195, is one of the two close runs), AP at k = 2 on livemap (23%), AS
at k = 4 on livegraph (68.2–83.4 ms) and AP at k = 4 on markbench (17%).

**Mark.**

livemap, sequential 36.0 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 85.2 (0.42) | 46.7 (0.77) | **26.5 (1.36)** | 23.5 (1.53) |
| AS | 88.1 (0.41) | 47.9 (0.75) | 30.8 (1.17) | **22.4 (1.61)** |
| BP | 99.4 (0.36) | 53.3 (0.68) | 28.2 (1.27) | 25.4 (1.41) |
| BS | 100.9 (0.36) | 59.3 (0.61) | 35.4 (1.02) | 26.5 (1.36) |
| O | 51.5 (0.70) | 146.9 (0.25) | 232.2 (0.16) | 229.3 (0.16) |

livegraph, sequential 174.9 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 148.3 (1.18) | 76.1 (2.30) | 45.4 (3.85) | 43.8 (3.99) |
| AS | 241.9 (0.72) | 118.6 (1.47) | 68.2 (2.56) | 47.6 (3.67) |
| BP | 155.6 (1.12) | 77.7 (2.25) | **40.0 (4.37)** | **36.2 (4.83)** |
| BS | 255.1 (0.69) | 118.1 (1.48) | 65.1 (2.69) | 40.1 (4.36) |
| O | 220.4 (0.79) | 556.9 (0.31) | 1337.4 (0.13) | 2111.1 (0.08) |

markbench, sequential 2195.3 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 1064.8 (2.06) | 519.8 (4.22) | 286.5 (7.66) | 253.7 (8.65) |
| AS | 2808.6 (0.78) | 1332.9 (1.65) | 769.1 (2.85) | 514.2 (4.27) |
| BP | 1104.2 (1.99) | 540.2 (4.06) | **277.7 (7.91)** | **201.6 (10.89)** |
| BS | 2485.6 (0.88) | 1222.7 (1.80) | 689.6 (3.18) | 440.1 (4.99) |
| O | 2806.3 (0.78) | 2415.1 (0.91) | 2216.8 (0.99) | 2577.5 (0.85) |

minilight, sequential 0.96 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 1.70 (0.56) | 1.12 (0.86) | **0.73 (1.32)** | 0.72 (1.32) |
| AS | 1.93 (0.50) | 1.18 (0.82) | 0.75 (1.27) | **0.65 (1.47)** |
| BP | 1.94 (0.50) | 1.18 (0.81) | 0.75 (1.27) | 0.76 (1.26) |
| BS | 2.14 (0.45) | 1.28 (0.75) | 0.80 (1.19) | 0.70 (1.37) |
| O | 1.62 (0.59) | 2.29 (0.42) | 2.08 (0.46) | 3.06 (0.31) |

bdd, sequential 2.57 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 4.93 (0.52) | 2.95 (0.87) | 2.84 (0.90) | 4.71 (0.55) |
| AS | 5.50 (0.47) | 3.08 (0.84) | **1.93 (1.33)** | **1.47 (1.75)** |
| BP | 4.85 (0.53) | 2.96 (0.87) | 2.91 (0.88) | 4.56 (0.56) |
| BS | 5.20 (0.49) | 3.02 (0.85) | 2.02 (1.27) | 1.54 (1.67) |
| O | 4.14 (0.62) | 12.3 (0.21) | 21.0 (0.12) | 40.5 (0.06) |

fft, sequential 14.3 ms:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 24.2 (0.59) | 12.1 (1.18) | 6.73 (2.12) | **6.04 (2.36)** |
| AS | 23.4 (0.61) | 12.1 (1.18) | **6.40 (2.23)** | 6.10 (2.34) |
| BP | 39.1 (0.37) | 19.2 (0.74) | 10.1 (1.42) | 6.95 (2.06) |
| BS | 37.3 (0.38) | 19.0 (0.75) | 9.62 (1.49) | 6.21 (2.30) |
| O | 26.0 (0.55) | 67.7 (0.21) | 169.7 (0.08) | 236.5 (0.06) |

**Whole collection.**

livemap, sequential 57.9 ms, of which the sweep is 14.8:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 106.9 (0.54) | 68.5 (0.84) | **48.0 (1.21)** | 45.2 (1.28) |
| AS | 109.2 (0.53) | 69.4 (0.83) | 52.6 (1.10) | **43.5 (1.33)** |
| BP | 120.9 (0.48) | 74.5 (0.78) | 48.8 (1.19) | 46.1 (1.26) |
| BS | 121.3 (0.48) | 81.1 (0.71) | 56.1 (1.03) | 47.0 (1.23) |
| O | 87.5 (0.66) | 183.0 (0.32) | 267.5 (0.22) | 264.6 (0.22) |

livegraph, sequential 197.0 ms, of which the sweep is 14.9:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 169.0 (1.17) | 97.6 (2.02) | 66.0 (2.98) | 64.7 (3.04) |
| AS | 263.5 (0.75) | 140.0 (1.41) | 89.3 (2.21) | 68.3 (2.88) |
| BP | 175.8 (1.12) | 98.8 (1.99) | **60.9 (3.23)** | **56.3 (3.50)** |
| BS | 275.9 (0.71) | 142.1 (1.39) | 85.8 (2.30) | 59.9 (3.29) |
| O | 254.9 (0.77) | 592.4 (0.33) | 1371.8 (0.14) | 2145.6 (0.09) |

markbench, sequential 2301.1 ms, of which the sweep is 105.0:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 1168.5 (1.97) | 627.2 (3.67) | 391.4 (5.88) | 360.4 (6.39) |
| AS | 2915.6 (0.79) | 1441.7 (1.60) | 877.6 (2.62) | 619.9 (3.71) |
| BP | 1198.3 (1.92) | 636.6 (3.61) | **371.5 (6.19)** | **296.5 (7.76)** |
| BS | 2580.7 (0.89) | 1318.9 (1.74) | 785.4 (2.93) | 535.5 (4.30) |
| O | 3040.7 (0.76) | 2624.7 (0.88) | 2432.8 (0.95) | 2822.5 (0.82) |

minilight, sequential 2.25 ms, of which the sweep is 0.45:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 3.00 (0.75) | 2.41 (0.93) | 2.03 (1.11) | 2.04 (1.10) |
| AS | 3.22 (0.70) | 2.46 (0.91) | 2.05 (1.10) | **1.95 (1.15)** |
| BP | 3.14 (0.72) | 2.41 (0.93) | **1.99 (1.13)** | 2.02 (1.11) |
| BS | 3.39 (0.66) | 2.53 (0.89) | 2.04 (1.10) | 1.95 (1.15) |
| O | 3.32 (0.68) | 3.99 (0.56) | 3.77 (0.60) | 4.78 (0.47) |

bdd, sequential 5.53 ms, of which the sweep is 0.55:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 8.02 (0.69) | 6.06 (0.91) | 6.00 (0.92) | 7.85 (0.70) |
| AS | 8.56 (0.65) | 6.14 (0.90) | **5.02 (1.10)** | 4.64 (1.19) |
| BP | 7.85 (0.71) | 5.92 (0.94) | 5.87 (0.94) | 7.53 (0.73) |
| BS | 8.23 (0.67) | 5.99 (0.92) | 5.02 (1.10) | **4.54 (1.22)** |
| O | 7.77 (0.71) | 16.1 (0.34) | 25.0 (0.22) | 44.6 (0.12) |

fft, sequential 48.9 ms, of which the sweep is 13.8:

| variant | k = 1 | k = 2 | k = 4 | k = 8 |
|---|---|---|---|---|
| AP | 59.6 (0.82) | 47.4 (1.03) | 42.2 (1.16) | 41.2 (1.19) |
| AS | 58.1 (0.84) | 47.5 (1.03) | **41.9 (1.17)** | 41.6 (1.18) |
| BP | 72.7 (0.67) | 51.7 (0.95) | 43.5 (1.13) | 39.6 (1.23) |
| BS | 70.8 (0.69) | 51.3 (0.95) | 42.3 (1.16) | **39.2 (1.25)** |
| O | 74.6 (0.66) | 116.9 (0.42) | 217.5 (0.22) | 285.8 (0.17) |

Run times (median wall s, sequential → fastest): markbench 13.5 → 3.35 (BP,
k = 8), livegraph 4.48 → 3.86, livemap 31.7 → 31.1, minilight 19.3 → 18.4,
bdd 34.7 (no gain), fft 19.0 → 18.7. Only markbench changes much; the others
spend too little of the run in collections.

### 5.3 Where parallel time goes

One profiled run of each variant at k = 2, 4, 8 per program
(`python3 parmark2_summarize.py --prof results_parmark2/matrix.prof.jsonl`
prints all 120 rows; the first 15 are binarytrees 16 on battery, in §4).
Selected rows; columns as in §4. The mark times here are one run with
profiling on and can differ from the medians above (markbench BP at k = 4:
388 against 278 ms).

| bench | config | mark ms/coll | idle % | steal % | pool % (lock wait %) | scan % | CAS fail /M claims (lost, neighbour) | steals ok/coll (tries) | packets pub/coll (shares) | lock contended % | thread start+join ms/coll |
|---|---|---|---|---|---|---|---|---|---|---|---|
| bt18 | AS-k4 | 43.00 | 0 | 0 | 0 (0) | 100 | 0 (0, 0) | 65 (66) | - | - | 0.23 |
| bt18 | BS-k4 | 51.13 | 0 | 0 | 0 (0) | 100 | 0 (0, 0) | 62 (64) | - | - | 0.24 |
| bt18 | O-k4 | 310.61 | 56 | 0 | 0 (0) | 44 | - | - | 1518 msgs | 1 | 0.23 |
| livemap | BP-k4 | 28.37 | 0 | 0 | 2 (1) | 98 | 186 (0, 186) | - | 3078 (32) | 2 | 0.24 |
| livemap | O-k4 | 362.56 | 11 | 0 | 59 (43) | 31 | - | - | 849926 msgs | 10 | 0.25 |
| livegraph | AS-k4 | 68.98 | 0 | 0 | 0 (0) | 99 | 0 (0, 0) | 9684 (10530) | - | - | 0.25 |
| livegraph | BP-k4 | 39.87 | 0 | 0 | 1 (1) | 99 | 5 (1, 4) | - | 1498 (103) | 2 | 0.24 |
| livegraph | BS-k4 | 62.87 | 0 | 0 | 0 (0) | 100 | 3 (1, 3) | 420 (441) | - | - | 0.25 |
| livegraph | O-k4 | 2101.98 | 23 | 0 | 50 (38) | 28 | - | - | 4799955 msgs | 13 | 0.26 |
| sm:markbench | AP-k4 | 278.80 | 0 | 0 | 0 (0) | 100 | 1 (1, 0) | - | 63 (48) | 15 | 0.21 |
| sm:markbench | AS-k4 | 725.41 | 0 | 0 | 0 (0) | 100 | 2412 (2412, 0) | 7404 (7880) | - | - | 0.24 |
| sm:markbench | BP-k4 | 388.27 | 0 | 0 | 0 (0) | 100 | 11 (2, 9) | - | 260 (40) | 3 | 0.29 |
| sm:markbench | BS-k4 | 662.56 | 0 | 0 | 0 (0) | 100 | 10441 (4534, 5906) | 8095 (8446) | - | - | 0.22 |
| sm:markbench | O-k4 | 3318.63 | 56 | 0 | 12 (4) | 32 | - | - | 5079255 msgs | 1 | 0.52 |
| sm:minilight | AP-k8 | 0.73 | 5 | 0 | 20 (14) | 74 | 1 (1, 0) | - | 112 (91) | 25 | 0.26 |
| sm:minilight | AS-k8 | 0.66 | 8 | 1 | 0 (0) | 91 | 2 (2, 0) | 214 (230) | - | - | 0.31 |
| sm:minilight | BP-k8 | 0.82 | 10 | 0 | 20 (14) | 70 | 121 (1, 120) | - | 111 (89) | 23 | 0.29 |
| sm:bdd | AP-k8 | 4.88 | 17 | 0 | 58 (40) | 25 | 143 (143, 0) | - | 1822 (1767) | 34 | 0.28 |
| sm:bdd | AS-k8 | 1.47 | 3 | 3 | 0 (0) | 94 | 328 (328, 0) | 1750 (1800) | - | - | 0.37 |
| sm:bdd | BP-k8 | 4.86 | 17 | 0 | 58 (40) | 26 | 708 (127, 581) | - | 1819 (1764) | 34 | 0.28 |

- **S is not slower on livegraph and markbench for lack of balance.** AS and
  BS spend 99–100% of worker time scanning there, with no idle time, just as
  on binarytrees. They steal much more often (livegraph AS k = 4: 9,684 steals
  per collection; markbench: 1,600–14,800), and on markbench they lose
  claims: AS fails 2,412 CAS per million claims at k = 4, BS 10,441. But the
  difference is already there at k = 1, so it is the cost of scanning in that
  order, not of sharing work.
- **Packets break down on bdd** at k = 8: 58% of worker time in the pool, 40%
  waiting for its lock, 34% of acquisitions contended. bdd's marks are about
  3 ms, and packets are shared (published while another worker is idle) at
  almost every publication (1,767 of 1,822 per collection). minilight's
  sub-millisecond marks show the same trend more weakly (20% in the pool at
  k = 8).
- **O** idles 4–71% of worker time and, on livemap, livegraph, bdd and fft,
  spends 29–59% in locks and the counter. It sends 0.5–5.3 million messages
  per collection on livemap and livegraph.
- Starting and joining threads costs 0.2–0.5 ms per collection at k ≤ 4 and up
  to 1.15 ms at k = 8. On minilight (0.96 ms sequential mark) that is nearly
  a third of the parallel mark at k = 4.

## 6. Sandmark

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
- **Timed (§5)**: with a heap 4× the live peak, almost every
  Sandmark program spends well under 1% of its time in the mark, so a parallel
  mark cannot change it measurably. Selected are the programs whose sequential
  mark is at least 1% of the run and which do at least 3 major collections:
  `markbench` (Sandmark's own mark benchmark: about 2.8 s per mark; 87% of the
  run), `minilight`, `bdd`, `fft`. All four pass the header check on all five
  variants.

## 7. Reproducing, and open questions

On mains power, with the machine left alone (about 6 hours for everything):

```
cd generational/ocaml-integration/tests
caffeinate -dims ./parmark2_matrix.sh results_parmark2/matrix 3
python3 parmark2_summarize.py results_parmark2/matrix.jsonl
python3 parmark2_summarize.py --prof results_parmark2/matrix.prof.jsonl
```

The results (`results_parmark2/*.jsonl`, not committed) are appended to, not
replaced. The current files hold both sessions, in order: in `matrix.jsonl`,
lines 1–105 are on battery (binarytrees 16, binarytrees 18 runs 1 and 2) and
lines 106–504 on mains power; in `matrix.prof.jsonl`, lines 1–15 are on
battery and 16–120 on mains power. The summariser takes the median over all
runs it is given, so the sessions have to be split before summarising
binarytrees 18 (the tables above were made that way).

Open:

- **Why packets scan faster** on livegraph and markbench, even at k = 1. The
  likely cause is the breadth-first-in-batches order (§1), which gives the
  core independent loads to overlap. To check: count cache misses
  (or run the sequential mark with a FIFO of 256-entry batches) on those two
  programs. If the order is the cause, a deque variant could take the same
  order, and the choice between S and P would come down to bdd's pool
  contention.
- **Why binarytrees 18 was 20–25% slower on mains power** than on battery.
  binarytrees 16 on mains power would show whether it is the program or the
  session.
- **Short marks**: on minilight and bdd (1–3 ms) thread start and join is
  0.2–0.4 ms per collection. A pool of threads kept across collections would
  remove it.

## 8. Files

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
