# Parallel mark + parallel sweep: a design check

Read-only review (no code changed) of one combination:

- **(a)** the parallel mark **BS** from `docs/parallel-mark-prototype2.md`
  (`par_mark2.c`): a side mark bitmap, one bit per heap word, set with a 32-bit
  CAS; Chase-Lev work stealing. The mark never writes a header.
- **(b)** a sweep that reads the marks from that bitmap (`vergc_par2_sweep`:
  `fused_sweep_coalesce` with "black" read as "bit set", each bit cleared as it
  is read).
- **(c)** the parallel sweep of branch `sheera/parallel-sweep` (`2ad43d8`):
  `prepass` cuts, `sweep_segment` per piece on threads, sequential `merge`;
  proved `sweep_par bs g == fused_sweep_coalesce g` under `valid_bounds g bs`.
- **(d)** an **object-start table** kept by the allocator. Entry `T[j]` gives the
  first header at or after the boundary `B_j = zero_addr + j * 64 KB`, and the
  parallel sweep takes its cuts from the table instead of from `prepass`.

Addresses below are written relative to `zero_addr` (`Z`). One table window is
`0x10000` bytes (8192 words). A bitmap word (32 bits) covers 32 heap words
(256 bytes).

## 1. Summary

1. **The combination is sound only if the table holds walk positions.** The
   proof of (c) needs exactly one thing from the cuts: `valid_bounds g bs`,
   meaning every interior cut is a header that the walk from `Z` lands on. That
   the cut is the *first* header after a boundary only affects load balance.
   So the correctness invariant for (d) is:

   > every `T[j]` is `heap_size`, or a walk position of the current heap.

   Allocation never removes a walk position: it only shrinks a free block in
   place and adds a header (§3.1). The invariant therefore survives any
   allocator behaviour, including doing nothing. **Coalescing is the only thing
   that removes walk positions**, so the sweep and the merge are the writers
   that correctness depends on. The allocator matters only for balance.
2. **Three races or wrong results** need a design decision. Each is traced in §4:
   - **R1, the bitmap word shared at a cut** (§4.4). `vergc_par2_sweep` clears
     a bit with a relaxed load followed by a store. When two segments clear bits
     in the same 32-bit word, one bit survives. A surviving bit on a live object
     makes the next mark skip that object's fields (BS tests the bit before it
     reads the header), and the object's children are freed while still
     reachable. Every load and store is atomic, so ThreadSanitizer will
     **not** report it. The existing B check ("bitmap clear after the sweep")
     would catch it.
   - **R2, a stale table entry after a merge** (§4.2, §4.3). If a header that a
     table entry names is absorbed into a coalesced run, the next sweep cuts
     inside a free block. It then parses stale bytes as a header and puts live
     objects on the free list.
   - **R3, exact maintenance by the allocator is quadratic** (§4.6). Keeping
     every entry exactly "the first header" costs O(block / 64 KB) writes for
     each allocation carved from a large free block. The allocator carves
     right-justified from the top of one huge initial block, so this is the
     common case. Updating one entry per allocation is enough (§3.2).
3. **Proofs that change** (§5): the sweep needs a bitmap version and a table
   postcondition. Coalescing needs a new lemma: the walk positions after
   coalescing are the survivors and the run starts. In the parallel sweep, the
   theorem and the joining lemma stay. `sweep_segment`, `merge` and the driver
   change, and `prepass` is replaced by a cut function proved from the table
   invariant. The allocator needs one lemma ("allocation keeps every walk
   position"), plus table frames through promotion if it writes the table.
   `gc_correct` and `gen_gc` need the bitmap and the table as new state. The
   mark's postcondition moves from headers to the bitmap. BS itself is
   unverified.
4. **Estimate (§6), binarytrees 18, 4 threads.** The whole collection goes from
   244.3 ms to about 80–126 ms, a **1.9–3.0× speed-up, about 2.4× in the middle
   case**. BS alone gives 1.36×. With `prepass` instead of the table, the
   serial pre-pass walk on a header-dense heap uses up most of the gain:
   1.0–1.3×.

## 2. The pieces as they are

**BS mark** (`par_mark2.c`). The bitmap has `bit i` for the word at
`Z + 8i`, packed 32 per `_Atomic uint32_t`. A claim is a CAS loop on the word.
Only headers of marked objects get a bit. The mark tests the bit at `v − 8`
before it reads the header, so a set bit means "already marked, do not scan".
Workers are joined before the sweep.

**Bitmap sweep** (`vergc_par2_sweep`). This is the sequential walk of
`fused_sweep_coalesce`, with `marked` meaning that the header's bit is set. It
clears that bit with `atomic_load` followed by `atomic_store(word & ~m)`, which
is not a read-modify-write. A live header is already white, so nothing is
written to it. Free runs are flushed with `flush_blue`. The free list comes out
in descending address order, as from the verified sweep.

**Parallel sweep** (`parallel-sweep/`, extracted to `GC_SweepPar.c`, threads in
`c/par_sweep.c`):

- `prepass` (sequential, one walk over every header) writes cuts `b0 = Z <
  b1 < … < bn = heap_size`. Cut `i` is the first object start at or after
  `Z + floor(i * W / k)` words. So the table in (d) computes exactly what the
  pre-pass computes now, rounded to 64 KB.
- `sweep_segment(lo, hi)` walks the headers in `[lo, hi)` and returns
  `seg_result {all_free, lead_fb, lead_rw, trail_fb, trail_rw, has_link,
  first_link, local_head}`. It whitens survivors (`makeWhite_r`), flushes
  interior runs onto a local list, and leaves the leading and trailing runs
  unflushed.
- `merge` runs sequentially after every worker is joined. Left to right, it
  joins `carry + lead`, flushes the joined run, patches `first_link` to the
  head so far, and carries `trail` forward. All-free segments only extend
  the carry.
- Proved: `sweep_par_correct` (`sweep_par bs g == fused_sweep_coalesce g`,
  heap and head), `join_correct`, `sweep_segment`, `merge`, `prepass`,
  `sweep_par_seq`. Trusted: the thread handling in `par_sweep.c`, and the
  hand-added hook in the extracted `GC_Gen_Impl.c`.

**Allocator** (`GC.Spec.Allocator`, `GC.Impl.Allocator`, extracted `allocate` /
`allocate_part1`). First fit along the free list. It is right-justified: with
`leftover = block_wz − wz`, a leftover of 0 hands the block over, a leftover of
1 leaves a header-only fragment at the block's address, and a leftover of 2 or
more shrinks the block in place. In every case the object's header goes at
`hd + leftover * 8`. Promotion (`forward_if_minor`, inside `minor_collect_full`)
and the C bridge's direct major path both use it.

## 3. The combined design, stated

### 3.1 What may write headers, and what each does to walk positions

| Writer | Effect on the walk positions | Effect on `T` (correctness) |
|---|---|---|
| allocator, leftover 0 | none (same header, new size = old size) | none needed |
| allocator, leftover 1 | adds `hd + 8` (`hd` stays, now wosize 0) | none needed |
| allocator, leftover ≥ 2 | adds `p = hd + leftover * 8` (`hd` stays, shrunk) | none needed |
| promotion | the same as the allocator, since it calls `allocate_part1` | none needed |
| BS mark | none (it writes only the bitmap) | none |
| `Obj.set_tag`, lazy forcing, `make_forward` | none (tag only) | none |
| `Obj.truncate` (if reachable) | adds a header in the object's tail | none needed |
| sweep / merge, coalescing a run `[r, e)` | **removes** every header in `(r, e)` | **must rewrite** entries naming them |

The only removing writer is the sweep. So the design needs:

- **Invariant `table_ok g T`:** for every `j`, `T[j] = heap_size`, or
  `walk_visits g Z T[j]`. For balance only, also `T[j] ≥ B_j`.
- **Cuts:** before any worker starts, read `T` at an even stride
  (`j_i ≈ i * N / k`). Drop entries equal to `heap_size` and entries that do
  not exceed the previous cut, then prepend `Z` and append `heap_size`. Under
  `table_ok`, this is `valid_bounds g bs`: the list is strictly increasing,
  aligned (headers are), every interior cut is below `heap_size`, and every
  interior cut is a walk position.

### 3.2 Who writes `T`

**The sweep, exactly, every collection.** Segment `s` with range `[lo, hi)`
owns the entries with `B_j ∈ (lo, hi]`. These sets are disjoint across
segments, so there are no write conflicts. For each owned `B_j`:

- if `B_j` falls before the segment's first survivor `f` (in the leading run),
  it writes `T[j] = f`. This is final: the leading run's header ends up at `lo`
  or earlier, so `f` is the first header at or after `B_j`.
- if `B_j` falls inside an interior run, or a survivor follows it, it writes
  the next survivor or run start after `B_j`. That is final too.
- if `B_j` falls in the trailing run `(t, hi]`, it writes `hi` provisionally.
  This is correct only if `hi` is still a header after the merge.
- in an all-free segment, it writes `hi` provisionally.

**The merge, for joined runs.** When it flushes `carry + lead` for a segment
`s + 1` that is not all free, the run ends at that segment's first survivor
`f = lead_fb − 8 + lead_rw * 8` (or `lo` when `lead_rw = 0`). The merge rewrites
every entry with `B_j ∈ (run_header, f]` to `f`. The final carry rewrites its
entries to `heap_size`. These are the entries the segments wrote
provisionally. The merge runs after the join, so it races with nothing. At
most one entry per 64 KB of joined run is rewritten.

**The allocator, for balance only, O(1) per allocation.** When it carves a
header at `p` from a free block at `hd`: let `j = ⌊(p − Z) / 64 KB⌋`. If
`hd < B_j`, set `T[j] = p`. This is exact for every window that receives a new
header. Entries for windows that lie entirely inside the shrunk free block keep
their old value. That value is still a walk position, and those windows hold
one free block, so they carry no work. Doing nothing at all is also correct,
but then the first collection on a fresh heap gets a single segment: every
entry is `heap_size` until the first sweep.

**Alternative semantics, for comparison:** `T[j]` = the header of the object
*containing* `B_j` (a block-offset table, as in HotSpot). Right-justified
carving then needs O(1 + wz / 8192) exact updates, because only boundaries
inside the new object change. A cut is the containing header, which is also a
walk position. Either semantics proves the same way; the choice is about
balance and the allocator's footprint.

### 3.3 The bitmap

- The segments read bits only at headers in their own range.
- **Clearing (fix for R1): clear in bulk, after the join.** Once every segment
  has finished, each worker `memset`s the bitmap words it owns, by word index.
  This adds one parallel pass over `heap_size / 64` bytes. In Pulse, the
  segments then hold a fractional read permission on the bitmap, the full
  permission returns at the join, and the clear can be stated as "bitmap all
  zero" with ordinary array ownership. Two other fixes would work. One is
  `atomic_fetch_and` per bit, which costs one locked RMW per live object; the
  proof would need an atomic invariant. The other is to cut on 256-byte
  boundaries, which the table cannot guarantee.
- The bitmap must be all zero when the mark starts. Two things depend on it:
  the mark's "bit set means do not scan" test, and the sweep's reading of
  "bit set" as "live".

## 4. Scenarios, step by step

### 4.1 A free block spanning a cut

A *block* cannot span a cut: under `table_ok`, every cut is a header. A *free
run* (consecutive free or dead objects) can span one, and the model handles it.

```
Z+0xFFC0  A  live, wosize 3        (ends Z+0xFFE0)
Z+0xFFE0  D1 dead, wosize 3        (ends Z+0x10000)
Z+0x10000 D2 dead, wosize 7        (ends Z+0x10040)   ← T[1] = Z+0x10000 = cut
Z+0x10040 S  live
```

1. Segment 0 ends with `trail = (fb = Z+0xFFE8, rw = 4)`. It writes `T[1] =
   Z+0x10000` provisionally, since `B_1 ∈ (lo0, hi0]` and `B_1` is in its
   trailing run.
2. Segment 1 starts at D2: `lead = (Z+0x10008, 8)`, then the survivor S.
3. Merge: `carry + lead = (Z+0xFFE8, 12)`, one run. `flush_blue` writes the
   header `wosize 11, blue` at `Z+0xFFE0` and the link at `Z+0xFFE8`. Both
   writes fall in segment 0's range, after the join. The header at
   `Z+0x10000` is no longer a walk position.
4. Merge, table: `B_1 = Z+0x10000 ∈ (Z+0xFFE0, Z+0x10040]`, so `T[1] :=
   Z+0x10040` (S).

The result equals the sequential sweep's: one free block `[Z+0xFFE0,
Z+0x10040)`. This is the theorem.

### 4.2 Coalescing across a cut, with the merge's table fix missing (R2)

Take the same heap as §4.1, but suppose the merge does not rewrite `T[1]`, so
`T[1]` stays `Z+0x10000`. The next cycle proceeds like this:

1. The mutator promotes a wosize-3 object N. The free list reaches `F =
   [Z+0xFFE0, wosize 11)`. The leftover is 8, so F shrinks to wosize 7, ending
   at `Z+0x10020`. N's header goes at `Z+0x10020`, covering
   `[Z+0x10020, Z+0x10040)`.
2. A wosize-2 object M follows. The leftover is 5, so F shrinks to wosize 4,
   ending at `Z+0x10008`. M's header goes at `Z+0x10008`.
3. The word at `Z+0x10000` is now the last field of F. Nothing zeroes free
   blocks (#33), so it still holds D2's old header: wosize 7, white.
4. The next sweep cuts at `Z+0x10000`. Segment 0 walks to F at `Z+0xFFE0`.
   F's wosize is 4, so the next header is at `Z+0x10008`, which is past `hi`.
   The walk stops there: F becomes `trail = (Z+0xFFE8, 5)` and extends past
   the cut.
5. Segment 1 reads the stale header at `Z+0x10000`, wosize 7, bit clear (no
   live object has its header there). It takes `[Z+0x10000, Z+0x10040)` as
   one dead object: `lead = (Z+0x10008, 8)`. **M's and N's headers are never
   read.**
6. Merge: `(Z+0xFFE8, 5 + 8)`. The header goes at `Z+0xFFE0` with wosize 12,
   and the block lands on the free list. **M and N are live, but now lie
   inside a free block**: the next allocation overwrites them. This is a
   use-after-free, reachable from safe OCaml.

The same holds if an allocation writes data over `Z+0x10000` instead. The
"header" is then arbitrary bits, and segment 1's walk goes anywhere. In the
proof, step 4 is where `valid_bounds` fails. So this bug can only come from
unverified table code. The table updates therefore belong in the verified
sweep and merge, not in C beside them.

### 4.3 Table entries after a merge across all-free segments

Take a free run that starts in segment 1's trailing run at `Z+0x1F000`, covers
all-free segments 2 and 3, and ends at segment 4's first survivor
`f = Z+0x52000`. Before the merge, segment 1 has `T[2] = hi1` (provisional),
segments 2 and 3 have their entries at their `hi` (provisional), and segment 4
has `T[5] = f` (final).

The merge flushes one run `[Z+0x1F000, f)` and then rewrites `T[2], T[3],
T[4], T[5]` to `f`. That is every `B_j ∈ (Z+0x1F000, f]`. If it stopped at
segment 2's entries, `T[3]` and `T[4]` would name segment 3's and segment 4's
old cut headers, which are now inside the run: this is the R2 failure of §4.2.
Rewriting only from `results`, without reading the heap, needs the segment's
`lo`, or the first survivor's address added to `seg_result`. The rewrite costs
at most one entry per window of joined run. Over a heap of 88M words that is at
most 10,752 entries per collection.

A run that reaches `heap_size` rewrites its entries to `heap_size`. The cut
function then drops them. A big free block at the top of the heap therefore
gives fewer segments, never a cut inside the block.

### 4.4 Two segments clearing bits in one bitmap word (R1)

Take the cut at `Z+0x10010` (bit `0x2002`: word `0x100`, bit 2). Segment 0's
last live object L has its header at `Z+0x10000` (bit `0x2000`: word `0x100`,
bit 0).

| Step | Segment 0 (L) | Segment 1 (cut object) | `bitmap[0x100]` |
|---|---|---|---|
| 0 | | | `0b101` |
| 1 | `atomic_load` → `0b101` | | `0b101` |
| 2 | | `atomic_load` → `0b101` | `0b101` |
| 3 | `atomic_store(0b100)` | | `0b100` |
| 4 | | `atomic_store(0b001)` | `0b001` |

After the sweep, bit 0 is still set. In the next collection, L is live and the
mark reaches it. The bit at `v − 8` is set, so L is treated as already marked,
and its fields are never scanned. L's children that nothing else reaches stay
unmarked and are swept: a use-after-free.

All accesses are atomic, so this is not a C data race and ThreadSanitizer stays
silent. The lost update is a logic error. It needs a cut that is not 256-byte
aligned, with a marked header on each side within the same 32 words. Cuts come
from a 64 KB table and land on arbitrary headers, so with k ≥ 2 it happens on
most collections. Fix: §3.3.

### 4.5 A worker reading its cut while another updates the table

`par_sweep.c` already fills `bounds[]` before it starts any thread. The table
design must keep that: **the cuts are copied out of `T` before the workers
start**, because the workers write `T` (§3.2). If each worker instead read
`T[j_i]` to find its own start, it would read entries that its left neighbour
owns and may be writing: a C data race. The values written there are
provisional, but the read is still undefined behaviour. In Pulse, the
segments' ownership of disjoint index ranges of `T` rules this out.

### 4.6 Exact "first header" maintenance by the allocator (R3)

On a fresh heap of 88M words there is one free block, and table windows
1…10,751 all hold `heap_size`. Promotion carves the first object at
`p1 ≈ heap_size − 32` (right-justified). For every entry to be exactly "the
first header at or after `B_j`", windows 1…10,751 must all become `p1`. The
next object at `p2 < p1` requires the same rewrite again. That is about 10,000
writes per allocation until the block is used up; hamming does 1.6M
promotions. The O(1) rule of §3.2 avoids this, and stays exact wherever a
window receives a header (see the note there).

### 4.7 The mark-to-sweep and sweep-to-mutator handoffs

- **Mark to sweep:** BS workers are joined (`pthread_join`), and then the sweep
  threads start. That happens-before edge makes the relaxed bitmap reads
  ordered.
- **Sweep to mutator:** the sweep workers are joined, then the merge runs on
  the main thread, then the bulk clear's workers are joined.
- **Allocator against sweep:** both are stop-the-world, and promotion runs
  inside `gen_gc` before the mark. The allocator never runs during a sweep.
  A lazy or concurrent sweep would change that: the allocator's O(1) table
  write and the sweep's writes would then need an ownership protocol.

## 5. Proofs that change

| Area | Modules | Change |
|---|---|---|
| **Sweep** | `GC.Spec.SweepCoalesce.Defs`, `GC.Spec.Sweep`, `GC.Impl.FusedSweepCoalesce(.Lemmas)` | A bitmap sweep: `fused_sweep_coalesce_bm g bm`, proved equal to `fused_sweep_coalesce (recolor g bm)`, where `recolor` makes the headers with a set bit black. The precondition adds "bits only at headers; every live header white". The postcondition adds "bitmap all zero" and `table_ok` of the result. `fused_pre` and the existing equality are unchanged. |
| **Coalescing** | `GC.Spec.Coalesce`, `GC.Spec.Coalesce.Correct` (`walk_visits`), `.Shape`, `.Dense`, `GC.Impl.Coalesce` | `flush_blue` is unchanged. New lemma: the walk positions of `fst (fused_sweep_coalesce g)` are exactly the survivors' headers plus each run's first header. With it, the sweep and merge table rules give `table_ok`. Also new: `walk_visits` depends only on sizes, so it is unchanged by `recolor`. |
| **Parallel sweep** | `GC.Spec.SweepPar` (theorem), `.Join`, `.Local`, `.SegLoop`, `GC.Impl.SweepSegment`, `GC.Impl.SweepPar.Merge`, `GC.Impl.SweepPar.Prepass`, `GC.Impl.SweepPar(.fsti)`, `GC.Impl.HeapRange` | `sweep_par_correct` and `join_correct` stay, applied to `recolor g bm`. `sweep_segment` reads the bitmap (a fractional permission), no longer whitens, and writes its owned `T` range; its loop invariant and record gain the table facts, and locality extends to the bitmap bits. `merge` gains the joined-run table rewrite and its postcondition. `prepass` is replaced by `cuts_of_table`, proved `valid_bounds` from `table_ok` (dedupe, drop `heap_size`); its share arithmetic goes away. `sweep_par_seq` threads `T` and the bitmap, and adds the bulk clear. |
| **Allocator** | `GC.Spec.Allocator(.Lemmas.Split, .Dense)`, `GC.Impl.Allocator`, and its callers `GC.Gen.Impl.Promote`, `GC.Gen.Impl.Cheney`, `GC.Gen.Impl`, `GC.Gen.AllocExact` | For correctness, one lemma: `allocate` keeps every walk position (and adds `p`), so it keeps `table_ok`. If the allocator also writes the O(1) entry, `T` joins its footprint. Every caller, including promotion inside Cheney, must then frame it. That is mechanical but wide, so the allocator write could be delayed until balance needs it. |
| **gc_correct** | `GC.Impl.Correct` (mark-and-sweep), `GC.Impl.collect_with_roots`, and the generational `GC.Gen.Impl` (`gen_gc`) | New state on entry and exit: bitmap all zero and `table_ok`. `mark_post` is about header colours; for BS it becomes a bitmap statement ("bit set iff reachable header"). Composed through `recolor`, `gc_safe` and `gc_live` carry over unchanged, because the parallel sweep's result is *equal* to the sequential one (stronger than `heaps_agree_mod_free`). |
| **The mark** | `GC.Spec.Mark`, `GC.Impl.MarkBounded(*)` | BS is an unverified C prototype. Either it gets a proof of its own, or "the bitmap equals the reachable set" becomes a trusted assumption of the combined collector. That is the largest open item. |
| **Trusted C** | `par_sweep.c`, the hook in the extracted `GC_Gen_Impl.c` | The hook must now pass the bitmap and `T`. The thread code must still give each worker its own range and join before the merge. |

## 6. Estimate: whole collection at 4 threads, binarytrees 18

These are inputs from `docs/parallel-mark-prototype2.md`, measured on battery
with Low Power Mode on. Per collection, sequentially: whole 244.3 ms = mark
102.3 + sweep 141 + other (roots, minor) ≈ 1.0. BS at k = 4 gives a mark of
42.1 ms (2.43×) and a whole collection of 179.3 ms (1.36×). The bitmap sweep
costs the same as the verified sweep (ratio 0.97–1.02).

Model: `whole = 1.0 + 42.1 + σ + c1 × 141 / s4`.

- **σ (serial part)**: reading the cuts from `T` (microseconds), thread start
  and join (≈ 0.2 ms at k ≤ 4), the merge (≈ 0 on header-dense heaps; there is
  no zeroing since #33), and the table rewrites. Taken as 0.3–1 ms.
- **c1** is the cost of one thread's segments relative to the sequential
  sweep. Measured before #33: 0.92–1.20 (`all free` to `all live`). The
  byte-wise `read_word_r` costs extra, and the bitmap variant writes no
  survivor headers, which saves some. Range 1.0–1.4.
- **s4** is the 4-thread scaling of the segments. BS's mark scaled 3.79× from
  k = 1 to k = 4 (AS: 3.86×). A header walk is closer to a pure memory stream,
  so it may stop scaling earlier. Range 2.4–3.8.

| Case | c1 | s4 | Sweep, ms | Whole, ms | Speed-up |
|---|---|---|---|---|---|
| Sequential (now) | – | – | 141 | 244.3 | 1.00× |
| BS mark only (measured) | – | – | ≈ 136 | 179.3 | 1.36× |
| BS + par. sweep with table, optimistic | 1.0 | 3.8 | 37.4 | 80.5 | **3.0×** |
| BS + par. sweep with table, middle | 1.2 | 3.0 | 56.9 | 100.0 | **2.4×** |
| BS + par. sweep with table, pessimistic | 1.4 | 2.4 | 83.3 | 126.4 | **1.9×** |
| Ideal parallel sweep (c1 = 1, s4 = 4, σ = 0) | 1.0 | 4.0 | 35.3 | 78.4 | 3.1× |
| BS + par. sweep with `prepass` (middle) | 1.2 | 3.0 | 56.9 + P | 185–241 | 1.0–1.3× |

`P` is `prepass`'s serial walk over every header. On generated header-dense
heaps it took 0.6× the time of the pre-#33 sequential sweep, and #33 made the
sweep itself about one such walk. For binarytrees 18, 0.6–1.0 × 141 ms is
taken. That is the reason for (d): without the table, the parallel sweep's
serial pre-pass costs about as much as the time it saves. Even with the sweep
free, the mark limits the speed-up to 244.3 / 43.1 = 5.7×.

The parallel sweep has never been timed on a binarytrees 18-sized heap. On the
repository's test programs it was slower than sequential at every thread count
(their heaps have few headers). The middle case therefore needs the
measurement from the prototype report's §6 before it is relied on.

## 7. Open points

- `seg_result` lacks the first survivor's address, which the merge's table
  rewrite needs. It can be derived from `lead_fb`, `lead_rw` and `lo`, but `lo`
  is not in the record today (`merge` takes no bounds).
- The table's size and stride: at 64 KB there are 2,048 entries for a 16M-word
  heap, and 64 pieces at most (`MAX_PIECES`).
- The bulk clear is a third parallel pass. If its cost shows, clearing
  inside the segments with ownership aligned to 256 bytes needs cuts at
  256-byte boundaries, which header cuts cannot give.
- Moving the table writes into F\* adds `T` to the extracted sweep's
  signature, so the hand-added hook in `GC_Gen_Impl.c` must change with it.
