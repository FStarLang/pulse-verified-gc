# Design: a parallel mark and a parallel sweep for the page allocator

Branch `sheera/pages-parallel`, from `origin/sheera/pages-allocator`
(`3bc6b042`). **Design only; no code is changed.** For review before any
stage starts.

**The project rule** (from `docs/pages-allocator-proof-plan.md`, applied
here): the Pulse code is as fast as a fast C prototype of the same
algorithm, at most 5% slower on each workload, and is proved to compute
exactly an F\* model's function, or to meet the same theorems where it makes
a different valid choice. Code is never made slower for verification, and no
theorem is weakened to fit the code.

**Sources.**
- The page plan, `docs/pages-allocator-proof-plan.md` (§§9–17 as built).
- The parallel mark prototype report,
  `origin/sheera/parallel-mark-proto2:docs/parallel-mark-prototype2.md`, and
  its code, `generational/ocaml-integration/verified_gc/par_mark2.c` (BP:
  l.137–147 packets and pool, l.194–216 claim, l.380–393 share, l.470–541
  idle loop and termination, l.555–587 roots).
- The page prototype's parallel sweep: `verified_gc/proto/alloc_pages.c` on
  `origin/sheera/alloc-pages-proto` (`chunk_bounds` l.689–702, `lists_install`
  l.427–464, `sweep_range` l.405–425), with its thread pool and chunk counter
  in `proto_common.c` l.325–424.
- `origin/sheera/parallel-sweep` (`GC.Spec.SweepPar`, `GC.Impl.HeapRange`,
  trusted `par_sweep.c`), `origin/sheera/parallel-mark` (the ownership model
  O, its `work_in_flight` argument), `fork/sheera/spike-parallel` (the
  extraction spike and its five issue drafts), and
  `docs/parallel-gc-combined-design.md` on `parallel-mark-proto2` (BS for the
  free-list allocator).
- This repository's F\*: `fstar/`, nightly 2026-10-17, commit `f43a1127`.

**Labels.** *Measured* numbers name their report. *Estimate* marks guesses.

---

## 0. Summary

1. **Mark: BP, with the marks in one bitmap laid out by page.** One bit per
   heap word, in 32-bit words. Page *i*'s bits are bitmap words
   `[i·128, (i+1)·128)` at 32 KB pages (64 at 16 KB), so the bitmap is at
   the same time one global array (what the mark indexes) and a slice per
   page (what the sweep owns). The heap is never written during the mark,
   so every worker holds a read-only share of it, and only the bitmap, the
   packets and a counter are shared and mutable. This is what makes BP
   provable where A (a header CAS) would put the whole heap in an invariant.
2. **The bdd fix: stop most shares and most lock acquisitions** (§1.3). One
   idle worker requests one share through an atomic flag, instead of every
   busy worker sharing every 32 entries; idle workers poll an atomic count
   and take the lock only when it is non-zero; and a persistent thread pool
   replaces per-collection thread creation. A sharded pool is the fallback
   if bdd still collapses. All of it is scheduling, invisible to the proof.
3. **Mark proof target:** the final bitmap is exactly the set of headers of
   objects reachable from the roots. With `with_marks g B` (the heap `g`
   with the headers in `B` coloured black), that gives
   `GcPillars.marked h_init (with_marks h_init B) roots` and
   `MarkPhase.mark_inv`, which are exactly the hypotheses of the existing
   `GcCorrect.gc_correct_gen`. The sequential mark meets the same
   `mark_post`, so the two mark the same set.
4. **Sweep: the page prototype's chunks, joined in address order** (§2).
   Chunk bounds are fixed before the threads start and moved past run
   continuation pages, so a run belongs to the chunk holding its head.
   Each chunk builds its own list fragments. A serial join splices the class
   fragments in ascending chunk order and the large fragments in descending
   order, which is exactly the order `sweep_all` leaves. Chunk bounds are page
   aligned, so no bitmap word is shared between chunks, and clearing the
   bits needs no atomics.
5. **Sweep proof target:** exactly `SweepAll.sweep_all (with_marks g B) st`,
   and the bitmap all zero. It rests on the two facts that `sweep_commute`
   rests on, `unit_frame` and `unit_local`, lifted from units to chunks,
   plus a new list-splitting lemma.
6. **No existing page proof changes** (§3). The sweep specifications keep
   reading header colours; only the Pulse sweep reads the bitmap, and its
   loop invariant is "the specification's heap is `with_marks` of the real
   heap and the bitmap still set".
7. **Toolchain** (§4): we upgrade to an F\* nightly after `bc02ebf`
   (FStar#4812), which makes the U32 `cas`, `read_atomic` and `write_atomic`
   truly atomic in C and realizes `SpinLock` in C. Four trusted primitives
   remain, in one file with a short specification each: a CAS and an
   atomic load on an array element (the bitmap), a pause hint, and fork/join
   of k workers (`par` does not extract with karamel). Fetch-and-add and the
   pool lock are verified code over `cas`.
8. **Effort, estimated:** 13–22k proof lines, plus 1–1.5k lines of C and
   about two weeks of prototype work and measurement (§7). **The main risk**
   is the Pulse proof of the mark loop against a shared invariant with ghost
   accounting of pending work (§8).

---

## 1. The parallel mark

### 1.1 The algorithm: BP as in the prototype

Kept from `par_mark2.c` BP, because it is what was measured:

- **No grey colour.** A mark entry is a field range, one word: first field's
  offset in the low 48 bits, length in the high 16. An object is claimed,
  then pushed as one range (several if it has more than 65,535 fields).
  When a range of more than CHUNK = 256 fields is popped, the rest is pushed
  back before scanning.
- **Claim:** set the object's header bit in the bitmap with a 32-bit CAS
  loop. The mark never writes the heap.
- **Bitmap-first test:** before reading a target's header, test the bit at
  `v − 8`. Only object headers' bits are ever set, so a set bit means
  marked, and an infix pointer (whose `v − 8` is an infix header, never set)
  goes on to be resolved to its closure. Without this test B was twice as
  slow as A (*measured*, report §2).
- **Packets:** each worker has an input, an output and a spare packet of
  PKT = 256 entries. It pops from the input and pushes to the output; when
  the input is empty the two swap. That is breadth-first in batches of 256,
  which made BP the fastest variant on livegraph (4.37× at k = 4) and
  markbench (7.91×) (*measured*, report §5).
- **Pool:** full packets are published to a pool under a lock; an idle
  worker takes one.
- **Roots:** the main thread claims each root and packs the entries into
  packets in the pool before the workers start.
- **Termination:** `work_in_flight` (§1.4).

### 1.2 Where the mark bits live

| Option | Mark cost | Sweep cost | Proof | Verdict |
|---|---|---|---|---|
| **One bitmap, bit per heap word, page-aligned slices** | one shift and mask from the address; no page-map read | page *i* reads and clears its own 128 words | the heap is read-only during the mark; each page's slice is owned by whoever sweeps it | **chosen** |
| Bit per slot, per page | needs the page's class to turn an address into a slot number: a page-map read per visit | fewer words | the same | rejected: an extra dependent load on every pointer visited |
| Bitmap inside each pool page (OCaml 5 has a pool header) | as the chosen one | as the chosen one | our pages have no header; slot 0 is at the page start (plan §1.3), so this changes the layout and every layout proof | rejected |
| Header colour, CAS on the header (A) | 1.0 (B/A is 0.79–1.62, *measured*) | whitens survivors in place | every heap word that holds a header becomes shared mutable state in an invariant, including what the sweep and mutator touch | rejected: not provable at a reasonable cost; the user chose BP |

**Layout.** `bm : array U32.t` of `heap_words / 32` words, outside the heap,
allocated with the page map at heap creation. Bit `j` of word `w` is heap
word `32·w + j`, counted from `zero_addr`. Since `page_wsize` is a multiple
of 32 (4096 or 2048), page *i* is exactly words
`[i · page_wsize/32, (i+1) · page_wsize/32)`. That is 1/64 of the heap:
2 MB for a 128 MB heap. The heap's tail after the last page (plan §1.1) has
no object that can be marked, but its words are covered for simplicity.

**Invariant between collections:** the bitmap is all zero. The mark sets
bits; the sweep clears each swept page's slice. Free pages have no bit set,
because no object in a free page is reachable (`no_pointer_to_blue`), so the
sweep, which skips free pages, leaves them zero.

### 1.3 The pool-lock contention on bdd, and the fix

**What was measured** (report §5.3, bdd, BP at k = 8): 58% of worker time in
pool operations, 40% waiting for the lock, 34% of acquisitions contended;
1,767 of 1,822 publications per collection were *shares*. bdd's marks are
about 3 ms, so workers often run dry. In `par_mark2.c`:
- every busy worker checks, every 32 scanned entries, whether
  `idle_workers > 0 && nfull == 0`, and if so shares half its packet
  (l.530–535). With k − 1 busy workers, one idle worker can cause up to
  k − 1 shares, each a lock acquisition and a fresh small packet;
- the idle loop polls `nfull` and then calls `pool_take`, which locks; many
  idle workers race for the one packet just published;
- threads are created and joined per collection: 0.2–0.4 ms at k ≤ 4
  (report §5.3), a tenth of a bdd mark.

**The fix, in order. Each step is measured in the prototype (stage P0)
before the next is tried.**
1. **One share per request.** An idle worker sets an atomic
   `share_wanted` flag (CAS 0 → 1) instead of only incrementing
   `idle_workers`. A busy worker shares only when it wins a CAS of
   `share_wanted` from 1 to 0, and only if it holds at least `S_min`
   entries (start with 16). So each request causes one share, not up to
   k − 1.
2. **Test before lock.** Idle workers spin on the atomic `nfull` and call
   `pool_take` only when it is non-zero, with `pause` and then
   exponential back-off. `pool_take` uses `trylock` first; on failure it
   goes back to spinning on `nfull`. (The prototype already reads `nfull`
   without the lock; the change is to never block on the lock from the idle
   loop.)
3. **A persistent thread pool** for both the mark and the sweep, as the page
   prototype's `proto_common.c` already has (mutex and condition variables,
   job 0 on the caller, rebuilt after `fork`).
4. **Fallback: a sharded pool.** One pool per worker, each with its own
   lock. A worker publishes to its own shard and takes from its own first,
   then from the others starting at a random one, with `trylock`. This
   removes the single lock altogether. It is kept as a fallback because it
   changes the order in which work is taken, which may cost the
   breadth-first batches their advantage on livegraph and markbench.

**Acceptance (C prototype):** on bdd at k = 4, BP-fixed at least as fast as
BS (1.27× the sequential mark, *measured*); at k = 2 and 4 on every other
program, within 5% of BP as measured, or faster.

**Why the proof does not care.** The proof's invariant (§1.6) is about which
entries exist and who holds them, not about when they move. Who shares,
when, and from which shard are scheduling choices; each transfer is a step
that preserves the invariant. A sharded pool is *k* locks with the same
resource each, plus the counter.

### 1.4 Termination

As in the prototype, a sequentially consistent counter `work_in_flight`
counts the workers that hold work (entries, or a range being scanned) plus
the packets in the pool.
- Publishing adds 1 under the pool lock; taking a packet takes over its
  count. A worker gives up its own count when its input and output are
  empty. The main thread sets the initial count to the number of root
  packets before the workers start.
- **A 0 is final:** a count can only be added by a worker that holds one, or
  by publishing a packet, which needs entries, which needs a count. So once
  0 is read, no entry exists anywhere and no worker is scanning; every worker
  that reads 0 exits.
- This is the argument already proved in `origin/sheera/parallel-mark`'s
  `GC.Spec.MarkPar2.Count`/`Term` for the ownership design; the packet
  version is simpler (no inboxes).
- In the proof, the counter is part of the shared invariant (§1.6), and the
  fact needed at the end is: *counter = 0 ⇒ the pool is empty and every
  worker's pending set is empty and it is not scanning*.

### 1.5 Overflow

The prototype has no overflow: when a worker needs an empty packet and the
spare and the pool's empty list are exhausted, it `malloc`s one (l.356–369).
It aborts only if `malloc` fails.

**Design:** the same, in two steps.
- **First version, as the prototype:** packets come from a free list and are
  allocated on demand; packets are reused across collections. In Pulse,
  allocation is total (Pulse assumes `alloc` succeeds, as every Pulse array
  allocation in the collector already does), so this adds no new trust.
  Memory is bounded by the number of entries in flight, which in the worst
  case is about the number of marked objects.
- **Later, optional (stage M7):** a cap on the number of packets, beyond
  which a claimed object is not pushed and an atomic `overflow` flag is set.
  After termination, if the flag is set, a parallel rescan by pages pushes
  the unmarked children of every marked object, and the mark runs again.
  That is the sequential mark's overflow-and-rescan (PR #40), whose proof
  pattern carries over: the invariant gains "or the overflow flag is set".
  It is left optional because the sequential mark had no overflow on any
  measured program (report §5), and the prototype measured no cap.

### 1.6 The proof target and how to reach it

**The target.** For the heap `h` (unchanged by the mark) and the roots:

```fstar
(* after the parallel mark, with B the bitmap's set of marked addresses *)
forall (x: obj_addr). mem_graph_vertex (create_graph h) x ==>
  (hd_of x ∈ B <==> Seq.mem x (reachable_set (create_graph h) roots'))
/\ (forall a. a ∈ B ==> exists x. a == hd_of x)        (* only headers *)
/\ is_heap heap h                                      (* the heap is unchanged *)
```

From it, a new lemma `bitmap_marked` gives
`GP.marked h (with_marks h B) roots` and `MP.mark_inv (with_marks h B) st`,
the hypotheses of `GcCorrect.gc_correct_gen`. `marked` is
`Correctness.mark_post` plus the fields clause. Each of its clauses follows
from a recolouring: objects, wosizes, fields and `create_graph` do not
depend on colour; no grey because the heap had none (the sweep leaves white
and blue only, `gc_safe_pages`); `tri_color_invariant` from the closure
(a black object points only to black ones); `mark_inv` by
`MarkPhase.mark_inv_recolour`, once per marked object (or a set form of it).
**The sequential mark meets the same `mark_post`**
(`mark_satisfies_mark_post`, `mark_bounded_satisfies_mark_post`), so the
two marks colour exactly the same set: that is the sense in which the
parallel mark equals the sequential one. The heap the sweep sees is a
function of that set, so the whole collection is the same.

**The invariant** (over the read-only heap `h`):
- **I1, soundness:** every address in `B` is an object's header, and that
  object is reachable from the roots. Stable, because `B` only grows by
  claiming a target of a field of a marked object or a root.
- **I2, closure obligation:** for every marked object `x` and every pointer
  field `f` of `x` (resolved through infix headers as the sequential mark
  does) pointing to an object `y`: `y` is marked, or field `f` of `x` lies
  in a *pending* range. Pending ranges are those in a packet (a worker's
  input, output or spare, or the pool) or in the range a worker is scanning,
  from the field it has reached on.
- **I3, accounting:** `work_in_flight` = the number of workers whose pending
  set is non-empty or who are scanning, plus the packets in the pool.
- **At the end:** all workers have read 0 and exited. By I3 nothing is
  pending, so by I2 `B` is closed under fields. The roots were claimed
  before the workers started, so everything reachable is in `B`; with I1,
  `B` is exactly the reachable set.

**How it is held in Pulse.**
- **The heap:** each worker gets a fraction of `is_heap heap h`. This needs a
  fractional `is_heap` (today it is `pts_to h.data s` at full permission,
  `common/impl/GC.Impl.Heap.fst:79`): `read_word` gains an implicit `#p`
  defaulting to 1.0, with `share` and `gather`. That is source-compatible
  with every existing caller.
- **The shared invariant** (`Pulse.Lib.Inv`, opened with
  `with_invariants`; made cancellable with `CancellableInvariant` so that the
  main thread gets the bitmap back after the join) holds:
  - the bitmap array at full permission, and a ghost monotonic set `M`
    (`Pulse.Lib.MonotonicGhostRef`) equal to its set bits;
  - the counter;
  - the authoritative half of a ghost map `worker → multiset of pending
    ranges` (`Pulse.Lib.GhostPCMReference` over a map PCM), with I1–I3
    stated over `M`, the map and the counter.
- **Each worker owns** its packets and the fragment of the ghost map for its
  own id. The pool's lock owns the pool's packets and the fragment for a
  pseudo-worker "pool".
- **A field visit** is: an atomic load of the bitmap word (bitmap-first
  test), a read of the header from the heap fraction, and, if unmarked, the
  CAS. The CAS's invariant step adds `y` to `M` and `y`'s range to the
  worker's pending multiset in one atomic step, then a ghost step removes
  field `f` from the range being scanned. These steps are ghost: they cost
  nothing at run time.
- **Packet moves** (publish, take, share) are ghost transfers between a
  worker's fragment and the pool's, inside the lock, together with the
  counter update.
- **First as a model.** Before Pulse, the algorithm is modelled in F\* as an
  interleaving of atomic steps (stage M1), as `GC.Spec.MarkPar2` did for O:
  a state of bitmap, packets, pool and counter; a step relation with one
  case per atomic action; I1–I3 preserved by every step; termination.
  The Pulse invariant is then the model's invariant, and each Pulse atomic
  block is one model step. This finds mistakes in the invariant cheaply.

**A gap to close in the spike (P1):** each `with_invariants` costs one
`later_credit`. The per-visit cost must be ghost. If credits can only be
produced by a real step in this Pulse version, the invariant must instead be
a *non-later* form (e.g. an invariant over a timeless slprop, if this
version provides one); the spike checks which.

---

## 2. The parallel sweep

### 2.1 How pages are shared between threads

As the page prototype does it (`chunk_bounds`, `chunk_job`):
1. `start_sweep` as today (O(1): the epoch and the list heads).
2. **Chunk bounds, before the threads start**, on the main thread:
   `n_chunks = 8·k` (at most 64). Chunk *c* starts at
   `lo_c = ⌊c · n_pages / n_chunks⌋`, moved forward past every `LargeCont`
   page; `lo_{n_chunks} = n_pages`. So every chunk starts at a unit start
   (a free page, a pool page or a run head), and a run belongs to the chunk
   that holds its head, even if its pages reach into the next chunk.
   - Fixing the bounds before the threads start is what avoids the race the
     prototype found (report results §9.1): a run sweep splits runs and
     changes page kinds, so a thread must never read another chunk's page
     map while it is being written.
3. **Each chunk is swept by one thread**, which takes the next chunk from an
   atomic counter (dynamic) or is assigned chunks `t, t+k, t+2k, …` (static).
   *Choose by measurement in P0*: the prototype is dynamic, with a balance
   (slowest/mean) of 1.02–1.04 on big heaps (*measured*, results §9.8).
   Static is simpler to prove (no shared counter; §2.4); if it is within 5%
   of dynamic at k = 2 and 4 on every program, take it.
   *Outcome (P0, §9.3):* at k = 2 the two are equal. At k = 4, static's
   sweep is 5–27% slower on five programs, but by at most 0.2 ms, under 2%
   of a collection. Dynamic is recommended; S2 can start with static.
4. **What a chunk owns:** the heap words `[page_base lo_c, page_base
   lo_{c+1})` (including a run reaching past `lo_{c+1}`'s nominal start,
   which by construction is inside), the page-map entries `[lo_c,
   lo_{c+1})`, the bitmap words of those pages, and its result record
   `parts[c]`. It reads, shared, the class tables in `tw`.
   - **Page-aligned bounds mean no bitmap word is shared** between chunks (a
     page is 128 whole words), so the combined design's race R1 (two
     segments clearing bits in one word) cannot occur, and clearing needs no
     atomics.

### 2.2 Per-chunk results and the join

`parts[c]` holds, as the prototype's `lists_t`:
- per class `c'`: the head and tail of the chunk's pages with a free slot,
  in ascending page order (the sweep appends: `SweepStep.push_avail`);
- the head of the chunk's large fragment, and the address of its *open
  link*: the link field of the fragment's last listed block, which must
  later point to the rest of list 0;
- the lowest free page (for the free-page hint).

A chunk is swept exactly as `sweep_all` sweeps, but starting from empty
lists: pool pages appended to the fragment, runs linked in front of the
fragment's large head. The first run that lists a block is swept with head
0, and its last listed block's link is the open link.

**The join** (serial, on the main thread, after all chunks are done):
- **Class lists, ascending:** for each class, for each chunk in ascending
  order with a non-empty fragment, set the previous tail page's `next` to
  the fragment's head. The result is the class's pages in address order,
  which is what `sweep_all` leaves (§17.2).
- **List 0, descending:** `sweep_all` links each run in front of the list it
  is given, so a later run comes first, and each run's blocks are in address
  order within it. So list 0 is fragment `n−1`, then `n−2`, …, then 0: for
  each chunk in descending order, write the fragment's open link with the
  head of the next lower non-empty fragment (0 for the last).
- **The hint** is the minimum of the chunks' lowest free pages.
- Cost: `n_chunks × (n_cls + 1)` = at most 2,048 steps, about a microsecond.

This is the prototype's `lists_install`, whose comment says "a parallel
sweep leaves exactly what the sequential one does"; here it is a theorem.

### 2.3 The proof target

**Exactly `SweepAll.sweep_all (with_marks g B) st0`**, where `st0 =
start_sweep st`, as a heap and a `pstate`, and the bitmap all zero after.
With `gc_correct_gen`, the collection is then safe and live with no new
statement.

**The proof.**
1. **`sweep_range`**: `sweep_from` stopped at a unit boundary `hi`
   (`SweepAll.sweep_from` already walks from unit to unit). Splitting
   `sweep_all` at the chunk bounds is then `sweep_from` unfolded:
   `sweep_all = sweep_range lo_{n−1} n_pages ∘ … ∘ sweep_range 0 lo_1`.
2. **Range frame and range locality.** `sweep_commute` rests on two facts
   about one unit: `unit_frame` (it changes only its span's words and its
   pages' entries) and `unit_local` (what it writes depends only on those).
   By induction over the units of a range, the same holds for a range,
   *except for the lists*. `sweep_commute` itself is the two-unit case; the
   chunk theorem needs its two premises generalised, not the lemma.
3. **List splitting (new).** Sweeping a range from lists `L` equals
   sweeping it from empty lists, giving fragments `F`, then:
   - for each class, `L ++ F` (the old tail's `next` set to `F`'s head);
   - for list 0, `F ++ L` (the open link set to `L`'s head).

   The class half is `push_avail`'s append (`push_ok`, `chain_snoc`). The
   large half needs a specification form of the Pulse run sweep's
   `val_at_fp`: **`run_head_only`**, `SweepRun.sweep_run g pm i fp` and
   `sweep_run g pm i fp'` differ only at the last listed block's link, and
   return heads that differ only when the run lists nothing.
4. **The join lemma.** From 1–3: the chunks' results, each computed from
   the starting heap restricted to the chunk, joined as in §2.2, equal
   `sweep_all`. This is the statement the Pulse join proves it computes.
5. **The page map's hint and epoch** are not part of `pstate`'s view beyond
   `meta_ok` (§17); the join re-establishes `meta_ok` (no free page below
   the hint).

In Pulse, the parallelism is separation: each worker ends with its chunk's
words, entries and bitmap slice equal to the slice of `sweep_range` from
empty lists (by range frame and locality), and `parts[c]` describing its
fragments. The join gathers the slices (`pts_to_range_join`) and applies the
join lemma.

### 2.4 Dynamic chunks in Pulse, if measurement asks for them

Static assignment is `k` workers each owning a fixed set of chunks: an
iterated star of chunk resources split before the fork. Dynamic claiming
needs the chunk counter in an invariant:
`exists n. counter ↦ n ** (⊛ c ≥ n. chunk_res c) ** (⊛ c < n. claimed_or_done c)`.
A fetch-and-add moves chunk `n`'s resources out; a finished chunk puts its
result back with a `done c` token (a ghost map with authority in the
invariant). After the join, the main thread cancels the invariant and
knows every chunk is done. *Estimate:* 1–1.5k lines more than static.

---

## 3. How the sweep reads the bitmap, and which page proofs change

**Approach: the specification is not changed.** Every sweep specification
(`SweepPage`, `RunList.olds`, `SweepRun`, `SweepAll`) keeps reading
`color_at g a = Black`. A new specification module, `GC.Spec.Pages.Bitmap`,
defines:
- `bset : Type` (the bitmap's view, a sequence of `U32.t`) and `marked_at bs
  a`;
- **`with_marks g bs`**: `g` with every header whose bit is set made black;
- **`with_marks_unit`**: for a unit `i` whose bits are a subset of its
  objects' headers, `sweep_unit (with_marks g bs) pm i fp` equals
  `sweep_unit g' pm i fp` where `g'` agrees with `with_marks g bs` on the
  unit's words only (from `unit_local`), and its result has *no* black
  header and equals `with_marks` of the real result with that unit's bits
  cleared;
- `clear_page bs i`.

**The Pulse sweep's loop invariant** is then: *the specification's
intermediate heap equals `with_marks` of the real heap and the bitmap as it
is now*. Bits are cleared as pages are swept, so when the bitmap is all
zero the two heaps are equal.

**What changes in Pulse:**
- **`SweepPage.sweep_slots`:** the live test reads the slot's bit (an index
  computed from `slot_base`) instead of `get_color` of the header; a live
  slot is **not written** at all, since `colorHeader (black h) White == h`
  for the white header the real heap has. This is one load of a bitmap word
  per slot in place of the header load, and one store fewer per survivor.
  At the end the page's 128 bitmap words are zeroed (a 512-byte store). The
  prototype instead clears each bit as it reads it; P0 measures both and
  the faster is used.
- **`SweepRun`:** the same for `olds`'s live test and `hval`'s whitening of
  live blocks, and the run's pages' bitmap words zeroed.
- **`Sweep`:** a new `sweep_chunk` (range-restricted), `join`, and the
  worker entry; the existing `sweep_all` gains the bitmap and the
  `with_marks` invariant and stays as the k = 1 path.
- **Range-restricted heap and state access:** the chunk sweep owns only a
  slice of the heap, of `tpm`, and of the bitmap. `pool_step`'s and
  `run_step`'s signatures change from `is_heap heap g ** pages_st t st` to
  ranges (heap: `GC.Impl.HeapRange` from `origin/sheera/parallel-sweep`,
  ported; `tpm` and `bm`: `pts_to_range`; `tw`'s tables: a read-only
  fraction). Their postconditions become slice equalities, derived from the
  current whole-heap equalities by `unit_frame`/`unit_local`. The ghost
  ranges cost nothing at run time; the C must be the same loop.
- **`State`:** `pstate_t` gains `bm` (a third pointer). §17.2 found that
  pointers loaded per allocation cost; `bm` is not used by the allocator,
  so it can be a separate argument to the collector rather than a field
  loaded on the allocation path.

**Page proofs that change: none of the specification's.** New: `Bitmap`,
`SweepChunks` (§2.3) and `bitmap_marked` (§1.6). Changed in Pulse:
`SweepPage`, `SlotLemmas` (the `pend` relation gains `with_marks`),
`SweepRun`, `RunLemmas`, `RunMapLemmas` (map pass on a range), `Sweep`,
`State`, `Vacuity`; in `common/`: `GC.Impl.Heap` (fractional reads).

**Also unchanged:** the allocator (it does not read live colours,
`ColourFacts`), `start_sweep`, `gc_correct_gen`, `collection_cycle`.

**An alternative rejected:** restating `sweep_page_spec` and `olds` with a
`live` predicate parameter (header colour or bit). It would touch the ~40
specification files that mention `color_at`/`Black` (`Survive`, `GcPillars`,
`SweepUnits`, `Theorems`, …) for no gain over `with_marks`, which keeps them
as they are.

---

## 4. What F\* and Pulse provide, and what is missing

**Decision (2026-11-14): we will upgrade to an F\* nightly after commit
`bc02ebf`, which contains FStar#4812. Not yet:** the current toolchain stays
until stage P1. The design assumes the upgraded toolchain.

**What #4812 gives** (merged into F\* master early November 2026): the U32
`cas`, `read_atomic` and `write_atomic` of `Pulse.Lib.Primitives` become
truly atomic in C, and `Pulse.Lib.SpinLock` is realized in hand-written C.
In today's nightly (2026-10-17, `f43a1127`) they are
`Pulse.Lib.Core.as_atomic` (an assumption) over a plain read, compare and
write (`Pulse.Lib.Primitives.fst` l.30, 33, 62), and `write_atomic` even
loses its store when extracted (spike issue 1). All of them are on a
`ref U32.t`, not on an array element.

**After the upgrade.**

| Need | Provided after the upgrade | Remaining trusted primitive, or how it is built |
|---|---|---|
| 32-bit CAS on a bitmap word | `cas` on a `ref U32.t` only; a bitmap of one `ref` per word is not a flat array (`Pulse.Lib.Reference.Array` only goes from a ref to an array) | **trusted `cas_cell`** (below) |
| atomic load of a bitmap word (the bitmap-first test, concurrent with CASes; a plain load would be a data race in C) | `read_atomic` on a ref only | **trusted `load_cell`** (below) |
| fetch-and-add/sub (termination counter, chunk counter) | none | **not trusted:** a verified CAS loop over the upgraded `cas` on a `ref U32.t`. The counter moves only at publish, take and idle transitions, and the chunk counter once per chunk, so a CAS loop costs the same as `lock xadd` there. P0 measures it in the prototype |
| the pool lock, with `try_acquire` (§1.3) | `SpinLock` in C, but its interface has no `try_acquire` | **not trusted:** a verified test-and-test-and-set spin lock over the upgraded `cas` (`try_acquire` is one `cas`). P0 measures it against the prototype's `pthread_mutex_t`; if it is slower, `try_acquire` is added to the trusted file instead |
| back-off in spin loops | none | **trusted `cpu_pause`** (below): no logical effect, extracted as `_mm_pause()` |
| fork/join of k workers | `Pulse.Lib.Par.par` passes closures and karamel drops it; `fork_core` has no realization; `Pulse.Lib.Task` crashes karamel (spike issue 4). #4812 does not change this | **trusted `run_workers`** (below), monomorphic, as Spike 2's `par_env` (polymorphic assumes are not extracted, spike issue 5) |
| invariants, ghost state | `Pulse.Lib.Inv` (`with_invariants_a`, costs a `later_credit`), `CancellableInvariant`, `GhostPCMReference`, `MonotonicGhostRef`, PCM maps | enough; the later-credit cost to be checked (§1.6) |
| array splitting | `pts_to_range_split/join/share/gather`, `pts_to_mask` with `split_mask`/`join_mask`, `ArrayPtr.split` | enough |
| memory order | all seq_cst (#4812's C uses `__ATOMIC_SEQ_CST`) | fine on the test machine: on x86 a seq_cst CAS is `lock cmpxchg` and a seq_cst load is a `mov`, the same instructions as relaxed; only seq_cst stores cost (`xchg`), and there are none on hot paths. On ARM this would cost; out of scope |

**The trusted primitives, all in one file** (`GC.Impl.Par.Trusted.fsti`,
with its C in `gc_par_trusted.c`, extracted with `-library`), each with a
short specification. Nothing else in the parallel collector is trusted
beyond what F\* and Pulse themselves trust.

```fstar
(* Atomically: if a.(i) = u then a.(i) <- v.  Used inside with_invariants. *)
val cas_cell (a: array U32.t) (i: SZ.t) (u v: U32.t) (#s: erased (Seq.seq U32.t))
  : stt_atomic bool #Observable emp_inames
      (pts_to a s ** pure (SZ.v i < Seq.length s))
      (fun b -> if b then pts_to a (Seq.upd s (SZ.v i) v) ** pure (Seq.index s (SZ.v i) == u)
                     else pts_to a s)
      (* C: __atomic_compare_exchange_n(&a[i], &u, v, false, SEQ_CST, SEQ_CST) *)

(* Atomically read a.(i), with any fraction. *)
val load_cell (a: array U32.t) (i: SZ.t) (#p: perm) (#s: erased (Seq.seq U32.t))
  : stt_atomic U32.t #Observable emp_inames
      (pts_to a #p s ** pure (SZ.v i < Seq.length s))
      (fun x -> pts_to a #p s ** pure (x == Seq.index s (SZ.v i)))
      (* C: __atomic_load_n(&a[i], SEQ_CST) *)

(* A spin-loop hint; no logical effect. *)
val cpu_pause (_: unit) : stt unit emp (fun _ -> emp)       (* C: _mm_pause() *)

(* Run f on each of the k environments, f envs.(0) on the calling thread and
   the others on the pool's threads, and return when all have returned.  One
   instance per environment type (mark, sweep), since an assumed val cannot
   be polymorphic. *)
val run_workers_mark (k: SZ.t{SZ.v k >= 1}) (envs: array mark_env)
  (pre post: nat -> slprop) {| forall i. is_send (pre i) |} {| forall i. is_send (post i) |}
  (f: (i: SZ.t) -> stt unit (pre (SZ.v i)) (fun _ -> post (SZ.v i)))
  : stt unit (on_range pre 0 (SZ.v k)) (fun _ -> on_range post 0 (SZ.v k))
      (* C: the persistent pthread pool of proto_common.c *)
(* run_workers_sweep: the same, for sweep_env. *)
```

So after the upgrade, **four trusted primitives remain**: the array-element
CAS, the array-element atomic load, the pause hint, and fork/join (one
declaration per environment type). Fetch-and-add and the lock are verified
code over #4812's `cas`, unless P0 shows that costs time, in which case
`fetch_add_u32` or `try_acquire` joins the file with a specification of the
same size. P1 checks the exact form of the `is_send` instances and of
`on_range` (an iterated star) in the upgraded Pulse.

**Until the upgrade**, none of these extract correctly; P1's spike can be
done on the new nightly in a scratch worktree, so that the upgrade of the
main build stays a separate step.

---

## 5. The C prototype to match

**Built in stage P0, on a prototype branch** (`sheera/pages-parallel-proto`
from `origin/sheera/alloc-pages-proto`, with `par_mark2.c` brought over),
unverified, for measurement only:
- the mark: `par_mark2.c`'s BP, with the bitmap laid out as §1.2, the fix of
  §1.3, and the persistent pool;
- the sweep: `alloc_pages.c`'s parallel B2 sweep (chunks, `parts`,
  `lists_install`), with `sweep_pool` and the large-area sweep reading and
  clearing the bitmap instead of header colours, and writing nothing for a
  survivor;
- the checks the prototypes already have: `VGC_PAR_MARK_CHECK` (bitmap
  against the sequential mark's headers, set-bit count equal), the
  prototype's oracle (the sweep's heap and lists byte for byte against the
  sequential verified sweep's), the negative controls (flip a bit; a plain
  read-modify-write in place of the CAS), and ThreadSanitizer.

**What it is compared with.**
- **The project rule's comparison:** the extracted Pulse code against this
  prototype, same algorithm, at k = 1, 2, 4, ≤ 5% slower on each.
- **For the design:** the prototype against the sequential collector
  (header mark, sequential page sweep), and against the existing
  measurements of BP and B2 par.

**Two benchmark levels.**
1. **`mark-and-sweep/pages-c/bench`, extended** (as §17 did for the
   allocator): the extracted C and the prototype linked into one driver,
   each workload in its own process, alternated, medians.
   - New workloads, at k = 1, 2, 4: `psweep10/50/90` (today's sweep
     workloads, with bits set in the bitmap instead of header bits, l.141);
     `pmark-tree` (binary trees), `pmark-graph` (a random graph, like
     livegraph), `pmark-wide` (large arrays, to exercise CHUNK splitting),
     `pmark-short` (a small live set, about 1 ms, bdd-like, for the pool);
     and `pcollect` (mark then sweep).
2. **Programs on the runtime**, after 5b connects the page allocator: the
   eight of the mark report (binarytrees 16 and 18, livemap, livegraph,
   markbench, minilight, bdd, fft), at k = 1, 2, 4, 3 runs each, on mains
   power with `caffeinate`, mark, sweep and whole-collection times and run
   time. Thread counts 8 are not required (4 cores, hyper-threaded).

**The k = 1 question.** With one thread, BP was 0.36–0.53× the sequential
header mark on binarytrees, livemap, minilight, bdd and fft, and faster on
markbench (2×) and livegraph (1.1×) (*measured*). **Decision (2026-11-14):
with one thread the collector uses today's sequential mark** (the verified
header mark, `MarkBounded`) with the existing, verified sequential page
sweep, both unchanged, **unless P0 shows that the sequential bitmap mark**
(gray stack, bitmap, no packets) **is as fast**. If it is, k = 1 uses the
bitmap mark and the bitmap sweep instead (a second, simpler mark to prove,
*Estimate:* 1–1.5k lines, reusing the I1/I2 argument without concurrency).

**Outcome (P0, §9.2):** the sequential bitmap mark is not as fast (0.55–0.93×
the header mark on seven of nine programs; faster only on fft). k = 1 keeps
the header mark and the header sweep.

---

## 6. Interaction with the sequential and incremental work

**The allocator interface is unchanged.** Allocation never runs during a
stop-the-world parallel collection; it does not read live colours
(`ColourFacts`); new objects are white; and the bitmap is zero between
collections, so `alloc_correct` and the `Idle` invariant need nothing new.

**Unchanged:** every specification module of the page allocator and sweep;
`gc_correct_gen` and the cycle; the Pulse allocator; `start_sweep`; the
minor collection; the header-colour sequential mark (`MarkBounded`) and the
header-colour Pulse sweep, which stay as the sequential configuration until
the k = 1 decision.

**Depends on 5b.** Running on the OCaml runtime needs stage 5b (threading
the page state through `gen_gc`, after akhil's merge). As in 5a, all the
parallel work goes in new modules and is extracted and tested in
`pages-c/` on its own, so it does not wait for 5b. Its runtime
integration does.

**With the incremental collector (plan §7):**
- **The sweep side composes.** Incremental sweeping sweeps one unit at a
  time with `sweep_page_correct`; the parallel sweep sweeps chunks of units.
  Both rest on the frame and locality of units. A per-page "swept" epoch
  already exists.
- **The mark side conflicts and needs a decision before the two lines
  meet.** akhil's incremental mark and its deletion barrier colour headers.
  With the marks in the bitmap: the barrier must set bits, an object
  allocated while marking gets its bit set (not a black header:
  `alloc_col`'s colour becomes "white plus a bit"), and akhil's
  `marking_inv` is restated over `with_marks`. Alternatively the
  incremental collector keeps header colours and only the stop-the-world
  collector uses the bitmap, at the cost of two sweeps. Not decided here.

---

## 7. Staged plan

*Estimates* in proof lines, new plus changed, as the page plan counts them.
Every stage ends with no admits on its modules, checked without `--retry`
and at the default rlimit, and with vacuity checks for each new invariant.

| # | Stage | Content | *Estimate* |
|---|---|---|---|
| P0 | C prototype | §5's prototype; the bdd fix in steps; static vs dynamic chunks; bit clearing per bit vs per page; the sequential bitmap mark for k = 1. Checks, controls, TSan. Measure k = 1, 2, 4 on the eight programs. **Gate:** the decisions in §5 and §2.1 | 4–6 days, no proofs |
| P1 | Primitives spike | On a nightly after `bc02ebf`, in a scratch worktree: the trusted file of §4 with its C; the verified CAS-loop counter and spin lock over #4812's `cas`; `run_workers` over the pool; a two-thread toy (counter + bitmap CAS + lock) proved, extracted, run under TSan; the later-credit question. The main build's upgrade is a separate step | 2–4 days, 0.3k F\*, 0.3k C |
| S1 | Sweep specification | `Bitmap` (`with_marks`, `with_marks_unit`); `SweepChunks` (`sweep_range`, range frame and locality, `run_head_only`, list splitting, the join lemma) | 2–3.5k |
| S2 | Pulse sweep | Fractional and range heap access; the bitmap in `sweep_slots` and the run sweep; `sweep_chunk`, `join`, workers (static first); `sweep_all` on the bitmap for k = 1. Extract; `pages_test.c` extended; `psweep*` workloads within 5% of P0's sweep | 2.5–4k, + 0.3k C |
| M1 | Mark model | Interleaving model of BP (§1.6): steps, I1–I3, termination, `B` = reachable; `bitmap_marked` to `GP.marked` and `mark_inv` | 3–5k |
| M2 | Pulse mark | Worker loop, packets, pool, share rule, counter, roots; the invariant and ghost map; `run_workers`. Extract; tests; `pmark*` within 5% of P0 | 4–7k, + 0.3k C |
| T | Tests | Differential test at every collection (bitmap against the sequential mark's black set; heap and lists against the sequential sweep), TSan, the prototype's controls on the extracted C; mutants rejected by proof (`tools/try-module.sh`) and tests: a plain RMW for the CAS, a skipped claim, a missing push-back of a split range, a chunk bound not moved past `LargeCont`, class fragments joined descending, a counter decrement before the output is empty | 0.5–1k C and scripts |
| E | Efficiency pass and measurements | As §17: every workload within 5% of P0 at k = 1, 2, 4, by changing code and re-proving, never by weakening; then the programs after 5b | 1–2 weeks |
| M7 | Optional: overflow cap and rescan | §1.5 | 1.5–2.5k |

**Total, estimated:** 13–22k proof lines without M7. **Order:** P0, P1,
then the sweep (S1, S2) before the mark (M1, M2). The sweep is lower risk,
is useful on its own (it can be tested with bitmaps set by the test, and it
can also run after the sequential mark if that writes bits), and builds the
range-access layer the mark's reads reuse.

---

## 8. Main risks

1. **The Pulse proof of the mark** (M2): a fine-grained invariant opened at
   every claim, with a ghost map of pending ranges, in a Pulse whose
   concurrency libraries this repository has never used. The model (M1)
   reduces the risk to the Pulse encoding; the spike (P1) to the
   primitives. If the later-credit cost or the invariant encoding proves
   unworkable, a fallback is a coarser invariant: the claim stays a CAS but
   pending work is accounted per packet, not per range.
2. **The bdd fix may not be enough** without the sharded pool, and the
   sharded pool may lose the breadth-first advantage on livegraph and
   markbench. P0 decides before any proof.
3. **k = 1 is slower than today's sequential mark** with BP (0.36–0.53× on
   five programs, *measured*). Needs the decision in §5.
4. **Toolchain:** the upgrade to a nightly after `bc02ebf` is needed before
   any parallel Pulse code extracts, and it may touch the existing build
   (#4812 also renames Pulse's model files). Four trusted primitives remain
   after it (§4); fork/join is the largest.
5. **Range-restricted signatures** for `pool_step`, `run_step` and their
   loops may cost the §17 performance (register pressure was already an
   issue: `sweep_slots` is kept out of line). The C must stay the same loop;
   S2's acceptance checks it.
6. **Merging with the incremental line** (§6): the bitmap and header
   colours have to be reconciled before an incremental parallel collector.
7. **Measurement noise:** the mark report saw a 20–25% unexplained shift
   between sessions on binarytrees 18. Compare only within one session, with
   alternated binaries, as `bench.sh` does.

---

## 9. Stage P0 results (2026-11-14)

### 9.1 What was built and checked

**Where.** The prototype is in worktree `~/Documents/pgc-pages-par-proto` on branch
`sheera/pages-parallel-proto`, uncommitted, under `generational/ocaml-integration/`:
- **`verified_gc/proto/par_mark_pages.c`** (new). It has three marks, chosen with
  `VERGC_MARK`:
  - `hdr`: the sequential header mark;
  - `bm`: the sequential bitmap mark (a growable gray stack and a plain claim);
  - `bp`: BP with the §1.3 fixes (step chosen with `VERGC_BP_FIX`=0/1/2; the
    default is 2), on the persistent pool, with the mutex or spin pool lock and
    a locked or CAS work counter.
- **`alloc_pages.c`**: the page sweep reads and clears the bitmap. It writes no
  live header. `VERGC_BM_CLEAR` chooses how the bitmap is cleared:
  - `page` (the default): memset the page's slice if the page has a survivor;
  - `bit`: clear each bit.
- **`proto_common.c`**: `VERGC_CHUNKS=static` gives the sweep's static chunk
  assignment.

**Checks.**
- **Check matrix: 97 of 97 runs pass.** The matrix is 12 configurations on
  eight programs, plus bt18 with BP at k = 4. The configurations include
  PKT = 2 or 4 and CHUNK = 1 or 4, to force splitting and sharing. Each run
  checks every major collection:
  - the bitmap equals the verified mark's black set;
  - the heap and lists after the sweep are byte-equal to the verified sweep's;
  - the bitmap is zero after the sweep;
  - the program's output equals stock OCaml's.
- **Negative controls, all rejected:**
  - a flipped bit (mark control);
  - three sweep mutants, the third of which skips the slice memset.
- **ThreadSanitizer** (`tests/pagespar/build_tsan.sh`): clean on bdd, livegraph
  and bt14 across the variants. The race control (a plain read-modify-write
  in place of the CAS) is reported.

### 9.2 Timings

**Method.** Tag `p0a`, 3 runs each, medians. The tables give ms per major
collection, with the speed-up over the sequential page collector (header
mark, k = 1) in brackets. hamming does a single major collection, so it was
run for correctness only.

**Whole collection** (mark + sweep + the rest):

| program | majors | bm k=1 | bp k=1 | bp k=2 | bp k=4 | hdr mark, k=4 sweep |
|---|---|---|---|---|---|---|
| bt16 | 58 | 0.71 | 0.66 | 1.15 | 1.74 | 1.27 |
| bt18 | 33 | 0.72 | 0.66 | 1.29 | 2.58 | 1.67 |
| livemap | 14 | 0.80 | 0.92 | 1.58 | 2.55 | 1.07 |
| livegraph | 4 | 0.94 | 1.19 | 2.27 | 4.10 | 1.02 |
| markbench | 5 | 0.84 | 2.13 | 4.40 | 7.98 | 1.02 |
| minilight | 1110 | 0.95 | 0.85 | 1.20 | 1.52 | 1.02 |
| bdd | 329 | 0.94 | 0.79 | 1.16 | 1.34 | 1.04 |
| fft | 33 | 1.16 | 0.71 | 1.03 | 1.35 | 1.05 |

**Mark only, k = 1:**

| program | hdr ms | bm | bp |
|---|---|---|---|
| bt16 | 23.9 | 0.55 | 0.49 |
| bt18 | 97.6 | 0.55 | 0.48 |
| livemap | 66.5 | 0.73 | 0.87 |
| livegraph | 164.0 | 0.93 | 1.20 |
| markbench | 2184 | 0.83 | 2.15 |
| minilight | 1.22 | 0.88 | 0.74 |
| bdd | 2.98 | 0.91 | 0.73 |
| fft | 18.3 | 1.55 | 0.50 |

**Run time (wall clock).** At k = 4, run time improves by 0–16%, except on
markbench (4.1×), because collection is a small share of most programs' run
time.

### 9.3 Decisions and findings

1. **One thread: keep the sequential header mark** and the header sweep, as
   decided in §5.
   - The bitmap mark is 0.55× the header mark on binarytrees, 0.73–0.93× on
     livemap, livegraph, markbench, minilight and bdd, and faster only on fft
     (1.55×). Its whole collection loses on the same seven programs.
   - BP at k = 1 is faster than the header mark on markbench (2.15×) and
     livegraph (1.20×), as in the mark report. The cause is not diagnosed:
     bm's bitmap and claim do not explain it, since bm is slower there.
2. **Chunks: dynamic recommended, by a small margin.** All figures are
   sweep ms, k = 4, static against dynamic.
   - At k = 2 the two are equal.
   - At k = 4 static is slower on seven of nine programs:

     | program | static | dynamic |
     |---|---|---|
     | bdd | 0.19 | 0.15 |
     | minilight | 0.16 | 0.14 |
     | livegraph | 2.86 | 2.66 |
     | fft | 2.79 | 2.62 |
     | bt16 | 4.50 | 4.26 |

     - It ties on livemap and is slightly faster on bt18 and markbench.
     - That is 5–27%, more than the 5% gate of §2.1, though under 2% of a
       collection.
   - Noise: mark times, which chunks do not affect, differ by up to 10%
     between the same two configurations. So only the consistent direction
     is evidence.
   - Dynamic costs 1–1.5k lines (§2.4) and needs fetch-and-add. After the
     `bc02ebf` upgrade, that is verified over `cas` and is not a new trusted
     primitive.
   - Plan: S2 proves static first, then adds dynamic.
3. **The bdd fix works; the sharded pool is not needed.** Figures are bdd,
   k = 4, per collection:

   | step | mark ms | shares | contended / acquisitions |
   |---|---|---|---|
   | 0 | 2.57 | 938 | 541 / 3,103 |
   | 1 | 2.24 | 455 | 312 / 1,714 |
   | 2 | 2.02 | 217 | 38 / 843 |

   - With step 2, BP's mark is 1.48× the sequential mark (acceptance: at
     least 1.27×) and its whole collection 1.34×.
   - Against step 0 (BP as measured), step 2 is within 5% or faster on six
     of eight programs:
     - faster on livemap (+11%), bt16 (+8%), livegraph (+6%), minilight
       (+6%) and markbench (+4%);
     - equal on bt18.
   - **Open: fft.** Step 2 is 15% slower than step 0 there (11.3 against
     9.8 ms). fft publishes 9 packets a collection, so with one share per
     request and `S_min` = 16 entries, idle threads starve. A likely
     remedy, to try in E: count `S_min` in fields, not entries, since one
     range entry holds up to 256 fields. hamming also favours step 0, but
     that is one collection and one sample per run.
4. **The spin lock and CAS counter cost nothing measurable.** The
   configuration that #4812's verified spin lock and a CAS-loop counter will
   give is within noise of the mutex on every program: −4% to +4%, and fft
   +7%. The design's trusted list (§4) stands.
5. **Clearing per page beats clearing per bit.** The sweep is 1.11–1.47×
   faster with per-page clearing on six programs and equal on binarytrees.
   Per page is kept.
6. **The bitmap sweep alone is faster than the header sweep** at k = 1
   (1.03–1.68× on seven of nine programs; equal on bt16, and slower on
   hamming's single collection), because it writes no live
   header. That is not enough to repay the bitmap mark at k = 1.
7. **New risk: at k = 2, BP's mark only equals the header mark** on
   binarytrees and fft (0.91–0.98×, since BP is about 0.5× per thread
   there). The k = 2 collection still wins (1.03–1.29×), thanks to the
   parallel sweep.
   - A header mark with a parallel sweep (header colours) would be about as
     good at k = 2 on bt18, but it would mean a second parallel sweep to
     prove. Not recommended.
   - The per-thread cost of BP (the bitmap is a separate cache line from the
     object it marks, plus the CAS and the packets) is what E must keep
     within 5%; it is not something to remove.
