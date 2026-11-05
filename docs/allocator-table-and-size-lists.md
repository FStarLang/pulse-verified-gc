# Object-start table and size-segregated free lists: design

This is step 1 of three: the allocator now, then the parallel mark, then the
parallel sweep. It began as a design-only note, based on `origin/main`
(`1ecb000`). §0.1 records the review's decisions, and §7 records part B as
built. It builds on
`docs/parallel-gc-combined-design.md` on `sheera/parallel-mark-proto2`
(referred to below as *the combined design*). That note analyses the
object-start table as part (d) of a parallel sweep.

- **Part A** is an object-start table `T` for the major heap. It is kept valid
  now, so that the later parallel sweep can take its cuts from it.
- **Part B** adds a separate exact-fit free list for each wosize from 1 to 16,
  with the current first-fit list kept for larger sizes. This fixes #44
  (hamming is 233× slower than stock).

Addresses are written relative to `Z = zero_addr`. In the C bridge, `Z` is the
`calloc`'d base (`alloc_gen.c:152`), so `T` holds absolute addresses there. The
window size `B` defaults to 64 KB (`0x10000` bytes, 8192 words), so `b[j] = Z +
j * 0x10000`. "Header" means a header address `hd`; the object is at `hd + 8`.

## 0. Summary

1. **Both parts change one piece of state: what used to be the single free
   pointer `fp`.** That state becomes an *allocator state*: 17 list heads
   (index 0 is the large list, indexes 1 to 16 are the small lists) and the
   table `T`. They are bundled once into one Pulse record and one ghost value.
   This is the only way to change the signature of every function that threads
   `fp` (about 20 Pulse functions and 170 spec vals) a single time instead of
   twice.
2. **Part B is a recombination of proofs that already exist.**
   - A small exact fit is `alloc_search` on list `n`, finding the block at the
     head with leftover 0.
   - A fallback, or a large allocation, is `alloc_search` on another list, with
     one new step afterwards: *relist* the remnant, because its size, and so its
     class, has changed.
   - The sweep's lists are, list by list, the subsequence of today's single
     list that has the given size. A *filter lemma* carries `fl_exact`,
     descending order and termination over from the existing proofs.
3. **Part A must use the heap walk.** Every entry must be a header the walk
   from `Z` reaches, or the sentinel `heap_size`. The sweep rebuilds `T`
   exactly in one ascending pass, at one compare per surviving header. This
   makes the combined design's R2 (a stale entry after coalescing) impossible
   by construction.
4. **The stated invariant and "at most one entry per allocation" pull against
   each other** (§3.2, C2). A non-decreasing `T` with every `T[j] ≥ b[j]`
   allows the allocator to write only under a guard. The guard blocks the
   update exactly in the common case: carving downwards through a free block
   that spans several windows. Correctness is not at risk. Load balance in the
   *later* parallel sweep is: a region refilled from one large free block
   stays a single segment until the next sweep. §1.2 gives three options. This
   is the one decision I need from the review.
5. **hamming, measured (§7.5)**: from 70.5 s to 0.28 s at 16M words; livemap
   from 32.1 s to 8.0 s; binarytrees and livegraph are 1–2% slower. The
   original estimate was from 98 s to about 0.5–2 s. Today each promotion
   skips 740–2,230 blocks; with size lists it takes O(1). This has not been
   measured. The risks are a scan of up to 15 empty heads on a heap with no
   holes, scattered placement, and first-fit kept for requests over 16 words
   (§4).

### 0.1 Decisions after review

1. **Part A semantics: A3, decided now.** `T[j]` is the start (the header) of
   the object or free block that *contains* `b[j]`. The allocator writes at
   most one entry per allocation, and the sweep rebuilds the table. §1.2 below
   is updated for this; the A1/A0 text there is kept as the record of the
   options.
   - **A flaw in "at most one entry per allocation"** (found while planning
     part A; not implemented, since part A is deferred). An allocated object
     contains every boundary `b[j]` inside its extent, and under A3 each of
     those entries must become the object's header. An object of 64 KB (8,192
     words) or more can contain two or more boundaries. Concrete case: fasta's
     direct major allocation of `THREE`, 1.59M words, contains about 194
     boundaries, so A3 needs about 194 writes for that one allocation.
     Promotions (at most 256 words) and every object under 64 KB need at most
     one. The options are: (a) accept `ceil(size / B)` writes for large
     objects, which costs less than the runtime's own initialisation of the
     object; (b) give up exactness for windows inside a large object (they
     keep naming the old free block's start, which is no longer a header, so
     (W) breaks — not acceptable); (c) a second-level table for large objects.
     I recommend (a), stated as "at most one write per 64 KB of object, and at
     most one for any object under 64 KB". This needs a decision before step 3.
2. **No bitmap of non-empty lists for now.** The allocator scans the heads
   from the request's own class upwards and skips empty ones (`allocate`'s
   loop tests `heads[i] = 0` before searching a list). §7.4 measures how often
   an empty head is scanned; the bitmap waits for that number.
3. **`mark-and-sweep/ocaml-integration/verified_gc/allocator.c` is not built or
   tested.** It is untouched since the initial commit (`b074578`), its
   `GC_Impl.c` is a frozen extraction with the old `collect(heap, st, fp)`
   signature, and neither CI nor any `make` target compiles it. It is left
   unchanged. (§2.1's row for it, and §6.1 step 4, are superseded.)
4. **Part B first, on its own,** as its own PR (§7). Part A is not started.

## 1. Design

### 1.1 Allocator state

```
fl_state  = { heads : lseq U64.t 17 }     // ghost / spec
alloc_st  = { heads : A.array U64.t (17); // Pulse; extracted to uint64_t*
              tbl   : A.array U64.t (NT) }
NT        = ceil((heap_size - Z) / B)
class w   = if 1 <= w <= 16 then w else 0  // index 0 is the large list; never called with w = 0
```

`gen_heap_t.fp_ref` (`GC.Gen.Impl.fsti:58`) is replaced by `st: alloc_st`.
`is_gen_heap … fp` becomes `is_gen_heap … fls t`, with `A.pts_to st.heads fls
** A.pts_to st.tbl t`. `N_SMALL = 16` is one constant in a new spec module, so
it can be changed without touching the proofs (§4.4).

### 1.2 Part A: the table

**Invariant `table_ok g t` (A3, decided):** for each `j`, `t[j] = hd_address o`
for the object or free block `o ∈ objects Z g` whose extent contains `b[j]`:

- (W) `t[j]` is a walk position of `g`;
- (C) `t[j] ≤ b[j] < t[j] + whsize(o)·8`.

(M), `t[j] ≤ t[j+1]`, follows from (C), because the walk's blocks are
disjoint and in address order. No sentinel is needed: the walk from `Z` tiles
the heap, so every `b[j] < heap_size` is inside some block, and `T[0] = Z`.
Only (W) and (M) matter for the correctness of the later cuts; (C) makes every
entry exact, so balance does not depend on the history of allocations.

The text from here to the decision table describes the options as they were
put to review (A1 and A0 keep `t[j] ≥ b[j]` instead of (C)). The allocator
under A3 is: when an object is carved at `p` from a block at `hd`, every
boundary in `[p, p + whsize·8)` gets `T[j] := p`; boundaries in the remainder
`[hd, p)` keep `hd`, which is still the remainder's header. That is at most one
write for an object under 64 KB, and `ceil(size / B)` for a larger one (§0.1).
A relist moves no header, so it writes nothing. The sweep sets every boundary
inside a run to the run's header, and every boundary inside a surviving object
to that object's header.

**Who removes walk positions.** Only coalescing does. The combined design
(§3.1) has the full table. Every other writer leaves the walk the same or adds
positions, because it keeps the wosize at each existing position:

- The allocator adds `p` at leftover ≥ 1.
- Promotion's `set_promoted_tag` rewrites the new header with the same wosize
  (`GC.Gen.Promote.fsti:67`).
- The mark changes only colour bits.
- Cheney's pointer rewrite and the mutator's field writes touch body words.

**The sweep: an exact rebuild, not a repair.** The fused sweep already visits
the headers in ascending order. Its output walk positions are exactly:

- the black (surviving) headers, and
- the first header of each run, `fb − 8`, which `flush_blue` rewrites into the
  run's header, even for a one-word run.

A cursor `k` and the next boundary `nb = b[k]` are kept in registers. When the
sweep *decides* that a header `h` is an output position (a black object, or a
non-black object that starts a run with `rw = 0`), it runs
`while k < NT && b[k] <= h: T[k] := h; k++`. After the loop, every remaining
entry gets `heap_size`. This writes every entry once per sweep, so nothing
that a run absorbed can survive in `T`. The pass never reads `T`, so its
precondition needs only the permission.

**The allocator: optional, at most one guarded write.** When a header `p` is
carved from a block at `hd` with `hd < p` (leftover ≥ 1), let `j = (p − Z) / B`.
The write is:

```
if hd < b[j] && (j = 0 || T[j-1] <= p) then T[j] := p
```

- (W) holds because `p` is now a header.
- (≥) holds because `b[j] ≤ p`.
- (M) holds on the right because the old `T[j]` was a walk position at or after
  `b[j] > hd`. Inside the old block `(hd, E)` there was none, so the old value
  was at least `E > p`. It holds on the left by the guard.
- The new value is exact: no header lies in `[b[j], p)`, because that range is
  inside the remnant.

Without the guard, (M) breaks (C2). With the guard, the write is skipped
whenever window `j − 1` also starts inside the same free block. In that case
its entry still names something at or beyond `E`.

**Decision for review: what the allocator does about the table.**

| Option | Allocator | Invariant | Balance of a region refilled from one big block | Proof cost |
|---|---|---|---|---|
| **A1: as specified** | the guarded write above | W, ≥, M | **one segment** until the next sweep: the guard blocks every update except in the lowest window | the allocator frames `T`; one guard lemma |
| A2: drop (M) | unguarded `T[j] := p` | W, ≥ | exact for every window that gets a header | the later cut function sorts and dedupes (the combined design's `cuts_of_table`); workers do not use `[T[j], T[j+1])` directly |
| **A3: containing header** (block-offset table) | `T[j] := p` for each `b[j] ∈ [p, p + whsize·8)`: **at most one write** for any object under 64 KB | W, M, and `T[j] ≤ b[j] < T[j] + whsize` | exact | the sweep sets every window inside a run to the run's start; same rebuild cost |
| A0: allocator never writes | none | W, ≥, M | one segment until the next sweep | smallest: `T` stays out of the allocator's footprint |

My recommendation:

- **For step 1:** build A0 plus the exact sweep rebuild. The table is not used
  until step 3, and A0 keeps `T` out of `allocate` and so out of the Cheney
  ladder for now. The record from §1.1 still carries `T`, so adding the
  allocator write later changes no signature.
- **For the semantics:** choose A3 before step 3. It satisfies "one entry per
  allocation" and monotonicity at once. Its only cost is giving up "at or
  after `b[j]`", which correctness never needed.

This is a recommendation. The rest of this note follows the semantics as
specified (A1/A0) unless it says otherwise.

### 1.3 Part B: size lists

**Invariant `fls_ok g fls`**, for each `i ∈ 0..16`:

- `fl_valid g fls[i] heap_words /\ fl_chain_terminates g fls[i] heap_words`:
  the existing per-list predicates, unchanged.
- (C) Every cell reachable on list `i` has `class (wosize) = i`. That is,
  wosize exactly `i` for `i ≥ 1`, and wosize > 16 for `i = 0`.
- `fls_exact`: every cell is blue (`fl_sound` per list), and every blue object
  with wosize ≥ 1 is reachable on list `class(wosize)` (`fl_complete`, routed
  by class). Wosize-0 fragments are on no list, as today.

(C) gives **disjointness of the lists for free**: one block has one class.
Without it, a block could be on two lists and be handed out twice.

**Allocation** of `wz` (`wz ≥ 1`; the C bridge already maps 0 to 1):

1. **Exact small**: if `wz ≤ 16` and `heads[wz] ≠ 0`, pop the head:
   `heads[wz] := link(head)`, and write the header (white, wosize `wz`) in
   place. Spec: this is `alloc_search g heads[wz] 0 heads[wz] wz _`, taking the
   `found_head` arm with leftover 0 (`alloc_from_block_exact`). It is the
   existing spec.
2. **Small fallback**: the smallest `s ∈ wz+1..16` with `heads[s] ≠ 0`, as
   stock's `bf_allocate` does (`freelist.c:1524`). Pop it. The block is
   right-justified as today, so the remnant keeps `hd` with wosize `s − wz − 1`.
   - If the remnant has wosize ≥ 1, **relist** it: `link(hd+8) :=
     heads[s−wz−1]; heads[s−wz−1] := hd+8`.
   - If it has wosize 0 (`s = wz + 1`), it is a fragment and stays unlisted.
3. **Large**: first-fit on `heads[0]`, exactly today's `alloc_search`, with
   one change to the replacement rule:
   - The block stays in place only if the remnant's wosize is still above 16.
   - Otherwise it is unlinked at `prev`, as an exact fit is today. A remnant of
     wosize 1..16 is then relisted on its small list.
   - In spec terms, `alloc_replacement_fp`'s `leftover < 2` becomes `leftover <
     2 + keep_min − 1`, with `keep_min = 17` for list 0 (and ∞ for small lists,
     where any remnant moves).
4. **OOM** happens only if all three steps fail. So the order searched is:
   list `wz`, then lists `wz+1..16`, then the large list. Every block that fits
   is reachable, which is what `alloc_succeeds_when_a_block_fits` needs (M4
   below).

**Writes.** These are the remnant header at `hd`, the object header at
`hd + leftover·8`, the predecessor's link (large list only), the remnant's link
at `hd + 8`, and the heads. Every heap write is inside the chosen block or in
the link word of its predecessor, a free cell. That is the same footprint as
today, which is what keeps `alloc_spec_read_other` and its relatives
re-provable with the same shape.

**Sweep.** `flush_blue` pushes a run of `rw ≥ 2` words onto
`heads[class(rw − 1)]` instead of `fp`. A one-word run is still an unlisted
fragment. `fused_aux` starts from **all 17 heads = 0**: today it ignores the
incoming `fp` and starts from `0UL`, and the multi-list version must reset
every head (C5). The pass walks upwards and pushes, so each list comes out
descending, as the single list does today.

## 2. What changes where

### 2.1 Modules

| Layer | Module | Change |
|---|---|---|
| F\* spec, new | `common/spec/GC.Spec.SizeClass` | `N_SMALL`, `class`, `B`, `NT`, `b j`. |
| | `mark-and-sweep/spec/GC.Spec.FreeLists` | `fls_valid`, `fls_terminates`, `fls_class`, `fls_exact`, `fls_avoids g fls x = ∀i. chain_avoids g fls[i] x heap_words`, `fls_pointer_or_zero`, `fls_in_heap`, plus intro/elim lemmas. All are defined per list, on top of the existing single-list predicates. |
| | `mark-and-sweep/spec/GC.Spec.Allocator.Lists` | `alloc_lists_spec g fls wz : {heap_out; fls_out; obj_out}`, built from `alloc_search` plus `relist`. A lemma kit with the same shapes as the `_part1` lemmas in `GC.Spec.Allocator.Lemmas.fsti:192–420`, with `fp` replaced by `fls`. |
| | `mark-and-sweep/spec/GC.Spec.ObjectTable` | `walk_pos`, `table_ok`, `rebuild_table` (the spec of the cursor pass), and frames: a colour change, a write to a non-header word, and an allocation each keep the walk positions (`alloc_keeps_walk_positions`). |
| F\* spec, changed | `GC.Spec.Allocator` | Unchanged. `alloc_search` and `alloc_from_block` are reused as is. Only `alloc_replacement_fp` gains the `keep_min` threshold (a transparent mirror, per the lesson of `allocator-exactness.md` §5). |
| | `GC.Spec.Coalesce` (`flush_blue`, `coalesce_aux`), `GC.Spec.SweepCoalesce.Defs` (`fused_aux`, `fused_sweep_coalesce`) | Thread `fls` instead of `fp`, and return `(heap, fls)`. Add the new **filter lemma**: list `i` of the new result is `filter (class = i)` of today's chain, in the same order, and the new heap equals today's except at link words of blue blocks. |
| | `GC.Spec.HeapAgree` | A weaker relation `heaps_agree_mod_free_links`, which also ignores the link word, so that `coalesce_correct` (`Coalesce.Correct`, 3,839 lines) transfers instead of being re-proved. None of its four parts reads a link. |
| | `GC.Spec.Coalesce.Complete`, `.Descending`, `GC.Spec.FreeList(.Sweep)`, `GC.Spec.Allocator.Oom`, `GC.Spec.Partition` | `fls_exact` from `fl_exact` through the filter lemma. Per-list descending order. `fused_oom_no_fit` over all lists. The partition's "on-chain words" becomes a sum over lists. |
| Pulse | `GC.Impl.Allocator` | `allocate` / `allocate_part1` take `st: alloc_st`. The body is a class dispatch, a head scan, and the existing first-fit loop applied to `heads[0]`, then `relist`. `init_heap` sets `heads[0] = Z + 8`, the other heads to 0, `T[0] = Z`, and `T[j≥1] = heap_size`. |
| | `GC.Impl.Coalesce` (`flush_blue_impl`), `GC.Impl.FusedSweepCoalesce` | `heads` array instead of `fp_ref`; zero all 17 heads at entry; the table cursor in the loop (two more locals). The loop invariant gains "`T[0..k)` = `rebuild_table` of the output prefix". |
| | `GC.Impl` (`collect`, `collect_with_roots`), `GC.Impl.Correct` | Return the heads instead of `final_fp`. `gc_coalesce_source`, `gc_safe` and `gc_live` take `fls`. |
| Pulse, generational | `GC.Gen.Impl.Promote` (`promote_one`), `GC.Gen.Impl.Cheney` (all five functions), `GC.Gen.Impl` (`gen_alloc`, `minor_collect_full`, `gen_gc`, `promote_phase`) | `fp_ref` → `st`. Every invariant's `fl_valid ∧ fl_chain_terminates` becomes `fls_valid ∧ fls_terminates` (∧ `fls_class`). |
| Spec, generational | `GC.Gen.Promote` (`promote_object`), `GC.Gen.Cheney*`, `GC.Gen.CheneyPreservation*`, `GC.Gen.CheneyFlComplete`, `GC.Gen.PromoteUpdate*`, `GC.Gen.AllocProps`, `GC.Gen.AllocExact`, `GC.Gen.HeapInvariant`, `GC.Gen.PostCollectionShape`, `GC.Gen.MajorPrecondition`, `GC.Gen.WriteBodyLemmas`, `GC.Gen.FreeListShape` | Mechanical `fp → fls` substitution, plus the class conjunct. `major_heap_shape` gains `fls_class` and (Part A) `table_ok`. `cs_fp` becomes `cs_fls` (`GC.Gen.Cheney.Sim.fsti:39`). |
| SPOT | the 3 hand-built `major_heap_shape` heaps | Heads: `[fp, 0, …, 0]` or the class of the one free block, and the table of a fresh heap. |
| Extracted C | `generational/snapshot/GC_Gen_Impl.c` and friends | Regenerated. `allocate(heap_t, uint64_t *heads, uint64_t *tbl, uint64_t wosize)` returns the object. `promote_one` is `inline_for_extraction`, so its seven inlined copies (`GC_Gen_Impl.c:698…1198`) change with it. |
| Runtime bridge | `generational/ocaml-integration/verified_gc/alloc_gen.c` | `ensure_heap` (`:160–171`) allocates `heads[17]` and `tbl[NT]` instead of `fp_ref`, or calls the verified `init_heap`. `verified_allocate` (`:774`) passes the state. `do_full_gc` and `do_minor_gc_core` are unchanged apart from the type. The header rewrite in `memory.c:466` is unchanged. |
| Unverified | `mark-and-sweep/ocaml-integration/verified_gc/allocator.c` | Its C first-fit consumes the sweep's `fp`, and it is left-justified, not verified. It must learn to read 17 heads. The minimal version treats them as 17 first-fit lists. Its left-justified split adds a header and removes none, so `table_ok` survives it. |

### 2.2 How promotion uses the allocator

`minor_collect_full` → `cheney_promote_phase` → `forward_roots` / `scan_loop` →
`forward_if_minor(_infix)` → `promote_one` → `allocate_part1`. Today this
threads `fp_ref`; it will thread `st`.

- Cheney's work list is an explicit queue (`GC.Gen.Cheney.Sim.fsti:31–48`), not
  a scan of contiguous to-space. Placing promoted objects in holes, rather than
  carving them from one block, does not affect the traversal.
- On OOM, `promote_one` leaves heap and state unchanged
  (`alloc_spec_oom_unchanged`). It must still do so when a fallback has
  already been *considered*: the head scan must not write anything until a
  block is chosen.
- Promotion requests are at most `Max_young_wosize = 256` (`alloc_gen.c:177`).
  Every one of them uses the small lists or the large list. Direct major
  allocations (`verified_allocate`) use the same `allocate`.

## 3. Invariants and the proofs that carry them

### 3.1 Which proofs, and how

| Proof | Carries `fls_ok` | Carries `table_ok` |
|---|---|---|
| **Allocator** (`GC.Spec.Allocator.Lists`) | Exact pop: the existing `found_head` and exact lemmas on one list; the other 16 lists are unchanged because the write is inside a block not on them (by (C) and `fls_avoids`). Relist: a push onto list `r` of a cell `c` with `class c = r`. Termination holds because `c` was unlinked from its old list and, by (C), is on no other list. `fls_exact` follows `alloc_spec_preserves_fl_exact` (`AllocExact:827`), plus a "moves from list `s` to list `r`" lemma. | A0: `alloc_keeps_walk_positions` (adds `p`; `hd` stays). A1: plus the guard lemma (§1.2). |
| **Sweep and coalescing** | Filter lemma, then the existing `coalesce_exact`, `coalesce_desc`, `coalesce_fl_entry` and `fused_exact` per list. `fused_agrees_sweep_coalesce` (`SweepCoalesce.fst:433`) is restated with `heaps_agree_mod_free_links`. | New lemma: the output walk positions are the survivors plus the run starts (the combined design's §5, "Coalescing"). From it, `rebuild_table` gives `table_ok` by an induction parallel to `fused_aux`. |
| **Minor collection** | `promote_object_preserves_*` and the `CheneyFlComplete` ladder with `fls`. The pointer rewrite (`update_major_pointers_preserves_fl_complete`, `AllocExact:1056`) writes no header and no link, so it is the same argument per list. | Promotion = allocation + body writes + a same-wosize header write: all frames. The pointer rewrite writes body words: a frame. |
| **`gen_gc`** | `major_heap_shape` gains `fls_class`. `PostCollectionShape` gets it from the filter lemma. | `major_heap_shape` gains `table_ok`, established by the sweep and carried through the minor collection. The mark is a colour-only frame. |
| **`gc_correct`** (mark-and-sweep) | `gc_safe`'s `fl_sound` and `gc_live`'s `free_blocks_listed` become per-list. `heap_partitioned` sums over lists. `gc_correct` itself is re-derived from the same sources. | Add `table_ok s2 t2` to the postcondition as a new safety conjunct. |
| **AllocExact headline** | `alloc_succeeds_when_a_block_fits` with `fls`. The new obligation is that the dispatch searches every list a fitting block could be on. | Not involved. `event` gains nothing; `field_write_preserves_entry` gets a table frame. |

Two assumptions stay as they are: the program writes only fields of live
objects, and the runtime fills new objects before the next collection
(`allocator-exactness.md` §9). `table_ok` needs the first one too: a mutator
write to a header would move the walk.

### 3.2 Must existing vals change?

**Yes, by type.** Every `val`/`fn` whose signature mentions the free pointer
changes. A `U64.t` becomes `fl_state` (spec) or `alloc_st` (Pulse). That
covers:

- `alloc_spec` and its lemma kit, `allocate`, `allocate_part1`, `init_heap`
- `flush_blue(_impl)`, `fused_sweep_coalesce` (spec and Pulse), `coalesce`
- `collect`, `collect_with_roots`, `gc_coalesce_source`, `gc_correct`,
  `collect_correct`
- `promote_object`, `promote_one`, the Cheney functions and their specs,
  `minor_collect_full`, `gen_gc`, `gen_alloc`
- `major_heap_shape` / `collection_heap_shape`, and the `GC.Gen.Impl.fsti`
  helpers that take `fp` (`:98–279`)

**No, in strength.** No `ensures` gets weaker. The changes are `fp → fls`,
added conjuncts (`fls_class`, `table_ok`), and one relaxed relation
(`heaps_agree_mod_free_links`). That relation sits inside
`gc_coalesce_source`'s existential, so `gc_safe` and `gc_live` keep their
meaning. One `requires` gets stronger: `allocate_part1` additionally needs
`fls_class`. The 17 heads could only be avoided by storing them in the major
heap, where the walk would see them as an object. I rejected that.

**The cheapest order** is to introduce `fl_state` as a one-element wrapper
first, with no behaviour change. That makes the wide mechanical edit
(about 170 vals, 20 Pulse functions, re-verified downstream of
`GC.Gen.HeapInvariant`) separate from the new behaviour (§5).

## 4. Caveats: wrong results, traced

Each trace starts from a valid state and shows a plausible implementation
error, and where it turns into wrong output. Each of these is a mutation in §5.

C1 and C2 concern A1's guard and do not arise under A3, where an allocation
writes exactly the boundaries the new object contains. They are kept as the
record of why A1 was rejected.

**C1. A free block spanning a table boundary.** Correct behaviour, shown for
contrast.

1. Free block `F = [Z+0xFF00, Z+0x30000)`, header at `Z+0xFF00`. Live `S` at
   `Z+0x30000`. Then `T[1] = T[2] = Z+0x30000` (`b[1] = Z+0x10000` and `b[2] =
   Z+0x20000` are inside `F`).
2. Promote 3 words: leftover large. `p = Z+0x2FFE0`, `j = 2`. `hd < b[2]`, but
   `T[1] = Z+0x30000 > p`, so the A1 guard skips. `T` is unchanged and still
   valid: `Z+0x30000` is still a header.
3. Continue until `p < Z+0x20000`, so `j = 1`. Now `T[0] = Z ≤ p`, so `T[1] :=
   p` is allowed. `T[2]` keeps `Z+0x30000`.
4. Result: (W), (≥) and (M) hold. Window 2's whole refill is behind `T[2]`, so
   a later worker 1 covers `[T[1], T[2])`, which is up to two windows. This is
   the balance cost of A1.

**C2. Allocator table write without the guard (A1 with (M) kept).**

1. Same heap as C1. Promote at `p = Z+0x2FFE0`, and write `T[2] := p`
   unguarded.
2. Now `T[1] = Z+0x30000 > T[2] = Z+0x2FFE0`. (M) fails.
3. Later, the parallel sweep gives worker 1 the range `[T[1], T[2])`, which is
   empty or negative. If it is computed as `hi − lo` in `uint64`, it wraps to
   about 2^64 words. Worker 1 then walks from `Z+0x30000` to the end of the
   heap, while worker 2 walks `[Z+0x2FFE0, T[3])`. Both sweep the same
   objects. Two flushes then link the same run twice, and a block ends up on
   two lists: a double allocation.

   Under A2, the cut function sorts and drops the entry, so this is harmless.
   Under the specified invariant, it is the reason for the guard.

**C3. Coalescing absorbs the header an entry names.**

1. `T[1] = Z+0x10000`, which is the header of dead `D2` (wosize 7). The run
   `D1 + D2` spans `[Z+0xFFE0, Z+0x10040)`, and live `S` is at `Z+0x10040`
   (the combined design's §4.1 heap).
2. The sweep flushes a run with its header at `Z+0xFFE0`, wosize 11, and
   pushes it onto **list 11**. `Z+0x10000` is no longer a header.
3. Correct rebuild: at the run start `Z+0xFFE0`, `b[1] > Z+0xFFE0`, so nothing
   is emitted. At `S = Z+0x10040`, `T[1] := Z+0x10040`. ✓
4. Mutation M6, where the cursor emits every *visited* header rather than every
   *output* position: at `D2 = Z+0x10000`, `T[1] := Z+0x10000`, a stale
   header.
5. Two allocations of 3 and 2 words follow; the 11-word block now comes from
   list 11 by fallback. Right-justification puts their headers at
   `Z+0x10020` and `Z+0x10008`. The remnant `[Z+0xFFE0, Z+0x10008)` has
   wosize 4 and is relisted on list 4.
6. The word at `Z+0x10000` is now the remnant's last field. It still holds
   D2's old header (nothing zeroes free blocks, #33).
7. In step 3 the parallel sweep cuts at `Z+0x10000`. It reads "wosize 7, not
   marked" and frees `[Z+0x10000, Z+0x10040)` **including the two live
   objects**.

   With the sequential sweep (step 1), the table is never read, so this is a
   latent bug. The checker in §5 must catch it now, by checking `table_ok` by
   a heap walk after every sweep.

**C4. A small block split by an allocation, with the remnant not relisted
(M1).**

1. List 5 = `[X]`, `X`'s header at `Z+0x500`, wosize 5, covering
   `[Z+0x500, Z+0x530)`. List 3 is empty. Request 3.
2. Fallback to `s = 5`. Leftover 2: the object header goes at `Z+0x510`, and
   the remnant at `Z+0x500` has wosize 1.
3. M1: `heads[5]` stays `X+8`. That is today's in-place split rule, which is
   correct for the single list.
4. Request 5. The exact pop takes `X` and writes the header "wosize 5" at
   `Z+0x500`. The new object's fields `[Z+0x508, Z+0x530)` **cover the live
   3-word object at `Z+0x510`**. The mutator's initialisation overwrites its
   header and fields. This is memory corruption, reachable from safe OCaml.

   F\* catches it as (C) failing for list 5. At run time, a size check at pop
   (`wosize(head) == n`) catches it.

**C5. A block whose size changes after coalescing (M3, heads not reset).**

1. After cycle 1, list 2 = `[Y, …]`, with `Y`'s header at `Z+0x900` and
   wosize 2.
2. In cycle 2, the free block `Y` and a dead neighbour at `Z+0x918` (wosize 3)
   merge into one run of wosize 6. The flush pushes it onto list 6.
3. M3: the sweep zeroes only the heads it flushes into. `heads[2]` still names
   `Y`.

   `Y+8` is now on two lists: list 2 (stale) and list 6 (as the head of the
   merged block).
4. Request 2: an exact pop of `Y` from list 2 writes a white "wosize 2" header
   at `Z+0x900` and hands out `[Z+0x908, Z+0x918)`.
5. Request 6: an exact pop from list 6 takes `Y` again and hands out
   `[Z+0x908, Z+0x938)`. The two objects overlap, which is a double
   allocation. If `Y` had instead been absorbed into a run that started below
   it, the stale head would point into the middle of a free block, and the
   stale "header" read there could be anything.

   The spec catches this because `fused_aux` must start from 17 zeros. The
   Pulse postcondition `(s2, fls2) == fused_sweep_coalesce 's` forces the
   implementation to match.

**C6. A large block shrinking into the small range (M5).**

1. The large list is `[L(20), M(4000)]`. Request 3. First fit takes `L`:
   leftover 17, so the remnant has wosize 16.
2. With today's rule (leftover ≥ 2 means it stays in place), `L` stays on list
   0 with wosize 16. This breaks (C).
3. Safety still holds: the large search checks `wosize ≥ request`. The harm is
   performance. Repeat this, and list 0's prefix fills with 1- to 16-word
   remnants that every large request walks: **#44 again**, one level up. It is
   also invisible in testing unless the checker checks (C).
4. Correct behaviour: `prev.link := next`, then push `L` onto list 16.

**C7. An empty small list falling back to a larger one, with a fragment
remnant (M2).**

1. Request 2. Lists 2 and 3 are empty except for list 3 = `[W]`, with `W`'s
   header at `Z+0x700`, wosize 3, covering `[Z+0x700, Z+0x720)`.
2. Leftover 1: the remnant is a header-only fragment (wosize 0) at `Z+0x700`,
   and the object header goes at `Z+0x708`.
3. M2: `relist` computes `class 0 = 0` and pushes the fragment onto list 0. The
   push writes the link at `hd + 8 = Z+0x708`, **which is the new object's
   header**. The object's header becomes a pointer value. The next walk (the
   sweep) reads a garbage wosize: the heap walk is corrupt.
4. Correct behaviour: a remnant of wosize 0 is never listed (`fl_cell` demands
   wosize ≥ 1). The spec's `class` is applied only when the wosize is ≥ 1.

   A second variant (M4) skips list `wz+1`, to avoid making fragments. Request
   2 then fails with OOM although `W` fits. This breaks
   `alloc_succeeds_when_a_block_fits`, and at run time it is a spurious
   `Out_of_memory` after a full collection.

**C8. A minor collection promoting while lists change.**

1. The queue holds `A` (wosize 2) and `C` (wosize 2). List 2 = `[P, Q]`.
2. Promote `A`: pop `P`, so `heads[2] = Q`, and copy `A`'s fields into `P`.
3. Promote `C`: pop `Q`. Correct.
4. Mutation M9: a C-level "optimisation" caches `heads[n]` in a local across
   the `promote_one` calls (for example in the hand-written bridge, or in the
   hook added to the extracted code). Step 3 then pops `P` again. `A` and `C`
   share memory, and their fields overwrite each other. The roots are
   rewritten to the same address for both.

   In Pulse this cannot be written, because `heads` is owned by `st` and each
   call returns the new ghost value. It is a risk only in unverified C.

   A second hazard: the relist write lands at `hd + 8`. Right-justification
   puts every promoted object strictly above `hd + 8` when leftover ≥ 2, so the
   relist never touches a copy. At leftover = 1, `hd + 8` *is* the object's
   header: this is C7's case, and the reason the fragment is never listed.

**C9. A huge direct allocation over many windows** (fasta's `THREE`, 1.59M
words, about 194 windows).

- The table needs nothing: entries for windows inside the object keep values
  at or beyond its end, which are still headers.
- Under A3 (decided), it needs about 194 writes, one per boundary the object
  contains. That is O(size) and dominated by the runtime's own initialisation
  of the object, but it is not "at most one entry per allocation" (§0.1).
  #37 (fragmentation leading to OOM) is not changed by either part.

## 5. Performance

### 5.1 Table

- **Sweep:** one compare per output position (`h >= nb`), predicted not-taken
  except once per 64 KB, plus `NT` stores per sweep. At 88M words that is
  10,752 stores (86 KB). The binarytrees 18 sweep takes 141 ms; the expected
  added cost is under 1%. Memory: `heap/8192` words, 0.012%.
- **Allocator (A3):** a subtract, a shift and a compare to find whether the
  new object contains a boundary, and then one store: 2–5 ns, on the
  allocation slow path only. With 1.6M promotions in hamming, that is under
  10 ms. A large object adds one store per 64 KB.

### 5.2 Size lists

- **Exact hit:** a compare, a load of `heads[n]` (in L1: 136 bytes, 3 lines),
  a load of the block's link, and two stores. The load of the block's link
  touches the line that the object's initialisation touches anyway. This
  replaces a walk of 740–2,230 nodes in hamming (#44), about 23 ns per node
  (3.6 × 10⁹ steps in 84 s).
- **Fallback:** a scan of up to 15 heads in L1, about 5–15 ns. Stock uses a
  bitmap plus `ffs` (`freelist.c:1526`). That is an implementation-only
  optimisation with the invariant "bit `i` ⇔ `heads[i] ≠ 0`", and I would add
  it only if the measurement in §6 shows the scan.
- **Large:** today's first fit, over a list that now holds only blocks over 16
  words.
- **Sweep:** `class` is a compare, and `heads[c]` replaces the `fp` register
  with an L1 access. No measurable change is expected.

### 5.3 Is 1 to 16 right?

- Stock uses 16 (`BF_NUM_SMALL`).
- The holes in hamming are wosize 1–2. Its requests are about 2–5: lazy
  blocks, `Cons`, closures, and `Int64` custom blocks.
- Promotion requests go up to 256. Those from 17 to 256 still use first fit,
  which is the remaining exposure: a program that promotes 50- to 256-word
  arrays into a heap with many 17- to 49-word holes still walks them.
- `N_SMALL` is one constant, and nothing in the proofs depends on its value.
  It could be raised to 32 or 64 at the cost of a longer fallback scan (a
  bitmap then becomes worthwhile).
- §6 measures the histogram of request sizes and of free-block sizes before
  choosing.

### 5.4 Fragmentation

- **Compared with first fit:** small requests now prefer exact holes and split
  nothing. First fit splits the first block that is big enough, which is often
  a hole one word larger, and that leaves a fragment. Expect fewer fragments
  and holes that are consumed sooner. Large requests behave as before.
- **Compared with stock best-fit:** the small policy is the same. For large
  requests, stock uses best fit in a splay tree, and our first fit can split a
  big block where stock would use a closer fit. That means more fragmentation
  for large requests. #37 shows that this region matters, and this design does
  not close the gap.
- **Fragments are bounded per cycle,** because the sweep coalesces them back.

### 5.5 hamming, estimated (not measured)

- **Today:** at 16M words, minor GCs take 81.2 s of 98.1 s, and about 84 s of
  that is free-list walking.
- **After:** O(1) promotions: 1.6M × about 50 ns is about 0.1 s. What remains
  is the rest of the minor collection: root scan, Cheney, and zeroing the
  nursery 40 times. Other Sandmark programs run at 1.0–2.4× stock, and stock
  hamming takes 0.42 s, so expect **0.5–2 s, a 50–200× speed-up**, still above
  stock.
- **Why still above stock:** `Forward_tag` cells are not short-circuited, so
  70K–301K extra objects stay live and are promoted.
- **What the estimate assumes:** that each promotion finds a hit or a
  fallback. That holds because the one big block heads the large list, so a
  fallback ends at once.

### 5.6 What could get slower

1. **Heaps with no holes**, such as everything before the first major
   collection, or a program whose garbage dies young. Every small request then
   scans up to 15 empty heads before reaching list 0. Today's first fit hits
   the head immediately in that case. Cost: about 5–15 ns per promotion. This
   is the one systematic regression. The bitmap removes it.
2. **Locality.** Today, 3+-word promotions are carved downwards from one block,
   so consecutive promotions are adjacent. Hole-filling scatters them, which
   could slow later traversals by the mutator and the mark. Stock behaves this
   way too.
3. **Medium-size promotions (17–256 words)** with many medium holes: no worse
   than today, but not fixed.
4. **Proof and verification time,** not run time. `GC.Gen.AllocProps` and
   `AllocExact` already take tens of seconds, and the class conjunct adds to
   every query in the Cheney ladder. The mitigation is to keep `fls_*` opaque
   with intro/elim lemmas, as `major_heap_shape` is.

## 6. Plan for the proof and implementation prompt

### 6.1 Order of work

1. **Wrapper first.** Introduce `fl_state` / `alloc_st` with exactly one list
   and no table, and change every signature (§3.2). Behaviour is unchanged;
   the extracted C is the same modulo a pointer. This isolates the wide
   mechanical edit, and CI's snapshot check confirms it.
2. **Size lists, spec.** Add `GC.Spec.SizeClass`, `GC.Spec.FreeLists`, and
   `GC.Spec.Allocator.Lists` with the lemma kit, then the filter lemma and
   `heaps_agree_mod_free_links`. Port `coalesce_exact`, `fused_exact`, `Oom`
   and `Partition`. Port `AllocExact`, including the headline.
3. **Size lists, Pulse.** Change `allocate` / `allocate_part1`,
   `flush_blue_impl` and the fused sweep, then propagate through promotion,
   Cheney, `gen_gc` and `collect`/`gc_correct`. Update the SPOT heaps.
4. **Bridge and extraction.** Change `alloc_gen.c` and the unverified
   mark-and-sweep `allocator.c`, and regenerate the snapshot. Run the tests and
   the hamming timing. **Part B is complete here and could merge on its own.**
5. **Table.** Add `GC.Spec.ObjectTable` (walk positions after coalescing, and
   the frames), the rebuild in the fused sweep, and `table_ok` (A3, §1.2) in
   `major_heap_shape` and `gc_safe`. The allocator writes the boundaries the
   new object contains; settle the large-object case (§0.1) first.
6. **Negative controls** (§6.3) and **measurements** (§6.4).

### 6.2 Tests

- The existing suite: `make -C generational/ocaml-integration/tests
  correctness` (including `alloc_exact_promotion`, `large_alloc_garbage`,
  `gray_overflow` and `no_scan`), the OCaml testsuite in CI (0 new failures
  against `ci/expected-failures.txt`), and the SPOT proofs.
- **A checker build** (`VGC_CHECK_ALLOC=1`, a compile flag, off by default).
  After every sweep, and every 1,024th allocation, it walks the heap and
  checks:
  - every list cell is blue with `class(wosize) = i`;
  - each list ends within `heap_words` steps;
  - no cell is on two lists;
  - every blue block of wosize ≥ 1 is on its class list;
  - `table_ok` (A3): `T[0] = Z`, and every entry is a visited header whose
    block contains `b[j]`.
- **New OCaml tests** (`tests/size_classes.ml`):
  - a churn of sizes 1–20, with checksums, that forces exact hits, small
    fallbacks with remnants of every size 0–15, and large-to-small remnants;
  - a test that drains every small list so that list 0 must serve small
    requests.
  - Hamming itself (n = 10,000, at 4M and 16M words), with its output compared
    to stock's.

### 6.3 Deliberately broken variants

Each variant must fail F\* verification (as a negative control, like the ones
in #29). Each must also be caught at run time when patched into a scratch copy
of the extracted C, by the checker or by a test.

| ID | Mutation | Expected F\* failure | Expected runtime catch |
|---|---|---|---|
| M1 | small split: remnant not relisted (C4) | `fls_class` after allocation | checker: class mismatch; `size_classes` checksum |
| M2 | wosize-0 fragment pushed onto list 0 (C7) | `fl_valid` (wosize ≥ 1) | checker: walk corrupt |
| M3 | sweep does not reset all 17 heads (C5) | `fused_sweep_coalesce` postcondition equality | checker: cell not blue or wrong class |
| M4 | fallback skips list `wz+1`, or skips list 0 | `alloc_succeeds_when_a_block_fits` | spurious `Out_of_memory` in a drained-lists test |
| M5 | large remnant ≤ 16 left on list 0 (C6) | `fls_class` | checker: class mismatch |
| M6 | table cursor emits absorbed headers (C3) | `table_ok` (W) after the sweep | checker: entry is not a walk position |
| M7 | allocator does not update a boundary the new object contains (A3) | `table_ok` (C) | checker: entry's block does not contain `b[j]` |
| M8 | table stores `obj` (`hd + 8`) instead of `hd` | `table_ok` (W) | checker |
| M9 | exact pop without updating `heads[n]` (C8) | `fls_avoids` / `alloc_spec_obj_not_in_chain` | checker: allocated block still listed; double-use test |
| M10 | `class` returns 16 for wosize 17 (off by one) | `fls_class` | checker |

A script similar to `tools/mutation-ov-never-set.sh` applies each mutation to a
scratch worktree and asserts that it fails. Every check must run from a clean
scratch worktree, because of the `_cache` pollution noted for
`--admit_except`.

### 6.4 Measurements

All counters go into scratch copies of `alloc_gen.c` / `GC_Gen_Impl.c`, as in
`sandmark-failures.md`. No `sample`, `lldb` or other attaching tool is used.

1. **hamming**, n = 10,000, at 4M and 16M words: wall, user, minor and full GC
   time, and free-list steps per promotion, before and after. Also stock.
2. **Sandmark set:** the harness from `sheera/parallel-mark-proto2`
   (`tests/sandmark/build.sh`, `benchmarks.txt`). Every program, before and
   after, against stock, to find any regression (§5.6). Repeat 3 times on AC
   power, with Low Power Mode off.
3. **`make bench-mark`** (binarytrees 16/18, livemap, livegraph): sweep time
   with and without the table rebuild, to check the under-1% claim.
4. **Allocation profile:** a histogram of request sizes, and the share of
   exact hits, small fallbacks (by distance `s − wz`), large-list hits and
   large-list steps. Also free-block sizes after each full GC, to decide
   `N_SMALL` (§5.3) and whether the bitmap is needed (§5.6.1).
5. **Fragmentation:** after each full GC, free words, fragments, the largest
   block, and the number of blocks per list. Also the minimum heap for fasta
   (`tests/bench_min_heap.sh`, #37), before and after.
6. **Table balance**, for step 3: at each sweep, the spread of segment sizes
   that the cuts from `T` (A3) give at k = 4.
7. **Verification time** per changed module, against `main`.

## 7. Part B as built

Part B is implemented end to end on `sheera/size-lists` (from `origin/main`
`1ecb000`): spec and proofs, the Pulse allocator and sweep, extraction, the
runtime bridge, a checker build, directed tests, negative controls and
measurements. Part A is not started. `N_SMALL = 16`, so there are 17 lists.

### 7.1 How it was done

- **Step 1 (signatures, no behaviour change).** `fl_state` (a sequence of
  heads) replaced `fp` everywhere, with `n_small = 0`. The kit and the SPOT
  heaps went through a one-list reduction, removed in step 2.
- **Step 2 (the lists).** `n_small_u64 = 16UL`, `n_lists_sz = 17sz`
  (`GC.Spec.SizeClass`, the one place the number lives; `n_small` is opaque to
  the SMT solver, so no proof depends on its value).

The allocator spec (`GC.Spec.Allocator.Lists`) keeps `alloc_search` exactly as
it was and adds one decision on top:

- `alloc_on g fls i wz` runs first fit on list `i`. If the remainder's class
  is no longer `i` (`relists`), it instead allocates the whole block (first
  fit at the block's own size, which stops at the same block:
  `first_fit_same_block`), splits it with `alloc_from_block`, and pushes the
  remainder on its own list.
- `alloc_from` tries list `wz`, then `wz+1 .. 16`, then list 0.

This differs from §1.3 in one respect: there is no `keep_min` threshold inside
`alloc_replacement_fp`. The relist is a separate composition, so
`GC.Spec.Allocator` is untouched.

The proofs reuse the single-list proofs almost entirely:

- `search_at` / `found_cells` give first fit's stopping point in closed form
  (`found_heap`, `found_prev`).
- `relist_read` / `relist_writes` show that a relist writes exactly the words
  §1.3 lists: the block's two headers, the remainder's link, and the
  predecessor's link.
- In the kit (`GC.Gen.AllocLists`), a relist heap is the single-list
  allocation's heap plus two link writes (`relist_heap`). So every heap fact
  transfers through one frame lemma (`link_write`).
- The lists are handled one by one: the other lists keep their cells
  (`chain_frame`), list `j` is a single-list allocation's
  (`list_class_after`), and the remainder is pushed (`fls_push`).

The Pulse allocator is a write-free `find_fit` loop, then the writes for
`alloc_on`, inside a loop over the lists that skips empty heads.

### 7.2 Changes to existing vals, and why

No `ensures` got weaker except where noted, and no rlimit was raised.

| Val | Change | Why |
|---|---|---|
| `GC.Impl.collect`, `collect_with_roots`, `gc_precondition*`, `darken_precondition` | take `heads` (Pulse) / `fls` (spec); the incoming `fp` argument is gone | the state is the heads. The collector never read the incoming `fp`: the sweep starts from empty lists. |
| `GC.Impl.Correct.gc_correct`, `collect_post`, `gc_safe`, `gc_live` | over `fls` | as above |
| `coalescing_lossless` (in `gc_live`) | `heaps_agree_mod_free` → `heaps_agree_mod_free_links`, and `final_fp == snd r` → `fls_of_chain s2 fls (fst r) (snd r)`: list `i` reaches exactly the class-`i` cells of the coalescer's chain, in descending order. The reference sweep is started from `0UL` instead of the incoming `fp`. | **Weaker in one respect:** the link word of a free block is no longer compared with the single-list reference. The links differ by construction, because the same blocks are threaded into 17 lists. Everything else that `heaps_agree_mod_free` gave is still derived (`gc_result_agree_links`), and `gc_result_agree` itself is unchanged. The `0UL`: the original statement named the incoming `fp` as the reference sweep's starting list. The collector never used it, because its sweep starts every list empty, so the reference is now taken from `0UL`. |
| `heap_partitioned` | the on-list words are summed over the lists (`onchain_whsize_lists`) | the sum equals `cell_whsize`, so the equation also says that no block is on two lists |
| `gen_gc` | returns `ok: bool` | matches upstream's minor collection, which already did |
| `allocate`, `allocate_part1`, `init_heap` | take `heads`; ensure `alloc_lists_spec` / `init_heap_lists_spec` | the state |
| `fused_sweep_coalesce` (Pulse and spec) | takes `heads`; ensures `fused_sweep_coalesce_lists` | the state |
| `major_heap_shape`, `PostCollectionShape`, the Cheney and promotion specs | over `fls`. Spec variables still named `fp` there now hold an `fl_state`. | mechanical |
| `PromoteUpdate.BlueAlloc.alloc_spec_preserves_blue_link_fields_valid` | **gains `fls_pointer_or_zero fp` in `requires`** | a moved remainder's link becomes its new list's old head. `fl_valid` allows a garbage head as a terminal, so without this the link could be garbage. The only caller (`BlueProm`) already has it, because it calls the companion lemma, which always required it. |
| `GC.Gen.AllocExact.alloc_lists_preserves_fls_complete`, `alloc_lists_preserves_entry`, `alloc_lists_fits_succeeds` | same statements; proofs now generic | step 1 proved them by the one-list reduction |
| `GC.Gen.AllocLists` (kit) | same statements as step 1; adds `alloc_on_succeeds`, `alloc_lists_struct` (the shape of the lists after an allocation), `in_extent`, `extents_apart` | used by `AllocExact` and `BlueAlloc` |
| SPOT `spot_*_fls` | `fls_single fp` → `fls_one (size_class free_wosize) fp`; `single_shape_intro` takes the class | the one free block now sits on the list of its class |
| Removed | `fls_single`, `fls_single_valid`, `n_small_is_zero`, `alloc_lists_single` | step-1 scaffolding |
| Added, public | `Allocator.Dense.write_field_preserves_dense`, `Allocator.Oom.alloc_spec_oom_cells_small` (both were private helpers or a wrapper of one) | used by the kit and `AllocExact` |

### 7.3 Verification and tests

- `gmake verify` and `make -C spot` from a clean cache: see §7.6. There are no
  admits. The only `assume`s are the two pre-existing `platform_fits_u64`.
- Vacuity: for each new lemma with a nontrivial precondition (`search_at`,
  `relist_read`, the plain and relist list lemmas, `alloc_lists_struct`,
  `alloc_from_only`, `alloc_from_fails`, `fls_push`, the `BlueAlloc` lemma, the
  `AllocExact` entry lemma), a lemma "precondition implies `False`" fails, as
  it must.
- The snapshot harness (`generational/snapshot`, `make`) gains
  `size_lists_test.c`: directed tests of the extracted `allocate` for an exact
  hit, a fallback with a relist onto a non-empty list, the smallest fitting
  list winning, a header-only remainder, a large-to-small relist (20 → 16),
  a large remainder staying (40 → 36), a relist behind a predecessor, out of
  memory with heap and heads unchanged, drained lists, and the exact list
  preferred to list 0. `main.c` now initialises the heap with the verified
  `init_heap`.
- `make test` and `make test-native` pass.
- **Checker build:** `make -C generational/ocaml-integration/verified_gc
  VGC_EXTRA_CFLAGS=-DVGC_CHECK_ALLOC`. After every minor and full collection,
  and every 1,024th direct major allocation, `alloc_gen.c` walks the heap and
  checks:
  - every cell is a free block with a link on the list of its class;
  - every list ends, and no cell is listed twice;
  - every free block with a link is listed.

  `make test` passes on the checker runtime.
- The OCaml testsuite: see §7.6.
- `allocator.c` (mark-and-sweep) is left unchanged: it is not built (§0.1).

### 7.4 Negative controls (§6.3, part B)

Each F\* mutant was checked in a scratch copy with its own `_cache`. Each C
mutant was applied to a scratch copy of the extracted `GC_Gen_Impl.c`, then
run through the snapshot tests and a checker runtime on binarytrees 12,
`alloc_exact_promotion`, `large_alloc_garbage` and livemap.

| ID | F\* mutant | F\* failure | C mutant | Runtime catch |
|---|---|---|---|---|
| M1 | spec `relists` only on list 0 (M1s); Pulse relist test only on list 0 (M1i) | M1s: `AllocLists` (the remainder's class is not `j`). M1i: `GC.Impl.Allocator`, `relist == SAL.relists` | relist only when `i = 0` | snapshot tests (fallback, smallest-list); checker on binarytrees and livemap: "cell on the wrong list" |
| M2 | `relists` from leftover 1 (M2s); Pulse relist from leftover 1 (M2i) | M2s: `GC.Spec.Allocator.Lists` (`relist_read` / `relist_writes` need a remainder of wosize ≥ 1 to split and push). M2i: `GC.Impl.Allocator` | relist from leftover 1 | snapshot test (fragment); binarytrees, `large_alloc_garbage` and livemap abort with out-of-memory |
| M3 | Pulse sweep without `clear_heads` (M3i) | `GC.Impl.FusedSweepCoalesce`: the loop invariant | no `clear_heads` in the sweep | checker on all four workloads, after the first full collection: "cell is not a free block" |
| M4 | spec skips list `i+1` (M4s); Pulse starts at `start+1` (M4i) | M4s: `GC.Spec.Allocator.Lists` (`alloc_from_step`). M4i: `GC.Impl.Allocator`, the dispatch loop | skip list `wz+1` | snapshot test (fragment: spurious out-of-memory). The checker cannot catch it: no invariant breaks, which is why the drained-lists tests exist. |
| M5 | `relists` never on list 0 (M5s) | `AllocLists` (class) | small remainder stays on list 0 | snapshot tests (large-to-small, predecessor); checker on binarytrees and livemap: "cell on the wrong list" |
| M9 | Pulse exact pop without `heads.(i) <- next` (M9i) | `GC.Impl.Allocator`, the postcondition | same | snapshot tests (exact, exact-first); checker on binarytrees and livemap: "listed twice / not a free block" |
| M10 | Pulse `class_of 17 = 16` (M10i) | `GC.Impl.FreeLists`, `class_of`'s refinement | the sweep puts 17-word runs on list 16 | checker on livemap: "cell on the wrong list" (the snapshot tests do not sweep 17-word runs) |

Every F\* mutant fails, and every C mutant is caught at run time. A no-op
mutant (M0) passes everything, with output identical to the reference.

### 7.5 Measurements

Bytecode, one machine (macOS, x86-64), `hyperfine`, no attaching tools.
"Base" is `origin/main` `1ecb000`, built the same way. The bench-mark rows are
3 runs and the hamming rows 2. hamming is Sandmark's (`10_000`). Its output is
byte-identical on the size lists, the base and stock OCaml.

| Program (major heap, words) | Base, s | Size lists, s | Change |
|---|---|---|---|
| hamming (16M) | 70.46 ± 0.60 | 0.283 ± 0.003 | **249× faster** (stock: 0.19 s) |
| hamming (8M) | 22.44 ± 0.57 | 0.299 ± 0.006 | 75× faster |
| hamming (4M) | out of memory | out of memory | the same on both: the live set does not fit |
| livemap (25M) | 32.10 ± 0.39 | 7.96 ± 0.08 | 4.0× faster |
| binarytrees 16 (64M) | 12.72 ± 0.30 | 12.85 ± 0.10 | +1.0% |
| binarytrees 18 (512M) | 52.52 ± 0.54 | 53.25 ± 0.15 | +1.4% |
| livegraph (16M) | 4.48 ± 0.10 | 4.58 ± 0.03 | +2.3% |

**Allocation profile.** These are counters in a scratch copy of the extracted
allocator, covering every `allocate` call (promotions and direct major
allocations). "Empty heads" counts the heads skipped because they were 0.

| Program | Requests | Exact hit | Small fallback | List 0 | Relists | Empty heads per request |
|---|---|---|---|---|---|---|
| hamming 16M | 1,790,524 | 7.2% | 0.02% | 92.8% | 378 | 14.1 |
| binarytrees 16 | 15,567,346 | 0.001% | 0.006% | 99.99% | 1,154 | 7.0 |
| binarytrees 18 | 79,041,572 | 0.0003% | 0.0009% | 99.99% | 938 | 7.0 |
| livemap | 16,656,560 | 30.1% | 15.0% | 54.8% | 3,318,144 | 7.8 |
| livegraph | 5,937,847 | 10.8% | 22.8% | 66.5% | 1,134,777 | 10.2 |

Request sizes (wosize: count):

- hamming: 1: 473,256 and 2: 1,316,688; about 600 requests of 3–103 words.
- binarytrees 18: 3: 39.5M and 128: 39.6M; under 400 others.
- livemap: 2: 3.7M and 5: 12.9M.
- livegraph: 1: 2.0M, 3: 1.0M and 4: 3.0M.

What this says:

- **hamming is fixed, but not the way §5.5 assumed.** 93% of its requests are
  served from list 0, not from small holes. List 0 now holds only blocks of 17
  words or more, so first fit stops at its first block instead of walking the
  1- and 2-word holes that made up the old single list (#44).
- **The cut-off at 16 is right for these programs.** Every frequent request is
  5 words or less, except binarytrees' 128-word blocks, which are served from
  list 0 at the head (99.99%). No request size between 17 and 127 is frequent.
- **The empty-head scan is the measured cost** that §5.6.1 predicted: 7 to 14
  heads skipped per request. It costs 1.0–2.3% on the programs that do not
  benefit (binarytrees, livegraph). Decision 2 was to add the bitmap only if
  the scan shows. It does show, at that size, and the bitmap (bit `i` iff
  `heads[i] ≠ 0`, then a count-trailing-zeros) would remove it. This is left
  for review, not done.

### 7.6 Verification

- `gmake verify` from an empty `_cache`, in a scratch copy of the worktree:
  all 217 modules, 43.5 min at `-j4` while other jobs were running. Then
  `make -C spot`: all SPOT modules, 80 s. No errors, no admits.
  Verification time per module against `main` (§6.4.7) was not measured on a
  quiet machine.
- The OCaml testsuite (`ci/build-verified-toolchain.sh`,
  `ci/run-testsuite.sh`): 2,925 passed, 55 failed, 7 errors of 3,141. **No new
  failures** against `ci/expected-failures.txt`, and 10 expected failures now
  pass (`eintr`, `ephe_infix`, `ephe_issue9391`, `finaliser`,
  `output-complete-obj`, in both variants). I have not checked whether those
  10 are related to this change or to this machine.
