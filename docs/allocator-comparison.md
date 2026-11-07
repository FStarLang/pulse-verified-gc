# Allocator comparison: size lists (A) and OCaml 5-style pages (B)

This note compares designs only. No code, spec or proof has changed. The goal
is to choose an allocator that works with the sequential GC, an incremental GC
and a parallel GC.

- **A** is the current design. It is PR #46 (`sheera/size-lists`, `3be9eb36`)
  plus the object-start table of PR #48 (`sheera/object-table`, `3388be28`,
  `f4f1cb61`, `39930322`). A worktree of it is at
  `/Users/sheerashamsu/Documents/pgc-size-lists` (written `WT/` below).
- **B** is an allocator in the style of OCaml 5, adapted to our collector (§3).

**Decision rule.** Correctness comes first. A sequential slowdown of up to 5%
is acceptable if B clearly speeds up the parallel GC and shortens
incremental-GC pauses.

**Sources.**
- The OCaml 5 source read here is `~/ocaml` at `243f4cd378` (2023-11-27,
  5.2.0+dev). The last change to `runtime/shared_heap.c` there is `8cfd9c5a39`
  (#12755). Line numbers refer to that tree.
- The OCaml 4.14 source is the opam switch
  `~/.opam/4.14.1/.opam-switch/sources/ocaml-base-compiler.4.14.1`.

**Labels.** Numbers marked *measured* come from earlier notes, with the note
named. Numbers marked *estimate* are not measured. Settling them is the
purpose of §6.

## 0. Summary

1. **B can keep the invariant that every proof rests on.** That invariant is
   that the heap is one contiguous region tiled by headers, which `objects
   zero_addr g` walks. 172 F\* files use it.
   - B divides the same `calloc` region into 32 KB pages.
   - Every word stays covered by a header:
     - a free slot gets a blue header for the whole slot;
     - the leftover after a rounded-up object gets a filler header;
     - a page's unused tail gets a filler header.
   - With that, the mark, the Cheney minor collection, `well_formed_heap`,
     `full_gc_correctness` and the heap partition carry over unchanged.
   - What changes is the allocator, the sweep, and the liveness clauses about
     free lists.
2. **B makes the parallel sweep simple, and its correctness close to a frame
   argument.** Pages are disjoint, and nothing is coalesced across a page
   boundary. A sweep of page *p* reads and writes only *p* and the record for
   *p* in a side table. So:
   - the parallel sweep is a separating parallel composition;
   - there is no join step;
   - the object-start table is not needed for pool pages, because a page start
     is always a walk position.
3. **B bounds the incremental pause by construction.** OCaml 5 never allocates
   in an unswept pool. Before an allocation can use a pool, it sweeps that
   pool. It sweeps at most one pool per allocation (§1.4). In A, the sweep
   rebuilds the free lists from empty (`clear_heads`). An allocation partway
   through the sweep may therefore have to sweep forward an unbounded
   distance to find a fit.
4. **The 4.14 block splitting is not a blocker for B.**
   - intern.c re-tiles only blocks above `Max_young_wosize` (256 words). Those
     go to B's large space, which keeps A's walk-and-coalesce rules.
   - Obj.truncate inside a pool slot leaves the slot owned by the object at
     its start, so the slot sweep stays sound.
   - I still recommend changing intern.c's major path to allocate each object
     separately, as OCaml 5 does (§4.4).
5. **The open risks are sequential speed and memory.**
   - Rounding up to a size class wastes up to 10% per object.
   - binarytrees' 128-word blocks (whsize 129) round up to 141 words, which is
     8.5%, and they are about 97% of its allocated words.
   - A pool page that holds one live object keeps the whole page in use.
   - B writes one header per dead slot instead of one per coalesced run.
   - Whether B stays within the 5% limit cannot be known without measuring.
6. **Proof effort, estimated.** B costs about as much as #46 and #48 together:
   - a page-map invariant;
   - a new allocator, a new per-page sweep, and restated free-list liveness;
   - another change to the allocator-state type threaded through `gen_gc`.

   B also removes work:
   - the parallel sweep's join;
   - for pool pages, the table's exactness proof.

**Recommendation:** build the unverified B prototype and measure it (§6)
before deciding. On criteria 1 (correctness) and 2 (parallel and incremental)
the analysis favours B. The decision depends on the sequential and memory
numbers.

## 1. What OCaml 5 does

All references are to `runtime/` in `~/ocaml`.

### 1.1 Pages ("pools") and size classes

- **Page size.** `POOL_WSIZE 4096` words, which is 32 KB on 64-bit, and
  `POOL_HEADER_WSIZE 4` (`caml/sizeclasses.h`).
  - A pool starts with a 4-word header, `struct pool` (`shared_heap.c:49`):
    `next`, `next_obj` (the head of its free-slot list), `owner` (the
    domain) and `sz` (the size class).
  - Slots start at `POOL_FIRST_BLOCK(p, sz) = p + 4 + wastage_sizeclass[sz]`
    (`:56`). The wasted words sit between the pool header and the first slot,
    so the last slot ends exactly at `POOL_END`.
- **Size classes.**
  - There are `NUM_SIZECLASSES 32` classes, up to `SIZECLASS_MAX 128` words
    *including the header*.
  - `wsize_sizeclass` = {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 17, 19, 22,
    25, 28, 32, 33, 37, 42, 47, 53, 59, 65, 73, 81, 89, 99, 108, 118, 128}.
  - `sizeclass_wsize[whsize]` maps a size to its class in one load.
  - The table is generated by `tools/gen_sizeclasses.ml`, which keeps the
    overhead below `max_overhead = 0.101` and forces classes 16 and 32 for
    cache-line-aligned atomics.
- **Free slots.** A free slot has header 0. Its word 1 links to the next free
  slot in the same pool (`pool_initialize`, `:254`).
  - `pool_initialize` threads every slot of a new pool into `next_obj`.
  - In DEBUG builds the rest of the slot is filled with `Debug_free_major`.
- **Allocation.** `caml_shared_try_alloc` (`:428`) is called by
  `caml_alloc_shr` (`memory.c:425`), by the minor GC's promotion
  (`alloc_shared`, `minor_gc.c:153`) and by intern (`intern.c:418`).
  - If `whsize <= SIZECLASS_MAX`, it calls `pool_allocate(sizeclass_wsize[whsize])`
    (`:394`). That pops `r->next_obj`. If the pool becomes full, the pool moves
    from `avail_pools[sz]` to `full_pools[sz]`.
  - Otherwise it calls `large_allocate` (`:415`), which is a plain `malloc` of
    the object plus a 2-word `large_alloc` header (`owner`, `next`). The
    object goes on `swept_large`.
  - The new header is coloured `MARKED`: OCaml 5 allocates black.
- **Finding a pool.** `pool_find` (`:358`) tries, in order:
  1. `avail_pools[sz]`;
  2. sweeping `unswept_avail_pools[sz]` until a pool becomes available;
  3. `pool_global_adopt` (`:297`), which takes a pool orphaned by a
     terminated domain;
  4. `pool_acquire` (`:183`), which takes a free pool from
     `pool_freelist.free` or `caml_mem_map`s a new one.
- **Per-domain state.** `struct caml_heap_state` (`:88`) holds four lists per
  class: `avail_pools`, `full_pools`, `unswept_avail_pools`,
  `unswept_full_pools`. It also holds `swept_large`, `unswept_large` and the
  cursor `next_to_sweep`. There are no global free lists of objects, only of
  pools.

### 1.2 Sweeping

- **`pool_sweep(local, plist, sz, release_to_global_pool)`** (`:469`) takes
  one pool off `plist` and steps over it by `wsize_sizeclass[sz]`. For each
  slot:
  - header 0: it is already free;
  - `GARBAGE`: run the custom finaliser if there is one, set the header to 0
    and push the slot on `next_obj`;
  - otherwise: the slot is live, and the pool cannot be released.

  Afterwards the pool is released to `pool_freelist.free` (if it was entirely
  free and release is allowed), or it goes onto `full_pools` or `avail_pools`.
- **Live objects' headers are never rewritten.** `caml_cycle_heap_from_stw_single`
  (`:1391`) rotates the meaning of the three colours at the start of each cycle:
  - MARKED becomes UNMARKED;
  - UNMARKED becomes GARBAGE;
  - GARBAGE becomes MARKED (that set is empty, because it has been swept).
- **`large_alloc_sweep`** (`:535`) sweeps one large object per call and
  `free`s it if it is GARBAGE.
- **`caml_sweep(local, work)`** (`:566`) sweeps pools class by class
  (`next_to_sweep`), the avail ones before the full ones, then the large
  objects, until `work` is used up. It returns the work left over, which is
  positive only when sweeping is finished.
- **`caml_cycle_heap`** (`:1401`) runs at the end of a major cycle in the
  stop-the-world section (`major_gc.c:1463`). It moves every swept list to its
  unswept counterpart, and also adopts orphaned global pools.

### 1.3 When pages are swept

- **Lazily and incrementally.** `major_collection_slice` (`major_gc.c:1642`)
  sweeps first, in budgeted calls to `caml_sweep` (`:1683`), while
  `!sweeping_done`, and only then marks. The phase is
  `Phase_sweep_and_mark_main`: the sweep of cycle *n* overlaps the mark of
  cycle *n*+1. That is safe because sweeping frees only GARBAGE, and marking
  never produces it.
- **On demand.** `pool_find` sweeps an unswept pool of the requested class
  before allocating from it. It never allocates into an unswept pool.
- **To completion.** `caml_finish_sweeping` (`major_gc.c:1984`) loops on
  `caml_sweep(.., 10)`.
- **Compaction.** `caml_compact_heap` (`shared_heap.c:938`) runs only when
  forced (`major_gc.c:1468`). It evacuates sparse pools of each class into
  denser ones and rewrites pointers. Without it, partly empty pools are never
  merged.

### 1.4 Two properties worth keeping

- **Allocation sweeps at most one pool.** A pool on `unswept_avail_pools` had
  at least one free slot (header 0) when the cycle started. `pool_sweep`
  leaves free slots alone and sets `all_used = 0` when it sees one. So the
  first unswept-avail pool that `pool_find` sweeps becomes available, and the
  `while` loop at `:366` runs at most once per call.
- **No coalescing.** Free space never crosses a slot. The only merging is a
  whole free pool going back to `pool_freelist.free`.

### 1.5 Splitting blocks in OCaml 5

- **`Obj.truncate` is gone.** It is not in `stdlib/obj.mli`; in 4.14 it is at
  `obj.mli:75`.
- **intern does not re-tile major blocks.** Each object is allocated
  separately: `intern_alloc_obj` (`intern.c:406`) calls
  `caml_shared_try_alloc` per object when the total is too large for the minor
  heap. Small totals still use one minor block, which is re-tiled
  (`intern_alloc_storage`, `:373`). That is safe because the minor GC copies
  objects one by one.
- **Allocation does not collect.** `caml_shared_try_alloc` never starts a
  collection, so intern cannot be interrupted part way.

## 2. A, as it stands

This is a brief summary; the details are in `WT/docs/allocator-table-and-size-lists.md`.

**Heap.** One `calloc` block of fixed size (32M words by default, or
`MIN_EXPANSION_WORDSIZE`), set up in `ensure_heap` (`alloc_gen.c:114`). It
never grows. When allocation fails, `verified_allocate` runs `do_full_gc` and
retries. If that fails too, the result is `Out_of_memory`.

**Allocation** (`GC.Impl.Allocator`):
- There are 17 heads. List *w* (1–16) holds exactly the free blocks of wosize
  *w*. List 0 holds larger blocks, in first-fit order.
- `alloc_lists_impl` (`:480`) tries list *w*, then lists *w*+1 to 16, then
  list 0. It carves right-justified, and if the remainder's class changes it
  moves the remainder to its new list ("relist").
- Wosize-0 remainders are fragments that are on no list.

**Sweep.** `GC.Impl.FusedSweepCoalesce.fused_sweep_coalesce` (`:116`):
1. `clear_heads` sets all 17 heads to 0.
2. One ascending walk turns black objects white.
3. Each maximal run of non-black objects is merged into one blue block and
   pushed onto `heads[class(rw-1)]`.
4. The walk also rebuilds the object-start table exactly.

**Object-start table.**
- There is one entry per 64 KB window. `table_sound` (each entry is a walk
  position, at or below its boundary, non-decreasing) always holds.
- `table_ok` (exact) holds after a sweep and is a conjunct of `gc_safe`.
- It supplies the cut points for a parallel sweep, whose correctness needs
  only `valid_bounds` (every cut is a walk position).
- It is weak in general because intern.c (`intern.c:375`) and Obj.truncate
  (`obj.c:214–217`) add walk positions it is not told about. This is decision
  (b) in the memory note "object table intern flaw".

**Measured (allocator note §7.5, bytecode, against `1ecb000`):**

| Program | Before #46 | A (#46) |
|---|---|---|
| hamming (16M words) | 70.46 s | 0.283 s (stock 0.19 s) |
| livemap | 32.1 s | 7.96 s |
| binarytrees 16 | 12.72 s | 12.85 s (+1.0%) |
| binarytrees 18 | 52.52 s | 53.25 s (+1.4%) |
| livegraph | 4.48 s | 4.58 s (+2.3%) |

**Request profile, measured (§7.5):**
- binarytrees 18 takes 99.99% of its requests from list 0 and skips 7 empty
  heads per request.
- Its request sizes are wosize 3 (39.5M) and wosize 128 (39.6M).
- livemap requests wosize 2 and 5; livegraph requests wosize 1, 3 and 4.

**Parallel sweep, measured (`docs/parallel-sweep-phase1.md`, branch
`sheera/parallel-sweep`):**
- `sweep_par_correct` is proved, but against the single-list sweep from
  before #46.
- Without the table it was slower everywhere (0.01–0.76×), because `prepass`
  is a serial walk of the whole heap.
- The combined design (`parallel-gc-combined-design.md` on
  `sheera/parallel-mark-proto2`) *estimates* about 2.4× on binarytrees 18 at
  4 threads with the table and a parallel mark.

**Incremental sweep.** `origin/akhil/incremental-sweep` (`ef630284`) adds
`VERGC_SWEEP=incremental`, with `sweep_slice` and `finish_sweep` in
`GC.Gen.Impl.Incremental`.
- An object allocated during the sweep is coloured black if it is ahead of
  the cursor and white if it is behind it.
- It works on the single list from before #46 and conflicts with both #46 and
  #48.

## 3. B, sketched for our collector

OCaml 5's design assumes several domains, `malloc` for large objects, and no
need to walk the heap. Ours has one mutator, one fixed region, and proofs
built on the walk. The sketch below keeps what matters from OCaml 5 and
changes the rest.

### 3.1 Layout

- **The region stays.** It is the same contiguous `calloc` region from
  `ensure_heap`. Its first page starts at `Z` (aligned up to a page), and it
  is divided into **pages of 4096 words (32 KB)**, as in OCaml 5.
  - A 64 KB page would match the table window. But the generator then gives
    fewer classes for the same overhead, and a sparse page wastes more.
    4096 is the default; 8192 is a measurement option.
- **The page map is a side table.** `pm[n_pages]` is a Pulse array, like the
  object-start table. Each entry has a kind `Free | Pool c | Large`, a
  free-slot head, a next link, a live count and a `swept` bit.
- **Page metadata stays out of the heap.**
  - This differs from OCaml 5's in-page `struct pool`.
  - The mutator then never sees metadata words.
  - It also leaves no 4-word header to explain to the walk.
- **Size classes.** I ran `gen_sizeclasses.ml` with `max_slot = 257`, so that
  every promotion from the minor heap fits a class (`Max_young_wosize = 256`).
  - It gives 40 classes: {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 17, 19, 22,
    25, 28, 32, 36, 40, 45, 51, 57, 63, 70, 78, 87, 96, 105, 114, 126, 141,
    153, 167, 183, 204, 216, 229, 245, 257} (whsize).
  - The worst rounding is 10.0%.
  - The benchmarks' sizes fall like this:
    - wosize 1–5 (whsize 2–6): exact;
    - wosize 128 (whsize 129): rounds to 141, which is 8.5%.

  Stock OCaml 5's `max_slot = 128` would send binarytrees' 128-word blocks to
  the large path. The classes are data, so the proofs need not depend on them.
- **Large objects** are those with whsize > 257. They live in **large pages**:
  runs of consecutive pages marked `Large`, managed by A's list-0 allocator
  (first fit, right-justified, coalescing). Coalescing stops at the edge of a
  run. Two alternatives were considered:
  - one page run per object, the analogue of OCaml 5's `malloc`, which wastes
    up to 32 KB at the tail of each object;
  - a fixed split of the heap, with pools at the bottom and large space at the
    top. This is cheaper to prove, but free pool pages cannot then serve large
    requests.

### 3.2 Keeping the heap tiled

The invariant is `objects zero_addr g`: every word is covered by a header, and
the walk ends exactly at `heap_size`. B keeps it as follows.

- **Free slot:** one blue header of wosize `wh_c - 1`. Field 0 holds the
  link. This is the format today's free blocks use.
- **Allocated slot, `whsize < wh_c`:** the object, then one filler header for
  the remainder. The filler is a wosize-0 fragment if the remainder is one
  word, as A already allows, and otherwise a fragment of no-scan wosize.
  - Fillers are never reachable and are never on a list.
  - Classes 1–8 are exact, so the small sizes that dominate the benchmarks
    need no filler.
- **Page tail:** `4096 mod wh_c` words. They form one filler at the end of
  the page, where OCaml 5 puts the wastage at the start.
- **Free page:** one blue block covering the page, linked from the free-page
  list.

With this, the extracted verified mark, the Cheney collection and every
walk-based lemma run unchanged on a B heap. The unverified prototype can also
reuse them as they are (§6).

### 3.3 Allocation

- **Small (whsize ≤ 257):**
  1. `c = class[whsize]`; `p = avail[c]`.
  2. If `p` is null:
     - sweep one unswept page of class `c` that has a free slot (incremental
       mode only);
     - otherwise take a free page and initialise it as `Pool c`.
  3. Pop a slot. Write the header, and the filler if needed. If the page is
     now full, move it to `full[c]`.
  4. If there is no free page, run `do_full_gc` and retry, as today.
- **Colour.** The object is white, as in 4.14. It is not black as in OCaml 5,
  because our runtime uses the 4.14 colour encoding (§4.6).
- **Large:** A's list-0 first fit, restricted to large runs. If none fits,
  take a run of free pages, mark them `Large` and push them as one blue block.

### 3.4 Sweep

For each pool page, step slot by slot:
- a black slot becomes white;
- a white slot, or a blue one not yet listed, becomes blue and goes on the
  page's list.

Then:
- a page with no live slot goes back to the free-page list;
- a page with free slots goes to `avail[c]`;
- any other page goes to `full[c]`.

For large runs, run A's fused sweep restricted to the run. An empty run goes
back to free pages, merged with neighbouring free pages.

Fillers in a slot are absorbed when the slot is freed. Only the header at the
slot start decides whether the slot is live (§4.4).

## 4. Comparison

### 4.1 Correctness: can `gc_correct` be proved, and what carries over?

`gc_correct` (`WT/mark-and-sweep/impl/GC.Impl.Correct.fst`, 595 lines, no
admits) states:

- **`gc_safe`:** `well_formed_heap`, `full_gc_correctness`,
  `major_gc_live_subgraph_isomorphism`, `fl_sound` and `table_ok`.
- **`gc_live`:**
  - (a) `unreachable_reclaimed`;
  - (b) `free_blocks_listed`;
  - (c1) `coalescing_lossless`;
  - (c2) `heap_partitioned`.

| Clause | A (#46 + #48) | B (§3) |
|---|---|---|
| `well_formed_heap`, walk | Proved. | **Carries over.** The tiling is kept (§3.2). |
| `full_gc_correctness`, isomorphism | Proved. | **Carries over.** The mark is unchanged, and the sweep turns black to white per object as before. |
| `fl_sound` | Per list, with `fls_class` and `fls_exact`. | **New, simpler:** each page list holds only the page's own blue slots, each at a slot start, linked without cycles. `FreeLists.Push` can be reused. |
| `table_ok` | Exact after the sweep; `table_sound` always. | **For pool pages, not needed:** page starts are walk positions by `pages_ok`. Large runs need a table only if they are swept in parallel (§4.2). |
| (a) unreachable reclaimed | Proved. | Holds per slot: a dead object's slot becomes blue. **Needs the slot-start rule** (§4.4). |
| (b) free blocks listed | Routed by class. | **Restated:** every blue slot is on its page's list; every free page is on the free-page list. |
| (c1) coalescing lossless | No two adjacent blue blocks. | **Replaced** in pool pages by "a page with no live slot is a free page"; kept inside large runs. This is weaker than A's: two adjacent free slots stay separate by design. |
| (c2) heap partitioned | white + listed + fragments. | Same form. Fillers and page tails count as fragments. |

**The key new invariant for B, `pages_ok g pm`:**
1. Every page start is a walk position, except inside a large run, where only
   the run start is.
2. In a `Pool c` page, the slot starts `first + k·wh_c` are walk positions.
   The walk from a slot start stays inside the slot. The page tail is one
   filler.
3. The page's list is exactly its blue slots. `live count` = number of
   non-blue slots, if the count is kept in the proof at all.
4. Allocation and incremental sweep: a page with `swept = 1` contains no
   black slot.
5. A large run is a sub-heap that satisfies A's list-0 invariants.

**Which proofs carry over:**
- **Unchanged:** the mark (`GC.Spec.Mark`, `MarkBoundedCorrectness`, skip
  rescan), the Cheney ladder, `HeapAgree`, `Partition`, `WalkEnd`, and the
  `well_formed_heap` lemmas in `Fields.fst`.
- **New:** the allocator spec (a pop from a page list is A's exact pop with
  leftover 0, plus a filler write) and the per-page sweep.
- **Reused by restriction, for large runs:** `Coalesce.Correct` (3,839 lines)
  and `SweepCoalesce`.
  - This needs one change: a run of free blocks ends at a page-kind boundary.
  - `HEAP_EXPANSION.md:154–165` already describes the same change for chunk
    edges.
  - It is the riskiest proof edit in B, because `fused_aux` is long.

**Can safety and liveness both be proved for B?** Yes; I see no clause that
cannot be. The one weaker conclusion is (c1), and the weakening is the point
of the design.

**Risks to correctness:**
- A: the table exists only in the weak form (decision (b)). The claim that
  intern and truncate only *add* positions is audited, not proved.
- B: the slot-start rule (§4.4) needs the runtime never to place two
  independent objects in one pool slot. That holds if intern's major path
  goes to large runs, which it does by size (§4.4).

### 4.2 Speed for each collector

**Sequential**

- **Allocation.**
  - A: an exact hit for wosize ≤ 16 is O(1). binarytrees, however, takes
    99.99% of its requests from list 0 and skips 7 empty heads each time
    (measured).
  - B: O(1) for every size up to 257: one table load and one pop. When a page
    fills there is one list move.
  - *Estimate:* B allocates faster than A on binarytrees and livemap, and
    about as fast on hamming (where A is already O(1)).
- **Locality.**
  - A carves consecutive promotions from the top of one large block, so a
    promoted tree is contiguous.
  - B separates sizes: binarytrees' 3-word nodes and 128-word blocks go to
    different pages.
  - The effect on mark time is unknown in either direction. It must be
    measured.
- **Sweep.**
  - A writes one header and one link per *run* of dead objects.
  - B writes them per *dead slot*. binarytrees frees long runs, so B does more
    writes there.
  - B also does no `clear_heads`, no relisting and no table rebuild.
  - *Estimate:* sweep time is within ±20% either way. Over the whole run, that
    is a few percent.
- **Collections.** If rounding and sparse pages make the occupied heap
  bigger, B may collect more often at a fixed heap size, and run time rises.
  This is the most likely source of a sequential loss beyond 5%. It is why
  §6 also measures the minimum heap.

**Parallel sweep, 1, 2 and 4 threads**

- **A:**
  - Cuts come from the table.
  - Each segment sweeps and coalesces on its own. The join then merges the
    runs that cross a cut, and concatenates the 17 lists of every segment in
    descending order.
  - The table must be rebuilt in the same pass. Each segment rebuilds its own
    windows, but entries at segment edges depend on the join.
  - `sweep_par_correct` must be re-proved for 17 lists and the table.
- **B:**
  - The page list is split into contiguous ranges, one per thread.
  - Each thread sweeps its pages, and builds per-class avail and full lists
    and a free-page list.
  - The join only concatenates `threads × 40` lists. There is no run merging
    and no table.
  - Large runs are swept serially; they are usually few objects.
- **Load balance.**
  - B: any page boundary is a cut, so the work per thread is within one page
    (4096 words) of even.
  - A: the work per thread is within one table window (8192 words) of even
    while the table is exact. When it is not (§1.2 of the allocator note), a
    region refilled from one large block stays a single segment.
- *Estimate:* both scale on the sweep itself. B has less serial work
  (no join, no table repair) and a simpler proof.

**Incremental sweep: the longest pause**

- **A:**
  - The sweep starts with `clear_heads`, so mid-sweep only blocks behind the
    cursor are listed.
  - A request that fits nothing yet listed must either sweep forward until a
    fitting run appears or call `finish_sweep`. A large request can therefore
    pause for up to the rest of the sweep.
  - The akhil branch's black-ahead / white-behind rule also makes every
    allocation compare against the cursor.
- **B:**
  - The unit of sweeping is one page: at most 4096 words, about 1,000 slots
    for small classes.
  - An allocation sweeps at most one page (§1.4).
  - The colour rule is per page: allocation happens only in swept pages, so a
    new object is white. There is no cursor test.
  - The longest pause is about one page sweep, a few microseconds. The
    exception is a large request that finds no large run and no free page.
    That forces sweeping to finish, as in A, but only for the large space.

### 4.3 Memory use and fragmentation

| Source | A | B |
|---|---|---|
| Rounding within a size | None: exact fit or split. | Up to 10% per object, by the generated table. binarytrees: 8.5% on its 129-word blocks, about 97% of its words. |
| Page tail | None. | `4096 mod wh_c` words per page, at most 245 words (whsize 257: 15 slots, 237 words). |
| External fragmentation | Small holes between live blocks. Today 1–2-word holes are on lists 1–2 and do not slow list 0. They are lost only if no request of that size comes. | A page with one live slot keeps 32 KB. There is no compaction. A program that leaves one survivor per page in a class it no longer allocates holds that memory until the survivors die. |
| Coalescing | Yes, everywhere. | Only whole pages, plus inside large runs. |
| Metadata | 17 heads, and the table (8 bytes per 64 KB). | The page map, about 32 bytes per 32 KB page (0.1%), plus 40×2 heads. |

**Peak heap.** Our heap is a fixed region, so the fair measure is the
**smallest `MIN_EXPANSION_WORDSIZE` at which a program completes**, which is
what `make bench-min-heaps` finds. §6 also records occupied words after each
sweep.

### 4.4 The 4.14 runtime's block splitting

- **intern.c, 4.14.**
  - For a total `wosize ≤ Max_young_wosize` (256), it allocates one minor
    block (`intern_alloc`, `intern.c:633`) and re-tiles it. The minor GC
    copies each sub-object separately, so neither A nor B sees anything.
  - For 256 < wosize ≤ `Max_wosize`, it calls `caml_alloc_shr_no_track_noexc`
    (`:638`) and re-tiles a major block (`:375`):
    - In A, this is the cause of decision (b).
    - In B, this block has whsize > 257 and so goes to a **large run**, where
      A's walk-based sweep frees each sub-object separately, exactly as today.
      Pool pages never see a re-tiled block.
  - Above `Max_wosize`, `intern_add_to_heap` (`:664`) is already fatal under
    the patch.
- **Recommended for B anyway: intern each object separately on the major
  path, as OCaml 5 does** (`intern.c:406`). Without it, a large unmarshalled
  structure puts millions of small objects in a large run, where they are
  swept serially and never share pool pages.
  - Our `verified_allocate` may collect on failure, and a collection must not
    run in the middle of intern.
  - The total `whsize` is known before intern starts. So the plan is to
    collect *before* intern if fewer than `whsize × 1.1` words plus some pages
    are free, then allocate without collecting.
  - This change would also let A keep the table exact (§2 of A's note
    rejected it for A).
- **Obj.truncate (4.14 `obj.c:184`).** It writes a leftover header inside the
  object. The leftover is black in the major heap (`frag_color`).
  - **A:** it adds a walk position. The table survives because it is only
    sound, not exact, and "black ⇒ root" is broken until the next collection.
  - **B, pool slot:** the slot is still decided by its start header, the
    truncated object, and the slot is freed whole when that object dies. The
    leftover's colour is never read. Tiling still holds (object + leftover +
    filler).
  - **B, large run:** the same as A.
  - It is deprecated in 4.14 and removed in 5.0. Making it fail early, as was
    done for weak arrays, is an option for both.
- **`caml_alloc_shr(0)`** is a known hazard in both, and unchanged.

**The slot-start rule.** In a pool page, a slot is live if and only if the
header at the slot start is black. This is sound exactly when no other
reachable object starts inside the slot. Truncate creates only an unreachable
leftover. Intern never uses pool slots. Nothing else in 4.14 writes headers
inside a block; the audit in §8.4 of A's note lists the writers.

### 4.5 Proof effort (estimate)

**A, still to do:**
- re-prove `sweep_par_correct` for 17 lists and the table;
- the parallel-sweep join with table repair at cuts;
- port the incremental sweep (akhil branch) to 17 lists and the table,
  including mid-sweep allocation against lists that are only partly rebuilt.

**B, to do:**
1. `pages_ok` and its frame lemmas. *Estimate:* 1.5–2.5K lines.
2. Allocator: class lookup, page-list pop, filler write, page acquire.
   It reuses the exact-pop lemmas. *Estimate:* 2–3K lines.
3. Per-page sweep plus page release. It reuses `Sweep` colour lemmas and
   `FreeLists.Push`. *Estimate:* 2–4K lines.
4. Large runs: A's fused sweep with runs that stop at page-kind edges, plus
   restricting `Coalesce.Correct`. *Estimate:* 1–3K lines changed, and this is
   the main risk.
5. Restating liveness, (b), (c1) and (c2): 1–2K lines.
6. Changing the allocator-state type again through about 20 Pulse functions
   and 170 vals, as #46 did.

**B, in exchange:**
- The parallel sweep is a separating composition over disjoint pages, with no
  join proof.
- The incremental invariant is a bit per page.
- No table exactness for pools.

The total is of the same order as #46 and #48 together. The parallel and
incremental proofs that follow are smaller for B than for A.

### 4.6 Colours

OCaml 5 rotates the meaning of colours so that the sweep never rewrites a
survivor's header (`caml_cycle_heap_from_stw_single`). That saves one write
per survivor, but our 4.14 runtime and its patch read fixed colours
(`Is_white_val`, `Is_black_val`, and intern's `intern_color`). I would not
adopt rotation now. B does not depend on it.

## 5. Scorecard

| Criterion | A | B | Remark |
|---|---|---|---|
| 1. Correctness | Proved sequentially. The table is sound only, and its preservation by intern and truncate is audited. | Provable. The walk is kept, so most of the safety proofs carry over. Two edits are risky: liveness (c1) and coalescing in large runs. | about even; B's parallel and incremental cases are easier |
| 2a. Sequential | Measured; 1–2% slower than before #46 on binarytrees. | Unknown. Allocation is faster; sweep writes and rounding work against it. | measure |
| 2b. Parallel sweep | Needs an exact table and a join. | Pages are independent. | B |
| 2c. Incremental pause | Up to the rest of the sweep for an unlucky request. | About one page; at most one page per allocation. | B |
| 3. Memory | Exact fit and coalescing. | Up to 10% rounding, and sparse pages. | A |
| 4. Block splitting | Decision (b). | Contained in large runs; per-object intern recommended. | B, slightly |
| 5. Proof effort | Smaller now, larger later. | Larger now, smaller later. | about even overall |

## 6. A fair measurement

### 6.1 Prototype

- **Code.** An unverified C implementation of B in
  `generational/ocaml-integration/verified_gc/` (for example
  `alloc_pages.c`), selected at build time (`-DVERGC_ALLOC_PAGES`). It
  replaces `allocate` and the sweep only.
- **Unchanged.** The extracted mark, Cheney collection and root handling. They
  work because the heap stays tiled (§3.2).
- **The sweep hook.** It enters through a hook in the sweep step of
  `gen_gc`, like the parallel sweep's `vergc_sweep_hook`.
- **Parameters.** Pages of 4096 words; the 40 classes of §3.1. Large runs use
  a C copy of A's list-0 allocator and fused sweep, with runs that stop at
  page-kind edges.
- **Intern.** Intern is changed to allocate per object on the major path
  (§4.4). The change is behind its own flag, so that B can also be measured
  without it.
- **Parallel sweep.** `pthread` workers, started once and reused. Each sweeps
  a contiguous range of pages. Thread count is set by
  `VERGC_PAR_SWEEP_THREADS` = 1, 2 or 4.
- **Incremental sweep.** `VERGC_SWEEP=incremental`. At each collection the
  pages become unswept. A sweep slice sweeps *k* pages, and an allocation
  sweeps at most one page of its class first, as in `pool_find`.

### 6.2 Correctness checks

The checks match those used before.

1. **The same result as the verified collector at every collection.** In a
   check build (`VERGC_PAGES_CHECK`), at every major collection after the mark:
   1. copy the heap;
   2. run the extracted, verified `fused_sweep_coalesce` on the copy (the
      heap is tiled, so its precondition holds);
   3. record the set of surviving headers and their contents;
   4. restore, run B's sweep, and record the same;
   5. abort unless:
      - the survivor sets and contents are identical;
      - every non-survivor word is covered by a blue slot, a free page, or a
        blue block in a large run.

   Addresses cannot be compared across allocators, but survivors at the same
   heap snapshot can. A control flag (`..._CHECK_CONTROL=1`) runs a mutant
   that skips the last slot of every page, to show that the check catches a
   difference.
2. **An invariant checker after each collection.** In the style of
   `-DVGC_CHECK_ALLOC`, it checks:
   - `pages_ok`;
   - the per-page lists (no duplicates, each entry a blue slot of the page);
   - the free-page list;
   - that the walk ends at `heap_size`.

   The checks also run in the parallel mode (by comparison with 1 thread) and
   in the incremental mode (at the end of each sweep).
3. **`make test`** and **`make test-native`**.
4. **The OCaml testsuite.** Use `ci/build-verified-toolchain.sh` and
   `ci/run-testsuite.sh`, gated on `ci/expected-failures.txt`. The last
   baseline was 2,925 passed, 55 failed and 7 errors out of 3,141. B must add
   no new failures.
5. **Program output** must be byte-identical to stock OCaml and to A on every
   benchmark.

### 6.3 Benchmarks

**Programs:** hamming (16M and 8M words), binarytrees 16 and 18, livemap,
livegraph, and the four Sandmark programs. I did not find a fixed list of four
in the repo, so please name them. All programs are run in bytecode, and in
native code as well where the earlier notes did.

**Builds:**
- **A:** `sheera/object-table`, which is #46 plus #48.
- **B:** the prototype on the same base.
- **Stock:** for reference.

**Rules:**
- The same machine, `hyperfine`, at least 5 runs each.
- No `sample`, `lldb` or attaching tool.
- Timers are inside the runtime, using `clock_gettime`.

| Collector | Metric | How |
|---|---|---|
| Sequential | Run time | `hyperfine` wall time at the benchmark's usual `MIN_EXPANSION_WORDSIZE` |
| | Collection time | Mark, sweep and minor collection, from in-runtime timers, summed per run |
| | Allocation time | Major allocations, in total and by size class, from counters in a separate stats build |
| | Peak heap | (i) The smallest heap size at which the program completes (`bench-min-heaps`, by bisection). (ii) The maximum over collections of the words in use after the sweep: for B, pages in use × 4096; for A, the walk words that are not free. (iii) Words lost to rounding and page tails (B), and to fragments (A). |
| Parallel | Sweep time at 1, 2 and 4 threads | B by pages; A by the object-start table, using the parallel sweep of `sheera/parallel-sweep` adapted to 17 lists, or a C prototype of it if that port is not ready. Report the median sweep time per collection, and the speedup over each allocator's own sequential sweep. |
| Incremental | Longest pause | Interleave the sweep with allocation while the program runs. For B, page by page. For A, the akhil incremental sweep adapted to the size lists, with slices of the same number of words (4096). Record each mutator-visible pause (slice + sweeping during allocation + `finish_sweep`). Report the maximum, the 99th percentile, and the total. |

**Decision.** Choose B if all of the following hold:
1. Every correctness check passes.
2. B's sequential run time is at most 5% above A's on every program.
3. B's parallel sweep at 4 threads is clearly faster than A's (for example,
   at least 1.3× faster on binarytrees 18 and livemap).
4. B's longest incremental pause is clearly shorter.

A minimum heap more than 10% above A's is a warning sign. If it appears,
tune the classes (for example, add a class at 129) and measure again.

## 7. Main risks

1. **Memory.** Class rounding (8.5% on binarytrees' main size) and sparse
   pages could raise the minimum heap and the number of collections, and so
   exceed the 5% limit.
2. **Proving coalescing that stops at page-kind edges** inside
   `Coalesce.Correct` / `fused_aux`, for large runs.
3. **The change to intern.c** to allocate per object without collecting part
   way. Without it, unmarshalled data stays in serially swept large runs.
4. **The slot-start rule** depends on an audited fact about 4.14: that nothing
   places two reachable objects in one pool slot. It is not proved.
5. **Locality** of promoted structures that are now split across pages by
   size. Mark time could change in either direction.
6. **Fairness of the A baselines.** A's parallel and incremental sweeps exist
   only for the single list. Porting them to 17 lists for the comparison is
   work in itself, and a weak port would favour B.
