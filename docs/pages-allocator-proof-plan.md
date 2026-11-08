# Proof plan: the OCaml 5-style page allocator (B2)

This is the plan for proving B2. Stage 1, the specification, and stage 2,
the allocator, are done on branch `sheera/pages-allocator`, which is based
on `origin/sheera/size-lists` (§9, §10). The allocator leaves a new
object's fields to its caller, as `caml_alloc_shr` does (§10).

**Decisions (2026-11-08):**
- **Size limit:** a block is small when `whsize ≤ 128`, as in OCaml 5.
- **The smallest class is 2 words.** OCaml 5's 1-word class is dropped, so
  there are 31 classes. A 1-word block takes a 2-word slot: its header, then a
  1-word filler (§1.3).
- **Base:** #46 plus `1d3e401a` (weak arrays, ephemerons and `Gc.finalise`
  fail early), without the object-start table of #48 (§5).
- **The minor collection goes behind an allocator interface** (§1.5).
- **`Obj.truncate` fails early,** reusing `b14ae30b` (§4.2).

**Goal.** Implement and prove B2 with our sequential collector.
- Small blocks go in pages, by OCaml 5's size classes.
- Larger blocks go in a separate large-object area, at their exact size.
- The size-class table and the page size are parameters. Their conditions
  are stated once, so no proof depends on their values.
- The two candidate page sizes are 16 KB (2048 words) and 32 KB (4096 words).

**Designed for the next step.** The sequential collector will later be
replaced by an incremental one. To keep that step small, this stage
already has:
- a self-contained, proved `sweep_page` that depends only on its own page;
- a swept or not-swept state for each page from the start;
- an allocator whose correctness depends only on swept pages.

**Sources.**
- **The measured prototype.** B2 is in `proto/alloc_pages.c`
  (`VERGC_B_VARIANT=2`), on `sheera/alloc-pages-proto` in
  `~/Documents/pgc-size-lists` (written `WT/` below).
  - The results are in `WT/docs/allocator-comparison-results.md` §9.
- **The proofs referred to** are on `sheera/size-lists` (PR #46, `3be9eb36`)
  and `sheera/object-table` (PR #48).
- **The other branches drawn on:**
  - `akhil/incremental-sweep` and `akhil/incremental-mark`;
  - `sheera/parallel-sweep` (origin, `8e9895bf`).
- **OCaml sources.** OCaml 5 is `~/ocaml` at `243f4cd378`. OCaml 4.14 is the
  patched tree built by `ci/build-verified-toolchain.sh`.

**Labels.**
- *Measured* numbers name their note.
- *Estimate* marks guesses.
- Line counts of existing files come from `wc -l` on `WT/`.

---

## 0. Summary

1. **The specification is a page map beside the heap we already have.**
   - The heap stays one tiled region, and `objects zero_addr g` still walks
     it.
   - A side table records each page's kind (free, pool of class *c*, or
     large run) and whether it is swept.
   - The new invariant, `pages_ok`, ties the walk to the page map.
2. **Three theorems carry the work:**
   - `sweep_page_correct`, about one page, with a frame;
   - `alloc_correct`, about swept pages only;
   - `gc_correct`, restated with the same safety and liveness headings as
     today.
3. **About 30k of the existing ~99k proof lines carry over unchanged.** These
   are the mark, the heap walk, the reachability files, and the half of the
   minor collection that never touches the allocator.
   - The rest of the minor collection changes in one way. It calls
     `alloc_lists_spec` by name and uses the free-list facts that come with
     it. B2 moves it behind an allocator interface.
4. **The 4.14 runtime needs one small trusted change** (§4): `Obj.truncate`
   must fail early. `caml_alloc_shr(0)` no longer needs a runtime fix: a
   1-word block takes a 2-word slot, and the verified allocator writes its
   filler.

   intern.c can stay as it is: its major-heap blocks are always large.
5. **The object-start table of #48 is no longer needed** (§5). Pages give the
   cut points for a parallel sweep. Base B2 on #46 without #48.
6. **Effort, estimated:** 20–33k proof lines new or changed (§6). That is 2–3
   times #46, which was +8.4k/−3.1k.
7. **The main risk** is restricting #46's coalescing sweep (`fused_aux`,
   `Coalesce.Correct`) to one large run.

---

## 1. Specification

### 1.1 Parameters, stated once

The parameters live in one interface, `GC.Spec.Pages.Params.fsti`. Every
other module sees only that interface, so no proof can unfold a value.

```fstar
val page_wsize : pos                          (* 4096 or 2048 *)
val n_cls      : pos                          (* 31 *)
val cls (c: nat{c < n_cls}) : pos             (* slot size in words, header included *)
let small_max : pos = cls (n_cls - 1)         (* 128 *)

let params_cond : prop =
  (* C1 *) cls 0 >= 2 /  (* C2 *) (forall (c: nat). c + 1 < n_cls ==> cls c < cls (c + 1)) /  (* C3 *) small_max <= page_wsize /  (* C4 *) page_wsize < pow2 20
val params_ok : unit -> Lemma params_cond
```

- **C1** lets a free slot hold its header and its link.
- **C2** makes the table a strictly increasing list of sizes.
- **C3** puts at least one slot of every class in a page.
- **C4** keeps page arithmetic far from overflow.

**The class table** is OCaml 5's (`runtime/caml/sizeclasses.h`) without its
1-word class: {2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 17, 19, 22, 25, 28, 32,
33, 37, 42, 47, 53, 59, 65, 73, 81, 89, 99, 108, 118, 128}.

**The page size.** `GC.Spec.Pages.Params.fst` defines both candidates,
`page_wsize_16k = 2048` and `page_wsize_32k = 4096`, and proves the
conditions for both by normalisation (`both_candidates_ok`). `page_wsize` is
set to one of them; changing it is a one-line edit and a rebuild, not a
re-proof. It is 4096 for now, the size B2 was measured at.
- This replaces the earlier idea of two `.fst` instances chosen by include
  path. One file is simpler for the build and checks both candidates on every
  build.

**`class_of` is defined, not assumed.** `GC.Spec.Pages.Layout.class_of w`
is the least class whose slot holds `w` words, for `1 ≤ w ≤ small_max`. That
it fits and is least are lemmas proved from C1 and C2 (`class_of_fits`,
`class_of_least`), so they are not conditions.

**Deliberately not conditions:**
- **The waste bound.** OCaml 5's generator keeps waste below 10.1%. That is
  about memory, not correctness. At 16 KB, OCaml 5's table reaches 12.7%
  (a 119-word block in a 128-word slot, 15 slots per page). At 32 KB it
  reaches 10.0%.
- **Cache-line classes** (16 and 32 words).

**The heap and pages.**
- Page *i* covers `[zero_addr + i·page_wsize·8, … + page_wsize·8)`. Pages are
  a logical division of the `calloc` region, as in the prototype; no
  hardware alignment is needed.
- **No new assumption about the heap size.** The heap's tail after the last
  whole page, fewer than `page_wsize` words, is either too short for a
  header or one blue block on no list (`tail_shape`). The bridge still
  rounds `MIN_EXPANSION_WORDSIZE` up so that the tail is empty, but the proofs
  do not rely on that. This replaces the condition P5 of the first draft,
  which would have been a new configuration axiom.

### 1.2 The page map

The page map is a Pulse array `pm` of `n_pages` records, outside the heap,
like #48's table. Its ghost view is `pm : seq page_info`.

```fstar
type page_kind = Free | Pool of c:nat{c < n_cls} | LargeHead of n:pos | LargeCont
type page_info = { kind: page_kind; swept: bool;
                   free_head: U64.t;   (* Pool: first free slot, 0 = none *)
                   nfree: U64.t;       (* Pool: number of free slots *)
                   next: U64.t }       (* Pool: link in avail[c] *)
```

The allocator state is
`ast = { pm; avail: array U64.t (n_cls); large: fl_state (#46's 17 heads); hint: U64.t }`.
- `avail[c]` lists the *swept* `Pool c` pages that have a free slot, linked
  through `next`.
- `hint` is only where scans for a free page start. It carries no invariant:
  the scan wraps around.
- There is no free-page list. Taking a page scans `pm` for `Free`, which
  saves proving a second list.

### 1.3 Page layout (in the heap)

**Free page.** One blue block, wosize `page_wsize − 1`.

**`Pool c` page.**
- With `wh = cls c` and `ns = page_wsize / wh`, slot *k* (k < ns) starts at
  `page + k·wh`.
- The tail, `page_wsize mod wh` words, is one *filler* at the page end.
- **A difference from OCaml 5 and the prototype.** They put a 4-word pool
  header and the wastage at the page start. Our metadata is in `pm`, so
  the slots start at the page start.
- **A free slot** is one blue block of wosize `wh − 1`. Field 0 links to the
  next free slot of the same page, or holds 0.
- **A used slot** holds an object of whsize `w ≤ wh` at the slot start. If
  `w < wh`, a filler of `wh − w` words follows. A 1-word block (wosize 0,
  as `caml_alloc_shr(0)` makes) takes a 2-word slot with a 1-word filler.
  - A 1-word filler is a wosize-0 header, the fragment A already allows.
  - A longer filler is a blue block.
- **Fillers** are recognised by position: inside a slot after its object, or
  in the page tail. They are never on a list and never pointed to.

**Large run.**
- `LargeHead n` at page *p*, followed by `n − 1` `LargeCont` pages, is a
  *run* covering `[pa p, pa (p + n))`.
- Inside a run is a sub-heap with #46's rules:
  - the walk from `pa p` ends exactly at `pa (p + n)`;
  - objects are white, black or blue;
  - free blocks are blue.
- Merging stops at the run's edges: a blue block never crosses `pa (p+n)`.
- **Free pieces smaller than `lg_min = small_max + 1` words are unlisted.**
  No large request could use them. The prototype's B3-8K took over 10
  minutes on binarytrees when they were listed (results §9.1).
  - They count as fillers until the sweep merges them with a neighbour.

### 1.4 The invariants linking them

`pages_ok g ast` is the conjunction of the following.

| | Clause | Meaning |
|---|---|---|
| L1 | tiling | `well_formed_heap g` (unchanged). Every `Free`, `Pool` and `LargeHead` page start is a walk position. |
| L2 | free page | `Free` ⇒ one blue block covering the page. |
| L3 | pool shape | `Pool c` ⇒ every slot start is a walk position. Each slot is free or used (§1.3). The tail is one filler. |
| L4 | pool list | `Pool c ∧ swept` ⇒ `free_head` lists *exactly* the free slots of the page, acyclic, and `nfree` is their number. |
| L5 | swept pool | `Pool c ∧ swept` ⇒ no black or grey header anywhere in the page. |
| L6 | run shape | `LargeHead n` ⇒ pages *p+1 … p+n−1* are `LargeCont` with `swept` equal to the head's. The walk from `pa p` ends at `pa (p+n)`. |
| L7 | swept run | `LargeHead ∧ swept` ⇒ no black or grey header in the run. No two adjacent blue blocks. No page of the run is wholly one blue block, because such pages go back as `Free`. |
| L8 | avail | `avail[c]` lists exactly the swept `Pool c` pages with `nfree > 0`, acyclic. |
| L9 | large lists | #46's `fls_valid`, `fls_terminates` and `fls_exact`, with every listed node in a swept run. Every blue block of at least `lg_min` words in a swept run is listed. |
| L10 | fillers | No field of any non-free object points to a filler or to a free block (`no_pointer_to_blue`, extended to fillers). |

**Swept state in the sequential collector.**
- Between collections, every page is swept.
- At the start of a major sweep, after the mark, the sweep clears `avail`
  and the large heads and marks every `Pool` and `Large` page unswept, as
  #46's `clear_heads` does.
- It then sweeps every page in turn. `swept` is a real field from the
  start, even though the sequential collector never shows a half-swept heap
  to the mutator.

### 1.5 The allocator interface

Today the minor collection calls `SAL.alloc_lists_spec major fp wosize` by
name (`GC.Gen.Promote.fsti:89`). It takes `fls_valid` and `fls_terminates`
in about 25 lemma files. B2 puts an interface in between,
`GC.Spec.AllocIface.fsti`.

```fstar
val ast_t : Type
val alloc_inv : heap -> ast_t -> prop      (* B2: pages_ok; #46: the fls_* conjunction *)
val alloc_spec : heap -> ast_t -> wz:pos -> heap & ast_t & U64.t
(* lemma kit: fresh white object of wosize wz at obj, every other object
   unchanged, only blue or filler words consumed, alloc_inv preserved,
   obj not reachable, OOM => heap unchanged *)
```

The minor collection's files are then proved once against the kit. #46
becomes one instance, which checks that the kit is complete, and B2 the
other.

---

## 2. Top-level theorems

### 2.1 `sweep_page_correct`, the building block

```fstar
val sweep_page_spec : heap -> page_info -> p:nat -> heap & page_info

val sweep_page_correct (g:heap) (pm:seq page_info) (p:nat{p < n_pages}) : Lemma
  (requires pm[p].kind = Pool c /\ not pm[p].swept /\ page_shape g pm p   (* L1, L3 *)
            /\ no_grey_in_page g p)
  (ensures  let (g', i') = sweep_page_spec g pm[p] p in
     (* frame *)      (forall a. not (in_page p a) ==> g' a == g a)
     (* survivors *)  /\ (forall k. black at slot k in g ==> slot k in g' = the same object, white, same fields)
     (* reclaimed *)  /\ (forall k. white or blue at slot k in g ==> slot k free in g')
     (* listed *)     /\ i'.swept /\ L4 and L5 hold for p in g'
     (* empty page *) /\ (nfree = ns ==> i'.kind = Free /\ L2 holds for p in g'))
```

Pushing the page onto `avail[c]` touches only `pm[p].next` and one head.
That push is a separate, two-line lemma, so `sweep_page_correct` mentions
no other page at all.
- **Slot starts only.** The sweep reads and writes slot starts. The tiling
  that L3 guarantees makes this equal to a walk of the page.
  - This needs the slot invariant "used slot = object at the start, then at
    most one filler", which `Obj.truncate` would break (§4.2).

**`sweep_run_correct`** is the same statement for a run `[pa p, pa (p+n))`:
- the frame is the run's words, its `pm` entries and the large heads;
- survivors are unchanged;
- maximal non-black stretches become one blue block;
- whole free pages split off as `Free`;
- free blocks of at least `lg_min` words are pushed onto #46's lists with
  `FreeLists.Push`.

**`sweep_all`** sweeps every page and run once.
- `sweep_order_independent`: sweeping disjoint pages in any order gives the
  same heap and page map, up to the order of the lists.
- It follows from the frames. Incremental and parallel sweeps both rest on
  it.

### 2.2 `alloc_correct`

```fstar
val alloc_correct (g:heap) (a:ast) (wz:pos) : Lemma
  (requires alloc_ok g a)      (* L1, L2, L8, L9, and L3–L7 for swept pages only *)
  (ensures  match alloc_spec g a wz with
    | (g', a', 0)   -> g' == g /\ a' == a /\ no_fit g a wz
    | (g', a', obj) -> fresh_object g g' obj wz      (* white header, wosize wz *)
                       /\ others_unchanged g g' obj
                       /\ alloc_ok g' a'
                       /\ (forall p. not pm[p].swept ==> page p of g' == page p of g /\ a'.pm[p] == a.pm[p]))
```

- **The caller writes the fields.** As built (§10), the allocator writes
  only the header; `alloc_ok g' a'` is asked of every heap the caller can
  make by writing valid values in the new object's fields.
- **Small path** (`wz + 1 ≤ small_max`):
  - with `c = class_of (wz+1)`, pop a slot from the first page on
    `avail[c]`;
  - write the header, and a filler if `wz + 1 < cls c`;
  - if `nfree` reaches 0, drop the page from `avail[c]`;
  - if `avail[c]` is empty, take a `Free` page, make it `Pool c` and swept,
    thread its slots, then pop.
- **Large path:**
  - #46's `alloc_lists_spec`, restricted to list 0, carving from the right;
  - a remainder below `lg_min` is left unlisted;
  - if nothing fits, take *k* consecutive `Free` pages, join them to a
    swept run next to them or start a new run, push one blue block, and
    retry.
- **The precondition mentions only swept pages, free pages and the lists.**
  Unswept pages appear only in the frame conjunct. This is what the
  incremental collector needs (§7).
- **`no_fit`** is the out-of-memory clause:
  - no swept page of the class has a free slot;
  - no `Free` page exists;
  - for a large request, no listed block fits and no *k* consecutive free
    pages exist.

  It replaces `alloc_succeeds_when_a_block_fits`.

### 2.3 `gc_correct`, restated for pages

The headings are today's (`WT/mark-and-sweep/impl/GC.Impl.Correct.fst`,
595 lines). Only the clauses that named the coalescing sweep or the 17
lists change.

**Safety, `gc_safe_pages`:**
- **The mark is exact:** `full_gc_correctness`, restated against
  `sweep_all (mark h)` instead of `coalesce (sweep (mark h))`. Its mark half
  is unchanged.
- **Survivors are unchanged:** `major_gc_live_subgraph_isomorphism`
  (unchanged).
- **Free slots and free large blocks are not live:**
  - no reachable object is blue or a filler;
  - no field of a survivor points to one (L10).
- **The layout is intact:** `well_formed_heap` and `pages_ok`, with every
  page swept.

**Liveness, `gc_live_pages`:**
- **(a) Every unreachable object is freed.** `unreachable_reclaimed` keeps
  its statement: every word of an unreachable object is `blue_covered` in
  `s2`. A dead object's whole slot becomes a free slot, filler included.
- **(b) Free memory is listed:**
  - every free slot is on its page's list (L4);
  - every page with a free slot is on `avail[c]` (L8);
  - every free page is `Free` (L2);
  - every free large block of at least `lg_min` words is on the large lists
    (L9).
- **(c1) No memory is held without cause.** This replaces
  `coalescing_lossless`:
  - a pool page with no live slot is `Free`;
  - inside a run, no two blue blocks are adjacent, and no page is wholly
    free (L7).
- **(c2) No memory is lost.** This restates `heap_partitioned`:

  `heap words = live + free slots + free large blocks + free pages + waste`,

  where `waste` is the sum of three bounded terms:
  - rounding fillers, fewer than `cls c − w` words per live object;
  - page tails, `page_wsize mod cls c` per pool page;
  - unlisted large pieces, each smaller than `lg_min` and next to a live
    block.

`collect_correct` and `collect_stack_correct` apply it to the Pulse
functions, as today. Vacuity checks follow the pattern at `:562` and
`:573`.

---

## 3. What carries over, what changes, what is new

Line counts are from `WT/` and include `.fsti` files.

**Unchanged (about 30k lines):**
- **The heap model and walk:** `common/` (8.4k): `GC.Spec.Fields`
  (`objects`, `well_formed_heap`), `GC.Spec.Object`, `Heap`, `HeapGraph`,
  `Graph`, `DFS`, `GC.Impl.Heap`, `GC.Impl.Object`.
- **The mark,** spec and impl (11.4k): `GC.Spec.Mark`, `MarkBounded*`,
  `MarkInv`, `GC.Impl.MarkBounded*`, and the skip-rescan proof.
- **Sweep colour lemmas:** `GC.Spec.Sweep` (1.6k), `SweepInv`, `WalkEnd`,
  `Partition.Lists`, `GC.Impl.Sweep.Lemmas`.
- **Minor-collection files with no allocator or free-list reference**
  (8.3k): `CheneyBFS`, `CombinedGraph`, `Reachability`,
  `ReachabilityBridge`, `MajorReachabilityTransfer`, `Remembered`,
  `HeapExtensional`, `MinorCollectForwarding.{NonPointerFields,
  Reflection}`, `PromoteUpdate.NoScanField`, `NoBlueUtil`,
  `TwoPassEquiv.Classification`, `GC.Gen.Impl.MinorHeap`.

**Changed:**
- **Minor collection, against the interface (§1.5).**
  - Files: `Cheney` (2.1k), `CheneyPreservation.*` (8.3k), `Promote`,
    `PromoteUpdate.*`, `MinorCollectForwarding` (main, Edges, NormalEdges),
    `CheneyFlComplete`, `TwoPassEquiv`, `Cheney.Sim*`, and
    `GC.Gen.Impl.{Cheney, Promote, UpdatePtrs}`.
  - Most of these only pass `alloc_lists_spec` or `fp` along, so the edit is
    mechanical.
  - The real work is in the preservation lemmas that take `fls_valid` or
    `fls_terminates`. Those become `alloc_inv`.
- **The driver and heap shape:**
  - `GC.Gen.Impl` (1.9k) threads `ast` instead of `heads` and `tbl`;
  - `HeapInvariant` (`major_heap_shape`), `PostCollectionShape`,
    `FreeListShape` and `MajorPrecondition` are restated over `pages_ok`.
- **Top-level correctness:**
  - `GC.Spec.Correctness` (2.2k): `full_gc_correctness` against `sweep_all`;
  - `GC.Impl.Correct` (595): the clauses of §2.3;
  - `GC.Impl` (`collect`).
- **Reused by restriction to one run:**
  - #46's large-object allocator: `Allocator.Lists`, `Allocator.Lemmas.*`,
    `GC.Gen.AllocLists`, `AllocExact`, `AllocProps`, `FreeLists`,
    `FreeLists.Push`;
  - the fused sweep: `Coalesce` (2.7k), `Coalesce.Correct` (3.8k),
    `Coalesce.Complete`, `SweepCoalesce*`, `HeapAgree*`, `Partition`,
    `CollectLists`, and `GC.Impl.FusedSweepCoalesce`.
  - These are stated from `zero_addr` to `heap_size`. They need generalising
    to `[lo, hi)` with `objects lo g` ending at `hi`.
    `HEAP_EXPANSION.md:160–164, 260–264` describes the same change for heap
    chunks.
  - `sheera/parallel-sweep` already proves a fused sweep of a segment with a
    frame (`GC.Spec.SweepPar`, `segment_correct`,
    `sweep_segment_local`). It is for the single list that predates #46, so
    it is a guide rather than a drop-in.

**New:**
- `GC.Spec.Pages.Params` with its two instances;
- `GC.Spec.Pages.Map` (page map, `pages_ok`, frame lemmas);
- `GC.Spec.Pages.Pool` (slot arithmetic, pool alloc);
- `GC.Spec.Pages.SweepPage`, `GC.Spec.Pages.SweepRun`,
  `GC.Spec.Pages.SweepAll` (order independence);
- `GC.Spec.Pages.Large` (run shape, growth, splitting off free pages);
- `GC.Spec.AllocIface`;
- `GC.Spec.Pages.Correct`;
- Pulse `GC.Impl.Pages.{Map, Alloc, SweepPage, SweepRun, Sweep}`.

**Removed from the build:** #48's object-start table (6 files, 2.1k lines)
and its threading (§5).

---

## 4. The OCaml 4.14 runtime

### 4.1 Unmarshalling (intern.c)

- **Current behaviour.** The patched 4.14 intern.c is stock.
  - For a total `wosize ≤ 256` it re-tiles a *minor* block. The minor
    collection promotes each object separately, so the major heap never
    sees that block.
  - For `256 < wosize ≤ Max_wosize` it takes one major block
    (`caml_alloc_shr_no_track_noexc`, `intern.c:638`). It then writes
    headers inside it, with no gaps (`:375`, `:405`, `:477`).
  - Larger requests already fail (`intern_add_to_heap`).
- **Effect on B2: this is safe.**
  - A major intern block has whsize ≥ 258 > 128, so it is always in a
    large run.
  - A run requires only the walk (L6), and re-tiling one white block into
    several white objects that cover it keeps that walk.
  - The run sweep frees each sub-object separately, as A does today. Pool
    pages never see a re-tiled block.
  - The trusted bridge obligation is one sentence: *a fresh large block may
    be re-tiled into white objects that cover it exactly, before the next
    collector call*. The mutation-test harness can check it.
- **Allocating each object separately, as OCaml 5 does**
  (`~/ocaml/runtime/intern.c:406`, `intern_alloc_obj`). Not now.
  - It does not affect correctness here.
  - It needs an allocation that cannot collect: OCaml 5's
    `caml_shared_try_alloc` never collects. Our `verified_allocate` collects
    and retries (`alloc_gen.c:963–989`), and a collection mid-intern would
    find objects reachable only from `intern_obj_table`.
  - The way to do it would be:
    - a verified `alloc_nogc`, which is `alloc_spec` with no retry;
    - a check before intern that collects if the total `whsize`, plus a
      margin of pages, is not free.
  - **Why it might matter later:** when an unmarshalled structure partly
    dies, its small pieces stay in the large area as unlisted pieces until
    a neighbour dies. None of our benchmarks unmarshals much. Add one that
    does to §6 stage 9, and decide on the number.

### 4.2 Obj.truncate

- **Current behaviour.** It writes a leftover header inside the object.
  The header is black in the major heap (stock `obj.c:184–219`).
- **In a pool slot this breaks L5.** The page sweep reads slot starts only,
  so the black leftover is never whitened. The next mark then starts with a
  black header in the heap, but the mark's precondition is no black
  headers (`major_heap_shape`).
  - So truncate is not just a weaker invariant; it would make the bridge
    unsound.
- **Recommendation: make it fail early.** `b14ae30b` on `akhil/incremental-*`
  already makes `Obj.truncate` raise `Invalid_argument`.
  - It is deprecated in 4.14 and removed in 5.0.
  - Add it next to `1d3e401a`, which makes weak arrays, ephemerons and
    `Gc.finalise` fail early.
  - The other option, a page sweep that walks every slot, would cost a walk
    per slot and the slot-start proof shortcut.

### 4.3 Two smaller points

- **`caml_alloc_shr(0)`.** Today the bridge turns wosize 0 into wosize 1,
  and the runtime then writes a wosize-0 header, which leaves the second word
  stale. The walk would read that stale word as a header (in B2, the old
  free-slot link).
  - This is a known hazard (`WT/docs/allocator-table-and-size-lists.md`).
  - **With the decision above it is fixed in verified code.** The allocator
    accepts wosize 0. It puts the block in a 2-word slot and writes a 1-word
    filler after it. The bridge stops rewriting wosize 0, and the runtime's
    own header write keeps wosize 0.
- **The trigger.** The prototype scales the major-collection trigger by its
  ratio of slot words to requested words (`VERGC_CONSUMED`, results §1.1).
  For B2 that ratio is close to 1. The verified build should count slot
  words directly.

---

## 5. What the object-start table (#48) is still needed for

**Its only runtime use was to give cut points for a parallel sweep.**
Everything else that touches it is checking:
- the `VGC_CHECK_ALLOC` checker;
- the prototype's exact comparison.

**In B2, pages give every cut.**
- A page start is a walk position (L1), except inside a run.
- Merging stops at run edges, so whole runs are independent too.
- A parallel sweep is a split over pages and runs, with no join beyond
  concatenating lists.

**The one gap is balance inside one very large run.** One huge array is one
unit of work. A table restricted to large runs would fix that. Defer it
until a measurement shows the need.

**Recommendation:** base B2 on `sheera/size-lists` (#46, `3be9eb36`) plus
`1d3e401a`, not on `sheera/object-table`. This drops:
- 2.1k lines of table proofs;
- the `tbl` threading (17 signatures);
- decision (b), the intern.c flaw.

---

## 6. Staged plan

**How the estimates were made.** #46 changed +8.4k/−3.1k proof lines in 140
files. Its commits are squashed, so they do not show how long it took.
- The estimates below are in proof lines, new plus changed. They exclude
  pure renames.
- They follow the stage order. Each stage ends with no admits on its
  modules.

| # | Stage | Content | *Estimate* |
|---|---|---|---|
| 0 | Prototype check | Fix `VERGC_PROTO_CHECK_CONTROL` parsing (done). Give the large-area sweep a mutant that fires, and confirm the check rejects it in all three modes. B2 at 16 KB is measured in stage 9. | under 1 day, no proofs |
| 1 | Specification | `Params`; layout arithmetic; the walk relation and its bridge to `objects`; `Pages.Map`; page shapes and the tiling theorem; `pages_ok` with its lists; the allocator interface. The §2 theorems are stated as predicates on a candidate function, not as admitted lemmas, since there are to be no admits. Vacuity checks that `pages_ok` holds on an empty heap and on a heap with a pool page. | 2–3k |
| 2 | Allocator | Pool allocation, page acquire, large allocation (#46 restricted, unlisted small pieces, run growth and join). `alloc_correct` and `no_fit`. #46's exact-pop lemmas reused. | 3–5k |
| 3 | `sweep_page` | `sweep_page_correct`, the push lemma, page release. Then `sweep_run_correct` by restricting the fused sweep to `[lo, hi)`, which is the risky part. Then `sweep_all` and order independence. | 5–8k, of which 3–5k for runs |
| 4 | `gc_correct` | Restate `full_gc_correctness` against `sweep_all`; the clauses of §2.3. Move the minor collection behind the interface and re-prove its preservation lemmas against `pages_ok`. Restate `major_heap_shape` and `PostCollectionShape`. | 6–10k |
| 5 | Pulse | `GC.Impl.Pages.*`: page-map array, allocation, the `sweep_page` loop, `sweep_run`. Thread `ast` through `gen_gc` and about 20 functions, as #46 did. | 3–5k |
| 6 | Extraction | Entry modules in `generational/Makefile`. Check that the classes extract as a static table, `page_wsize` as a constant, and the `pm` record as a struct. Snapshot. | under 0.5k, plus C glue |
| 7 | Bridge | `ensure_heap` rounds the heap and builds `pm`. Slot-word trigger. The `caml_alloc_shr(0)` fix and truncate fail-early in the patch. A page checker under `VGC_CHECK_ALLOC`, ported from the prototype's `impl_check`. | about 1k C |
| 8 | Tests | See below. | about 1k C and scripts |
| 9 | Measurements | See below. | 2–4 days |

**Total, estimated:** 20–33k proof lines, about 2–3 times #46.

**Stage 0: what the prototype check showed.**
- B2 has been measured only at 32 KB. The 16 KB result in results §9.3 is
  B3's (`B3-16K`), whose classes differ. Measuring B2 at 16 KB moves to
  stage 9.
- `proto_common.c` read `VERGC_PROTO_CHECK_CONTROL` as a boolean, so setting
  it to 2 gave 1, and the large-area mutant had never run. This is fixed on
  `sheera/alloc-pages-proto`.
- **With the fix, the large-area mutant is still not rejected** on
  binarytrees 16, in any of the three sweep modes (2026-11-08). The reason
  is the mutant, not the check: it keeps the *first block* of a run when it
  is not blue. B2 carves large blocks from the right, so a run's first block
  is the run's left-over piece, which is blue. On binarytrees every large
  block is 129 words, and each 4096-word run keeps a piece of at least 97
  words at its start, so the mutant's condition never holds.
  - **The mutant now keeps the run's first non-blue block even when it is
    dead.** It fired and was rejected on binarytrees 16, bdd and fft, in all
    three sweep modes. The kept blocks were 129, 16,385 and 524,289 words. On
    livemap, minilight and markbench no large block died, so it never fired.

**Stage 8, tests:**
- **Snapshot tests:** `pages_test.c` beside `size_lists_test.c`, covering
  every class at both page sizes, run growth and joining, and a page
  returned from a run.
- **The oracle check,** as in the prototype: at every collection, the
  verified page sweep and #46's verified fused sweep on a copy must keep the
  same survivors with the same contents.
- **Mutants,** each of which must be rejected by both the proof
  (`tools/try-module.sh`) and the tests:
  - skip the last slot;
  - keep a run's first dead block;
  - let a merge cross a run edge;
  - leave `swept` unset.
- **`make test`, `make test-native`,** and the OCaml testsuite against
  `ci/expected-failures.txt`, with no new failures. It was not run for B2.
- **Program output** byte-identical to stock OCaml and to A.

**Stage 9, measurements:**
- **Builds:** A (#46, the verified build without the table), B2-16K and
  B2-32K (verified), and prototype B2 at both sizes, to see the cost of the
  proofs' choices (no pool header, slot-word trigger).
- **Programs:** the set of results §9: hamming, binarytrees 16 and 18,
  livemap, livegraph, markbench, minilight, bdd, fft, plus an
  unmarshalling program for §4.1.
- **Metrics:** run time (median of at least 5), smallest heap, where the
  memory goes (as in §9.4), and mark and sweep time.
- **The decision rule** of `docs/allocator-comparison.md` §6.3. The page
  size is chosen by the rule in that note: 16 KB unless 32 KB is clearly
  faster.

---

## 7. What the incremental collector will need from this design

**What this stage already provides:**
- a `swept` bit per page and per run, and allocation only from swept pages
  and runs;
- `sweep_page_correct` and `sweep_run_correct`, each with a frame;
- order independence;
- `alloc_correct`, whose precondition does not mention unswept pages.

**What the incremental step adds:**
1. **A mid-sweep invariant, per page.** It is `pages_ok` with L4, L5 and L7
   required only of swept pages. For unswept pages it requires the shape
   (L3, L6) and the meaning of the colours after the mark: black means a
   survivor, and white means garbage that is not yet freed.
   - This is akhil's `sweep_inv_incremental` (`behind_swept`,
     `front_unswept`, `pending_free`), with "behind the cursor" replaced by
     "swept".
   - `sweep_page_correct` is its step lemma, and the frame gives the rest.
2. **The colour of a new object.**
   - While sweeping, a new object is in a swept page and is white. There is
     no cursor test, unlike `allocation_color (Sweeping c)` on
     `akhil/incremental-sweep`.
   - While marking, a new object is black, as on `akhil/incremental-mark`.
     That is a parameter of `fresh_object`, which is white only today.
3. **Sweeping on allocation.** When `avail[c]` is empty, sweep one unswept
   `Pool c` page before taking a free page, as OCaml 5's `pool_find` does.
   - This needs a list of unswept pages per class, or a scan.
   - Each allocation then does at most one page's sweep. The prototype's
     incremental pauses met the decision rule for B2 (results §9.9).
4. **The minor collection mid-sweep.** Promotion goes through
   `alloc_correct`, so it lands in swept pages. akhil's
   `minor_keeps_sweep_phase` becomes a frame argument over unswept pages.
5. **Starting a cycle cheaply.** Marking every page unswept is O(pages).
   An epoch number makes it O(1): a page is swept when its epoch equals the
   current one. The specification can keep the boolean, with the epoch as
   the implementation.
6. **The mark.** akhil's `marking_inv` and the deletion barrier
   (`GC.Gen.Barrier`) do not depend on the allocator. What they need from
   the sweep is `sweep_end_shape`: every page swept, no black or grey
   header, and free means blue or filler. `gc_safe_pages` already gives
   that.

**A conflict to plan for.**
- `akhil/incremental-sweep` deletes `Coalesce*`, `SweepCoalesce*` and
  `HeapAgree`, and moves to one ascending list.
- B2 reuses those modules for large runs. Merging the two lines means
  either keeping them for runs or porting the run sweep to akhil's
  ascending, single-list form.
- Decide this before stage 3, since `sweep_run` is the riskiest proof.

---

## 8. Main risks

1. **Restricting the coalescing sweep to a run** (`fused_aux`,
   `Coalesce.Correct`, 3.8k lines, all stated from `zero_addr`). If it
   proves too costly, there is a fallback: prove a fresh, simpler run
   sweep, modelled on `GC.Spec.SweepPar.segment_correct`. Its frame
   structure is already the one needed.
2. **The minor collection's move to the allocator interface.** It touches
   about 25 files and 15k lines. Most edits are mechanical, but the
   `CheneyPreservation.*` lemmas may depend on #46's list shape in ways the
   kit does not capture.
3. **B2 at 16 KB is not measured.** OCaml 5's classes waste up to 12.7% at
   16 KB, against 10.0% at 32 KB. The 16 KB gain on minilight was measured
   with B3's classes.
4. **Trusted runtime changes** (§4): truncate failing early, the
   `caml_alloc_shr(0)` fix, and the intern re-tiling obligation. Each is
   small, but none is proved.
5. **The large-area sweep was tested against only one deliberate error**
   (§6, stage 0): keeping a run's first live-looking block. That mutant is
   rejected in every mode.
6. **Diverging from akhil's incremental line** (§7).

---

## 9. Stage 1 as built

All modules are in `mark-and-sweep/spec/`. They verify from a clean cache at
the default rlimit of 20, with no admits and no assumptions. `Pages.Init`,
`Pages.PoolInit` and `Pages.Theorems` are roots in the `Makefile`, so
`make verify` checks them all.

| Module | Lines (1,687 in all) | What it holds |
|---|---|---|
| `Pages.Params` (`.fsti`, `.fst`) | 45 + 49 | The page size and the class table, abstract to every other module. Conditions C1–C4, proved for both 2048 and 4096 words. |
| `Pages.Layout` | 180 | `class_of`, with `class_of_fits` and `class_of_least`; page and slot arithmetic; slots and tail fill a page. |
| `Pages.Walk` | 181 | `steps_to g a b`, the walk over a stretch; composition, frame; the bridge to `objects` (`steps_to_objects`, `objects_steps_to`) and to `walk_end`. |
| `Pages.Map` | 122 | Page kinds, `page_info`, `map_ok`; walk pages and their spans. Vacuity: `all_free_ok`. |
| `Pages.Shape` | 250 | Page shapes (L1–L3, L6) and **`heap_tiled`**: if every page has its shape, the global walk reaches the end of the heap and every walk page is an object. |
| `Pages.Inv` | 189 | **`pages_ok`**, with clauses L4, L5, L7, L8, L9 and L10. |
| `Pages.Init` | 290 | Vacuity: **`init_pages_ok`**, the empty heap of pages satisfies `pages_ok` for every heap size. |
| `Pages.PoolInit` | 247 | Non-vacuity of L3 and L4: **`pool_init_ok`**, a fresh pool page has its shape and an exact free-slot list, and nothing outside the page changes. This is also the allocator's page-acquire step for stage 2. |
| `Pages.Theorems` | 134 | `sweep_page_meets` and `alloc_meets`: the §2.1 and §2.2 statements as predicates on a candidate function. |

**Changes to the plan made in stage 1:**
- The §2 theorems are predicates on a candidate function, proved in stages 2
  and 3, instead of admitted lemmas.
- One parameters file checks both page sizes (§1.1).
- No configuration axiom about the heap size: the heap's tail is a blue
  block or too short for a header (§1.1).
- The free-slot list (L4) and the page lists (L8) are stated with a ghost
  list witness (`slot_chain`, `page_chain`): no repeats and exactly the
  right members. That makes them finite and acyclic without a fuel bound.
- `in_swept_run` and the run clauses use the walk over a run (`steps_to`),
  not #46's whole-heap walk, so the run sweep of stage 3 can be stated per
  run.
- **Moved to stage 4:** the allocator interface of §1.5. It is only useful
  once it is instantiated with #46's allocator, and that instantiation is
  the minor-collection work of stage 4.
- **Moved to stage 4:** `gc_correct` restated for pages. Its clauses reuse
  the existing `full_gc_correctness` and isomorphism, which stage 4 restates
  against `sweep_all`.

---

## 10. Stage 2 as built

All modules are in `mark-and-sweep/spec/`. They verify from a clean cache at
the default rlimit of 20, with no admits and no assumptions. `Pages.Alloc`
is a root in the `Makefile`, so `make verify` checks them all.

**The theorem.** `GC.Spec.Pages.Alloc.alloc_correct : unit -> Lemma
(alloc_meets alloc)`: the allocator `alloc` meets the §2.2 statement of
`Pages.Theorems` for every heap, state and wosize, 0 included. As OCaml's
`caml_alloc_shr` does, `alloc` writes the new object's header and leaves its
fields as they were; `alloc_ok` asks that every heap the caller can make by
writing valid values in the fields satisfy `pages_ok` and
`well_formed_heap` (see the changes below).

**Vacuity.**
- `init_alloc_pre`: the empty heap of pages satisfies the precondition,
  `pages_ok` and `well_formed_heap`.
- `init_alloc_succeeds` and `init_alloc_large_succeeds`: on that heap a
  small block, and a large block that fits in the pages, are allocated
  (the result is not 0), so the theorem is not met by always failing.
- `alloc_fill_exists`: after any allocation the caller can write the
  fields (clearing them will do), and the heap it gets satisfies `pages_ok`
  and `well_formed_heap`; so the caller's clause of `alloc_ok` is not
  vacuous. `init_alloc_filled` combines it with `init_alloc_succeeds`.

| Module | Lines (5,326 in all) | What it holds |
|---|---|---|
| `Pages.Replace` | 431 | `replaces g g' a e`: a stretch of free blocks the walk covers is laid over with new blocks the walk covers, none infix, none with a pointer field unless free. `replace_ok` derives `well_formed_heap`, `no_pointer_to_blue` and "every object that was not free keeps its place, header and fields" once, for every allocator step. Rests on `steps_to_det`, the walk is deterministic. |
| `Pages.Cells` | 345 | #46's fuel-based lists as ghost lists of cells: `cells_of` and `cells_valid` go both ways between `fl_valid`/`fl_chain_terminates`/`chain_avoids`/`reachable_on_fl` and list membership. `lview`: L9 as "list 0 is exactly the free listable blocks, the exact-fit lists are empty" (`large_ok_lview`, `lview_large_ok`). |
| `Pages.Frame` | 267 | `page_local` (L1–L7 of one page): kept when the page's entry and the words of its span are (`page_local_frame`). `avail_frame` for L8. |
| `Pages.Blocks` | 214 | The writes: a fresh object's header (`put_hdr`), the same with its fields cleared (`put_obj`), a blue header; `clears`, the allocator's heap against the cleared one; `two_blocks` walks one or two new blocks. |
| `Pages.Step` | 208 | `pages_ok` intro/elim; `cleared_ok`, the statement the per-path proofs meet, and `cleared_ok_compose` (two steps); `others_local` (a rewrite of whole spans keeps every other page); `lview_away` (a rewrite outside every swept run keeps L9). |
| `Pages.Pool` | 911 | `pop` (a slot from the first page on `avail[c]`), `acquire` (a free page becomes a pool page, by `pool_init_ok`), `small_alloc_ok`. |
| `Pages.Run` | 169 | `run_after_replace`: a swept run keeps L6 and L7 when one of its free blocks is rewritten into white or blue blocks, no two blue ones adjacent. |
| `Pages.Large` | 1,106 | First fit on list 0 (`split_fit`), carving from the right; `carve_ok`. A remainder of at least `lg_min` words stays listed in place; a smaller one, or none, leaves the list by unlinking (`cells_unlink`). |
| `Pages.NewRun` | 712 | `new_run_ok`: `pages_for w` consecutive free pages become a swept run, the object first, the rest one free block, pushed on list 0 if listable. |
| `Pages.Fill` | 482 | `fill_ok`: writing the fields of an object that is neither free nor a closure with values `field_ok` allows keeps `pages_ok` and `well_formed_heap`. Every position the walk reaches lies outside the fields (`apart`), so the walk, the pages and the lists are kept. `cleared_written`: clearing the fields is such a write. |
| `Pages.Alloc` | 481 | `alloc`, `alloc_correct` (`alloc_ok_of` takes the per-path proofs from the cleared heap to the allocator's, with `fill_ok`; `fields_swept`: the new fields lie in swept pages), the vacuity lemmas. |

**Changes to the plan made in stage 2:**
- **Three corrections to stage 1's statements.** None weakens a proved
  theorem; stage 1 proved only `init_pages_ok` and `pool_init_ok`, and
  both still hold.
  - `no_fit` (`Pages.Theorems`) demanded "no free page" for large requests
    as well, so `alloc_meets` held of no allocator: a request larger than
    the heap must fail while a free page exists. It now says what §2.2
    says: for a large block, no listed block fits and no `pages_for w`
    consecutive pages are free (`free_run`).
  - `unswept_unchanged` used `page_frame g g' i`, "only page `i` changed",
    for every unswept page, which no step that writes another page can
    meet. It now uses `page_kept g g' i`, "page `i`'s words are unchanged",
    the meaning intended.
  - `large_ok` (L9) did not say a listed block is free, so an allocator
    could carve a live object. It now includes `fls_sound`, as §1.4's
    "`fls_exact`" asked; `init_pages_ok` is re-proved.
- **A fifth parameter condition, C5:** `small_max > n_small` (#46's 16
  exact-fit lists). Every listable block is then on list 0, the only list
  the large allocator searches. Both page sizes meet it (128 > 16).
- **The caller writes the new object's fields (decided 2026-11-08).**
  As OCaml's `caml_alloc_shr` (4.14) and the pool allocator of OCaml 5,
  and as #46's `alloc_spec`, the allocator returns the object with its
  fields as they were; the caller must write every field before the next
  collection. Stage 2 first cleared the fields, because `alloc_ok` asked
  for `pages_ok` and `well_formed_heap` right after the allocation, and a
  free slot's first field links to another free block. Now:
  - `alloc_ok` (`Pages.Theorems`) no longer asks for `pages_ok` and
    `well_formed_heap` of the allocator's heap `g'`. It asks them of every
    `g''` with `fields_written g' g'' x`: `g''` is `g'` but for the fields
    of the new object `x`, and each field holds a value `field_ok` allows,
    a non-pointer or a pointer that resolves to an object that is not free
    (`x` itself included). The rest of `alloc_ok` is unchanged, and stated
    of `g'`.
  - `Pages.Fill.fill_ok` is the lemma behind it, for any object that is
    neither free nor a closure.
  - The per-path proofs are unchanged; they are about the heap the
    allocator would make if it cleared the fields, and meet `cleared_ok`
    (`Pages.Step`), the old `alloc_ok`. The write helpers take a flag
    `clr` (`put_obj_as`, `fill_slot_as`, `pop_as`, `carve_as`,
    `new_run_as`, `alloc_as`); `alloc` is `alloc_as false`. The object's
    header is now written after the filler or the run's free block, so the
    cleared heap is the allocator's with `zeros` applied last (`clears`).
  - For the Pulse allocator of stage 5 there is no field write; the
    caller's obligation is `fields_written`.
- **No run joining.** When nothing fits, the allocator starts a new run of
  `pages_for w` free pages; it never extends a neighbouring run (§2.2).
  `no_fit` is stated to match. Joining can come later as an optimisation.
- **Carving keeps #46's policy, with a different threshold.** The remainder
  stays listed when it has at least `lg_min` words, not 2; a smaller one is
  unlinked and left as an unlisted piece. Unlinking is proved here
  (`cells_unlink`), since #46's `alloc_spec` lemmas do not say that the
  other cells stay on the list.
- **`pages_ok` is sealed** (`opaque_to_smt`), as #46's `fls_*` bundles are;
  clients use `Pages.Step.pages_ok_intro` and `pages_ok_elim`. Without it,
  queries that only carry `pages_ok` timed out.
