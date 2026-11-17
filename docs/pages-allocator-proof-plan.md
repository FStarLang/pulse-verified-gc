# Proof plan: the OCaml 5-style page allocator (B2)

This is the plan for proving B2. Stage 1, the specification, stage 2, the
allocator, and stage 3, the sweep, are done on branch
`sheera/pages-allocator`, which is based on `origin/sheera/size-lists`
(§9, §10, §11). The allocator leaves a new object's fields to its caller,
as `caml_alloc_shr` does (§10). The run sweep is a fresh proof, not #46's
coalescing sweep restricted to a run (§11). In stage 4, item 0 makes the
allocator a component with a phase-aware interface, and the new object's
colour a parameter (§12). Item 2 proves the swept heap well formed and
adds the step before the sweep (§13). Item 3 restates `gc_correct` for
pages, proves it, and proves the allocation/collection cycle (§14).
Afterwards, (c2) gains the word-count equation, and the seed-sensitive
query of `Pages.Large` is split (item 4) (§15). Stage 5a writes the
allocator and the sweep in Pulse, each function proved to compute exactly
its specification, and extracts them to C with a test (§16). The
efficiency pass after it is §17.

**Project rule (2026-11-10): the verified code is as efficient as the
unverified code.** The extracted C must be as efficient as the prototype
(`proto/alloc_pages.c` on `sheera/alloc-pages-proto`) and as OCaml 5's
`shared_heap.c`. Making code less efficient for the sake of verification
is not acceptable.
- Use their algorithms: table lookups for size classes, a free-page search
  that does not start from page 0, no per-page work at the start of a
  sweep where they have none, one pass per page in the sweep.
- Prove each fast function equal to the specification's function where it
  computes the same result. Where it may make a different valid choice,
  prove it against the theorems (`alloc_meets` with `alloc_ok`,
  `sweep_page_meets`, `sweep_run_ok`). A different valid choice may also
  be made by changing the specification's function and re-proving its
  theorem. Never weaken a theorem to fit the code.
- Measure the extracted C against the prototype on the same operations
  (`mark-and-sweep/pages-c/bench`). The target is at most 5% slower.

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
- **Settled in stage 3 (§11):** the run sweep does not use `Coalesce*`,
  `SweepCoalesce*` or `HeapAgree`, so B2 no longer depends on them, and
  akhil's line may remove them.

---

## 8. Main risks

1. **Restricting the coalescing sweep to a run** (`fused_aux`,
   `Coalesce.Correct`, 3.8k lines, all stated from `zero_addr`). If it
   proves too costly, there is a fallback: prove a fresh, simpler run
   sweep, modelled on `GC.Spec.SweepPar.segment_correct`. Its frame
   structure is already the one needed.
   - **Resolved in stage 3:** the fallback was taken (§11).
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

---

## 11. Stage 3 as built

All modules are in `mark-and-sweep/spec/`. They verify from a clean cache at
the default rlimit of 20, with no local rlimit raised, no admits and no
assumptions. `Pages.SweepAll`, `Pages.SweepOrder` and `Pages.SweepVacuity`
are roots in the `Makefile`, so `make verify` checks them all.

**The theorems.**
- `GC.Spec.Pages.SweepPage.sweep_page_correct : unit -> Lemma
  (sweep_page_meets sweep_page)`, the pool page of §2.1:
  - a black slot keeps its block, made white; the rest of its slot, its
    fields and filler, is unchanged;
  - every other slot becomes a free slot, and the page's list holds exactly
    them (L4); the page tail is unchanged;
  - a page with no black slot becomes a `Free` page;
  - only page `i`'s words and entry change, and the entry is swept.
- `GC.Spec.Pages.SweepRun.sweep_run_correct : unit -> Lemma
  (sweep_run_meets sweep_run)`, the run of §2.1 (`sweep_run_ok` in
  `Pages.Theorems`):
  - only the run's words and its pages' entries change, and the map stays
    `map_ok`;
  - a survivor (a black block of the walk over the run) keeps its place and
    fields, made white; every block of the swept run that is not free was a
    survivor;
  - every stretch of dead blocks is merged into one free block, which stops
    at the run's edges;
  - a free block that holds whole pages gives them back as `Free` pages, and
    the rest of the run becomes one or more smaller swept runs, each with
    its shape (L6) and its swept clause (L7);
  - a run with no survivor becomes `Free` pages only;
  - the free blocks of at least `lg_min` words in the new runs are linked,
    in address order, in front of a list head the caller gives, and the new
    head is returned (`lchain`).
- `GC.Spec.Pages.SweepAll.sweep_all_correct`: `sweep_all` sweeps every unit
  once, from page 0 on.
  - **Precondition:** `sweep_ready` (the shapes, every page that is not
    `Free` unswept, the lists empty, no grey block in a pool page or run) and
    `mark_done` (`well_formed_heap`, `no_pointer_to_blue`,
    `tri_color_invariant`, `noGreyObjects`).
  - **Result:** every page is swept and `pages_ok` holds, L10 included.
    Each unit holds exactly the mark's survivors, made white
    (`SweepUnits.unit_ok`).
  - A swept pool page with a free slot goes on its class's list. This is the
    push lemma, `SweepStep.push_ok`.
- `GC.Spec.Pages.SweepOrder.sweep_commute`, order independence (§2.1):
  - for two different unit heads of a `map_ok` map, sweeping them in either
    order gives the same heap and page map, and each unit returns the same
    list head;
  - each unit is given its own list head, so this is an exact equality;
  - there is no shape precondition: both sweeps' frames hold for any heap.

**Vacuity** (`Pages.SweepVacuity`), for any page `i` of any heap:
- a fresh pool page whose first slot holds a black block is a marked pool
  page; the sweep keeps the page a pool page, with that slot used and white;
- a fresh pool page with no black block is a marked pool page too; the sweep
  gives it back as a `Free` page;
- a one-page run holding a black block is a marked run; the sweep keeps the
  block, made white;
- the same run holding a white block is a marked run too; the sweep gives
  its page back as a `Free` page;
- the empty heap of pages satisfies `sweep_ready` and `mark_done`
  (`sweep_all_ready`).

| Module | Lines (4,512 in all) | What it holds |
|---|---|---|
| `Pages.SweepPage` | 421 | `sweep_page`, slot by slot as OCaml 5's `pool_sweep`; `sweep_page_correct`. The swept heap is read back slot by slot (`sw_hd`, `sw_link`, `sw_rest`, `sw_out`), and the free-slot list is followed from the last free slot down (`dead_chain`). |
| `Pages.Blk` | 290 | A stretch as a list of blocks `{at; w; t}` (`Live`, `Dead`, `Page`). `contig` (end to end), `blk_at`, `slice`; `tiles_steps`: when the headers give the sizes, the walk steps over the list and stops exactly at its starts. |
| `Pages.RunList` | 480 | The run's layout in three steps: `olds` (the walk), `merge` (dead stretches become one block, `nodd`), `split` (whole pages become `Page` blocks; what is left holds no whole page). `fin_spec`, `fin_all_free`. |
| `Pages.RunMap` | 174 | The new page map from the layout's free pages: each stretch of other pages becomes a swept run (`new_map`, `new_map_ok`, `head_facts`, `cont_head`). |
| `Pages.SweepRun` | 846 | `sweep_run`: write the layout's headers and links (`wr_all`), read them back (`val_at`), and prove each clause of `sweep_run_ok`; `new_run_ok` is L6 and L7 for each new run. |
| `Pages.SweepVacuity` | 237 | The vacuity lemmas above. |
| `Pages.SweepUnits` | 253 | `unit_ok`, a unit's survivor facts, from each sweep theorem (`pool_unit_ok`, `run_unit_ok`, `free_unit_ok`), and their frame. |
| `Pages.SweepStep` | 629 | One step of the whole sweep: `push_avail` and `push_ok` (L8); `lview_frame` and `lview_run` (L9: the run's listed blocks go in front of the old list); `pool_step`, `run_step`. |
| `Pages.SweepAll` | 702 | `sweep_all`, its invariant (`inv`, sealed), the steps, and the final theorem. L10 comes from `mark_done`: an object that is not free was black, so its pointers lead to black objects, which survive. |
| `Pages.SweepOrder` | 480 | `sweep_unit`, the unconditional frames and locality of both sweeps, `sweep_commute`. |

**Changes to the plan made in stage 3:**
- **The run sweep is the fallback of §8,** a fresh sweep in the manner of
  `GC.Spec.SweepPar.segment_correct`, not #46's coalescing sweep restricted
  to a run. It is computed on lists of blocks (`Pages.Blk`), so the heap
  reasoning is done once, in `tiles_steps` and `wr_all`'s read-back. Its
  frame is the run's words and pages. It took about 1.8k lines (`Blk`,
  `RunList`, `RunMap`, `SweepRun`), against the 3–5k estimated.
- **The run sweep splits runs,** as the prototype's `sweep_large` does:
  L7 forbids a swept run to hold a whole free page, so a dead stretch that
  holds whole pages gives them back, and the run becomes smaller runs.
  §2.1 asked only for whole free pages to "split off"; `sweep_run_ok` states
  the result page by page (`run_pages_ok`).
- **Statements added to `Pages.Theorems`; none weakened:**
  - `sweep_page_ok` now also says that a survivor's slot keeps its fields
    and filler (`slot_rest_kept`) and that a pool page keeps its tail
    (`pool_tail_kept`). Nothing had proved it before.
  - `sweep_run_ok`, `sweep_run_meets`, `marked_run`, `run_pages_ok`,
    `whitened_at`, `run_survivor` and `lchain` are new.
  - The pool tail clause is named `pool_tail_kept`, because `tail_kept`
    would shadow `Pages.Step.tail_kept` in `Pages.Large`.
- **The lists.** The run sweep links its listed blocks in front of the head
  it is given, rather than calling `FreeLists.Push` per block. `sweep_all`
  turns that into L9 with `cells_prepend`, which reuses stage 2's
  `NewRun.push_len` for the `heap_words` bound.
- **The precondition of the sweep is stated on headers.** "No grey block"
  is asked of every used slot and run block (`sweep_ready`), not only of the
  objects of the walk. A one-word block that ends the heap is not an object,
  so `noGreyObjects` does not cover it. Stage 4 discharges this from the
  mark.
- **Order independence** is an exact equality, with each unit given its
  own list head. "Up to the order of the lists" in §2.1 is this: the order
  of the sweeps only decides which heads the units are given. It uses
  `GC.Gen.HeapExtensional.heap_read_word_ext`, as other `mark-and-sweep/spec`
  modules already use `GC.Gen.*`.
- **Left to stage 4:**
  - `well_formed_heap` after `sweep_all`. `sweep_all_correct` gives
    `pages_ok` and the survivor facts; well-formedness follows the same
    argument as L10 (`SweepAll.target_after`) but is not proved yet.
  - The step before the sweep, which clears the lists and marks the pages
    unswept. `sweep_ready` assumes it has been done.
- **Proof stability.** The stage-2 module `Pages.Large` has one query that
  fails on some Z3 seeds without `--retry`. With the Makefile's `--retry 3`
  it passes; it is not changed here. (Split in §15.)


---

## 12. Stage 4, item 0 as built: the allocator as a component

All modules are in `mark-and-sweep/spec/`. They verify at the default rlimit
of 20, with no local rlimit raised, no `--retry`, no admits and no
assumptions. `GC.Spec.AllocIface` and `GC.Spec.Pages.Allocator` are roots in
the `Makefile`, so `make verify` checks them all.

**The two interfaces.**
- `GC.Spec.AllocIface` is the allocator interface, for any allocator and any
  collector. It does not depend on pages. An allocator is a record
  `allocator` with:
  - its state;
  - its invariant per phase;
  - its allocation per phase;
  - `unswept`, the memory it must not touch.

  The phase is `Idle | Marking | Sweeping`. `new_colour` makes a new object
  black while marking and white otherwise.
  - `alloc_post` says what one allocation does:
    - the new object has the phase's colour and the requested wosize, and
      was not a live object;
    - every live object keeps its header and fields;
    - unswept memory is unchanged;
    - every heap the caller makes by writing the fields satisfies the
      invariant;
    - on failure, nothing changes.
  - `allocator_ok a` says that every allocation meets `alloc_post`.
  - `phase_ok a` says that entering `Marking` keeps the invariant, and that
    recolouring a live object to any colour but blue keeps it while marking.
- `GC.Spec.Pages.Allocator` (`.fsti` and `.fst`) is the page allocator's
  interface. A collector needs nothing else.
  - **Invariant per phase.**
    - `Idle`: `pages_ok`, `well_formed_heap`, and every page swept.
    - `Marking`: `pages_ok_mc` and every page swept.
    - `Sweeping`: `pages_ok_mc`.
  - **Allocation.** `alloc ph` is `alloc_col (new_colour ph)`, and
    `pages_allocator` is the `AllocIface` instance:
    - **`pages_allocator_ok`**: `allocator_ok` and `phase_ok`;
    - `alloc_idle`: in `Idle` it is stage 2's `alloc`, and meets the exact
      `alloc_ok`;
    - `alloc_no_fit`: the out-of-memory clause.
  - **Sweep.** The sweep is exposed as a step function, as on
    `akhil/sweep-refactor`:
    - `sweep_step g st p` sweeps the unit at page `p` and returns the next
      unit;
    - `sweep_inv` (`SweepAll.inv`) is the invariant at every step;
    - `sweep_start`, `sweep_step_inv` and `sweep_end` prove it;
    - `sweep_all` is the step iterated from page 0.

    `sweep_page`, `sweep_run`, their theorems and `sweep_commute` are
    re-exported.
  - **The collector's contract.**
    - `mark_done` is what the sweep's safety needs: well formed, no grey
      object, the tricolour invariant, and no pointer to a free block. An
      incremental mark can meet it with floating garbage.
    - `mark_exact` is what liveness needs: the same objects, black exactly
      when reachable from the roots. Reachability is from the graph modules,
      not `GC.Spec.Correctness`, which depends on modules akhil's line
      deletes.

**The colour of a new object is a parameter, and `alloc_correct` holds for
either colour.**
- `AllocPhase.alloc_col col` is `alloc` with the new header recoloured.
  `alloc_col_white` proves `alloc_col White == alloc` from `pages_ok_mc`. So
  `alloc_correct` (`alloc_meets alloc`, unchanged) is a theorem about the
  white allocator, and `alloc_col_white_ok` restates it.
- **`alloc_col_correct`**: for any colour but blue, from `pages_ok_mc`,
  `alloc_col col` meets `alloc_ok_col col`.
  - `alloc_ok_col col` is `alloc_ok`, with two changes:
    - the new object has colour `col`;
    - the caller's heap satisfies `pages_ok_mc` (it includes
      `well_formed_heap`).
  - Every other clause is `alloc_ok`'s word for word: `no_fit`,
    `others_unchanged` (live headers keep their colour exactly) and
    `unswept_unchanged`.
- **`pages_ok_mc g st`**, `pages_ok` up to colours, is `well_formed_heap g`
  and some list `ys` of live objects of `g` such that `whiten g ys`
  satisfies `pages_ok`. `pages_ok` with `well_formed_heap` implies it
  (`mc_of_ok`).
- **Why it holds** (`GC.Spec.Pages.Recolour.alloc_paint`):
  - The allocator reads and writes only words inside free blocks of the
    whitened heap (free slots, free pages, list cells) and the state.
  - No header of a live object lies in a free block (`blue_avoid`, from
    `Fill.apart`).
  - So allocating in `g` and in `g` with any of `ys` repainted any colour
    gives the same state and object, and the same heap up to that
    repainting.
  - With the whitened heap this carries `alloc_correct` back. With each
    object painted its own colour, it shows that live headers are kept
    exactly (`kept_hdr_y`).
- **Only swept pages are used**: `AllocPhase.new_hdr_swept` proves that the
  new object's header is not in an unswept page. Stage 2's `fields_swept`
  proves the same of its fields.
- **The mark keeps the `Marking` invariant**
  (`MarkPhase.mark_inv_recolour`). Every page is swept, so every live object
  is white in the whitened heap (`live_white`), and whitening it again
  changes nothing. `alloc_swept`: allocation keeps every page swept.

**Vacuity.**
- `AllocPhase`:
  - the empty heap satisfies `pages_ok_mc` (`init_mc`);
  - a black allocation there succeeds and gives a black object
    (`init_black`);
  - clearing its fields gives a heap satisfying `pages_ok_mc`
    (`init_black_filled`);
  - the hypotheses of `alloc_col_correct` are not refutable
    (`expect_failure`).
- `Allocator`:
  - the empty heap satisfies every phase's invariant (`init_inv`);
  - an allocation there succeeds in every phase, with the phase's colour
    (`init_alloc_ok`);
  - `inv`, the sweep's precondition and `mark_exact` are not refutable.

| Module | Lines (2,312 in all) | What it holds |
|---|---|---|
| `AllocIface` | 145 | Phases, `new_colour`, `allocator`, `alloc_post`, `allocator_ok`, `phase_ok`. |
| `Pages.Recolour` | 691 | `paint`, `whiten`; their reads and writes; `blue_avoid`; per path (pool pop, page acquire, carve, new run), allocation commutes with repainting; `alloc_paint`. |
| `Pages.ColourFacts` | 180 | Recolouring a live object keeps the walk, which blocks are free, `field_ok` and `well_formed_heap`, both ways (`step_facts`, `whiten_facts`). |
| `Pages.AllocPhase` | 663 | `pages_ok_mc`, `alloc_col`, `alloc_ok_col`, `alloc_col_correct`, `alloc_col_white`, `new_hdr_swept`, the vacuity lemmas. |
| `Pages.MarkPhase` | 253 | `mark_inv`, `live_white`, `mark_inv_recolour`, `alloc_swept`, `mark_inv_alloc`. |
| `Pages.Allocator` (`.fsti`, `.fst`) | 208 + 172 | The page allocator's interface and its proofs. |

**Changes to the plan made in item 0.**
- **The interface is phase-aware** (akhil, 2026-11-09). It does not use
  `alloc_inv`/`alloc_spec` as in §1.5. The phase decides the colour, and
  the invariant is per phase. Item 1 instantiates the same `allocator`
  record with #46's allocator.
- **While sweeping, a new object is white** and goes only in swept memory.
  akhil's `allocation_color (Sweeping c)` allocates in front of the cursor
  too, black. With pages there is no cursor, and plan §7.2 already chose
  "only swept pages".
- **New statements; none weakened.** `Pages.Theorems` is unchanged.
  `alloc_correct` still proves `alloc_meets alloc`.
  - `alloc_ok_col` asks only `pages_ok_mc` of the caller's heap, not
    `pages_ok`. A black object breaks L5 and L7, so `pages_ok` cannot hold.
  - For white, `alloc_col_white_ok` gives the full `alloc_ok`, and the
    `Idle` instance uses it.
- **Open for the incremental collector:** allocation *during* an
  incremental sweep.
  - The `Sweeping` invariant is `pages_ok_mc`, which is what the allocator
    is proved from.
  - A sweep in progress does not yet establish it. Unswept pages hold dead
    white objects whose fields may point to blocks already freed, so L10
    and `well_formed_heap` fail for them.
  - Plan §7.1's per-page mid-sweep invariant is the remaining work. It is
    akhil's `well_formed_heap_with (free_incremental c)` with "behind the
    cursor" replaced by "swept".
  - The sequential collector never allocates while sweeping, so stage 4 does
    not need it.
- **The `Sweeping → Idle` step still lacks `well_formed_heap`.** `sweep_end`
  gives `pages_ok` and every page swept; `well_formed_heap` after the sweep
  is item 2. *(Done in item 2, §13.)*
- **For the rebase onto akhil's main:** `Pages.Walk`, `Pages.Shape` and
  `Pages.Inv` use `GC.Spec.WalkEnd`, which his line replaces with
  `GC.Spec.Walk`. No other Pages module uses a module his line deletes.

---

## 13. Stage 4, item 2 as built: well-formedness after the sweep, and the step before it

All modules are in `mark-and-sweep/spec/`. They verify at the default rlimit
of 20, with no local rlimit raised, no `--retry`, no admits and no
assumptions. `make verify` checks them through `GC.Spec.Pages.Allocator`.

**The theorems.**
- **`SweepWf.sweep_all_wf`**: from `sweep_ready` and `mark_done`,
  `sweep_all` ends with `well_formed_heap`, as well as `pages_ok` and every
  page swept. This is what §11 left to stage 4.
  - Part 1 holds of every heap.
  - Parts 2 and 3 (`field_target`, `target_in`): a pointer field of a
    survivor is a field of a black object of the marked heap. Its target was
    black, so it survives, and it resolves to the same object. Infix targets
    keep `infix_addr_wf`, because their header lies in the fields of a
    survivor.
  - Part 4, no object is infix:
    - a survivor keeps its tag;
    - every free block of the swept heap either has a header the sweep
      wrote, of tag 0, or is a block of the marked heap with its header
      kept, and so not infix by the marked heap's part 4.

    This is `SweepTags.blue_ok`, proved per unit (`pool_blue_ok`,
    `run_blue_ok`, `kept_blue_ok`). It is carried through the sweep by
    `SweepWf.inv2`, which is `SweepAll.inv` with `blue_ok` for every unit
    swept so far. The heap's tail is kept from the marked heap.
- **`StartSweep.start_ready`**, the step before the sweep:
  - `start_sweep st` keeps every page's kind, marks every page that is not
    free unswept, and empties the lists of pages and the large lists. It does
    not touch the heap.
  - From the `Marking` invariant (`MarkPhase.mark_inv`: `pages_ok_mc` and
    every page swept) and `noGreyObjects`, it gives `sweep_ready`.
  - The pages keep their shapes, because the walk and which blocks are free
    do not read the colours of live objects (`shape_back`, `steps_same`).
  - No used slot or run block is grey: a live object is not grey, and any
    other block has its colour from the whitened heap, where every swept
    page holds white and free blocks only. This covers the one-word block at
    the end of the heap that §11 noted `noGreyObjects` does not reach.
- **`StartSweep.collection_cycle`**: the `Marking` invariant and
  `mark_done` give, after `start_sweep` and `sweep_all`, the `Idle`
  invariant (`pages_ok`, `well_formed_heap`, every page swept). With item 0's
  `phase_ok` (`Idle → Marking`, and the mark keeps `Marking`), this closes
  the sequential collector's cycle, for item 3.

**Interface changes (`GC.Spec.Pages.Allocator`).** All of them strengthen
the interface; none weakens it.
- `sweep_inv` is now `SweepWf.inv2`, which is stronger than `SweepAll.inv`.
  `sweep_start` and `sweep_step_inv` are proved for it.
- `sweep_end` and `sweep_all_correct` now also give `well_formed_heap`.
- New: `start_sweep`, `start_ready` and `collection_cycle`.

**Vacuity.**
- The empty heap of pages meets `collection_cycle`'s hypotheses
  (`init_cycle`).
- The hypotheses of `start_ready`, `collection_cycle` and `sweep_all_wf` are
  not refutable (`expect_failure`).

| Module | Lines (910 in all) | What it holds |
|---|---|---|
| `Pages.SweepTags` | 284 | `blue_ok` and its frame; `pool_pos3`, the walk over a pool page (slot starts, fillers, tail); `pool_blue_ok`, `run_blue_ok`, `kept_blue_ok`. |
| `Pages.SweepWf` | 380 | `inv2` and its step; `in_unit_lt`; part 4 (`part4_after`); parts 2 and 3 (`target_in`, `field_target`); `sweep_all_wf`, `sweep_end_wf`. |
| `Pages.StartSweep` | 246 | `start_sweep`, `clear_map_ok`; `same_shape`, `steps_same`, `shape_back`; `not_grey`; `start_ready`, `collection_cycle`; vacuity. |

**Changes to the plan made in item 2.**
- **What the sweep needs from the mark is stated with the allocator's
  invariant.** `start_ready` asks for `mark_inv` (the heap before the mark
  satisfied `pages_ok` up to colours) and `noGreyObjects`, not for a
  separate shape argument. Item 3 discharges `mark_inv` from item 0's
  `phase_ok`, and `noGreyObjects` from the mark.
- **No change to the stage-3 sweep theorems.** The tag facts are proved
  from the sweeps' definitions (`SweepPage.sw_hd`, `SweepRun.blk_hdr`), not
  added to `sweep_page_ok` or `sweep_run_ok`.

---

## 14. Stage 4, item 3 as built: `gc_correct` for pages, and the cycle

Item 3 adds new modules only, in `mark-and-sweep/spec/`, and one `Makefile`
root (`Pages.GcCorrect`). It leaves the existing `GC.Impl.Correct.gc_correct`,
the minor collection and the allocator interface unchanged. All modules
verify without `--retry` and with no local rlimit above 20 (the vacuity
checks run at 5). There are no admits and no assumptions.

**The theorems** (`GC.Spec.Pages.GcCorrect`). As built here,
`gc_correct_pages`, the cycle and `phases` held only without roots; §18
restates them over a collection that first greys the roots.
- `collect h_mark st = sweep_all h_mark (start_sweep st)`: the collector
  after the mark.
- `gc_correct_pages h_init st gs roots`:
  - **Requires** `PA.inv Idle h_init st` (the allocator's invariant) and
    `mark_pre h_init gs roots`, what the unbounded mark needs (as
    `Corr.mark_satisfies_mark_post`, with the graph facts of
    `gc_precondition_with_roots`).
  - **Ensures** `gc_safe_pages` and `gc_live_pages` of
    `collect (Mark.mark h_init gs) st`.
- `gc_correct_gen`: the same conclusion for any marked heap that satisfies
  `GP.marked` (`Corr.mark_post` and its clause on fields) and the
  allocator's marking invariant `MP.mark_inv`.
- `MarkSteps.mark_keeps_inv`: `Mark.mark` keeps the marking invariant. It
  only recolours objects that are not free, and item 0's
  `mark_inv_recolour` (the `phase_ok` clause) keeps the invariant at each
  recolouring. This is how item 2's `start_ready` gets `mark_inv`.
- **The cycle.** `reach g st` is an inductive type of the states reached
  from the empty heap of pages by any sequence of:
  - allocations, through the interface in `Idle`, each followed by the
    caller's writes to the new object's fields (`I.fields_written`);
  - collections, each with roots that satisfy `mark_pre`.

  Two theorems follow:
  - `reach_inv`: every state reached is in the `Idle` invariant;
  - `cycle_correct`: every collection from a reached state satisfies
    `gc_correct_pages`.

  `phases` spells out the phases of one collection through the interface:
  `Idle` gives `Marking` (`phase_ok`), the mark keeps `Marking`, and clearing
  then sweeping gives `Idle` (item 2's `collection_cycle`).

**The old and the new `gc_correct`, clause by clause.** Old:
`GC.Impl.Correct` (`gc_safe`, `gc_live`). New: `GC.Spec.Pages.GcCorrect`
(`gc_safe_pages`, `gc_live_pages`).

| | Old clause | New clause | |
|---|---|---|---|
| Hypotheses | `gc_precondition_with_roots` (bounded mark) and `collect_post`, the Pulse collector's postcondition | `PA.inv Idle h_init st` and `mark_pre` (unbounded `Mark.mark`), with the collection given by `collect` | restated |
| **Safety** | | | |
| Layout | `well_formed_heap s2` | `well_formed_heap g` | same |
| The mark is exact | `Corr.full_gc_correctness h_init s2 roots` | `Corr.full_gc_correctness h_init g roots` | same predicate |
| Survivors unchanged | `Corr.major_gc_live_subgraph_isomorphism h_init s2 roots` | `Corr.major_gc_live_subgraph_isomorphism h_init g roots` | same predicate |
| Lists hold only free blocks | `FLs.fls_sound s2 fls` (the 17 lists) | `lists_sound g st`: `FLs.fls_sound g st.large`, and each swept pool page's list holds exactly its free slots (L4) | restated |
| No pointer to free memory | (inside `well_formed_heap`'s use by the mark) | `Mark.no_pointer_to_blue g` (L10) | new |
| The allocator can run again | — | `PA.inv Idle g st`: `pages_ok`, `well_formed_heap`, every page swept | new |
| **Liveness** | | | |
| (a) Unreachable reclaimed | `unreachable_reclaimed h_init s2 roots`, with `CC.in_extent`, `CC.blue_covered` | `unreachable_reclaimed h_init g roots`, with `SV.in_extent`, `SV.blue_covered`, the same definitions copied word for word | same |
| (b) Free memory listed | `fls_complete s2 fls`: every free block with a field is on its class's list | `free_listed g st`: every free slot is on its page's list (L4); every page with a free slot is on `avail[c]` (L8); every free block of a run of at least `lg_min` words is on the large lists (L9) | restated |
| (c1) Nothing held without cause | `coalescing_lossless`: some correct mark `h_mark`; `s2` agrees with `coalesce (sweep h_mark)`; the lists are the coalescer's; `coalesce_correct_post` (free space and free words as the swept heap's, no two adjacent free blocks, white survivors at their size) | `sweep_lossless`: some marked heap `h_mark` (`GP.marked`) with `(g, st) == collect h_mark st_m`, and `lossless`: every black object survives white at its size; every object that is not free was black; a word of a block of `h_mark` is free exactly when the block was not black; in a run, no two adjacent free blocks and no free whole page (L7); a page still in a pool holds a live object, so an empty pool page is `Free` | restated |
| (c2) Nothing lost | `heap_partitioned`: `zero + (white + on lists + fragments) * 8 == walk_end` | `heap_classified`: every block of the walk is live, a free slot, a filler (`cls c − w` words), a pool page's tail (`tail_words c`), a `Free` page, a free block of a run (listed when at least `lg_min`, by (b)), or the heap's tail; and `PT.heap_partitioned`: `zero + (live + listed + waste, by kind) * 8 == walk_end`, `walk_end + 8 >= heap_size` (§15) | restated, with the equation |
| **Vacuity** | `gc_correct_hyps_not_false`, `gc_live_not_from_safe`, `unreachable_reclaimed_header` | the same three, plus `gc_correct_gen_hyps_not_false`, `swept_not_false`, `MarkSteps.mark_keeps_inv_hyps_not_false`, and `reach_start` | |

How the new clauses compare in strength:
- **The safety clauses keep their exact predicates** from
  `GC.Spec.Correctness`.
- **(a) is unchanged.**
- **(b)** lists by page and by run instead of by size class. A free block
  in a run smaller than `lg_min` is not listed. (c2) counts it as waste,
  and L7 limits how many there are.
- **(c1)** compares the result with the marked heap directly. The old
  clause compares it with the coalesced heap, through agreement up to free
  links. "A word is free exactly when its block was dead" combines the old
  clause's two coverage equalities, sweep then coalesce, into one.
- **(c2) is not the old arithmetic statement.** It says the same thing (no
  fourth class of block) as a case split on each block of the walk, and
  bounds each kind of waste per block. The word-count equation was added
  afterwards (§15).

**How it is proved.**
- **Survivors** (`Pages.Survive`):
  - `black_survives` and `obj_survivor` give the survivors;
  - `pointer_fields_kept` gives their fields and how their pointers
    resolve, so the same successors in the heap graph (`GcPillars.succ_kept`);
  - `dead_covered` and `live_uncovered` give which words are free.
- **The witness for the pillars** (`Pages.GcPillars`).
  `full_gc_correctness` quantifies `is_black x h_mark` over every object of
  the final heap.
  - **Why the marked heap won't do:** the page sweep gives back whole
    pages from inside dead large objects. Each such page gets a new header,
    at a word that was a field of the dead object and may read as black.
  - **The witness instead:** `clean h_mark`, the marked heap with each page
    start that is not on its walk set to a white header. No header of the
    walk changes, so pillar 2 holds as in the marked heap (`black_same`).
  - **Why it works:** an object of the final heap that is black in
    `clean h_mark` is not free (`black_clean`), so it is a survivor.
- **Where free blocks start** (`Pages.SweepStarts`). `starts_ok` is a new
  per-unit fact, carried through the sweep by `inv3`, as `inv2` carries the
  tag facts: every free block of the swept unit starts where a block of the
  marked heap started, or at a page start. It gives `black_clean`. It also
  gives (a) at the heap's last word: a block there would be too short to be
  an object, and no page starts there.
- **Pool pages** (`Pages.SweepPools`): `pool_live`, carried through the
  sweep with `SweepAll.inv`. A page still in a pool after the sweep holds a
  live object.

| Module | Lines (1,875 in all) | What it holds |
|---|---|---|
| `Pages.MarkSteps` | 117 | `push_inv`, `step_inv`, `aux_inv`: `Mark.mark` keeps `MP.mark_inv`; vacuity. |
| `Pages.SweepStarts` | 327 | `starts_ok`, its frame; `pool_starts`, `run_starts` (`olds_at`, `merge_at`, `split_at`); `inv3`, `sweep_all_inv3`. |
| `Pages.SweepPools` | 159 | `pool_live`; `step_entries`, `pool_new`, `pools_step`; `sweep_all_pools`. |
| `Pages.Survive` | 374 | `in_extent`, `blue_covered`; `swept`; `black_survives`, `survivor`; `cover_at`, `not_last`, `dead_covered`, `live_uncovered`; `field_kept`, `pointer_fields_kept`. |
| `Pages.GcPillars` | 396 | `marked`, `graph_pre`; the witness `clean` (`clean_walk`, `clean_from_page`, `black_same`, `black_clean`); `succ_kept`, `field_same`, `pillars`, `iso`. |
| `Pages.GcCorrect` | 502 | `collect`, `mark_pre`; the clauses; `live_a`, `lists`, `live_c1`, `classify_page`, `live_c2`; `gc_correct_gen`, `mark_ok`, `gc_correct_pages`; `reach`, `reach_inv`, `cycle_correct`, `phases`; vacuity. |

**Changes to the plan made in item 3.**
- **The pillars use a cleaned witness**, not the marked heap (see above).
  §2.3 assumed the marked heap would do.
- **(c2) is a classification of blocks**, not the word-count equation. The
  equation was added afterwards (§15).
- **The theorem is about the specification's unbounded `Mark.mark`.** The
  Pulse collector uses `mark_bounded`, with overflow rescans, and has no
  page version yet, so there is no `collect_correct` for pages.
  - `mark_bounded` also only recolours objects that are not free, so
    `MarkSteps`' induction applies to it unchanged.
  - Any other mark can use `gc_correct_gen` directly.
- **The cycle is sequential:** allocations happen only in `Idle`.
  Allocation while marking is item 0's `mark_inv_alloc` and
  `alloc_col_correct`. Allocation while sweeping needs the mid-sweep
  invariant of §7.1, which is still open.

---

## 15. Stage 4, after item 3: the (c2) equation, and item 4

Both changes verify without `--retry` and with no local rlimit above 20.
There are no admits and no assumptions.

**(c2) as a word count** (`GC.Spec.Pages.Partition`, 254 lines).
- **Estimate first.** The old equation is `GC.Spec.Partition`'s
  `partition_exhaustive` and `walk_is_tiled`, about 250 lines. For pages
  the classification of every block was already proved (§14), so the
  equation needs only the sums and the tiling. The estimate was 300 to
  450 lines, under the 1,000 allowed, so it was proved.
- **Kinds.** `kind_of g st y` gives each block of the walk exactly one
  kind, the first that applies:
  - `KLive`: white;
  - `KSlot`: a free slot (on its page's list, L4);
  - `KListed`: a free block of a swept run of at least `lg_min` words (on
    the large lists, L9);
  - `KFiller`, `KTail`, `KFreePage`, `KRunWaste` (a free block of a run
    smaller than `lg_min`), `KHeapTail`: the waste of `block_class`;
  - `KOther`: none of these.
- **The equation.** `heap_partitioned g st`:
  `zero + (live + (slots + listed) + (fillers + tails + free pages + run
  waste + heap tail)) * 8 == walk_end g zero`, and
  `walk_end g zero + 8 >= heap_size`.
  - The second conjunct is new. The old clause bounds its words by
    `walk_end` only. Here the walk is shown to reach the end of the heap,
    up to a last word too short for a header (`Shape.heap_tiled`).
  - The kinds are exclusive by construction, so nothing is counted twice.
    The old clause needs list disjointness for that; here the lists are
    disjoint by L4 and L9 and are not summed.
- **The proof.**
  - `kinds_exhaustive`: the total splits by kind.
  - `other_zero`: `KOther` sums to zero when every block satisfies
    `block_class`.
  - `walk_tiled`: the total reaches `walk_end`, through
    `WE.walk_end_step`.
- **Where it is used.** `block_class` moved from `Pages.GcCorrect` to
  `Pages.Partition`, unchanged except that it names its disjuncts.
  `gc_live_pages` gains `PT.heap_partitioned g st` after
  `heap_classified`, and `live_c2` proves both.
- **Vacuity.**
  - `partitioned_needs_class`: the equation does not follow from the
    tiling alone.
  - `partitioned_hyps_not_false`: the hypotheses of `partitioned` are not
    refutable.
  - `gc_live_not_from_safe` still holds with the new conjunct.

**Item 4: the seed-sensitive query of `Pages.Large`.**
- The query was the precondition of `lists_B` in `carve_B_prev`,
  `unlink_ctx`. It is a conjunction of about twenty facts, proved there in
  the context of all of `pages_ok`. It timed out at the default seed
  without `--retry`.
- It is split into two lemmas, each with only the facts it needs:
  - `unlink_ctx_intro` proves `unlink_ctx` from the link step and the
    cell's facts in the relinked heap;
  - `carve_B_lists` moves the cell's facts to the relinked heap and calls
    `lists_B`.

  `carve_B_prev` calls `carve_B_lists` right after `pages_ok_elim`. No
  statement changes.
- **Stability.**
  - `Pages.Large` passes without `--retry` at the default seed and at
    seeds 1 to 8.
  - `Pages.Partition` passes at seeds 0 to 7. Its recursive step in
    `walk_tiled` failed at seed 2 until the unfolding was made explicit
    (`total_step`).
  - `Pages.GcCorrect` passes at seeds 0 to 3.


---

## 16. Stage 5a as built: the allocator and the sweep in Pulse

akhil's merge into main has not landed, so stage 5a adds new modules only.
It does not touch the minor collection, the existing Pulse collector, the
runtime bridge (`alloc_gen.c`) or the existing `gc_correct`. Threading the
allocator through `gen_gc` and the minor collection is left for 5b, after
the rebase (§6 stage 5, second half).

All modules are in `mark-and-sweep/impl/`. They verify without `--retry`,
with no local rlimit raised (every module runs at 20), no admits and no
assumptions. `GC.Impl.Pages` is a root in the `Makefile`, so `make verify`
checks them all.
- **Trusted:** only what the rest of the collector already trusts.
  - The word reads and writes of `GC.Impl.Heap`.
  - Its platform assumption that `size_t` holds 64 bits
    (`platform_fits_u64`). The page map's array indices rely on it.
- **Verified from clean.** `make verify` was run from an empty cache in a
  scratch worktree: 277 modules, 35 minutes. It was then re-run
  incrementally after the last edits.
- **Seed stability.** Every new module passes at Z3 seeds 0, 1 and 2,
  without `--retry`; `RunMapLemmas` also passes at 3.
  - The seed checks found two fragile proofs: `Pool.fill_slot`'s `rewrite`,
    and the second-pass lemmas of `RunMapLemmas`.
  - Both were restructured (an existential postcondition; one explicit
    lemma per entry, `pass2_upd`). No rlimit was raised.

**The theorems.** Each Pulse function's postcondition is an equality with
the specification's function, for every heap and state the precondition
allows:

| Pulse function | Computes exactly | Precondition |
|---|---|---|
| `Init.init` | `Init.init_heap g`, `Init.init_state` | none |
| `Alloc.alloc heap t wz col` | `AllocPhase.alloc_col col g st wz` | none |
| `Alloc.alloc_white` | `Alloc.alloc g st wz` | none |
| `Pool.small_alloc`, `pop`, `acquire`, `pool_init`, `find_free` | `Pool.small_alloc_as false`, `pop_as false`, `acquire`, `PoolInit.pool_init`, `find_free` | none (`wz + 1 <= small_max` for `small_alloc`) |
| `Large.large_alloc`, `find_fit`, `carve`, `find_run`, `new_run` | `Alloc.large_alloc_as false`, `split_fit` on `walk g (large_head st) heap_words`, `carve_as false`, `find_run`, `new_run_as false` | none beyond the indices' ranges |
| `SweepPage.sweep_page`, `pool_step` | `SweepPage.sweep_page`; then `SweepStep.push_avail` | the record is the page's entry |
| `SweepRun.run_step` | `SweepRun.sweep_run` with the list head, then `SweepStep.run_state` | the record is a run head and the run's pages are run pages |
| `Sweep.start_sweep` | `StartSweep.start_sweep` | none |
| `Sweep.sweep_all` | `SweepAll.sweep_all` | `map_ok` of the starting map |
| `Sweep.sweep` | `SweepAll.sweep_all g (StartSweep.start_sweep st)` | `map_ok` |

- With the specification's theorems, these give the allocator's and the
  sweep's correctness directly:
  - `alloc_col_correct` (any colour but blue, from `pages_ok_mc`), and
    `alloc_correct` for white;
  - `sweep_all_correct`, `sweep_all_wf` and `collection_cycle` for the
    sweep;
  - `init_pages_ok` and `Allocator.init_inv` for `init`.
- The allocator has no precondition at all. The specification's allocator
  is total, and the Pulse code follows its guarded reads and writes
  (`Shape.hdr`, `Blocks.wr`) with the same tests. So, for example, the
  walk of list 0 stops after `heap_words` cells, as `Cells.walk` does,
  even on a cyclic list.
- `sweep_all` needs `map_ok` only to know that a run it reaches still has
  its run pages. A step changes only its own unit's entries
  (`Sweep.pool_ahead`, `run_ahead`). `sweep_ready` includes `map_ok`, so
  the collector always has it.

**The state in memory** (`GC.Impl.Pages.State`).
- `pstate_t` is three arrays:
  - `tpm`, one `pinfo` per page;
  - `tavail`, `n_cls` words;
  - `tlarge`, `n_lists` words.
- `pages_st t st` ties them to the specification's `pstate`.
- `pinfo` is the C form of `page_info`. The kind is a code (0 free, 1 pool,
  2 run head, 3 run continuation) with its argument (the class or the run
  length) beside it, and `nfree` is a machine word. `view` reads a record
  as a `page_info`. It is total: a record with a bad code or argument reads
  as a free page, and the code tests (`is_pool`, `is_head`, `is_cont`) are
  exactly the tests `view` makes.
- `pm_rel` relates the array to the page map entry by entry.

**How the run sweep is proved** (`GC.Impl.Pages.RunLemmas`,
`RunMapLemmas`, `SweepRun`).
- The specification builds the run's layout as a list,
  `fin g s e = split (merge (olds g s e))`, and writes it in one go
  (`wr_all`). The Pulse code makes one pass over the run instead.
- **`fin`, a stretch at a time:**
  - `fin_live`: a black block is first in `fin`;
  - `fin_dead`: a block that is not black starts a stretch that ends at
    `dead_end`, and `fin` starts with `split1` of that stretch, cut into
    the piece before its whole pages, the pages, and the piece after them;
  - `fin_stop`: where the walk leaves the run, `fin` is empty.
  - The key step is `merge_dead`, proved by induction over the stretch.
- **The deferred link.** A listed block's link is the next listed block,
  which is not known yet. The pass writes it when that block is found, and
  closes the last one with the old list head.
  - `emit_ok` is the invariant: every word reads as the specification's
    writes of the blocks so far (`val_at`), with the open link still as it
    was.
  - `val_at_fp` is what makes this work: the list head given to the writes
    matters only at the last listed block's link.
  - `emit_plain`, `emit_listed` and `close_eq` are the steps; `close_eq`
    ends with `wr_all` by heap extensionality.
- **The map in two passes:**
  - the first pass gives each whole free page a free page's entry as it
    writes it (`map_in`);
  - a second pass gives the other pages their entries: each stretch's first
    page a run head with the stretch's length (`run_from`), the rest
    continuation entries (`pass2`, `pass2_done`).
  - A page is free after the first pass exactly when the layout freed it
    (`freed_iff`), since every page of a run was a run page.

**Other main lemmas.**
- `Large`: `fit_inv_ex`, the first-fit invariant. `split_fit` on the walk is
  the cells passed so far, followed by `split_fit` on the rest. Its four
  steps are `fit_start_ex`, `fit_next_ex`, `fit_found_ex` and `fit_none_ex`.
- `Pool`, `Large`: per-branch unfoldings of the specification's writes
  (`fill_unfold_f`, `carved_split`, `run_listed`, ...). See the Pulse
  lessons below.
- `SweepPage`: `sw_step`, `dead_step`, and `sw_out` from the specification.
- `Sweep`: `sweep_from_step`, the four cases of `step`, and the frame
  lemmas above.

**Vacuity** (`GC.Impl.Pages.Vacuity`).
- Each loop invariant holds where its loop starts: `emit_ok`, `map_in`,
  `pass2` and `fit_inv_ex`.
- `sweep_all`'s precondition holds of the empty heap of pages.
- The hypotheses of the step lemmas are not refutable (`expect_failure`):
  `emit_plain`, `emit_listed`, `fin_live`, `fin_dead`, `run_pages`,
  `pass2_head`, `pass2_cont`, `pass2_done` and `fit_found`.
- The postconditions are equalities with the specification's functions,
  so they cannot hold vacuously.

**Extraction and the C test** (`mark-and-sweep/pages-c/`).
- **`make extract`** extracts `GC.Impl.Pages.{Init,Alloc,Sweep}` from
  their checked files into one bundle, `GC_Pages.{c,h}` (1.4k lines of C).
  - The entry points are `init`, `alloc`, `alloc_white`, `start_sweep`,
    `sweep_all` and `sweep`.
  - `pinfo` and `pstate_t` extract as structs. The page size folds to a
    constant (`32768ULL`), and the class table is a chain of tests
    (`cls_u64`).
  - There is no `Prims` or `krml_checked_int` arithmetic.
  - `krmlinit_globals()` must run after `zero_addr` and `heap_size_u64`
    are set, as for the generational snapshot.
- **`make test`** builds `pages_test.c`, which needs neither F* nor
  KaRaMeL: it uses `compat.c` and `krmllib/` from `generational/snapshot`.
  - Each test lays out a small heap of 32 KB pages by hand, runs the
    extracted function, and checks every header, link, entry and list head
    against values worked out from the specification. 407 checks, all
    passing:
    - `init`, with and without a heap tail;
    - small blocks: a fresh pool page and its slot links, a second pop, a
      black allocation, wosize 0 with its 1-word filler, and a 9-word block
      with its filler and the page's tail filler;
    - large blocks: a new run with its listed rest, carving that stays
      listed, carving that unlinks a remainder below `lg_min`, a request
      with no room (heap and state byte-for-byte unchanged), a page filled
      exactly, a run of two pages, and no free page for a new class;
    - the sweep:
      - a pool page with a survivor (the free slots linked from the last
        one down, the page first on its class's list), and a pool page
        given back;
      - a run whose dead stretch gives back a whole page and leaves a
        listed piece, and a dead run given back;
      - a run with two listed stretches and an unlisted one, in address
        order in front of the earlier run's;
      - a short dead tail, and stale lists cleared;
    - a sweep followed by allocations from what it freed.
  - **Mutants.** In a scratch copy of the C, each of these was rejected:
    linking a free slot to its header instead of its object (6 checks
    fail), and listing only blocks above 200 words (2 fail) or not
    listing a new run's rest (9 fail).

| Module | Lines (3.8k in all) | What it holds |
|---|---|---|
| `Pages.Params` (`.fsti`, `.fst`) | 27 + 83 | `page_wsize_u64`, `n_cls_u64`, `cls_u64`, tied to the specification's parameters through `friend`; `Spec.Pages.Params` is unchanged. |
| `Pages.State` | 259 | `pinfo`, `view`, `pm_rel`, `pstate_t`, `pages_st`; reading and writing an entry, a class's list head and list 0's head; `clear_lists`. |
| `Pages.Heap` | 141 | `hdr_at` and `wr`, the guarded read and write; the header values (`ohdr_u64`, `bhdr_u64`, `blue_hdr_u64`, `recolour_hdr`) proved equal to the specification's. |
| `Pages.Init` | 123 | `init`. |
| `Pages.Pool` | 436 | `class_of_u64`, `find_free`, `pool_init`, `acquire`, `fill_slot`, `pop`, `small_alloc`. |
| `Pages.Large` | 691 | `find_fit`, `carve`, `all_free`, `find_run`, `write_run`, `new_run`, `large_alloc`. |
| `Pages.Alloc` | 107 | `alloc_white`, `alloc`. |
| `Pages.SweepPage` | 298 | `page_any_live`, `sweep_slots`, `sweep_page`, `push_avail`, `pool_step`. |
| `Pages.RunLemmas` | 373 | `dead_end`, `fin_live`, `fin_dead`, `merge_dead`; `va`, `val_at_append`, `val_at_fp`; `emit_ok`, `emit_plain`, `emit_listed`, `close_eq`. |
| `Pages.RunMapLemmas` | 201 | `map_in`, `freed_iff`, `pass2` and its steps (`pass2_upd`, `new_head`, `new_cont`), `pass2_done`. |
| `Pages.SweepRun` | 686 | `run_inv`, `emit`, `emit_pre`, `emit_stretch`, `find_dead_end`, `lay_out`, `close_run`, `count_run`, `pass2`, `run_step`. |
| `Pages.Sweep` | 253 | `start_sweep`, `sweep_all`, `sweep`, and the step and frame lemmas. |
| `Pages.Vacuity` | 120 | The vacuity checks above. |
| `Pages` | 22 | The root: includes `Init`, `Alloc`, `Sweep` and `Vacuity`. |

**Changes to the plan made in stage 5a.**
- **Split stage 5.** 5a is the allocator and the sweep as functions, in new
  modules, extracted and tested on their own. 5b threads the state through
  `gen_gc`, the minor collection and the bridge, after the rebase onto
  akhil's merge. With that split, §6 stage 6's checks are done here for the
  allocator: the class table, the page size and the `pm` record extract as
  intended.
- **The parameters are read through `friend`.** A new interface,
  `GC.Impl.Pages.Params`, gives `page_wsize_u64` and `cls_u64` with their
  values tied to the specification's. Every other module still sees the
  parameters as abstract.
  - Changing the page size is now a two-line edit: `Spec.Pages.Params`, and
    the literal in `Impl.Pages.Params`, whose `assert_norm` fails the build
    if they disagree.
  - The class table extracts as a chain of tests, not the static table
    §6 stage 6 asked for. It is used only in allocation's class search and
    in a pool page's slot arithmetic. Make it a table if stage 9 shows it
    matters.
- **The page map is an array of `pinfo` records**, not of `page_info`.
  `page_info`'s kind carries arguments and its `nfree` is a `nat`, so it
  cannot be a C struct.
- **The page sweep makes two passes**, as the specification does: first
  `any_live`, then the slots. The specification gives back a page with no
  survivor as one blue header on the *unswept* page. A single pass, as in
  OCaml 5's `pool_sweep`, would also leave the slots' blue headers and links
  in the freed page's words. Those words are dead, but the heaps would
  differ.
- **The run sweep is one pass over the run plus one over its pages,** not a
  list built and then written (above).
- **Performance is not addressed here** (stage 9):
  - `find_run` is the specification's search: quadratic in the worst case.
  - `start_sweep` visits every page (§7.5's epoch is the fix).
  - The class search is linear in the class number.
- **Extraction is a separate bundle** in `mark-and-sweep/pages-c/`, not in
  `generational/Makefile`. The generational collector does not use the
  page allocator yet, and keeping it apart leaves the existing snapshot as
  it is.

**Lessons for Pulse proofs against total specification functions.**
- Postconditions of the form `exists* g'. is_heap heap g' ** pure (g' == f g)`
  are robust. `rewrite p as q` is not: Pulse normalises both sides,
  unfolding `Blocks.wr` and the specification's `if`s, and then fails to
  match them branch by branch. Give each branch its own unfolding lemma,
  with the addresses as arguments (`fill_unfold_f`, `carved_split`).
- After a `while` loop, read the loop variable (`let vj = !j`) and assert
  the exit fact before using it. A lemma called last in a function needs
  its conclusion asserted for the postcondition to see it.
- Pass ghost lists and positions as implicit arguments, unified with an
  existential's witness and constrained by pure equations. Then calls
  chain without slprop rewrites (`emit`'s `#xs #a`).
- Return a final position as a machine word rather than an erased `nat`.
  A doubly erased `nat` in a pure fact did not match its use.
- Bind `get_color` to a variable before testing it: KaRaMeL rejects its
  inlined `let` inside `||`.

## 17. The efficiency pass (2026-11-10)

This applies the project rule above to stage 5a's Pulse allocator and
sweep. Every theorem is unchanged. Each Pulse function is still proved
equal to a specification function. Two of those specification functions
now make the choices the fast code makes, and their theorems are proved
again unchanged (the page sweep), or need nothing new (the allocator's
fast path takes a precondition the invariant gives).

**What changed.**

| Before (§16) | Now | Like |
|---|---|---|
| `class_of` by a linear search, each step a chain of tests | a table of 129 words in the state (`State.class_at`) | OCaml 5's `sizeclass_wsize`, the prototype's `cls_of` |
| slot size and slots per page by a chain of tests and a division | two tables of 31 words (`cls_at`, `ns_at`) | `cls_wh`, `cls_ns` |
| `pop`: the slot from the list entry by a division, then checks | the list entry *is* the slot; no division, no check (`Ready.heads_ready`) | `alloc_small` |
| `pop` stores the whole page entry | stores the free-slot head and count only (`State.write_slots`) | `alloc_small` |
| guarded reads and writes in `pop` | plain ones, with the slot's bounds proved | `alloc_small` |
| `find_free` scans from page 0 | from the free-page hint, which it then moves up | `take_free_page`, `free_hint` |
| `find_run` tests every start, `all_free` at each: quadratic | one pass from the hint, counting free pages in a row | `lg_grow` |
| `start_sweep` visits every page | adds one to a sweep epoch; visits the pages only when the epoch wraps (once in 2^64 cycles) | OCaml 5's cycle start (list heads only) |
| page sweep: a pass for a survivor, then a pass over the slots | one pass; the page has a survivor when fewer slots than all are freed | `pool_sweep`, `sweep_pool` |

- The class tables are arrays in the state, not functions. KaRaMeL writes a
  function of constants (an `if` chain or a `match`) as nested `?:`, and
  clang did not make the 128-case one a table: 23 ns per allocation
  against 15.5 ns with an array (measured). `init` fills them from
  `Params.class_u64`, `cls_u64` and `n_slots_u64`. `pages_st` fixes their
  contents to the specification's values (`State.tables`).

**The proofs.**
- **The state** (`GC.Impl.Pages.State`). A stored record (`prec`) keeps the
  epoch of its page's last sweep, not a swept bit. `to_pinfo` reads it back:
  swept when free or swept in the current epoch.
  - `meta_ok`: no stored epoch is past the current one, the epoch is at
    least 1, and no page below the hint is free (`none_free_below`).
  - `start_epoch` proves `pages_st t ({ st with pm = unswept_map st.pm })`,
    which `Sweep.start_eq` shows is `StartSweep.start_sweep`'s map.
  - `write_entry` lowers the hint when it stores a free page below it.
    `write_used` skips the hint for records that are not free.
  - `init` now takes the arrays with any contents (`pages_raw`), as a caller
    has them at start-up.
- **The allocator** (`GC.Impl.Pages.Ready`, `Pool`). `heads_ready st` says
  that each class's list head is 0, or names a pool page of the class whose
  free-slot list starts at a slot.
  - `pages_ok_ready` and `mc_ready` prove it from `pages_ok` and from
    `pages_ok_mc`, the preconditions of `alloc_meets` and
    `alloc_col_correct`. So `alloc` and `alloc_white` take it as a
    precondition and lose nothing.
  - Under it, `pop` equals `Pool.pop_as false` exactly (`ready_head`,
    `slot_of_obj`).
  - `find_free` equals `find_free pm 0`: `find_free_skip` shows the search
    may start at the hint, and `find_free_below` shows the hint may move to
    the page found.
  - `find_run` equals `NewRun.find_run pm k 0`. `hint_skip` covers the start,
    `run_skip` and `not_free_breaks` a page that is not free, and
    `run_found` and `run_none` the two ends.
- **The page sweep: a specification change.** `SweepPage.page_freed` now
  writes the page's blue header *over the swept slots* (`sw_heap`), not over
  the marked page. That is what a single pass leaves.
  - `sweep_page_correct` (`sweep_page_meets`) is proved again, unchanged in
    statement (`page_freed_ok`).
  - `SweepStarts.freed_page_starts`, `SweepTags.freed_page_blue_ok`, and
    `SweepOrder.page_frame` and `page_local` follow (`sw_out`, `sw_local`).
  - `dead_count` gives the single pass its test.
- **Checked:** every changed and new module, without `--retry` and with no
  rlimit raised. `make verify` was run from an empty cache in a scratch
  worktree: 281 modules, 42 minutes, no errors. The C test passes, with `pages_test.c` changed for the
  stored records, the epoch, `tmeta` and the tables: 407 checks.

**The measurements** (`mark-and-sweep/pages-c/bench`, `make bench`).
- Both builds use `cc -O2 -flto` on an Intel i5-1038NG7. The heap is 4096
  pages of 32 KB. Each run is a fresh heap, and the same requests and
  survivors go to both.
- Medians of 15 repetitions, 5 rounds alternating the two binaries, taken
  before `reallocS` was added. The `reallocS` row is 3 rounds of 15.

| Workload | Prototype B2 | Verified | Before §17 |
|---|---|---|---|
| small allocation (ns) | 11.83 | 12.10 (+2.3%) | 50.4 |
| mixed, 0.5% large (ns) | 32.9 | 20.2 | 70.9 |
| large only (µs) | 4.73 | 2.81 | 5.73 |
| sweep, 10% survive (ms) | 1.145 | 1.059 | 1.42 |
| sweep, 50% (ms) | 1.990 | 1.947 | 2.61 |
| sweep, 90% (ms) | 1.081 | 1.028 | 1.30 |
| realloc after sweep50, mixed heap (ns) | 12.40 | 13.91 (+12%) | 50.6 |
| reallocS, small-only heap (ns) | 12.6 | 15.1 (+20%) | — |

- Large allocation is faster than the prototype's. The prototype's
  `lg_grow` joins a new run to its neighbours, which makes its first-fit
  list longer. That difference is in the prototype's layout, not in proof
  overhead.
- **Allocation after a sweep was not yet within 5%** (`realloc` +12%,
  `reallocS` +20%). The second pass below closes it.
- Not addressed: the prototype keeps never-used pages as one "wilderness"
  block, so they are never touched; `init` writes one header per page.

**Files.** New: `GC.Impl.Pages.Ready`, `mark-and-sweep/pages-c/bench/`
(`bench.c`, `proto_stubs.c`, `stub/GC_Gen_Impl.h`, `Makefile`; the
prototype's sources are read from its branch with `git show`). Changed:
`Pages.{Params,State,Pool,Large,Alloc,SweepPage,SweepRun,Sweep,Init}`,
`Spec.Pages.{SweepPage,SweepStarts,SweepTags,SweepOrder}`, and the
extracted C and its test.

### 17.2 The prototype's list orders, and the state as two pointers (2026-11-10)

Decision (the user, 2026-11-10): both lists in the prototype's order, every
theorem unchanged.
- A page's free slots are linked lowest address first.
- Each class's list of pages is in address order, with a list tail per
  class in the specification's state.

**The free slots, lowest first** (`Spec.Pages.SweepPage`).
- `sw_heap` links a freed slot to the next freed slot after it
  (`nd_from`, `dead_from`), not to the one before it. The list head is the
  lowest freed slot (`pool_swept`'s `free_head = nd_from g i c 0`).
- `sweep_page_correct` is proved again with its statement unchanged:
  `dead_chain` now runs up the page; `dead_from_mem`, `dead_from_norep`
  and `dead_len` replace their downward forms.
  - In `SweepOrder`, `nd_local` replaces `hd_upto`'s half of `dead_local`.
- **The Pulse pass** (`Impl.Pages.SweepPage.sweep_slots`, `SlotLemmas`).
  It is still one pass in address order. A freed slot's link is written
  when the next freed slot is found, and the last one's (0) at the end, as
  in the prototype's sweep.
  - `pend g i c k last` is the heap after slot `k - 1`: the swept slots,
    except the open link at `last`, which still holds the marked heap's
    word. `last_ok` says where `last` is.
  - The steps are `pend_live`, `pend_dead` and `pend_end`, each by heap
    extensionality (`HE.heap_read_word_ext`).
  - `link_last` writes the open link only when there is one, so the two
    branches join.

**The page lists, in address order** (`Spec.Pages.Inv`, `Pool`,
`SweepStep`, `Frame`).
- `pstate` has `atail`: per class, the last page on the list (index + 1;
  0 if none). `avail_ok` adds `atail.[c] == chain_tail ps` for the list's
  pages `ps`.
- Allocation takes pages from the front, as before:
  - `acquire` puts a fresh page in front, and sets the tail when the list
    was empty;
  - `pop`, when a page fills, removes it, and sets the tail to 0 when that
    empties the list (`pop_tail`).
- The sweep appends (`SweepStep.push_avail` = `push0`, then the link):
  - `push0` stores page `i`'s entry with link 0, makes it the tail, and
    makes it the head when the list was empty;
  - then the old tail (`old_tail`, a page already on the list,
    `old_tail_listed`) links to it (`set_next`).
  - `push_ok` is the push lemma for the append. It uses `chain_last` (the
    tail is the chain's last page, with link 0) and `chain_snoc` (the
    chain with `i` at its end).
  - `relink_ok`: setting one pool page's link keeps every clause that
    reads no link (`map_ok`, `page_local`, `shape_ok`, `in_swept_run`,
    `lview`).
- **What a pool step changes, restated.** It may set the link of a page
  already on a list, so:
  - `pool_step` now ensures `same_but_next` for every other page, and that
    any page that changed was on a list;
  - `SweepAll.pool_next` derives that the pages from `p + 1` on are
    unchanged (none is on a list under `sweep_ready`);
  - `inv_next` and `units_kept` ask, of the pages before `p`, only their
    kinds and swept bits;
  - `SweepPools.step_entries` and `kept_live` ask only kinds;
  - in the Pulse sweep (`Impl.Pages.Sweep`), `ahead` is now about kinds.
- `sweep_ready` also asks for empty tails, which `start_sweep` gives.
- Two queries in modules this pass did not edit, `Partition.walk_tiled`
  and `SweepWf.in_unit_lt`, passed only with `--retry` once `pstate` grew.
  Each now has its arithmetic step stated (`add_mul8`; a `page_base_mono`
  call). Neither statement changed.

**The state as two pointers** (`Impl.Pages.State`).
- With the orders as the prototype's, the verified code made exactly the
  prototype's accesses, in the same order. This was checked by printing
  the first slots handed out after a sweep: same pages, same order.
- A hand-written prototype-style `pop` in the extracted C was no faster.
  The remaining cost was the state: 10 array pointers, loaded at every
  allocation, and passed in memory (80 bytes).
- So `pstate_t` is now `{ tpm; tw }`. `tw` is one word array:
  - avail, atail, the large lists, the hint and the epoch;
  - then the three tables.
- `pages_st` ties each region (`sl w o n`) to the state (`w_ok`), and
  `w_upd` shows that a write changes only its region. No other module
  changed.
- `init` fills the whole array in one loop (`w_start`).

**The slot loop out of line.**
- Inlined into the whole sweep, the slot loop ran out of registers and
  reloaded the heap's base address at every slot. That made `sweep50`
  7–12% slower than the prototype, with the same C for the loop.
- `[@@CPrologue "KRML_NOINLINE"]` on `sweep_slots` keeps it out of line.
  Custard does not translate `CNoInline`; it keeps `CPrologue` text.

**The benchmark runs each workload in its own process** (`bench.sh`,
`make bench`).
- In one process, the earlier workloads moved the later ones by up to 10%,
  and differently for the two allocators.
- The same reallocS code measured 10.0 or 11.0 ns depending on the driver
  around it.
- `bench.sh ROUNDS REPS` alternates the binaries and prints medians.

**Checked.**
- Every changed module was checked without `--retry`, with no rlimit
  raised.
- `make verify` from an empty cache in a scratch worktree: 282 checked
  files, 41 minutes, no errors. It ran with the Makefile's `--retry 3`,
  which `GC.Gen.Reachability` (not touched here) needs.
- `SlotLemmas`, `Impl.Pages.State`, `SweepStep`, `Frame` and
  `Spec.Pages.SweepPage` also pass at Z3 seeds 1 and 2, without retry.

**The C test.** `pages_test.c` has the word array, the expected lists in
the new orders, and `test_list_order`: three pages swept are listed 1, 2, 3
with tail 3; pages leave from the front, and the tail empties with the
list. 468 checks, all passing.

**Measurements** (`make bench`, 5 rounds × 15 repetitions, medians; three
runs, so a range is given).

| Workload | Prototype B2 | Verified | Difference |
|---|---|---|---|
| small allocation (ns) | 9.71–10.07 | 9.46–9.54 | −2% to −6% |
| mixed, 0.5% large (ns) | 25.1–25.6 | 15.3–15.7 | −39% |
| large only (µs) | 3.37–3.44 | 2.00–2.01 | −41% |
| sweep, 10% survive (ms) | 0.99–1.04 | 0.90–0.94 | −7% to −12% |
| sweep, 50% (ms) | 1.58–1.61 | 1.53–1.58 | −1% to −3% |
| sweep, 90% (ms) | 0.97–1.01 | 0.84–0.87 | −13% to −14% |
| realloc after sweep50, mixed heap (ns) | 10.00–10.23 | 9.37–9.94 | −2% to −8% |
| reallocS, small-only heap (ns) | 9.94–10.12 | 9.84–10.07 | 0% to −2% |

- Every workload is at or below the prototype's time.
- The machine's clock varies between sessions (§17's first table was taken
  at a lower one), so compare rows only within a table.

**For the runtime (5b).** The extracted code reads and writes heap words
through `compat.c`'s `read_u64_le` and `write_u64_le`. Here they inline
only through `-flto`. A build without LTO would pay a call per word, so 5b
must compile them inline (LTO, or a header definition).

---

## 18. The roots are greyed first; the vacuity rule and its audit (2026-11-15)

### 18.1 The gap

`gc_correct_pages` (§14) held only when there are no roots.
- Its precondition was `PA.inv I.Idle h_init st /\ mark_pre h_init gs roots`.
- In `Idle` every live object is white (`MarkPhase.live_white`).
- `mark_pre` needs every root grey or black (`Mark.root_props`), and every
  stack entry grey (`MarkInv.mark_inv`'s `stack_props`).
- So `roots` and `gs` had to be empty. `GcCorrect.idle_mark_pre_empty` now
  proves this.
- The cycle had the same gap: `Collect` asked for `mark_pre`, so the only
  collections in `reach` were the ones with no roots. `phases` too: it asked
  for `MarkInv.mark_inv g gs` in `Idle`, so `gs` was empty.
- Its vacuity check, `gc_correct_pages_hyps_not_false`, missed this. It was
  an `expect_failure` test, so Z3 failing to refute the hypotheses within
  rlimit 5 counted as success. The cycle's check, `reach_start`, used only
  the empty heap.
- Found in stage M1 of the parallel mark (`docs/pages-parallel-gc-design.md`
  §11 on `sheera/pages-parallel`).

### 18.2 The fix: a step that darkens the roots

`GC.Spec.Pages.Darken` (new, 309 lines):
- `darken h roots` greys each root in turn, as OCaml's
  `caml_darken_all_roots`. The roots are then the mark's stack.
- `roots_ok h roots`: each root is an object of `h` and not free, and
  `GP.graph_pre h roots` (with it, the roots are distinct).
- `start_pre h st roots = PA.inv I.Idle h st /\ roots_ok h roots`. It is
  `ParMark.Heap.par_pre` on `sheera/pages-parallel`, word for word.
- **`darken_ok`**: from `start_pre`, the darkened heap
  - meets `mark_ready`, which is `mark_pre` with the roots as the stack;
  - is in the allocator's marking invariant, `MP.mark_inv` and
    `PA.inv I.Marking` (each greying is `MarkPhase.mark_inv_recolour`: the
    allocator ignores live objects' colours);
  - differs from `h` only in the roots' colours (`kept`): the same walk,
    graph, blue blocks, sizes and fields.
- Density (`heap_objects_dense`, which `MarkInv.mark_inv` needs) follows
  from `Idle` by `Shape.heap_tiled` and `WalkEnd.dense_from_walk_end`
  (`idle_dense`).

`GC.Spec.MarkInv` gains `mark_inv_intro`. The pruning of 79bdaaf6 had
removed it as dead code, so nothing could establish `MarkInv.mark_inv`,
which `Corr.mark_satisfies_mark_post` assumes. Its only users are the page
modules.

`GcCorrect` (changed):
- `collection h st roots = collect (Mark.mark (D.darken h roots) roots) st`.
- `marked_of_darkened` restates the mark's `Corr.mark_post` about the
  darkened heap as one about the first heap (`Corr.mark_post_intro`): the two
  differ only in colours, and the first has no black object.
- `mark_ok` gives `GP.marked h_init hm roots` and `MP.mark_inv hm st` for
  `hm = Mark.mark (D.darken h_init roots) roots`.
- `gc_correct_gen`, the clauses and every lemma behind them are unchanged.

The statements, old and new:

| | Old (§14) | New |
|---|---|---|
| `gc_correct_pages` arguments | `h_init st gs roots` | `h_init st roots` |
| requires | `PA.inv I.Idle h_init st /\ mark_pre h_init gs roots` | `D.start_pre h_init st roots`, that is `PA.inv I.Idle h_init st /\ D.roots_ok h_init roots` |
| the collection | `collect (Mark.mark h_init gs) st` | `collection h_init st roots` = `collect (Mark.mark (D.darken h_init roots) roots) st` |
| ensures | `gc_safe_pages h_init g st' roots /\ gc_live_pages h_init g st' roots` | the same, word for word, about the same `h_init` (the heap before the roots are greyed) |
| `reach`'s `Collect` | `gs roots`, `squash (mark_pre g gs roots)`, to `collect (Mark.mark g gs) st` | `roots`, `squash (D.roots_ok g roots)`, to `collection g st roots` |
| `reach_inv` | every state of `reach` is in `Idle` | the same statement, over the larger `reach` |
| `cycle_correct` | `r: reach g st`, `mark_pre g gs roots`; ensures as above on `collect (Mark.mark g gs) st` | `r: reach g st`, `D.roots_ok g roots`; ensures the same clauses on `collection g st roots` |
| `phases` | `PA.inv I.Idle g st /\ MarkInv.mark_inv g gs`; ensures `Marking` of `g` and of `Mark.mark g gs` | `PA.inv I.Idle g st /\ D.roots_ok g roots`; ensures `Marking` of `g`, of `D.darken g roots` and of its mark, and `Idle` after `collect` |

- No clause of a conclusion is weakened.
- The old theorem was satisfiable only with `roots` and `gs` empty. There
  the new one covers it: `D.darken h [] == h` and the collection is the same.
- The new hypotheses are weaker: everything in `mark_pre` except
  `graph_pre` is now derived from `Idle`.

### 18.3 The vacuity rule

From now on, in this plan and in `docs/pages-parallel-gc-design.md`:
- **Every theorem with hypotheses about heaps has a constructive witness**:
  a concrete state, built by definitions and the theorems already proved,
  shown to satisfy all its hypotheses.
- An `expect_failure` check (failing to prove `False`) is not enough: a
  solver timeout looks the same as success. Such checks may stay, but they
  do not count.
- **Witnesses are non-trivial**: at least one root, one reachable object,
  one unreachable object, and, where the theorem concerns them, at least
  one pool page and one large run.
- **The vacuity audit runs at the end of every stage and before any PR**:
  for each theorem, name its witness, or build one.

The shared witness, **`GC.Spec.Pages.Witness`** (new, 668 lines, identical
on `sheera/pages-parallel`):
- From the empty heap of pages, through `PA.alloc I.Idle` with the
  caller's field writes:
  1. B, `small_max` fields (a large object): a new run of `kL` pages at
     `i0`; fields 0;
  2. A, one field, in the first free page, which becomes a pool page; its
     field points to B;
  3. C, one field; field 0.
- Roots `[A]`. A is a root in a pool page; B heads a run and is reachable
  through A, not a root; C is a live object that is unreachable
  (`w_graph`, through `reach_two` on the graph).
- `w_ok` sums it up: `Idle`, live roots with `graph_pre`, the
  reachability facts, the pages. `w_reach` is the state as a term of
  `reach` (`Start`, then three `Alloc`).
- It needs only `big_enough`: `pages_for (small_max + 1) + 2 <= n_pages`.
  The parameters are abstract, so every witness is stated under it.
- Each allocation is shown to succeed from `alloc_ok`'s failure clause:
  failure means `no_fit`, and a free page is kept free (`small_kinds`,
  `large_init` track the page kinds).

**`GC.Spec.Pages.Vacuity`** (new, 341 lines) derives the witnesses from `W`,
by the theorems themselves: `W`; `hd`, `W` with its roots greyed; `hm`, the
mark of `hd` (A and B black, C not); the sweep's start (A's pool page and
B's run unswept); the collection's result.

**`GC.Spec.Pages.SweepingStart`** (new, 109 lines): `start_sweep` keeps
`pages_ok` (`start_keeps_ok`), so the `Sweeping` invariant holds where the
sweep starts, with every page that is not free unswept
(`sweeping_at_start`). Before, no state with an unswept page was known to
satisfy `Sweeping`.

### 18.4 The audit

`W` means the witness above. "Empty heap" means `Init.init_heap`: no
object, no root.

| Theorem | Witness before | Witness now | Problem found |
|---|---|---|---|
| `GcCorrect.gc_correct_pages` | `expect_failure` only | `Vacuity.gc_correct_pages_witness` (`W`) | **Hypotheses contradictory for any root** (§18.1). Fixed. |
| `GcCorrect.reach_inv`, `cycle_correct` (the cycle) | `reach_start` (empty heap) | `Vacuity.cycle_witness`: `W` as a term of `reach`, and a `Collect` from it with roots `[A]`; `cycle_witness_ok` | **`Collect` only without roots** (§18.1). Fixed. |
| `GcCorrect.phases` | none | `gc_correct_pages_witness` (same hypotheses) | **Stack empty in `Idle`** (§18.1). Restated. |
| `Darken.darken_ok` (new) | — | `gc_correct_pages_witness` | — |
| `GcCorrect.idle_mark_pre_empty` (new) | — | `idle_mark_pre_witness`: `W` with no roots, the only kind it allows | states the gap |
| `GcCorrect.gc_correct_gen` | `expect_failure` | `gc_correct_gen_witness`: `W` and `hm` | — |
| `MarkSteps.mark_keeps_inv` | `expect_failure` | `mark_keeps_inv_witness`: `hd`, stack `[A]`, A grey | — |
| `start_ready` (`Allocator`, `StartSweep`) | `expect_failure` | `start_ready_witness`: `hm` | — |
| `collection_cycle` | `init_cycle` (empty heap) and `expect_failure` | `start_ready_witness`: `hm`, `mark_done` | — |
| `SweepWf.sweep_all_wf`, `Allocator.sweep_all_correct` | `SweepVacuity.sweep_all_ready` (empty heap) and `expect_failure` | `sweep_witness`: `hm` and its sweep's start | — |
| `Allocator.sweep_start`, `sweep_step_inv`, `sweep_end` | `sweep_all_ready` (empty heap) | `sweep_witness`: `sweep_inv` at page 0 and at `n_pages` | — |
| `Survive.swept` (the setting of `black_survives` and the rest) | `expect_failure` | `sweep_witness` | — |
| The interface's phases: `inv` of `Idle`, `Marking`, `Sweeping` (`pages_allocator_ok`, `alloc_no_fit`) | `init_inv` (empty heap) and `expect_failure` | `interface_witness`: `Idle` `W`; `Marking` `hd` and `hm`; `Sweeping` `hm`. `sweeping_witness`: `Sweeping` with A's pool page and B's run unswept | **`Sweeping` had no witness with an unswept page**. Now `SweepingStart`. |
| `alloc_idle`, `Alloc.alloc_correct` | `init_alloc_pre`, `init_alloc_succeeds`, `init_alloc_large_succeeds` (empty heap) | `W` is built by three successful allocations; `interface_witness` | — |
| `alloc_col_correct` (`Allocator`, `AllocPhase`) | `init_mc`, `init_black` (empty heap) and `expect_failure` | `interface_witness`: `pages_ok_mc` of `hm`, A and B black | — |
| `MarkPhase.mark_inv_recolour` (the `phase_ok` clause) | none | `interface_witness`: `hd`, A live | — |
| `Allocator.mark_exact`, `mark_exact_done` | `expect_failure` | `mark_exact_witness`: B black, C not | — |
| `Partition.partitioned` | `expect_failure` | `partitioned_witness`: the collection of `W` | — |
| `sweep_page_correct`, `sweep_run_correct` (`Th.sweep_page_meets`, `sweep_run_meets`) | `SweepVacuity`: a pool page and a one-page run, each with a black block and with none (page-level, no roots) | unchanged | — |
| The Pulse allocator and sweep (`GC.Impl.Pages`: `alloc_white`, `alloc`, `sweep`, `sweep_all`) | `sweep_pre_holds` (empty heap) | `pulse_pre_witness`: `pages_ok` of `W`, `pages_ok_mc` of `hm` (so `heads_ready`), `map_ok` before and at the sweep's start | — |
| The Pulse loop lemmas (`Impl.Pages.Vacuity`: `emit_plain`, `emit_listed`, `fin_dead`, `fin_live`, `run_pages`, `pass2_head`, `pass2_cont`, `pass2_done`, `fit_found`) | loop starts (`emit_ok_start`, `map_start`, `fit_start`) and `expect_failure` | **not built**: they need states in the middle of a loop | open |
| `SweepOrder.sweep_commute` | none | `sweep_commute_witness`: A's pool page and B's run, two units of the sweep's start | — |

The parallel branch's theorems are audited in
`docs/pages-parallel-gc-design.md` §11.8 on `sheera/pages-parallel`.

**Checked.**
- Every new and changed module (`MarkInv`, `Darken`, `GcCorrect`,
  `Witness`, `SweepingStart`, `Vacuity`) verifies without `--retry` at Z3
  seeds 0, 1 and 2. No local rlimit is above 40; the most any query uses is
  17.3 (`Witness.w_succ`, under rlimit 40); every other uses at most 8.6.
- Check times (seed 0): `Witness` 39 s, `Vacuity` 20 s, `GcCorrect` 10 s,
  the others under 5 s.
- `make verify` from an empty cache in a scratch worktree: 286 checked
  files, no errors. On the first run `GC.Spec.Coalesce.Correct`, which
  depends on none of these changes, timed out while the machine was also
  running the seed checks; the rerun passed it.
- No admits, no assumptions.

---

## 19. Rebased onto main's incremental collector (2026-11-16)

`sheera/pages-allocator` now sits on `origin/main` `5623c7f6` (PR #52, akhil's
incremental mark and sweep), no longer on #46. The rebase is textual. The
commits keep their content, and one "port to main" commit at the end makes the
branch build. Commits between the first and the port do not build on their
own. The impact assessment is `docs/main-merge-impact.md`.

**The first commit carries #46's size-class list state.** The large-object
area uses `GC.Spec.SizeClass`, `GC.Spec.FreeLists` and `GC.Spec.FreeLists.Push`
from `sheera/size-lists`. #46's sweep and collect modules are built on modules
main deleted, so only these three come over. They are unchanged except that
`fls_push` states its precondition with main's `blocks_fit`, which has the
same body as the old `well_formed_heap_part1`. `FreeLists.Push` is a root
module.

**Rebase conflicts.**
- Only `Makefile` conflicted (the `ROOT_MODULES` lists of both sides), and
  only on the first page commit. Both sides were kept. Every other commit
  applied with a 3-way merge.
- Main had already added `MarkInv.mark_inv_intro`, word for word as stage
  4 did. The merge kept both declarations. The port drops ours.

**What the port changes.** No page statement changes meaning.
`Pages.Theorems`, `Pages.Allocator.fsti` and `AllocIface` are byte-identical
to before the rebase.
- **`GC.Spec.WalkEnd` → `GC.Spec.Walk`.** Main's `Walk.walk_end` is the same
  function as the old one; its guard is `can_step`, the guard of `objects`.
  A new module, `GC.Spec.Pages.WalkEnd`, restates the five old lemmas the
  page proofs use, about `Walk.walk_end`:
  - `walk_end_step`, `walk_head`, `walk_end_empty` and
    `walk_nonempty_of_walk_end`, with the old proofs;
  - `dense_from_walk_end`, from main's `dense_of_reaches_end`.

  The six modules that used `WalkEnd` (`Darken`, `Inv`, `Partition`,
  `Shape`, `Vacuity`, `Walk`) now alias it instead.
- **Well-formedness.** Main restated `well_formed_heap` as
  `well_formed_heap_with free_stw`, whose parts are `blocks_fit`,
  `pointers_lead_to_non_free`, `interior_pointers_valid` and
  `no_infix_block`. It also retired `GC.Spec.Mark.no_pointer_to_blue` (L10),
  which the second part now contains. A new module, `GC.Spec.Pages.Wf`,
  defines the old parts and the old `no_pointer_to_blue` word for word, and
  proves
  `wfh_old_parts`: `well_formed_heap g <==> part1 ∧ part2 ∧ part3 ∧ part4 ∧
  no_pointer_to_blue g`.
  It also restates the old helpers the page proofs use:
  `fields_constrained`, `well_formed_heap_part2_3_from_resolved_field_closure`,
  `wf_field_target_in_objects`, `wf_field_target_infix_wf`,
  `no_pointer_to_blue_intro_from_fields` and `mark_post_elim_no_pointer_to_blue`.
  - In 13 page modules the change is qualifiers only:
    `Mark.no_pointer_to_blue` → `Wf.no_pointer_to_blue`, and
    `reveal_opaque (`%well_formed_heap)` → `Wf.wfh_old_parts ()`.
  - L10 stays in `pages_ok` with its old meaning. By `wfh_old_parts` it is now
    implied by `well_formed_heap`, but removing it would change `pages_ok`'s
    text, and nothing needs that.
- **Three proofs needed one more fact each.** Main's `well_formed_heap`
  contains `no_pointer_to_blue`, and main's `mark_post` gained a clause:
  - `Alloc.init_alloc_pre` proves `well_formed_heap` of the empty heap from
    the old parts. It now also calls `Init.init_no_pointer_to_blue`.
  - `SweepWf.wf_after` proves it after the sweep. It now also calls
    `SweepAll.no_blue_after`, which was already proved for L10.
  - `GcCorrect.marked_of_darkened` builds `mark_post` with
    `Corr.mark_post_intro`. Main's version also asks that marking keeps
    every block's blueness. The proof now calls `Corr.mark_post_elim_blue`
    on the mark from the darkened heap, and `Darken.same` gives the step
    before it.
- **Comments:** `Survive` names `FusedSweep.Lossless` as the source of its
  `in_extent`/`blue_covered`, which are word for word main's.

**Checked.**
- `make verify`: 372 checked files, no errors, with the Makefile's default
  `--retry 3` as CI runs it.
  - It ran in a scratch worktree whose cache was main's own clean build at
    `5623c7f6` (295 files, built from an empty cache in another scratch
    worktree).
  - Without `--retry`, main's own `GC.Gen.Reachability` (unchanged since
    `1ecb0004`) fails a query at line 588 on this machine. That is main's,
    not ours.
- Every new and changed module verifies without `--retry` at Z3 seeds 0, 1
  and 2: 22 modules, 66 checks. They are `Pages.Wf`, `Pages.WalkEnd`, the
  17 page modules the port touches, `SizeClass`, `FreeLists` and
  `FreeLists.Push`. The slowest is `Pages.Large`, at about 80 s.
- `pages-c`: `make extract` from that cache gives C byte-identical to the
  committed files, and `make test` passes all 468 checks.
- No admits, no assumptions.
- `pages-c/bench` (`bench.sh 5 7`), extracted from the clean build of
  `ef186b67`, median of 5 rounds (verified against the prototype):
  - small −3.9%, mixed −38.8%, large −41.0%;
  - sweep10 −7.3%, sweep50 −4.5%, sweep90 −9.4%;
  - realloc −0.6%, reallocS −2.9%.

  Every workload is at or below the prototype, so the ≤ 5% rule holds.

---

## 20. Design: the page allocator in main's incremental cycle (2026-11-16)

Design only. Nothing here is built. It replaces §7's sketch and stage-4
item 1, now that the incremental collector is on main. References to main
are at `5623c7f6`.

### 20.1 What main's cycle needs from an allocator

**The allocator is hard-wired.** Main's cycle names its allocator directly:
- `GC.Gen.MarkPhase.Cycle.marking` has an `Alloc` step on
  `AC.alloc_phase g fp Marking`.
- `GC.Gen.SweepPhase.Cycle.cycle` has an `Alloc` step on
  `AC.alloc_phase g fp (Sweeping c)`.
- Promotion calls `AP.alloc_at ph`, which is `AC.alloc_phase g fp ph`
  (`GC.Gen.Promote.promote_object`).
- The implementation keeps `fp_ref` and `phase_ref` in `gen_heap_t`. Its only
  allocator calls are `promote_one`, and `verified_allocate` in `alloc_gen.c`.

**The proofs use five facts about an allocation:**
1. **The colour** (`Phase.allocation_color`):
   - Idle: white.
   - Marking: black.
   - `Sweeping c`: black if the header is at or above `c`, white below it.
2. **Only the new object comes into use, carved from a free block.** The
   facts are `Mut.alloc_in_use`, `MarkPhase.Alloc.alloc_in_use` and
   `allocations_not_free`.
3. **Every other block is kept.** This is `keeps_blocks` and `Mut.alloc_keeps`.
4. **The walk is kept.** The facts are `MW.alloc_reaches` and `Mut.alloc_walk_end`.
5. **The allocator's own invariant is kept.** This is `fl_ascending` with `alloc_ok`.
   - In the mark phase, `fl_ascending` is the only place the free list
     appears (`marking_alloc`).
   - In the sweep phase, the free list sits inside the collector's
     invariant: `sweep_inv_incremental` includes `fl_ascending`.

**No allocator facts appear in the mark side.** The mark invariant
(`marking_inv`), the barrier, the scan position and the mark slice mention
no allocator.

### 20.2 The colour rule

**Today's rule and main's rule.**
- `AllocIface.new_colour` is a function of the phase only:
  - Marking: black.
  - Idle and Sweeping: white.
- Main's rule depends on the address while sweeping.

**The common rule.**

    colour_at a s ph x = Black  if ph = Marking
                         Black  if ph = Sweeping and a.unswept s (hd_address x)
                         White  otherwise

`alloc_post`'s colour clause becomes `color_of_object x g' == colour_at a s ph x`.

**The record's one field `unswept` has two jobs today. It splits into two:**
- `unswept s b`: memory the sweep has yet to visit. This decides the colour.
- `pending s b`: memory the allocator must not change, which is the sweep's
  remaining work. This is the frame clause of `alloc_post`, unchanged in form.

| | `unswept s b` | `pending s b` |
|---|---|---|
| Main's first fit | `b >= c` | the words of `pending_free c` blocks (white, at or above `c`) |
| Pages | `b` is in an unswept page | the same |

Main's allocator does allocate above the cursor. It takes blue cells there,
never pending ones, which is why main needs two predicates.

**Check that no page theorem's conclusion weakens.** The rule may be applied
only if this holds.
- The page allocator never allocates into an unswept page.
  `AllocPhase.new_hdr_swept` proves this of the header, and stage 2's
  `fields_swept` proves it of the fields.
- So for pages `colour_at` is `new_colour ph` at every allocation. The page
  `alloc` (`alloc_col (new_colour ph)`) does not change.
- `alloc_correct`, `alloc_col_correct`, `alloc_idle`, `alloc_no_fit`,
  `Pages.Theorems` and `Pages.Allocator.fsti` are untouched.
- `pages_allocator_ok` is re-proved against the new `alloc_post`. A lemma
  `alloc_post_new_old` shows that, for pages, the new `alloc_post` implies the
  old one: `colour_at = new_colour` there by `new_hdr_swept`, and the frame
  clause is the same predicate.
- So every page conclusion is kept as it is. If a page theorem had to change
  (for example, if pages allocated into unswept pages), the rule would not
  be applied, and pages would keep `new_colour` as its own instance's colour.

**One more generalisation** is needed by 20.4: `fields_written`'s
`field_ok` becomes `field_ok_with free`, where `free` is the collector's
`free_def` (20.3). `field_ok` is the instance at `free_stw`.

### 20.3 Page-by-page sweeping and main's Sweeping phase

**The mismatch.**
- Main's sweep is one address-ordered cursor. `Sweeping of U64.t` holds the
  cursor, and free means `free_incremental c` (blue, or white at or above
  `c`).
- `SweepPhase.Slice.phase_slice` advances the cursor. `state_at` derives the
  caches from it.
- The page sweep has no such order:
  - Its unit is a page or a run, and units commute (`sweep_commute`).
  - Plan §7 item 3 sweeps on allocation, as OCaml 5's `pool_find` does.
    That sweeps a page of the requested class out of address order.
  - Progress is a set of swept pages, implemented as a per-page epoch.

**Recommended: make the phase's payload the sweeper's own state.** A new
record `GC.Spec.SweeperIface.sweeper` has:
- `sst: Type0`, the sweep's progress;
- `unswept: sst -> hp_addr -> bool`, shared with the allocator's colour rule;
- `free_of: sst -> free_def`, with `free_def_ok (free_of s)` and
  `allocations_not_free` for the allocator;
- `start: heap -> sst`, `slice: sst -> heap -> budget -> heap & sst`, `done: sst -> bool`;
- `sweep_inv: heap -> a.ast -> sst -> prop`, and the facts main's
  `sweep_slice_phase` gives:
  - in-use objects stay in use, as the same block;
  - pending work strictly shrinks;
  - when done, `well_formed_heap`, nothing pending, and only white or blue
    blocks.

The phase becomes `Idle | Marking | Sweeping of sst`.

**Main's instance:**
- `sst` is the cursor `c`; `unswept s b = b >= c`;
- `free_of c = free_incremental c`;
- `slice = phase_slice`; `sweep_inv = sweep_inv_incremental`.
- The lemmas already exist: `sweep_slice_phase`, `sweep_inv_incremental_end`,
  `minor_keeps_sweep_phase` and `free_incremental_allocations_not_free`.

**The page instance:**
- `sst` is a swept set, `page -> bool` in the spec and an epoch in the
  implementation (§17).
- `unswept s b` holds when `page_of b` is not swept.
- `free_of s g x = is_blue x g || (is_white x g && not (s (page_of x)))`.
  - This is a `free_def`: for a fixed `s` it reads only `x`'s header and
    address, so `free_def_ok` holds.
- `slice` sweeps unswept units in page order up to the budget, each with
  `sweep_page_correct`/`sweep_run_correct`.
- **Sweeping on allocation** is a collector step, `Slice_unit p`, taken just
  before the `Alloc` step in the run. It is not an effect inside the
  allocator. The implementation's fused `pool_find` is proved equal to
  `Slice_unit` followed by `alloc`. So `alloc_post` never mentions `sst`.

**Alternative, not recommended:** keep main's `Sweeping of U64.t` and sweep
pages in address order behind a page-aligned cursor. Main's types then stay
as they are, apart from `free_def`. But this forbids sweeping on allocation,
which is what keeps the page allocator's pauses short (results §9.9).

### 20.4 Allocation during an incremental page sweep: the proof

**The mid-sweep invariant** is plan §7.1's,
`pages_ok_sw g st s`:
- **Swept pages:** `pages_ok`'s L4, L5 and L7 (exact lists, slots and runs).
  Colours are white or blue, as after `sweep_page`. The lists hold cells of
  swept pages only.
- **Unswept pages:** shape L3 and L6. Colours are black, white or blue, never grey.
- **The heap:** `well_formed_heap_with (free_of s) g`, the page map
  (`map_ok`) and `heap_partitioned`.

**The obstacle.** `alloc_col_correct` assumes `pages_ok_mc`, which includes
`well_formed_heap`, that is, `free_stw`. That fails mid-sweep: a dead white
object in an unswept page may point to a block already freed in a swept page.

**The plan.**
1. **Weaken the precondition, which strengthens the theorem.** Find
   `alloc_pre g st`, the parts of `pages_ok_mc` that the allocation proofs
   actually read. Expected:
   - the page map;
   - the swept pages' lists and shapes;
   - the tiling;
   - `blocks_fit` and `no_infix_block`. These two parts of
     well-formedness do not depend on `free`, so they hold mid-sweep.

   Restate `alloc_col_correct` from `alloc_pre`. The old statement is the
   instance `pages_ok_mc ⇒ alloc_pre`, so nothing weakens. Then prove
   `pages_ok_sw ⇒ alloc_pre`.
2. **The invariant after allocation and field writes.**
   - **Swept pages:** from `alloc_ok_col`'s clauses, as in stage 4.
   - **Unswept pages:** from `unswept_unchanged` and `Pages.Frame`.
   - **`well_formed_heap_with (free_of s)`:** the new object is white in a
     swept page, so it is in use. Its fields are written with
     `field_ok_with (free_of s)` values. Every other block is kept
     (`others_unchanged`).

     This follows main's sweep-phase lemmas one for one, and the page
     analogues get the same names: `alloc_sweep_phase`, `fresh_write`,
     `fresh_close` and `program_write`.
3. **The five facts of 20.1:**
   - **Colour:** white, by `new_hdr_swept` and the 20.2 rule.
   - **In use:** `in_use (free_of s) g' y == in_use g y || y = obj`. The
     object was carved from blue memory of a swept page, and others are
     unchanged.
   - **Others kept:** `others_unchanged`.
   - **Walk kept:** new lemma `alloc_reaches_pages`. A pool allocation
     rewrites a slot header in place, at the same size. A large carve
     splits a blue block into two that tile it. In both cases `W.reaches g
     zero e` implies `W.reaches g' zero e` (`W.walk_write` and
     `W.walk_merge` read backwards). For the large carve this is the hardest
     new lemma.
   - **Not pending:** the new object is in a swept page.
4. **A minor collection mid-sweep** promotes through `alloc Sweeping`.
   `allocations_not_free (free_of s)` holds by 3. `CheneyGeneric` gives the
   rest, as `minor_keeps_sweep_phase` does for main.
5. **Vacuity.** `SweepingStart` already gives a `Sweeping` state with
   unswept pages.
   - Add a run like main's `GC.SPOT.SweepPhaseCycleAlloc`:
     start the sweep → `Slice_unit` → `Alloc` → `Write` → finish.
   - Add one with a minor collection, like `SweepPhaseFreedByEnd`.

### 20.5 Generalising main's cycle proofs over `AllocIface`

**Two ways to do it.**
- **(A) Edit akhil's modules to take the records.** There is one proof, but
  it rewrites the signatures and proofs of `MarkPhase.Cycle`,
  `SweepPhase.Cycle`, `Gen.Cycle`, `MarkPhase.Alloc`,
  `SweepPhase.Mutator`/`Completeness`, `Promote`, the Cheney simulation and
  the two minor-collection modules.
- **(B, recommended) Add generic modules beside his.** The new modules are
  `GC.Gen.Cycle.Generic`, `.MarkRun` and `.SweepRun`. They state the run
  types and the generic cycle theorems over `allocator` and `sweeper`:
  - `cycle_account`, `cycle_complete`, `cycle_frees_unreachable` and
    `cycle_survives` are generic.
  - `cycle_lossless` and `cycle_covered` describe the fused sweep's extents,
    so they stay instance theorems. For pages the analogues are
    `Survive`'s `dead_covered` and `live_uncovered`.

  The generic proofs are adapted from his, with the allocator facts
  replaced by the interface's clauses.

**Instance 1: main's first fit with the fused sweep.**
- Prove `alloc_phase` meets the new `alloc_post`, with the walk clause. The
  proofs come from `Allocator.Cursor`, `Allocator.Phase`, `Allocator.Exact`,
  `SweepPhase.Mutator.alloc_*` and `MarkPhase.Walk.alloc_reaches`, all
  already proved.
- The sweeper is the fused sweep phase.
- **Evidence the interface is not vacuous:**
  - main's own `GC.Gen.Cycle` theorems are re-derived from the generic ones
    at instance 1, with the same statements;
  - main's SPOT runs (`MarkPhaseCycleAlloc`, `SweepPhaseCycleAlloc`,
    `SweepPhaseFreedByEnd`) are rebuilt through the interface.
- Once this is stable, akhil may choose to replace his concrete runs with
  the instance. That is his call.

**Instance 2: the page allocator** with the page sweeper (20.3 and 20.4).

**Which parts touch akhil's proofs:**

| Part | Option A | Option B (recommended) |
|---|---|---|
| `MarkPhase.Cycle`, `SweepPhase.Cycle`, `Gen.Cycle` (run types, cycle theorems) | rewritten | **used, not edited**: instance 1's theorems are re-derived from them |
| `MarkPhase.Alloc.marking_alloc`, `Completeness.account_alloc`, `Gen.MarkPhase.Walk.alloc_reaches`, `SweepPhase.Mutator.alloc_*` | restated over the record | **used** to prove instance 1's `alloc_post` |
| `Promote`, `CheneyGeneric`, `MarkPhase.Minor`, `SweepPhase.Minor` | `alloc_at ph` → `a.alloc ph` throughout the Cheney simulation | **used** for instance 1. For pages, promotion needs the same Cheney facts from the record (header written, fields not touched, other blocks kept). Either `Promote` takes the record (an edit to his module), or a generic copy of the promotion lemmas is made. **This is the largest piece; decide it with akhil.** |
| `marking_inv`, barrier, scan position, mark slice, `FusedSweep`, `Walk` | untouched | untouched |
| Impl: `gen_heap_t.fp_ref`/`phase_ref`, `promote_one`'s `allocate`, `alloc_gen.c`'s `verified_allocate` | edited | **edited (unavoidable)**: see below |

**The implementation, under either option.**
- Add an interface `GC.Impl.AllocIface.fsti` with an abstract allocator
  state, its slprop and `allocate`, related to `alloc_post`.
- `GC.Impl.Allocator` (main) and `GC.Impl.Pages` (pages) each implement it.
- The build chooses one, as two extraction bundles. There is no
  indirection at run time, as the ≤ 5% rule requires.
- `gen_heap_t` holds the interface's state in place of `fp_ref`/`phase_ref`.
  This touches main's implementation, not akhil's spec proofs.

**Order of work, smallest risk first:**
1. `AllocIface` v2: `colour_at`, `pending`, `field_ok_with` and the walk
   clause. Re-prove `pages_allocator_ok`, and add `alloc_post_new_old`.
2. Instance 1's `alloc_post`, from main's lemmas.
3. `SweeperIface` and the generic sweep run, with both instances. Main's
   SPOT runs are the witnesses.
4. The page mid-sweep invariant and allocation during the sweep (20.4).
5. The generic mark run.
6. Promotion and the minor collection, after deciding the Promote question
   with akhil.
7. The implementation interface, then 5b (`gen_gc` with the page state).

---

## 21. §20.2 and §20.4 as built (2026-11-17)

Built: the colour rule (§20.2) and allocation during an incremental page
sweep (§20.4), in the page modules and the allocator interface only. Not
built: the sweeper record (§20.3), the generic cycle modules (§20.5), and
the minor collection mid-sweep (§20.4 step 4), which needs `Promote`. No
module of akhil's changed. All modules are in `mark-and-sweep/spec/`.

### 21.1 `AllocIface` v2: the colour rule

**The record** has a fifth field. `unswept` now decides the colour, and
`pending` is the frame:
- `unswept s b`: memory the sweep has yet to visit;
- `pending s b`: memory the allocator must not change.

**The colour** is `colour_at a s ph x`:
- `Marking`: black;
- `Sweeping`: black if `a.unswept s (hd_address x)`, white otherwise;
- `Idle`: white.

`alloc_post`'s colour clause is `color_of_object x g' == colour_at a s ph x`,
with `s` the state before the allocation. Its frame clause is on `pending`.

**What the caller may store** depends on what the collector counts as free:
- `field_ok_with free` and `fields_written_with free` generalise
  `field_ok` and `fields_written`. `field_ok_stw` and `fields_written_stw`
  show the old ones are the instances at `free_stw`.
- `alloc_post_with free` is the guarantee. `alloc_post` is
  `alloc_post_with free_stw`.
- `allocator_ok_with a free` takes `free` per phase and state.
  `allocator_ok a` is the instance at `free_stw` in every phase
  (`allocator_ok_stw`).
- The sweeper's `free_of` (§20.3) would supply `free`; it is a parameter
  until the sweeper record exists.

**The first version is kept as `alloc_post_v1`** (colour `new_colour ph`,
frame on `unswept`, `fields_written`), to show nothing is lost.

**`Pages.Allocator`**:
- `pages_allocator` sets `pending = unswept`.
- `pages_allocator_ok` is re-proved against the new `alloc_post`. The new
  object's header is in a swept page (`new_swept`, from
  `AllocPhase.new_hdr_swept` through the whitened heap), so `colour_at` is
  `new_colour ph` (`colour_new`).
- **`alloc_post_new_old`** (new): for pages, from the phase's invariant, the
  new `alloc_post` implies `alloc_post_v1`.

**No page conclusion weakens:**

| Statement | Change |
|---|---|
| `Pages.Theorems` | byte-identical |
| `alloc_correct`, `alloc_col_correct`, `alloc_idle`, `alloc_no_fit` | unchanged statements and proofs |
| `pages_allocator_ok` | same text; it now means the v2 `alloc_post`, and with `alloc_post_new_old` it gives v1 too |
| `pages_allocator` | one more field, `pending = unswept` |
| `inv`, `phase_ok`, the sweep and contract lemmas of `Pages.Allocator.fsti` | unchanged |

The modules that use the interface (`Darken`, `GcCorrect`, `MarkSteps`,
`SweepingStart`, `Vacuity`, `Witness`) verify unchanged.

### 21.2 The mid-sweep invariant (`MidSweep`)

- **`free_sw pm g x`**: `x` is blue, or white with its header in a page
  unswept in `pm` (`unswept_at`, from `Graft.uw`). It is main's
  `free_incremental c` with "at or above the cursor" read as "unswept". The
  swept set is the page map's own `swept` bits; `free_sw_ok` proves
  `free_def_ok`.
- **`pages_ok_sw g st`** (sealed; `pages_ok_sw_intro`, `pages_ok_sw_elim`):
  - `Scrub.core g st`: `pages_ok` without L10. That is the shapes of every
    page (L1–L3, L6), the free-slot lists, colours and runs of swept pages
    (L4, L5, L7), and the lists (L8, L9), which hold swept pages and blocks
    only;
  - `no_grey_unswept`: no grey block in an unswept pool page or run;
  - `well_formed_heap_with (free_sw st.pm) g`.
- With every page swept it is the `Idle` invariant (`MidSweepStep.sw_end`).
- `map_ok` and the tiling are in `core`. `heap_partitioned` is not in it;
  `Partition` is not needed by any proof here.

### 21.3 Allocation during the sweep (`MidSweepAlloc`)

**The obstacle** (§20.4) is unchanged: a dead white object of an unswept
page may point to a block a swept page has freed, so `well_formed_heap`
and L10 fail, and `alloc_correct` does not apply.

**The proof is not plan step 1** (restating the allocator's proofs from a
weaker precondition). The per-path proofs carry `well_formed_heap` through
every intermediate step (`Replace.replace_ok`), so that would rewrite
`Pool`, `Large`, `NewRun`, `Replace`, `Fill` and `Recolour`. Instead the
allocator runs on a surrogate heap:
1. **`Scrub`**: `scrub g zs` clears the fields of the objects `zs`, the dead
   objects of unswept pages (`MidSweep.dead_list`). The walk and every
   header are kept, and `core` holds of the scrubbed heap exactly when it
   holds of `g` (`core_fill_objs`, by `Fill`'s lemmas, one object at a
   time). The scrubbed fields hold no pointer (`scrubbed_no_pointer`).
2. **`MidSweep.surrogate`**: the scrubbed heap satisfies `pages_ok` and
   `well_formed_heap`. The blocks in use mid-sweep are those not blue and
   not dead, so main's `SweepPhase.Intrinsic.wf_transport` carries
   well-formedness to the surrogate with the dead objects counted free; the
   dead objects then hold no pointer. The surrogate agrees with `g` off the
   unswept pages, since the dead objects' blocks lie in unswept pages
   (`block_uw`).
3. **`Graft`**: the allocator does not read unswept pages. `alloc_graft`:
   allocating in `graft gk d pm` (`gk` with the unswept words of `d`) gives
   the same state and object as in `gk`, and the result grafted. The proof
   follows `Recolour` path by path, with "not in an unswept page"
   (`pop_out`, `free_page_out`, `cell_out`, `free_run_out`) where
   `Recolour` has "not a painted header". `alloc_agree` instantiates it.
4. **`MidSweep.alloc_relate`**: the heap allocated from `g` is the
   surrogate's, with the dead fields put back (`Scrub.fill_objs`, the
   general form of the scrub). The objects and headers are those of the
   surrogate's heap.
5. **The caller's writes** (`after_*`): scrubbing the caller's heap gives a
   heap the surrogate's caller could have written (`after_written`). So
   `alloc_ok` gives it `pages_ok` and `well_formed_heap`, which carry back to
   `core` and `no_infix_block`. The pointer clauses follow from the blocks
   in use being those of `g` and the new object (6), by `wf_transport`
   with the new object counted free, then its fields (`wf_close`).
6. **`NewOnly`**: an allocation brings only the new object into use.
   **`alloc_new_only`**, from `pages_ok` and `well_formed_heap`: every block
   of the allocator's heap that is not free, other than the new object, was
   a block that was not free. `alloc_correct` has only the other half
   (`others_unchanged`). The proof uses the stretches each path replaces
   (`Replace.replaces`) and their layouts (`Pool.fill_blocks`,
   `PoolInit.pool_init_free`, `Large.carve_layout`, `Large.link_replaces`,
   `NewRun.run_layout`), on the cleared allocator, then `Blocks.clears`.

**`alloc_sw_ok`**, from `pages_ok_sw g st`, for the `Sweeping` allocator
`PA.alloc I.Sweeping` (`alloc_col White`, equal here to `Alloc.alloc` by
`sweeping_alloc`):
- every page keeps its swept bit (`same_swept`, by `alloc_same`);
- on failure, nothing changes and `no_fit` holds;
- on success, the new object `x` is an object of the heap, of wosize `wz`,
  white, not in an unswept page, and was not in use;
- **`in_use (free_sw st'.pm) g' y == (in_use (free_sw st.pm) g y || y = x)`**;
- for every `g''` with `fields_written_with (free_sw st.pm) g' g'' x`,
  `pages_ok_sw g'' st'` and the walk of `g''` reaches the end of the heap;
- `others_unchanged g g'` and `unswept_unchanged g g' st st'`.

**Main's five facts (§20.1):**

| Fact | Where |
|---|---|
| 1. The colour | `colour_at`: white, the header not in an unswept page (`alloc_sw_ok`, `MidSweepAlloc.sweeping_post`) |
| 2. Only the new object comes into use | the `in_use` equation of `alloc_sw_ok` (`NewOnly.alloc_new_only`, `use_eq`) |
| 3. Every other block is kept | `others_unchanged g g'`, header and fields, for every block not blue (more than `keeps_blocks (free_sw pm)`) |
| 4. The walk | `WalkEnd.walk_end g'' zero_addr + 8 >= heap_size` (main's `heap_objects_dense` form); see 21.6 |
| 5. The invariant | `pages_ok_sw g'' st'` |
| Not pending | `unswept_unchanged`; the new object's header and fields are in swept pages (`new_out`) |

**`pages_allocator_sw`** (`MidSweepAlloc`) is the page allocator with
`pages_ok_sw` as its `Sweeping` invariant (`inv_sw`), and `PA.inv`
otherwise. **`pages_allocator_sw_ok`**:
`allocator_ok_with pages_allocator_sw free_ph /\ phase_ok pages_allocator_sw`.
`free_ph` is `free_sw st.pm` while sweeping and `free_stw` otherwise.

### 21.4 Sweeping further pages (`MidSweepStep`, `MidSweepRun`)

- **`step_sw`**: from `pages_ok_sw`, one `SweepAll.step` keeps it, unsweeps
  nothing, and sweeps its unit. The kinds and swept bits outside the unit
  are kept.
  - The page invariant and the lists come from `SweepStep.pool_step` and
    `run_step`. They are local and need only the unit as the mark left it.
  - No grey position in a marked pool page (`pool_no_grey`, by
    `SweepTags.pool_pos3`). Other pages: `no_grey_frame`.
  - Well-formedness: the blocks in use are the same before and after the
    step. The survivors were black, and are white in a swept page; the rest
    of the unit was free mid-sweep and is free. Block for block, by
    `SweepUnits.unit_ok` (`step_use`, `step_block`), with no infix block by
    `SweepTags.blue_ok` (`step_infix`). Then `wf_transport` (`step_wf`).
- **`sw_start`**: the sweep's start (`sweep_ready`, `mark_done`) is in
  `pages_ok_sw`. A block in use there is black (`start_unswept`), and the
  mark's tri-colour invariant gives its targets.
- **`sw_end`**: `pages_ok_sw` with every page swept is the `Idle`
  invariant.
- **`sweep_rest`**: from any `pages_ok_sw` state, `SweepAll.sweep_all`,
  whose steps skip swept units, ends in the `Idle` invariant
  (`sweep_from_sw`).
- **`MidSweepRun.sw_run`**: start, then allocations (`SwAlloc`, through the
  interface in `Sweeping`, with the caller's writes) and sweep steps
  (`SwStep`) in any order. **`sw_run_inv`**: every state is in
  `pages_ok_sw`. **`sw_run_ends`**: from every state, the rest of the sweep
  ends in `Idle`.

### 21.5 Vacuity (`MidSweepVacuity`)

The witness is a run of `sw_run` from the sweep's start of `W`'s mark
(`Vacuity.hm`, `Vacuity.s_sw`), where every page that is not free is
unswept:
0. **Start** (`start_witness`): `pages_ok_sw`. C is a dead object in an
   unswept pool page of A's class (`c_page`, `c_uw`): it is an object of the
   heap and not in use. B is in use. `V.nontrivial` holds.
1. **C's page swept** (`step1_witness`): that page is swept, and it keeps a
   free slot or became a free page (`sweep_frees`). B's run is still
   unswept.
2. **An allocation** (`alloc_witness`), with C's page swept and B's run
   unswept: it succeeds, because `no_fit` would contradict 1. The new object
   is white, in a swept page, and in use; it was not in use before. The
   caller clears its field (`zeros_written`), and the heap is in
   `pages_ok_sw` with B's run still unswept.
3. **B's run swept** (`sw_witness_ok`).
4. **The rest**: `sweep_all` gives `pages_ok_sw` with every page swept
   (`sw_end`'s hypotheses) and the `Idle` invariant.

`sw_witness g` is the run: `SwStart`, `SwStep` (C's page), `SwAlloc`, and
`SwStep` (B's run). The steps are stated over any heap with the facts they
need (`step1_abs`, `alloc_abs`) and instantiated with `W` at the end, as
§18.3 advises.

| Theorem | Witness |
|---|---|
| `Graft.alloc_graft`, `alloc_agree` | `surrogate_witness`: the surrogate of the start, C scrubbed |
| `NewOnly.alloc_new_only` | the same surrogate, and `W` |
| `Scrub.scrub_facts`, `core_scrub`, `scrubbed_no_pointer` | `surrogate_witness`: `zs` the dead list, C in it |
| `MidSweep.surrogate`, `alloc_relate`, `alloc_facts` | `surrogate_witness` (start); state 1 through `alloc_sw_ok` |
| `MidSweepAlloc.alloc_sw_ok` | `alloc_witness`: state 1, the allocation succeeds |
| `pages_allocator_sw_ok` (`Sweeping` invariant) | states 0–3 |
| `MidSweepStep.step_sw` | a pool page (state 0) and a run (state 2) |
| `sw_start` | state 0 |
| `sw_end`, `sweep_rest`, `sweep_from_sw` | `sw_witness_ok`: the rest from state 3 |
| `MidSweepRun.sw_run_inv`, `sw_run_ends` | `sw_witness` |
| `Pages.Allocator.alloc_post_new_old` | `Vacuity.interface_witness` (each phase's invariant, unchanged hypotheses) |

### 21.6 Changes to the plan

- **The walk clause of §20.4 step 3 is false for pages.** The plan says
  `W.reaches g zero e` implies `W.reaches g' zero e`. A new run of `k`
  pages overwrites `k` free pages with the object and one free rest. So the
  page bases inside the object stop being positions of the walk. What is
  proved is the form main's cycles use the clause for: the walk reaches
  the end of the heap after the allocation and the writes (`heap_objects_dense`
  through `WalkEnd.dense_from_walk_end`). Main's `alloc_walk_end`
  (equality of the walk's end) can also fail for pages: when
  `heap_size = pages_end`, a last page that turns from free into a pool page
  with a one-word tail ends the walk 8 bytes earlier. The walk clause is
  not in `AllocIface`.
- **Fact 2 needed its own lemma** (`NewOnly`); §20.4 expected it from
  `others_unchanged`, which gives only the other direction.
- **The `Sweeping` invariant of `pages_allocator` is still `pages_ok_mc`.**
  The mid-sweep instance is a second record, `pages_allocator_sw`, so no
  statement about `pages_allocator` changes meaning. A collector that
  sweeps incrementally uses `pages_allocator_sw`.
- **The swept set is the page map's swept bits**, not a separate `sst`.
  The page sweeper of §20.3 can take `sst = page_map` when it is built.
- **Not built:** sweeping on allocation (`Slice_unit`), the minor collection
  mid-sweep (§20.4 step 4: `Promote` is akhil's), and the runs like main's
  `SPOT.SweepPhaseCycleAlloc` (§20.4 step 5; `MidSweepRun` is the page form).

### 21.7 Modules

| Module | Lines | What it holds |
|---|---|---|
| `AllocIface` (changed) | 233 (was 145) | `colour_at`, `pending`, `field_ok_with`, `fields_written_with`, `alloc_post_with`, `allocator_ok_with`, `alloc_post_v1` |
| `Pages.Allocator` (`.fsti`, `.fst`, changed) | +57 | `pending = unswept`; `new_swept`, `colour_new`, `alloc_post_new_old` |
| `Pages.Graft` | 526 | `uw`, `graft`; `alloc_graft`, `alloc_agree` |
| `Pages.NewOnly` | 362 | `new_only`; `alloc_new_only` |
| `Pages.Scrub` | 289 | `core`; `fill_objs`, `scrub`; `fill_facts`, `core_fill_objs`, `scrubbed_no_pointer`; `objects_where` |
| `Pages.MidSweep` | 709 | `free_sw`, `pages_ok_sw`, `dead_list`; `block_uw`, `surrogate`, `alloc_same`, `new_out`, `alloc_relate`, `alloc_facts`, `no_grey_frame`, `target_fill` |
| `Pages.MidSweepAlloc` | 566 | `after_*`; **`alloc_sw_ok`**; `pages_allocator_sw`, `pages_allocator_sw_ok` |
| `Pages.MidSweepStep` | 607 | `step_use`, `step_block`, `step_infix`, `step_wf`; **`step_sw`**, `sw_start`, `sw_end`, `sweep_rest` |
| `Pages.MidSweepRun` | 95 | `sw_run`; `sw_run_inv`, `sw_run_ends` |
| `Pages.MidSweepVacuity` | 382 | the witness run and its facts |

`MidSweepRun` and `MidSweepVacuity` are roots in the `Makefile`.

### 21.8 Checked

- Every new and changed module (`AllocIface`, `Pages.Allocator` `.fsti` and
  `.fst`, `Graft`, `NewOnly`, `Scrub`, `MidSweep`, `MidSweepAlloc`,
  `MidSweepStep`, `MidSweepRun`, `MidSweepVacuity`) verifies without
  `--retry` at Z3 seeds 0, 1 and 2, from the clean cache of `ef186b67`:
  33 checks.
- No local rlimit is above 40. The most any query uses is 24.8
  (`MidSweepVacuity.step1_abs`, under 40); then 22.5 (`MidSweepAlloc.alloc_sw_basic`,
  under 40) and 20.1 (`MidSweepStep.run_step_sw`, under 40). Under the
  default rlimit of 20, at most 9.1.
- Three queries were fragile at some seed and were split, not given more
  rlimit: `Graft.pop_out` (`pop_swept`, `page_out`), `NewOnly.carve_new_only`
  (`carve_arith` first) and `NewOnly.pop_new_only` (`pop_ctx_new_only`);
  `MidSweepAlloc.alloc_sw_ok` (36 of 40 before) became `alloc_sw_basic`,
  `alloc_sw_fill` and `after_intro`.
- No admits, no assumptions.
- `make verify`, with the Makefile's default `--retry 3` as CI runs it, in a
  scratch worktree whose cache was the clean build of `ef186b67`: 427
  checked files (419 + the 8 new modules), no errors. The modules that use
  the interface (`Darken`, `GcCorrect`, `MarkSteps`, `SweepingStart`,
  `Vacuity`, `Witness`) were rechecked against it.

---

## 22. Design for review: the sweeper record, `AllocIface` v3 and the minor-collection event (2026-11-17)

Design only. Nothing here is built. It is written to be agreed with akhil
before any proof. References to main are at `5623c7f6`.

**Why this comes first.** Stage A (generic modules for main's incremental
cycle over `AllocIface` v2) stopped before any module was written. The cycle
cannot be stated over an allocator alone:
- **The sweep run is the first-fit allocator's.** In
  `GC.Gen.SweepPhase.Cycle`, `Slice` is `SL.phase_slice g fp`, the fused
  sweep that rebuilds the free list. The state at a slice,
  `sweep_inv_incremental g fp c`, mixes the cursor (`behind_swept`,
  `front_unswept`, `no_adjacent_free`, `free_incremental c`) with
  `fl_ascending`. Making it generic needs a sweeper record (22.2).
- **Both runs have a `Minor` event,** and it allocates through `Promote`
  (`AP.alloc_at`, which is `AC.alloc_phase`). Without `Minor`, the instance's
  theorems would cover fewer runs than akhil's. With `Minor` as an abstract
  event (22.5), `Promote` is not touched.
- **Some allocator facts the proofs use are not in v2** (22.3), and the walk
  fact they use is false for pages (22.4).

### 22.1 What the cycle's theorems use

**The collector's state is a hypothesis of every event, not a conclusion.**
Each constructor of `MC.marking` and `SC.cycle` takes the state at that point
(`GI.phase_shape`, `sweep_inv_incremental`, `sweep_shape`) as a `squash`
hypothesis. The entry points supply it. The cycle theorems use only the
*account* each event keeps (`MC.mark_run_inv`, `SC.cycle_inv`). So:
- For the cycle theorems, an event needs only "this event keeps the
  account". §20.1's fact 5 (the allocator keeps its invariant) is not used
  by them.
- Fact 5 is still needed to show runs exist (the vacuity witnesses, §18.3)
  and by the implementation. So it stays in the interface (clause F, 22.3).

| Run | Event | Lemmas it uses | Allocator? |
|---|---|---|---|
| marking | `Start` | `MStart.mark_start_shape`, `GMS.start_keeps_blocks`, `GMC.cycle_start` | only through `start_pre`'s `collection_heap_shape` |
| marking | `Slice` | `S.mark_steps_inv`, `MPC.account_steps`, `MPC.mark_steps_keep_blocks`, `S.mark_steps_darker` | no (`fp` appears only in `phase_shape`) |
| marking | `Write` | `MM.marking_write_barrier`, `MPC.account_barrier`, `GMS.modify_keeps_blocks`, `GB.modify_phase_shape` | no (`fp` only in `phase_shape`) |
| marking | `Alloc` | `MPC.account_alloc`, `MPA.marking_alloc`, `MPA.marking_fresh_write`, `MPC.account_fresh_close`, `MW.alloc_reaches` | **yes** (22.3) |
| marking | `Minor` | `GMC.account_minor`, `GMM.minor_keeps_marking_inv_with`, `GMM.minor_keeps_block`, `GMM.minor_new_block_black`, `MW.minor_reaches` | **promotion** (22.5) |
| sweep | `Start` | `phase_account_start` | **sweeper** (22.2) |
| sweep | `Slice` | `phase_account_slice` | **sweeper** |
| sweep | `Alloc` | `survivor_or_new_alloc`, `reclaimed_was_dead_alloc` | **yes**, with the sweeper's free |
| sweep | `Write` | `survivor_or_new_body_write`, `reclaimed_was_dead_body_write` | no, given that the shape keeps every header (`same_heads`) |
| sweep | `Minor` | `SPC.survivor_or_new_minor_made`, `SPC.reclaimed_was_dead_minor` | **promotion** |

**Collector-side work, not about the allocator.** akhil's statements mention
`fp` only through `phase_shape`, `collection_heap_shape` and
`collection_shape_with`. The generic modules need the collector's state
without the free list, `col_shape minor g ph sp`. For instance 1 they need
`phase_shape minor g fp ph sp <==> col_shape … /\ a1.shape ph g (fp, c)`.
- `GenInv.major_shape_with` is opaque, with `_intro` and `_elim`. So this
  should be a short proof.
- Generic copies of `mark_start_shape`, `modify_keeps_blocks` and
  `modify_phase_shape` are then stated from `col_shape`. They are
  allocator-free and their proofs carry over.
- Recommended: define `col_shape` in the generic module, not in
  `GC.Gen.Incremental` (question 3, 22.7).

### 22.2 The sweeper record (proposed shape)

**One change from §20.3: the sweep's progress lives in the allocator's
state.** There is no separate `sst`:
- **In both instances the sweep rewrites the allocator's state.** Main's
  fused sweep rebuilds `fp`. The page sweep rebuilds the page lists and the
  swept bits in `pstate`.
- **The allocator needs the progress** to colour a new object
  (`a.unswept`).
- §21.6 already found that the page sweeper's swept set is the page map's
  own bits.
- So for main, `ast = (fp, c)`. `Ph.gc_phase`'s `Sweeping c` stays in
  akhil's modules. The generic modules use `AllocIface.phase` and read `c`
  from the state.

    noeq type sweeper (a: allocator3) = {
      free_of   : a.ast -> free_def;              (* what the collector counts as free mid-sweep *)
      start     : heap -> a.ast -> a.ast;          (* the state at the hand-over *)
      slice     : heap -> a.ast -> nat -> GTot (heap & a.ast);   (* one slice, of a budget *)
      done      : a.ast -> bool;
      sweep_inv : heap -> a.ast -> prop;           (* the collector's Sweeping state *)
    }

**The generic account.** These predicates are akhil's, generic in what
counts as free. The walk-end equality is dropped (22.4).
- `acct free g0 since g`: `heap_objects_dense g`, and every block in use
  (`in_use free g x`) is a `survivor g0 g x` or in `since`.
  - Main's `survivor_or_new g0 since g c` gives
    `acct (free_incremental c) g0 since g`: the walk end is `g0`'s and `g0`
    is dense.
- `reclaimed_was_dead g0 since free g`: unchanged. It is already generic in
  `free`.
- At the end of the sweep: `acct free_stw`, and `reclaimed_was_dead … free_stw`.

**The contract, `sweeper_ok a sw`.** Each clause is stated with these
predicates, so main supplies its lemmas as they are.

| | Clause | Main (instance 1) | Pages (instance 2) |
|---|---|---|---|
| S1 | `free_def_ok (free_of s)` | `free_incremental_ok` | `MidSweep.free_sw_ok` |
| S2 | free agrees with the colour rule: for a block `x`, `free_of s g x <==> is_blue x g \/ (is_white x g /\ a.unswept s (hd_address x))` | the definition (`pending_free`: white, `x > c`); alignment to check | the definition of `free_sw` |
| S3 | **start**: from the marked heap (nothing grey, the tri-colour invariant, ready to sweep): `sweep_inv g (start g s)`, `acct (free_of s0) g nothing_new g`, and `reclaimed_was_dead g nothing_new (free_of s0) g` | `phase_account_start` | invariant: `MidSweepStep.sw_start`. Account: **new**, small (a block in use is black at the start: `start_unswept`) |
| S4 | **slice**: from `sweep_inv g s`, the slice gives `sweep_inv g' s'`, or the end state if `done s'`, and keeps `acct` and `reclaimed_was_dead` with `free_of s'` | `phase_account_slice`, `GI.phase_slice_shape` | invariant: `step_sw` per unit. Account: **new**, from `SweepUnits.unit_ok` through `step_use` and `step_block` (the blocks in use are the same before and after a step); words from `Survive` |
| S5 | **end**: `sweep_inv g s /\ done s` gives the `Idle` shape, `well_formed_heap`, and `free_of s` agreeing with `free_stw` on `g` | `GI.sweep_end_shape` | `sw_end` |
| S6 | **the program's events do not move the sweep**: allocation and body writes keep `sweep_inv`, and `free_of` is the same on old blocks | `alloc_sweep_phase`, `fresh_close`, `write_sweep_phase` (cursor unchanged) | `alloc_sw_ok` (`same_swept`); a body write leaves the page map alone |
| S7 | **finishing** (liveness; the cycle theorems do not use it): an unbounded slice ends `done` | `GI.phase_slice_finishes` | `sweep_rest` |

**The instances' fields:**

| Field | Main | Pages |
|---|---|---|
| `a.ast` | `(fp, c)` | `pstate` |
| `free_of` | `free_incremental c` | `free_sw st.pm` |
| `start` | `(fp, sweep_start.cursor)` | `StartSweep.start_sweep st` |
| `slice` | `SL.phase_slice` | **new definition**: `SA.step` over the next unswept units in page order, up to the budget |
| `done` | `sweep_done c` | `all_swept st` |
| `sweep_inv` | `sweep_inv_incremental g fp c` | `pages_ok_sw g st` |

**Sweeping on allocation** (pages' `pool_find`) stays a collector step taken
just before `Alloc` (§20.3's `Slice_unit`).
- In the record it could be an optional field
  `slice_unit: heap -> a.ast -> unit -> heap & a.ast`, with S4's contract.
- Main would have none. Whether it belongs in the record or only in the
  page instance is question 1b (22.7).

### 22.3 `AllocIface` v3

**Form.** v3 is a new record, `allocator3`, beside v2. No v2 statement
changes (`pages_allocator_ok`, `pages_allocator_sw_ok` and §21 stay as they
are). Each instance proves that v3 gives v2.

**Changes to the record:**
1. **The tag.** `alloc : phase -> heap -> ast -> nat -> tag -> GTot (heap & ast & U64.t)`,
   with `tag < 256` and `tag <> infix_tag`. Main's `alloc_phase` takes one,
   and the cycle needs it: `marking_alloc` concludes
   `tag_of_object obj = tag`; `no_infix_block` and `program_write`'s
   `~is_closure` read it.
2. **The invariant splits.**
   - `shape ph g s` is the allocator's own structures. It does not read the
     fields of blocks in use.
   - Well-formedness of the fields is the collector's
     (`well_formed_heap_with free`).
   - v2's `inv` is `shape /\ well_formed_heap_with free` (an instance lemma).
   - Main's `shape` is the `fl_ascending`/`alloc_ok` part (`sweep_shape`
     while sweeping). Pages' is `Scrub.core` plus each phase's colour facts,
     without the well-formedness and L10.
3. **`pending` takes the heap before the allocation**:
   `pending : ast -> heap -> hp_addr -> prop`. Main's pending words are the
   words of the `pending_free c` blocks of `g` (§20.2's table), which depend
   on the heap. Pages ignores the heap.

**The guarantee.** `free` is what the collector counts as free before the
allocation, and `free'` after it: `free_stw` in `Idle` and `Marking`,
`sw.free_of s` and `sw.free_of s'` in `Sweeping`. v2's clauses stay: on
failure nothing changes; the new object `x` is an object of `g'` of wosize
`wz`, of colour `colour_at`, and was not live in `g`; `others_unchanged`;
the `pending` frame. The new clauses:

| | Clause | Main's source | Pages' source |
|---|---|---|---|
| T | **tag**: `tag_of_object x g' == tag` | `alloc_phase_new_block` (`new_block`), `marking_alloc` | **none.** The page allocator writes tag 0 (`Pages.Alloc`: "white with tag 0"). Needs `alloc_tag`: `alloc_col`, then a header rewrite of the tag bits, proved as `Recolour` does for the colour bits. Risk: closures (`is_closure`, and infix headers in the body that the caller writes); `tag <> infix_tag` as main. Cost: the same header store, so the ≤ 5% rule is unaffected |
| N+K | **only the new object comes into use, and no block in use becomes free**: `in_use free' g' y == (in_use free g y \|\| y = x)` | `Mut.alloc_in_use`, `alloc_keeps` (Sweeping, any cursor). For `Marking`/`Idle`: through the colour, since `alloc_phase` differs between phases only in the header's colour (an `AP` lemma, to check) | `Sweeping`: `alloc_sw_ok`'s `in_use` equation (`NewOnly.alloc_new_only`, `MidSweepAlloc.use_eq`). `Idle`: `NewOnly.alloc_new_only` with `others_unchanged` (`Th.alloc_ok`). `Marking` (`alloc_col Black` from `pages_ok_mc`): **new**, a transfer through `Recolour` as `pages_allocator_ok` does for its other clauses |
| C | **carved from free space**: a word in the extent of `x`, or of a block free in `g'`, was in the extent of a block free in `g` | `Mut.alloc_carved` (`carved_from`: the object and the rest of block `q`) | per path, `Replace.replaces` (the replaced stretch was all blue; `NewOnly` uses each path's). **New**: one lemma over the paths, from `NewOnly`'s per-path facts |
| W | **the walk is dense after the allocation**, and after the caller's writes: `heap_objects_dense g'` | `MW.alloc_reaches`, any phase (positions kept, so dense) | `Sweeping`: `alloc_sw_ok` (`walk_end g'' + 8 >= heap_size`), then `WalkEnd.dense_from_walk_end`. `Idle`: the result's `pages_ok` (`Th.alloc_ok`), then `Darken.idle_dense`. `Marking`: **new**, the same argument over `pages_ok_mc` |
| W+ | **optional, per instance**: the walk ends where it did, `walk_end g' == walk_end g` | `Mut.alloc_walk_end`, `MW.alloc_reaches` | **false** when `heap_size = pages_end` (§21.6); see 22.4 |
| F | **the bridge, write by write**. (i) Right after the allocation, `shape ph g' s'` and `well_formed_heap_with (free' ∪ {x}) g'` (`x` counted free while its fields are unwritten). (ii) A write into the body of `x`, or of a block in use, keeps (i), every header and the walk. (iii) Once `x`'s fields are storable (`fields_storable free' g'' x`), `well_formed_heap_with free' g''` | `Marking`: `MPA.marking_alloc` (`marking_fresh`: `wf_with (free_or_new obj)`), `marking_fresh_write`, `marking_fresh_close`. `Sweeping`: `alloc_sweep_phase` (`fresh_ok`, `free_or_uninitialised`), `fresh_write`, `body_write_shape`, `fresh_close` | (iii): `MidSweepAlloc.wf_close` (from `wf_with (free_x pm' x)`) with `after_wf`/`after_use`, stated after all writes. (i) and (ii) are **new**: today pages states the invariant only once every field is written (`fields_written_with`). Needed: `Scrub.core` does not read the fields of live objects; `Scrub.core_fill_objs` proves it for filling dead objects, and a per-write form for a live object is new |

Clause F is not used by the cycle's theorems (22.1). It is how the runs'
hypotheses are met in the witnesses and the implementation.

**What the generic `Alloc` events then use:**
- **marking:** N+K, `others_unchanged`, black (`colour_at Marking`), F(i)
  and W;
- **sweep:** N+K and C (for `reclaimed_was_dead`), W, the `pending` frame,
  and S6.

The generic form of `MPA.marking_alloc` (that the marking invariant holds
with `x` fresh) is collector-side work from these clauses: the blocks in
use, their edges and their colours are those of `g` plus a black `x`. This
is the largest new proof of the generic marking run.

### 22.4 The walk clause

**What akhil's proofs use the walk for:**
1. **Marking.** `mark_run_inv` carries `W.reaches g zero_addr (walk_end g0)`,
   so the hand-over has `walk_end gh == walk_end g0` (`same_blocks_reaches`).
2. **The sweep.** `survivor_or_new` and `idle_account` carry
   `walk_end g == walk_end g0`.
   - `reclaimed_was_dead_transfer` and `lossless_at_idle` use it.
   - `survived_at_idle` uses it to find a block of `g` over `x`'s header
     (`block_over g p`, with `p < walk_end g0`).
3. **The cycle's words.** `start_words` and `handover_words` compare the
   words below `walk_end g0` and below `walk_end gh`.

**Proposal: the generic proofs carry only density.** Density is
`heap_objects_dense`, that is `walk_end + 8 >= heap_size`
(`W.reaches_end_of_dense`). Every word `p` with `p + 8 < heap_size` lies
below every dense heap's walk end. So:
- **`cycle_survives` stays as it is, generically.** `x`'s header is at most
  `heap_size - 16`, so it is below the walk's end in any dense heap.
- **`cycle_lossless`, generic form:** for `p + 8 < heap_size`.
- **`cycle_lossless_walk`:** the full form, for every `p < heap_size`, when
  the instance gives W+ for every event. That is akhil's statement.
  - Main meets W+ with `alloc_walk_end`, `same_heads_walk_end` (writes),
    `phase_account_slice` (which carries the equality), the minor lemmas
    (whose `survivor_or_new` carries it) and `same_blocks_reaches` (marking).
  - So instance 1 gives exactly his `cycle_lossless`.
- **Pages.** W+ fails only for the last word, in the tail case. There the
  page `cycle_lossless` is the `p + 8 < heap_size` form. To cover the last
  word too, either the page layout keeps a one-word tail as a block, or the
  statement stays partial (question 4, 22.7).

**Risk.** `reclaimed_was_dead_transfer` and `lossless_at_idle` are stated
with the equality. Their generic copies must be re-proved from density.
This is the part of the generic sweep most likely to need new work.

### 22.5 The abstract minor collection

**The generic runs take a record that the instance supplies:**

    noeq type minor_event (a: allocator3) = {
      ev   : Type;                              (* main: the nursery and the roots *)
      pre  : phase -> heap -> a.ast -> MP.scan_pos -> (obj_addr -> prop) -> ev -> prop;
                                                 (* the event's hypotheses; the set is outside the snapshot *)
      run  : phase -> heap -> a.ast -> ev -> GTot (heap & a.ast);
      pre_refs  : heap -> ev -> obj_addr -> prop;   (* outside references before (main: outside_refs_of) *)
      post_refs : heap -> ev -> obj_addr -> prop;   (* and after (main: root_refs of the new roots) *)
    }

**Main's `pre`:**
- `Marking`: `GI.phase_shape`, `roots_valid_for_minor_collection`,
  `outside_refs_reached` for the roots, and
  `minor_major_fields_not_free (outside_snapshot s)`.
- `Sweeping`: `sweep_inv_incremental`, `minor_heap_shape`, and
  `minor_major_fields_not_free (free_incremental c)`.

These are the hypotheses of akhil's `Minor` constructors, word for word.

**What an instance proves.** Write `(g', s') = run ph g s e`.
`made y` is `in_use free' g' y /\ ~(in_use free g y)`.

| | At `Marking` | Main's lemma |
|---|---|---|
| M1 | **account**: `within_snapshot s g` gives `within_snapshot (with_new_blocks s g g') g'` | `GMC.account_minor` |
| M2 | **marking invariant**, for every extra set `r`: `marking_inv g (pre_refs ∪ r) sp` gives `marking_inv g' (post_refs ∪ r) sp` | `GMM.minor_keeps_marking_inv_with` |
| M3 | **blocks in use are kept**: `in_use free_stw g y` gives `y` in the objects of `g'`, with the same header | `GMM.minor_keeps_block` |
| M4 | **made blocks are black** | `GMM.minor_new_block_black` |
| M5 | **the walk**: density kept, and W+ (positions kept) where the instance has it | `MW.minor_reaches` |

| | At `Sweeping` | Main's lemma |
|---|---|---|
| N1 | **account**: `acct (free_of s) g0 since g` gives `acct (free_of s') g0 (since ∪ made) g'` | `SPC.survivor_or_new_minor_made` |
| N2 | **converse**: `reclaimed_was_dead` kept, with `made` added | `SPC.reclaimed_was_dead_minor` |
| N3 | **the sweep does not move**: `free_of s'` agrees with `free_of s` on old blocks | `GI.minor_keeps_phase_shape` (`pending_free` kept; the cursor unchanged) |

**What the generic run must still supply itself:** that
`marking_inv g (pre_refs ∪ r) sp` holds, where `r` is what was reachable
at the start. akhil's `minor_inv` gets it from `phase_shape`, the event's
`outside_refs_reached` and `satb`. It is collector-side, a union of outside
sets for `MP.marking_inv`.

**The pages instance, later, by promotion.** A promotion is, for each live
nursery object, an allocation at the phase (`a.alloc ph … tag`), its field
writes, and the forwarding. With v3:
- M3 and N3 follow from `others_unchanged` and N+K, one allocation at a
  time.
- M4 follows from `colour_at Marking = Black`.
- N1 and N2 follow from N+K, C and W, one allocation at a time.
- M5 follows from W.
- M1 and M2 are the Cheney simulation (`CheneyGeneric`) given these.

This is §20.5 item 6, whether as a generic copy of the promotion lemmas or
as `Promote` taking the record (akhil's call).

### 22.6 The generic runs and instance 1

- **`gmarking a sw me g0 rs`** has `Start`, `Slice`, `Write`, `Alloc` and
  `Minor`, as `MC.marking`. Each event's hypotheses are `col_shape`,
  `a.shape` and the event's own (`me.pre` for `Minor`).
- **`gsweep`** has `Start`, `Slice` (`sw.slice`), `Alloc`, `Write` and
  `Minor`, as `SC.cycle`.
- **`gcycle`** composes them, as `GC.Gen.Cycle.major_cycle`.
- **The theorems:** `cycle_account`, `cycle_complete`,
  `cycle_frees_unreachable`, `cycle_survives`, `cycle_addresses_lossless`
  and `cycle_covered`. `cycle_lossless` comes in the two forms of 22.4.
  `per_step_safety` keeps the collector's state through each event, from
  S4, S6 and F.
- **Instance 1: "exactly his theorems".**
  - A total map `to_generic` from each of akhil's run types to the generic
    one, at main's allocator, sweeper and minor event.
  - Each of his conclusions is then the generic theorem applied to
    `to_generic r`, with the same statement. His types and theorems are not
    edited.
  - Witnesses: main's SPOT runs (`MarkPhaseCycleAlloc`,
    `SweepPhaseCycleAlloc`, `SweepPhaseFreedByEnd`) mapped through
    `to_generic`.

### 22.7 Questions for akhil

1. **Progress.** (a) Should the sweep's progress live in the allocator's
   state rather than in `Ph.gc_phase` (22.2)? (b) Does sweeping on
   allocation belong in the record, or only in the page instance?
2. **`Minor`.** Should it be an abstract event with the properties of 22.5?
   Should `Promote` eventually take the allocator record, or should a
   generic copy of the promotion lemmas be made?
3. **`col_shape`.** Should it be defined in the generic modules (recommended;
   no edit to `GC.Gen.Incremental`), or in his?
4. **The walk.** Density in the generic proofs, W+ as an instance clause for
   the full `cycle_lossless` (22.4). For pages, keep the tail word as a
   block, or accept the partial statement?
5. **The tag.** Should it be in the allocator's signature (22.3, change 1)?

### 22.8 Order of work, once agreed

1. `AllocIface` v3 (`allocator3`, the clauses), and instance 1's clauses from
   main's lemmas (22.3).
2. Pages' v3 clauses: `alloc_tag`; N+K at `Marking`; C as one lemma; W at
   `Marking`; F (i) and (ii) per write.
3. The sweeper record, instance 1 from akhil's lemmas, the generic sweep
   run, and `to_generic` for `SC.cycle`.
4. The generic marking run with `minor_event`, instance 1, and `to_generic`
   for `MC.marking`.
5. The generic cycle; instance 1's theorems; vacuity through the SPOT runs.
6. The page sweeper instance (S3 and S4's accounts are new). Then pages'
   minor event, by promotion (§20.5 item 6).

## 23. Plan: a pages-only incremental cycle in our own modules (2026-11-17)

**This replaces §22 as the plan of record; §22 stays as an alternative.**
§22 made akhil's cycle generic and needed five decisions from him (22.7).
This plan needs none:
- akhil's modules are only imported, and his lemmas are called as they are.
  Nothing in `generational/` or `mark-and-sweep/spec/GC.Spec.*Phase*`
  changes;
- there is no `AllocIface` v3 and no sweeper record;
- the cost is that the page cycle is a second run type beside his, with the
  same statements. Where his proof is in a private helper of a `.fst`, it is
  copied into our module with the allocator facts replaced, never edited in
  place.

### 23.1 What we build

| Piece | Our module (proposed) | What it is |
|---|---|---|
| Page marking run | `GC.Spec.Pages.Cycle.Mark` | `pmarking g0 rs g st sp since`: Start, Slice, Write, Alloc and Minor events, over a page state `st` in place of `fp` |
| Page sweep run | `GC.Spec.Pages.Cycle.Sweep` | `psweep g0 g st ph since`: Start, Step (one `SA.step` unit, or a budget of them), Alloc, Write and Minor; built on `MidSweepRun.sw_run`'s events |
| Page cycle | `GC.Spec.Pages.Cycle` | `pcycle g0 rs g st ph since = PMark … \| PSweep …`, and the theorems |
| Page promotion | `GC.Spec.Pages.Promote*` | promotion into the page allocator (23.6) |
| Witness | `GC.Spec.Pages.Cycle.Vacuity` | a full cycle, both phases, non-trivial (23.8) |

**The theorems, with akhil's statements word for word** (his `GC.Gen.Cycle`,
with `major_cycle … fp …` read as `pcycle … st …`):
`cycle_account`, `cycle_complete`, `cycle_frees_unreachable`,
`cycle_survives`, `cycle_addresses_lossless`, `cycle_covered`,
`cycle_lossless`. Their bodies use his predicates unchanged
(`MC.snapshot`, `GMC.reachable_at_start`, `SPC.freed`, `SPC.new_covered`,
`LL.blue_covered`, `unreachable_covered`), so they mean what his mean. In
particular `cycle_lossless` is for every `p < heap_size`, the last word
included; 23.5 is what makes that true for pages.

### 23.2 The marking side: his lemmas, reused unchanged

His marking run's events take `GI.phase_shape minor g fp Ph.Marking sp`,
which holds main's free-list shape, so we cannot build his `MC.marking`
from page states. But `phase_shape` is used in his proofs only to get two
facts, by `GI.phase_shape_marking`: `well_formed_heap g` and
`MP.marking_inv g (nursery_refs minor) sp`. Both are allocator-free. Our
marking state is

    pmark_ok minor g st sp = pages_ok_mc g st /\ all_swept st /\
                             MP.marking_inv g (GMM.nursery_refs minor) sp /\
                             <the nursery facts of collection_shape_with, with free_stw>

and `pages_ok_mc` holds `well_formed_heap` (`AllocPhase.pages_ok_mc`).

**Reused as they are** (called from our module, statements unchanged):

| Event | His lemmas we call | Allocator-free because |
|---|---|---|
| all | `MC.snapshot`, `MC.satb`, `MC.mark_run_inv`, `MC.init_writes` (definitions) | they mention only the heap |
| Start | `MPC.account_start`, `MB.darken_roots_bounded_prefix_*`, `MPC.account_grey`, `MPC.reachable_outside_refs`, `MPC.reachable_closed`, `GMC.reachable_at_start_eq` | root darkening is a recolouring |
| Slice | `MPC.account_steps`, `MPC.mark_steps_keep_blocks`, `MPC.grey_keeps_blocks`, `MPC.cycle_handover`, `MP.marking_inv_*` | `S.mark_steps` only recolours |
| Write | `GB.modify_heap`, `GB.modify_ok`, `MPC.account_barrier`, `MPC.cycle_write`, `MM.write_heads` | the barrier is darken-then-write |
| Alloc (after the allocation) | `MPC.account_fresh_write`, `MPC.account_fresh_close`, `MPA.marking_fresh`, `MPA.marking_fresh_write`, `MPA.marking_fresh_close`, `MPA.keeps_blocks_resolve`, `keeps_blocks_edges`, `keeps_blocks_reach`, `MPA.free_or_new_ok` | they are stated over `keeps_blocks` and `well_formed_heap_with`, not over the allocator |
| Hand-over | `MPC.account_marked`, and `handover`'s argument | — |

**Copied, with the allocator fact replaced** (his are private helpers of
`GC.Gen.MarkPhase.Cycle.fst` or take `phase_shape`):
`start_prefix`/`start_prefix_edges`, `start_satb`, `start_extra`, `slice_inv`,
`barrier_blocks`, `write_inv`, `init_inv`, `alloc_inv`, `minor_inv`,
`same_blocks_reaches`, `mark_run_account`, `handover`. About 400 of his 475
lines, mostly unchanged text: each `GI.phase_shape_marking` becomes our
`pmark_ok_elim`.

**New for pages, the marking side:**

| | What | From |
|---|---|---|
| M-a | **mark steps keep `pmark_ok`**: `S.mark_steps g sp g' sp'` keeps `pages_ok_mc` | `MPC.mark_steps_keep_blocks` (only colours change) and `MarkPhase.mark_inv_recolour`, as `MarkSteps` does for the stop-the-world mark. Small |
| M-b | **the barrier keeps `pmark_ok`**: darken (a recolouring, as M-a), then a write into the body of a block in use | the write is new: `Scrub.core` and `pages_ok` do not read the fields of blocks in use (`Scrub.core_fill_objs` proves it for dead ones), and `no_pointer_to_blue` is kept since the value is storable. Medium |
| M-c | **`marking_alloc` for pages**: from `pmark_ok`, `PA.alloc Marking` gives a black block `x` that was not in use, `keeps_blocks free_stw g g'`, `well_formed_heap_with (free_or_new x) g'`, `blocks_fit g'`, and `pmark_ok` with `x` fresh | his `MPA.marking_alloc` is first-fit (`alloc_kept`, `alloc_in_use`, `MarkPhase.Alloc.fst:155-285`); ours is the same argument from `Th.alloc_ok`, `others_unchanged`, `NewOnly.alloc_new_only` and `Recolour` (Marking paints black). The in-use equation at `Marking` is new (N+K of §22.3). Then his `keeps_blocks_*` give the rest. Medium |
| M-d | **`account_alloc` for pages** (`within_snapshot_fresh` after the allocation) | his `MPC.account_alloc` proof with M-c in place of `MPA.alloc_in_use`. Small |
| M-e | **init writes keep `pages_ok_mc`** (each write into the fresh object's body) | as M-b, for the fresh object. Small once M-b exists |
| M-f | **the walk**: `W.reaches g zero (walk_end g0)` kept by an allocation | with the layout of 23.5 the walk always ends at `heap_size`; we carry `walk_end g == heap_size` in place of `reaches`, from `pages_ok` (Partition). Small |
| M-g | **start**: the page `Idle` invariant (`pages_ok`, `well_formed_heap`, `all_swept`) gives his `start_pre`'s heap facts (well formed, nothing grey or black) | `pool_white`, `run_swept_ok`. Small |

### 23.3 The sweeping side: our page sweep, his account predicates

The sweep runs on the page sweep already proved (§21.4): `pages_ok_sw`,
`step_sw`, `alloc_sw_ok`, `sw_start`, `sw_end`, `sweep_rest`, and the
interleaved runs of `MidSweepRun.sw_run`. No sweeper record and no cursor.

**What the run carries** (our `psweep_inv`), with his predicates:

    Sweeping: walk_end g == walk_end g0 /\
              (forall x. in_use (free_sw st.pm) g x ==> SPC.survivor g0 g x \/ since x) /\
              SPC.reclaimed_was_dead g0 since (free_sw st.pm) g
    Idle:     SPC.idle_account g0 since g /\ SPC.reclaimed_was_dead g0 since free_stw g

The `Sweeping` line is his `survivor_or_new g0 since g c` with
`free_incremental c` replaced by `free_sw st.pm`; it is a definition of ours
(`survivor_or_new_pg`), since his fixes the cursor's free.

**Reused unchanged** (all generic in `free`, or about `Idle`):
- `SPC.survivor`, `survived_mark`, `nothing_new`, `with_new`, `idle_account`,
  `new_covered`, `free_or_new_at`, `freed`, `reclaimed_was_dead`
  (definitions);
- `SPC.reclaimed_was_dead_transfer`: for every sweep step, allocation, write
  and minor collection, with `free = free_sw pm`, `free' = free_sw pm'`.
  It needs the walk's end equal; 23.5 gives it;
- `SPC.covered_at_idle`, `SPC.lossless_at_idle`, `SPC.survived_at_idle`: the
  end of the cycle, as they are;
- `LL.blue_covered`, `LL.dead_covered`, `LL.in_extent`.

**New for pages, the sweeping side:**

| | What | From |
|---|---|---|
| S-a | **the start account**: at `sw_start`, `survivor_or_new_pg g0 nothing_new g0` and `reclaimed_was_dead g0 nothing_new (free_sw pm0) g0` | a block in use at the start is black (`start_unswept`); a free block is blue or white-unswept, so dead at mark. Small |
| S-b | **a sweep step keeps the account** | `step_use` and `step_block` (the blocks in use are the same, with their sizes) give the transfer's hypotheses with `made = nothing`. The walk end: 23.5. Small to medium |
| S-c | **an allocation keeps the account**, `since` gains `x` | `alloc_sw_ok`'s in-use equation (`MidSweepAlloc.use_eq`), `made = {x}`; the transfer. Small |
| S-d | **a write keeps it** | the write keeps every header (`same_heads`), so `in_use` and the walk. Small |
| S-e | **the end**: `pages_ok_sw` with every page swept gives `idle_account` | `sw_end`; `free_sw pm = free_stw` when nothing is unswept. Small |
| S-f | **the hand-over**: his `handover` facts on `gh`, and `pages_ok_mc gh st`, give `sweep_ready gh (start_sweep st)` and `mark_done gh`, so `sw_start` | `SweepingStart` does this from the stop-the-world mark; ours is from `pages_ok_mc` after mark steps. Small to medium |
| S-g | **writes during the sweep keep `pages_ok_sw`** | as M-b, with `free_sw`. Small once M-b exists |

### 23.4 The cycle

`pcycle` composes the two runs as his `major_cycle` does (`Mark`, and
`Sweep` with the hand-over slice), and its theorems are proved as his
`GC.Gen.Cycle.fst` proves them (251 lines, copied with our run types): the
marking half from `handover` (23.2), the sweeping half from
`psweep_inv` at `Idle` and his `lossless_at_idle`, `survived_at_idle`,
`covered_at_idle`, joined by his `start_words`/`handover_words` argument.
That argument compares words below `walk_end g0` and `walk_end gh`; with
23.5 both are `heap_size`.

### 23.5 The heap's last word

**The gap.** `cycle_lossless` is for every `p < heap_size`. With the
current layout it is false for pages in one case:
- when `heap_size = pages_end` (the runtime's case: the bridge rounds the
  heap to whole pages), and the last page is a pool page of a class with a
  one-word page tail, that word is not a block (its object address would be
  `heap_size`), and the walk ends at `heap_size - 8`;
- the classes with `page_wsize % cls c = 1` exist: at 4096 words they are
  3, 5, 7 and 65 (at 2048, 89);
- **the counterexamples go both ways.** The sweep turns such a page with
  every slot dead into a `Free` page, one blue block to `heap_size`: the
  word was in no block of `g0` and is now free (left side false, right side
  true). An allocation turns a free last page into such a pool page: the
  word was in a free block of `g0`, and is now in no block (left true,
  right false);
- the stop-the-world page theorem (`GcCorrect.lossless`) does not meet this
  because it quantifies over the words of blocks of the marked heap, not
  over every word.

So without a change to the allocator or the layout the theorem is false,
and the plan does not weaken it. The options:

| | Option | Change to the proofs | Performance |
|---|---|---|---|
| **L1 (recommended)** | **Reserve the heap's tail: at least two words after the last page, always one blue block.** `n_pages = (heap_size - zero_addr - 16) / page_bytes`. Then `tail_shape` is always its blue-block case, every page (and a one-word page tail, now at `pages_end - 8`, an object address below `heap_size`) is a block of the walk, and **the walk ends at `heap_size` in every page state**. W+ of §22.3 holds for pages, so his walk-end lemmas apply unchanged | `Layout`: `n_pages`, and `pages_end_bound` becomes `16 <= heap_size - pages_end < page_bytes + 16`; its 22 call sites (half in `Init`) checked against the new bound. `tail_shape` stays as it is (its short case never holds). `Init` writes the tail block (it already has a case for a heap tail). New: `walk_end g == heap_size` from `shape_ok` (`Partition` gives it up to the last word). No change to `Alloc`, `Sweep*`, `MidSweep*` | 16 bytes per heap. The bridge adds two words to the heap it asks for, so no page is lost. No change on any fast path |
| L2 | **A parameter condition and a run rule**: no class with a one-word page tail (`page_wsize % cls c <> 1`, a new C6), and a new run never leaves a one-word rest | `Params`, `NewRun` (a run whose rest would be one word); `SweepRun` pieces at the heap's end to check | changes OCaml 5's class table (3, 5, 7, 65 at 4096), so memory overhead and the bench numbers move; must be re-benchmarked against the ≤ 5% rule |
| L3 | **Avoid the last page** for those classes and for runs whose rest would be one word | the page-taking paths (`PoolInit`, `NewRun`, `Pages.Alloc`): a new case in each, and in their Pulse code | at most one page unused for those classes; a branch on the page-taking slow path |
| L4 | Assume `heap_size - pages_end >= 16` of the runtime | none, but it is a configuration axiom on the extern `heap_size` (`GC.Spec.ZeroAddr`), which §1.1 rejected (the old P5) | none |

L1 is the smallest change and the only one that makes the walk's end
constant, which is what lets 23.3 reuse his transfer and `Idle` lemmas
unchanged. The stop-the-world theorems (`gc_correct_pages`) keep their
statements; their proofs are rechecked under the new `n_pages`.

### 23.6 Promotion

**Why his promotion cannot be called as it is.** `Promote.promote_object`
calls `AP.alloc_at ph major fp …` (main's first fit) in its definition
(`GC.Gen.Promote.fsti:83-94`), and the Cheney state carries `cs_fp`
(`Cheney.fsti:46`). `cheney_collect_spec_with ph free` is generic in the
phase and in what counts as free, but not in the allocator:
`allocations_not_free` quantifies over `AP.alloc_at`, and `promote_pre`
holds `fl_valid` and `chain_objects_blue` (`CheneyGeneric.fsti:47`). So
every lemma whose statement mentions `cheney_collect_spec_with`,
`collect_marking` or `collect_at` is about first fit, even where its proof
uses only heap facts. Since we do not edit his modules, a page promotion is
our own definition, `ppromote`, with `PA.alloc` in place of `AP.alloc_at`,
and the lemmas about it are ours.

**His promotion modules, by how much they depend on first fit** (a survey of
`generational/spec`, line counts with interfaces, not checked by F*):

| Group | Modules | Lines | For pages |
|---|---|---|---|
| allocator-free | `CheneyBFS`, `ForwardingArray`, `MinorHeap`, `PromoteUpdate.Field`/`Obj`/`Header`/`Aux`, `CombinedGraph`, `Reachability`, `ReachabilityBridge`, the definitions of `Cheney.fst`, `Cheney.Sim` (one `fl_ascending_valid`) | ~7.4k | **reused unchanged**: forwarding, field rewriting, the reachability and BFS theory, the nursery's shape |
| free list only threaded | `MinorCollectForwarding.*`, `CheneyPreservation.*`, `Cheney.Induction`, `SimOne`, `CheneyCorrectness`, the well-formedness part of `CheneyGeneric`, `MarkPhase.Minor`, `SweepPhase.Minor` | ~14.5k | **copied and edited**: the reasoning is about the heap, but the statements name `fp` and his promotion. In our copy, `fp` becomes `pstate`, `alloc_ok g fp` becomes the page invariant, and the frame lemmas, stated today with `chain_avoids g fp x` (obtained from "x not blue" through `chain_objects_blue`), become "a block that is not blue is unchanged", which the page allocator gives directly (`others_unchanged`) |
| essential free-list reasoning | `Promote.fst:159-230`, `Cheney.Steps`, `PromoteUpdate.BlueProm`/`BlueAlloc`, `WriteBodyLemmas`, `AllocExact`, `FreeListAscending`, `CheneyFlComplete`, `FreeListShape`, `PostCollectionShape`, `Cheney.fst:253-347`, the free-list part of `CheneyGeneric`, `Cheney.Dense`, `GC.Gen.SweepPhase.fst` | ~4.6k | **not used**; replaced by ~1.5-2.5k lines of page proofs |

**The allocation facts promotion uses** (from the survey; each must be a
page lemma, at the phase promotion runs at):

| Fact | Page source |
|---|---|
| the new object is an object of the result, in bounds, of the requested size | `Th.alloc_ok`, `alloc_sw_ok` |
| not blue; the phase's colour | `colour_at`, `Recolour` |
| **the tag** (`promoted_tag`, the minor object's own) | **new**: the page allocator writes tag 0. `ppromote` writes the header's tag after the allocation (a one-header rewrite, proved as `Recolour` does for colours), or the page `alloc` takes a tag. Our choice, since `PA.alloc` is ours |
| old objects kept, only one new object | `NewOnly.alloc_new_only`, `others_unchanged` |
| old blue blocks: as the walk needs | `Replace.replaces` per path |
| headers and bodies of blocks that are not blue unchanged | `others_unchanged` (in place of `chain_avoids`) |
| `no_infix_block` kept | **new**, small (the new header's tag is not `infix_tag`; the rest unchanged) |
| the walk dense, and (with 23.5) its end at `heap_size` | 23.5 |
| copying the fields keeps the page invariant | as M-b (field writes into a block in use), for each copied field |
| the pointer update (`update_walk`) keeps the page invariant | as M-b |
| mid-sweep: `pages_ok_sw`, `same_swept`, the in-use equation | `alloc_sw_ok` |

**What the cycle needs from `ppromote`** is the page form of the properties
in §22.5, now as our lemmas about our definition:
- while marking: the account with the promoted copies (his `account_minor`,
  our copy, with "allocated black" from `colour_at Marking`); `pmark_ok`
  kept for any extra outside references (his `minor_keeps_marking_shape`
  without the free list); blocks in use kept; new blocks black; the walk's
  end;
- while sweeping: `survivor_or_new_pg` and `reclaimed_was_dead` with the
  copies made (his `survivor_or_new_minor_made`, `reclaimed_was_dead_minor`,
  copied: they use `minor_keeps_blocks` and the walk's end, both heap-side
  once the frame is "not blue ⇒ unchanged"); `pages_ok_sw` kept and nothing
  swept or unswept (`same_swept`).

**An alternative, not proposed here:** if akhil later makes `promote_object`
take the allocator as a parameter (the §22 route), the ~14.5k copied lines
collapse to instantiations. The copy is the price of not depending on that.

### 23.7 Estimate

Rough, by lines of F* (what §21 took is the yardstick: about 3.9k lines of
`MidSweep*`, `Graft`, `NewOnly`, `Scrub` for §20.2 and §20.4).

| Stage | New proof | Copied from akhil, edited | Risk |
|---|---|---|---|
| 1. Layout L1 (23.5) | ~150 (`walk_end == heap_size`, `Init`'s tail block) | — | low: every page module rechecked; 22 `pages_end_bound` sites |
| 2. Marking side (23.2) | ~900-1,300 (M-a … M-g; M-b and M-c are most of it) | ~400 | medium: M-b, the per-write bridge |
| 3. Sweeping side (23.3) | ~600-900 (S-a … S-g) | ~150 | low to medium: S-f |
| 4. Cycle without minor collections, and its witness | ~300 + ~600 (witness) | ~250 (`GC.Gen.Cycle.fst`) | low |
| 5. Promotion (23.6) and the `Minor` events | ~1,500-2,500 | ~14,500 (mechanical, but each module must re-verify under the rules: seeds 0-2, no `--retry`, rlimit ≤ 40; his may not all meet that today) | **high, and most of the cost** |
| 6. Witness with a minor collection in each phase | ~400 | — | medium |

Stages 1-4 total about 3-4k new lines, about §21's size. Stage 5 roughly
doubles the whole, and its copied lines need checking against our rules
(no `--retry`), which his were not written for.

### 23.8 Vacuity

The witness is one run of `pcycle` built from `MidSweepVacuity`'s heap `W`:
- Start with a reachable A, an unreachable C, and a free page;
- a mark slice, a barrier write that cuts the edge to A while A is white
  (so the barrier greys it), an allocation while marking (black);
- the hand-over, a sweep step, an allocation mid-sweep, the rest of the
  sweep;
- in stage 6, one minor collection in each phase, promoting one object.

At the end:
- `cycle_survives` holds of A;
- `cycle_complete` of C;
- `cycle_lossless` of a word of C, a word of the free page, and the heap's
  last word (the tail block of L1);

each with both sides non-trivial. As in §21.5, each step is stated over any
heap with the facts it needs, and is then instantiated.

### 23.9 Order of work, and what to agree

1. **L1** (23.5): the only change to an existing page definition (`n_pages`).
   This is the one decision for the user. Its cost to the stop-the-world
   theorems is a recheck, not a change of statement.
2. Stages 2-4: the cycle **without minor collections**, with its witness.
   Until stage 5 the page cycle covers fewer runs than his (no `Minor`
   event), and is reported as such.
3. Stage 5: `ppromote`, then the `Minor` events, then stage 6.
4. The tag (23.6) is decided in stage 5.

Nothing here needs akhil's agreement. If his modules change upstream, our
copies (23.2, 23.6) do not follow automatically. Each copied lemma names its
original, so a diff can be checked.
