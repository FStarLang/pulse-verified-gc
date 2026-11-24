/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepRun - sweeping one large run
/// ---------------------------------------------------------------------------
///
/// `sweep_run g pm h fp` sweeps the large run at page `h`.  It is the
/// fallback of docs/pages-allocator-proof-plan.md §8: a fresh run sweep in
/// the manner of `GC.Spec.SweepPar.segment_correct` (parallel-sweep), with
/// a frame, rather than #46's coalescing sweep restricted to a run.
///
///   - The layout is `GC.Spec.Pages.RunList.fin`: survivors stay where they
///     are; each stretch of dead and free blocks becomes one free block; a
///     free block that holds whole pages gives them back as free pages.
///   - The heap gets the layout's headers (`wr_all`): a survivor's header
///     made white, a blue header on every free block and free page.  A free
///     block of at least `lg_min` words is listed: its first field links to
///     the next listed block, the last one to `fp`; the new head is returned.
///   - The page map (`GC.Spec.Pages.RunMap.new_map`): the free pages become
///     `Free`, and each stretch of pages between them a swept run of its own.
///
/// Only the run's words and its pages' entries change.  `sweep_run_correct`
/// proves `sweep_run_meets sweep_run` (`GC.Spec.Pages.Theorems`).

module GC.Spec.Pages.SweepRun

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Theorems
open GC.Spec.Pages.Blk
open GC.Spec.Pages.RunList
open GC.Spec.Pages.RunMap

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module B = GC.Spec.Pages.Blocks

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// A free block the large lists hold.
let listable (b: blk) : bool =
  b.t = Dead && b.w >= lg_min && b.at % 8 = 0 && b.at + 8 < heap_size

let obj_at (b: blk{listable b}) : obj_addr = mk_hp_addr (b.at + 8)

/// The first listed block from `bs` on, or `fp`.
let rec lhead (bs: list blk) (fp: U64.t) : Tot U64.t (decreases bs) =
  match bs with
  | [] -> fp
  | b :: bs' -> if listable b then (obj_at b <: U64.t) else lhead bs' fp

let rec listed (bs: list blk) : Tot (list obj_addr) (decreases bs) =
  match bs with
  | [] -> []
  | b :: bs' -> if listable b then obj_at b :: listed bs' else listed bs'

/// The header the sweep writes at a block.
let hval (g0: heap) (b: blk) : U64.t =
  if b.t = Live then colorHeader (hdr g0 b.at) White
  else if b.w <= pow2 54 then B.bhdr b.w else 0UL

/// Write the layout `bs` into `g0`.
let rec wr_all (g0: heap) (bs: list blk) (fp: U64.t) : GTot heap (decreases bs) =
  match bs with
  | [] -> g0
  | b :: bs' ->
    let g2 = B.wr (wr_all g0 bs' fp) b.at (hval g0 b) in
    if listable b then B.wr g2 (b.at + 8) (lhead bs' fp) else g2

let sweep_run (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
  : GTot (heap & page_map & U64.t)
  = match (entry pm h).kind with
    | LargeHead n ->
      let fs = fin g (page_base h) (page_base (h + n)) in
      (wr_all g fs fp, new_map pm fs h n, lhead fs fp)
    | _ -> (g, pm, fp)

/// ---------------------------------------------------------------------------
/// Reading the written layout back
/// ---------------------------------------------------------------------------

/// The value written at `x`, if any.
let rec val_at (g0: heap) (bs: list blk) (fp: U64.t) (x: nat) : Tot (option U64.t) (decreases bs) =
  match bs with
  | [] -> None
  | b :: bs' ->
    if x = b.at then Some (hval g0 b)
    else if listable b && x = b.at + 8 then Some (lhead bs' fp)
    else val_at g0 bs' fp x

let rec wr_all_read (g0: heap) (bs: list blk) (fp: U64.t) (x: hp_addr)
  : Lemma (ensures read_word (wr_all g0 bs fp) x ==
                   (match val_at g0 bs fp (U64.v x) with Some v -> v | None -> read_word g0 x))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      wr_all_read g0 bs' fp x;
      let g2 = B.wr (wr_all g0 bs' fp) b.at (hval g0 b) in
      B.wr_read (wr_all g0 bs' fp) b.at (hval g0 b) x;
      if listable b then B.wr_read g2 (b.at + 8) (lhead bs' fp) x

let lg_min_ge2 () : Lemma (lg_min >= 3)
  = cls_bounds (n_cls - 1)

/// Nothing is written at `x` when no block starts there and no listed block
/// has its link there.
let rec va_none (g0: heap) (bs: list blk) (fp: U64.t) (x: nat)
  : Lemma (requires forall (c: blk). L.mem c bs ==> x <> c.at /\ ~(listable c /\ x == c.at + 8))
          (ensures val_at g0 bs fp x == None)
          (decreases bs)
  = match bs with
    | [] -> ()
    | _ :: bs' -> va_none g0 bs' fp x

let rec va_start (g0: heap) (bs: list blk) (a e: nat) (fp: U64.t) (b: blk)
  : Lemma (requires contig bs a e /\ L.mem b bs)
          (ensures val_at g0 bs fp b.at == Some (hval g0 b))
          (decreases bs)
  = match bs with
    | c :: r ->
      if c = b then ()
      else begin
        lg_min_ge2 ();
        contig_mem r (bend c) e b;
        va_start g0 r (bend c) e fp b
      end

/// The suffix after a block.
let from_cons (c: blk) (r: list blk) (x: nat)
  : Lemma (requires c.at < x) (ensures from_ (c :: r) x == from_ r x)
  = ()

let from_next (r: list blk) (x e: nat)
  : Lemma (requires contig r x e) (ensures from_ r x == r)
  = ()

let rec va_link (g0: heap) (bs: list blk) (a e: nat) (fp: U64.t) (b: blk)
  : Lemma (requires contig bs a e /\ L.mem b bs /\ listable b)
          (ensures val_at g0 bs fp (b.at + 8) == Some (lhead (from_ bs (bend b)) fp))
          (decreases bs)
  = lg_min_ge2 ();
    match bs with
    | c :: r ->
      if c = b then begin
        from_next r (bend c) e;
        from_cons c r (bend c)
      end else begin
        contig_mem r (bend c) e b;
        from_cons c r (bend b);
        va_link g0 r (bend c) e fp b
      end

/// Nothing is written inside a survivor, nor outside the layout.
let va_inner (g0: heap) (bs: list blk) (a e: nat) (fp: U64.t) (b: blk) (x: nat)
  : Lemma (requires contig bs a e /\ L.mem b bs /\ b.t = Live /\ b.at < x /\ x < bend b)
          (ensures val_at g0 bs fp x == None)
  = lg_min_ge2 ();
    let aux (c: blk) : Lemma (L.mem c bs ==> x <> c.at /\ ~(listable c /\ x == c.at + 8))
      = if L.mem c bs then begin
          contig_order bs a e b c;
          contig_order bs a e c b
        end
    in
    FStar.Classical.forall_intro aux;
    va_none g0 bs fp x

let va_out (g0: heap) (bs: list blk) (a e: nat) (fp: U64.t) (x: nat)
  : Lemma (requires contig bs a e /\ (x < a \/ x >= e))
          (ensures val_at g0 bs fp x == None)
  = lg_min_ge2 ();
    let aux (c: blk) : Lemma (L.mem c bs ==> x <> c.at /\ ~(listable c /\ x == c.at + 8))
      = if L.mem c bs then contig_mem bs a e c
    in
    FStar.Classical.forall_intro aux;
    va_none g0 bs fp x

/// ---------------------------------------------------------------------------
/// The list of the layout's listed blocks
/// ---------------------------------------------------------------------------

let rec listed_mem (bs: list blk) (a e: nat) (y: obj_addr)
  : Lemma (requires contig bs a e)
          (ensures L.mem y (listed bs) <==>
                   (match blk_at bs (U64.v y - 8) with Some c -> listable c | None -> false))
          (decreases bs)
  = match bs with
    | [] -> ()
    | c :: r ->
      listed_mem r (bend c) e y;
      blk_at_spec r (bend c) e c.at;
      (match blk_at r c.at with
       | Some b -> contig_mem r (bend c) e b
       | None -> ());
      if listable c then begin
        assert (U64.v (obj_at c) == c.at + 8);
        if c.at = U64.v y - 8 then U64.v_inj (obj_at c) y
      end

let rec listed_norep (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e) (ensures L.noRepeats (listed bs)) (decreases bs)
  = match bs with
    | [] -> ()
    | c :: r ->
      listed_norep r (bend c) e;
      if listable c then begin
        listed_mem r (bend c) e (obj_at c);
        assert (U64.v (obj_at c) - 8 == c.at);
        blk_at_spec r (bend c) e c.at;
        match blk_at r c.at with
        | Some b -> contig_mem r (bend c) e b
        | None -> ()
      end

let rec lchain_of (g': heap) (bs: list blk) (a e: nat) (fp: U64.t)
  : Lemma (requires contig bs a e /\
                    (forall (c: blk). L.mem c bs /\ listable c ==>
                       read_word g' (obj_at c <: hp_addr) == lhead (from_ bs (bend c)) fp))
          (ensures lchain g' (lhead bs fp) (listed bs) fp)
          (decreases bs)
  = match bs with
    | [] -> ()
    | c :: r ->
      let tl (d: blk) : Lemma (L.mem d r ==> from_ bs (bend d) == from_ r (bend d))
        = if L.mem d r then (contig_mem r (bend c) e d; from_cons c r (bend d))
      in
      FStar.Classical.forall_intro tl;
      lchain_of g' r (bend c) e fp;
      if listable c then begin
        from_cons c r (bend c);
        from_next r (bend c) e
      end

/// ---------------------------------------------------------------------------
/// The run's layout
/// ---------------------------------------------------------------------------

/// The run's bounds.
let run_bounds (pm: page_map) (h: nat{h < n_pages})
  : Lemma (requires map_ok pm /\ LargeHead? (entry pm h).kind)
          (ensures (let n = run_len (entry pm h).kind in
                    h + n <= n_pages /\ page_base h >= z /\ page_base h % 8 == 0 /\
                    page_base h < page_base (h + n) /\ page_base (h + n) <= heap_size /\
                    page_base (h + n) % 8 == 0))
  = let n = run_len (entry pm h).kind in
    assert (run_ok pm h);
    page_base_aligned h;
    page_base_aligned (h + n);
    page_base_lt h (h + n);
    page_base_mono (h + n) n_pages

/// What the swept heap holds at each block of the layout.
let blk_hdr (g: heap) (fs: list blk) (s e: nat) (fp: U64.t) (c: blk)
  : Lemma (requires contig fs s e /\ e <= heap_size /\ s % 8 == 0 /\ L.mem c fs /\
                    (c.t = Live ==> words_at g c.at == c.w))
          (ensures (let g' = wr_all g fs fp in
                    c.at % 8 == 0 /\ c.at < heap_size /\ bend c <= heap_size /\
                    hdr g' c.at == hval g c /\ words_at g' c.at == c.w /\
                    (c.t = Live ==> color_at g' c.at == White) /\
                    (c.t <> Live ==> color_at g' c.at == Blue)))
  = let g' = wr_all g fs fp in
    contig_aligned fs s e;
    contig_mem fs s e c;
    va_start g fs s e fp c;
    wr_all_read g fs fp (mk_hp_addr c.at);
    if c.t = Live then begin
      colorHeader_getColor (hdr g c.at) White;
      colorHeader_preserves_wosize (hdr g c.at) White
    end else begin
      assert (c.w * 8 <= heap_size);
      FStar.Math.Lemmas.pow2_plus 54 3;
      assert_norm (pow2 3 == 8);
      B.bhdr_spec c.w
    end

/// The colour the swept heap holds at each block of the layout, and the size
/// of a free one.
let blk_color (g: heap) (fs: list blk) (s e: nat) (fp: U64.t) (c: blk)
  : Lemma (requires contig fs s e /\ e <= heap_size /\ s % 8 == 0 /\ L.mem c fs)
          (ensures (let g' = wr_all g fs fp in
                    (c.t = Live ==> color_at g' c.at == White) /\
                    (c.t <> Live ==> color_at g' c.at == Blue /\ words_at g' c.at == c.w)))
  = let g' = wr_all g fs fp in
    contig_aligned fs s e;
    contig_mem fs s e c;
    va_start g fs s e fp c;
    wr_all_read g fs fp (mk_hp_addr c.at);
    if c.t = Live then colorHeader_getColor (hdr g c.at) White
    else begin
      FStar.Math.Lemmas.pow2_plus 54 3;
      assert_norm (pow2 3 == 8);
      B.bhdr_spec c.w
    end

/// The links of the listed blocks.
let links_ok (g: heap) (fs: list blk) (s e: nat) (fp: U64.t)
  : Lemma (requires contig fs s e)
          (ensures forall (c: blk). L.mem c fs /\ listable c ==>
                     read_word (wr_all g fs fp) (obj_at c <: hp_addr) == lhead (from_ fs (bend c)) fp)
  = let links (c: blk)
      : Lemma (L.mem c fs /\ listable c ==>
               read_word (wr_all g fs fp) (obj_at c <: hp_addr) == lhead (from_ fs (bend c)) fp)
      = if L.mem c fs && listable c then begin
          va_link g fs s e fp c;
          wr_all_read g fs fp (obj_at c <: hp_addr)
        end
    in
    FStar.Classical.forall_intro links

let hdrs_after (g: heap) (fs: list blk) (s e: nat) (fp: U64.t)
  : Lemma (requires contig fs s e /\ e <= heap_size /\ s % 8 == 0 /\
                    (forall (c: blk). L.mem c fs /\ c.t = Live ==> words_at g c.at == c.w))
          (ensures hdrs_ok (wr_all g fs fp) fs)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (blk_hdr g fs s e fp))

/// The setting of the proof: a marked run and its layout.
let run_ctx (g: heap) (pm: page_map) (h: nat{h < n_pages}) : prop =
  marked_run g pm h

let layout_facts (g: heap) (pm: page_map) (h: nat{h < n_pages})
  : Lemma (requires run_ctx g pm h)
          (ensures (let n = run_len (entry pm h).kind in
                    let s = page_base h in
                    let e = page_base (h + n) in
                    let fs = fin g s e in
                    h + n <= n_pages /\ s >= z /\ s % 8 == 0 /\ s < e /\ e <= heap_size /\
                    steps_to g s e /\
                    contig (olds g s e) s e /\ hdrs_ok g (olds g s e) /\
                    (forall (b: blk). L.mem b (olds g s e) ==>
                       b.t <> Page /\ (b.t = Live <==> color_at g b.at == Black)) /\
                    contig fs s e /\ nodd fs /\
                    (forall (c: blk). L.mem c fs ==>
                       (c.t = Live ==> L.mem c (olds g s e)) /\
                       (c.t <> Live ==> piece_ok c)) /\
                    (forall (c: blk). L.mem c (olds g s e) /\ c.t = Live ==> L.mem c fs) /\
                    (forall (c: blk). L.mem c fs /\ c.t = Live ==> words_at g c.at == c.w)))
  = run_bounds pm h;
    let n = run_len (entry pm h).kind in
    let s = page_base h in
    let e = page_base (h + n) in
    olds_spec g s e;
    fin_spec g s e

/// The layout's facts the page-map proofs need, alone.
let layout_lite (g: heap) (pm: page_map) (h: nat{h < n_pages})
  : Lemma (requires run_ctx g pm h)
          (ensures (let n = run_len (entry pm h).kind in
                    let s = page_base h in
                    let e = page_base (h + n) in
                    let fs = fin g s e in
                    map_ok pm /\ (entry pm h).kind == LargeHead n /\
                    h + n <= n_pages /\ s >= z /\ s % 8 == 0 /\ s < e /\ e <= heap_size /\
                    contig fs s e /\
                    (forall (c: blk). L.mem c fs ==> (c.t <> Live ==> piece_ok c))))
  = layout_facts g pm h

/// ---------------------------------------------------------------------------
/// Pages of the layout
/// ---------------------------------------------------------------------------

/// A block of the layout that is not a free page lies in a page that is not
/// free.
let not_freed_at (fs: list blk) (s e: nat) (c: blk)
  : Lemma (requires contig fs s e /\ L.mem c fs /\ c.t <> Page /\ c.at >= z)
          (ensures not (freed fs (pg_floor c.at)))
  = let j = pg_floor c.at in
    pg_floor_spec c.at;
    page_base_succ j;
    if freed fs j then begin
      contig_order fs s e (page_blk j) c;
      contig_order fs s e c (page_blk j)
    end

/// A page start of the run that is the run's start or follows a free page is
/// a cut of the layout; so is one that is a free page.
let cut_after (fs: list blk) (s e: nat) (j: nat)
  : Lemma (requires contig fs s e /\ freed fs j /\ page_base (j + 1) <= e)
          (ensures cut fs e (page_base (j + 1)))
  = page_base_succ j;
    if page_base (j + 1) < e then contig_next fs s e (page_blk j)

let cut_at (fs: list blk) (s e: nat) (j: nat)
  : Lemma (requires contig fs s e /\ freed fs j)
          (ensures cut fs e (page_base j))
  = blk_at_mem fs s e (page_blk j)

/// A layout block in pages `j .. j + m - 1`, none of them free, is not a
/// free page.
let not_page_in (fs: list blk) (s e: nat) (j m: nat) (c: blk)
  : Lemma (requires contig fs s e /\ L.mem c fs /\ (c.t <> Live ==> piece_ok c) /\
                    page_base j <= c.at /\ c.at < page_base (j + m) /\
                    (forall (k: nat). j <= k /\ k < j + m ==> not (freed fs k)))
          (ensures c.t <> Page)
  = if c.t = Page then begin
      let k = pg_floor c.at in
      assert (c == page_blk k);
      page_base_lt j k;
      page_base_lt k (j + m)
    end

/// The swept clause (L7) at one block of the layout in pages
/// `j .. j + m - 1`, none of them free.
let next_blk (fs: list blk) (s e: nat) (j m: nat) (c: blk)
  : Lemma (requires contig fs s e /\ nodd fs /\
                    (forall (c: blk). L.mem c fs ==> (c.t <> Live ==> piece_ok c)) /\
                    L.mem c fs /\ c.t = Dead /\ page_base j <= c.at /\ bend c < page_base (j + m) /\
                    page_base (j + m) <= e /\
                    (forall (k: nat). j <= k /\ k < j + m ==> not (freed fs k)))
          (ensures Some? (blk_at fs (bend c)) /\
                   (let c' = Some?.v (blk_at fs (bend c)) in L.mem c' fs /\ c'.t = Live /\ c'.at == bend c))
  = contig_next fs s e c;
    blk_at_spec fs s e (bend c);
    let c' = Some?.v (blk_at fs (bend c)) in
    assert (c'.at == bend c);
    assert (page_base j <= c'.at /\ c'.at < page_base (j + m));
    not_page_in fs s e j m c';
    nodd_mem fs s e c c'

let l7_blk (g: heap) (fs: list blk) (s e: nat) (fp: U64.t) (j m: nat) (c: blk)
  : Lemma (requires contig fs s e /\ nodd fs /\ s % 8 == 0 /\ e <= heap_size /\
                    (forall (c: blk). L.mem c fs ==> (c.t <> Live ==> piece_ok c)) /\
                    (forall (c: blk). L.mem c fs /\ c.t = Live ==> words_at g c.at == c.w) /\
                    L.mem c fs /\ page_base j <= c.at /\ c.at < page_base (j + m) /\
                    page_base (j + m) <= e /\
                    (forall (k: nat). j <= k /\ k < j + m ==> not (freed fs k)))
          (ensures GC.Spec.Pages.Run.l7_at (wr_all g fs fp) j m c.at)
  = let g' = wr_all g fs fp in
    let y = page_base (j + m) in
    not_page_in fs s e j m c;
    blk_hdr g fs s e fp c;
    assert (words_at g' c.at == c.w);
    if c.t = Dead then begin
      assert (piece_ok c);
      assert (no_page c.at (bend c));
      assert (color_at g' c.at == Blue);
      if bend c < y then begin
        next_blk fs s e j m c;
        let c' = Some?.v (blk_at fs (bend c)) in
        blk_hdr g fs s e fp c';
        assert (color_at g' (bend c) =!= Blue)
      end
    end

/// The layout in pages `j .. j + m - 1` is one swept run.
let new_run_ok (g: heap) (fs: list blk) (s e: nat) (fp: U64.t) (j m: nat)
  : Lemma (requires contig fs s e /\ nodd fs /\ s % 8 == 0 /\ s >= z /\ e <= heap_size /\
                    (forall (c: blk). L.mem c fs ==> (c.t <> Live ==> piece_ok c)) /\
                    (forall (c: blk). L.mem c fs /\ c.t = Live ==> words_at g c.at == c.w) /\
                    cut fs e (page_base j) /\ cut fs e (page_base (j + m)) /\
                    s <= page_base j /\ page_base j < page_base (j + m) /\ page_base (j + m) <= e /\
                    (forall (k: nat). j <= k /\ k < j + m ==> not (freed fs k)))
          (ensures (let g' = wr_all g fs fp in
                    steps_to g' (page_base j) (page_base (j + m)) /\
                    (forall (a: nat). run_block g' j m a ==> GC.Spec.Pages.Run.l7_at g' j m a)))
  = let g' = wr_all g fs fp in
    let x = page_base j in
    let y = page_base (j + m) in
    slice_spec fs s e x y;
    let sl = slice fs x y in
    hdrs_after g fs s e fp;
    tiles_steps g' sl x y;
    let blk_l7 (a: nat)
      : Lemma (requires run_block g' j m a)
              (ensures GC.Spec.Pages.Run.l7_at g' j m a)
      = blk_at_spec sl x y a;
        let c = Some?.v (blk_at sl a) in
        l7_blk g fs s e fp j m c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires blk_l7)

/// ---------------------------------------------------------------------------
/// The clauses of `sweep_run_ok`
/// ---------------------------------------------------------------------------

let s_of (pm: page_map) (h: nat{h < n_pages}) : nat = page_base h
let e_of (pm: page_map) (h: nat{h < n_pages /\ LargeHead? (entry pm h).kind}) : nat =
  page_base (h + run_len (entry pm h).kind)

let lay (g: heap) (pm: page_map) (h: nat{h < n_pages /\ LargeHead? (entry pm h).kind}) : list blk =
  fin g (s_of pm h) (e_of pm h)

let g_of (g: heap) (pm: page_map) (h: nat{h < n_pages /\ LargeHead? (entry pm h).kind}) (fp: U64.t) : GTot heap =
  wr_all g (lay g pm h) fp

/// The layout lies end to end over the run.
let lay_contig (g: heap) (pm: page_map) (h: nat{h < n_pages})
  : Lemma (requires run_ctx g pm h)
          (ensures contig (lay g pm h) (s_of pm h) (e_of pm h) /\ s_of pm h % 8 == 0 /\
                   e_of pm h <= heap_size)
  = layout_facts g pm h

/// The swept heap's walk over the run, and its blocks.
let walk_after (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
  : Lemma (requires run_ctx g pm h)
          (ensures (let s = s_of pm h in
                    let e = e_of pm h in
                    let g' = g_of g pm h fp in
                    steps_to g' s e /\
                    (forall (x: nat). (steps_to g' s x /\ x < e) <==> Some? (blk_at (lay g pm h) x))))
  = layout_facts g pm h;
    let s = s_of pm h in
    let e = e_of pm h in
    hdrs_after g (lay g pm h) s e fp;
    tiles_steps (g_of g pm h fp) (lay g pm h) s e

/// The walk over the marked run, and its blocks.
let walk_before (g: heap) (pm: page_map) (h: nat{h < n_pages})
  : Lemma (requires run_ctx g pm h)
          (ensures (let s = s_of pm h in
                    let e = e_of pm h in
                    forall (x: nat). (steps_to g s x /\ x < e) <==> Some? (blk_at (olds g s e) x)))
  = layout_facts g pm h;
    tiles_steps g (olds g (s_of pm h) (e_of pm h)) (s_of pm h) (e_of pm h)

/// A survivor is kept, made white.
let survivor_at (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t) (a: nat)
  : Lemma (requires run_ctx g pm h /\ run_survivor g h (run_len (entry pm h).kind) a)
          (ensures steps_to (g_of g pm h fp) (s_of pm h) a /\ whitened_at g (g_of g pm h fp) a)
  = layout_facts g pm h;
    walk_before g pm h;
    walk_after g pm h fp;
    let s = s_of pm h in
    let e = e_of pm h in
    let os = olds g s e in
    let fs = lay g pm h in
    let g' = g_of g pm h fp in
    blk_at_spec os s e a;
    let b = Some?.v (blk_at os a) in
    blk_at_mem fs s e b;
    blk_hdr g fs s e fp b;
    let inner (x: hp_addr)
      : Lemma (requires a < U64.v x /\ U64.v x < a + words_at g a * 8)
              (ensures read_word g' x == read_word g x)
      = va_inner g fs s e fp b (U64.v x);
        wr_all_read g fs fp x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires inner)

/// A block of the swept run that is not free was a survivor.
let freed_at (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t) (b: nat)
  : Lemma (requires run_ctx g pm h /\ steps_to (g_of g pm h fp) (s_of pm h) b /\ b < e_of pm h /\
                    color_at (g_of g pm h fp) b =!= Blue)
          (ensures run_survivor g h (run_len (entry pm h).kind) b)
  = layout_facts g pm h;
    walk_before g pm h;
    walk_after g pm h fp;
    let s = s_of pm h in
    let e = e_of pm h in
    let fs = lay g pm h in
    blk_at_spec fs s e b;
    let c = Some?.v (blk_at fs b) in
    blk_hdr g fs s e fp c;
    blk_at_mem (olds g s e) s e c

/// Nothing outside the run is written.
let frame_after (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t) (x: hp_addr)
  : Lemma (requires run_ctx g pm h /\ (U64.v x < s_of pm h \/ U64.v x >= e_of pm h))
          (ensures read_word (g_of g pm h fp) x == read_word g x)
  = layout_facts g pm h;
    va_out g (lay g pm h) (s_of pm h) (e_of pm h) fp (U64.v x);
    wr_all_read g (lay g pm h) fp x

/// A run with no survivor becomes free pages.
let empty_run (g: heap) (pm: page_map) (h: nat{h < n_pages}) (j: nat{j < n_pages})
  : Lemma (requires run_ctx g pm h /\
                    ~(exists (a: nat). run_survivor g h (run_len (entry pm h).kind) a) /\
                    h <= j /\ j < h + run_len (entry pm h).kind)
          (ensures (entry (new_map pm (lay g pm h) h (run_len (entry pm h).kind)) j).kind == Free)
  = layout_facts g pm h;
    walk_before g pm h;
    let n = run_len (entry pm h).kind in
    let s = s_of pm h in
    let e = e_of pm h in
    let os = olds g s e in
    let no_live (c: blk) : Lemma (L.mem c os ==> c.t <> Live)
      = if L.mem c os then begin
          contig_mem os s e c;
          blk_at_mem os s e c;
          if c.t = Live then assert (run_survivor g h n c.at)
        end
    in
    FStar.Classical.forall_intro no_live;
    fin_all_free g h n;
    pages_spec h (h + n);
    assert (freed (lay g pm h) j);
    in_facts pm (lay g pm h) h n j

/// An address of page `j` lies in a swept run exactly when page `j` is a
/// page of a swept run.
let in_page_run (pm: page_map) (j: nat{j < n_pages}) (a: nat)
  : Lemma (requires map_ok pm /\ page_base j <= a /\ a < page_base (j + 1))
          (ensures in_swept_run pm a <==>
                   ((LargeHead? (entry pm j).kind \/ (entry pm j).kind == LargeCont) /\
                    (entry pm j).swept == true))
  = let back (u: nat{u < n_pages})
      : Lemma (requires LargeHead? (entry pm u).kind /\ (entry pm u).swept /\
                        page_base u <= a /\ a < page_base (u + run_len (entry pm u).kind))
              (ensures (LargeHead? (entry pm j).kind \/ (entry pm j).kind == LargeCont) /\
                       (entry pm j).swept == true)
      = page_base_lt u (j + 1);
        page_base_lt j (u + run_len (entry pm u).kind);
        assert (run_ok pm u)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires back);
    if (entry pm j).swept then
      match (entry pm j).kind with
      | LargeHead m ->
        assert (run_ok pm j);
        page_base_lt (j + 1) (j + m);
        assert (in_run pm j j)
      | LargeCont ->
        assert (cont_ok pm j);
        eliminate exists (u: nat{u < n_pages}). u < j /\ in_run pm u j
        with begin
          assert (run_ok pm u);
          page_base_lt u j;
          page_base_lt (j + 1) (u + run_len (entry pm u).kind)
        end
      | _ -> ()

/// The page of a block of the run.
let blk_page (h n: nat) (x: nat)
  : Lemma (requires page_base h <= x /\ x < page_base (h + n))
          (ensures h <= pg_floor x /\ pg_floor x < h + n /\
                   page_base (pg_floor x) <= x /\ x < page_base (pg_floor x + 1))
  = pg_floor_spec x;
    page_base_lt h (pg_floor x + 1);
    page_base_lt (pg_floor x) (h + n)

/// A block of the layout lies in a swept run of the new map exactly when it
/// is not a free page.
let swept_run_at (g: heap) (pm: page_map) (h: nat{h < n_pages}) (c: blk)
  : Lemma (requires run_ctx g pm h /\ L.mem c (lay g pm h))
          (ensures in_swept_run (new_map pm (lay g pm h) h (run_len (entry pm h).kind)) c.at <==>
                   c.t <> Page)
  = layout_lite g pm h;
    let n = run_len (entry pm h).kind in
    let s = s_of pm h in
    let e = e_of pm h in
    let fs = lay g pm h in
    let pm' = new_map pm fs h n in
    new_map_ok pm fs h n;
    contig_mem fs s e c;
    assert (s <= c.at /\ c.at < e);
    assert (s == page_base h /\ e == page_base (h + n));
    blk_page h n c.at;
    let j = pg_floor c.at in
    in_page_run pm' j c.at;
    in_facts pm fs h n j;
    if c.t = Page then assert (c == page_blk j)
    else not_freed_at fs s e c

let obj_hd (y: obj_addr) : Lemma ((U64.v y - 8) % 8 == 0 /\ U64.v y - 8 + 8 < heap_size) = ()

/// A listed block, as the specification states it.
let listed_at (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t) (y: obj_addr)
  : Lemma (requires run_ctx g pm h)
          (ensures (let n = run_len (entry pm h).kind in
                    let s = s_of pm h in
                    let e = e_of pm h in
                    let fs = lay g pm h in
                    let g' = g_of g pm h fp in
                    L.mem y (listed fs) <==>
                    (s <= U64.v y - 8 /\ U64.v y - 8 < e /\ steps_to g' s (U64.v y - 8) /\
                     color_at g' (U64.v y - 8) == Blue /\ words_at g' (U64.v y - 8) >= lg_min /\
                     in_swept_run (new_map pm fs h n) (U64.v y - 8))))
  = lay_contig g pm h;
    walk_after g pm h fp;
    let s = s_of pm h in
    let e = e_of pm h in
    let fs = lay g pm h in
    let g' = g_of g pm h fp in
    let x = U64.v y - 8 in
    listed_mem fs s e y;
    blk_at_spec fs s e x;
    match blk_at fs x with
    | Some c ->
      contig_mem fs s e c;
      blk_color g fs s e fp c;
      swept_run_at g pm h c;
      lg_min_ge2 ();
      assert (steps_to g' s x /\ x < e /\ s <= x);
      obj_hd y;
      assert (listable c <==> (c.t = Dead /\ c.w >= lg_min))
    | None -> ()

/// The listed blocks.
let list_after (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
  : Lemma (requires run_ctx g pm h)
          (ensures (let n = run_len (entry pm h).kind in
                    let s = s_of pm h in
                    let e = e_of pm h in
                    let fs = lay g pm h in
                    let g' = g_of g pm h fp in
                    let pm' = new_map pm fs h n in
                    let xs = listed fs in
                    lchain g' (lhead fs fp) xs fp /\ L.noRepeats xs /\
                    (forall (y: obj_addr).
                       L.mem y xs <==>
                       (s <= U64.v y - 8 /\ U64.v y - 8 < e /\ steps_to g' s (U64.v y - 8) /\
                        color_at g' (U64.v y - 8) == Blue /\ words_at g' (U64.v y - 8) >= lg_min /\
                        in_swept_run pm' (U64.v y - 8)))))
  = layout_lite g pm h;
    let s = s_of pm h in
    let e = e_of pm h in
    let fs = lay g pm h in
    links_ok g fs s e fp;
    lchain_of (g_of g pm h fp) fs s e fp;
    listed_norep fs s e;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (listed_at g pm h fp))

/// The layout's facts a new run's proof needs.
let layout_run (g: heap) (pm: page_map) (h: nat{h < n_pages})
  : Lemma (requires run_ctx g pm h)
          (ensures (let s = s_of pm h in
                    let e = e_of pm h in
                    let fs = lay g pm h in
                    contig fs s e /\ nodd fs /\ s % 8 == 0 /\ s >= z /\ e <= heap_size /\
                    s == page_base h /\ e == page_base (h + run_len (entry pm h).kind) /\
                    (forall (c: blk). L.mem c fs ==> (c.t <> Live ==> piece_ok c)) /\
                    (forall (c: blk). L.mem c fs /\ c.t = Live ==> words_at g c.at == c.w)))
  = layout_facts g pm h

/// A free page of the new map.
let page_free_after (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t) (j: nat{j < n_pages})
  : Lemma (requires run_ctx g pm h /\ h <= j /\ j < h + run_len (entry pm h).kind /\
                    (entry (new_map pm (lay g pm h) h (run_len (entry pm h).kind)) j).kind == Free)
          (ensures free_page_shape (g_of g pm h fp) j)
  = lay_contig g pm h;
    let n = run_len (entry pm h).kind in
    let fs = lay g pm h in
    free_facts pm fs h n j;
    blk_color g fs (s_of pm h) (e_of pm h) fp (page_blk j);
    contig_aligned fs (s_of pm h) (e_of pm h);
    contig_mem fs (s_of pm h) (e_of pm h) (page_blk j)

/// A new run begins and ends at cuts of the layout.
let run_cuts (fs: list blk) (s e: nat) (h n j m: nat)
  : Lemma (requires contig fs s e /\ s == page_base h /\ e == page_base (h + n) /\
                    h <= j /\ j + m <= h + n /\ m > 0 /\
                    (j = h \/ freed fs (j - 1)) /\ (j + m = h + n \/ freed fs (j + m)))
          (ensures cut fs e (page_base j) /\ cut fs e (page_base (j + m)) /\
                   s <= page_base j /\ page_base j < page_base (j + m) /\ page_base (j + m) <= e)
  = page_base_lt h j;
    page_base_lt j (j + m);
    page_base_lt (j + m) (h + n);
    if j = h then contig_first fs s e
    else begin
      page_base_lt (j - 1) (h + n);
      cut_after fs s e (j - 1)
    end;
    if j + m < h + n then cut_at fs s e (j + m)

/// The new run at page `j` has its shape and its swept clause.
let head_run (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t) (j m: nat)
  : Lemma (requires run_ctx g pm h /\ h <= j /\ j + m <= h + run_len (entry pm h).kind /\ m > 0 /\
                    (j = h \/ freed (lay g pm h) (j - 1)) /\
                    (j + m = h + run_len (entry pm h).kind \/ freed (lay g pm h) (j + m)) /\
                    (forall (k: nat). j <= k /\ k < j + m ==> not (freed (lay g pm h) k)))
          (ensures (let g' = g_of g pm h fp in
                    steps_to g' (page_base j) (page_base (j + m)) /\
                    (forall (a: nat). run_block g' j m a ==> GC.Spec.Pages.Run.l7_at g' j m a)))
  = layout_run g pm h;
    let n = run_len (entry pm h).kind in
    let fs = lay g pm h in
    run_cuts fs (s_of pm h) (e_of pm h) h n j m;
    new_run_ok g fs (s_of pm h) (e_of pm h) fp j m

/// A head of the new map.
let page_head_after (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t) (j: nat{j < n_pages})
  : Lemma (requires run_ctx g pm h /\ h <= j /\ j < h + run_len (entry pm h).kind /\
                    LargeHead? (entry (new_map pm (lay g pm h) h (run_len (entry pm h).kind)) j).kind)
          (ensures (let n = run_len (entry pm h).kind in
                    let pm' = new_map pm (lay g pm h) h n in
                    let m = run_len (entry pm' j).kind in
                    j + m <= h + n /\ run_shape (g_of g pm h fp) j m /\
                    run_swept_ok (g_of g pm h fp) pm' j))
  = let n = run_len (entry pm h).kind in
    let fs = lay g pm h in
    head_facts pm fs h n j;
    in_facts pm fs h n j;
    head_run g pm h fp j (run_len (entry (new_map pm fs h n) j).kind)

/// The run's pages.
let pages_after (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t) (j: nat{j < n_pages})
  : Lemma (requires run_ctx g pm h /\ h <= j /\ j < h + run_len (entry pm h).kind)
          (ensures (let n = run_len (entry pm h).kind in
                    let fs = lay g pm h in
                    let g' = g_of g pm h fp in
                    let pm' = new_map pm fs h n in
                    (entry pm' j).swept == true /\
                    (match (entry pm' j).kind with
                     | Free -> free_page_shape g' j
                     | LargeHead m -> j + m <= h + n /\ run_shape g' j m /\ run_swept_ok g' pm' j
                     | LargeCont -> (exists (u: nat{u < n_pages}). h <= u /\ u < j /\ in_run pm' u j)
                     | Pool _ -> False)))
  = layout_lite g pm h;
    let n = run_len (entry pm h).kind in
    let fs = lay g pm h in
    let pm' = new_map pm fs h n in
    in_facts pm fs h n j;
    match (entry pm' j).kind with
    | Free -> page_free_after g pm h fp j
    | LargeHead m -> page_head_after g pm h fp j
    | LargeCont -> cont_head pm fs h n j
    | Pool _ -> ()

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

let sweep_run_ok_at (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
  : Lemma (requires marked_run g pm h)
          (ensures (let (g', pm', fp') = sweep_run g pm h fp in sweep_run_ok g pm h fp g' pm' fp'))
  = let n = run_len (entry pm h).kind in
    let fs = lay g pm h in
    layout_facts g pm h;
    new_map_ok pm fs h n;
    walk_after g pm h fp;
    list_after g pm h fp;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (frame_after g pm h fp));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (pages_after g pm h fp));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (survivor_at g pm h fp));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (freed_at g pm h fp));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (empty_run g pm h))

/// **The run sweep meets its specification.**
let sweep_run_correct () : Lemma (sweep_run_meets sweep_run)
  = let aux (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
      : Lemma (marked_run g pm h ==>
               (let (g', pm', fp') = sweep_run g pm h fp in sweep_run_ok g pm h fp g' pm' fp'))
      = FStar.Classical.move_requires (sweep_run_ok_at g pm h) fp
    in
    FStar.Classical.forall_intro_4 aux
