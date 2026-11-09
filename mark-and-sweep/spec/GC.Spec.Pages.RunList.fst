/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.RunList - the run sweep as lists of blocks
/// ---------------------------------------------------------------------------
///
/// The large-run sweep is computed in three steps on lists of blocks
/// (`GC.Spec.Pages.Blk`), all from the heap the mark leaves:
///   1. `olds`: the blocks the walk finds in the run; a black block is a
///      survivor (`Live`), every other one is dead (`Dead`);
///   2. `merge`: each stretch of dead blocks becomes one dead block, so no
///      two dead blocks are adjacent; it never crosses the run's ends;
///   3. `split`: a dead block that holds whole pages is cut at them: the
///      whole pages become free pages (`Page`), and what is left on either
///      side, if anything, stays a dead block, which then holds no whole
///      page.
/// `fin` is the result.  `GC.Spec.Pages.SweepRun` writes it into the heap
/// and derives the new page map from its free pages.

module GC.Spec.Pages.RunList

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Blk

module U64 = FStar.UInt64
module L = FStar.List.Tot
module R = GC.Spec.Pages.Replace

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let z : nat = U64.v zero_addr

/// ---------------------------------------------------------------------------
/// 1. The blocks of the run
/// ---------------------------------------------------------------------------

let rec olds (g: heap) (a e: nat) : Tot (list blk) (decreases (if a < e then e - a else 0)) =
  if a >= e then []
  else begin
    let w = words_at g a in
    if a + w * 8 > e then []
    else { at = a; w = w; t = (if color_at g a = Black then Live else Dead) } :: olds g (a + w * 8) e
  end

let rec olds_spec (g: heap) (a e: nat)
  : Lemma (requires steps_to g a e)
          (ensures contig (olds g a e) a e /\ hdrs_ok g (olds g a e) /\
                   (forall (b: blk). L.mem b (olds g a e) ==>
                      b.t <> Page /\ (b.t = Live <==> color_at g b.at == Black)))
          (decreases (if a < e then e - a else 0))
  = if a >= e then steps_to_le g a e
    else begin
      steps_to_le g a e;
      let ha = mk_hp_addr a in
      steps_to_next g ha e;
      R.block_bytes_words g a;
      olds_spec g (a + words_at g a * 8) e
    end

/// ---------------------------------------------------------------------------
/// No two adjacent dead blocks
/// ---------------------------------------------------------------------------

let rec nodd (bs: list blk) : Tot bool (decreases bs) =
  match bs with
  | x :: y :: r -> not (x.t = Dead && y.t = Dead) && nodd (y :: r)
  | _ -> true

let hd_dead (l: list blk) : bool = match l with x :: _ -> x.t = Dead | [] -> false

let rec last_dead (l: list blk) : Tot bool (decreases l) =
  match l with
  | [] -> false
  | [x] -> x.t = Dead
  | _ :: r -> last_dead r

let rec last_dead_mem (l: list blk)
  : Lemma (requires last_dead l) (ensures exists (c: blk). L.mem c l /\ c.t = Dead) (decreases l)
  = match l with
    | [x] -> ()
    | _ :: r -> last_dead_mem r

#push-options "--fuel 2"
let rec nodd_append (l1 l2: list blk)
  : Lemma (requires nodd l1 /\ nodd l2 /\ ~(last_dead l1 /\ hd_dead l2))
          (ensures nodd (L.append l1 l2))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | [x] -> ()
    | x :: y :: r -> nodd_append (y :: r) l2

/// Adjacent blocks of a list with no two adjacent dead blocks.
let rec nodd_mem (bs: list blk) (a e: nat) (b1 b2: blk)
  : Lemma (requires contig bs a e /\ nodd bs /\ L.mem b1 bs /\ L.mem b2 bs /\ b2.at == bend b1)
          (ensures not (b1.t = Dead && b2.t = Dead))
          (decreases bs)
  = match bs with
    | x :: r ->
      if b1 = x then begin
        contig_mem r (bend x) e b2;
        (if b2 = x then () else
         match r with
         | y :: _ -> contig_order r (bend x) e y b2)
      end else begin
        contig_mem r (bend x) e b1;
        if b2 = x then ()
        else nodd_mem r (bend x) e b1 b2
      end
#pop-options

/// ---------------------------------------------------------------------------
/// 2. Merging
/// ---------------------------------------------------------------------------

let rec merge (bs: list blk) : Tot (list blk) (decreases bs) =
  match bs with
  | [] -> []
  | b :: bs' ->
    let m = merge bs' in
    if b.t = Live then b :: m
    else match m with
         | c :: m' -> if c.t = Live then { b with t = Dead } :: m
                      else { at = b.at; w = b.w + c.w; t = Dead } :: m'
         | [] -> [{ b with t = Dead }]

#push-options "--fuel 2"
let rec merge_spec (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e)
          (ensures contig (merge bs) a e /\ nodd (merge bs) /\
                   (forall (c: blk). L.mem c (merge bs) ==> c.t = Live \/ c.t = Dead) /\
                   (forall (c: blk). (L.mem c (merge bs) /\ c.t = Live) <==> (L.mem c bs /\ c.t = Live)))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      merge_spec bs' (bend b) e;
      let m = merge bs' in
      if b.t = Live then ()
      else match m with
           | [] -> ()
           | c :: m' -> if c.t = Live then () else ()
#pop-options

/// A run with no survivor merges into one dead block.
#push-options "--fuel 2"
let rec merge_all_dead (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e /\ a + 8 <= e /\ (forall (c: blk). L.mem c bs ==> c.t <> Live))
          (ensures merge bs == [{ at = a; w = (e - a) / 8; t = Dead }] /\ (e - a) % 8 == 0)
          (decreases bs)
  = match bs with
    | b :: bs' ->
      contig_le bs' (bend b) e;
      if bend b = e then begin
        assert (bs' == []);
        FStar.Math.Lemmas.cancel_mul_div b.w 8
      end else begin
        merge_all_dead bs' (bend b) e;
        FStar.Math.Lemmas.lemma_div_exact (e - bend b) 8;
        FStar.Math.Lemmas.cancel_mul_div b.w 8
      end
#pop-options

/// ---------------------------------------------------------------------------
/// Pages of a byte offset
/// ---------------------------------------------------------------------------

/// The first page that starts at or after `x`, and the page `x` lies in.
let pg_ceil (x: nat) : nat = if x <= z then 0 else (x - z + page_bytes - 1) / page_bytes
let pg_floor (x: nat) : nat = if x <= z then 0 else (x - z) / page_bytes

let pg_ceil_spec (x: nat)
  : Lemma (requires x >= z)
          (ensures x <= page_base (pg_ceil x) /\
                   (pg_ceil x > 0 ==> page_base (pg_ceil x - 1) < x))
  = if x = z then ()
    else begin
      let p = pg_ceil x in
      FStar.Math.Lemmas.lemma_div_mod (x - z + page_bytes - 1) page_bytes;
      if p > 0 then FStar.Math.Lemmas.distributivity_sub_left p 1 page_bytes
    end

let pg_floor_spec (x: nat)
  : Lemma (requires x >= z)
          (ensures page_base (pg_floor x) <= x /\ x < page_base (pg_floor x + 1))
  = FStar.Math.Lemmas.lemma_div_mod (x - z) page_bytes;
    FStar.Math.Lemmas.distributivity_add_left (pg_floor x) 1 page_bytes

/// Pages are ordered as their starts.
let page_base_lt (i j: nat)
  : Lemma (page_base i < page_base j <==> i < j)
  = if i < j then FStar.Math.Lemmas.lemma_mult_le_right page_bytes (i + 1) j
    else FStar.Math.Lemmas.lemma_mult_le_right page_bytes j i

let page_base_succ (j: nat)
  : Lemma (page_base (j + 1) == page_base j + page_wsize * 8)
  = FStar.Math.Lemmas.distributivity_add_left j 1 page_bytes

/// A stretch holds no whole page.
let no_page (x y: nat) : prop =
  forall (j: nat). ~(x <= page_base j /\ page_base (j + 1) <= y)

/// No whole page lies between `x` and the first page boundary after it, nor
/// between the last one before `y` and `y`, nor in `[x, y)` when no page
/// boundary is crossed twice.
let no_page_of (x y: nat)
  : Lemma (requires x >= z /\ x <= y /\ pg_ceil x >= pg_floor y)
          (ensures no_page x y)
  = pg_ceil_spec x;
    pg_floor_spec y;
    let aux (j: nat) : Lemma (~(x <= page_base j /\ page_base (j + 1) <= y))
      = if x <= page_base j && page_base (j + 1) <= y then begin
          if pg_ceil x > 0 then page_base_lt (pg_ceil x - 1) j;
          if pg_ceil x = 0 then page_base_lt 0 j;
          page_base_lt j (pg_floor y + 1);
          page_base_lt (pg_floor y) (j + 1)
        end
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// 3. Splitting off whole pages
/// ---------------------------------------------------------------------------

let page_blk (j: nat) : blk = { at = page_base j; w = page_wsize; t = Page }

let rec pages (p q: nat) : Tot (list blk) (decreases (if p < q then q - p else 0)) =
  if p < q then page_blk p :: pages (p + 1) q else []

/// The dead piece before the first whole page, and the one after the last.
let pre_of (r p: nat) : list blk =
  if r + 8 <= page_base p then [{ at = r; w = (page_base p - r) / 8; t = Dead }] else []

let suf_of (q e: nat) : list blk =
  if page_base q + 8 <= e then [{ at = page_base q; w = (e - page_base q) / 8; t = Dead }] else []

let split1 (b: blk) : list blk =
  if b.t <> Dead then [b]
  else begin
    let r = b.at in
    let e = bend b in
    let p = pg_ceil r in
    let q = pg_floor e in
    if r < z || p >= q then [b]
    else L.append (pre_of r p) (L.append (pages p q) (suf_of q e))
  end

let rec split (bs: list blk) : Tot (list blk) (decreases bs) =
  match bs with
  | [] -> []
  | b :: bs' -> L.append (split1 b) (split bs')

#push-options "--fuel 2"
let rec pages_spec (p q: nat)
  : Lemma (requires p <= q)
          (ensures contig (pages p q) (page_base p) (page_base q) /\ nodd (pages p q) /\
                   (forall (c: blk). L.mem c (pages p q) <==> (exists (j: nat). p <= j /\ j < q /\ c == page_blk j)))
          (decreases (q - p))
  = if p < q then begin
      page_base_succ p;
      pages_spec (p + 1) q
    end
#pop-options

/// What a piece of `split1` is.
let piece_ok (c: blk) : prop =
  (c.t = Dead ==> no_page c.at (bend c)) /\
  (c.t = Page ==> c == page_blk (pg_floor c.at) /\ c.at >= z) /\
  c.t <> Live

let pg_floor_base (j: nat)
  : Lemma (pg_floor (page_base j) == j /\ pg_ceil (page_base j) == j /\ page_base j >= z)
  = FStar.Math.Lemmas.cancel_mul_div j page_bytes;
    if j > 0 then begin
      FStar.Math.Lemmas.lemma_div_plus (page_bytes - 1) j page_bytes;
      FStar.Math.Lemmas.small_div (page_bytes - 1) page_bytes
    end

let pages_pieces (p q: nat)
  : Lemma (requires p <= q)
          (ensures (forall (c: blk). L.mem c (pages p q) ==> piece_ok c /\ c.t = Page) /\
                   ~(last_dead (pages p q)) /\ ~(hd_dead (pages p q)))
  = pages_spec p q;
    let aux (c: blk) : Lemma (L.mem c (pages p q) ==> piece_ok c /\ c.t = Page)
      = if L.mem c (pages p q) then
          eliminate exists (j: nat). p <= j /\ j < q /\ c == page_blk j
          with pg_floor_base j
    in
    FStar.Classical.forall_intro aux;
    if last_dead (pages p q) then last_dead_mem (pages p q)

/// Two word-aligned offsets differ by whole words.
let diff8 (x y: nat)
  : Lemma (requires x % 8 == 0 /\ y % 8 == 0 /\ x <= y)
          (ensures ((y - x) / 8) * 8 == y - x /\ (y < x + 8 ==> y == x))
  = FStar.Math.Lemmas.lemma_div_exact x 8;
    FStar.Math.Lemmas.lemma_div_exact y 8;
    FStar.Math.Lemmas.distributivity_sub_left (y / 8) (x / 8) 8;
    FStar.Math.Lemmas.cancel_mul_div (y / 8 - x / 8) 8

/// The piece before page `p` holds no whole page.
#push-options "--fuel 2"
let pre_ok (r p: nat)
  : Lemma (requires r >= z /\ r % 8 == 0 /\ r <= page_base p /\ pg_ceil r == p)
          (ensures contig (pre_of r p) r (page_base p) /\ nodd (pre_of r p) /\
                   (forall (c: blk). L.mem c (pre_of r p) ==> piece_ok c))
  = page_base_aligned p;
    pg_floor_base p;
    diff8 r (page_base p);
    if r + 8 <= page_base p then begin
      no_page_of r (page_base p);
      let c0 : blk = { at = r; w = (page_base p - r) / 8; t = Dead } in
      assert (bend c0 == page_base p);
      assert (pre_of r p == [c0]);
      assert (piece_ok c0)
    end
#pop-options

#push-options "--fuel 2"
let suf_ok (q e: nat)
  : Lemma (requires e % 8 == 0 /\ page_base q <= e /\ pg_floor e == q)
          (ensures contig (suf_of q e) (page_base q) e /\ nodd (suf_of q e) /\
                   (forall (c: blk). L.mem c (suf_of q e) ==> piece_ok c))
  = page_base_aligned q;
    pg_floor_base q;
    diff8 (page_base q) e;
    if page_base q + 8 <= e then begin
      no_page_of (page_base q) e;
      let c0 : blk = { at = page_base q; w = (e - page_base q) / 8; t = Dead } in
      assert (bend c0 == e);
      assert (suf_of q e == [c0]);
      assert (piece_ok c0)
    end
#pop-options

let split_bounds (r e: nat)
  : Lemma (requires r >= z /\ r <= e /\ pg_ceil r < pg_floor e)
          (ensures r <= page_base (pg_ceil r) /\ page_base (pg_ceil r) <= page_base (pg_floor e) /\
                   page_base (pg_floor e) <= e)
  = pg_ceil_spec r;
    pg_floor_spec e;
    page_base_lt (pg_ceil r) (pg_floor e)

#push-options "--fuel 2"
let mem_single (x: blk)
  : Lemma ((forall (c: blk). L.mem c [x] <==> c == x) /\ contig [x] x.at (bend x) /\ nodd [x])
  = ()
#pop-options

let split1_dead (b: blk)
  : Lemma (requires b.t = Dead /\ b.at >= z /\ b.at % 8 == 0)
          (ensures contig (split1 b) b.at (bend b) /\ nodd (split1 b) /\
                   (forall (c: blk). L.mem c (split1 b) ==> piece_ok c))
  = let r = b.at in
    let e = bend b in
    let p = pg_ceil r in
    let q = pg_floor e in
    FStar.Math.Lemmas.lemma_mod_plus r b.w 8;
    if p >= q then (no_page_of r e; mem_single b; assert (split1 b == [b]))
    else begin
      split_bounds r e;
      let pre = pre_of r p in
      let mid = pages p q in
      let suf = suf_of q e in
      pre_ok r p;
      suf_ok q e;
      pages_spec p q;
      pages_pieces p q;
      contig_append mid suf (page_base p) (page_base q) e;
      contig_append pre (L.append mid suf) r (page_base p) e;
      nodd_append mid suf;
      assert (hd_dead (L.append mid suf) == hd_dead mid);
      nodd_append pre (L.append mid suf);
      let mem_pieces (c: blk)
        : Lemma (L.mem c (L.append pre (L.append mid suf)) ==> piece_ok c)
        = L.append_mem pre (L.append mid suf) c;
          L.append_mem mid suf c
      in
      FStar.Classical.forall_intro mem_pieces
    end

let split1_live (b: blk)
  : Lemma (requires b.t = Live)
          (ensures split1 b == [b])
  = ()

#push-options "--fuel 2"
let rec split_spec (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e /\ a >= z /\ a % 8 == 0 /\ nodd bs /\
                    (forall (c: blk). L.mem c bs ==> c.t = Live \/ c.t = Dead))
          (ensures contig (split bs) a e /\ nodd (split bs) /\
                   (forall (c: blk). L.mem c (split bs) ==> (c.t = Live /\ L.mem c bs) \/ piece_ok c) /\
                   (forall (c: blk). L.mem c bs /\ c.t = Live ==> L.mem c (split bs)) /\
                   (Cons? bs /\ (L.hd bs).t = Live ==> Cons? (split bs) /\ (L.hd (split bs)).t = Live))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      contig_aligned bs a e;
      contig_le bs' (bend b) e;
      split_spec bs' (bend b) e;
      let rest = split bs' in
      if b.t = Live then begin
        split1_live b;
        assert (split bs == b :: rest)
      end else begin
        split1_dead b;
        (match bs' with
         | [] -> ()
         | c :: _ -> assert (c.t = Live));
        nodd_append (split1 b) rest
      end;
      contig_append (split1 b) rest a (bend b) e;
      let mem_all (c: blk)
        : Lemma (L.mem c (split bs) ==> (c.t = Live /\ L.mem c bs) \/ piece_ok c)
        = L.append_mem (split1 b) rest c
      in
      FStar.Classical.forall_intro mem_all;
      let live_in (c: blk)
        : Lemma (L.mem c bs /\ c.t = Live ==> L.mem c (split bs))
        = L.append_mem (split1 b) rest c
      in
      FStar.Classical.forall_intro live_in
#pop-options

/// ---------------------------------------------------------------------------
/// The swept run
/// ---------------------------------------------------------------------------

let fin (g: heap) (s e: nat) : list blk = split (merge (olds g s e))

/// **What the run sweep lays out.**  The blocks lie end to end over the
/// run, no two dead ones adjacent; a survivor is a black block of the walk,
/// and every black block of the walk is one; a dead block holds no whole
/// page; a free page is exactly a page.
let fin_spec (g: heap) (s e: nat)
  : Lemma (requires steps_to g s e /\ s >= z /\ s % 8 == 0)
          (ensures (let fs = fin g s e in
                    contig fs s e /\ nodd fs /\
                    (forall (c: blk). L.mem c fs ==>
                       (c.t = Live ==> L.mem c (olds g s e)) /\
                       (c.t <> Live ==> piece_ok c)) /\
                    (forall (c: blk). L.mem c (olds g s e) /\ c.t = Live ==> L.mem c fs)))
  = olds_spec g s e;
    let os = olds g s e in
    merge_spec os s e;
    split_spec (merge os) s e

/// A run with no survivor becomes free pages.
let fin_all_free (g: heap) (h n: nat)
  : Lemma (requires steps_to g (page_base h) (page_base (h + n)) /\ n > 0 /\
                    (forall (c: blk). L.mem c (olds g (page_base h) (page_base (h + n))) ==> c.t <> Live))
          (ensures fin g (page_base h) (page_base (h + n)) == pages h (h + n))
  = let s = page_base h in
    let e = page_base (h + n) in
    olds_spec g s e;
    page_base_lt h (h + n);
    merge_all_dead (olds g s e) s e;
    let b = { at = s; w = (e - s) / 8; t = Dead } in
    assert (bend b == e);
    pg_floor_base h;
    pg_floor_base (h + n);
    assert (pre_of s h == []);
    assert (suf_of (h + n) e == []);
    L.append_l_nil (pages h (h + n));
    assert (pg_ceil b.at == h /\ pg_floor (bend b) == h + n /\ b.at >= z /\ h < h + n);
    assert (split1 b == L.append (pre_of s h) (L.append (pages h (h + n)) (suf_of (h + n) e)));
    let ps = pages h (h + n) in
    assert (L.append ps (suf_of (h + n) e) == ps);
    assert (L.append (pre_of s h) (L.append ps (suf_of (h + n) e)) == ps);
    assert (split1 b == pages h (h + n));
    assert (merge (olds g s e) == [b]);
    assert (split [b] == L.append (split1 b) (split []));
    assert (split ([] <: list blk) == []);
    L.append_l_nil (split1 b)
