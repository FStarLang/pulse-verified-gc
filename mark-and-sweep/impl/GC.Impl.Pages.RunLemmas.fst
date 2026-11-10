/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.RunLemmas - the run sweep as one pass over the run
/// ---------------------------------------------------------------------------
///
/// The specification's run sweep (`GC.Spec.Pages.SweepRun.sweep_run`) builds
/// a list of blocks, `fin g s e = split (merge (olds g s e))`, and writes it
/// into the heap at once (`wr_all`), each listed block linked to the next.
/// The Pulse run sweep makes one pass from the run's start instead:
///
///   - a black block is a survivor: `fin` starts with it (`fin_live`);
///   - a block that is not black starts a stretch of such blocks, which ends
///     at `dead_end`; `fin` starts with that stretch, cut into its whole
///     pages and the pieces around them (`fin_dead`);
///   - where the walk leaves the run, `fin` is empty (`fin_stop`).
///
/// Each block of `fin` is written as soon as it is known.  A listed block's
/// link is the next listed block, which is not known yet; it is written when
/// that block is found, and the last one gets the old list head at the end.
/// `emit_ok` is the pass's invariant: the heap reads as the specification's
/// writes of the blocks so far (`val_at`), with the last listed block's link
/// still as it was (`vopen`).  `emit_plain`, `emit_listed` and `close_ok`
/// are its steps, and `close_eq` gives the specification's heap at the end.

module GC.Impl.Pages.RunLemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Blk
open GC.Spec.Pages.RunList
open GC.Spec.Pages.SweepRun

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module B = GC.Spec.Pages.Blocks
module HE = GC.Gen.HeapExtensional

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// 1. `fin`, a stretch at a time
/// ---------------------------------------------------------------------------

/// The end of the stretch of blocks that are not black, from `a`.
let rec dead_end (g: heap) (a e: nat) : Tot nat (decreases (if a < e then e - a else 0)) =
  if a >= e then a
  else begin
    let w = words_at g a in
    if a + w * 8 > e then a
    else if color_at g a = Black then a
    else dead_end g (a + w * 8) e
  end

/// The block at `a` is in the run.
let fits (g: heap) (a e: nat) : bool = a < e && a + words_at g a * 8 <= e

let rec dead_end_props (g: heap) (a e: nat)
  : Lemma (ensures a <= dead_end g a e /\ (a <= e ==> dead_end g a e <= e) /\
                   (dead_end g a e - a) % 8 == 0 /\
                   (fits g a e /\ color_at g a <> Black ==> dead_end g a e >= a + 8) /\
                   (let d = dead_end g a e in ~(fits g d e /\ color_at g d <> Black)))
          (decreases (if a < e then e - a else 0))
  = if a >= e then ()
    else begin
      let w = words_at g a in
      if a + w * 8 > e then ()
      else if color_at g a = Black then ()
      else begin
        dead_end_props g (a + w * 8) e;
        FStar.Math.Lemmas.lemma_mod_sub_distr (dead_end g (a + w * 8) e - a) (w * 8) 8
      end
    end

/// Outside the run, nothing.
let fin_stop (g: heap) (a e: nat)
  : Lemma (requires ~(fits g a e)) (ensures fin g a e == [])
  = ()

/// A survivor.
#push-options "--fuel 2"
let fin_live (g: heap) (a e: nat)
  : Lemma (requires fits g a e /\ color_at g a == Black)
          (ensures fin g a e == { at = a; w = words_at g a; t = Live } :: fin g (a + words_at g a * 8) e)
  = ()
#pop-options

/// The merged list from a stretch that is not black.
#push-options "--fuel 2"
let rec merge_dead (g: heap) (a e: nat)
  : Lemma (requires fits g a e /\ color_at g a <> Black)
          (ensures (let d = dead_end g a e in
                    d >= a + 8 /\
                    merge (olds g a e) == { at = a; w = (d - a) / 8; t = Dead } :: merge (olds g d e)))
          (decreases (if a < e then e - a else 0))
  = let w = words_at g a in
    let a' = a + w * 8 in
    dead_end_props g a e;
    if fits g a' e && color_at g a' <> Black then begin
      merge_dead g a' e;
      dead_end_props g a' e
    end else begin
      assert (dead_end g a e == a');
      if fits g a' e then ()
      else assert (olds g a' e == [])
    end
#pop-options

/// A stretch that is not black, cut.
let fin_dead (g: heap) (a e: nat)
  : Lemma (requires fits g a e /\ color_at g a <> Black)
          (ensures (let d = dead_end g a e in
                    d >= a + 8 /\
                    fin g a e == L.append (split1 { at = a; w = (d - a) / 8; t = Dead }) (fin g d e)))
  = merge_dead g a e

/// `split1` of a stretch, by cases.
let split1_whole (b: blk)
  : Lemma (requires b.t == Dead /\ (b.at < z \/ pg_ceil b.at >= pg_floor (bend b)))
          (ensures split1 b == [b])
  = ()

let split1_cut (b: blk)
  : Lemma (requires b.t == Dead /\ b.at >= z /\ pg_ceil b.at < pg_floor (bend b))
          (ensures split1 b ==
                   L.append (pre_of b.at (pg_ceil b.at))
                            (L.append (pages (pg_ceil b.at) (pg_floor (bend b))) (suf_of (pg_floor (bend b)) (bend b))))
  = ()

#push-options "--fuel 2"
let pages_cons (p q: nat)
  : Lemma (requires p < q) (ensures pages p q == page_blk p :: pages (p + 1) q)
  = ()

let pages_nil (p q: nat) : Lemma (requires p >= q) (ensures pages p q == []) = ()

let append_cons (x: blk) (r t: list blk)
  : Lemma (L.append (x :: r) t == x :: L.append r t)
  = ()

let append_one (x: blk) (t: list blk) : Lemma (L.append [x] t == x :: t) = ()
#pop-options

/// ---------------------------------------------------------------------------
/// 2. The heap the specification writes, read back
/// ---------------------------------------------------------------------------

/// The word at `x` once the blocks `bs` are written into `g0` with list
/// head `fp`.
let va (g0: heap) (bs: list blk) (fp: U64.t) (x: hp_addr) : U64.t =
  match val_at g0 bs fp (U64.v x) with Some v -> v | None -> read_word g0 x

#push-options "--fuel 2"
let rec lhead_append (xs ys: list blk) (fp: U64.t)
  : Lemma (ensures lhead (L.append xs ys) fp == lhead xs (lhead ys fp)) (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: r -> lhead_append r ys fp

let rec listed_append (xs ys: list blk)
  : Lemma (ensures listed (L.append xs ys) == L.append (listed xs) (listed ys)) (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: r -> listed_append r ys

let rec val_at_append (g0: heap) (xs ys: list blk) (fp: U64.t) (x: nat)
  : Lemma (ensures val_at g0 (L.append xs ys) fp x ==
                   (match val_at g0 xs (lhead ys fp) x with
                    | Some v -> Some v
                    | None -> val_at g0 ys fp x))
          (decreases xs)
  = match xs with
    | [] -> ()
    | b :: r -> lhead_append r ys fp; val_at_append g0 r ys fp x

let rec lhead_listed (bs: list blk) (fp: U64.t)
  : Lemma (ensures lhead bs fp == (match listed bs with [] -> fp | y :: _ -> (y <: U64.t))) (decreases bs)
  = match bs with
    | [] -> ()
    | _ :: r -> lhead_listed r fp
#pop-options

/// Every listed block of a run lies past its start.
let rec listed_past (bs: list blk) (a e: nat) (y: obj_addr)
  : Lemma (requires contig bs a e /\ L.mem y (listed bs)) (ensures U64.v y >= a + 8) (decreases bs)
  = match bs with
    | c :: r -> if listable c && y = obj_at c then () else listed_past r (bend c) e y

#push-options "--fuel 2"
let rec last_mem (l: list obj_addr)
  : Lemma (requires Cons? l) (ensures L.mem (L.last l) l) (decreases l)
  = match l with
    | [_] -> ()
    | _ :: r -> last_mem r

let rec last_append (l1 l2: list obj_addr)
  : Lemma (requires Cons? l2) (ensures L.last (L.append l1 l2) == L.last l2) (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: r -> last_append r l2

let last_cons (y: obj_addr) (r: list obj_addr)
  : Lemma (requires Cons? r) (ensures L.last (y :: r) == L.last r)
  = ()
#pop-options

/// The list head given to the writes matters only at the last listed
/// block's link.
let rec val_at_fp (g0: heap) (bs: list blk) (a e: nat) (fp fp': U64.t) (x: nat)
  : Lemma (requires contig bs a e)
          (ensures val_at g0 bs fp' x ==
                   (if Cons? (listed bs) && x = U64.v (L.last (listed bs)) then Some fp'
                    else val_at g0 bs fp x))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: r ->
      val_at_fp g0 r (bend b) e fp fp' x;
      lhead_listed r fp;
      lhead_listed r fp';
      lg_min_ge2 ();
      if Cons? (listed r) then begin
        last_mem (listed r);
        listed_past r (bend b) e (L.last (listed r));
        if listable b then last_cons (obj_at b) (listed r)
      end

/// ---------------------------------------------------------------------------
/// 3. The pass's invariant
/// ---------------------------------------------------------------------------

/// The value of the open link `pend` (0 when no block is listed yet).
let vopen (g0: heap) (pend: U64.t) : U64.t = hdr g0 (U64.v pend)

/// The open link is the last listed block's, and `first` the first listed
/// block.
let links_ok (bs: list blk) (first pend: U64.t) : prop =
  (listed bs == [] <==> pend == 0UL) /\
  (Cons? (listed bs) ==> pend == (L.last (listed bs) <: U64.t) /\ first == (L.hd (listed bs) <: U64.t))

/// The pass has written the blocks `bs`, which lie from `s` to `a`.
let emit_ok (g0 g: heap) (bs: list blk) (s a: nat) (first pend: U64.t) : prop =
  contig bs s a /\ s % 8 == 0 /\
  links_ok bs first pend /\
  (forall (x: hp_addr). read_word g x == va g0 bs (vopen g0 pend) x)

let emit_start (g0: heap) (s: nat)
  : Lemma (requires s % 8 == 0) (ensures emit_ok g0 g0 [] s s 0UL 0UL)
  = ()

/// Past the blocks written, the heap is as it was.
let emit_past (g0 g: heap) (bs: list blk) (s a: nat) (first pend: U64.t) (x: hp_addr)
  : Lemma (requires emit_ok g0 g bs s a first pend /\ U64.v x >= a)
          (ensures read_word g x == read_word g0 x)
  = va_out g0 bs s a (vopen g0 pend) (U64.v x)

let hdr_past (g0 g: heap) (bs: list blk) (s a: nat) (first pend: U64.t) (x: nat)
  : Lemma (requires emit_ok g0 g bs s a first pend /\ x >= a)
          (ensures hdr g x == hdr g0 x)
  = if x < heap_size && x % 8 = 0 then emit_past g0 g bs s a first pend (mk_hp_addr x)

/// The block written after `bs`.
#push-options "--fuel 2"
let one_val (g0: heap) (b: blk) (fp: U64.t) (x: nat)
  : Lemma (val_at g0 [b] fp x ==
           (if x = b.at then Some (hval g0 b) else if listable b && x = b.at + 8 then Some fp else None))
  = ()

let lhead_one (b: blk) (fp: U64.t)
  : Lemma (lhead [b] fp == (if listable b then (obj_at b <: U64.t) else fp)) = ()

let listed_one (b: blk)
  : Lemma (listed [b] == (if listable b then [obj_at b] else [])) = ()
#pop-options

#push-options "--fuel 2"
let contig_snoc (bs: list blk) (s a: nat) (b: blk)
  : Lemma (requires contig bs s a /\ b.at == a) (ensures contig (L.append bs [b]) s (bend b))
  = assert (contig [b] a (bend b));
    contig_append bs [b] s a (bend b)
#pop-options

/// A block that is not listed: its header.
let emit_plain (g0 g: heap) (bs: list blk) (s a: nat) (first pend: U64.t) (b: blk)
  : Lemma (requires emit_ok g0 g bs s a first pend /\ b.at == a /\ not (listable b))
          (ensures emit_ok g0 (B.wr g a (hval g0 b)) (L.append bs [b]) s (bend b) first pend)
  = contig_snoc bs s a b;
    listed_append bs [b];
    listed_one b;
    L.append_l_nil (listed bs);
    let v = vopen g0 pend in
    lhead_one b v;
    let aux (x: hp_addr)
      : Lemma (read_word (B.wr g a (hval g0 b)) x == va g0 (L.append bs [b]) v x)
      = B.wr_read g a (hval g0 b) x;
        val_at_append g0 bs [b] v (U64.v x);
        one_val g0 b v (U64.v x);
        if U64.v x >= a then va_out g0 bs s a v (U64.v x)
    in
    FStar.Classical.forall_intro aux

/// A listed block: its header, and the open link set to it.
let emit_listed_heap (g: heap) (a: nat) (h: U64.t) (pend o: U64.t) : GTot heap =
  let g1 = B.wr g a h in
  if pend = 0UL then g1 else B.wr g1 (U64.v pend) o

let emit_listed (g0 g: heap) (bs: list blk) (s a: nat) (first pend: U64.t) (b: blk)
  : Lemma (requires emit_ok g0 g bs s a first pend /\ b.at == a /\ listable b)
          (ensures emit_ok g0 (emit_listed_heap g a (hval g0 b) pend (obj_at b))
                           (L.append bs [b]) s (bend b)
                           (if pend = 0UL then (obj_at b <: U64.t) else first) (obj_at b))
  = contig_snoc bs s a b;
    listed_append bs [b];
    lg_min_ge2 ();
    let v = vopen g0 pend in
    let o : U64.t = obj_at b in
    let v' = vopen g0 o in
    let bs' = L.append bs [b] in
    listed_one b;
    lhead_one b v';
    last_append (listed bs) [obj_at b];
    (if Cons? (listed bs) then begin
       last_mem (listed bs);
       listed_past bs s a (L.last (listed bs));
       contig_le bs s a
     end);
    let aux (x: hp_addr)
      : Lemma (read_word (emit_listed_heap g a (hval g0 b) pend o) x == va g0 bs' v' x)
      = let g1 = B.wr g a (hval g0 b) in
        B.wr_read g a (hval g0 b) x;
        (if pend <> 0UL then B.wr_read g1 (U64.v pend) o x);
        val_at_append g0 bs [b] v' (U64.v x);
        one_val g0 b v' (U64.v x);
        val_at_fp g0 bs s a v o (U64.v x);
        if U64.v x >= a then va_out g0 bs s a v (U64.v x);
        if U64.v x >= a then va_out g0 bs s a o (U64.v x);
        if U64.v x = a + 8 then assert (hdr g0 (U64.v o) == read_word g0 x)
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// 4. The end of the pass
/// ---------------------------------------------------------------------------

let close_heap (g: heap) (pend fp: U64.t) : GTot heap =
  if pend = 0UL then g else B.wr g (U64.v pend) fp

let close_head (first pend fp: U64.t) : U64.t = if pend = 0UL then fp else first

let close_eq (g0 g: heap) (bs: list blk) (s a: nat) (first pend fp: U64.t)
  : Lemma (requires emit_ok g0 g bs s a first pend)
          (ensures close_heap g pend fp == wr_all g0 bs fp /\
                   close_head first pend fp == lhead bs fp)
  = lhead_listed bs fp;
    let g' = close_heap g pend fp in
    let aux (x: nat)
      : Lemma (x < heap_size /\ x % 8 == 0 ==>
               read_word g' (U64.uint_to_t x) == read_word (wr_all g0 bs fp) (U64.uint_to_t x))
      = if x < heap_size && x % 8 = 0 then begin
          let hx : hp_addr = U64.uint_to_t x in
          wr_all_read g0 bs fp hx;
          val_at_fp g0 bs s a (vopen g0 pend) fp x;
          if pend <> 0UL then B.wr_read g (U64.v pend) fp hx
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext g' (wr_all g0 bs fp)
