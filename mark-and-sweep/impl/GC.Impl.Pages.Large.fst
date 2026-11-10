/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Large - allocation of large blocks, in Pulse
/// ---------------------------------------------------------------------------
///
/// Each function here computes exactly what its specification computes, for
/// every heap and state:
///   - `find_fit`: `Large.split_fit` on the cells of list 0
///     (`Cells.walk g (large_head st) heap_words`): the first cell of at
///     least `w` words, and the cell before it;
///   - `carve`: `Large.carve_as false`, an object carved from the right end of
///     that cell, the cell unlinked when what is left is too small to list;
///   - `find_run`: `NewRun.find_run`, the first `k` consecutive free pages,
///     found as the prototype's `lg_grow` does: one pass from the free-page
///     hint, counting the free pages in a row;
///   - `new_run`: `NewRun.new_run_as false`, those pages made a swept run with
///     the object first and the rest one free block;
///   - `large_alloc`: `Alloc.large_alloc_as false`.
///
/// The walk follows list 0 for at most `heap_words` cells, as the
/// specification does, so it stops on a list that is cyclic.

module GC.Impl.Pages.Large

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State
open GC.Impl.Pages.Heap

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module SO = GC.Spec.Object
module Sh = GC.Spec.Pages.Shape
module B = GC.Spec.Pages.Blocks
module Ce = GC.Spec.Pages.Cells
module LG = GC.Spec.Pages.Large
module NR = GC.Spec.Pages.NewRun
module T = GC.Spec.Pages.Theorems
module A = GC.Spec.Pages.Alloc
module FLs = GC.Spec.FreeLists
module PL = GC.Impl.Pages.Pool

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The powers of two the arithmetic below needs.
let bounds () : Lemma (pow2 20 < pow2 54 /\ pow2 54 < pow2 57 /\ pow2 57 < pow2 64 /\
                       pow2 57 == 8 * pow2 54 /\ pow2 55 == 2 * pow2 54 /\ pow2 64 == 2 * pow2 63 /\
                       pow2 63 == 2 * pow2 62 /\ pow2 62 == 2 * pow2 61 /\ pow2 61 == 2 * pow2 60 /\
                       pow2 58 == 2 * pow2 57 /\ pow2 59 == 2 * pow2 58 /\ pow2 60 == 2 * pow2 59)
  = FStar.Math.Lemmas.pow2_lt_compat 54 20;
    FStar.Math.Lemmas.pow2_lt_compat 57 54;
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    assert_norm (pow2 57 == 8 * pow2 54);
    assert_norm (pow2 55 == 2 * pow2 54);
    assert_norm (pow2 64 == 2 * pow2 63);
    assert_norm (pow2 63 == 2 * pow2 62);
    assert_norm (pow2 62 == 2 * pow2 61);
    assert_norm (pow2 61 == 2 * pow2 60);
    assert_norm (pow2 58 == 2 * pow2 57);
    assert_norm (pow2 59 == 2 * pow2 58);
    assert_norm (pow2 60 == 2 * pow2 59)

/// ---------------------------------------------------------------------------
/// First fit on list 0
/// ---------------------------------------------------------------------------

/// `split_fit` on a list, with cells `pre0` already passed.
let prepend (pre0: list Base.obj_addr) (r: option (list Base.obj_addr & Base.obj_addr & list Base.obj_addr))
  : option (list Base.obj_addr & Base.obj_addr & list Base.obj_addr) =
  match r with
  | None -> None
  | Some (pre, c, post) -> Some (L.append pre0 pre, c, post)

/// What `find_fit` returns: the cell, the cell before it (0 when it is the
/// first), and whether a cell was found.
let fit_ok (g: Base.heap) (fp: U64.t) (w: nat) (found: bool) (prev c: U64.t) : prop =
  match LG.split_fit g (Ce.walk g fp Base.heap_words) w with
  | None -> found == false
  | Some (pre, c', _) ->
    found == true /\ c == (c' <: U64.t) /\
    (pre == [] ==> prev == 0UL) /\
    (pre =!= [] ==> prev == (L.last pre <: U64.t) /\ prev <> 0UL)

#push-options "--fuel 1"
let walk_step (g: Base.heap) (fp: U64.t) (n: nat)
  : Lemma (requires n > 0 /\ Ce.node fp)
          (ensures Ce.walk g fp n == (fp <: Base.obj_addr) :: Ce.walk g (SH.read_word g (fp <: Base.hp_addr)) (n - 1))
  = ()

let walk_stop (g: Base.heap) (fp: U64.t) (n: nat)
  : Lemma (requires n == 0 \/ not (Ce.node fp)) (ensures Ce.walk g fp n == [])
  = ()

#push-options "--fuel 2"
let split_cons (g: Base.heap) (c: Base.obj_addr) (rest: list Base.obj_addr) (w: nat)
  : Lemma (LG.split_fit g (c :: rest) w ==
           (if SO.whsize g c >= w then Some ([], c, rest) else prepend [c] (LG.split_fit g rest w)))
  = match LG.split_fit g rest w with
    | None -> ()
    | Some (pre, d, post) -> assert (L.append [c] pre == c :: pre)
#pop-options

let split_nil (g: Base.heap) (w: nat) : Lemma (LG.split_fit g [] w == None) = ()
#pop-options

let prepend_assoc (a b: list Base.obj_addr) (r: option (list Base.obj_addr & Base.obj_addr & list Base.obj_addr))
  : Lemma (prepend a (prepend b r) == prepend (L.append a b) r)
  = match r with
    | None -> ()
    | Some (pre, c, post) -> L.append_assoc a b pre

#push-options "--fuel 2"
let rec last_snoc (a: list Base.obj_addr) (x: Base.obj_addr)
  : Lemma (ensures L.last (L.append a [x]) == x /\ L.append a [x] =!= []) (decreases a)
  = match a with
    | [] -> ()
    | [_] -> ()
    | _ :: r -> last_snoc r x
#pop-options

#push-options "--fuel 1"
let append_nil (a: list Base.obj_addr) : Lemma (L.append a [] == a) = L.append_l_nil a
#pop-options

/// The whole size of the block whose object is at `c`.
let whsize_eq (g: Base.heap) (c: Base.obj_addr)
  : Lemma (SO.whsize g c == U64.v (SO.getWosize (SH.read_word g (SH.hd_address c))) + 1 /\
           U64.v (SH.hd_address c) == U64.v c - 8)
  = SO.wosize_of_object_spec c g;
    SH.hd_address_spec c

let is_node (x: U64.t) : r: bool{r == Ce.node x} =
  U64.gte x 8UL && U64.lt x heap_size_u64 && U64.rem x 8UL = 0UL

/// The fit invariant: the answer is the passed cells followed by what the
/// rest of the walk gives.
let fit_inv (g: Base.heap) (fp: U64.t) (w: nat) (pre0: list Base.obj_addr) (prev cur: U64.t) (n: nat) : prop =
  LG.split_fit g (Ce.walk g fp Base.heap_words) w == prepend pre0 (LG.split_fit g (Ce.walk g cur n) w) /\
  (pre0 == [] ==> prev == 0UL) /\
  (pre0 =!= [] ==> prev == (L.last pre0 <: U64.t) /\ prev <> 0UL)

let fit_found (g: Base.heap) (fp: U64.t) (w: nat) (pre0: list Base.obj_addr) (prev cur: U64.t) (n: nat)
  : Lemma (requires fit_inv g fp w pre0 prev cur n /\ n > 0 /\ Ce.node cur /\ SO.whsize g cur >= w)
          (ensures fit_ok g fp w true prev cur)
  = walk_step g cur n;
    split_cons g cur (Ce.walk g (SH.read_word g (cur <: Base.hp_addr)) (n - 1)) w;
    append_nil pre0

let fit_next (g: Base.heap) (fp: U64.t) (w: nat) (pre0: list Base.obj_addr) (prev cur: U64.t) (n: nat)
  : Lemma (requires fit_inv g fp w pre0 prev cur n /\ n > 0 /\ Ce.node cur /\ SO.whsize g cur < w)
          (ensures fit_inv g fp w (L.append pre0 [cur]) cur (SH.read_word g (cur <: Base.hp_addr)) (n - 1))
  = walk_step g cur n;
    split_cons g cur (Ce.walk g (SH.read_word g (cur <: Base.hp_addr)) (n - 1)) w;
    prepend_assoc pre0 [cur] (LG.split_fit g (Ce.walk g (SH.read_word g (cur <: Base.hp_addr)) (n - 1)) w);
    last_snoc pre0 cur

let fit_none (g: Base.heap) (fp: U64.t) (w: nat) (pre0: list Base.obj_addr) (prev cur: U64.t) (n: nat)
  : Lemma (requires fit_inv g fp w pre0 prev cur n /\ (n == 0 \/ not (Ce.node cur)))
          (ensures fit_ok g fp w false 0UL 0UL)
  = walk_stop g cur n; split_nil g w

#push-options "--fuel 1"
let fit_start (g: Base.heap) (fp: U64.t) (w: nat)
  : Lemma (fit_inv g fp w [] 0UL fp Base.heap_words)
  = match LG.split_fit g (Ce.walk g fp Base.heap_words) w with
    | None -> ()
    | Some (pre, c, post) -> ()
#pop-options

/// The fit invariant, with the passed cells hidden.
let fit_inv_ex (g: Base.heap) (fp: U64.t) (w: nat) (prev cur: U64.t) (n: nat) : prop =
  exists (pre0: list Base.obj_addr). fit_inv g fp w pre0 prev cur n

let fit_found_ex (g: Base.heap) (fp: U64.t) (w: nat) (prev cur: U64.t) (n: nat)
  : Lemma (requires fit_inv_ex g fp w prev cur n /\ n > 0 /\ Ce.node cur /\ SO.whsize g cur >= w)
          (ensures fit_ok g fp w true prev cur)
  = eliminate exists (pre0: list Base.obj_addr). fit_inv g fp w pre0 prev cur n
    with fit_found g fp w pre0 prev cur n

let fit_next_ex (g: Base.heap) (fp: U64.t) (w: nat) (prev cur: U64.t) (n: nat)
  : Lemma (requires fit_inv_ex g fp w prev cur n /\ n > 0 /\ Ce.node cur /\ SO.whsize g cur < w)
          (ensures fit_inv_ex g fp w cur (SH.read_word g (cur <: Base.hp_addr)) (n - 1))
  = eliminate exists (pre0: list Base.obj_addr). fit_inv g fp w pre0 prev cur n
    with fit_next g fp w pre0 prev cur n

let fit_none_ex (g: Base.heap) (fp: U64.t) (w: nat) (prev cur: U64.t) (n: nat)
  : Lemma (requires fit_inv_ex g fp w prev cur n /\ (n == 0 \/ not (Ce.node cur)))
          (ensures fit_ok g fp w false 0UL 0UL)
  = eliminate exists (pre0: list Base.obj_addr). fit_inv g fp w pre0 prev cur n
    with fit_none g fp w pre0 prev cur n

let fit_start_ex (g: Base.heap) (fp: U64.t) (w: nat)
  : Lemma (fit_inv_ex g fp w 0UL fp Base.heap_words)
  = fit_start g fp w

let heap_words_u64 () : r: U64.t{U64.v r == Base.heap_words} = U64.div heap_size_u64 8UL

fn find_fit (heap: heap_t) (fp: U64.t) (w: U64.t)
  requires is_heap heap 'g
  returns res: (bool & U64.t & U64.t)
  ensures is_heap heap 'g **
          pure (let (found, prev, c) = res in fit_ok 'g fp (U64.v w) found prev c)
{
  bounds ();
  fit_start_ex 'g fp (U64.v w);
  pow54_lt_64 ();
  let mut prev = 0UL;
  let mut cur = fp;
  let mut n = heap_words_u64 ();
  let mut found = false;
  let mut go = true;
  while (!go)
    invariant exists* vprev vcur vn vfound vgo.
      R.pts_to prev vprev ** R.pts_to cur vcur ** R.pts_to n vn **
      R.pts_to found vfound ** R.pts_to go vgo ** is_heap heap 'g **
      pure ((vgo ==> fit_inv_ex 'g fp (U64.v w) vprev vcur (U64.v vn) /\ vfound == false) /\
            (not vgo ==> (if vfound then fit_ok 'g fp (U64.v w) true vprev vcur
                          else fit_ok 'g fp (U64.v w) false 0UL 0UL)))
    decreases (U64.v !n + (if !go then 1 else 0))
  {
    let vn = !n;
    let vcur = !cur;
    let vprev = !prev;
    if (vn = 0UL || not (is_node vcur)) {
      fit_none_ex 'g fp (U64.v w) vprev vcur (U64.v vn);
      go := false
    } else {
      whsize_eq 'g vcur;
      let h = read_word heap (U64.sub vcur 8UL);
      let sz = U64.add (get_wosize h) 1UL;
      if (U64.gte sz w) {
        fit_found_ex 'g fp (U64.v w) vprev vcur (U64.v vn);
        found := true;
        go := false
      } else {
        let nx = read_word heap vcur;
        fit_next_ex 'g fp (U64.v w) vprev vcur (U64.v vn);
        prev := vcur;
        cur := nx;
        n := U64.sub vn 1UL
      }
    }
  };
  let f = !found;
  if f {
    (true, !prev, !cur)
  } else {
    (false, 0UL, 0UL)
  }
}

/// ---------------------------------------------------------------------------
/// Carving
/// ---------------------------------------------------------------------------

let lg_min_u64 () : r: U64.t{U64.v r == lg_min} =
  let sm = PL.small_max_u64 () in
  cls_bounds (n_cls - 1);
  FStar.Math.Lemmas.pow2_lt_compat 64 20;
  U64.add sm 1UL

/// `carved_as false g c wz`, by cases: a free block and the object, or the
/// object alone.
let carved_split (g: Base.heap) (c: Base.obj_addr) (wz: nat{wz < pow2 54}) (h l x: nat)
  : Lemma (requires h == LG.hd_of c /\ l == LG.rem_of g c wz /\ l >= 1 /\ l <= pow2 54 /\ x == h + l * 8)
          (ensures LG.carved_as false g c wz == B.wr (B.wr g h (B.bhdr l)) x (B.ohdr wz))
  = ()

let carved_whole (g: Base.heap) (c: Base.obj_addr) (wz: nat{wz < pow2 54}) (h: nat)
  : Lemma (requires h == LG.hd_of c /\ ~(LG.rem_of g c wz >= 1 /\ LG.rem_of g c wz <= pow2 54))
          (ensures LG.carved_as false g c wz == B.wr g h (B.ohdr wz))
  = ()

/// The block at `c` read back as a whole size, in the current heap.
fn whsize_at (heap: heap_t) (c: U64.t{Ce.node c})
  requires is_heap heap 'g
  returns r: U64.t
  ensures is_heap heap 'g ** pure (U64.v r == SO.whsize 'g c /\ U64.v r <= pow2 54)
{
  bounds ();
  whsize_eq 'g c;
  pow54_lt_64 ();
  let h = read_word heap (U64.sub c 8UL);
  U64.add (get_wosize h) 1UL
}

/// `carved_as false g c wz` and `obj_of g c wz`, for a cell of the current heap.
fn carve_at (heap: heap_t) (c: U64.t{Ce.node c}) (wz: U64.t{U64.v wz < pow2 54})
  requires is_heap heap 'g
  returns o: U64.t
  ensures exists* g'. is_heap heap g' ** pure (g' == LG.carved_as false 'g c (U64.v wz) /\ o == LG.obj_of 'g c (U64.v wz))
{
  bounds ();
  let ws = whsize_at heap c;
  let w = U64.add wz 1UL;
  let l = (if U64.gte ws w then U64.sub ws w else 0UL);
  let h = U64.sub c 8UL;
  FStar.Math.Lemmas.pow2_lt_compat 64 57;
  FStar.Math.Lemmas.pow2_plus 54 3;
  let x = U64.add h (U64.mul l 8UL);
  FStar.UInt.shift_left_value_lemma #64 1 54;
  if (U64.gte l 1UL && U64.lte l (U64.shift_left 1UL 54ul)) {
    wr heap h (bhdr_u64 l);
    wr heap x (ohdr_u64 wz);
    carved_split 'g c (U64.v wz) (U64.v h) (U64.v l) (U64.v x);
    U64.add x 8UL
  } else {
    wr heap h (ohdr_u64 wz);
    carved_whole 'g c (U64.v wz) (U64.v h);
    U64.add x 8UL
  }
}

/// `carve_as false`, given where the cell is on list 0.
let carve_unfold (g: Base.heap) (st: pstate) (pre: list Base.obj_addr) (c: Base.obj_addr) (wz: nat{wz < pow2 54})
  : Lemma (LG.carve_as false g st pre c wz ==
           (if SO.whsize g c < wz + 1 then (g, st, 0UL)
            else if LG.rem_of g c wz >= lg_min then (LG.carved_as false g c wz, st, LG.obj_of g c wz)
            else begin
              let nx = SH.read_word g (c <: Base.hp_addr) in
              let g1 = LG.unlink_heap g st pre nx in
              (LG.carved_as false g1 c wz, LG.unlink_state g st pre nx, LG.obj_of g1 c wz)
            end))
  = ()

let unlink_nil (g: Base.heap) (st: pstate) (nx: U64.t)
  : Lemma (LG.unlink_heap g st [] nx == g /\ LG.unlink_state g st [] nx == set_lhead st nx)
  = ()

let unlink_cons (g: Base.heap) (st: pstate) (pre: list Base.obj_addr) (nx: U64.t)
  : Lemma (requires pre =!= [])
          (ensures LG.unlink_heap g st pre nx == B.wr g (U64.v (L.last pre)) nx /\
                   LG.unlink_state g st pre nx == st)
  = ()

fn carve (heap: heap_t) (t: pstate_t) (c: U64.t{Ce.node c}) (prev: U64.t) (wz: U64.t{U64.v wz < pow2 54})
  (#st: erased pstate) (pre: erased (list Base.obj_addr))
  requires is_heap heap 'g ** pages_st t st **
           pure ((reveal pre == [] ==> prev == 0UL) /\
                 (reveal pre =!= [] ==> prev == (L.last pre <: U64.t) /\ prev <> 0UL))
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == LG.carve_as false 'g st pre c (U64.v wz))
{
  bounds ();
  carve_unfold 'g st pre c (U64.v wz);
  let ws = whsize_at heap c;
  let w = U64.add wz 1UL;
  if (U64.lt ws w) {
    0UL
  } else {
    if (U64.gte (U64.sub ws w) (lg_min_u64 ())) {
      carve_at heap c wz
    } else {
      let nx = read_word heap c;
      if (prev = 0UL) {
        unlink_nil 'g st nx;
        write_lhead t nx;
        carve_at heap c wz
      } else {
        unlink_cons 'g st pre nx;
        wr heap prev nx;
        carve_at heap c wz
      }
    }
  }
}

/// ---------------------------------------------------------------------------
/// A run of free pages
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let find_run_step (pm: page_map) (k: pos) (j: nat)
  : Lemma (NR.find_run pm k j ==
           (if j + k > n_pages then n_pages
            else if NR.all_free pm j k then j
            else NR.find_run pm k (j + 1)))
  = ()
#pop-options

let rec find_run_le (pm: page_map) (k: pos) (j: nat)
  : Lemma (ensures NR.find_run pm k j <= n_pages /\
                   (NR.find_run pm k j < n_pages ==> NR.find_run pm k j + k <= n_pages))
          (decreases (if j <= n_pages then n_pages + 1 - j else 0))
  = find_run_step pm k j;
    if j + k > n_pages then () else if NR.all_free pm j k then () else find_run_le pm k (j + 1)

/// No start of `k` free pages from `s` up to `q`: the search may go on from `q`.
let rec run_skip (pm: page_map) (k: pos) (s q: nat)
  : Lemma (requires s <= q /\
                    (forall (j: nat). s <= j /\ j < q ==> ~(NR.all_free pm j k) \/ j + k > n_pages))
          (ensures NR.find_run pm k s == NR.find_run pm k q)
          (decreases (q - s))
  = find_run_step pm k s;
    if s < q then begin
      if s + k > n_pages then find_run_step pm k q
      else run_skip pm k (s + 1) q
    end

/// A page that is not free ends every stretch of `k` pages over it.
let not_free_breaks (pm: page_map) (k: pos) (s p: nat)
  : Lemma (requires p < n_pages /\ (entry pm p).kind =!= Free /\ s <= p /\ p - s < k)
          (ensures forall (j: nat). s <= j /\ j < p + 1 ==> ~(NR.all_free pm j k) \/ j + k > n_pages)
  = let aux (j: nat) : Lemma (s <= j /\ j < p + 1 ==> ~(NR.all_free pm j k) \/ j + k > n_pages)
      = NR.all_free_spec pm j k
    in
    FStar.Classical.forall_intro aux

/// No page below the hint is free, so no stretch starts below it.
let hint_skip (pm: page_map) (k: pos) (h: nat)
  : Lemma (requires none_free_below pm h /\ h <= n_pages)
          (ensures NR.find_run pm k 0 == NR.find_run pm k h)
  = let aux (j: nat) : Lemma (j < h ==> ~(NR.all_free pm j k) \/ j + k > n_pages)
      = NR.all_free_spec pm j k
    in
    FStar.Classical.forall_intro aux;
    run_skip pm k 0 h

/// `k` free pages in a row from `s`: the search stops there.
let run_found (pm: page_map) (k: pos) (s: nat)
  : Lemma (requires s + k <= n_pages /\ (forall (j: nat). s <= j /\ j < s + k ==> (entry pm j).kind == Free))
          (ensures NR.find_run pm k s == s)
  = NR.all_free_spec pm s k;
    find_run_step pm k s

/// Fewer than `k` pages left from `s`: none found.
let run_none (pm: page_map) (k: pos) (s: nat)
  : Lemma (requires s + k > n_pages) (ensures NR.find_run pm k s == n_pages)
  = find_run_step pm k s

fn find_run (t: pstate_t) (k: U64.t{U64.v k > 0}) (#st: erased pstate)
  requires pages_st t st
  returns i: U64.t
  ensures pages_st t st ** pure (U64.v i == NR.find_run st.pm (U64.v k) 0)
{
  bounds ();
  let np = n_pages_u64 ();
  n_pages_small ();
  let h = read_hint t;
  hint_skip st.pm (U64.v k) (U64.v h);
  let mut p = h;
  let mut s = h;
  let mut res = np;
  let mut go = true;
  while (!go && U64.lt !p np)
    invariant exists* vp vs vres vgo.
      R.pts_to p vp ** R.pts_to s vs ** R.pts_to res vres ** R.pts_to go vgo ** pages_st t st **
      pure (U64.v vs <= U64.v vp /\ U64.v vp <= n_pages /\
            (vgo ==> U64.v vp - U64.v vs < U64.v k /\
                     (forall (j: nat). U64.v vs <= j /\ j < U64.v vp ==> (entry st.pm j).kind == Free) /\
                     NR.find_run st.pm (U64.v k) (U64.v vs) == NR.find_run st.pm (U64.v k) 0) /\
            (not vgo ==> U64.v vres == NR.find_run st.pm (U64.v k) 0))
    decreases (n_pages - U64.v !p + (if !go then 1 else 0))
  {
    let vp = !p;
    let vs = !s;
    let r = read_entry t vp;
    if (is_free_rec r) {
      if (U64.sub (U64.add vp 1UL) vs = k) {
        run_found st.pm (U64.v k) (U64.v vs);
        res := vs;
        go := false
      } else {
        p := U64.add vp 1UL
      }
    } else {
      not_free_breaks st.pm (U64.v k) (U64.v vs) (U64.v vp);
      run_skip st.pm (U64.v k) (U64.v vs) (U64.v vp + 1);
      p := U64.add vp 1UL;
      s := U64.add vp 1UL
    }
  };
  let vgo = !go;
  if vgo {
    let vs = !s;
    run_none st.pm (U64.v k) (U64.v vs);
    np
  } else {
    !res
  }
}

/// ---------------------------------------------------------------------------
/// A new run
/// ---------------------------------------------------------------------------

/// The records of a run's pages.
let head_rec (k: U64.t{U64.v k > 0}) : pinfo =
  { code = 2uy; arg = k; swept = true; free_head = 0UL; nfree = 0UL; next = 0UL }

let cont_rec : pinfo =
  { code = 3uy; arg = 0UL; swept = true; free_head = 0UL; nfree = 0UL; next = 0UL }

let head_rec_view (k: U64.t{U64.v k > 0}) : Lemma (view (head_rec k) == NR.head_entry (U64.v k)) = ()
let cont_rec_view () : Lemma (view cont_rec == NR.cont_entry) = ()

/// The map with pages `i .. i + m - 1` of the run written.
let run_part (pm: page_map) (i: nat) (k: pos) (m: nat) (j: nat{j < n_pages}) : page_info =
  if i <= j && j < i + m then (if j = i then NR.head_entry k else NR.cont_entry) else entry pm j

let run_map_done (pm pm': page_map) (i: nat) (k: pos)
  : Lemma (requires forall (j: nat{j < n_pages}). entry pm' j == run_part pm i k k j)
          (ensures pm' == NR.run_map pm i k)
  = NR.run_entries pm i k;
    Seq.lemma_eq_intro pm' (NR.run_map pm i k)

let pstate_eq (a b: pstate)
  : Lemma (requires a.pm == b.pm /\ a.avail == b.avail /\ a.large == b.large) (ensures a == b)
  = ()

fn write_run (t: pstate_t) (i: U64.t) (k: U64.t{U64.v k > 0 /\ U64.v i + U64.v k <= n_pages})
  (#st: erased pstate)
  requires pages_st t st
  ensures pages_st t ({ st with pm = NR.run_map st.pm (U64.v i) (U64.v k) })
{
  bounds ();
  head_rec_view k;
  cont_rec_view ();
  let mut m = 0UL;
  while (U64.lt !m k)
    invariant exists* vm st1.
      R.pts_to m vm ** pages_st t st1 **
      pure (U64.v vm <= U64.v k /\ st1.avail == st.avail /\ st1.large == st.large /\
            (forall (j: nat{j < n_pages}). entry st1.pm j == run_part st.pm (U64.v i) (U64.v k) (U64.v vm) j))
    decreases (U64.v k - U64.v !m)
  {
    let vm = !m;
    let j = U64.add i vm;
    let rr = (if vm = 0UL then head_rec k else cont_rec);
    write_entry t j rr;
    m := U64.add vm 1UL
  };
  with st1. assert (pages_st t st1);
  run_map_done st.pm st1.pm (U64.v i) (U64.v k);
  pstate_eq st1 ({ st with pm = NR.run_map st.pm (U64.v i) (U64.v k) });
  rewrite (pages_st t st1) as (pages_st t ({ st with pm = NR.run_map st.pm (U64.v i) (U64.v k) }))
}

/// `run_heap_as false g i k wz hd0` and `run_state`, by cases on the rest
/// `r = k * page_wsize - (wz + 1)` of the run: listed, unlisted, or none.
let run_listed (g: Base.heap) (st: pstate) (i: nat) (k: pos) (wz: nat{wz < pow2 54}) (hd0: U64.t)
               (a x r: nat) (o: U64.t)
  : Lemma (requires a == page_base i /\ r == k * page_wsize - (wz + 1) /\ x == a + (wz + 1) * 8 /\
                    U64.v o == x + 8 /\ r > 0 /\ r <= pow2 54 /\ r >= lg_min)
          (ensures NR.run_heap_as false g i k wz hd0 == B.wr (B.wr (B.wr g x (B.bhdr r)) (U64.v o) hd0) a (B.ohdr wz) /\
                   NR.run_state st i k (wz + 1) == set_lhead ({ st with pm = NR.run_map st.pm i k }) o)
  = ()

let run_unlisted (g: Base.heap) (st: pstate) (i: nat) (k: pos) (wz: nat{wz < pow2 54}) (hd0: U64.t)
                 (a x r: nat)
  : Lemma (requires a == page_base i /\ r == k * page_wsize - (wz + 1) /\ x == a + (wz + 1) * 8 /\
                    r > 0 /\ r <= pow2 54 /\ r < lg_min)
          (ensures NR.run_heap_as false g i k wz hd0 == B.wr (B.wr g x (B.bhdr r)) a (B.ohdr wz) /\
                   NR.run_state st i k (wz + 1) == { st with pm = NR.run_map st.pm i k })
  = ()

let run_full (g: Base.heap) (st: pstate) (i: nat) (k: pos) (wz: nat{wz < pow2 54}) (hd0: U64.t) (a r: nat)
  : Lemma (requires a == page_base i /\ r == k * page_wsize - (wz + 1) /\ r <= pow2 54 /\ ~(r > 0 /\ r <= pow2 54))
          (ensures NR.run_heap_as false g i k wz hd0 == B.wr g a (B.ohdr wz) /\
                   NR.run_state st i k (wz + 1) == { st with pm = NR.run_map st.pm i k })
  = cls_bounds (n_cls - 1)

let run_bound (i: nat) (k: pos) (w: pos)
  : Lemma (requires i + k <= n_pages /\ w <= k * page_wsize)
          (ensures page_base i + k * page_wsize * 8 <= Base.heap_size /\
                   page_base i + w * 8 + 16 <= pow2 64 /\ k * page_wsize < pow2 54)
  = page_base_mono (i + k) n_pages;
    FStar.Math.Lemmas.distributivity_add_left i k page_bytes;
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    assert_norm (pow2 57 == 8 * pow2 54)

fn new_run (heap: heap_t) (t: pstate_t) (i: U64.t) (k: U64.t{U64.v k > 0 /\ U64.v i + U64.v k <= n_pages})
  (wz: U64.t{U64.v wz + 1 <= U64.v k * page_wsize /\ U64.v wz < pow2 54})
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == NR.new_run_as false 'g st (U64.v i) (U64.v k) (U64.v wz))
{
  bounds ();
  let w = U64.add wz 1UL;
  run_bound (U64.v i) (U64.v k) (U64.v w);
  let a = page_base_u64 i;
  let r = U64.sub (U64.mul k page_wsize_u64) w;
  let hd0 = read_lhead t;
  let x = U64.add a (U64.mul w 8UL);
  let o = U64.add x 8UL;
  let ob = U64.add a 8UL;
  FStar.UInt.shift_left_value_lemma #64 1 54;
  if (U64.gt r 0UL && U64.lte r (U64.shift_left 1UL 54ul)) {
    if (U64.gte r (lg_min_u64 ())) {
      run_listed 'g st (U64.v i) (U64.v k) (U64.v wz) hd0 (U64.v a) (U64.v x) (U64.v r) o;
      wr heap x (bhdr_u64 r);
      wr heap o hd0;
      wr heap a (ohdr_u64 wz);
      write_run t i k;
      write_lhead t o;
      ob
    } else {
      run_unlisted 'g st (U64.v i) (U64.v k) (U64.v wz) hd0 (U64.v a) (U64.v x) (U64.v r);
      wr heap x (bhdr_u64 r);
      wr heap a (ohdr_u64 wz);
      write_run t i k;
      ob
    }
  } else {
    run_full 'g st (U64.v i) (U64.v k) (U64.v wz) hd0 (U64.v a) (U64.v r);
    wr heap a (ohdr_u64 wz);
    write_run t i k;
    ob
  }
}

/// ---------------------------------------------------------------------------
/// Large allocation
/// ---------------------------------------------------------------------------

let pages_for_u64 (w: U64.t{U64.v w > 0 /\ U64.v w <= pow2 54}) : r: U64.t{U64.v r == T.pages_for (U64.v w)}
  = cls_bounds 0;
    FStar.Math.Lemmas.pow2_lt_compat 64 55;
    FStar.Math.Lemmas.pow2_lt_compat 55 54;
    FStar.Math.Lemmas.pow2_lt_compat 54 20;
    FStar.Math.Lemmas.pow2_double_sum 54;
    U64.div (U64.sub (U64.add w page_wsize_u64) 1UL) page_wsize_u64

let large_unfold (g: Base.heap) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (A.large_alloc_as false g st wz ==
           (match LG.split_fit g (Ce.walk g (Ce.large_head st) Base.heap_words) (wz + 1) with
            | Some (pre, c, post) -> LG.carve_as false g st pre c wz
            | None ->
              let k = T.pages_for (wz + 1) in
              let i = NR.find_run st.pm k 0 in
              if i + k > n_pages then (g, st, 0UL)
              else NR.new_run_as false g st i k wz))
  = ()

let fit_pre (g: Base.heap) (fp: U64.t) (w: nat) (prev c: U64.t)
  : Lemma (requires fit_ok g fp w true prev c)
          (ensures (match LG.split_fit g (Ce.walk g fp Base.heap_words) w with
                    | Some (pre, c', _) -> Ce.node c /\ c' == c
                    | None -> False))
  = match LG.split_fit g (Ce.walk g fp Base.heap_words) w with
    | Some (pre, c', _) -> ()

let fit_pre_list (g: Base.heap) (fp: U64.t) (w: nat) (prev c: U64.t{Ce.node c})
  : Ghost (erased (list Base.obj_addr))
          (requires fit_ok g fp w true prev c)
          (ensures fun pre ->
             (match LG.split_fit g (Ce.walk g fp Base.heap_words) w with
              | Some (pre', c', _) -> reveal pre == pre' /\ c' == (c <: Base.obj_addr)
              | None -> False) /\
             (reveal pre == [] ==> prev == 0UL) /\
             (reveal pre =!= [] ==> prev == (L.last pre <: U64.t) /\ prev <> 0UL))
  = match LG.split_fit g (Ce.walk g fp Base.heap_words) w with
    | Some (pre, _, _) -> hide pre

let pages_for_ok (w: pos)
  : Lemma (w <= T.pages_for w * page_wsize)
  = NR.pages_for_spec w

fn large_alloc (heap: heap_t) (t: pstate_t) (wz: U64.t{U64.v wz < pow2 54})
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == A.large_alloc_as false 'g st (U64.v wz))
{
  bounds ();
  large_unfold 'g st (U64.v wz);
  let w = U64.add wz 1UL;
  let fp = read_lhead t;
  let res = find_fit heap fp w;
  let found = (match res with | (f, _, _) -> f);
  let prev = (match res with | (_, p, _) -> p);
  let c = (match res with | (_, _, c) -> c);
  if found {
    fit_pre 'g fp (U64.v w) prev c;
    let pre = fit_pre_list 'g fp (U64.v w) prev c;
    carve heap t c prev wz pre
  } else {
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    let k = pages_for_u64 w;
    pages_for_ok (U64.v w);
    let i = find_run t k;
    find_run_le st.pm (U64.v k) 0;
    let np = n_pages_u64 ();
    if (U64.gt k (U64.sub np i)) {
      0UL
    } else {
      new_run heap t i k wz
    }
  }
}
