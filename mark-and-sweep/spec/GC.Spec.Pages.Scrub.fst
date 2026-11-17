/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Scrub - clearing the fields of dead objects
/// ---------------------------------------------------------------------------
///
/// While the collector sweeps incrementally, a dead white object in an
/// unswept page may point to a block already freed in a swept page, so the
/// heap breaks `well_formed_heap` and L10 there, and the allocator's
/// theorems do not apply to it directly (plan §20.4).  The objects at fault
/// are dead: nothing reads their fields again.
///
/// `scrub g zs` is `g` with the fields of the objects `zs` set to 0.  It
/// keeps the walk and every header (`scrub_objects`), and the page
/// invariant without L10 holds of the scrubbed heap exactly when it holds of
/// `g` (`core_scrub`): every clause of `pages_ok` but L10 reads only walk
/// headers and the links of free blocks, which the fields of an object that
/// is not free never hold (`GC.Spec.Pages.Fill`).
///
/// `GC.Spec.Pages.MidSweep` scrubs the dead objects of the unswept pages; the
/// scrubbed heap then satisfies `pages_ok` and `well_formed_heap`, and agrees
/// with `g` off the unswept pages, so the allocator runs on `g` as on it
/// (`GC.Spec.Pages.Graft`).

module GC.Spec.Pages.Scrub

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
open GC.Spec.Pages.Frame
open GC.Spec.Pages.Replace
open GC.Spec.Pages.Cells
open GC.Spec.Pages.Blocks
open GC.Spec.Pages.Step

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module L = FStar.List.Tot
module F = GC.Spec.Pages.Fill

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The page invariant without L10
/// ---------------------------------------------------------------------------

/// `pages_ok` but L10 (`no_pointer_to_blue`): the shapes, the page-local
/// clauses, the class lists and the large lists.
let core (g: heap) (st: pstate) : prop =
  map_ok st.pm /\ (forall (i: nat{i < n_pages}). page_local g st.pm i) /\ tail_shape g /\
  avail_ok st /\ large_ok g st

let core_of_ok (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st) (ensures core g st /\ GC.Spec.Pages.Wf.no_pointer_to_blue g)
  = pages_ok_elim g st

let ok_of_core (g: heap) (st: pstate)
  : Lemma (requires core g st /\ GC.Spec.Pages.Wf.no_pointer_to_blue g) (ensures pages_ok g st)
  = pages_ok_intro g st

let core_shape (g: heap) (st: pstate)
  : Lemma (requires core g st) (ensures shape_ok g st.pm)
  = let one (i: nat{i < n_pages}) : Lemma (page_shape g st.pm i) = assert (page_local g st.pm i) in
    FStar.Classical.forall_intro one

/// Writing the fields of an object that is not free keeps it, both ways.
let core_fill (g g': heap) (z: obj_addr) (st: pstate)
  : Lemma (requires F.fctx g g' z /\ ~(is_blue z g) /\ core g st) (ensures core g' st)
  = core_shape g st;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (F.page_fill g g' z st.pm));
    F.tail_fill g g' z st.pm;
    large_ok_lview g st;
    F.lview_fill g g' z st (walk g (large_head st) heap_words);
    lview_large_ok g' st (walk g (large_head st) heap_words)

/// ---------------------------------------------------------------------------
/// Writing the fields of objects
/// ---------------------------------------------------------------------------

/// `h` with the `n` words from `a` set to `v` of their address.
#push-options "--fuel 1"
let rec put_words (h: heap) (a: nat) (n: nat) (v: hp_addr -> GTot U64.t) : GTot heap (decreases n) =
  if n = 0 then h
  else begin
    let h1 = put_words h a (n - 1) v in
    let b = a + (n - 1) * 8 in
    if b < heap_size && b % 8 = 0 then write_word h1 (mk_hp_addr b) (v (mk_hp_addr b)) else h1
  end
#pop-options

let aligned_eq (x b: nat)
  : Lemma (requires x % 8 == 0 /\ b % 8 == 0 /\ b <= x /\ x < b + 8) (ensures x == b)
  = FStar.Math.Lemmas.lemma_div_mod x 8;
    FStar.Math.Lemmas.lemma_div_mod b 8

#push-options "--fuel 1"
let rec put_words_read (h: heap) (a: nat) (n: nat) (v: hp_addr -> GTot U64.t) (x: hp_addr)
  : Lemma (requires a % 8 == 0)
          (ensures read_word (put_words h a n v) x ==
                   (if a <= U64.v x && U64.v x < a + n * 8 then v x else read_word h x))
          (decreases n)
  = if n = 0 then ()
    else begin
      put_words_read h a (n - 1) v x;
      let b = a + (n - 1) * 8 in
      let h1 = put_words h a (n - 1) v in
      FStar.Math.Lemmas.lemma_mod_plus a (n - 1) 8;
      if a <= U64.v x && U64.v x < a + n * 8 && not (U64.v x < a + (n - 1) * 8) then aligned_eq (U64.v x) b;
      if b < heap_size && b % 8 = 0 then begin
        if U64.v x = b then begin
          assert (mk_hp_addr b == x);
          read_write_same h1 (mk_hp_addr b) (v (mk_hp_addr b))
        end
        else read_write_different h1 (mk_hp_addr b) x (v (mk_hp_addr b))
      end
    end

/// `g` with the fields of each of `zs` (their sizes in `g`) set to `v`.
let rec fill_objs (g: heap) (zs: list obj_addr) (v: hp_addr -> GTot U64.t) : GTot heap (decreases zs) =
  match zs with
  | [] -> g
  | z :: zs' -> put_words (fill_objs g zs' v) (U64.v z) (U64.v (wosize_of_object z g)) v
#pop-options

/// The scrub: every such field cleared.
let scrub (g: heap) (zs: list obj_addr) : GTot heap = fill_objs g zs (fun _ -> 0UL)

/// The objects `zs` are objects of `g` that are not free.
let objs (g: heap) (zs: list obj_addr) : prop =
  forall (z: obj_addr). L.mem z zs ==> Seq.mem z (objects zero_addr g) /\ ~(is_blue z g)

/// The word `a` is a field of one of `zs`.
let in_fields (g: heap) (zs: list obj_addr) (a: nat) : prop =
  exists (z: obj_addr). L.mem z zs /\ U64.v z <= a /\ a < F.fields_end g z

/// Every word of the filled heap.
#push-options "--fuel 1"
let rec fill_read (g: heap) (zs: list obj_addr) (v: hp_addr -> GTot U64.t) (a: hp_addr)
  : Lemma (ensures (in_fields g zs (U64.v a) ==> read_word (fill_objs g zs v) a == v a) /\
                   (~(in_fields g zs (U64.v a)) ==> read_word (fill_objs g zs v) a == read_word g a))
          (decreases zs)
  = match zs with
    | [] -> ()
    | z :: zs' ->
      fill_read g zs' v a;
      put_words_read (fill_objs g zs' v) (U64.v z) (U64.v (wosize_of_object z g)) v a
#pop-options

/// What the fill keeps: the objects and their headers.
let fill_objs_ok (g: heap) (zs: list obj_addr) (v: hp_addr -> GTot U64.t) : prop =
  forall (y: obj_addr).
    (Seq.mem y (objects zero_addr (fill_objs g zs v)) <==> Seq.mem y (objects zero_addr g)) /\
    (Seq.mem y (objects zero_addr g) ==>
       read_word (fill_objs g zs v) (hd_address y) == read_word g (hd_address y))

/// One more object, as a step of `Fill`.
let fill_step (g h: heap) (z: obj_addr) (v: hp_addr -> GTot U64.t)
  : Lemma (requires Seq.mem z (objects zero_addr h) /\ read_word h (hd_address z) == read_word g (hd_address z))
          (ensures (let h' = put_words h (U64.v z) (U64.v (wosize_of_object z g)) v in
                    F.fctx h h' z /\ F.fields_end h z == F.fields_end g z /\ F.fctx h' h z))
  = let n = U64.v (wosize_of_object z g) in
    let h' = put_words h (U64.v z) n v in
    wosize_of_object_spec z g;
    wosize_of_object_spec z h;
    FStar.Classical.forall_intro (put_words_read h (U64.v z) n v);
    F.obj_same h h' z z;
    hd_address_spec z;
    wosize_of_object_spec z h'

#push-options "--fuel 1"
let rec fill_facts (g: heap) (zs: list obj_addr) (v: hp_addr -> GTot U64.t)
  : Lemma (requires objs g zs) (ensures fill_objs_ok g zs v) (decreases zs)
  = match zs with
    | [] -> ()
    | z :: zs' ->
      fill_facts g zs' v;
      let h = fill_objs g zs' v in
      let h' = fill_objs g zs v in
      hd_address_spec z;
      fill_step g h z v;
      FStar.Classical.forall_intro (F.obj_same h h' z)
#pop-options

let scrub_ok (g: heap) (zs: list obj_addr) : prop =
  fill_objs_ok g zs (fun _ -> 0UL) /\
  (forall (a: hp_addr). ~(in_fields g zs (U64.v a)) ==> read_word (scrub g zs) a == read_word g a) /\
  (forall (a: hp_addr). in_fields g zs (U64.v a) ==> read_word (scrub g zs) a == 0UL)

let scrub_facts (g: heap) (zs: list obj_addr)
  : Lemma (requires objs g zs) (ensures scrub_ok g zs)
  = fill_facts g zs (fun _ -> 0UL);
    FStar.Classical.forall_intro (fill_read g zs (fun _ -> 0UL))

/// The fields of a scrubbed object hold no pointer.
let scrubbed_no_pointer (g: heap) (zs: list obj_addr) (z: obj_addr) (dst: obj_addr)
  : Lemma (requires objs g zs /\ L.mem z zs)
          (ensures ~(points_to (scrub g zs) z dst))
  = scrub_facts g zs;
    let h = scrub g zs in
    hd_address_spec z;
    wosize_of_object_spec z g;
    wosize_of_object_spec z h;
    let wz = wosize_of_object z h in
    wosize_of_object_bound z h;
    let one (idx: nat{idx < U64.v wz})
      : Lemma (let far = U64.add_mod z (U64.mul_mod (U64.uint_to_t idx) mword) in
               U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
               ~(is_pointer_to (read_word h (far <: hp_addr)) dst))
      = FStar.Math.Lemmas.pow2_lt_compat 64 58;
        FStar.Math.Lemmas.pow2_lt_compat 57 54;
        FStar.Math.Lemmas.pow2_double_sum 57;
        FStar.Math.Lemmas.pow2_plus 54 3;
        assert_norm (pow2 3 == 8);
        assert (idx < pow2 54);
        assert (idx * 8 < pow2 57);
        FStar.Math.Lemmas.modulo_lemma (idx * 8) (pow2 64);
        assert (U64.v z + idx * 8 < pow2 58);
        FStar.Math.Lemmas.modulo_lemma (U64.v z + idx * 8) (pow2 64);
        let far = U64.add_mod z (U64.mul_mod (U64.uint_to_t idx) mword) in
        assert (U64.v far == U64.v z + idx * 8);
        if U64.v far < heap_size && U64.v far % 8 = 0 then
          assert (in_fields g zs (U64.v far))
    in
    FStar.Classical.forall_intro one;
    efptu_false_if_no_field_matches h z wz dst

/// ---------------------------------------------------------------------------
/// The invariant without L10, through the scrub
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec core_fill_objs (g: heap) (zs: list obj_addr) (v: hp_addr -> GTot U64.t) (st: pstate)
  : Lemma (requires objs g zs) (ensures core (fill_objs g zs v) st <==> core g st) (decreases zs)
  = match zs with
    | [] -> ()
    | z :: zs' ->
      core_fill_objs g zs' v st;
      fill_facts g zs' v;
      let h = fill_objs g zs' v in
      let h' = fill_objs g zs v in
      hd_address_spec z;
      fill_step g h z v;
      color_of_header_eq z h h';
      color_of_header_eq z h g;
      if FStar.IndefiniteDescription.strong_excluded_middle (core h st) then core_fill h h' z st;
      if FStar.IndefiniteDescription.strong_excluded_middle (core h' st) then core_fill h' h z st
#pop-options

let core_scrub (g: heap) (zs: list obj_addr) (st: pstate)
  : Lemma (requires objs g zs) (ensures core (scrub g zs) st <==> core g st)
  = core_fill_objs g zs (fun _ -> 0UL) st

/// ---------------------------------------------------------------------------
/// Lists of objects
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec gfilter (f: obj_addr -> GTot bool) (l: list obj_addr) : GTot (list obj_addr) (decreases l) =
  match l with
  | [] -> []
  | x :: t -> if f x then x :: gfilter f t else gfilter f t

let rec gfilter_mem (f: obj_addr -> GTot bool) (l: list obj_addr) (x: obj_addr)
  : Lemma (ensures L.mem x (gfilter f l) <==> L.mem x l /\ f x) (decreases l)
  = match l with
    | [] -> ()
    | _ :: t -> gfilter_mem f t x
#pop-options

/// The objects of `g` with a property, as a list.
let objects_where (g: heap) (p: obj_addr -> GTot bool)
  : Ghost (list obj_addr) (requires True)
          (ensures fun zs -> forall (z: obj_addr). L.mem z zs <==> Seq.mem z (objects zero_addr g) /\ p z)
  = let s = objects zero_addr g in
    let l = Seq.seq_to_list s in
    SP.lemma_seq_list_bij s;
    let aux (z: obj_addr) : Lemma (L.mem z (gfilter p l) <==> Seq.mem z s /\ p z)
      = gfilter_mem p l z;
        SP.mem_seq_of_list z l
    in
    FStar.Classical.forall_intro aux;
    gfilter p l
