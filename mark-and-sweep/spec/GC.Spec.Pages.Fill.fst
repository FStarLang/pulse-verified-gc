/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Fill - the caller writes the fields of a new object
/// ---------------------------------------------------------------------------
///
/// The allocator hands out an object with its fields as they were, as
/// OCaml's `caml_alloc_shr` does; the caller writes every field before the
/// heap is valid again.  **`fill_ok`** is the lemma for that: in a heap with
/// `pages_ok` and `well_formed_heap`, writing the fields of an object that
/// is neither free nor a closure, each with a value `field_ok` allows, keeps
/// both.
///
/// Nothing but the walk headers and the links of free blocks is read by the
/// clauses of `pages_ok`, and the fields of a non-free object hold neither:
/// every position the walk reaches lies outside them (`apart`).  So the walk,
/// the pages and the lists are kept, and only the field-closure clauses need
/// the values written.
///
/// `cleared_written` shows the caller can always do it: clearing the fields
/// writes valid values.

module GC.Spec.Pages.Fill

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
open GC.Spec.Pages.Theorems
open GC.Spec.Pages.Step

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Only the fields change
/// ---------------------------------------------------------------------------

/// The end of the fields of `x`.
let fields_end (g: heap) (x: obj_addr) : GTot nat = U64.v x + U64.v (wosize_of_object x g) * 8

/// `g'` is `g` but for the fields of `x`, an object of `g`.
let fctx (g g': heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\
  (forall (a: hp_addr). U64.v a < U64.v x \/ U64.v a >= fields_end g x ==>
     read_word g' a == read_word g a)

/// A position the walk reaches, other than the header of `x`, starts a
/// block that lies wholly before `x` or after its fields.
let apart (g: heap) (x: obj_addr) (p: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ steps_to g z p /\ p <> U64.v x - 8)
          (ensures (p < U64.v x - 8 /\ p + words_at g p * 8 <= U64.v x - 8) \/ p >= fields_end g x)
  = let h = U64.v x - 8 in
    hd_address_spec x;
    obj_iff g x;
    hdr_obj g x;
    if p < h then block_before g z p h
    else block_before g z h p

/// So no position the walk reaches is a field of `x`.
let walk_out (g: heap) (x: obj_addr) (p: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ steps_to g z p)
          (ensures p < U64.v x \/ p >= fields_end g x)
  = if p <> U64.v x - 8 then apart g x p

/// Headers the walk reaches are kept.
let hdr_kept (g g': heap) (x: obj_addr) (p: nat)
  : Lemma (requires fctx g g' x /\ steps_to g z p)
          (ensures hdr g' p == hdr g p /\ words_at g' p == words_at g p /\
                   color_at g' p == color_at g p)
  = walk_out g x p;
    if p < heap_size && p % 8 = 0 then
      assert (read_word g' (mk_hp_addr p) == read_word g (mk_hp_addr p))

/// The walk from a position the walk reaches is kept.
#push-options "--fuel 1 --ifuel 1"
let rec walk_eq (g g': heap) (x: obj_addr) (s b: nat)
  : Lemma (requires fctx g g' x /\ steps_to g z s)
          (ensures steps_to g' s b == steps_to g s b)
          (decreases (if s <= b then b - s else 0))
  = if s = b || s > b || b > heap_size || s % 8 <> 0 then ()
    else begin
      let sa = mk_hp_addr s in
      hdr_kept g g' x s;
      assert (read_word g' sa == read_word g sa);
      let nx = s + block_bytes g sa in
      if nx <= b then begin
        steps_to_one g sa nx;
        steps_to_trans g z s nx;
        walk_eq g g' x nx b
      end
    end
#pop-options

/// Every object of either heap is an object of both, with the same header.
let obj_same (g g': heap) (x: obj_addr) (y: obj_addr)
  : Lemma (requires fctx g g' x)
          (ensures (Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g)) /\
                   (Seq.mem y (objects zero_addr g) ==>
                      read_word g' (hd_address y) == read_word g (hd_address y)))
  = let h = U64.v y - 8 in
    hd_address_spec y;
    steps_to_refl g z;
    walk_eq g g' x z h;
    obj_iff g y;
    obj_iff g' y;
    hdr_obj g y;
    hdr_obj g' y;
    if steps_to g z h then hdr_kept g g' x h

/// The block of another object lies away from the fields of `x`.
let other_apart (g: heap) (x y: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\ y <> x)
          (ensures fields_end g y <= U64.v x - 8 \/ U64.v y - 8 >= fields_end g x)
  = hd_address_spec y;
    obj_iff g y;
    hdr_obj g y;
    apart g x (U64.v y - 8)

/// ---------------------------------------------------------------------------
/// The pages
/// ---------------------------------------------------------------------------

/// What the clauses of a pool page read of slot `k`.
let slot_same (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c}) : prop =
  (slot_free g' i c k <==> slot_free g i c k) /\
  (slot_used g' i c k <==> slot_used g i c k) /\
  color_at g' (slot_base i c k) == color_at g (slot_base i c k) /\
  (slot_free g i c k ==> hdr g' (slot_obj i c k) == hdr g (slot_obj i c k))

#push-options "--z3rlimit 40"
let slot_fill (g g': heap) (x: obj_addr) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires fctx g g' x /\ ~(is_blue x g) /\
                    steps_to g z (slot_base i c k) /\ slot_ok g i c k)
          (ensures slot_same g g' i c k)
  = let a = slot_base i c k in
    cls_bounds c;
    slot_reads g i c k;
    page_base_mono (i + 1) n_pages;
    slot_base_aligned i c k;
    hdr_kept g g' x a;
    if words_at g a < cls c then begin
      let w = words_at g a in
      block_steps g a w;
      steps_to_trans g z a (a + w * 8);
      hdr_kept g g' x (a + w * 8)
    end;
    if color_at g a = Blue then begin
      (* a free slot is not `x`, so its link word is not a field of `x` *)
      hdr_obj g x;
      is_blue_iff x g;
      apart g x a;
      if a + 8 < heap_size then
        assert (read_word g' (mk_hp_addr (a + 8)) == read_word g (mk_hp_addr (a + 8)))
    end
#pop-options

let slots_same (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : prop =
  forall (k: nat{k < n_slots c}). slot_same g g' i c k

let pool_fill_slots (g g': heap) (x: obj_addr) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires fctx g g' x /\ ~(is_blue x g) /\
                    steps_to g z (page_base i) /\ pool_shape g i c)
          (ensures slots_same g g' i c /\
                   (tail_words c > 0 ==> hdr g' (slots_end i c) == hdr g (slots_end i c)))
  = let aux (k: nat{k < n_slots c}) : Lemma (slot_same g g' i c k)
      = slots_steps g i c k;
        steps_to_trans g z (page_base i) (slot_base i c k);
        slot_fill g g' x i c k
    in
    FStar.Classical.forall_intro aux;
    slots_steps g i c (n_slots c);
    steps_to_trans g z (page_base i) (slots_end i c);
    if tail_words c > 0 then hdr_kept g g' x (slots_end i c)

#push-options "--fuel 1"
let rec slot_chain_same (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (hd: U64.t) (ks: list nat)
  : Lemma (requires slots_same g g' i c /\ slot_chain g i c hd ks)
          (ensures slot_chain g' i c hd ks)
          (decreases ks)
  = match ks with
    | [] -> ()
    | k :: ks' ->
      assert (slot_same g g' i c k);
      slot_chain_same g g' i c (hdr g (slot_obj i c k)) ks'
#pop-options

let pool_list_same (g g': heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires (entry pm i).kind == Pool c /\ slots_same g g' i c /\ pool_list_ok g pm i)
          (ensures pool_list_ok g' pm i)
  = if (entry pm i).swept then
      eliminate exists (ks: list nat).
        slot_chain g i c (entry pm i).free_head ks /\ L.noRepeats ks /\
        (forall (k: nat). k < n_slots c ==> (L.mem k ks <==> slot_free g i c k)) /\
        (entry pm i).nfree == L.length ks
      with begin
        slot_chain_same g g' i c (entry pm i).free_head ks;
        let aux (k: nat) : Lemma (k < n_slots c ==> (slot_free g' i c k <==> slot_free g i c k))
          = if k < n_slots c then assert (slot_same g g' i c k)
        in
        FStar.Classical.forall_intro aux
      end

let pool_fill (g g': heap) (x: obj_addr) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires fctx g g' x /\ ~(is_blue x g) /\ (entry pm i).kind == Pool c /\
                    steps_to g z (page_base i) /\ page_local g pm i)
          (ensures page_local g' pm i)
  = pool_fill_slots g g' x i c;
    let aux (k: nat)
      : Lemma (k < n_slots c ==>
               slot_ok g' i c k /\
               (slot_used g' i c k <==> slot_used g i c k) /\
               color_at g' (slot_base i c k) == color_at g (slot_base i c k))
      = if k < n_slots c then assert (slot_same g g' i c k)
    in
    FStar.Classical.forall_intro aux;
    pool_list_same g g' pm i c

/// The blocks of a run, and what they read, are kept.
let run_block_fill (g g': heap) (x: obj_addr) (h: nat) (n: pos) (a: nat)
  : Lemma (requires fctx g g' x /\ steps_to g z (page_base h) /\
                    steps_to g (page_base h) (page_base (h + n)))
          (ensures (run_block g' h n a <==> run_block g h n a) /\
                   (run_block g h n a ==>
                      color_at g' a == color_at g a /\ words_at g' a == words_at g a /\
                      (a + words_at g a * 8 < page_base (h + n) ==>
                         color_at g' (a + words_at g a * 8) == color_at g (a + words_at g a * 8))))
  = walk_eq g g' x (page_base h) a;
    if run_block g h n a then begin
      steps_to_trans g z (page_base h) a;
      block_before g (page_base h) a (page_base (h + n));
      steps_to_le g (page_base h) a;
      steps_to_le g (page_base h) (page_base (h + n));
      hdr_kept g g' x a;
      let nx = a + words_at g a * 8 in
      if nx < page_base (h + n) then begin
        block_steps g a (words_at g a);
        steps_to_trans g z a nx;
        hdr_kept g g' x nx
      end
    end

let run_fill (g g': heap) (x: obj_addr) (pm: page_map) (i: nat{i < n_pages}) (n: pos)
  : Lemma (requires fctx g g' x /\ (entry pm i).kind == LargeHead n /\
                    steps_to g z (page_base i) /\ page_local g pm i)
          (ensures page_local g' pm i)
  = walk_eq g g' x (page_base i) (page_base (i + n));
    steps_to_le g (page_base i) (page_base (i + n));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (run_block_fill g g' x i n))

/// **Every page keeps its clauses.**
let page_fill (g g': heap) (x: obj_addr) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires fctx g g' x /\ ~(is_blue x g) /\ shape_ok g pm /\ page_local g pm i)
          (ensures page_local g' pm i)
  = match (entry pm i).kind with
    | LargeCont -> ()
    | Free ->
      walk_pages_reached g pm i;
      hdr_kept g g' x (page_base i)
    | Pool c ->
      walk_pages_reached g pm i;
      pool_fill g g' x pm i c
    | LargeHead n ->
      walk_pages_reached g pm i;
      run_fill g g' x pm i n

let tail_fill (g g': heap) (x: obj_addr) (pm: page_map)
  : Lemma (requires fctx g g' x /\ shape_ok g pm)
          (ensures tail_shape g')
  = walk_pages_reached g pm n_pages;
    hdr_kept g g' x pages_end

/// ---------------------------------------------------------------------------
/// The large lists
/// ---------------------------------------------------------------------------

/// A free block's header and link are kept.
let free_kept (g g': heap) (x: obj_addr) (y: obj_addr)
  : Lemma (requires fctx g g' x /\ ~(is_blue x g) /\
                    Seq.mem y (objects zero_addr g) /\ is_blue y g)
          (ensures read_word g' (hd_address y) == read_word g (hd_address y) /\
                   (U64.v (wosize_of_object y g) >= 1 ==>
                      read_word g' (y <: hp_addr) == read_word g (y <: hp_addr)))
  = obj_same g g' x y;
    other_apart g x y;
    wosize_of_object_spec y g

let lview_fill (g g': heap) (x: obj_addr) (st: pstate) (cs: list obj_addr)
  : Lemma (requires fctx g g' x /\ ~(is_blue x g) /\ lview g st cs)
          (ensures lview g' st cs)
  = let in_cs (y: obj_addr)
      : Lemma (requires L.mem y cs)
              (ensures Seq.mem y (objects zero_addr g') /\
                       U64.v (wosize_of_object y g') >= 1 /\
                       read_word g' (y <: hp_addr) == read_word g (y <: hp_addr) /\
                       is_blue y g' /\ large_listable g' st.pm y)
      = cells_mem g (large_head st) cs y;
        obj_same g g' x y;
        free_kept g g' x y;
        color_of_header_eq y g g';
        wosize_of_object_spec y g;
        wosize_of_object_spec y g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires in_cs);
    cells_frame g g' (large_head st) cs;
    let complete (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' st.pm y)
              (ensures L.mem y cs)
      = obj_same g g' x y;
        color_of_header_eq y g g';
        wosize_of_object_spec y g;
        wosize_of_object_spec y g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires complete)

/// ---------------------------------------------------------------------------
/// The fields
/// ---------------------------------------------------------------------------

/// A target that resolved to an object that is not free still does, unless
/// it lay in the fields of `x`, which only a closure may hold.
#push-options "--z3rlimit 40"
let target_kept (g g': heap) (x: obj_addr) (v: obj_addr)
  : Lemma (requires fctx g g' x /\ ~(is_closure x g) /\
                    Seq.mem (resolve_object v g) (objects zero_addr g) /\
                    infix_addr_wf g (objects zero_addr g) v /\
                    ~(is_blue (resolve_object v g) g))
          (ensures Seq.mem (resolve_object v g') (objects zero_addr g') /\
                   infix_addr_wf g' (objects zero_addr g') v /\
                   ~(is_blue (resolve_object v g') g'))
  = hd_address_spec v;
    if is_infix v g then begin
      infix_addr_wf_elim g (objects zero_addr g) v;
      let w = U64.v (wosize_of_object v g) in
      let p = U64.v v - w * 8 in
      let pa : obj_addr = U64.uint_to_t p in
      wosize_of_object_spec pa g;
      if pa = x then assert False
      else other_apart g x pa;
      assert (read_word g' (hd_address v) == read_word g (hd_address v));
      resolve_object_locality v g g';
      obj_same g g' x pa;
      resolve_object_locality pa g g';
      infix_addr_wf_transfer g g' (objects zero_addr g) (objects zero_addr g') v
    end else begin
      resolve_non_infix v g;
      obj_same g g' x v;
      resolve_object_locality v g g';
      infix_addr_wf_non_infix g' (objects zero_addr g') v
    end;
    let r = resolve_object v g in
    obj_same g g' x r;
    color_of_header_eq r g g'
#pop-options

/// Every pointer field of the new heap resolves to an object that is not
/// free.
#push-options "--z3rlimit 40"
let field_fill (g g': heap) (x: obj_addr) (src: obj_addr) (j: nat) (v: obj_addr)
  : Lemma (requires fctx g g' x /\ ~(is_blue x g) /\ ~(is_closure x g) /\
                    well_formed_heap g /\ Mark.no_pointer_to_blue g /\
                    (forall (a: hp_addr). U64.v x <= U64.v a /\ U64.v a < fields_end g x ==>
                       field_ok g' (read_word g' a)) /\
                    Seq.mem src (objects zero_addr g') /\ fields_constrained g' src /\
                    field_at g' src j /\ read_word g' (field_addr src j) == (v <: U64.t) /\
                    is_pointer (v <: U64.t))
          (ensures Seq.mem (resolve_object v g') (objects zero_addr g') /\
                   infix_addr_wf g' (objects zero_addr g') v /\
                   ~(is_blue (resolve_object v g') g'))
  = obj_same g g' x src;
    wosize_of_object_spec src g;
    wosize_of_object_spec src g';
    if src = x then assert (field_ok g' (read_word g' (field_addr src j)))
    else begin
      other_apart g x src;
      color_of_header_eq src g g';
      is_no_scan_spec src g;
      is_no_scan_spec src g';
      tag_of_object_spec src g;
      tag_of_object_spec src g';
      assert (read_word g (field_addr src j) == read_word g' (field_addr src j));
      old_target g src j v;
      target_kept g g' x v
    end
#pop-options

let fill_part4 (g g': heap) (x: obj_addr)
  : Lemma (requires fctx g g' x /\ well_formed_heap_part4 g)
          (ensures well_formed_heap_part4 g')
  = let aux (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g'))
              (ensures ~(is_infix y g'))
      = obj_same g g' x y;
        resolve_object_locality y g g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let fill_heap (g g': heap) (x: obj_addr)
  : Lemma (requires fctx g g' x /\ ~(is_blue x g) /\ ~(is_closure x g) /\
                    well_formed_heap g /\ Mark.no_pointer_to_blue g /\
                    (forall (a: hp_addr). U64.v x <= U64.v a /\ U64.v a < fields_end g x ==>
                       field_ok g' (read_word g' a)))
          (ensures well_formed_heap g' /\ Mark.no_pointer_to_blue g')
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    part1_always g';
    fill_part4 g g' x;
    let closure (src: obj_addr) (j: nat)
      : Lemma (requires Seq.mem src (objects zero_addr g') /\ fields_constrained g' src /\
                        j < U64.v (wosize_of_object src g') /\
                        U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let v = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer v ==>
                        Seq.mem (resolve_object (v <: obj_addr) g') (objects zero_addr g') /\
                        infix_addr_wf g' (objects zero_addr g') (v <: obj_addr)))
      = let v = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
        assert (U64.uint_to_t (U64.v src + j * 8) == field_addr src j);
        if is_pointer v then field_fill g g' x src j v
    in
    well_formed_heap_part2_3_from_resolved_field_closure g' closure;
    let field (src: obj_addr) (dst: obj_addr) (j: nat)
      : Lemma (requires Seq.mem src (objects zero_addr g') /\
                        ~(is_blue src g') /\
                        fields_constrained g' src /\
                        j < U64.v (wosize_of_object src g') /\
                        U64.v src + j * 8 + 8 <= heap_size /\
                        is_pointer_to (read_word g' (U64.uint_to_t (U64.v src + j * 8))) dst)
              (ensures ~(is_blue (resolve_object dst g') g'))
      = let v = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
        assert (U64.uint_to_t (U64.v src + j * 8) == field_addr src j);
        hd_address_spec dst;
        hd_address_spec v;
        assert (v == (dst <: U64.t));
        field_fill g g' x src j dst
    in
    Mark.no_pointer_to_blue_intro_from_fields g' field

/// ---------------------------------------------------------------------------
/// The lemma
/// ---------------------------------------------------------------------------

/// **Writing the fields of an object that is neither free nor a closure with
/// values `field_ok` allows keeps `pages_ok` and `well_formed_heap`.**
let fill_ok (g g': heap) (st: pstate) (x: obj_addr)
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ ~(is_closure x g) /\
                    (forall (a: hp_addr). U64.v a < U64.v x \/ U64.v a >= fields_end g x ==>
                       read_word g' a == read_word g a) /\
                    (forall (a: hp_addr). U64.v x <= U64.v a /\ U64.v a < fields_end g x ==>
                       field_ok g' (read_word g' a)))
          (ensures pages_ok g' st /\ well_formed_heap g')
  = pages_ok_elim g st;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (page_fill g g' x st.pm));
    tail_fill g g' x st.pm;
    large_ok_lview g st;
    lview_fill g g' x st (walk g (large_head st) heap_words);
    lview_large_ok g' st (walk g (large_head st) heap_words);
    fill_heap g g' x;
    pages_ok_intro g' st

/// **The caller can always do it**: clearing the fields writes valid values.
let cleared_written (g: heap) (x: obj_addr)
  : Lemma (fields_written g (zeros g (U64.v x) (U64.v (wosize_of_object x g))) x)
  = let n = U64.v (wosize_of_object x g) in
    let aux (a: hp_addr)
      : Lemma (read_word (zeros g (U64.v x) n) a ==
               (if U64.v x <= U64.v a && U64.v a < U64.v x + n * 8 then 0UL else read_word g a))
      = zeros_read g (U64.v x) n a
    in
    FStar.Classical.forall_intro aux
