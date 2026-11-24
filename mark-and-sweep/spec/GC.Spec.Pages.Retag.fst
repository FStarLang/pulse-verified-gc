/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Retag - rewriting the header of an object at its size and colour
/// ---------------------------------------------------------------------------
///
/// Plan §27.1.  `rctx g g' x`: `g'` is `g` but for the header word of `x`,
/// an object of `g` that is not free, rewritten at the same wosize and
/// colour (a new tag).  The page clauses read headers only through
/// `words_at` and `color_at`, and the links of free blocks, which lie away
/// from the header of `x`; so the walk, the objects and `Sc.core` are kept
/// (`core_retag`), as `GC.Spec.Pages.Fill` keeps them when the fields of
/// `x` change.  With the old tag not a closure, the pointer clauses are kept
/// too (`wf_retag`).

module GC.Spec.Pages.Retag

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

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module F = GC.Spec.Pages.Fill
module Sc = GC.Spec.Pages.Scrub

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The context
/// ---------------------------------------------------------------------------

/// `g'` is `g` but for the header of `x`, at the same size and colour.
let rctx (g g': heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
  (forall (a: hp_addr). a <> hd_address x ==> read_word g' a == read_word g a) /\
  words_at g' (U64.v x - 8) == words_at g (U64.v x - 8) /\
  color_at g' (U64.v x - 8) == color_at g (U64.v x - 8)

/// Every position keeps its size and colour, and all but the header of `x`
/// their word.
let r_hdr (g g': heap) (x: obj_addr) (p: nat)
  : Lemma (requires rctx g g' x)
          (ensures words_at g' p == words_at g p /\ color_at g' p == color_at g p /\
                   (p <> U64.v x - 8 ==> hdr g' p == hdr g p))
  = hd_address_spec x;
    if p < heap_size && p % 8 = 0 && p <> U64.v x - 8 then
      assert (read_word g' (mk_hp_addr p) == read_word g (mk_hp_addr p))

/// The walk is kept.
#push-options "--fuel 1 --ifuel 1"
let rec r_steps (g g': heap) (x: obj_addr) (a b: nat)
  : Lemma (requires rctx g g' x)
          (ensures steps_to g' a b == steps_to g a b)
          (decreases (if a <= b then b - a else 0))
  = if a = b || a > b || b > heap_size || a % 8 <> 0 then ()
    else begin
      r_hdr g g' x a;
      assert (block_bytes g' (mk_hp_addr a) == block_bytes g (mk_hp_addr a));
      let nx = a + block_bytes g (mk_hp_addr a) in
      if nx <= b then r_steps g g' x nx b
    end
#pop-options

/// The objects are kept, and every header but that of `x`.
let r_obj (g g': heap) (x: obj_addr) (y: obj_addr)
  : Lemma (requires rctx g g' x)
          (ensures (Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g)) /\
                   (y <> x ==> read_word g' (hd_address y) == read_word g (hd_address y)))
  = hd_address_spec y;
    hd_address_spec x;
    obj_iff g y;
    obj_iff g' y;
    r_steps g g' x z (U64.v y - 8);
    r_hdr g g' x (U64.v y - 8)

/// Membership in the objects and blueness are kept.
let r_objs (g g': heap) (x: obj_addr)
  : Lemma (requires rctx g g' x)
          (ensures (forall (y: obj_addr). Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g)) /\
                   (forall (y: obj_addr). is_blue y g' <==> is_blue y g))
  = let aux (y: obj_addr)
      : Lemma ((Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g)) /\
               (is_blue y g' <==> is_blue y g))
      = r_obj g g' x y;
        hdr_obj g y;
        hdr_obj g' y;
        r_hdr g g' x (U64.v y - 8);
        is_blue_iff y g;
        is_blue_iff y g'
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// The pages
/// ---------------------------------------------------------------------------

/// A free slot's link word is not the header of `x`.
#push-options "--z3rlimit 30"
let slot_link (g: heap) (x: obj_addr) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    steps_to g z (slot_base i c k) /\ slot_free g i c k)
          (ensures slot_obj i c k <> U64.v x - 8)
  = let a = slot_base i c k in
    cls_bounds c;
    hdr_obj g x;
    is_blue_iff x g;
    F.apart g x a
#pop-options

let all_eq (g g': heap) (x: obj_addr)
  : Lemma (requires rctx g g' x)
          (ensures (forall (p: nat). words_at g' p == words_at g p /\ color_at g' p == color_at g p) /\
                   (forall (a b: nat). steps_to g' a b == steps_to g a b))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (r_hdr g g' x));
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (r_steps g g' x))

#push-options "--z3rlimit 30"
let slot_eq (g g': heap) (x: obj_addr) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
  : Lemma (requires rctx g g' x)
          (ensures (slot_free g' i c k <==> slot_free g i c k) /\
                   (slot_used g' i c k <==> slot_used g i c k) /\
                   (slot_ok g' i c k <==> slot_ok g i c k))
  = let a = slot_base i c k in
    r_hdr g g' x a;
    r_hdr g g' x (a + words_at g a * 8)
#pop-options

let pool_shape_eq (g g': heap) (x: obj_addr) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires rctx g g' x)
          (ensures pool_shape g' i c <==> pool_shape g i c)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (slot_eq g g' x i c));
    r_hdr g g' x (slots_end i c)

let page_shape_eq (g g': heap) (x: obj_addr) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires rctx g g' x)
          (ensures page_shape g' pm i <==> page_shape g pm i)
  = match (entry pm i).kind with
    | Free -> r_hdr g g' x (page_base i)
    | Pool c -> pool_shape_eq g g' x i c
    | LargeHead n -> r_steps g g' x (page_base i) (page_base (i + n))
    | LargeCont -> ()

#push-options "--fuel 1"
let rec slot_chain_r (g g': heap) (x: obj_addr) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (hd: U64.t) (ks: list nat)
  : Lemma (requires rctx g g' x /\ slot_chain g i c hd ks /\
                    (forall (k: nat{k < n_slots c}). steps_to g z (slot_base i c k)))
          (ensures slot_chain g' i c hd ks)
          (decreases ks)
  = match ks with
    | [] -> ()
    | k :: ks' ->
      slot_eq g g' x i c k;
      slot_link g x i c k;
      r_hdr g g' x (slot_obj i c k);
      slot_chain_r g g' x i c (hdr g (slot_obj i c k)) ks'
#pop-options

let pool_list_r (g g': heap) (x: obj_addr) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires rctx g g' x /\ (entry pm i).kind == Pool c /\ pool_list_ok g pm i /\
                    (forall (k: nat{k < n_slots c}). steps_to g z (slot_base i c k)))
          (ensures pool_list_ok g' pm i)
  = if (entry pm i).swept then
      eliminate exists (ks: list nat).
        slot_chain g i c (entry pm i).free_head ks /\ L.noRepeats ks /\
        (forall (k: nat). k < n_slots c ==> (L.mem k ks <==> slot_free g i c k)) /\
        (entry pm i).nfree == L.length ks
      with begin
        slot_chain_r g g' x i c (entry pm i).free_head ks;
        FStar.Classical.forall_intro (FStar.Classical.move_requires (slot_eq g g' x i c))
      end

let pool_white_r (g g': heap) (x: obj_addr) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires rctx g g' x /\ pool_white g pm i) (ensures pool_white g' pm i)
  = match (entry pm i).kind with
    | Pool c ->
      FStar.Classical.forall_intro (FStar.Classical.move_requires (slot_eq g g' x i c));
      all_eq g g' x
    | _ -> ()

let run_swept_r (g g': heap) (x: obj_addr) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires rctx g g' x /\ run_swept_ok g pm i) (ensures run_swept_ok g' pm i)
  = all_eq g g' x

/// **Every page keeps its clauses.**
#push-options "--z3rlimit 30"
let page_retag (g g': heap) (x: obj_addr) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires rctx g g' x /\ shape_ok g pm /\ page_local g pm i)
          (ensures page_local g' pm i)
  = page_shape_eq g g' x pm i;
    pool_white_r g g' x pm i;
    run_swept_r g g' x pm i;
    match (entry pm i).kind with
    | Pool c ->
      walk_pages_reached g pm i;
      let st (k: nat{k < n_slots c}) : Lemma (steps_to g z (slot_base i c k))
        = slots_steps g i c k;
          steps_to_trans g z (page_base i) (slot_base i c k)
      in
      FStar.Classical.forall_intro st;
      pool_list_r g g' x pm i c
    | _ -> ()
#pop-options

/// ---------------------------------------------------------------------------
/// The large lists
/// ---------------------------------------------------------------------------

/// A free block keeps its header and link.
let free_kept (g g': heap) (x: obj_addr) (y: obj_addr)
  : Lemma (requires rctx g g' x /\ Seq.mem y (objects zero_addr g) /\ is_blue y g)
          (ensures y <> x /\ read_word g' (hd_address y) == read_word g (hd_address y) /\
                   (U64.v (wosize_of_object y g) >= 1 ==>
                      read_word g' (y <: hp_addr) == read_word g (y <: hp_addr)))
  = r_obj g g' x y;
    F.other_apart g x y;
    hd_address_spec x;
    wosize_of_object_spec y g

let lview_retag (g g': heap) (x: obj_addr) (st: pstate) (cs: list obj_addr)
  : Lemma (requires rctx g g' x /\ lview g st cs)
          (ensures lview g' st cs)
  = r_objs g g' x;
    let in_cs (y: obj_addr)
      : Lemma (requires L.mem y cs)
              (ensures Seq.mem y (objects zero_addr g') /\
                       U64.v (wosize_of_object y g') >= 1 /\
                       read_word g' (y <: hp_addr) == read_word g (y <: hp_addr) /\
                       is_blue y g' /\ large_listable g' st.pm y)
      = cells_mem g (large_head st) cs y;
        free_kept g g' x y;
        wosize_of_object_spec y g;
        wosize_of_object_spec y g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires in_cs);
    cells_frame g g' (large_head st) cs;
    let complete (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' st.pm y)
              (ensures L.mem y cs)
      = free_kept g g' x y;
        wosize_of_object_spec y g;
        wosize_of_object_spec y g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires complete)

/// **`Sc.core` is kept.**
let core_retag (g g': heap) (x: obj_addr) (st: pstate)
  : Lemma (requires rctx g g' x /\ Sc.core g st) (ensures Sc.core g' st)
  = Sc.core_shape g st;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (page_retag g g' x st.pm));
    r_hdr g g' x pages_end;
    large_ok_lview g st;
    lview_retag g g' x st (walk g (large_head st) heap_words);
    lview_large_ok g' st (walk g (large_head st) heap_words)

/// ---------------------------------------------------------------------------
/// The pointer clauses
/// ---------------------------------------------------------------------------

/// `exists_field_pointing_to_unchecked` reads only the words it scans
/// (`GC.Spec.SweepPhase.Intrinsic.efptu_congr`, private there).
#push-options "--fuel 1 --ifuel 0"
let rec efptu_congr (h1 h2: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma (requires forall (a: hp_addr).
                      U64.v a >= U64.v src /\ U64.v a + 8 <= U64.v src + U64.v wz * 8 ==>
                      read_word h1 a == read_word h2 a)
          (ensures exists_field_pointing_to_unchecked h1 src wz dst ==
                   exists_field_pointing_to_unchecked h2 src wz dst)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_plus 54 3;
      assert_norm (pow2 3 == 8);
      assert (U64.v idx * 8 < pow2 57);
      FStar.Math.Lemmas.pow2_lt_compat 64 57;
      FStar.Math.Lemmas.small_mod (U64.v idx * 8) (pow2 64);
      assert (U64.v (U64.mul_mod idx mword) == U64.v idx * 8);
      FStar.Math.Lemmas.pow2_double_sum 57;
      FStar.Math.Lemmas.pow2_lt_compat 64 58;
      FStar.Math.Lemmas.small_mod (U64.v src + U64.v idx * 8) (pow2 64);
      assert (U64.v (U64.add_mod src (U64.mul_mod idx mword)) == U64.v src + U64.v idx * 8);
      efptu_congr h1 h2 src idx dst
    end
#pop-options

/// `g'` is `g` but for the block of `x`: its header and its fields.
let bframe (g g': heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\
  (forall (a: hp_addr). U64.v a < U64.v x - 8 \/ U64.v a >= F.fields_end g x ==> read_word g' a == read_word g a)

let rctx_bframe (g g': heap) (x: obj_addr)
  : Lemma (requires rctx g g' x) (ensures bframe g g' x)
  = hd_address_spec x

let fctx_bframe (g g': heap) (x: obj_addr)
  : Lemma (requires F.fctx g g' x) (ensures bframe g g' x)
  = ()

/// Another block lies away from the block of `x`, header included.
let other_away (g: heap) (x y: obj_addr) (a: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\ y <> x /\
                    U64.v y - 8 <= a /\ a < F.fields_end g y)
          (ensures a < U64.v x - 8 \/ a >= F.fields_end g x)
  = F.other_apart g x y

/// A source other than `x` keeps its header, size, scanning and edges.
#push-options "--z3rlimit 30"
let src_kept (g g': heap) (x src dst: obj_addr)
  : Lemma (requires bframe g g' x /\ Seq.mem src (objects zero_addr g) /\ src <> x)
          (ensures read_word g' (hd_address src) == read_word g (hd_address src) /\
                   wosize_of_object src g' == wosize_of_object src g /\
                   is_no_scan src g' == is_no_scan src g /\
                   points_to g' src dst == points_to g src dst)
  = hd_address_spec src;
    other_away g x src (U64.v src - 8);
    wosize_of_object_spec src g; wosize_of_object_spec src g';
    is_no_scan_spec src g; is_no_scan_spec src g';
    tag_of_object_spec src g; tag_of_object_spec src g';
    wosize_of_object_bound src g;
    let w (a: hp_addr)
      : Lemma (U64.v a >= U64.v src /\ U64.v a + 8 <= U64.v src + U64.v (wosize_of_object src g) * 8 ==>
               read_word g' a == read_word g a)
      = if U64.v a >= U64.v src && U64.v a + 8 <= U64.v src + U64.v (wosize_of_object src g) * 8
        then other_away g x src (U64.v a)
    in
    FStar.Classical.forall_intro w;
    efptu_congr g' g src (wosize_of_object src g) dst
#pop-options

/// A target of a block in use keeps its resolution, in use, and its
/// interior-pointer validity, when only the block of `x`, not a closure,
/// changed.
#push-options "--z3rlimit 40"
let tgt_kept (free: free_def) (g g': heap) (x dst: obj_addr)
  : Lemma (requires bframe g g' x /\ ~(is_closure x g) /\ ~(is_infix x g) /\ ~(is_infix x g') /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g)) /\
                    (forall (y: obj_addr). in_use free g' y == in_use free g y) /\
                    in_use free g (resolve_object dst g) /\ infix_addr_wf g (objects zero_addr g) dst)
          (ensures in_use free g' (resolve_object dst g') /\ infix_addr_wf g' (objects zero_addr g') dst)
  = hd_address_spec dst;
    if dst = x then begin
      resolve_non_infix x g;
      resolve_non_infix x g';
      infix_addr_wf_non_infix g' (objects zero_addr g') x
    end else if is_infix dst g then begin
      infix_addr_wf_elim g (objects zero_addr g) dst;
      parent_closure_addr_nat_spec dst g;
      resolve_infix_spec dst g;
      let w = U64.v (wosize_of_object dst g) in
      let p : obj_addr = U64.uint_to_t (U64.v dst - w * 8) in
      assert (p =!= x);
      hd_address_spec p;
      other_away g x p (U64.v p - 8);
      other_away g x p (U64.v dst - 8);
      resolve_object_locality dst g g';
      resolve_object_locality p g g';
      infix_addr_wf_transfer g g' (objects zero_addr g) (objects zero_addr g') dst
    end else begin
      resolve_non_infix dst g;
      other_away g x dst (U64.v dst - 8);
      resolve_object_locality dst g g';
      resolve_non_infix dst g';
      infix_addr_wf_non_infix g' (objects zero_addr g') dst
    end
#pop-options

/// **The pointer clauses are kept** when only the block of `x` changed, `x`
/// not a closure before and no infix block after, provided the blocks in
/// use are the same and `x`'s own edges, if it is scanned after, are fine.
#push-options "--z3rlimit 30"
let wf_kept (free: free_def) (g g': heap) (x: obj_addr)
  : Lemma (requires well_formed_heap_with free g /\ bframe g g' x /\
                    ~(is_closure x g) /\ ~(is_infix x g') /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g)) /\
                    (forall (y: obj_addr). in_use free g' y == in_use free g y) /\
                    (in_use free g' x /\ scannable g' x ==>
                       (forall (dst: obj_addr). points_to g' x dst ==>
                          in_use free g' (resolve_object dst g') /\ infix_addr_wf g' (objects zero_addr g') dst)))
          (ensures well_formed_heap_with free g')
  = wf_with_parts ();
    GC.Spec.SweepPhase.Util.part1_holds g';
    let ninf (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr g') ==> ~(is_infix y g'))
      = if Seq.mem y (objects zero_addr g') && y <> x then begin
          src_kept g g' x y y;
          resolve_object_locality y g g'
        end
    in
    FStar.Classical.forall_intro ninf;
    assert (~(is_infix x g));
    let tg (src dst: obj_addr)
      : Lemma (requires in_use free g' src /\ scannable g' src /\ points_to g' src dst)
              (ensures in_use free g' (resolve_object dst g') /\ infix_addr_wf g' (objects zero_addr g') dst)
      = if src = x then ()
        else begin
          src_kept g g' x src dst;
          points_to_target_not_free free g src dst;
          tgt_kept free g g' x dst
        end
    in
    pointers_lead_to_non_free_intro free g' (fun src dst -> tg src dst);
    interior_pointers_valid_intro free g' (fun src dst -> tg src dst)
#pop-options

/// Blocks in use other than `x` are kept by a change of the block of `x`.
let in_use_other (free: free_def) (g g': heap) (x y: obj_addr)
  : Lemma (requires free_def_ok free /\ bframe g g' x /\ y <> x /\
                    (Seq.mem y (objects zero_addr g') <==> Seq.mem y (objects zero_addr g)))
          (ensures in_use free g' y == in_use free g y)
  = if Seq.mem y (objects zero_addr g) then begin
      src_kept g g' x y y;
      in_use_is_determined_from_header free g g' y
    end

/// **A retag keeps well-formedness**: the old tag is no closure and was
/// scanned, the new one is not infix.
#push-options "--z3rlimit 30"
let wf_retag (free: free_def) (g g': heap) (x: obj_addr)
  : Lemma (requires well_formed_heap_with free g /\ free_def_ok free /\ rctx g g' x /\
                    ~(is_closure x g) /\ ~(is_no_scan x g) /\ ~(is_infix x g') /\
                    in_use free g' x == in_use free g x)
          (ensures well_formed_heap_with free g')
  = rctx_bframe g g' x;
    r_objs g g' x;
    let iu (y: obj_addr) : Lemma (in_use free g' y == in_use free g y)
      = if y <> x then in_use_other free g g' x y
    in
    FStar.Classical.forall_intro iu;
    wf_with_parts ();
    assert (~(is_infix x g));
    let own (dst: obj_addr)
      : Lemma (requires in_use free g' x /\ points_to g' x dst)
              (ensures in_use free g' (resolve_object dst g') /\ infix_addr_wf g' (objects zero_addr g') dst)
      = hd_address_spec x;
        r_hdr g g' x (U64.v x - 8);
        hdr_obj g x; hdr_obj g' x;
        wosize_of_object_bound x g;
        let w (a: hp_addr)
          : Lemma (U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                   read_word g' a == read_word g a)
          = ()
        in
        FStar.Classical.forall_intro w;
        efptu_congr g' g x (wosize_of_object x g) dst;
        points_to_target_not_free free g x dst;
        tgt_kept free g g' x dst
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires own);
    wf_kept free g g' x
#pop-options

/// **Writing the fields of a no-scan object keeps well-formedness**: they
/// are never read.
#push-options "--z3rlimit 30"
let wf_fill_noscan (free: free_def) (g g': heap) (x: obj_addr)
  : Lemma (requires well_formed_heap_with free g /\ free_def_ok free /\ F.fctx g g' x /\ is_no_scan x g)
          (ensures well_formed_heap_with free g')
  = fctx_bframe g g' x;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (F.obj_same g g' x));
    let iu (y: obj_addr) : Lemma (in_use free g' y == in_use free g y)
      = F.obj_same g g' x y;
        if Seq.mem y (objects zero_addr g) then in_use_is_determined_from_header free g g' y
    in
    FStar.Classical.forall_intro iu;
    F.obj_same g g' x x;
    hd_address_spec x;
    resolve_object_locality x g g';
    is_no_scan_spec x g; is_no_scan_spec x g';
    tag_of_object_spec x g; tag_of_object_spec x g';
    is_closure_spec x g;
    closure_tag_val ();
    no_scan_tag_val ();
    wf_with_parts ();
    wf_kept free g g' x
#pop-options

/// A value the tagged heap may hold in a field of `x`, other than a pointer
/// into the body of `x`, the untagged heap may hold too.
#push-options "--z3rlimit 40"
let field_back (free: free_def) (h h': heap) (x: obj_addr) (v: U64.t)
  : Lemma (requires rctx h h' x /\ ~(is_infix x h) /\ ~(is_infix x h') /\
                    (forall (y: obj_addr). in_use free h' y == in_use free h y) /\
                    GC.Spec.AllocIface.field_ok_with free h v /\
                    GC.Spec.Pages.AllocTag.away x (U64.v (wosize_of_object x h)) v)
          (ensures GC.Spec.AllocIface.field_ok_with free h' v)
  = r_objs h h' x;
    if is_pointer v then begin
      let d : obj_addr = v in
      hd_address_spec d; hd_address_spec x;
      if d = x then begin
        resolve_non_infix x h;
        resolve_non_infix x h';
        infix_addr_wf_non_infix h' (objects zero_addr h') x
      end else begin
        r_obj h h' x d;
        resolve_object_locality d h h';
        if is_infix d h then begin
          infix_addr_wf_elim h (objects zero_addr h) d;
          parent_closure_addr_nat_spec d h;
          resolve_infix_spec d h;
          let w = U64.v (wosize_of_object d h) in
          let p : obj_addr = U64.uint_to_t (U64.v d - w * 8) in
          assert (p =!= x);
          r_obj h h' x p;
          hd_address_spec p;
          resolve_object_locality p h h';
          infix_addr_wf_transfer h h' (objects zero_addr h) (objects zero_addr h') d
        end else begin
          resolve_non_infix d h;
          resolve_non_infix d h';
          infix_addr_wf_non_infix h' (objects zero_addr h') d
        end
      end
    end
#pop-options
