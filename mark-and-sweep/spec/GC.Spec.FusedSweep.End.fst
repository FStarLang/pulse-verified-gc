module GC.Spec.FusedSweep.End

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

module U64 = FStar.UInt64
module HeapGraph = GC.Spec.HeapGraph
module FLA = GC.Spec.FreeList.Ascending
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let sweep_post_elim g0 g fp = reveal_opaque (`%sweep_post) (sweep_post g0 g fp)

/// ---------------------------------------------------------------------------
/// Consequences
/// ---------------------------------------------------------------------------

let sweep_post_white_or_blue (g0 g: heap) (fp: U64.t) (x: obj_addr) =
  sweep_post_elim g0 g fp

/// A survivor's word at `a`, inside its body.
let survivor_word (g0 g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr)
  : Lemma (requires sweep_post g0 g fp /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0 /\
                    U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g0) * 8)
          (ensures read_word g a == read_word g0 a)
  = sweep_post_elim g0 g fp

#push-options "--z3rlimit 60"
let sweep_post_target (g0 g: heap) (fp: U64.t) (src dst: obj_addr) =
  sweep_post_elim g0 g fp;
  wf_parts ();
  let objs0 = objects zero_addr g0 in
  Mark.colors_exclusive src g0;
  pointers_lead_to_non_free_elim free_stw g0 src dst;
  interior_pointers_valid_elim free_stw g0 src dst;
  let r = resolve_object dst g0 in
  // the target is black: not white (tri-colour), not grey, not blue
  assert (~(is_white r g0));
  assert (~(is_gray r g0));
  assert (~(is_blue r g0));
  Mark.color_exhaustive r g0;
  assert (is_black r g0);
  assert (survives g0 g r);
  if is_infix dst g0 then begin
    infix_addr_wf_elim g0 objs0 dst;
    parent_closure_addr_nat_spec dst g0;
    resolve_infix_spec dst g0;
    hd_address_spec dst;
    let a : hp_addr = hd_address dst in
    survivor_word g0 g fp r a;
    resolve_object_locality dst g g0
  end else begin
    resolve_non_infix dst g0;
    white_header_facts (read_word g0 (hd_address dst));
    tag_of_object_spec dst g; tag_of_object_spec dst g0;
    wosize_of_object_spec dst g; wosize_of_object_spec dst g0;
    is_infix_spec dst g; is_infix_spec dst g0;
    resolve_non_infix dst g
  end
#pop-options

/// `exists_field_pointing_to_unchecked` reads only the words it scans.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec efptu_congr (h1 h2: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54})
    (dst: obj_addr)
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

/// A survivor points where it pointed.
#push-options "--z3rlimit 40"
let survivor_points_to (g0 g: heap) (fp: U64.t) (src dst: obj_addr)
  : Lemma (requires sweep_post g0 g fp /\ Seq.mem src (objects zero_addr g0) /\ is_black src g0)
          (ensures points_to g src dst == points_to g0 src dst)
  = sweep_post_elim g0 g fp;
    wosize_of_object_bound src g0;
    efptu_congr g g0 src (wosize_of_object src g0) dst
#pop-options

/// A live source of the result was a live (black) source of `g0`.
#push-options "--z3rlimit 40"
let live_source (g0 g: heap) (fp: U64.t) (src: obj_addr)
  : Lemma (requires sweep_post g0 g fp /\ Seq.mem src (objects zero_addr g) /\ ~(is_blue src g))
          (ensures Seq.mem src (objects zero_addr g0) /\ is_black src g0 /\ survives g0 g src /\
                   is_no_scan src g == is_no_scan src g0)
  = sweep_post_elim g0 g fp;
    Mark.colors_exclusive src g0;
    Mark.colors_exclusive src g
#pop-options

#push-options "--z3rlimit 60"
let sweep_post_wf (g0 g: heap) (fp: U64.t) =
  sweep_post_elim g0 g fp;
  wf_parts ();
  let objs = objects zero_addr g in
  let objs0 = objects zero_addr g0 in
  let p1 (h: obj_addr)
    : Lemma (Seq.mem h objs ==>
             (let wz = wosize_of_object h g in
              U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length g))
    = if Seq.mem h objs then begin
        objects_member_size_bound zero_addr g h;
        wosize_of_object_spec h g
      end
  in
  FStar.Classical.forall_intro p1;
  assert (blocks_fit g);
  assert (no_infix_block g);
  let facts (src dst: obj_addr)
    : Lemma (requires in_use free_stw g src /\ scannable g src /\ points_to g src dst)
            (ensures in_use free_stw g (resolve_object dst g) /\ infix_addr_wf g objs dst)
    = live_source g0 g fp src;
      survivor_points_to g0 g fp src dst;
      sweep_post_target g0 g fp src dst;
      let r = resolve_object dst g0 in
      assert (survives g0 g r);
      Mark.colors_exclusive r g;
      interior_pointers_valid_elim free_stw g0 src dst;
      if is_infix dst g0 then begin
        infix_addr_wf_elim g0 objs0 dst;
        parent_closure_addr_nat_spec dst g0;
        resolve_infix_spec dst g0;
        is_closure_spec r g; is_closure_spec r g0
      end;
      infix_addr_wf_transfer g0 g objs0 objs dst
  in
  pointers_lead_to_non_free_intro free_stw g (fun src dst -> facts src dst);
  interior_pointers_valid_intro free_stw g (fun src dst -> facts src dst)
#pop-options

#push-options "--z3rlimit 40"
let sweep_post_get_field (g0 g: heap) (fp: U64.t) (x: obj_addr) (i: U64.t{U64.v i >= 1}) =
  sweep_post_elim g0 g fp;
  hd_address_spec x;
  wosize_of_object_bound x g0;
  if U64.v (hd_address x) + U64.v mword * U64.v i + U64.v mword <= heap_size then begin
    HeapGraph.get_field_addr_eq g x i;
    HeapGraph.get_field_addr_eq g0 x i
  end
#pop-options

/// A pointer field of a survivor resolves the same way in both heaps.
#push-options "--z3rlimit 60"
let survivor_field_resolve (g0 g: heap) (fp: U64.t) (b: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires sweep_post g0 g fp /\ marked g0 /\
                    Seq.mem b (objects zero_addr g0) /\ is_black b g0 /\ ~(is_no_scan b g0) /\
                    U64.v j <= U64.v (wosize_of_object b g0))
          (ensures (let v = HeapGraph.get_field g0 b j in
                    HeapGraph.get_field g b j == v /\
                    HeapGraph.resolve_field g v == HeapGraph.resolve_field g0 v))
  = sweep_post_get_field g0 g fp b j;
    let v = HeapGraph.get_field g0 b j in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let vo : obj_addr = v in
      wf_parts ();
      let wz = wosize_of_object b g0 in
      wosize_of_object_bound b g0;
      wf_object_size_bound g0 b;
      hd_address_spec b;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      HeapGraph.get_field_addr_eq g0 b j;
      field_read_implies_exists_pointing g0 b wz (U64.sub j 1UL) vo;
      assert (points_to g0 b vo);
      sweep_post_target g0 g fp b vo
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let rec survivor_gpf_aux (g0 g: heap) (fp: U64.t) (b: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires sweep_post g0 g fp /\ marked g0 /\
                    Seq.mem b (objects zero_addr g0) /\ is_black b g0 /\ ~(is_no_scan b g0) /\
                    ws == wosize_of_object b g0)
          (ensures HeapGraph.get_pointer_fields_aux g b i ws ==
                   HeapGraph.get_pointer_fields_aux g0 b i ws)
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else begin
      survivor_field_resolve g0 g fp b i;
      if U64.v i < U64.v ws then survivor_gpf_aux g0 g fp b (U64.add i 1UL) ws
    end
#pop-options

#push-options "--z3rlimit 40"
let sweep_post_pointer_fields (g0 g: heap) (fp: U64.t) (x: obj_addr) =
  sweep_post_elim g0 g fp;
  Mark.colors_exclusive x g0;
  Mark.colors_exclusive x g;
  assert (survives g0 g x);
  if not (is_no_scan x g0) then survivor_gpf_aux g0 g fp x 1UL (wosize_of_object x g0)
#pop-options
