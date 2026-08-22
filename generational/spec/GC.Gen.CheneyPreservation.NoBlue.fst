/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.NoBlue -- proofs
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.NoBlue

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module Mark = GC.Spec.Mark
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module Injectivity = GC.Gen.CheneyPreservation.Injectivity
module Frame = GC.Gen.CheneyPreservation.Frame
module Fields = GC.Gen.CheneyPreservation.Fields
module NonBlueOrigin = GC.Gen.CheneyPreservation.NonBlueOrigin
module NoBlueUtil = GC.Gen.NoBlueUtil
module GenInv = GC.Gen.HeapInvariant

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let cheney_promote_preserves_no_pointer_to_blue_from_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures Mark.no_pointer_to_blue
      (cheney_promote minor major fp roots).major_final)
  =
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_wfh_part4 minor major fp roots;
  Injectivity.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  let field_no_blue (src dst: obj_addr) (j: nat)
    : Lemma
      (requires Seq.mem src (objects zero_addr prom.major_final) /\
                ~(is_blue src prom.major_final) /\
                j < U64.v (wosize_of_object src prom.major_final) /\
                U64.v src + j * 8 + 8 <= heap_size /\
                is_pointer_to
                  (read_word prom.major_final (U64.uint_to_t (U64.v src + j * 8)))
                  dst)
      (ensures ~(is_blue dst prom.major_final))
    =
    assert ((U64.v src + j * 8) % 8 == 0);
    let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
    let field_val = read_word prom.major_final field_addr in
    assert (is_pointer_field field_val);
    if Seq.mem src (objects zero_addr major) && is_blue src major = false then begin
      Frame.cheney_promote_frame_old_header minor major fp roots src;
      color_of_header_eq src major prom.major_final;
      assert (~(is_blue src major));
      wosize_of_object_spec src major;
      wosize_of_object_spec src prom.major_final;
      assert (j < U64.v (wosize_of_object src major));
      assert (U64.v src + j * 8 + 8 <= heap_size);
      assert (U64.v src + j * U64.v mword + U64.v mword <= heap_size);
      assert ((U64.v src + j * 8) % U64.v mword == 0);
      Frame.cheney_promote_frame_old_fields minor major fp roots src j;
      assert (read_word major field_addr == field_val);
      assert (is_pointer_to (read_word major field_addr) dst);
      NoBlueUtil.field_pointer_target_in_objects_nat major src dst j;
      NoBlueUtil.field_pointer_no_blue_from_no_pointer_to_blue major src dst j;
      Frame.cheney_promote_frame_old_header minor major fp roots dst;
      color_of_header_eq dst major prom.major_final;
      assert (~(is_blue dst prom.major_final))
    end else begin
      assert (~(Seq.mem src (objects zero_addr major) /\
                is_blue src major = false));
      NonBlueOrigin.cheney_promote_nonblue_origin minor major fp roots src;
      let goal = ~(is_blue dst prom.major_final) in
      let proof (x: U64.t)
        : Lemma
          (requires prom.fwd_map x == src /\ is_minor_pointer x)
          (ensures goal)
        =
        assert (U64.v (prom.fwd_map x) >= U64.v mword);
        assert (U64.v (prom.fwd_map x) < heap_size);
        assert (U64.v (prom.fwd_map x) % U64.v mword == 0);
        is_val_addr_spec (prom.fwd_map x);
        assert (is_val_addr (prom.fwd_map x));
        assert (well_formed_heap_part4 prom.major_final);
        assert (~(is_infix src prom.major_final));
        assert (is_infix (prom.fwd_map x) prom.major_final = false);
        assert (Injectivity.fwd_noninfix_sources_in_minor_objects
                  minor prom.fwd_map prom.major_final);
        assert (Seq.mem x (minor_objects minor));
        if j < minor_wosize minor x then begin
          Fields.cheney_promote_fwd_target_fields_match minor major fp roots x j;
          assert (read_word prom.major_final field_addr ==
                  minor_read_field minor x j);
          assert (is_pointer_to (minor_read_field minor x j) dst);
          assert (is_pointer_field (minor_read_field minor x j));
          GenInv.minor_major_fields_no_blue_elim minor major x j;
          let old_dst : obj_addr = minor_read_field minor x j in
          assert (hd_address old_dst == hd_address dst);
          if old_dst <> dst then begin
            hd_address_injective old_dst dst;
            assert False
          end;
          assert (old_dst == dst);
          Frame.cheney_promote_frame_old_header minor major fp roots old_dst;
          color_of_header_eq old_dst major prom.major_final;
          assert (~(is_blue dst prom.major_final))
        end else begin
          Fields.cheney_promote_fwd_target_extra_field_not_pointer minor major fp roots x j;
          assert (~(is_pointer_field field_val));
          assert False
        end
      in
      FStar.Classical.exists_elim goal #U64.t
        #(fun x -> prom.fwd_map x == src /\ is_minor_pointer x)
        ()
        (fun x -> FStar.Classical.move_requires proof x)
    end
  in
  Mark.no_pointer_to_blue_intro_from_fields prom.major_final field_no_blue
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let header_eq_preserves_no_scan
  (g1 g2: heap) (obj: obj_addr)
  : Lemma
    (requires read_word g1 (hd_address obj) == read_word g2 (hd_address obj))
    (ensures is_no_scan obj g1 == is_no_scan obj g2)
  =
  tag_of_object_spec obj g1;
  tag_of_object_spec obj g2;
  is_no_scan_spec obj g1;
  is_no_scan_spec obj g2

private let header_eq_preserves_infix
  (g1 g2: heap) (obj: obj_addr)
  : Lemma
    (requires read_word g1 (hd_address obj) == read_word g2 (hd_address obj))
    (ensures is_infix obj g1 == is_infix obj g2)
  =
  tag_of_object_spec obj g1;
  tag_of_object_spec obj g2;
  is_infix_spec obj g1;
  is_infix_spec obj g2
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let update_major_pointers_preserves_no_pointer_to_blue
  (major: heap) (fwd: forwarding_map)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      well_formed_heap (update_major_pointers major fwd) /\
      no_scan_invariant (update_major_pointers major fwd) /\
      Mark.no_pointer_to_blue major /\
      Forwarding.fwd_valid_or_infix fwd major /\
      Injectivity.fwd_targets_not_blue fwd major)
    (ensures Mark.no_pointer_to_blue (update_major_pointers major fwd))
  =
  let updated = update_major_pointers major fwd in
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  update_major_pointers_preserves_objects major fwd;
  update_major_pointers_preserves_wfh_part1 major fwd;
  let field_no_blue (src dst: obj_addr) (j: nat)
    : Lemma
      (requires Seq.mem src (objects zero_addr updated) /\
                ~(is_blue src updated) /\
                j < U64.v (wosize_of_object src updated) /\
                U64.v src + j * 8 + 8 <= heap_size /\
                is_pointer_to
                  (read_word updated (U64.uint_to_t (U64.v src + j * 8)))
                  dst)
      (ensures ~(is_blue dst updated))
    =
    assert (Seq.mem src (objects zero_addr major));
    update_major_pointers_preserves_header major fwd src;
    color_of_header_eq src major updated;
    header_eq_preserves_no_scan major updated src;
    wosize_of_object_spec src major;
    wosize_of_object_spec src updated;
    assert (~(is_blue src major));
    assert (j < U64.v (wosize_of_object src major));
    assert ((U64.v src + j * 8) % 8 == 0);
    NoBlueUtil.field_pointer_target_in_objects_nat updated src dst j;
    assert (Seq.mem dst (objects zero_addr updated));
    assert (Seq.mem dst (objects zero_addr major));
    update_major_pointers_preserves_header major fwd dst;
    if is_no_scan src major then begin
      assert (is_no_scan src updated);
      no_scan_invariant_elim updated src j;
      assert (is_pointer_field
        (read_word updated (U64.uint_to_t (U64.v src + j * 8))));
      assert False
    end else begin
      update_major_pointers_field_effect major fwd src j;
      let field_addr = U64.uint_to_t (U64.v src + j * 8) in
      let old_raw = read_word major field_addr in
      let old_val = to_minor_offset old_raw in
      let new_val = read_word updated field_addr in
      if is_minor_pointer old_val && fwd old_val <> 0UL then begin
        assert (new_val == fwd old_val);
        assert (U64.v (fwd old_val) >= U64.v mword);
        assert (U64.v (fwd old_val) < heap_size);
        assert (U64.v (fwd old_val) % U64.v mword == 0);
        let fwd_obj : obj_addr = fwd old_val in
        assert (is_pointer_to (fwd old_val) dst);
        if fwd_obj <> dst then begin
          hd_address_injective fwd_obj dst;
          assert False
        end;
        assert (fwd old_val == dst);
        wf_objects_non_infix updated dst;
        header_eq_preserves_infix major updated dst;
        assert (is_infix dst major = false);
        assert (is_infix (fwd old_val) major = false);
        assert (is_val_addr (fwd old_val));
        assert (is_blue ((fwd old_val) <: obj_addr) major = false);
        color_of_header_eq dst major updated;
        assert (~(is_blue dst updated))
      end else begin
        assert (new_val == old_raw);
        assert (is_pointer_to old_raw dst);
        NoBlueUtil.field_pointer_no_blue_from_no_pointer_to_blue major src dst j;
        color_of_header_eq dst major updated;
        assert (~(is_blue dst updated))
      end
    end
  in
  Mark.no_pointer_to_blue_intro_from_fields updated field_no_blue
#pop-options
