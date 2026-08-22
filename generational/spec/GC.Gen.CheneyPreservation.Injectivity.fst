/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Injectivity -- forwarding injectivity
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Injectivity

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
open GC.Gen.WriteBodyLemmas
open GC.Lib.Header

module Allocator = GC.Spec.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
open GC.Gen.CheneyPreservation.Forwarding
module Frame = GC.Gen.CheneyPreservation.Frame

/// `hd_address t` sits exactly one word below `t`, phrased additively.
/// `hd_address_spec` states the subtractive form; rephrasing it costs nothing
/// here and is a query Z3 4.15.3 will not finish inside the injectivity proof.
private let hd_address_succ_v (t: obj_addr)
  : Lemma (ensures U64.v (hd_address t) + 8 == U64.v t)
  = hd_address_spec t


/// ---------------------------------------------------------------------------
/// Injectivity
/// ---------------------------------------------------------------------------

let inj_inv (cs: cheney_state) : prop =
  fwd_normal_injective cs.cs_fwd cs.cs_major /\
  fwd_targets_not_blue cs.cs_fwd cs.cs_major

let source_inv (minor: minor_state) (cs: cheney_state) : prop =
  fwd_noninfix_sources_in_minor_objects minor cs.cs_fwd cs.cs_major

let old_nonblue_preserved (major0: heap) (cs: cheney_state) : prop =
  forall (y: obj_addr).
    Seq.mem y (objects zero_addr major0) /\
    is_blue y major0 = false ==>
    Seq.mem y (objects zero_addr cs.cs_major) /\
    is_blue y cs.cs_major = false

let disjoint_inv (major0: heap) (cs: cheney_state) : prop =
  old_nonblue_preserved major0 cs /\
  fwd_normal_targets_disjoint_from_old_nonblue cs.cs_fwd cs.cs_major major0

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let extend_infix_preserves_fwd_normal_injective
  (fwd: forwarding_map) (g: heap) (addr sum: U64.t)
  : Lemma (requires fwd_normal_injective fwd g /\
                    is_val_addr sum /\
                    is_infix (sum <: obj_addr) g)
          (ensures fwd_normal_injective (extend_forwarding fwd addr sum) g)
  =
  let fwd' = extend_forwarding fwd addr sum in
  let aux (x y: U64.t) : Lemma
    (requires fwd' x <> 0UL /\ fwd' y <> 0UL /\
              is_val_addr (fwd' x) /\ is_val_addr (fwd' y) /\
              is_infix (fwd' x) g = false /\
              is_infix (fwd' y) g = false /\
              fwd' x = fwd' y)
    (ensures x = y)
    =
    if x = addr then begin
      assert (fwd' x == sum);
      assert (is_infix (fwd' x) g);
      assert (is_infix (fwd' x) g = false);
      assert False
    end else if y = addr then begin
      assert (fwd' y == sum);
      assert (is_infix (fwd' y) g);
      assert (is_infix (fwd' y) g = false);
      assert False
    end else begin
      assert (fwd' x == fwd x);
      assert (fwd' y == fwd y);
      assert (fwd x <> 0UL);
      assert (fwd y <> 0UL);
      assert (is_val_addr (fwd x));
      assert (is_val_addr (fwd y));
      assert (is_infix (fwd x) g = false);
      assert (is_infix (fwd y) g = false);
      assert (fwd x = fwd y);
      assert (x = y)
    end
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let source_inv_elim (minor: minor_state) (cs: cheney_state) (x: U64.t)
  : Lemma (requires source_inv minor cs /\
                    cs.cs_fwd x <> 0UL /\
                    is_val_addr (cs.cs_fwd x) /\
                    is_infix (cs.cs_fwd x) cs.cs_major = false)
          (ensures Seq.mem x (minor_objects minor))
  = ()
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let old_nonblue_preserved_elim
  (major0: heap) (cs: cheney_state) (y: obj_addr)
  : Lemma (requires disjoint_inv major0 cs /\
                    Seq.mem y (objects zero_addr major0) /\
                    is_blue y major0 = false)
          (ensures Seq.mem y (objects zero_addr cs.cs_major) /\
                   is_blue y cs.cs_major = false)
  = ()

private let disjoint_inv_elim
  (major0: heap) (cs: cheney_state) (x: U64.t) (y: obj_addr)
  : Lemma (requires disjoint_inv major0 cs /\
                    cs.cs_fwd x <> 0UL /\
                    is_val_addr (cs.cs_fwd x) /\
                    is_infix (cs.cs_fwd x) cs.cs_major = false /\
                    Seq.mem y (objects zero_addr major0) /\
                    is_blue y major0 = false)
          (ensures cs.cs_fwd x <> y)
  = ()
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let chain_avoids_from_blue
  (major: heap) (fp: U64.t) (obj: obj_addr)
  : Lemma
    (requires chain_objects_blue major fp /\
              Seq.mem obj (objects zero_addr major) /\
              is_blue obj major = false)
    (ensures AllocLemmas.chain_avoids major fp obj heap_words = true)
  = reveal_opaque (`%chain_objects_blue) chain_objects_blue
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_normal minor cs addr).cs_major)
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then begin
    cheney_forward_normal_noop minor cs addr;
    assert (cheney_forward_normal minor cs addr == cs)
  end
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then begin
      cheney_forward_normal_noop_wz0 minor cs addr;
      assert (cheney_forward_normal minor cs addr == cs)
    end
    else begin
      assert (Seq.mem addr (minor_objects minor));
      assert (cs.cs_fwd addr = 0UL);
      assert (wz > 0);
      minor_objects_not_infix minor addr;
      GC.Spec.Object.infix_tag_val ();
      assert (minor_tag minor addr <> 249);
      assert (U64.v GC.Spec.Object.infix_tag == 249);
      assert (minor_tag minor addr <> U64.v GC.Spec.Object.infix_tag);
      promote_object_preserves_wfh_part4 minor cs.cs_major addr cs.cs_fp wz;
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then begin
        cheney_forward_normal_noop_oom minor cs addr;
        assert (cheney_forward_normal minor cs addr == cs)
      end else begin
        cheney_forward_normal_success minor cs addr;
        assert ((cheney_forward_normal minor cs addr).cs_major == res.major_out);
        assert (well_formed_heap_part4 res.major_out)
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let cheney_forward_one_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_one minor cs addr).cs_major)
  =
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (cheney_forward_one minor cs addr == cs)
  end
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    let parent = infix_parent minor addr in
    infix_parent_value minor addr;
    assert (U64.v parent == U64.v addr - minor_wosize minor addr * 8);
    assert (U64.v addr >= U64.v parent);
    cheney_forward_one_infix minor cs addr;
    cheney_forward_normal_preserves_wfh_part4_local minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    assert ((cheney_forward_one minor cs addr).cs_major == cs'.cs_major);
    assert (well_formed_heap_part4 (cheney_forward_one minor cs addr).cs_major)
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_wfh_part4_local minor cs addr;
    assert (cheney_forward_one minor cs addr ==
      cheney_forward_normal minor cs addr)
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_fields minor cs parent idx wosize).cs_major)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    cheney_forward_fields_base minor cs parent idx wosize
  else begin
    cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    cheney_forward_one_preserves_wfh_part4_local minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_wfh_part4_local minor cs' parent (idx + 1) wosize
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_preserves_wfh_part4_local
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_roots minor cs roots idx).cs_major)
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots idx
  else begin
    cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    cheney_forward_one_preserves_wfh_part4_local minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_wfh_part4_local minor cs' roots (idx + 1)
  end
#pop-options

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
private let promote_object_preserves_old_target_not_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (target: obj_addr)
  : Lemma
    (requires well_formed_heap_part1 major /\
              AllocLemmas.fl_valid major fp heap_words /\
              AllocLemmas.fl_chain_terminates major fp heap_words /\
              chain_objects_blue major fp /\
              (promote_object minor major obj fp wz).new_addr <> 0UL /\
              Seq.mem target (objects zero_addr major) /\
              is_blue target major = false)
    (ensures
      (let res = promote_object minor major obj fp wz in
       Seq.mem target (objects zero_addr res.major_out) /\
       is_blue target res.major_out = false))
  =
  let res = promote_object minor major obj fp wz in
  promote_object_success minor major obj fp wz;
  promote_object_preserves_objects_part1 minor major obj fp wz;
  chain_avoids_from_blue major fp target;
  AllocProps.alloc_spec_obj_ne_excl major fp wz target;
  assert (res.new_addr <> target);
  promote_object_frame_old_header_derived minor major obj fp wz target;
  color_of_header_eq target major res.major_out;
  is_blue_iff target major;
  is_blue_iff target res.major_out
#pop-options

#push-options "--z3rlimit 75 --fuel 1 --ifuel 0"
private let cheney_forward_normal_old_target_preserved
  (minor: minor_state) (cs: cheney_state) (addr: U64.t) (x: U64.t)
  : Lemma
    (requires inj_inv cs /\
              fwd_classified cs /\
              well_formed_heap_part4 cs.cs_major /\
              well_formed_heap_part1 cs.cs_major /\
              AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
              AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
              chain_objects_blue cs.cs_major cs.cs_fp /\
              Seq.mem addr (minor_objects minor) /\
               cs.cs_fwd addr = 0UL /\
               minor_wosize minor addr > 0 /\
               (promote_object minor cs.cs_major addr cs.cs_fp (minor_wosize minor addr)).new_addr <> 0UL /\
               x <> addr /\
               is_val_addr (cs.cs_fwd x) /\
               (cheney_forward_normal minor cs addr).cs_fwd x <> 0UL /\
               is_val_addr ((cheney_forward_normal minor cs addr).cs_fwd x) /\
               is_infix ((cheney_forward_normal minor cs addr).cs_fwd x) (cheney_forward_normal minor cs addr).cs_major = false)
    (ensures
      (let cs' = cheney_forward_normal minor cs addr in
       let t : obj_addr = cs.cs_fwd x in
       Seq.mem t (objects zero_addr cs.cs_major) /\
       is_infix t cs.cs_major = false /\
       is_blue t cs.cs_major = false /\
       Seq.mem t (objects zero_addr cs'.cs_major) /\
       is_blue t cs'.cs_major = false))
  =
  let wz = minor_wosize minor addr in
  let cs' = cheney_forward_normal minor cs addr in
  let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
  cheney_forward_normal_success minor cs addr;
  cheney_forward_normal_other_fwd minor cs addr x;
  promote_object_success minor cs.cs_major addr cs.cs_fp wz;
  assert (cs'.cs_fwd x == cs.cs_fwd x);
  assert (cs'.cs_major == res.major_out);
  assert (is_val_addr (cs.cs_fwd x));
  let t : obj_addr = cs.cs_fwd x in
  if Seq.mem t (objects zero_addr cs.cs_major) then begin
    assert (~(is_infix t cs.cs_major));
    assert (is_infix t cs.cs_major = false);
    assert (is_blue t cs.cs_major = false);
    promote_object_preserves_old_target_not_blue minor cs.cs_major addr cs.cs_fp wz t
  end else begin
    // From fwd_classified, since ~(Seq.mem t (objects ...)), we're in the infix case.
    // We derive a contradiction: promote_preserves_is_infix_frame shows
    // is_infix t cs'.cs_major, but the requires says is_infix t cs'.cs_major = false.
    assert (is_infix t cs.cs_major);
    let goal_type = (Seq.mem t (objects zero_addr cs.cs_major) /\
                     is_infix t cs.cs_major = false /\
                     is_blue t cs.cs_major = false /\
                     Seq.mem t (objects zero_addr cs'.cs_major) /\
                     is_blue t cs'.cs_major = false) in
    let proof (p: obj_addr) : Lemma
      (requires Seq.mem p (objects zero_addr cs.cs_major) /\
                is_blue p cs.cs_major = false /\
                U64.v (cs.cs_fwd x) - 8 >= U64.v p /\
                U64.v (cs.cs_fwd x) <=
                  U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8)
      (ensures goal_type)
      =
        hd_address_succ_v t;
        assert (U64.v (hd_address t) >= U64.v p);
        assert (U64.v (hd_address t) + 8 <=
          U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8);
        promote_preserves_is_infix_frame minor cs.cs_major addr cs.cs_fp wz t p;
        // This gives is_infix t res.major_out, hence is_infix t cs'.cs_major
        // But requires says is_infix t cs'.cs_major = false → contradiction
        assert (is_infix t res.major_out);
        assert (is_infix t cs'.cs_major);
        assert (False)
    in
    FStar.Classical.exists_elim goal_type #obj_addr
      #(fun p -> Seq.mem p (objects zero_addr cs.cs_major) /\
                 is_blue p cs.cs_major = false /\
                 U64.v (cs.cs_fwd x) - 8 >= U64.v p /\
                 U64.v (cs.cs_fwd x) <=
                   U64.v p + U64.v (wosize_of_object p cs.cs_major) * 8)
      ()
      (fun p -> FStar.Classical.move_requires proof p)
  end
#pop-options

#push-options "--z3rlimit 65 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_disjoint_inv
  (minor: minor_state) (major0: heap) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires disjoint_inv major0 cs /\
                    inj_inv cs /\
                    fwd_classified cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_wf minor)
          (ensures disjoint_inv major0 (cheney_forward_normal minor cs addr))
  =
  let cs' = cheney_forward_normal minor cs addr in
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then begin
    cheney_forward_normal_noop minor cs addr;
    assert (cs' == cs)
  end else
    let wz = minor_wosize minor addr in
    if wz = 0 then begin
      cheney_forward_normal_noop_wz0 minor cs addr;
      assert (cs' == cs)
    end else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then begin
        assert (Seq.mem addr (minor_objects minor));
        assert (cs.cs_fwd addr = 0UL);
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr = 0UL);
        cheney_forward_normal_noop_oom minor cs addr;
        assert (cs' == cs)
      end else begin
        assert (Seq.mem addr (minor_objects minor));
        assert (cs.cs_fwd addr = 0UL);
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr <> 0UL);
        cheney_forward_normal_success minor cs addr;
        promote_object_success minor cs.cs_major addr cs.cs_fp wz;
        let aux_old (y: obj_addr) : Lemma
          (requires Seq.mem y (objects zero_addr major0) /\
                    is_blue y major0 = false)
          (ensures Seq.mem y (objects zero_addr cs'.cs_major) /\
                   is_blue y cs'.cs_major = false)
        =
          old_nonblue_preserved_elim major0 cs y;
          Frame.cheney_forward_normal_preserves_old_nonblue_shape minor cs addr y
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_old);
        let aux_fresh (x: U64.t) (y: obj_addr) : Lemma
          (requires cs'.cs_fwd x <> 0UL /\
                    is_val_addr (cs'.cs_fwd x) /\
                    is_infix (cs'.cs_fwd x) cs'.cs_major = false /\
                    Seq.mem y (objects zero_addr major0) /\
                    is_blue y major0 = false)
          (ensures cs'.cs_fwd x <> y)
        =
          old_nonblue_preserved_elim major0 cs y;
          if x = addr then begin
            assert (cs'.cs_fwd addr == res.new_addr);
            chain_avoids_from_blue cs.cs_major cs.cs_fp y;
            AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz y;
            assert (res.new_addr <> y)
          end else begin
            cheney_forward_normal_other_fwd minor cs addr x;
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (cs.cs_fwd x <> 0UL);
            assert (is_val_addr (cs.cs_fwd x));
            cheney_forward_normal_old_target_preserved minor cs addr x;
            assert (is_infix (cs.cs_fwd x) cs.cs_major = false);
            disjoint_inv_elim major0 cs x y
          end
        in
        FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux_fresh)
      end
#pop-options

#push-options "--z3rlimit 75 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_inj_inv
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires inj_inv cs /\
                    fwd_classified cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_wf minor)
          (ensures inj_inv (cheney_forward_normal minor cs addr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    cheney_forward_normal_noop minor cs addr
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then
      cheney_forward_normal_noop_wz0 minor cs addr
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        cheney_forward_normal_noop_oom minor cs addr
      else begin
        let cs' = cheney_forward_normal minor cs addr in
        cheney_forward_normal_success minor cs addr;
        promote_object_success minor cs.cs_major addr cs.cs_fp wz;
        promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz;
        let aux_targets (x: U64.t) : Lemma
          (ensures
            (cs'.cs_fwd x <> 0UL /\
             is_val_addr (cs'.cs_fwd x) /\
             is_infix (cs'.cs_fwd x) cs'.cs_major = false ==>
             Seq.mem ((cs'.cs_fwd x) <: obj_addr) (objects zero_addr cs'.cs_major) /\
             is_blue ((cs'.cs_fwd x) <: obj_addr) cs'.cs_major = false)) =
          FStar.Classical.impl_intro_gen
            #(cs'.cs_fwd x <> 0UL /\
              is_val_addr (cs'.cs_fwd x) /\
              is_infix (cs'.cs_fwd x) cs'.cs_major = false)
            #(fun (_: squash (cs'.cs_fwd x <> 0UL /\
                              is_val_addr (cs'.cs_fwd x) /\
                              is_infix (cs'.cs_fwd x) cs'.cs_major = false)) ->
              Seq.mem ((cs'.cs_fwd x) <: obj_addr) (objects zero_addr cs'.cs_major) /\
              is_blue ((cs'.cs_fwd x) <: obj_addr) cs'.cs_major = false)
            (fun _ ->
              assert (cs'.cs_fwd x <> 0UL);
              assert (is_val_addr (cs'.cs_fwd x));
              assert (is_infix (cs'.cs_fwd x) cs'.cs_major = false);
              if x = addr then begin
                assert (cs'.cs_fwd addr == res.new_addr);
                assert (Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out));
                assert (is_blue (res.new_addr <: obj_addr) res.major_out = false)
              end else begin
                cheney_forward_normal_other_fwd minor cs addr x;
                assert (cs'.cs_fwd x == cs.cs_fwd x);
                assert (is_val_addr (cs.cs_fwd x));
                cheney_forward_normal_old_target_preserved minor cs addr x
              end)
        in
        FStar.Classical.forall_intro aux_targets;
        let aux_inj (x y: U64.t) : Lemma
          (requires cs'.cs_fwd x <> 0UL /\ cs'.cs_fwd y <> 0UL /\
                    is_val_addr (cs'.cs_fwd x) /\ is_val_addr (cs'.cs_fwd y) /\
                    is_infix (cs'.cs_fwd x) cs'.cs_major = false /\
                    is_infix (cs'.cs_fwd y) cs'.cs_major = false /\
                    cs'.cs_fwd x = cs'.cs_fwd y)
          (ensures x = y) =
          if x = addr then begin
            if y = addr then ()
            else begin
              cheney_forward_normal_other_fwd minor cs addr y;
              assert (cs'.cs_fwd y == cs.cs_fwd y);
              assert (is_val_addr (cs.cs_fwd y));
              cheney_forward_normal_old_target_preserved minor cs addr y;
              let ty : obj_addr = cs.cs_fwd y in
              chain_avoids_from_blue cs.cs_major cs.cs_fp ty;
              AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz ty;
              assert (res.new_addr <> ty);
              assert (cs'.cs_fwd addr == res.new_addr);
              assert (res.new_addr == ty)
            end
          end else if y = addr then begin
            cheney_forward_normal_other_fwd minor cs addr x;
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (is_val_addr (cs.cs_fwd x));
            cheney_forward_normal_old_target_preserved minor cs addr x;
            let tx : obj_addr = cs.cs_fwd x in
            chain_avoids_from_blue cs.cs_major cs.cs_fp tx;
            AllocProps.alloc_spec_obj_ne_excl cs.cs_major cs.cs_fp wz tx;
            assert (res.new_addr <> tx);
            assert (cs'.cs_fwd addr == res.new_addr);
            assert (res.new_addr == tx)
          end else begin
            cheney_forward_normal_other_fwd minor cs addr x;
            cheney_forward_normal_other_fwd minor cs addr y;
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (cs'.cs_fwd y == cs.cs_fwd y);
            assert (is_val_addr (cs.cs_fwd x));
            assert (is_val_addr (cs.cs_fwd y));
            cheney_forward_normal_old_target_preserved minor cs addr x;
            cheney_forward_normal_old_target_preserved minor cs addr y;
            assert (cs.cs_fwd x <> 0UL);
            assert (cs.cs_fwd y <> 0UL);
            assert (is_val_addr (cs.cs_fwd x));
            assert (is_val_addr (cs.cs_fwd y));
            assert (is_infix (cs.cs_fwd x) cs.cs_major = false);
            assert (is_infix (cs.cs_fwd y) cs.cs_major = false);
            assert (cs.cs_fwd x = cs.cs_fwd y);
            assert (x = y)
          end
        in
        FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux_inj)
      end
#pop-options

#push-options "--z3rlimit 75 --fuel 1 --ifuel 0"
private let cheney_forward_one_preserves_inj_inv
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires inj_inv cs /\
                    fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures inj_inv (cheney_forward_one minor cs addr))
  =
  if cs.cs_fwd addr <> 0UL then
    cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_inj_inv minor cs parent;
    cheney_forward_normal_preserves_fwd_classified minor cs parent;
    cheney_forward_normal_preserves_infix_fwd_ready minor cs parent;
    cheney_forward_normal_preserves_wfh_part4_local minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    assert (inj_inv cs');
    assert (fwd_normal_injective cs'.cs_fwd cs'.cs_major);
    if not (cs'.cs_fwd parent <> 0UL &&
            U64.v addr >= U64.v parent &&
            U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size) then begin
      cheney_forward_one_infix_guard_fail minor cs addr;
      assert (cheney_forward_one minor cs addr == cs')
    end else begin
      cheney_forward_one_infix_guard_pass minor cs addr;
      let delta = U64.v addr - U64.v parent in
      let sum = U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta) in
      let r = cheney_forward_one minor cs addr in
      assert (r.cs_fwd == extend_forwarding cs'.cs_fwd addr sum);
      assert (r.cs_major == cs'.cs_major);
      assert (fwd_classified cs');
      assert (infix_fwd_ready minor cs');
      assert (is_infix_in_minor minor addr);
      assert (cs'.cs_fwd parent <> 0UL);
      assert (U64.v addr >= U64.v parent);
      assert (U64.v (cs'.cs_fwd parent) >= U64.v mword);
      assert (U64.v (cs'.cs_fwd parent) < heap_size);
      assert (U64.v (cs'.cs_fwd parent) % U64.v mword == 0);
      assert (U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size);
      assert (infix_fwd_ready_pre minor cs' addr);
      infix_fwd_ready_elim minor cs' addr;
      assert (infix_fwd_ready_post minor cs' addr ());
      assert (is_infix sum cs'.cs_major);
      let aux_targets (x: U64.t) : Lemma
        (ensures
          (r.cs_fwd x <> 0UL /\
           is_val_addr (r.cs_fwd x) /\
           is_infix (r.cs_fwd x) r.cs_major = false ==>
           Seq.mem ((r.cs_fwd x) <: obj_addr) (objects zero_addr r.cs_major) /\
           is_blue ((r.cs_fwd x) <: obj_addr) r.cs_major = false)) =
        FStar.Classical.impl_intro_gen
          #(r.cs_fwd x <> 0UL /\
            is_val_addr (r.cs_fwd x) /\
            is_infix (r.cs_fwd x) r.cs_major = false)
          #(fun (_: squash (r.cs_fwd x <> 0UL /\
                            is_val_addr (r.cs_fwd x) /\
                            is_infix (r.cs_fwd x) r.cs_major = false)) ->
            Seq.mem ((r.cs_fwd x) <: obj_addr) (objects zero_addr r.cs_major) /\
            is_blue ((r.cs_fwd x) <: obj_addr) r.cs_major = false)
          (fun _ ->
            assert (r.cs_fwd x <> 0UL);
            assert (is_val_addr (r.cs_fwd x));
            assert (is_infix (r.cs_fwd x) r.cs_major = false);
            if x = addr then begin
              assert (r.cs_fwd addr == sum);
              assert (is_infix sum cs'.cs_major);
              assert (is_infix (r.cs_fwd addr) r.cs_major);
              assert (is_infix (r.cs_fwd addr) r.cs_major = false);
              assert False
            end else begin
              cheney_forward_one_infix_fwd minor cs addr x;
              assert (r.cs_fwd x == cs'.cs_fwd x)
            end)
      in
      FStar.Classical.forall_intro aux_targets;
      assert (is_val_addr sum);
      extend_infix_preserves_fwd_normal_injective cs'.cs_fwd cs'.cs_major addr sum;
      assert (fwd_normal_injective r.cs_fwd r.cs_major)
    end
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_inj_inv minor cs addr
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let infix_delta_value (minor: minor_state) (addr: U64.t)
  : Lemma (requires is_infix_in_minor minor addr /\ minor_infix_wf minor)
          (ensures U64.v addr - U64.v (infix_parent minor addr) ==
                   minor_wosize minor addr * 8)
  =
  infix_parent_value minor addr;
  let parent = infix_parent minor addr in
  let wz = minor_wosize minor addr in
  let a = U64.v addr in
  let c = wz * 8 in
  assert (U64.v parent == a - c);
  assert (a - U64.v parent == a - (a - c));
  FStar.Math.Lemmas.subtraction_is_distributive a a c;
  assert (a - (a - c) == a - a + c);
  assert (a - a == 0);
  assert (a - a + c == c)
#pop-options

#restart-solver

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_source_inv
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires source_inv minor cs /\
                    inj_inv cs /\
                    fwd_classified cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_wf minor)
          (ensures source_inv minor (cheney_forward_normal minor cs addr))
  =
  let cs' = cheney_forward_normal minor cs addr in
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then begin
    cheney_forward_normal_noop minor cs addr;
    assert (cs' == cs)
  end else
    let wz = minor_wosize minor addr in
    if wz = 0 then begin
      cheney_forward_normal_noop_wz0 minor cs addr;
      assert (cs' == cs)
    end else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then begin
        assert (Seq.mem addr (minor_objects minor));
        assert (cs.cs_fwd addr = 0UL);
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr = 0UL);
        cheney_forward_normal_noop_oom minor cs addr;
        assert (cs' == cs)
      end else begin
        assert (Seq.mem addr (minor_objects minor));
        assert (cs.cs_fwd addr = 0UL);
        assert (minor_wosize minor addr > 0);
        assert ((promote_object minor cs.cs_major addr cs.cs_fp
                  (minor_wosize minor addr)).new_addr <> 0UL);
        cheney_forward_normal_success minor cs addr;
        let aux (x: U64.t)
          : Lemma
            (requires cs'.cs_fwd x <> 0UL /\
                      is_val_addr (cs'.cs_fwd x) /\
                      is_infix (cs'.cs_fwd x) cs'.cs_major = false)
            (ensures Seq.mem x (minor_objects minor))
          =
          if x = addr then
            assert (Seq.mem addr (minor_objects minor))
          else begin
            cheney_forward_normal_other_fwd minor cs addr x;
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (cs.cs_fwd x <> 0UL);
            assert (is_val_addr (cs.cs_fwd x));
            cheney_forward_normal_old_target_preserved minor cs addr x;
            assert (is_infix (cs.cs_fwd x) cs.cs_major = false);
            source_inv_elim minor cs x
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end

private let cheney_forward_one_preserves_source_inv
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires source_inv minor cs /\
                    inj_inv cs /\
                    fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures source_inv minor (cheney_forward_one minor cs addr))
  =
  let r = cheney_forward_one minor cs addr in
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (r == cs)
  end else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_source_inv minor cs parent;
    cheney_forward_normal_preserves_inj_inv minor cs parent;
    cheney_forward_normal_preserves_fwd_classified minor cs parent;
    cheney_forward_normal_preserves_infix_fwd_ready minor cs parent;
    cheney_forward_normal_preserves_wfh_part4_local minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    if not (cs'.cs_fwd parent <> 0UL &&
            U64.v addr >= U64.v parent &&
            U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size) then begin
      cheney_forward_one_infix_guard_fail minor cs addr;
      assert (r == cs')
    end else begin
      cheney_forward_one_infix_guard_pass minor cs addr;
      let delta = U64.v addr - U64.v parent in
      let sum = U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta) in
      assert (r.cs_fwd == extend_forwarding cs'.cs_fwd addr sum);
      assert (r.cs_major == cs'.cs_major);
      let aux (x: U64.t)
        : Lemma
          (requires r.cs_fwd x <> 0UL /\
                    is_val_addr (r.cs_fwd x) /\
                    is_infix (r.cs_fwd x) r.cs_major = false)
          (ensures Seq.mem x (minor_objects minor))
        =
        if x = addr then begin
          assert (r.cs_fwd addr == sum);
          assert (is_infix_in_minor minor addr);
          assert (minor_wosize minor addr * 8 <= U64.v addr - 8);
          infix_parent_value minor addr;
          infix_delta_value minor addr;
          let wz_infix = minor_wosize minor addr in
          assert (parent == infix_parent minor addr);
          assert (U64.v parent == U64.v addr - wz_infix * 8);
          assert (U64.v addr - U64.v (infix_parent minor addr) == wz_infix * 8);
          assert (U64.v addr - U64.v parent ==
                  U64.v addr - U64.v (infix_parent minor addr));
          assert (U64.v addr - U64.v parent == wz_infix * 8);
          assert (delta == wz_infix * 8);
          assert (wz_infix > 0);
          FStar.Math.Lemmas.multiple_modulo_lemma wz_infix 8;
          assert (delta % U64.v mword == 0);
          assert (U64.v (r.cs_fwd addr) == U64.v (cs'.cs_fwd parent) + delta);
          assert (U64.v (r.cs_fwd addr) % U64.v mword == 0);
          assert (U64.v (cs'.cs_fwd parent) == U64.v (r.cs_fwd addr) - delta);
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v (r.cs_fwd addr)) delta (U64.v mword);
          assert (U64.v (cs'.cs_fwd parent) % U64.v mword == 0);
          assert (cs'.cs_fwd parent <> 0UL);
          assert (U64.v (cs'.cs_fwd parent) >= U64.v mword);
          assert (is_infix sum cs'.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major = false)
        end else begin
          cheney_forward_one_infix_fwd minor cs addr x;
          assert (r.cs_fwd x == cs'.cs_fwd x);
          source_inv_elim minor cs' x
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_source_inv minor cs addr
  end
#pop-options

#push-options "--z3rlimit 55 --fuel 1 --ifuel 0"
private let cheney_forward_one_preserves_disjoint_inv
  (minor: minor_state) (major0: heap) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires disjoint_inv major0 cs /\
                    inj_inv cs /\
                    fwd_classified cs /\
                    infix_fwd_ready minor cs /\
                    well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures disjoint_inv major0 (cheney_forward_one minor cs addr))
  =
  let r = cheney_forward_one minor cs addr in
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (r == cs)
  end else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_disjoint_inv minor major0 cs parent;
    cheney_forward_normal_preserves_inj_inv minor cs parent;
    cheney_forward_normal_preserves_fwd_classified minor cs parent;
    cheney_forward_normal_preserves_infix_fwd_ready minor cs parent;
    cheney_forward_normal_preserves_wfh_part4_local minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    if not (cs'.cs_fwd parent <> 0UL &&
            U64.v addr >= U64.v parent &&
            U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size) then begin
      cheney_forward_one_infix_guard_fail minor cs addr;
      assert (r == cs')
    end else begin
      cheney_forward_one_infix_guard_pass minor cs addr;
      let delta = U64.v addr - U64.v parent in
      let sum = U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta) in
      assert (r.cs_fwd == extend_forwarding cs'.cs_fwd addr sum);
      assert (r.cs_major == cs'.cs_major);
      assert (disjoint_inv major0 cs');
      assert (infix_fwd_ready minor cs');
      assert (is_infix_in_minor minor addr);
      assert (cs'.cs_fwd parent <> 0UL);
      assert (U64.v addr >= U64.v parent);
      assert (U64.v (cs'.cs_fwd parent) >= U64.v mword);
      assert (U64.v (cs'.cs_fwd parent) < heap_size);
      assert (U64.v (cs'.cs_fwd parent) % U64.v mword == 0);
      assert (U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size);
      assert (infix_fwd_ready_pre minor cs' addr);
      infix_fwd_ready_elim minor cs' addr;
      assert (infix_fwd_ready_post minor cs' addr ());
      assert (is_infix sum cs'.cs_major);
      let aux_old (y: obj_addr) : Lemma
        (requires Seq.mem y (objects zero_addr major0) /\
                  is_blue y major0 = false)
        (ensures Seq.mem y (objects zero_addr r.cs_major) /\
                 is_blue y r.cs_major = false)
      =
        old_nonblue_preserved_elim major0 cs' y
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_old);
      assert (old_nonblue_preserved major0 r);
      let aux_fresh (x: U64.t) (y: obj_addr) : Lemma
        (requires r.cs_fwd x <> 0UL /\
                  is_val_addr (r.cs_fwd x) /\
                  is_infix (r.cs_fwd x) r.cs_major = false /\
                  Seq.mem y (objects zero_addr major0) /\
                  is_blue y major0 = false)
        (ensures r.cs_fwd x <> y)
      =
        if x = addr then begin
          assert (r.cs_fwd addr == sum);
          assert (is_infix sum cs'.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major = false);
          assert False
        end else begin
          cheney_forward_one_infix_fwd minor cs addr x;
          assert (r.cs_fwd x == cs'.cs_fwd x);
          assert (r.cs_fwd x <> 0UL);
          assert (is_val_addr (r.cs_fwd x));
          assert (is_infix (r.cs_fwd x) r.cs_major = false);
          assert (cs'.cs_fwd x <> 0UL);
          assert (is_val_addr (cs'.cs_fwd x));
          assert (is_infix (cs'.cs_fwd x) cs'.cs_major = false);
          disjoint_inv_elim major0 cs' x y
        end
      in
      FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux_fresh);
      assert (fwd_normal_targets_disjoint_from_old_nonblue
        r.cs_fwd r.cs_major major0);
      assert (disjoint_inv major0 r)
    end
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_disjoint_inv minor major0 cs addr
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The three forwarding-map invariants, carried through the Cheney traversal
///
/// `inj_inv`, `source_inv` and `disjoint_inv` used to be pushed through
/// `cheney_forward_fields`, `cheney_forward_roots`, `cheney_scan` and
/// `cheney_promote` by twelve separate inductions -- three invariants times
/// four operations -- with identical skeletons, each re-deriving the same case
/// analysis and the same list of side conditions.  They are now four
/// inductions carrying all three invariants at once.
/// ---------------------------------------------------------------------------

unfold let cheney_invs (minor: minor_state) (major0: heap) (cs: cheney_state) : prop =
  inj_inv cs /\ source_inv minor cs /\ disjoint_inv major0 cs

unfold let cheney_side (minor: minor_state) (cs: cheney_state) : prop =
  fwd_classified cs /\
  infix_fwd_ready minor cs /\
  well_formed_heap_part4 cs.cs_major /\
  well_formed_heap_part1 cs.cs_major /\
  AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
  AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  minor_infix_wf minor /\
  minor_wf minor

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_preserves_invs
  (minor: minor_state) (major0: heap) (cs: cheney_state)
  (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma (requires cheney_invs minor major0 cs /\ cheney_side minor cs)
          (ensures cheney_invs minor major0 (cheney_forward_fields minor cs parent i wosize))
          (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_inj_inv minor cs field_val;
    cheney_forward_one_preserves_source_inv minor cs field_val;
    cheney_forward_one_preserves_disjoint_inv minor major0 cs field_val;
    cheney_forward_one_preserves_fwd_classified minor cs field_val;
    cheney_forward_one_preserves_infix_fwd_ready minor cs field_val;
    cheney_forward_one_preserves_wfh_part4_local minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_invs minor major0 cs' parent (i + 1) wosize
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_preserves_invs
  (minor: minor_state) (major0: heap) (cs: cheney_state)
  (roots: seq U64.t) (ridx: nat)
  : Lemma (requires cheney_invs minor major0 cs /\ cheney_side minor cs)
          (ensures cheney_invs minor major0 (cheney_forward_roots minor cs roots ridx))
          (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_inj_inv minor cs r;
    cheney_forward_one_preserves_source_inv minor cs r;
    cheney_forward_one_preserves_disjoint_inv minor major0 cs r;
    cheney_forward_one_preserves_fwd_classified minor cs r;
    cheney_forward_one_preserves_infix_fwd_ready minor cs r;
    cheney_forward_one_preserves_wfh_part4_local minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_invs minor major0 cs' roots (ridx + 1)
  end
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
private let rec cheney_scan_preserves_invs
  (minor: minor_state) (major0: heap) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires cheney_invs minor major0 cs /\ cheney_side minor cs)
          (ensures cheney_invs minor major0 (cheney_scan minor cs scan fuel))
          (decreases fuel)
  =
  if fuel > 0 then begin
    if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      cheney_forward_fields_preserves_invs minor major0 cs obj 0 wz;
      cheney_forward_fields_preserves_fwd_classified minor cs obj 0 wz;
      cheney_forward_fields_preserves_wfh_part4_local minor cs obj 0 wz;
      cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
      cheney_forward_fields_preserves_cob minor cs obj 0 wz;
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      let fuel' : nat = fuel - 1 in
      assert (fuel' < fuel);
      cheney_scan_preserves_invs minor major0 cs' (scan + 1) fuel'
    end
  end else
    cheney_scan_base minor cs scan fuel
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let cheney_promote_invs
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures cheney_invs minor major
                     ({ cs_major = (cheney_promote minor major fp roots).major_final;
                        cs_fp = (cheney_promote minor major fp roots).fp_final;
                        cs_fwd = (cheney_promote minor major fp roots).fwd_map;
                        cs_queue = Seq.empty }))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  assert (inj_inv cs0);
  assert (source_inv minor cs0);
  assert (disjoint_inv major cs0);
  assert (fwd_classified cs0);
  assert (infix_fwd_ready minor cs0);
  cheney_forward_roots_preserves_invs minor major cs0 roots 0;
  cheney_forward_roots_preserves_fwd_classified minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part4_local minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_invs minor major cs1 0 (cheney_fuel minor)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_normal_injective (cheney_promote minor major fp roots).fwd_map
                                         (cheney_promote minor major fp roots).major_final)
  = cheney_promote_invs minor major fp roots

let cheney_promote_fwd_targets_not_blue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_targets_not_blue (cheney_promote minor major fp roots).fwd_map
                                        (cheney_promote minor major fp roots).major_final)
  = cheney_promote_invs minor major fp roots

let cheney_promote_fwd_noninfix_sources_in_minor_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_noninfix_sources_in_minor_objects
                     minor
                      (cheney_promote minor major fp roots).fwd_map
                      (cheney_promote minor major fp roots).major_final)
  = cheney_promote_invs minor major fp roots

let cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    chain_objects_blue major fp /\
                    minor_infix_wf minor /\
                    minor_wf minor)
          (ensures fwd_normal_targets_disjoint_from_old_nonblue
                     (cheney_promote minor major fp roots).fwd_map
                     (cheney_promote minor major fp roots).major_final
                     major)
  = cheney_promote_invs minor major fp roots
#pop-options
