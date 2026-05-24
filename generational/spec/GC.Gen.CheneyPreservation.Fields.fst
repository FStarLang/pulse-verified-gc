/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyPreservation.Fields -- promoted-field correspondence
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyPreservation.Fields

open FStar.Seq
module U64 = FStar.UInt64
module Classical = FStar.Classical

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney
open GC.Lib.Header

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Frame = GC.Gen.CheneyPreservation.Frame
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module WriteBody = GC.Gen.WriteBodyLemmas

let fwd_target_field_pre (minor: minor_state) (cs: cheney_state)
                         (x: U64.t) (j: nat) (field_addr: hp_addr) : prop =
  cs.cs_fwd x <> 0UL /\
  Seq.mem x (minor_objects minor) /\
  j < minor_wosize minor x /\
  U64.v (cs.cs_fwd x) + j * 8 + 8 <= heap_size /\
  (U64.v (cs.cs_fwd x) + j * 8) % 8 == 0 /\
  U64.v field_addr == U64.v (cs.cs_fwd x) + j * 8

let fwd_target_field_match (minor: minor_state) (cs: cheney_state)
                           (x: U64.t) (j: nat) (field_addr: hp_addr) : prop =
  fwd_target_field_pre minor cs x j field_addr ==>
  U64.v (cs.cs_fwd x) >= U64.v mword /\
  U64.v (cs.cs_fwd x) < heap_size /\
  U64.v (cs.cs_fwd x) % U64.v mword == 0 /\
  (let target : obj_addr = cs.cs_fwd x in
   Seq.mem target (objects zero_addr cs.cs_major) /\
   is_blue target cs.cs_major = false /\
   j < U64.v (wosize_of_object target cs.cs_major) /\
   read_word cs.cs_major field_addr == minor_read_field minor x j)

let fwd_target_fields_match_state (minor: minor_state) (cs: cheney_state) : prop =
  forall (x: U64.t) (j: nat) (field_addr: hp_addr).
    fwd_target_field_match minor cs x j field_addr

let fwd_target_fields_match_state_elim (minor: minor_state) (cs: cheney_state)
                                       (x: U64.t) (j: nat) (field_addr: hp_addr)
  : Lemma
    (requires fwd_target_fields_match_state minor cs /\
              fwd_target_field_pre minor cs x j field_addr)
    (ensures
      U64.v (cs.cs_fwd x) >= U64.v mword /\
      U64.v (cs.cs_fwd x) < heap_size /\
      U64.v (cs.cs_fwd x) % U64.v mword == 0 /\
      (let target : obj_addr = cs.cs_fwd x in
       Seq.mem target (objects zero_addr cs.cs_major) /\
       is_blue target cs.cs_major = false /\
       j < U64.v (wosize_of_object target cs.cs_major) /\
       read_word cs.cs_major field_addr == minor_read_field minor x j))
  =
  assert (fwd_target_field_match minor cs x j field_addr)

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let fwd_target_fields_match_initial (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma
    (ensures fwd_target_fields_match_state minor
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty })
  =
  let cs0 =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  let aux (x: U64.t) (j: nat) (field_addr: hp_addr)
    : Lemma (requires fwd_target_field_pre minor cs0 x j field_addr)
            (ensures
              U64.v (cs0.cs_fwd x) >= U64.v mword /\
              U64.v (cs0.cs_fwd x) < heap_size /\
              U64.v (cs0.cs_fwd x) % U64.v mword == 0 /\
              (let target : obj_addr = cs0.cs_fwd x in
               Seq.mem target (objects zero_addr cs0.cs_major) /\
               is_blue target cs0.cs_major = false /\
               j < U64.v (wosize_of_object target cs0.cs_major) /\
               read_word cs0.cs_major field_addr == minor_read_field minor x j))
    =
    assert (cs0.cs_fwd x == 0UL);
    assert (False)
  in
  Classical.forall_intro_3
    #(U64.t)
    #(fun _ -> nat)
    #(fun _ _ -> hp_addr)
    #(fun x j field_addr -> fwd_target_field_match minor cs0 x j field_addr)
    (Classical.move_requires_3
      #(U64.t) #(fun _ -> nat) #(fun _ _ -> hp_addr)
      #(fun x j field_addr -> fwd_target_field_pre minor cs0 x j field_addr)
      #(fun x j field_addr ->
          U64.v (cs0.cs_fwd x) >= U64.v mword /\
          U64.v (cs0.cs_fwd x) < heap_size /\
          U64.v (cs0.cs_fwd x) % U64.v mword == 0 /\
          (let target : obj_addr = cs0.cs_fwd x in
           Seq.mem target (objects zero_addr cs0.cs_major) /\
           is_blue target cs0.cs_major = false /\
           j < U64.v (wosize_of_object target cs0.cs_major) /\
           read_word cs0.cs_major field_addr == minor_read_field minor x j))
      aux)
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_normal_preserves_fwd_target_fields_match_state
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_fields_match_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_fields_match_state minor
        (cheney_forward_normal minor cs addr))
  =
  let cs' = cheney_forward_normal minor cs addr in
  let aux (x: U64.t) (j: nat) (field_addr: hp_addr)
    : Lemma
        (requires fwd_target_field_pre minor cs' x j field_addr)
        (ensures
          U64.v (cs'.cs_fwd x) >= U64.v mword /\
          U64.v (cs'.cs_fwd x) < heap_size /\
          U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
          (let target : obj_addr = cs'.cs_fwd x in
           Seq.mem target (objects zero_addr cs'.cs_major) /\
           is_blue target cs'.cs_major = false /\
           j < U64.v (wosize_of_object target cs'.cs_major) /\
           read_word cs'.cs_major field_addr == minor_read_field minor x j))
    =
    if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then begin
      cheney_forward_normal_noop minor cs addr;
      fwd_target_fields_match_state_elim minor cs x j field_addr
    end
    else
      let wz = minor_wosize minor addr in
      if wz = 0 then begin
        cheney_forward_normal_noop_wz0 minor cs addr;
        fwd_target_fields_match_state_elim minor cs x j field_addr
      end
      else
        let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
        if res.new_addr = 0UL then begin
          assert (Seq.mem addr (minor_objects minor));
          assert (cs.cs_fwd addr = 0UL);
          assert (wz > 0);
          assert (res.new_addr = 0UL);
          cheney_forward_normal_noop_oom minor cs addr;
          fwd_target_fields_match_state_elim minor cs x j field_addr
        end
        else begin
          cheney_forward_normal_success minor cs addr;
          if x = addr then begin
            assert (cs'.cs_fwd x == res.new_addr);
            assert (wz == minor_wosize minor x);
            minor_objects_valid minor x;
            promote_preserves_fields minor cs.cs_major addr cs.cs_fp wz;
            promote_object_preserves_alloc_invariants minor cs.cs_major addr cs.cs_fp wz;
            Forwarding.promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz;
            let target : obj_addr = res.new_addr in
            Forwarding.promote_object_new_addr_wosize_ge minor cs.cs_major addr cs.cs_fp wz target;
            wfh_part1_obj_bound res.major_out target;
            assert (U64.v target + wz * 8 <= heap_size);
            dst_fields_valid_from_bounds target wz;
            assert (j < wz);
            let expected_addr : hp_addr = U64.uint_to_t (U64.v target + j * 8) in
            assert (field_addr == expected_addr);
            assert (read_word res.major_out (U64.uint_to_t (U64.v target + j * 8)) ==
                    minor_read_field minor x j);
            assert (read_word res.major_out field_addr == minor_read_field minor x j)
          end
          else begin
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (fwd_target_field_pre minor cs x j field_addr);
            fwd_target_fields_match_state_elim minor cs x j field_addr;
            let target : obj_addr = cs.cs_fwd x in
            Frame.cheney_forward_normal_preserves_old_nonblue_shape minor cs addr target;
            Frame.cheney_forward_normal_frame_field minor cs addr target j;
            let expected_addr : hp_addr = U64.uint_to_t (U64.v target + j * 8) in
            assert (field_addr == expected_addr);
            assert (read_word cs'.cs_major field_addr ==
                    read_word cs.cs_major field_addr);
            assert (read_word cs.cs_major field_addr == minor_read_field minor x j)
          end
        end
  in
  Classical.forall_intro_3
    #(U64.t)
    #(fun _ -> nat)
    #(fun _ _ -> hp_addr)
    #(fun x j field_addr -> fwd_target_field_match minor cs' x j field_addr)
    (Classical.move_requires_3
      #(U64.t) #(fun _ -> nat) #(fun _ _ -> hp_addr)
      #(fun x j field_addr -> fwd_target_field_pre minor cs' x j field_addr)
      #(fun x j field_addr ->
          U64.v (cs'.cs_fwd x) >= U64.v mword /\
          U64.v (cs'.cs_fwd x) < heap_size /\
          U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
          (let target : obj_addr = cs'.cs_fwd x in
           Seq.mem target (objects zero_addr cs'.cs_major) /\
           is_blue target cs'.cs_major = false /\
           j < U64.v (wosize_of_object target cs'.cs_major) /\
           read_word cs'.cs_major field_addr == minor_read_field minor x j))
      aux)
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_one_preserves_fwd_target_fields_match_state
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_fields_match_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_fields_match_state minor
        (cheney_forward_one minor cs addr))
  =
  let cs' = cheney_forward_one minor cs addr in
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (cs' == cs)
  end
  else if is_infix_in_minor minor addr then begin
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_fwd_target_fields_match_state minor cs parent;
    let csn = cheney_forward_normal minor cs parent in
    let aux (x: U64.t) (j: nat) (field_addr: hp_addr)
      : Lemma
          (requires fwd_target_field_pre minor cs' x j field_addr)
          (ensures
            U64.v (cs'.cs_fwd x) >= U64.v mword /\
            U64.v (cs'.cs_fwd x) < heap_size /\
            U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
            (let target : obj_addr = cs'.cs_fwd x in
             Seq.mem target (objects zero_addr cs'.cs_major) /\
             is_blue target cs'.cs_major = false /\
             j < U64.v (wosize_of_object target cs'.cs_major) /\
             read_word cs'.cs_major field_addr == minor_read_field minor x j))
      =
      if x = addr then begin
        minor_objects_not_infix minor x;
        assert (False)
      end
      else begin
        assert (cs'.cs_major == csn.cs_major);
        cheney_forward_one_infix_fwd minor cs addr x;
        assert (cs'.cs_fwd x == csn.cs_fwd x);
        assert (fwd_target_field_pre minor csn x j field_addr);
        fwd_target_fields_match_state_elim minor csn x j field_addr
      end
    in
    Classical.forall_intro_3
      #(U64.t)
      #(fun _ -> nat)
      #(fun _ _ -> hp_addr)
      #(fun x j field_addr -> fwd_target_field_match minor cs' x j field_addr)
      (Classical.move_requires_3
        #(U64.t) #(fun _ -> nat) #(fun _ _ -> hp_addr)
        #(fun x j field_addr -> fwd_target_field_pre minor cs' x j field_addr)
        #(fun x j field_addr ->
            U64.v (cs'.cs_fwd x) >= U64.v mword /\
            U64.v (cs'.cs_fwd x) < heap_size /\
            U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
            (let target : obj_addr = cs'.cs_fwd x in
             Seq.mem target (objects zero_addr cs'.cs_major) /\
             is_blue target cs'.cs_major = false /\
             j < U64.v (wosize_of_object target cs'.cs_major) /\
             read_word cs'.cs_major field_addr == minor_read_field minor x j))
        aux)
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_fwd_target_fields_match_state minor cs addr
  end
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0 --split_queries always"
let rec cheney_forward_fields_preserves_fwd_target_fields_match_state
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma
      (requires
        fwd_target_fields_match_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_fields_match_state minor
        (cheney_forward_fields minor cs parent i wosize))
      (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_fwd_target_fields_match_state minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    Forwarding.cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_fwd_target_fields_match_state minor cs' parent (i + 1) wosize
  end
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0 --split_queries always"
let rec cheney_forward_roots_preserves_fwd_target_fields_match_state
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
      (requires
        fwd_target_fields_match_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_fields_match_state minor
        (cheney_forward_roots minor cs roots ridx))
      (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_fwd_target_fields_match_state minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    Forwarding.cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_fwd_target_fields_match_state minor cs' roots (ridx + 1)
  end
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let rec cheney_scan_preserves_fwd_target_fields_match_state
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma
      (requires
        fwd_target_fields_match_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_fields_match_state minor
        (cheney_scan minor cs scan fuel))
      (decreases fuel)
  =
  if fuel > 0 then begin
    assert (fuel > 0);
    if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      cheney_forward_fields_preserves_fwd_target_fields_match_state minor cs obj 0 wz;
      cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
      Forwarding.cheney_forward_fields_preserves_cob minor cs obj 0 wz;
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      assert (fuel - 1 < fuel);
      cheney_scan_preserves_fwd_target_fields_match_state minor cs' (scan + 1) (fuel - 1)
    end
  end else begin
    assert (fuel = 0);
    cheney_scan_base minor cs scan fuel
  end
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --split_queries always"
let cheney_promote_fwd_target_fields_match
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t) (j: nat)
  : Lemma
    (requires well_formed_heap major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              chain_objects_blue major fp /\
              minor_wf minor /\
              minor_infix_wf minor /\
              (let prom = cheney_promote minor major fp roots in
               prom.fwd_map x <> 0UL /\
               Seq.mem x (minor_objects minor) /\
               is_val_addr (prom.fwd_map x) /\
               is_infix (prom.fwd_map x) prom.major_final = false /\
               j < minor_wosize minor x /\
               U64.v (prom.fwd_map x) + j * 8 + 8 <= heap_size /\
               (U64.v (prom.fwd_map x) + j * 8) % 8 == 0))
    (ensures
      (let prom = cheney_promote minor major fp roots in
       read_word prom.major_final
         (U64.uint_to_t (U64.v (prom.fwd_map x) + j * 8))
       == minor_read_field minor x j))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  fwd_target_fields_match_initial minor major fp;
  cheney_forward_roots_preserves_fwd_target_fields_match_state minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_fwd_target_fields_match_state minor cs1 0 (cheney_fuel minor);
  let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
  assert ((cheney_promote minor major fp roots).fwd_map == cs2.cs_fwd);
  assert ((cheney_promote minor major fp roots).major_final == cs2.cs_major);
  let field_addr : hp_addr =
    U64.uint_to_t (U64.v ((cheney_promote minor major fp roots).fwd_map x) + j * 8) in
  assert (fwd_target_field_pre minor cs2 x j field_addr);
  fwd_target_fields_match_state_elim minor cs2 x j field_addr
#pop-options

let fwd_target_not_no_scan_pre (minor: minor_state) (cs: cheney_state)
                               (x: U64.t) : prop =
  cs.cs_fwd x <> 0UL /\
  Seq.mem x (minor_objects minor) /\
  minor_tag minor x < 251

let fwd_target_not_no_scan_match (minor: minor_state) (cs: cheney_state)
                                 (x: U64.t) : prop =
  fwd_target_not_no_scan_pre minor cs x ==>
  is_val_addr (cs.cs_fwd x) /\
  (let target : obj_addr = cs.cs_fwd x in
   Seq.mem target (objects zero_addr cs.cs_major) /\
   is_blue target cs.cs_major = false /\
   is_no_scan target cs.cs_major = false /\
   U64.v (wosize_of_object target cs.cs_major) >= minor_wosize minor x)

let fwd_target_not_no_scan_state (minor: minor_state) (cs: cheney_state) : prop =
  forall (x: U64.t). fwd_target_not_no_scan_match minor cs x

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let fwd_target_not_no_scan_state_elim
  (minor: minor_state) (cs: cheney_state) (x: U64.t)
  : Lemma
    (requires fwd_target_not_no_scan_state minor cs /\
              fwd_target_not_no_scan_pre minor cs x)
    (ensures
      is_val_addr (cs.cs_fwd x) /\
       (let target : obj_addr = cs.cs_fwd x in
        Seq.mem target (objects zero_addr cs.cs_major) /\
        is_blue target cs.cs_major = false /\
        is_no_scan target cs.cs_major = false /\
        U64.v (wosize_of_object target cs.cs_major) >= minor_wosize minor x))
  = assert (fwd_target_not_no_scan_match minor cs x)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let fwd_target_not_no_scan_initial (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma
    (ensures fwd_target_not_no_scan_state minor
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty })
  =
  let cs0 =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  let aux (x: U64.t) : Lemma
    (requires fwd_target_not_no_scan_pre minor cs0 x)
    (ensures
      is_val_addr (cs0.cs_fwd x) /\
      (let target : obj_addr = cs0.cs_fwd x in
       Seq.mem target (objects zero_addr cs0.cs_major) /\
       is_blue target cs0.cs_major = false /\
       is_no_scan target cs0.cs_major = false /\
       U64.v (wosize_of_object target cs0.cs_major) >= minor_wosize minor x))
  =
    assert (cs0.cs_fwd x == 0UL);
    assert False
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_normal_preserves_fwd_target_not_no_scan_state
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_not_no_scan_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_not_no_scan_state minor
        (cheney_forward_normal minor cs addr))
  =
  let cs' = cheney_forward_normal minor cs addr in
  let aux (x: U64.t) : Lemma
    (requires fwd_target_not_no_scan_pre minor cs' x)
    (ensures
      is_val_addr (cs'.cs_fwd x) /\
      (let target : obj_addr = cs'.cs_fwd x in
       Seq.mem target (objects zero_addr cs'.cs_major) /\
       is_blue target cs'.cs_major = false /\
       is_no_scan target cs'.cs_major = false /\
       U64.v (wosize_of_object target cs'.cs_major) >= minor_wosize minor x))
  =
    if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then begin
      cheney_forward_normal_noop minor cs addr;
      fwd_target_not_no_scan_state_elim minor cs x
    end
    else
      if minor_wosize minor addr = 0 then begin
        cheney_forward_normal_noop_wz0 minor cs addr;
        fwd_target_not_no_scan_state_elim minor cs x
      end
      else begin
        let wz = minor_wosize minor addr in
        assert (not (wz = 0));
        assert (wz > 0);
        let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
        if res.new_addr = 0UL then begin
          assert (Seq.mem addr (minor_objects minor));
          assert (cs.cs_fwd addr = 0UL);
          assert (wz > 0);
          cheney_forward_normal_noop_oom minor cs addr;
          fwd_target_not_no_scan_state_elim minor cs x
        end
        else begin
          cheney_forward_normal_success minor cs addr;
          promote_object_success minor cs.cs_major addr cs.cs_fp wz;
          if x = addr then begin
            assert (cs'.cs_fwd x == res.new_addr);
            assert (wz == minor_wosize minor x);
            Forwarding.promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz;
            let target : obj_addr = res.new_addr in
            Forwarding.promote_object_new_addr_wosize_ge minor cs.cs_major addr cs.cs_fp wz target;
            let alloc_res = GC.Spec.Allocator.alloc_spec cs.cs_major cs.cs_fp wz in
            let copied = WriteBody.copy_fields minor alloc_res.heap_out addr alloc_res.obj_out 0 wz in
            let padded = zero_promote_padding copied alloc_res.obj_out wz in
            let tag = minor_tag minor addr in
            minor_tag_bound minor addr;
            assert (tag < 256);
            assert (tag < pow2 64);
            let tag_u = U64.uint_to_t tag in
            assert (U64.v tag_u == tag);
            assert (tag < 251);
            set_promoted_tag_unfold padded target tag;
            let hdr = hd_address target in
            let new_hdr = makeHeader (getWosize (read_word padded hdr)) White tag_u in
            assert (res.major_out == set_promoted_tag padded target tag);
            read_write_same padded hdr new_hdr;
            tag_of_object_spec target res.major_out;
            makeHeader_getTag (getWosize (read_word padded hdr)) White tag_u;
            assert (tag_of_object target res.major_out == tag_u);
            no_scan_tag_val ();
            assert (U64.v (tag_of_object target res.major_out) < 251);
            assert_norm (251 < pow2 64);
            assert (no_scan_tag == U64.uint_to_t 251);
            assert (U64.v (U64.uint_to_t 251) == 251);
            assert (U64.v no_scan_tag == 251);
            assert (U64.v (tag_of_object target res.major_out) < U64.v no_scan_tag);
            assert (U64.gte (tag_of_object target res.major_out) no_scan_tag = false);
            is_no_scan_spec target res.major_out;
            assert (is_no_scan target res.major_out = false);
            assert (U64.v (wosize_of_object target res.major_out) >= minor_wosize minor x)
          end
          else begin
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (fwd_target_not_no_scan_pre minor cs x);
            fwd_target_not_no_scan_state_elim minor cs x;
            let target : obj_addr = cs.cs_fwd x in
            assert (U64.v (wosize_of_object target cs.cs_major) >= minor_wosize minor x);
            Frame.cheney_forward_normal_preserves_old_nonblue_shape minor cs addr target;
            assert (is_no_scan target cs'.cs_major == is_no_scan target cs.cs_major);
            assert (is_no_scan target cs'.cs_major = false);
            assert (wosize_of_object target cs'.cs_major == wosize_of_object target cs.cs_major);
            assert (U64.v (wosize_of_object target cs'.cs_major) >= minor_wosize minor x)
          end
        end
      end
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_one_preserves_fwd_target_not_no_scan_state
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_not_no_scan_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor /\
        Forwarding.fwd_classified cs /\
        Forwarding.infix_fwd_ready minor cs)
      (ensures fwd_target_not_no_scan_state minor
        (cheney_forward_one minor cs addr))
  =
  let r = cheney_forward_one minor cs addr in
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (r == cs)
  end else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_fwd_target_not_no_scan_state minor cs parent;
    Forwarding.cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    Forwarding.cheney_forward_normal_preserves_cob minor cs parent;
    Forwarding.cheney_forward_normal_preserves_fwd_classified minor cs parent;
    Forwarding.cheney_forward_normal_preserves_infix_fwd_ready minor cs parent;
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
      assert (is_infix_in_minor minor addr);
      assert (Forwarding.infix_fwd_ready_pre minor cs' addr);
      Forwarding.infix_fwd_ready_elim minor cs' addr;
      assert (Forwarding.infix_fwd_ready_post minor cs' addr ());
      assert (is_infix sum cs'.cs_major);
      let aux (x: U64.t) : Lemma
        (requires fwd_target_not_no_scan_pre minor r x)
        (ensures
          is_val_addr (r.cs_fwd x) /\
          (let target : obj_addr = r.cs_fwd x in
           Seq.mem target (objects zero_addr r.cs_major) /\
           is_blue target r.cs_major = false /\
           is_no_scan target r.cs_major = false /\
           U64.v (wosize_of_object target r.cs_major) >= minor_wosize minor x))
      =
        if x = addr then begin
          assert (r.cs_fwd addr == sum);
          minor_objects_not_infix minor addr;
          assert (Seq.mem addr (minor_objects minor));
          assert False;
          assert (is_infix sum cs'.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major);
          assert (is_infix (r.cs_fwd addr) r.cs_major = false);
          assert False
        end else begin
          cheney_forward_one_infix_fwd minor cs addr x;
          assert (r.cs_fwd x == cs'.cs_fwd x);
          assert (fwd_target_not_no_scan_pre minor cs' x);
          fwd_target_not_no_scan_state_elim minor cs' x
        end
      in
      Classical.forall_intro (Classical.move_requires aux)
    end
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_fwd_target_not_no_scan_state minor cs addr
  end
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
let rec cheney_forward_fields_preserves_fwd_target_not_no_scan_state
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma
      (requires
        fwd_target_not_no_scan_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor /\
        Forwarding.fwd_classified cs /\
        Forwarding.infix_fwd_ready minor cs)
      (ensures fwd_target_not_no_scan_state minor
        (cheney_forward_fields minor cs parent i wosize))
      (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_fwd_target_not_no_scan_state minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    Forwarding.cheney_forward_one_preserves_cob minor cs field_val;
    Forwarding.cheney_forward_one_preserves_fwd_classified minor cs field_val;
    Forwarding.cheney_forward_one_preserves_infix_fwd_ready minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_fwd_target_not_no_scan_state minor cs' parent (i + 1) wosize
  end

let rec cheney_forward_roots_preserves_fwd_target_not_no_scan_state
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
      (requires
        fwd_target_not_no_scan_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor /\
        Forwarding.fwd_classified cs /\
        Forwarding.infix_fwd_ready minor cs)
      (ensures fwd_target_not_no_scan_state minor
        (cheney_forward_roots minor cs roots ridx))
      (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_fwd_target_not_no_scan_state minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    Forwarding.cheney_forward_one_preserves_cob minor cs r;
    Forwarding.cheney_forward_one_preserves_fwd_classified minor cs r;
    Forwarding.cheney_forward_one_preserves_infix_fwd_ready minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_fwd_target_not_no_scan_state minor cs' roots (ridx + 1)
  end

let rec cheney_forward_roots_preserves_infix_ready_local
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
      (requires
        Forwarding.fwd_classified cs /\
        Forwarding.infix_fwd_ready minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures Forwarding.infix_fwd_ready minor
        (cheney_forward_roots minor cs roots ridx))
      (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    Forwarding.cheney_forward_one_preserves_infix_fwd_ready minor cs r;
    Forwarding.cheney_forward_one_preserves_fwd_classified minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    Forwarding.cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_infix_ready_local minor cs' roots (ridx + 1)
  end

let rec cheney_scan_preserves_fwd_target_not_no_scan_state
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma
      (requires
        fwd_target_not_no_scan_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor /\
        Forwarding.fwd_classified cs /\
        Forwarding.infix_fwd_ready minor cs)
      (ensures fwd_target_not_no_scan_state minor
        (cheney_scan minor cs scan fuel))
      (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if scan >= Seq.length cs.cs_queue then
    cheney_scan_base minor cs scan fuel
  else begin
    cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    cheney_forward_fields_preserves_fwd_target_not_no_scan_state minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    Forwarding.cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    Forwarding.cheney_forward_fields_preserves_fwd_classified minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    assert (fuel - 1 < fuel);
    cheney_scan_preserves_fwd_target_not_no_scan_state minor cs' (scan + 1) (fuel - 1)
  end
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let cheney_promote_fwd_target_not_no_scan_of_minor_tag_lt
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t)
  : Lemma
    (requires well_formed_heap major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              chain_objects_blue major fp /\
              minor_wf minor /\
              minor_infix_wf minor /\
              (let prom = cheney_promote minor major fp roots in
               prom.fwd_map x <> 0UL /\
               Seq.mem x (minor_objects minor) /\
               is_val_addr (prom.fwd_map x) /\
               is_infix (prom.fwd_map x) prom.major_final = false /\
               minor_tag minor x < 251))
    (ensures
      (let prom = cheney_promote minor major fp roots in
       let target : obj_addr = prom.fwd_map x in
       Seq.mem target (objects zero_addr prom.major_final) /\
       is_blue target prom.major_final = false /\
       is_no_scan target prom.major_final = false /\
       U64.v (wosize_of_object target prom.major_final) >= minor_wosize minor x))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  fwd_target_not_no_scan_initial minor major fp;
  assert (Forwarding.fwd_classified cs0);
  assert (Forwarding.infix_fwd_ready minor cs0);
  cheney_forward_roots_preserves_fwd_target_not_no_scan_state minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_cob minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_fwd_classified minor cs0 roots 0;
  cheney_forward_roots_preserves_infix_ready_local minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_fwd_target_not_no_scan_state minor cs1 0 (cheney_fuel minor);
  let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
  assert ((cheney_promote minor major fp roots).fwd_map == cs2.cs_fwd);
  assert ((cheney_promote minor major fp roots).major_final == cs2.cs_major);
  assert (fwd_target_not_no_scan_pre minor cs2 x);
  fwd_target_not_no_scan_state_elim minor cs2 x
#pop-options

let fwd_target_extra_field_pre (minor: minor_state) (cs: cheney_state)
                               (x: U64.t) (j: nat) (field_addr: hp_addr) : prop =
  cs.cs_fwd x <> 0UL /\
  Seq.mem x (minor_objects minor) /\
  j >= minor_wosize minor x /\
  U64.v (cs.cs_fwd x) >= U64.v mword /\
  U64.v (cs.cs_fwd x) < heap_size /\
  U64.v (cs.cs_fwd x) % U64.v mword == 0 /\
  U64.v field_addr == U64.v (cs.cs_fwd x) + j * 8

let fwd_target_extra_field_not_pointer
    (minor: minor_state) (cs: cheney_state)
    (x: U64.t) (j: nat) (field_addr: hp_addr) : prop =
  fwd_target_extra_field_pre minor cs x j field_addr ==>
  U64.v (cs.cs_fwd x) >= U64.v mword /\
  U64.v (cs.cs_fwd x) < heap_size /\
  U64.v (cs.cs_fwd x) % U64.v mword == 0 /\
  (let target : obj_addr = cs.cs_fwd x in
    Seq.mem target (objects zero_addr cs.cs_major) /\
    is_blue target cs.cs_major = false /\
    (j < U64.v (wosize_of_object target cs.cs_major) /\
     U64.v (cs.cs_fwd x) + j * 8 + 8 <= heap_size /\
     (U64.v (cs.cs_fwd x) + j * 8) % 8 == 0 ==>
     read_word cs.cs_major field_addr == 0UL /\
     ~(is_pointer_field (read_word cs.cs_major field_addr))))

let fwd_target_extra_fields_state (minor: minor_state) (cs: cheney_state) : prop =
  forall (x: U64.t) (j: nat) (field_addr: hp_addr).
    fwd_target_extra_field_not_pointer minor cs x j field_addr

let fwd_target_extra_fields_state_elim
    (minor: minor_state) (cs: cheney_state)
    (x: U64.t) (j: nat) (field_addr: hp_addr)
  : Lemma
    (requires fwd_target_extra_fields_state minor cs /\
              fwd_target_extra_field_pre minor cs x j field_addr)
    (ensures
      U64.v (cs.cs_fwd x) >= U64.v mword /\
      U64.v (cs.cs_fwd x) < heap_size /\
      U64.v (cs.cs_fwd x) % U64.v mword == 0 /\
      (let target : obj_addr = cs.cs_fwd x in
       Seq.mem target (objects zero_addr cs.cs_major) /\
       is_blue target cs.cs_major = false /\
        (j < U64.v (wosize_of_object target cs.cs_major) /\
         U64.v (cs.cs_fwd x) + j * 8 + 8 <= heap_size /\
         (U64.v (cs.cs_fwd x) + j * 8) % 8 == 0 ==>
         read_word cs.cs_major field_addr == 0UL /\
         ~(is_pointer_field (read_word cs.cs_major field_addr)))))
  =
  assert (fwd_target_extra_field_not_pointer minor cs x j field_addr)

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let fwd_target_extra_fields_initial (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma
    (ensures fwd_target_extra_fields_state minor
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty })
  =
  let cs0 =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  let aux (x: U64.t) (j: nat) (field_addr: hp_addr)
    : Lemma (requires fwd_target_extra_field_pre minor cs0 x j field_addr)
            (ensures
              U64.v (cs0.cs_fwd x) >= U64.v mword /\
              U64.v (cs0.cs_fwd x) < heap_size /\
              U64.v (cs0.cs_fwd x) % U64.v mword == 0 /\
              (let target : obj_addr = cs0.cs_fwd x in
               Seq.mem target (objects zero_addr cs0.cs_major) /\
               is_blue target cs0.cs_major = false /\
               (j < U64.v (wosize_of_object target cs0.cs_major) /\
                 U64.v (cs0.cs_fwd x) + j * 8 + 8 <= heap_size /\
                 (U64.v (cs0.cs_fwd x) + j * 8) % 8 == 0 ==>
                 read_word cs0.cs_major field_addr == 0UL /\
                 ~(is_pointer_field (read_word cs0.cs_major field_addr)))))
    =
    assert (cs0.cs_fwd x == 0UL);
    assert False
  in
  Classical.forall_intro_3
    #(U64.t)
    #(fun _ -> nat)
    #(fun _ _ -> hp_addr)
    #(fun x j field_addr -> fwd_target_extra_field_not_pointer minor cs0 x j field_addr)
    (Classical.move_requires_3
      #(U64.t) #(fun _ -> nat) #(fun _ _ -> hp_addr)
      #(fun x j field_addr -> fwd_target_extra_field_pre minor cs0 x j field_addr)
      #(fun x j field_addr ->
          U64.v (cs0.cs_fwd x) >= U64.v mword /\
          U64.v (cs0.cs_fwd x) < heap_size /\
          U64.v (cs0.cs_fwd x) % U64.v mword == 0 /\
          (let target : obj_addr = cs0.cs_fwd x in
           Seq.mem target (objects zero_addr cs0.cs_major) /\
           is_blue target cs0.cs_major = false /\
            (j < U64.v (wosize_of_object target cs0.cs_major) /\
             U64.v (cs0.cs_fwd x) + j * 8 + 8 <= heap_size /\
             (U64.v (cs0.cs_fwd x) + j * 8) % 8 == 0 ==>
             read_word cs0.cs_major field_addr == 0UL /\
             ~(is_pointer_field (read_word cs0.cs_major field_addr)))))
      aux)
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_normal_preserves_fwd_target_extra_fields_state
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_extra_fields_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_extra_fields_state minor
        (cheney_forward_normal minor cs addr))
  =
  let cs' = cheney_forward_normal minor cs addr in
  let aux (x: U64.t) (j: nat) (field_addr: hp_addr)
    : Lemma
        (requires fwd_target_extra_field_pre minor cs' x j field_addr)
        (ensures
          U64.v (cs'.cs_fwd x) >= U64.v mword /\
          U64.v (cs'.cs_fwd x) < heap_size /\
          U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
          (let target : obj_addr = cs'.cs_fwd x in
           Seq.mem target (objects zero_addr cs'.cs_major) /\
           is_blue target cs'.cs_major = false /\
              (j < U64.v (wosize_of_object target cs'.cs_major) /\
               U64.v (cs'.cs_fwd x) + j * 8 + 8 <= heap_size /\
               (U64.v (cs'.cs_fwd x) + j * 8) % 8 == 0 ==>
               read_word cs'.cs_major field_addr == 0UL /\
               ~(is_pointer_field (read_word cs'.cs_major field_addr)))))
    =
    if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then begin
      cheney_forward_normal_noop minor cs addr;
      fwd_target_extra_fields_state_elim minor cs x j field_addr
    end
    else
      let wz = minor_wosize minor addr in
      if wz = 0 then begin
        cheney_forward_normal_noop_wz0 minor cs addr;
        fwd_target_extra_fields_state_elim minor cs x j field_addr
      end
      else
        let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
        if res.new_addr = 0UL then begin
          assert (Seq.mem addr (minor_objects minor));
          assert (cs.cs_fwd addr = 0UL);
          assert (wz > 0);
          assert (res.new_addr = 0UL);
          cheney_forward_normal_noop_oom minor cs addr;
          fwd_target_extra_fields_state_elim minor cs x j field_addr
        end
        else begin
          cheney_forward_normal_success minor cs addr;
          if x = addr then begin
            assert (cs'.cs_fwd x == res.new_addr);
            assert (wz == minor_wosize minor x);
            minor_objects_valid minor x;
            promote_object_preserves_alloc_invariants minor cs.cs_major addr cs.cs_fp wz;
            Forwarding.promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz;
            let target : obj_addr = res.new_addr in
            if j < U64.v (wosize_of_object target res.major_out) then
              if U64.v target + j * 8 + 8 <= heap_size then
                if (U64.v target + j * 8) % 8 = 0 then begin
                  assert (j >= wz);
                  assert (U64.v target + j * 8 < heap_size);
                   promote_object_extra_field_not_pointer minor cs.cs_major addr cs.cs_fp wz j;
                   assert (field_addr == U64.uint_to_t (U64.v target + j * 8));
                   assert (read_word res.major_out field_addr == 0UL);
                   assert (~(is_pointer_field (read_word res.major_out field_addr)))
                end
          end
          else begin
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (fwd_target_extra_field_pre minor cs x j field_addr);
            fwd_target_extra_fields_state_elim minor cs x j field_addr;
            let target : obj_addr = cs.cs_fwd x in
            Frame.cheney_forward_normal_preserves_old_nonblue_shape minor cs addr target;
            if j < U64.v (wosize_of_object target cs'.cs_major) then
              if U64.v target + j * 8 + 8 <= heap_size then
                if (U64.v target + j * 8) % 8 = 0 then begin
                  assert (j < U64.v (wosize_of_object target cs.cs_major));
                  Frame.cheney_forward_normal_frame_field minor cs addr target j;
                  assert (read_word cs'.cs_major field_addr ==
                          read_word cs.cs_major field_addr);
                  assert (read_word cs.cs_major field_addr == 0UL);
                  assert (~(is_pointer_field (read_word cs.cs_major field_addr)));
                  assert (read_word cs'.cs_major field_addr == 0UL);
                  assert (~(is_pointer_field (read_word cs'.cs_major field_addr)))
                end
          end
        end
  in
  Classical.forall_intro_3
    #(U64.t)
    #(fun _ -> nat)
    #(fun _ _ -> hp_addr)
    #(fun x j field_addr -> fwd_target_extra_field_not_pointer minor cs' x j field_addr)
    (Classical.move_requires_3
      #(U64.t) #(fun _ -> nat) #(fun _ _ -> hp_addr)
      #(fun x j field_addr -> fwd_target_extra_field_pre minor cs' x j field_addr)
      #(fun x j field_addr ->
          U64.v (cs'.cs_fwd x) >= U64.v mword /\
          U64.v (cs'.cs_fwd x) < heap_size /\
          U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
          (let target : obj_addr = cs'.cs_fwd x in
           Seq.mem target (objects zero_addr cs'.cs_major) /\
           is_blue target cs'.cs_major = false /\
            (j < U64.v (wosize_of_object target cs'.cs_major) /\
             U64.v (cs'.cs_fwd x) + j * 8 + 8 <= heap_size /\
             (U64.v (cs'.cs_fwd x) + j * 8) % 8 == 0 ==>
             read_word cs'.cs_major field_addr == 0UL /\
             ~(is_pointer_field (read_word cs'.cs_major field_addr)))))
      aux)
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let cheney_forward_one_preserves_fwd_target_extra_fields_state
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_extra_fields_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_extra_fields_state minor
        (cheney_forward_one minor cs addr))
  =
  let cs' = cheney_forward_one minor cs addr in
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (cs' == cs)
  end
  else if is_infix_in_minor minor addr then begin
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_fwd_target_extra_fields_state minor cs parent;
    let csn = cheney_forward_normal minor cs parent in
    let aux (x: U64.t) (j: nat) (field_addr: hp_addr)
      : Lemma
          (requires fwd_target_extra_field_pre minor cs' x j field_addr)
          (ensures
            U64.v (cs'.cs_fwd x) >= U64.v mword /\
            U64.v (cs'.cs_fwd x) < heap_size /\
            U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
            (let target : obj_addr = cs'.cs_fwd x in
             Seq.mem target (objects zero_addr cs'.cs_major) /\
             is_blue target cs'.cs_major = false /\
              (j < U64.v (wosize_of_object target cs'.cs_major) /\
               U64.v (cs'.cs_fwd x) + j * 8 + 8 <= heap_size /\
               (U64.v (cs'.cs_fwd x) + j * 8) % 8 == 0 ==>
               read_word cs'.cs_major field_addr == 0UL /\
               ~(is_pointer_field (read_word cs'.cs_major field_addr)))))
      =
      if x = addr then begin
        minor_objects_not_infix minor x;
        assert False
      end
      else begin
        assert (cs'.cs_major == csn.cs_major);
        cheney_forward_one_infix_fwd minor cs addr x;
        assert (cs'.cs_fwd x == csn.cs_fwd x);
        assert (fwd_target_extra_field_pre minor csn x j field_addr);
        fwd_target_extra_fields_state_elim minor csn x j field_addr
      end
    in
    Classical.forall_intro_3
      #(U64.t)
      #(fun _ -> nat)
      #(fun _ _ -> hp_addr)
      #(fun x j field_addr -> fwd_target_extra_field_not_pointer minor cs' x j field_addr)
      (Classical.move_requires_3
        #(U64.t) #(fun _ -> nat) #(fun _ _ -> hp_addr)
        #(fun x j field_addr -> fwd_target_extra_field_pre minor cs' x j field_addr)
        #(fun x j field_addr ->
            U64.v (cs'.cs_fwd x) >= U64.v mword /\
            U64.v (cs'.cs_fwd x) < heap_size /\
            U64.v (cs'.cs_fwd x) % U64.v mword == 0 /\
            (let target : obj_addr = cs'.cs_fwd x in
             Seq.mem target (objects zero_addr cs'.cs_major) /\
             is_blue target cs'.cs_major = false /\
              (j < U64.v (wosize_of_object target cs'.cs_major) /\
               U64.v (cs'.cs_fwd x) + j * 8 + 8 <= heap_size /\
               (U64.v (cs'.cs_fwd x) + j * 8) % 8 == 0 ==>
               read_word cs'.cs_major field_addr == 0UL /\
               ~(is_pointer_field (read_word cs'.cs_major field_addr)))))
        aux)
  end
  else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_fwd_target_extra_fields_state minor cs addr
  end
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0 --split_queries always"
let rec cheney_forward_fields_preserves_fwd_target_extra_fields_state
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (i: nat) (wosize: nat)
  : Lemma
      (requires
        fwd_target_extra_fields_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_extra_fields_state minor
        (cheney_forward_fields minor cs parent i wosize))
      (decreases (if i < wosize then wosize - i else 0))
  =
  if i >= wosize then
    cheney_forward_fields_base minor cs parent i wosize
  else begin
    cheney_forward_fields_step minor cs parent i wosize;
    let field_val = to_minor_offset (minor_read_field minor parent i) in
    cheney_forward_one_preserves_fwd_target_extra_fields_state minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    Forwarding.cheney_forward_one_preserves_cob minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_fwd_target_extra_fields_state minor cs' parent (i + 1) wosize
  end
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0 --split_queries always"
let rec cheney_forward_roots_preserves_fwd_target_extra_fields_state
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (ridx: nat)
  : Lemma
      (requires
        fwd_target_extra_fields_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_extra_fields_state minor
        (cheney_forward_roots minor cs roots ridx))
      (decreases (if ridx < Seq.length roots then Seq.length roots - ridx else 0))
  =
  if ridx >= Seq.length roots then
    cheney_forward_roots_base minor cs roots ridx
  else begin
    cheney_forward_roots_step minor cs roots ridx;
    let r = Seq.index roots ridx in
    cheney_forward_one_preserves_fwd_target_extra_fields_state minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    Forwarding.cheney_forward_one_preserves_cob minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_fwd_target_extra_fields_state minor cs' roots (ridx + 1)
  end
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0 --split_queries always"
let rec cheney_scan_preserves_fwd_target_extra_fields_state
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma
      (requires
        fwd_target_extra_fields_state minor cs /\
        well_formed_heap_part1 cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_extra_fields_state minor
        (cheney_scan minor cs scan fuel))
      (decreases fuel)
  =
  if fuel = 0 then
    cheney_scan_base minor cs scan fuel
  else if fuel > 0 then
    if scan >= Seq.length cs.cs_queue then
      cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      cheney_forward_fields_preserves_fwd_target_extra_fields_state minor cs obj 0 wz;
      cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
      Forwarding.cheney_forward_fields_preserves_cob minor cs obj 0 wz;
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      assert (fuel - 1 < fuel);
      cheney_scan_preserves_fwd_target_extra_fields_state minor cs' (scan + 1) (fuel - 1)
    end
  else
    assert False
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --split_queries always"
let cheney_promote_fwd_target_extra_field_not_pointer
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t) (j: nat)
  : Lemma
    (requires well_formed_heap major /\
              AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
              chain_objects_blue major fp /\
              minor_wf minor /\
              minor_infix_wf minor /\
              (let prom = cheney_promote minor major fp roots in
               prom.fwd_map x <> 0UL /\
               Seq.mem x (minor_objects minor) /\
               is_val_addr (prom.fwd_map x) /\
               is_infix (prom.fwd_map x) prom.major_final = false /\
               j >= minor_wosize minor x /\
               j < U64.v (wosize_of_object (prom.fwd_map x <: obj_addr)
                                             prom.major_final) /\
               U64.v (prom.fwd_map x) + j * 8 + 8 <= heap_size /\
               (U64.v (prom.fwd_map x) + j * 8) % 8 == 0))
     (ensures
       (let prom = cheney_promote minor major fp roots in
       let field = read_word prom.major_final
          (U64.uint_to_t (U64.v (prom.fwd_map x) + j * 8)) in
       field == 0UL /\ ~(is_pointer_field field)))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  fwd_target_extra_fields_initial minor major fp;
  cheney_forward_roots_preserves_fwd_target_extra_fields_state minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  Forwarding.cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_fwd_target_extra_fields_state minor cs1 0 (cheney_fuel minor);
  let cs2 = cheney_scan minor cs1 0 (cheney_fuel minor) in
  assert ((cheney_promote minor major fp roots).fwd_map == cs2.cs_fwd);
  assert ((cheney_promote minor major fp roots).major_final == cs2.cs_major);
  let field_addr : hp_addr =
    U64.uint_to_t (U64.v ((cheney_promote minor major fp roots).fwd_map x) + j * 8) in
  assert (fwd_target_extra_field_pre minor cs2 x j field_addr);
  fwd_target_extra_fields_state_elim minor cs2 x j field_addr;
  let target : obj_addr = (cheney_promote minor major fp roots).fwd_map x in
  assert (j < U64.v (wosize_of_object target cs2.cs_major));
  assert (U64.v (cs2.cs_fwd x) + j * 8 + 8 <= heap_size);
  assert ((U64.v (cs2.cs_fwd x) + j * 8) % 8 == 0);
  assert (read_word cs2.cs_major field_addr == 0UL);
  assert (~(is_pointer_field (read_word cs2.cs_major field_addr)))
#pop-options
