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
open GC.Gen.Cheney.Induction
open GC.Gen.Cheney.Steps
open GC.Lib.Header

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Frame = GC.Gen.CheneyPreservation.Frame
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module WriteBody = GC.Gen.WriteBodyLemmas

/// Build a `U64.t` from a nat known to be below `heap_size`.  The
/// `FStar.UInt.size` side condition of `U64.uint_to_t` is a goal Z3 4.15.3 does
/// not finish inside the Cheney preservation proofs.
private let mk_u64_lt_heap (a: nat)
  : Pure U64.t (requires a < heap_size)
               (ensures fun r -> U64.v r == a /\ r == U64.uint_to_t a)
  = U64.uint_to_t a

/// An infix sub-object never sits below its parent: `infix_parent_value`
/// (`parent == addr - wz * 8`), proved here so the enclosing preservation
/// proofs, which carry the entire Cheney invariant, do not have to rediscover it.
private let infix_addr_ge_parent (minor: minor_state) (addr: U64.t)
  : Lemma (requires is_infix_in_minor minor addr /\ minor_infix_wf minor)
          (ensures U64.v addr >= U64.v (infix_parent minor addr))
  = infix_parent_value minor addr


/// `n < 256 ==> n < pow2 64`.  Proved in an empty context: the `pow2`
/// comparison diverges under the enclosing Cheney-state hypotheses.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let lt1_eq0 (n: nat) : Lemma (requires n < 1) (ensures n = 0) = ()
#pop-options

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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let fwd_target_fields_match_initial (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma
    (ensures fwd_target_fields_match_state minor
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty; cs_phase = ph })
  =
  let cs0 =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty; cs_phase = ph } in
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

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let cheney_forward_normal_preserves_fwd_target_fields_match_state
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_fields_match_state minor cs /\
        blocks_fit cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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
        let res = promote_object minor cs.cs_major addr cs.cs_fp wz cs.cs_phase in
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
            promote_preserves_fields minor cs.cs_major addr cs.cs_fp wz cs.cs_phase;
            promote_object_preserves_alloc_invariants minor cs.cs_major addr cs.cs_fp wz cs.cs_phase;
            Forwarding.promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz cs.cs_phase;
            let target : obj_addr = res.new_addr in
            Forwarding.promote_object_new_addr_wosize_eq minor cs.cs_major addr cs.cs_fp wz cs.cs_phase target;
            wfh_part1_obj_bound res.major_out target;
            dst_fields_valid_from_obj res.major_out target wz;
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

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let cheney_forward_one_preserves_fwd_target_fields_match_state
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_fields_match_state minor cs /\
        blocks_fit cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
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

private let match_inv (minor: minor_state) (cs: cheney_state) : prop =
  fwd_target_fields_match_state minor cs /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  minor_wf minor /\
  minor_infix_wf minor

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
private let match_one (minor: minor_state) : one_keeps minor (match_inv minor) =
  fun cs addr ->
    cheney_forward_one_preserves_fwd_target_fields_match_state minor cs addr;
    cheney_forward_one_preserves_cob minor cs addr
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_promote_fwd_target_fields_match (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t) (j: nat)
  =
  fwd_target_fields_match_initial ph minor major fp;
  cheney_promote_induction minor (match_inv minor) (match_one minor) ph major fp roots;
  let cs2 = cheney_run ph minor major fp roots in
  assert ((cheney_promote ph minor major fp roots).fwd_map == cs2.cs_fwd);
  assert ((cheney_promote ph minor major fp roots).major_final == cs2.cs_major);
  let field_addr : hp_addr =
    U64.uint_to_t (U64.v ((cheney_promote ph minor major fp roots).fwd_map x) + j * 8) in
  assert (fwd_target_field_pre minor cs2 x j field_addr);
  fwd_target_fields_match_state_elim minor cs2 x j field_addr
#pop-options

/// Every forwarded minor object has a well-formed, non-blue image in the major
/// heap whose *scannability matches the source tag*.  The equation rather than
/// a one-sided `= false` is what lets `GC.Gen.MinorCollectForwarding.Reflection`
/// conclude `minor_tag minor x < 251` from an edge out of the image: promotion
/// copies the tag verbatim (`GC.Gen.Promote.promote_object` allocates the copy
/// with `promoted_tag minor obj`), so the two agree exactly.
let fwd_target_not_no_scan_pre (minor: minor_state) (cs: cheney_state)
                               (x: U64.t) : prop =
  cs.cs_fwd x <> 0UL /\
  Seq.mem x (minor_objects minor)

let fwd_target_not_no_scan_match (free: free_def) (minor: minor_state) (cs: cheney_state)
                                 (x: U64.t) : prop =
  fwd_target_not_no_scan_pre minor cs x ==>
  is_val_addr (cs.cs_fwd x) /\
  (let target : obj_addr = cs.cs_fwd x in
   Seq.mem target (objects zero_addr cs.cs_major) /\
   is_blue target cs.cs_major = false /\
   is_no_scan target cs.cs_major = (minor_tag minor x >= 251) /\
   U64.v (wosize_of_object target cs.cs_major) == minor_wosize minor x /\
       not (free cs.cs_major target))

let fwd_target_not_no_scan_state (free: free_def) (minor: minor_state) (cs: cheney_state) : prop =
  forall (x: U64.t). fwd_target_not_no_scan_match free minor cs x

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let fwd_target_not_no_scan_state_elim
  (free: free_def) (minor: minor_state) (cs: cheney_state) (x: U64.t)
  : Lemma
    (requires fwd_target_not_no_scan_state free minor cs /\
              fwd_target_not_no_scan_pre minor cs x)
    (ensures
      is_val_addr (cs.cs_fwd x) /\
       (let target : obj_addr = cs.cs_fwd x in
        Seq.mem target (objects zero_addr cs.cs_major) /\
        is_blue target cs.cs_major = false /\
        is_no_scan target cs.cs_major = (minor_tag minor x >= 251) /\
        U64.v (wosize_of_object target cs.cs_major) == minor_wosize minor x /\
       not (free cs.cs_major target)))
  = assert (fwd_target_not_no_scan_match free minor cs x)
#pop-options

/// Z3 4.15.3 helper: extending a forwarding map at an *infix* minor address
/// preserves [fwd_target_not_no_scan_state].  The new binding is vacuous
/// because [fwd_target_not_no_scan_pre] requires membership in
/// [minor_objects], which excludes infix addresses.  Stated over abstract
/// states so the proof runs in an empty hypothesis context.
private
let fwd_state_extend_infix
  (free: free_def) (minor: minor_state) (cs' r: cheney_state) (addr sum: U64.t)
  : Lemma
      (requires
        fwd_target_not_no_scan_state free minor cs' /\
        minor_wf minor /\
        is_infix_in_minor minor addr /\
        r.cs_major == cs'.cs_major /\
        r.cs_fwd == extend_forwarding cs'.cs_fwd addr sum)
      (ensures fwd_target_not_no_scan_state free minor r)
  =
  let aux (x: U64.t) : Lemma
    (requires fwd_target_not_no_scan_pre minor r x)
    (ensures
      is_val_addr (r.cs_fwd x) /\
      (let target : obj_addr = r.cs_fwd x in
       Seq.mem target (objects zero_addr r.cs_major) /\
       is_blue target r.cs_major = false /\
       is_no_scan target r.cs_major = (minor_tag minor x >= 251) /\
       U64.v (wosize_of_object target r.cs_major) == minor_wosize minor x /\
       not (free r.cs_major target)))
    = if x = addr then begin
        minor_objects_not_infix minor addr;
        assert False
      end else begin
        assert (r.cs_fwd x == cs'.cs_fwd x);
        fwd_target_not_no_scan_state_elim free minor cs' x
      end
  in
  Classical.forall_intro (Classical.move_requires aux)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let fwd_target_not_no_scan_initial (ph: gc_phase) (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t)
  : Lemma
    (ensures fwd_target_not_no_scan_state free minor
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty; cs_phase = ph })
  =
  let cs0 =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty; cs_phase = ph } in
  let aux (x: U64.t) : Lemma
    (requires fwd_target_not_no_scan_pre minor cs0 x)
    (ensures
      is_val_addr (cs0.cs_fwd x) /\
      (let target : obj_addr = cs0.cs_fwd x in
       Seq.mem target (objects zero_addr cs0.cs_major) /\
       is_blue target cs0.cs_major = false /\
       is_no_scan target cs0.cs_major = (minor_tag minor x >= 251) /\
       U64.v (wosize_of_object target cs0.cs_major) == minor_wosize minor x /\
       not (free cs0.cs_major target)))
  =
    assert (cs0.cs_fwd x == 0UL);
    assert False
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let cheney_forward_normal_preserves_fwd_target_not_no_scan_state (ph: gc_phase)
  (free: free_def) (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_not_no_scan_state free minor cs /\
        cs.cs_phase == ph /\
        free_def_ok free /\ allocations_not_free ph free /\
        blocks_fit cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor)
      (ensures fwd_target_not_no_scan_state free minor
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
       is_no_scan target cs'.cs_major = (minor_tag minor x >= 251) /\
       U64.v (wosize_of_object target cs'.cs_major) == minor_wosize minor x /\
       not (free cs'.cs_major target)))
  =
    if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then begin
      cheney_forward_normal_noop minor cs addr;
      fwd_target_not_no_scan_state_elim free minor cs x
    end
    else
      if minor_wosize minor addr < 1 then begin
        lt1_eq0 (minor_wosize minor addr);
        cheney_forward_normal_noop_wz0 minor cs addr;
        fwd_target_not_no_scan_state_elim free minor cs x
      end
      else begin
        let wz = minor_wosize minor addr in
        assert (not (wz = 0));
        assert (wz > 0);
        let res = promote_object minor cs.cs_major addr cs.cs_fp wz cs.cs_phase in
        if res.new_addr = 0UL then begin
          assert (Seq.mem addr (minor_objects minor));
          assert (cs.cs_fwd addr = 0UL);
          assert (wz > 0);
          cheney_forward_normal_noop_oom minor cs addr;
          fwd_target_not_no_scan_state_elim free minor cs x
        end
        else begin
          cheney_forward_normal_success minor cs addr;
          promote_object_success minor cs.cs_major addr cs.cs_fp wz cs.cs_phase;
          if x = addr then begin
            assert (cs'.cs_fwd x == res.new_addr);
            assert (wz == minor_wosize minor x);
            Forwarding.promote_object_new_addr_in_objects_not_blue minor cs.cs_major addr cs.cs_fp wz cs.cs_phase;
            let target : obj_addr = res.new_addr in
            Forwarding.promote_object_new_addr_wosize_eq minor cs.cs_major addr cs.cs_fp wz cs.cs_phase target;
            Forwarding.promote_object_new_addr_tag minor cs.cs_major addr cs.cs_fp wz cs.cs_phase;
            Forwarding.promote_object_new_addr_not_free free minor cs.cs_major addr cs.cs_fp wz cs.cs_phase;
            let tag = minor_tag minor addr in
            no_scan_tag_val ();
            assert_norm (251 < pow2 64);
            assert (no_scan_tag == U64.uint_to_t 251);
            assert (U64.v (U64.uint_to_t 251) == 251);
            assert (U64.v no_scan_tag == 251);
            assert (U64.v (tag_of_object target res.major_out) == tag);
            // The promoted header carries the source tag verbatim, so the image
            // is no-scan exactly when the nursery object was.
            assert (U64.gte (tag_of_object target res.major_out) no_scan_tag
                      = (tag >= 251));
            is_no_scan_spec target res.major_out;
            assert (is_no_scan target res.major_out = (minor_tag minor x >= 251));
            assert (U64.v (wosize_of_object target res.major_out) == minor_wosize minor x)
          end
          else begin
            assert (cs'.cs_fwd x == cs.cs_fwd x);
            assert (fwd_target_not_no_scan_pre minor cs x);
            fwd_target_not_no_scan_state_elim free minor cs x;
            let target : obj_addr = cs.cs_fwd x in
            assert (U64.v (wosize_of_object target cs.cs_major) == minor_wosize minor x);
            Frame.cheney_forward_normal_preserves_old_nonblue_shape minor cs addr target;
            in_use_is_determined_from_header free cs.cs_major cs'.cs_major target;
            assert (is_no_scan target cs'.cs_major == is_no_scan target cs.cs_major);
            assert (is_no_scan target cs'.cs_major = (minor_tag minor x >= 251));
            assert (wosize_of_object target cs'.cs_major == wosize_of_object target cs.cs_major);
            assert (U64.v (wosize_of_object target cs'.cs_major) == minor_wosize minor x)
          end
        end
      end
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let cheney_forward_one_preserves_fwd_target_not_no_scan_state (ph: gc_phase)
  (free: free_def) (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires
        fwd_target_not_no_scan_state free minor cs /\
        cs.cs_phase == ph /\
        free_def_ok free /\ allocations_not_free ph free /\
        blocks_fit cs.cs_major /\
        AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
        AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
        chain_objects_blue cs.cs_major cs.cs_fp /\
        minor_wf minor /\
        minor_infix_wf minor /\
        Forwarding.fwd_classified cs /\
        Forwarding.infix_fwd_ready minor cs)
      (ensures fwd_target_not_no_scan_state free minor
        (cheney_forward_one minor cs addr))
  =
  let r = cheney_forward_one minor cs addr in
  if cs.cs_fwd addr <> 0UL then begin
    cheney_forward_one_noop minor cs addr;
    assert (r == cs);
    assert (fwd_target_not_no_scan_state free minor r)
  end else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    infix_addr_ge_parent minor addr;
    cheney_forward_one_infix minor cs addr;
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_fwd_target_not_no_scan_state ph free minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent;
    Forwarding.cheney_forward_normal_preserves_fwd_classified minor cs parent;
    Forwarding.cheney_forward_normal_preserves_infix_fwd_ready minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    if not (cs'.cs_fwd parent <> 0UL &&
            U64.v addr >= U64.v parent &&
            U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size) then begin
      cheney_forward_one_infix_guard_fail minor cs addr;
      assert (r == cs');
      assert (fwd_target_not_no_scan_state free minor r)
    end else begin
      cheney_forward_one_infix_guard_pass minor cs addr;
      let delta = U64.v addr - U64.v parent in
      let sum = mk_u64_lt_heap (U64.v (cs'.cs_fwd parent) + delta) in
      assert (r.cs_fwd == extend_forwarding cs'.cs_fwd addr sum);
      assert (r.cs_major == cs'.cs_major);
      assert (is_infix_in_minor minor addr);
      fwd_state_extend_infix free minor cs' r addr sum;
      assert (fwd_target_not_no_scan_state free minor r)
    end
  end else begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_preserves_fwd_target_not_no_scan_state ph free minor cs addr;
    assert (fwd_target_not_no_scan_state free minor r)
  end
#pop-options

private let image_inv (ph: gc_phase) (free: free_def) (minor: minor_state) (cs: cheney_state) : prop =
  fwd_target_not_no_scan_state free minor cs /\
  cs.cs_phase == ph /\
  free_def_ok free /\ allocations_not_free ph free /\
  chain_objects_blue cs.cs_major cs.cs_fp /\
  minor_wf minor /\
  minor_infix_wf minor /\
  Forwarding.fwd_classified cs /\
  Forwarding.infix_fwd_ready minor cs

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
private let image_one (ph: gc_phase) (free: free_def) (minor: minor_state) : one_keeps minor (image_inv ph free minor) =
  fun cs addr ->
    cheney_forward_one_preserves_fwd_target_not_no_scan_state ph free minor cs addr;
    cheney_forward_one_preserves_cob minor cs addr;
    Forwarding.cheney_forward_one_preserves_fwd_classified minor cs addr;
    Forwarding.cheney_forward_one_preserves_infix_fwd_ready minor cs addr
#pop-options

/// The image facts at the end of the run, for one definition of free.
#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"
private let cheney_promote_fwd_target_facts (ph: gc_phase)
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t)
  : Lemma
    (requires blocks_fit major /\ no_infix_block major /\
              AllocLemmas.fl_valid major fp heap_words /\
              AllocLemmas.fl_chain_terminates major fp heap_words /\
              chain_objects_blue major fp /\
              minor_wf minor /\
              minor_infix_wf minor /\
              free_def_ok free /\ allocations_not_free ph free /\
              (let prom = cheney_promote ph minor major fp roots in
               prom.fwd_map x <> 0UL /\
               Seq.mem x (minor_objects minor)))
    (ensures
      (let prom = cheney_promote ph minor major fp roots in
       let cs2 : cheney_state =
         { cs_major = prom.major_final; cs_fp = prom.fp_final;
           cs_fwd = prom.fwd_map; cs_queue = Seq.empty; cs_phase = ph } in
       fwd_target_not_no_scan_match free minor cs2 x))
  =
  fwd_target_not_no_scan_initial ph free minor major fp;
  assert (Forwarding.fwd_classified (cheney_init ph major fp));
  assert (Forwarding.infix_fwd_ready minor (cheney_init ph major fp));
  cheney_promote_induction minor (image_inv ph free minor) (image_one ph free minor) ph major fp roots;
  let cs2 = cheney_run ph minor major fp roots in
  assert ((cheney_promote ph minor major fp roots).fwd_map == cs2.cs_fwd);
  assert ((cheney_promote ph minor major fp roots).major_final == cs2.cs_major);
  assert (fwd_target_not_no_scan_pre minor cs2 x);
  fwd_target_not_no_scan_state_elim free minor cs2 x
#pop-options

let cheney_promote_fwd_target_no_scan_iff_minor_tag (ph: gc_phase)
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t)
  =
  free_stw_ok ();
  free_stw_allocations_not_free ph;
  cheney_promote_fwd_target_facts ph free_stw minor major fp roots x

let cheney_promote_fwd_target_not_free (ph: gc_phase)
  (free: free_def) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t)
  =
  cheney_promote_fwd_target_facts ph free minor major fp roots x
