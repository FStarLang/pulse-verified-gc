/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyLive -- Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyLive

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module PU = GC.Gen.PromoteUpdate
module Aux = GC.Gen.PromoteUpdate.Aux
module Frame = GC.Gen.CheneyPreservation.Frame
module Fwd = GC.Gen.CheneyPreservation.Forwarding
module Inj = GC.Gen.CheneyPreservation.Injectivity
module NBO = GC.Gen.CheneyPreservation.NonBlueOrigin

let update_live_pointers_preserves_live_ok major live upd fwd =
  PU.update_live_pointers_preserves_objects major upd fwd;
  let aux (x: obj_addr) : Lemma
    (requires live x)
    (ensures Seq.mem x (objects zero_addr (update_live_pointers major upd fwd)) /\
             ~(is_blue x (update_live_pointers major upd fwd)))
  = PU.update_live_pointers_preserves_header major upd fwd x;
    Aux.header_eq_object_facts (update_live_pointers major upd fwd) major x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// An old non-free block stays a non-free block through promotion.
private let old_nonblue_kept
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: obj_addr)
  : Lemma (requires promote_pre minor major fp /\
                    Seq.mem x (objects zero_addr major) /\ ~(is_blue x major))
          (ensures (let prom = cheney_promote minor major fp roots in
                    Seq.mem x (objects zero_addr prom.major_final) /\
                    ~(is_blue x prom.major_final)))
  = cheney_promote_preserves_objects minor major fp roots;
    Frame.cheney_promote_frame_old_header minor major fp roots x;
    Aux.header_eq_object_facts (cheney_promote minor major fp roots).major_final major x

/// The image of a promoted nursery object is a non-free block of the promoted heap.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let image_nonblue
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (v: U64.t) (x: obj_addr)
  : Lemma (requires promote_pre minor major fp /\
                    Seq.mem v (minor_objects minor) /\
                    (cheney_promote minor major fp roots).fwd_map v == x)
          (ensures (let prom = cheney_promote minor major fp roots in
                    Seq.mem x (objects zero_addr prom.major_final) /\
                    ~(is_blue x prom.major_final)))
  = let prom = cheney_promote minor major fp roots in
    minor_objects_not_infix minor v;
    Fwd.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
    assert (Seq.mem x (objects zero_addr prom.major_final));
    cheney_promote_preserves_wfh_part4 minor major fp roots;
    assert (~(is_infix x prom.major_final));
    Inj.cheney_promote_fwd_targets_not_blue minor major fp roots
#pop-options

let cheney_promote_live_ok minor major fp roots live =
  let prom = cheney_promote minor major fp roots in
  let aux (x: obj_addr) : Lemma
    (requires promoted_live minor live prom.fwd_map x)
    (ensures Seq.mem x (objects zero_addr prom.major_final) /\ ~(is_blue x prom.major_final))
  = if FStar.IndefiniteDescription.strong_excluded_middle (live x)
    then old_nonblue_kept minor major fp roots x
    else begin
      let v = FStar.IndefiniteDescription.indefinite_description_ghost U64.t
        (fun v -> Seq.mem v (minor_objects minor) /\ prom.fwd_map v == x) in
      image_nonblue minor major fp roots v x
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let promoted_live_idle minor major fp roots x =
  let prom = cheney_promote minor major fp roots in
  // (=>)
  cheney_promote_live_ok minor major fp roots (idle_live major);
  // (<=)
  if is_blue x prom.major_final then ()
  else if Seq.mem x (objects zero_addr major) && not (is_blue x major) then ()
  else begin
    NBO.cheney_promote_nonblue_origin minor major fp roots x;
    cheney_promote_preserves_wfh_part4 minor major fp roots;
    assert (~(is_infix x prom.major_final));
    Inj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots
  end
#pop-options

let cheney_collect_spec_over_idle minor major fp roots =
  let prom = cheney_promote minor major fp roots in
  let live' = promoted_live minor (idle_live major) prom.fwd_map in
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (promoted_live_idle minor major fp roots));
  PU.update_live_pointers_ext prom.major_final live' (idle_live prom.major_final) prom.fwd_map;
  PU.update_live_pointers_idle prom.major_final prom.fwd_map
