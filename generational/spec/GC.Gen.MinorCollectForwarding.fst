/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectForwarding

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered
open GC.Gen.Reachability
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant

let rec remembered_slot_targets_from
  (major: heap) (slots: seq U64.t) (n idx: nat)
  : GTot (seq U64.t) (decreases (n - idx)) =
  if idx >= n || idx >= Seq.length slots then Seq.empty
  else
    let slot = Seq.index slots idx in
    let rest = remembered_slot_targets_from major slots n (idx + 1) in
    if U64.v slot < heap_size && U64.v slot % U64.v mword == 0 then
      let v = to_minor_offset (read_word major (slot <: hp_addr)) in
      if is_minor_pointer v then Seq.cons v rest else rest
    else rest

let combined_reachable_minor_has_fwd
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      well_formed_heap major /\
      minor_wf minor /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures (
      let cg = CG.build_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      let fwd = (cheney_promote minor major fp roots).fwd_map in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) /\
        minor_wosize minor v > 0 ==> fwd v <> 0UL))
  = let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    RBridge.combined_minor_reachable_in_minor_reachable minor major roots;
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    let aux (v: U64.t) : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MinorV v) /\
                minor_wosize minor v > 0)
      (ensures (cheney_promote minor major fp roots).fwd_map v <> 0UL)
    = ()
    in
    Classical.forall_intro (Classical.move_requires aux)

let combined_reachable_images_valid_or_infix
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures combined_reachable_images_valid_or_infix_prop minor major fp roots)
  = let cg = CG.build_combined_graph minor major in
    let combined_roots = CG.classify_roots roots in
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let fwd = prom.fwd_map in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    RBridge.reachable_major_valid minor major roots;
    CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
    combined_reachable_minor_has_fwd minor major fp roots;
    CheneyPres.cheney_promote_fwd_valid_or_infix minor major fp roots;
    let major_aux (v: U64.t) : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MajorV v))
      (ensures
        U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (objects zero_addr res.mc_major))
    = ()
    in
    let minor_aux (v: U64.t) : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MinorV v) /\
                minor_wosize minor v > 0)
      (ensures
        fwd v <> 0UL /\
        U64.v (fwd v) >= U64.v mword /\
        U64.v (fwd v) < heap_size /\
        U64.v (fwd v) % U64.v mword == 0 /\
        (Seq.mem ((fwd v) <: obj_addr) (objects zero_addr prom.major_final) \/
         is_infix (fwd v) prom.major_final))
    = ()
    in
    Classical.forall_intro (Classical.move_requires major_aux);
    Classical.forall_intro (Classical.move_requires minor_aux)

let minor_collect_full_forwarding_kernel_intro
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat) (ok: bool)
  : Lemma
    (requires GenInv.collection_heap_shape minor major fp)
    (ensures (
      let res = cheney_collect_spec minor major fp roots in
      minor_collect_full_forwarding_kernel minor major fp roots slots n ok
        res.mc_major (rewrite_roots roots (cheney_promote minor major fp roots).fwd_map)))
  =
  reveal_opaque (`%minor_collect_full_forwarding_kernel)
    (minor_collect_full_forwarding_kernel minor major fp roots slots n ok
      (cheney_collect_spec minor major fp roots).mc_major
      (rewrite_roots roots (cheney_promote minor major fp roots).fwd_map));
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  assert (well_formed_heap major);
  assert (chain_objects_blue major fp);
  assert (minor_wf minor);
  assert (minor_infix_wf minor);
  CheneyCorr.cheney_collect_preserves_objects minor major fp roots;
  CheneyCorr.cheney_collect_rewrites_roots minor major fp roots;
  if remembered_targets_in_roots major roots slots n /\
     ok /\
     CheneyBFS.cheney_no_oom minor major fp roots
  then begin
    CheneyCorr.cheney_promotes_all_reachable minor major fp roots;
    CheneyPres.cheney_promote_fwd_valid_or_infix minor major fp roots;
    CheneyPres.cheney_promote_fwd_normal_injective minor major fp roots;
    CheneyPres.cheney_promote_fwd_targets_not_blue minor major fp roots;
    if RBridge.major_field_zero_no_minor minor major /\
       RBridge.remembered_roots_in_roots major roots
    then
      combined_reachable_images_valid_or_infix minor major fp roots
  end
