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
module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
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

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let rec remembered_slot_targets_from_mem
  (major: heap) (slots: seq U64.t) (n idx: nat) (i: nat)
  : Lemma
    (requires idx <= i /\ i < n /\ i < Seq.length slots /\
              U64.v (Seq.index slots i) < heap_size /\
              U64.v (Seq.index slots i) % U64.v mword == 0 /\
              (let slot = Seq.index slots i in
               is_minor_pointer (to_minor_offset (read_word major (slot <: hp_addr)))))
    (ensures
      (let slot = Seq.index slots i in
       Seq.mem (to_minor_offset (read_word major (slot <: hp_addr)))
         (remembered_slot_targets_from major slots n idx)))
    (decreases (n - idx)) =
  if idx >= n || idx >= Seq.length slots then ()
  else begin
    let slot = Seq.index slots idx in
    let rest = remembered_slot_targets_from major slots n (idx + 1) in
    if idx = i then begin
      assert (U64.v slot < heap_size);
      assert (U64.v slot % U64.v mword == 0);
      let v = to_minor_offset (read_word major (slot <: hp_addr)) in
      assert (is_minor_pointer v);
      Seq.mem_cons v rest
    end else begin
      remembered_slot_targets_from_mem major slots n (idx + 1) i;
      if U64.v slot < heap_size && U64.v slot % U64.v mword == 0 then begin
        let v0 = to_minor_offset (read_word major (slot <: hp_addr)) in
        if is_minor_pointer v0 then Seq.mem_cons v0 rest else ()
      end else ()
    end
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
let remembered_roots_in_roots_from_slots
  (major: heap) (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n)
    (ensures RBridge.remembered_roots_in_roots major roots)
  =
    let aux (r: U64.t) : Lemma
      (requires Seq.mem r (minor_roots_from_major major))
      (ensures Seq.mem r roots)
    =
      minor_roots_from_major_sound major r;
      let obj = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
        (fun obj -> exists (field_idx: nat).
          Seq.mem obj (objects zero_addr major) /\
          is_blue obj major = false /\
          is_no_scan obj major = false /\
          field_idx >= 1 /\
          field_idx < U64.v (wosize_of_object obj major) /\
          U64.v obj + field_idx * 8 + 8 <= heap_size /\
          (U64.v obj + field_idx * 8) % 8 == 0 /\
          read_word major (U64.uint_to_t (U64.v obj + field_idx * 8)) == r /\
          is_minor_object_addr r) in
      let field_idx = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun field_idx ->
          Seq.mem obj (objects zero_addr major) /\
          is_blue obj major = false /\
          is_no_scan obj major = false /\
          field_idx >= 1 /\
          field_idx < U64.v (wosize_of_object obj major) /\
          U64.v obj + field_idx * 8 + 8 <= heap_size /\
          (U64.v obj + field_idx * 8) % 8 == 0 /\
          read_word major (U64.uint_to_t (U64.v obj + field_idx * 8)) == r /\
          is_minor_object_addr r) in
      is_minor_object_addr_bounds r;
      to_minor_offset_in_minor_range r;
      assert (is_minor_pointer r);
      assert (to_minor_offset r == r);
      let slot_witness = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun i -> i < n /\ U64.v (Seq.index slots i) == U64.v obj + field_idx * 8) in
      let slot = Seq.index slots slot_witness in
      assert (U64.v slot == U64.v obj + field_idx * 8);
      assert (U64.v slot < heap_size);
      assert (U64.v slot % U64.v mword == 0);
      assert (slot == U64.uint_to_t (U64.v obj + field_idx * 8));
      assert (to_minor_offset (read_word major (slot <: hp_addr)) == r);
      remembered_slot_targets_from_mem major slots n 0 slot_witness;
      assert (Seq.mem r (remembered_slot_targets major slots n))
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

let combined_reachable_minor_has_fwd
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma
    (requires
      RBridge.major_field_zero_no_minor minor major /\
      RBridge.remembered_roots_in_roots major roots /\
      well_formed_heap major /\
      minor_wf minor /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
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
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
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
       RBridge.remembered_roots_in_roots major roots /\
       Mark.no_pointer_to_blue major /\
       RBridge.minor_no_pointer_to_blue minor major /\
       RBridge.roots_valid_nonblue roots major
    then
      combined_reachable_images_valid_or_infix minor major fp roots;
    if UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
       RBridge.major_field_zero_no_minor minor major /\
       Mark.no_pointer_to_blue major /\
       RBridge.minor_no_pointer_to_blue minor major /\
       RBridge.roots_valid_nonblue roots major
    then begin
      remembered_roots_in_roots_from_slots major roots slots n;
      combined_reachable_images_valid_or_infix minor major fp roots
    end
  end
