module GC.Gen.ChunkedCheneyInjectivity

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Lib.Header

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module Fields = GC.Spec.Fields
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedMarkTargetMembership =
  GC.Spec.ChunkedMarkBounded.TargetMembership
module ChunkedCheney = GC.Gen.ChunkedCheney
module CheneyPres = GC.Gen.CheneyPreservation
module GenMajorGCBridge = GC.Gen.ChunkedMajorGCBridge

/// Chunked Cheney forwarding is injective on ordinary minor object starts.
/// Infix sources are excluded because they map to interior pointers inside
/// their already-forwarded parent object.
[@"opaque_to_smt"]
val chunked_fwd_normal_injective
  : minor:minor_state -> fwd:forwarding_map -> Tot prop

val chunked_fwd_normal_injective_elim
  : minor:minor_state -> fwd:forwarding_map -> x:U64.t -> y:U64.t ->
    Lemma
      (requires
        chunked_fwd_normal_injective minor fwd /\
        fwd x <> 0UL /\
        fwd y <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        Seq.mem y (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        ~(is_infix_in_minor minor y) /\
        minor_wosize minor x > 0 /\
        minor_wosize minor y > 0 /\
        fwd x == fwd y)
      (ensures x == y)

/// Every nonzero forwarding entry for a non-infix source names an ordinary
/// positive-size minor object.  This source-shape fact is heap-independent; it
/// follows from the chunked Cheney forwarding equations alone.
[@"opaque_to_smt"]
val chunked_fwd_noninfix_sources_valid
  : minor:minor_state -> fwd:forwarding_map -> Tot prop

val chunked_fwd_noninfix_sources_valid_elim
  : minor:minor_state -> fwd:forwarding_map -> x:U64.t ->
    Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor fwd /\
        fwd x <> 0UL /\
        ~(is_infix_in_minor minor x))
      (ensures
        Seq.mem x (minor_objects minor) /\
        minor_wosize minor x > 0)

val chunked_cheney_promote_fwd_noninfix_sources_valid
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         chunked_fwd_noninfix_sources_valid minor res.fwd_map))

/// Ordinary forwarded minor object starts map to active non-blue major objects
/// in the current chunked major heap.  This is the reusable target-shape half of
/// the chunked Cheney injectivity invariant.
[@"opaque_to_smt"]
val chunked_fwd_normal_targets_not_blue
  : minor:minor_state -> fwd:forwarding_map -> mh:MH.major_heap -> Tot prop

val chunked_fwd_normal_targets_not_blue_elim
  : minor:minor_state -> fwd:forwarding_map -> mh:MH.major_heap ->
    x:U64.t ->
    Lemma
      (requires
        chunked_fwd_normal_targets_not_blue minor fwd mh /\
        fwd x <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        minor_wosize minor x > 0)
      (ensures
        is_val_addr (fwd x) /\
        (let target : obj_addr = fwd x in
         Seq.mem target (MH.major_objects mh) /\
         (match MH.read_word_in_major mh (hd_address target) with
          | Some hdr -> getColor hdr <> Blue /\ U64.v (getWosize hdr) >= 1
          | None -> False)))

val chunked_cheney_promote_fwd_normal_injective
  : minor:minor_state -> major:GC.Spec.MajorHeap.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GC.Gen.HeapInvariant.chunked_major_alloc_shape
          major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GC.Gen.HeapInvariant.chunked_chain_objects_blue
          major fp alloc_fuel /\
        GC.Gen.CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        chunked_fwd_normal_injective minor
          (GC.Gen.ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel).fwd_map)

val chunked_cheney_promote_fwd_normal_targets_not_blue
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GC.Gen.HeapInvariant.chunked_major_alloc_shape
          major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GC.Gen.HeapInvariant.chunked_chain_objects_blue
          major fp alloc_fuel /\
        GC.Gen.CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
          GC.Gen.ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         chunked_fwd_normal_targets_not_blue minor res.fwd_map res.major_final))

val chunked_cheney_promote_fwd_noninfix_targets_not_infix
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         GenMajorGCBridge.chunked_fwd_noninfix_targets_not_infix
           minor res.fwd_map res.major_final))

val chunked_cheney_promote_updated_fwd_noninfix_targets_not_infix
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final alloc_fuel))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         GenMajorGCBridge.chunked_fwd_noninfix_targets_not_infix
           minor res.fwd_map
           (GC.Gen.ChunkedUpdate.chunked_update_major_pointers
             res.major_final res.fwd_map)))

val chunked_cheney_promote_fwd_target_minor_field_no_infix
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    x:U64.t -> j:nat -> field_addr:hp_addr -> raw:U64.t ->
    Lemma
      (requires
        minor_wf minor /\
        GenInv.minor_fields_no_infix_targets minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         res.fwd_map x <> 0UL /\
         Seq.mem x (minor_objects minor) /\
         ~(is_infix_in_minor minor x) /\
         j < minor_wosize minor x /\
         U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword /\
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         is_minor_pointer (to_minor_offset raw)))
      (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))

val chunked_cheney_promote_old_nonblue_field_no_infix
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    src:obj_addr -> hdr:U64.t -> j:nat -> field_addr:hp_addr ->
    old:U64.t -> raw:U64.t ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        GenInv.chunked_major_minor_fields_no_infix_targets minor major /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> Blue /\
        U64.v (getTag hdr) < U64.v no_scan_tag /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         is_minor_pointer (to_minor_offset raw)))
      (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))

val chunked_cheney_promote_fwd_target_minor_major_field_raw_target
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    x:U64.t -> j:nat -> field_addr:hp_addr -> raw:U64.t ->
    Lemma
      (requires
        minor_wf minor /\
        GenInv.chunked_minor_major_fields_no_blue minor major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CheneyPres.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         res.fwd_map x <> 0UL /\
         Seq.mem x (minor_objects minor) /\
         ~(is_infix_in_minor minor x) /\
         j < minor_wosize minor x /\
         U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword /\
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         Fields.is_pointer_field raw /\
         MarkDefs.chunked_is_pointer_field res.major_final raw))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr
                    res.major_final raw)
           (MH.major_objects res.major_final)))

val chunked_cheney_promote_old_nonblue_field_raw_target
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    src:obj_addr -> hdr:U64.t -> j:nat -> field_addr:hp_addr ->
    old:U64.t -> raw:U64.t ->
    Lemma
      (requires
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         MarkDefs.chunked_is_pointer_field res.major_final raw))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr
                    res.major_final raw)
           (MH.major_objects res.major_final)))

val chunked_cheney_promote_old_field_source_case
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    src:obj_addr -> j:nat -> field_addr:hp_addr -> raw:U64.t ->
    Tot prop

val chunked_cheney_promote_fwd_field_source_case
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    src:obj_addr -> j:nat -> field_addr:hp_addr -> raw:U64.t ->
    Tot prop

val chunked_cheney_promote_field_source_cases
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Tot prop

val chunked_cheney_promote_old_field_source_case_intro
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    src:obj_addr -> hdr:U64.t -> j:nat -> field_addr:hp_addr ->
    raw:U64.t ->
    Lemma
      (requires
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (getTag hdr) < U64.v no_scan_tag /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw))
      (ensures
        chunked_cheney_promote_old_field_source_case
          minor major fp roots alloc_fuel src j field_addr raw)

val chunked_cheney_promote_fwd_field_source_case_intro
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    x:U64.t -> src:obj_addr -> j:nat -> field_addr:hp_addr ->
    raw:U64.t ->
    Lemma
      (requires
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         res.fwd_map x == src /\
         Seq.mem x (minor_objects minor) /\
         ~(is_infix_in_minor minor x) /\
         j < minor_wosize minor x /\
         U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword))
      (ensures
        chunked_cheney_promote_fwd_field_source_case
          minor major fp roots alloc_fuel src j field_addr raw)

val chunked_cheney_promote_field_source_cases_from_nonblue_origin
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        minor_infix_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CheneyPres.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        chunked_cheney_promote_field_source_cases
          minor major fp roots alloc_fuel)

val chunked_cheney_promote_major_minor_fields_no_infix_targets
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        minor_infix_wf minor /\
        GenInv.minor_fields_no_infix_targets minor /\
        GenInv.chunked_major_minor_fields_no_infix_targets minor major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CheneyPres.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         GenInv.chunked_major_minor_fields_no_infix_targets
           minor res.major_final))

/// Minor fields that already point into the chunked major heap must target
/// active non-blue, non-infix major objects.  This is the copied-field analogue
/// of `chunked_major_field_targets_non_infix`.
[@"opaque_to_smt"]
val chunked_minor_major_fields_nonblue_non_infix_targets
  : minor:minor_state -> mh:MH.major_heap -> Tot prop

val chunked_minor_major_fields_nonblue_non_infix_targets_elim
  : minor:minor_state -> mh:MH.major_heap -> obj:U64.t -> j:nat ->
    Lemma
      (requires
        chunked_minor_major_fields_nonblue_non_infix_targets minor mh /\
        Seq.mem obj (minor_objects minor) /\
        j < minor_wosize minor obj /\
        MarkDefs.chunked_is_pointer_field mh
          (minor_read_field minor obj j))
      (ensures
        (let raw = minor_read_field minor obj j in
         let target = MarkDefs.chunked_pointer_field_as_obj_addr mh raw in
         Seq.mem target (MH.major_objects mh) /\
         ~(GenInv.chunked_is_blue mh target) /\
         ~(SweepDefs.chunked_is_infix mh target)))

[@"opaque_to_smt"]
val chunked_nonblue_scanned_raw_targets_in_major
  : mh:MH.major_heap -> Tot prop

val chunked_nonblue_scanned_raw_targets_in_major_elim
  : mh:MH.major_heap -> obj:obj_addr -> i:U64.t{U64.v i >= 1} ->
    Lemma
      (requires
        chunked_nonblue_scanned_raw_targets_in_major mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(GenInv.chunked_is_blue mh obj) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         if MarkDefs.chunked_is_pointer_field mh v then
          let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          Seq.mem child_raw (MH.major_objects mh) /\
          ~(SweepDefs.chunked_is_infix mh child_raw)
         else
          True))

val chunked_cheney_promote_nonblue_scanned_raw_targets_in_major
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        minor_wf minor /\
        minor_infix_wf minor /\
        GenInv.chunked_no_pointer_to_blue major /\
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major major /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix major /\
        (forall (target: obj_addr).
          Seq.mem target (MH.major_objects major) ==>
          Fields.is_pointer_field target) /\
        chunked_minor_major_fields_nonblue_non_infix_targets minor major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        GC.Spec.MajorAllocator.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPres.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CheneyPres.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         chunked_nonblue_scanned_raw_targets_in_major res.major_final))

val chunked_nonblue_scanned_raw_targets_in_major_to_bounded
  : mh:MH.major_heap ->
    Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        ChunkedMarkTargetMembership.chunked_nonblue_scanned_raw_targets_in_major
          mh)
