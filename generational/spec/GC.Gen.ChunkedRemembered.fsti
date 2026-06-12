module GC.Gen.ChunkedRemembered

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module CReach = GC.Gen.ChunkedReachabilityBridge

val chunked_scan_object_fields_for_minor_refs
  : minor:minor_state -> major:MH.major_heap -> obj:obj_addr ->
    wz:nat -> i:nat -> GTot (seq U64.t)

val chunked_scan_object_for_minor_refs
  : minor:minor_state -> major:MH.major_heap -> obj:obj_addr ->
    GTot (seq U64.t)

val chunked_scan_major_objects_for_minor_refs
  : minor:minor_state -> major:MH.major_heap -> objs:seq obj_addr ->
    idx:nat -> GTot (seq U64.t)

val chunked_minor_roots_from_major
  : minor:minor_state -> major:MH.major_heap -> GTot (seq U64.t)

let chunked_minor_collection_roots
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  : GTot (seq U64.t) =
  Seq.append roots (chunked_minor_roots_from_major minor major)

let chunked_minor_roots_in_roots
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t) : prop =
  forall (v: U64.t).
    Seq.mem v (chunked_minor_roots_from_major minor major) ==>
    Seq.mem v roots

val chunked_minor_roots_in_collection_roots
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  : Lemma
    (ensures
      chunked_minor_roots_in_roots
        minor major (chunked_minor_collection_roots minor major roots))

val chunked_minor_roots_in_roots_append_prefix
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  : Lemma
    (ensures
      chunked_minor_roots_in_roots
        minor major
        (Seq.append (chunked_minor_roots_from_major minor major) roots))

val chunked_scan_object_fields_for_minor_refs_are_minor_pointers
  (minor: minor_state) (major: MH.major_heap) (obj: obj_addr)
  (wz i: nat) (v: U64.t)
  : Lemma
    (requires
      Seq.mem v
        (chunked_scan_object_fields_for_minor_refs minor major obj wz i))
    (ensures is_minor_pointer v)

val chunked_scan_object_for_minor_refs_are_minor_pointers
  (minor: minor_state) (major: MH.major_heap) (obj: obj_addr)
  (v: U64.t)
  : Lemma
    (requires
      Seq.mem v (chunked_scan_object_for_minor_refs minor major obj))
    (ensures is_minor_pointer v)

val chunked_scan_major_objects_for_minor_refs_are_minor_pointers
  (minor: minor_state) (major: MH.major_heap) (objs: seq obj_addr)
  (idx: nat) (v: U64.t)
  : Lemma
    (requires
      Seq.mem v (chunked_scan_major_objects_for_minor_refs minor major objs idx))
    (ensures is_minor_pointer v)

val chunked_minor_roots_from_major_are_minor_pointers
  (minor: minor_state) (major: MH.major_heap) (v: U64.t)
  : Lemma
    (requires Seq.mem v (chunked_minor_roots_from_major minor major))
    (ensures is_minor_pointer v)

val chunked_roots_valid_nonblue_collection_roots
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  : Lemma
    (requires CReach.chunked_roots_valid_nonblue roots major)
    (ensures
      CReach.chunked_roots_valid_nonblue
        (chunked_minor_collection_roots minor major roots) major)

val chunked_scan_object_fields_complete
  (minor: minor_state) (major: MH.major_heap) (obj: obj_addr)
  (wz i field_idx: nat) (field_addr: hp_addr) (raw v: U64.t)
  : Lemma
    (requires
      i <= field_idx /\
      field_idx < wz /\
      CG.chunked_major_field_slot obj field_idx == Some field_addr /\
      MH.read_word_in_major major field_addr == Some raw /\
      CG.chunked_classify_major_field minor major raw == Some (CG.MinorV v))
    (ensures
      Seq.mem v
        (chunked_scan_object_fields_for_minor_refs
          minor major obj wz i))

val chunked_scan_object_complete
  (minor: minor_state) (major: MH.major_heap) (obj: obj_addr)
  (field_idx: nat) (field_addr: hp_addr) (raw v: U64.t)
  : Lemma
    (requires
      ~(GenInv.chunked_is_blue major obj) /\
      CG.chunked_is_no_scan major obj == false /\
      field_idx <> 0 /\
      field_idx < CG.chunked_wosize_nat_of_object major obj /\
      CG.chunked_major_field_slot obj field_idx == Some field_addr /\
      MH.read_word_in_major major field_addr == Some raw /\
      CG.chunked_classify_major_field minor major raw == Some (CG.MinorV v))
    (ensures
      Seq.mem v (chunked_scan_object_for_minor_refs minor major obj))

val chunked_scan_major_objects_complete
  (minor: minor_state) (major: MH.major_heap) (objs: seq obj_addr)
  (idx k: nat) (v: U64.t)
  : Lemma
    (requires
      idx <= k /\
      k < Seq.length objs /\
      Seq.mem v
        (chunked_scan_object_for_minor_refs
          minor major (Seq.index objs k)))
    (ensures
      Seq.mem v
        (chunked_scan_major_objects_for_minor_refs
          minor major objs idx))

val chunked_minor_roots_from_major_complete
  (minor: minor_state) (major: MH.major_heap) (src: obj_addr)
  (i: nat) (field_addr: hp_addr) (raw v: U64.t)
  : Lemma
    (requires
      Seq.mem src (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major src) /\
      CG.chunked_is_no_scan major src == false /\
      i <> 0 /\
      i < CG.chunked_wosize_nat_of_object major src /\
      CG.chunked_major_field_slot src i == Some field_addr /\
      MH.read_word_in_major major field_addr == Some raw /\
      CG.chunked_classify_major_field minor major raw == Some (CG.MinorV v))
    (ensures
      Seq.mem v (chunked_minor_roots_from_major minor major))

val chunked_remembered_minor_edges_in_roots_from_scan
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  : Lemma
    (requires chunked_minor_roots_in_roots minor major roots)
    (ensures CReach.chunked_remembered_minor_edges_in_roots minor major roots)
