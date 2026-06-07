module GC.Gen.ChunkedRemembered

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module CReach = GC.Gen.ChunkedReachabilityBridge
module SeqMem = GC.Spec.SeqMemLemmas
module SeqProps = FStar.Seq.Properties

let rec chunked_scan_object_fields_for_minor_refs
  (minor: minor_state) (major: MH.major_heap) (obj: obj_addr)
  (wz: nat) (i: nat)
  : GTot (seq U64.t)
    (decreases (if i < wz then wz - i else 0))
  =
  if i >= wz then Seq.empty
  else
    let rest =
      chunked_scan_object_fields_for_minor_refs
        minor major obj wz (i + 1) in
    match CG.chunked_major_field_slot obj i with
    | None -> rest
    | Some field_addr ->
      match MH.read_word_in_major major field_addr with
      | None -> rest
      | Some raw ->
        match CG.chunked_classify_major_field minor major raw with
        | Some dst ->
          (match dst with
           | CG.MinorV v -> Seq.cons v rest
           | CG.MajorV _ -> rest
           | _ -> rest)
        | None -> rest

let chunked_scan_object_for_minor_refs
  (minor: minor_state) (major: MH.major_heap) (obj: obj_addr)
  : GTot (seq U64.t)
  =
  if GenInv.chunked_is_blue major obj then Seq.empty
  else if CG.chunked_is_no_scan major obj then Seq.empty
  else
    chunked_scan_object_fields_for_minor_refs
      minor major obj (CG.chunked_wosize_nat_of_object major obj) 1

let rec chunked_scan_major_objects_for_minor_refs
  (minor: minor_state) (major: MH.major_heap) (objs: seq obj_addr)
  (idx: nat)
  : GTot (seq U64.t)
    (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then Seq.empty
  else
    let obj = Seq.index objs idx in
    Seq.append
      (chunked_scan_object_for_minor_refs minor major obj)
      (chunked_scan_major_objects_for_minor_refs
        minor major objs (idx + 1))

let chunked_minor_roots_from_major
  (minor: minor_state) (major: MH.major_heap)
  : GTot (seq U64.t)
  =
  chunked_scan_major_objects_for_minor_refs
    minor major (MH.major_objects major) 0

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_minor_roots_in_collection_roots
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  : Lemma
    (ensures
      chunked_minor_roots_in_roots
        minor major (chunked_minor_collection_roots minor major roots))
  =
  let scan = chunked_minor_roots_from_major minor major in
  let prove (v: U64.t)
    : Lemma
      (requires Seq.mem v scan)
      (ensures Seq.mem v (Seq.append roots scan))
    =
    SeqProps.lemma_append_count roots scan
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove)

let chunked_minor_roots_in_roots_append_prefix
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  : Lemma
    (ensures
      chunked_minor_roots_in_roots
        minor major
        (Seq.append (chunked_minor_roots_from_major minor major) roots))
  =
  let scan = chunked_minor_roots_from_major minor major in
  let prove (v: U64.t)
    : Lemma
      (requires Seq.mem v scan)
      (ensures Seq.mem v (Seq.append scan roots))
    =
    SeqProps.lemma_append_count scan roots
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove)
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let rec chunked_scan_object_fields_complete
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
    (decreases (if i < wz then wz - i else 0))
  =
  if i >= wz then
    assert False
  else begin
    let rest =
      chunked_scan_object_fields_for_minor_refs
        minor major obj wz (i + 1) in
    if i = field_idx then begin
      match CG.chunked_major_field_slot obj i with
      | None -> assert False
      | Some field_addr_i ->
        assert (field_addr_i == field_addr);
        match MH.read_word_in_major major field_addr_i with
        | None -> assert False
        | Some raw_i ->
          assert (raw_i == raw);
          match CG.chunked_classify_major_field minor major raw_i with
          | Some dst ->
            (match dst with
             | CG.MinorV v_i ->
               assert (v_i == v);
               SeqMem.seq_mem_cons_head v rest
             | CG.MajorV _ -> assert False
             | _ -> assert False)
          | None -> assert False
    end else begin
      assert (i < field_idx);
      assert (i + 1 <= field_idx);
      chunked_scan_object_fields_complete
        minor major obj wz (i + 1) field_idx field_addr raw v;
      match CG.chunked_major_field_slot obj i with
      | None -> ()
      | Some field_addr_i ->
        match MH.read_word_in_major major field_addr_i with
        | None -> ()
        | Some raw_i ->
          match CG.chunked_classify_major_field minor major raw_i with
          | Some dst ->
            (match dst with
             | CG.MinorV v_i -> SeqMem.seq_mem_cons_tail v_i v rest
             | CG.MajorV _ -> ()
             | _ -> ())
          | None -> ()
    end
  end
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_scan_object_complete
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
  =
  if GenInv.chunked_is_blue major obj then
    assert False
  else if CG.chunked_is_no_scan major obj then
    assert False
  else begin
    assert (1 <= field_idx);
    chunked_scan_object_fields_complete
      minor major obj
      (CG.chunked_wosize_nat_of_object major obj)
      1 field_idx field_addr raw v
  end
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let rec chunked_scan_major_objects_complete
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
    (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then
    assert False
  else begin
    let refs =
      chunked_scan_object_for_minor_refs
        minor major (Seq.index objs idx) in
    let rest =
      chunked_scan_major_objects_for_minor_refs
        minor major objs (idx + 1) in
    if k = idx then begin
      assert (Seq.index objs k == Seq.index objs idx);
      FStar.Seq.Properties.lemma_append_count refs rest
    end else begin
      assert (idx < k);
      assert (idx + 1 <= k);
      chunked_scan_major_objects_complete
        minor major objs (idx + 1) k v;
      FStar.Seq.Properties.lemma_append_count refs rest
    end
  end
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_minor_roots_from_major_complete
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
  =
  chunked_scan_object_complete minor major src i field_addr raw v;
  let k = Seq.index_mem src (MH.major_objects major) in
  chunked_scan_major_objects_complete
    minor major (MH.major_objects major) 0 k v
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_remembered_minor_edges_in_roots_from_scan
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  : Lemma
    (requires chunked_minor_roots_in_roots minor major roots)
    (ensures CReach.chunked_remembered_minor_edges_in_roots minor major roots)
  =
  let prove (src: obj_addr) (i: nat) (field_addr: hp_addr)
            (raw v: U64.t)
    : Lemma
      (requires
        Seq.mem src (MH.major_objects major) /\
        ~(GenInv.chunked_is_blue major src) /\
        CG.chunked_is_no_scan major src == false /\
        i <> 0 /\
        i < CG.chunked_wosize_nat_of_object major src /\
        CG.chunked_major_field_slot src i == Some field_addr /\
        MH.read_word_in_major major field_addr == Some raw /\
        CG.chunked_classify_major_field minor major raw ==
          Some (CG.MinorV v))
      (ensures Seq.mem v roots)
    =
    chunked_minor_roots_from_major_complete
      minor major src i field_addr raw v;
    assert (Seq.mem v (chunked_minor_roots_from_major minor major))
  in
  let prove_for_quantifiers
    (src: obj_addr) (i: nat) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
      (ensures
        forall (v: U64.t).
          Seq.mem src (MH.major_objects major) /\
          ~(GenInv.chunked_is_blue major src) /\
          CG.chunked_is_no_scan major src == false /\
          i <> 0 /\
          i < CG.chunked_wosize_nat_of_object major src /\
          CG.chunked_major_field_slot src i == Some field_addr /\
          MH.read_word_in_major major field_addr == Some raw /\
          CG.chunked_classify_major_field minor major raw ==
            Some (CG.MinorV v) ==>
          Seq.mem v roots)
    =
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires
        (prove src i field_addr raw))
  in
  FStar.Classical.forall_intro_4 prove_for_quantifiers
#pop-options
