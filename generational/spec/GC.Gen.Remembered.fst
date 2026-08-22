/// ---------------------------------------------------------------------------
/// GC.Gen.Remembered — Implementation of major-heap scan for minor refs
/// ---------------------------------------------------------------------------

module GC.Gen.Remembered

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

/// ---------------------------------------------------------------------------
/// Scan a single object
/// ---------------------------------------------------------------------------

/// Scan fields of a single major-heap object for minor-heap pointers
let rec scan_object_fields (major: heap) (obj: obj_addr) (wosize: nat) (i: nat)
  : GTot (seq remembered_ref) (decreases (wosize - i)) =
  if i + 1 >= wosize then Seq.empty
  else
    let field_offset = U64.v obj + (i + 1) * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then Seq.empty
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      let target = to_minor_offset field_val in
      let rest = scan_object_fields major obj wosize (i + 1) in
      if is_minor_object_addr target then
        let ref = { rem_obj = obj; rem_field = i + 1; rem_target = target } in
        Seq.cons ref rest
      else
        rest

let scan_object_for_minor_refs (major: heap) (obj: obj_addr)
  : GTot (seq remembered_ref) =
  if is_blue obj major || is_no_scan obj major then Seq.empty
  else
    let wz = U64.v (wosize_of_object obj major) in
    scan_object_fields major obj wz 0

/// ---------------------------------------------------------------------------
/// Scan entire major heap
/// ---------------------------------------------------------------------------

/// Collect remembered refs from all objects in the major heap
let rec scan_objects_list (major: heap) (objs: seq obj_addr) (idx: nat)
  : GTot (seq remembered_ref) (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then Seq.empty
  else
    let obj = Seq.index objs idx in
    let refs = scan_object_for_minor_refs major obj in
    let rest = scan_objects_list major objs (idx + 1) in
    Seq.append refs rest

let scan_major_for_minor_refs (major: heap) : GTot (seq remembered_ref) =
  let objs = objects zero_addr major in
  scan_objects_list major objs 0

/// ---------------------------------------------------------------------------
/// Extract minor-heap targets as root addresses
/// ---------------------------------------------------------------------------

let rec extract_targets (refs: seq remembered_ref) (idx: nat)
  : GTot (seq U64.t) (decreases (Seq.length refs - idx)) =
  if idx >= Seq.length refs then Seq.empty
  else
    let target = (Seq.index refs idx).rem_target in
    Seq.cons target (extract_targets refs (idx + 1))

let minor_roots_from_major (major: heap) : GTot (seq U64.t) =
  extract_targets (scan_major_for_minor_refs major) 0

/// ---------------------------------------------------------------------------
/// Helper lemmas for correctness proof
/// ---------------------------------------------------------------------------

/// extract_targets includes the .rem_target of any element at a known index
#push-options "--fuel 1 --z3rlimit 10"
let rec extract_targets_mem (refs: seq remembered_ref) (idx: nat) (j: nat)
  : Lemma (requires j >= idx /\ j < Seq.length refs)
    (ensures Seq.mem (Seq.index refs j).rem_target (extract_targets refs idx))
    (decreases (Seq.length refs - idx)) =
  if idx = j then
    Seq.mem_cons (Seq.index refs j).rem_target (extract_targets refs (idx + 1))
  else begin
    extract_targets_mem refs (idx + 1) j;
    Seq.mem_cons (Seq.index refs idx).rem_target (extract_targets refs (idx + 1))
  end
#pop-options

#push-options "--fuel 1 --z3rlimit 10"
private let rec extract_targets_sound (refs: seq remembered_ref) (idx: nat) (v: U64.t)
  : Lemma (requires Seq.mem v (extract_targets refs idx))
          (ensures exists (j:nat). idx <= j /\ j < Seq.length refs /\
                            (Seq.index refs j).rem_target == v)
          (decreases (Seq.length refs - idx)) =
  if idx >= Seq.length refs then ()
  else begin
    let target = (Seq.index refs idx).rem_target in
    let rest = extract_targets refs (idx + 1) in
    Seq.mem_cons target rest;
    if v = target then ()
    else extract_targets_sound refs (idx + 1) v
  end
#pop-options

/// scan_object_fields produces an entry whose .rem_target is the normalized target.
/// Returns the concrete index of that entry as a Ghost witness.
#push-options "--fuel 2 --z3rlimit 10"
let rec scan_object_fields_witness (major: heap) (obj: obj_addr) (wosize: nat) (i: nat) (field_idx: nat)
  : Ghost nat
    (requires
      i <= field_idx - 1 /\ field_idx < wosize /\
      U64.v obj + field_idx * 8 + 8 <= heap_size /\
      (U64.v obj + field_idx * 8) % 8 == 0 /\
      is_minor_object_addr (to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8)))))
    (ensures (fun j ->
      let result = scan_object_fields major obj wosize i in
      let target = to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))) in
      j < Seq.length result /\ (Seq.index result j).rem_target == target))
    (decreases (wosize - i)) =
  let target = to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))) in
  let field_offset_i = U64.v obj + (i + 1) * 8 in
  // Intermediate field offsets are valid since (i+1) <= field_idx
  assert (field_offset_i + 8 <= U64.v obj + field_idx * 8 + 8);
  assert (field_offset_i + 8 <= heap_size);
  if i = field_idx - 1 then
    0
  else begin
    let rest_witness = scan_object_fields_witness major obj wosize (i + 1) field_idx in
    let field_val = read_word major (U64.uint_to_t field_offset_i) in
    let target_i = to_minor_offset field_val in
    if is_minor_object_addr target_i then
      rest_witness + 1
    else
      rest_witness
  end
#pop-options

#push-options "--fuel 1 --z3rlimit 10"
private let rec scan_object_fields_sound
  (major: heap) (obj: obj_addr) (wosize: nat) (i: nat) (k: nat)
  : Lemma
    (requires k < Seq.length (scan_object_fields major obj wosize i))
    (ensures
      (let refs = scan_object_fields major obj wosize i in
       let rr = Seq.index refs k in
       rr.rem_obj == obj /\
       i < rr.rem_field /\
       rr.rem_field < wosize /\
       U64.v obj + rr.rem_field * 8 + 8 <= heap_size /\
       (U64.v obj + rr.rem_field * 8) % 8 == 0 /\
       to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + rr.rem_field * 8))) == rr.rem_target /\
       is_minor_object_addr rr.rem_target))
    (decreases (wosize - i)) =
  if i + 1 >= wosize then ()
  else begin
    let field_offset = U64.v obj + (i + 1) * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else begin
      let field_val = read_word major (U64.uint_to_t field_offset) in
      let target = to_minor_offset field_val in
      let rest = scan_object_fields major obj wosize (i + 1) in
      if is_minor_object_addr target then begin
        let ref = { rem_obj = obj; rem_field = i + 1; rem_target = target } in
        if k = 0 then ()
        else scan_object_fields_sound major obj wosize (i + 1) (k - 1)
      end else
        scan_object_fields_sound major obj wosize (i + 1) k
    end
  end
#pop-options

/// If an entry at index j0 in scan_object_for_minor_refs of object k appears
/// in the full scan_objects_list, returns the concrete index in the combined result.
#push-options "--fuel 1 --z3rlimit 10"
let rec scan_objects_list_witness (major: heap) (objs: seq obj_addr) (idx: nat) (k: nat) (j0: nat)
  : Ghost nat
    (requires
      k >= idx /\ k < Seq.length objs /\
      j0 < Seq.length (scan_object_for_minor_refs major (Seq.index objs k)))
    (ensures (fun j ->
      j < Seq.length (scan_objects_list major objs idx) /\
      Seq.index (scan_objects_list major objs idx) j ==
      Seq.index (scan_object_for_minor_refs major (Seq.index objs k)) j0))
    (decreases (Seq.length objs - idx)) =
  if k = idx then
    j0
  else
    let first_len = Seq.length (scan_object_for_minor_refs major (Seq.index objs idx)) in
    let j' = scan_objects_list_witness major objs (idx + 1) k j0 in
    first_len + j'
#pop-options

#push-options "--fuel 1 --z3rlimit 12"
private let rec scan_objects_list_sound
  (major: heap) (objs: seq obj_addr) (idx: nat) (k: nat)
  : Lemma
    (requires k < Seq.length (scan_objects_list major objs idx))
    (ensures
      (let refs = scan_objects_list major objs idx in
       let rr = Seq.index refs k in
       exists (obj: obj_addr) (field_idx: nat).
         rr.rem_obj == obj /\
         Seq.mem obj objs /\
         is_blue obj major = false /\
         is_no_scan obj major = false /\
         field_idx == rr.rem_field /\
         field_idx >= 1 /\
         field_idx < U64.v (wosize_of_object obj major) /\
         U64.v obj + field_idx * 8 + 8 <= heap_size /\
         (U64.v obj + field_idx * 8) % 8 == 0 /\
          to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))) == rr.rem_target /\
       is_minor_object_addr rr.rem_target))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then
    assert (scan_objects_list major objs idx == Seq.empty)
  else begin
    let obj = Seq.index objs idx in
    let refs0 = scan_object_for_minor_refs major obj in
    let rest = scan_objects_list major objs (idx + 1) in
    if k < Seq.length refs0 then begin
      if is_blue obj major || is_no_scan obj major then begin
        assert (refs0 == Seq.empty);
        assert False
      end;
      assert (scan_objects_list major objs idx == Seq.append refs0 rest);
      assert (Seq.index (scan_objects_list major objs idx) k == Seq.index refs0 k);
      assert (refs0 == scan_object_fields major obj (U64.v (wosize_of_object obj major)) 0);
      scan_object_fields_sound major obj (U64.v (wosize_of_object obj major)) 0 k;
      assert (Seq.index refs0 k ==
              Seq.index (scan_object_fields major obj (U64.v (wosize_of_object obj major)) 0) k);
      assert (Seq.mem obj objs)
    end else begin
      let k' = k - Seq.length refs0 in
      assert (rest == scan_objects_list major objs (idx + 1));
      scan_objects_list_sound major objs (idx + 1) k';
      assert (scan_objects_list major objs idx == Seq.append refs0 rest);
      assert (Seq.index (scan_objects_list major objs idx) k ==
              Seq.index rest k')
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Correctness
/// ---------------------------------------------------------------------------

#push-options "--fuel 2 --z3rlimit 10"
let scan_complete (major: heap) (obj: obj_addr) (field_idx: nat)
  : Lemma (requires
             well_formed_heap major /\
             Seq.mem obj (objects zero_addr major) /\
             is_blue obj major = false /\
             is_no_scan obj major = false /\
             field_idx >= 1 /\ field_idx < U64.v (wosize_of_object obj major) /\
             U64.v obj + field_idx * 8 + 8 <= heap_size /\
             (U64.v obj + field_idx * 8) % 8 == 0 /\
              is_minor_object_addr (to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8)))))
          (ensures
             Seq.mem (to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))))
                     (minor_roots_from_major major)) =
  let target = to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))) in
  let objs = objects zero_addr major in
  let wz = U64.v (wosize_of_object obj major) in

  // Step 1: find an entry in scan_object_fields with .rem_target == target
  let j0 = scan_object_fields_witness major obj wz 0 field_idx in

  // Step 2: locate obj in the objects sequence
  let k = Seq.index_mem obj objs in

  // Step 3: lift to a position in scan_objects_list (= scan_major_for_minor_refs)
  let j = scan_objects_list_witness major objs 0 k j0 in

  // Step 4: conclude membership of target in extract_targets output
  assert ((Seq.index (scan_major_for_minor_refs major) j).rem_target == target);
  extract_targets_mem (scan_major_for_minor_refs major) 0 j
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 12"
let minor_roots_from_major_sound (major: heap) (v: U64.t)
  : Lemma (requires Seq.mem v (minor_roots_from_major major))
          (ensures
            exists (obj: obj_addr) (field_idx: nat).
              Seq.mem obj (objects zero_addr major) /\
              is_blue obj major = false /\
              is_no_scan obj major = false /\
              field_idx >= 1 /\
              field_idx < U64.v (wosize_of_object obj major) /\
              U64.v obj + field_idx * 8 + 8 <= heap_size /\
              (U64.v obj + field_idx * 8) % 8 == 0 /\
              to_minor_offset (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))) == v /\
              is_minor_object_addr v)
  =
    let refs = scan_major_for_minor_refs major in
    extract_targets_sound refs 0 v;
    let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun j -> j < Seq.length refs /\ (Seq.index refs j).rem_target == v) in
    scan_objects_list_sound major (objects zero_addr major) 0 j
#pop-options
