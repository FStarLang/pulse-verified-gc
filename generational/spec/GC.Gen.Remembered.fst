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
  if i >= wosize then Seq.empty
  else
    let field_offset = U64.v obj + (i + 1) * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then Seq.empty
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      let rest = scan_object_fields major obj wosize (i + 1) in
      if is_minor_addr field_val then
        let ref = { rem_obj = obj; rem_field = i + 1; rem_target = field_val } in
        Seq.cons ref rest
      else
        rest

let scan_object_for_minor_refs (major: heap) (obj: obj_addr)
  : GTot (seq remembered_ref) =
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
  let objs = objects 0UL major in
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
/// Correctness (admitted — to be proven)
/// ---------------------------------------------------------------------------

let scan_complete (major: heap) (obj: obj_addr) (field_idx: nat)
  : Lemma (requires
             well_formed_heap major /\
             Seq.mem obj (objects 0UL major) /\
             field_idx >= 1 /\ field_idx <= U64.v (wosize_of_object obj major) /\
             U64.v obj + field_idx * 8 + 8 <= heap_size /\
             (U64.v obj + field_idx * 8) % 8 == 0 /\
             is_minor_addr (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8))))
          (ensures
             Seq.mem (read_word major (U64.uint_to_t (U64.v obj + field_idx * 8)))
                     (minor_roots_from_major major)) =
  admit ()
