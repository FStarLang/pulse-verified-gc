/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Aux — the pointer-update walk: objects, part 1, live-set extensionality
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.Aux

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.Obj

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let header_eq_object_facts (g1 g2: heap) (h: obj_addr) =
  color_of_header_eq h g1 g2;
  wosize_of_object_spec h g1; wosize_of_object_spec h g2;
  tag_of_object_spec h g1; tag_of_object_spec h g2;
  is_no_scan_spec h g1; is_no_scan_spec h g2;
  is_infix_spec h g1; is_infix_spec h g2
#pop-options

#push-options "--z3rlimit 12 --fuel 1"
let update_object_pointers_step (major: heap) (obj: obj_addr) (fwd: forwarding_map) =
  let wz = U64.v (wosize_of_object obj major) in
  hd_address_spec obj;
  assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
  assert (forall (j:nat). j < wz ==>
    (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0));
  update_object_pointers_preserves_objects major obj wz fwd 0;
  let major' = update_object_pointers major obj wz fwd 0 in
  let hdr (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr major))
    (ensures read_word major' (hd_address h) == read_word major (hd_address h))
  = hd_address_spec h;
    if h = obj then
      update_object_pointers_preserves_self_header major obj wz fwd 0
    else if U64.v h > U64.v obj then
      update_object_pointers_preserves_other_header major obj wz fwd 0 h
    else
      // h < obj: hd_address(h) = h - 8 < h < obj, so it's below obj
      update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires hdr);
  let aux_wfh (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr major'))
    (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
  = hdr h;
    wosize_of_object_spec h major';
    wosize_of_object_spec h major
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh)
#pop-options

/// The live walk keeps the object list and part 1: each step does.
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let rec update_live_aux_preserves_objects_wfh
  (major: heap) (objs: seq obj_addr) (live: obj_addr -> prop) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major)
    (ensures (let major' = update_live_aux major objs live fwd idx in
              objects zero_addr major' == objs /\
              well_formed_heap_part1 major'))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if not (FStar.IndefiniteDescription.strong_excluded_middle (live obj)) then
      update_live_aux_preserves_objects_wfh major objs live fwd (idx + 1)
    else if is_no_scan obj major then
      update_live_aux_preserves_objects_wfh major objs live fwd (idx + 1)
    else begin
      let wz = U64.v (wosize_of_object obj major) in
      update_object_pointers_step major obj fwd;
      update_live_aux_preserves_objects_wfh
        (update_object_pointers major obj wz fwd 0) objs live fwd (idx + 1)
    end
  end
#pop-options

let update_live_pointers_preserves_objects major live fwd =
  update_live_aux_preserves_objects_wfh major (objects zero_addr major) live fwd 0

let update_live_pointers_preserves_wfh_part1 major live fwd =
  update_live_aux_preserves_objects_wfh major (objects zero_addr major) live fwd 0

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let rec update_live_aux_ext
  (major: heap) (objs: seq obj_addr) (live1 live2: obj_addr -> prop)
  (fwd: forwarding_map) (idx: nat)
  : Lemma (requires forall (x: obj_addr). Seq.mem x objs ==> (live1 x <==> live2 x))
    (ensures update_live_aux major objs live1 fwd idx == update_live_aux major objs live2 fwd idx)
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if not (FStar.IndefiniteDescription.strong_excluded_middle (live1 obj)) then
      update_live_aux_ext major objs live1 live2 fwd (idx + 1)
    else if is_no_scan obj major then
      update_live_aux_ext major objs live1 live2 fwd (idx + 1)
    else
      update_live_aux_ext
        (update_object_pointers major obj (U64.v (wosize_of_object obj major)) fwd 0)
        objs live1 live2 fwd (idx + 1)
  end
#pop-options

let update_live_pointers_ext major live1 live2 fwd =
  update_live_aux_ext major (objects zero_addr major) live1 live2 fwd 0

/// `update_major_pointers` is defined as the live walk at `idle_live`.
let update_live_pointers_idle major fwd = ()

/// update_major_pointers preserves the objects walk.
let update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map) =
  update_live_pointers_idle major fwd;
  update_live_pointers_preserves_objects major (idle_live major) fwd

/// update_major_pointers preserves well_formed_heap_part1.
let update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map) =
  update_live_pointers_idle major fwd;
  update_live_pointers_preserves_wfh_part1 major (idle_live major) fwd

