/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Field — Field-level effects of update_major_pointers
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.Field

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
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas

open GC.Gen.PromoteUpdate.Obj
open GC.Gen.PromoteUpdate.Aux
open GC.Gen.PromoteUpdate.Header
open GC.Gen.PromoteUpdate.NoScanField

/// ---------------------------------------------------------------------------
/// update_all_objects_aux field effect
/// ---------------------------------------------------------------------------

/// Helper: find the index of an element in a sequence
private let rec seq_index_of (#a:eqtype) (s: seq a) (x: a{Seq.mem x s})
  : GTot (n:nat{n < Seq.length s /\ Seq.index s n == x})
  (decreases Seq.length s) =
  if Seq.index s 0 = x then 0
  else begin
    Seq.lemma_index_is_nth s 0;
    let tl = Seq.tail s in
    Seq.lemma_mem_append (Seq.create 1 (Seq.index s 0)) tl;
    1 + seq_index_of tl x
  end

/// Helper: adjacent elements in objects list are strictly ordered.
/// Proof by structural induction on the objects list construction.
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
private let rec objects_monotone_adjacent (g: heap) (start: hp_addr) (i: nat)
  : Lemma
    (requires i + 1 < Seq.length (objects start g))
    (ensures U64.v (Seq.index (objects start g) i) < U64.v (Seq.index (objects start g) (i + 1)))
    (decreases (Seq.length g - U64.v start)) =
  // objects start g = if start+8 >= |g| then [] else cons (start+8) (objects next_start g)
  // where next_start = start + (wz+1)*8
  if U64.v start + 8 >= Seq.length g then ()  // impossible: objects is empty, contradicts precond
  else
    let header = read_word g start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()  // impossible
    else begin
      f_address_spec start;
      let first : obj_addr = f_address start in
      if next_start_nat >= heap_size then ()  // objects is singleton, can't have i+1 < 1
      else begin
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        let rest = objects next_start g in
        // objects start g = cons first rest
        // Seq.index (cons first rest) 0 = first
        // Seq.index (cons first rest) (k+1) = Seq.index rest k
        if i = 0 then begin
          // Need: first < Seq.index rest 0
          // All elements of rest are > next_start (from objects_addresses_gt_start)
          // next_start = start + (wz+1)*8 > start + 8 = first (since wz >= 0, (wz+1)*8 >= 8)
          // Actually next_start = start + (wz+1)*8 >= start + 8 = first
          // But wz could be 0 and then next_start = start + 8 = first!
          // No: wz is getWosize header. And next_start_nat < heap_size was checked.
          // If wz = 0, then next_start = start + 8 = first, and objects_addresses_gt_start
          // gives elements of rest > next_start = first. 
          objects_addresses_gt_start next_start g (Seq.index rest 0);
          FStar.Seq.Properties.seq_mem_k rest 0;
          assert (U64.v (Seq.index rest 0) > U64.v next_start);
          assert (U64.v next_start >= U64.v first)
        end else begin
          // i > 0: Seq.index (cons first rest) i = Seq.index rest (i-1)
          //        Seq.index (cons first rest) (i+1) = Seq.index rest i
          // Need: Seq.index rest (i-1) < Seq.index rest i
          // By induction on rest = objects next_start g
          objects_monotone_adjacent g next_start (i - 1)
        end
      end
    end
#pop-options

/// Helper: objects list is strictly monotone — earlier positions have lower addresses.
/// Proof: objects_addresses_gt_start shows all elements at index > 0 have address > first element.
/// By induction on the sequence structure, earlier positions have lower addresses.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let rec objects_strictly_monotone (g: heap) (i j: nat)
  : Lemma
    (requires
      i < j /\ j < Seq.length (objects zero_addr g))
    (ensures U64.v (Seq.index (objects zero_addr g) i) < U64.v (Seq.index (objects zero_addr g) j))
    (decreases j - i) =
  if j = i + 1 then
    objects_monotone_adjacent g zero_addr i
  else begin
    objects_strictly_monotone g i (j - 1);
    objects_strictly_monotone g (j - 1) j
  end
#pop-options

/// Helper: objects before position pos have addresses < obj
#push-options "--z3rlimit 20"
private let objects_below_before (g: heap) (obj: obj_addr) (pos: nat)
  : Lemma
    (requires
      pos < Seq.length (objects zero_addr g) /\
      Seq.index (objects zero_addr g) pos == obj)
    (ensures
      (forall (k:nat). k < pos /\ k < Seq.length (objects zero_addr g) ==>
        U64.v (Seq.index (objects zero_addr g) k) < U64.v obj)) =
  let aux (k: nat{k < Seq.length (objects zero_addr g)}) : Lemma
    (requires k < pos)
    (ensures U64.v (Seq.index (objects zero_addr g) k) < U64.v obj)
  = objects_strictly_monotone g k pos
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Helper: objects after position pos have addresses > obj
#push-options "--z3rlimit 20"
private let objects_above_after (g: heap) (obj: obj_addr) (pos: nat)
  : Lemma
    (requires
      pos < Seq.length (objects zero_addr g) /\
      Seq.index (objects zero_addr g) pos == obj)
    (ensures
      (forall (k:nat). k > pos /\ k < Seq.length (objects zero_addr g) ==>
        U64.v (Seq.index (objects zero_addr g) k) > U64.v obj)) =
  let aux (k: nat{k < Seq.length (objects zero_addr g)}) : Lemma
    (requires k > pos)
    (ensures U64.v (Seq.index (objects zero_addr g) k) > U64.v obj)
  = objects_strictly_monotone g pos k
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// update_all_objects_aux processing objects AFTER obj doesn't change obj's field j.
/// Those objects are at higher addresses, so their body regions don't overlap obj's fields.
#push-options "--z3rlimit 25 --fuel 1"
let rec update_all_objects_aux_after_preserves_field
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map)
  (idx: nat) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem obj objs /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      (forall (k:nat). k >= idx /\ k < Seq.length objs ==>
        U64.v (Seq.index objs k) > U64.v obj))
    (ensures
      (let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       read_word (update_all_objects_aux major objs fwd idx) field_addr ==
       read_word major field_addr))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let other = Seq.index objs idx in
    assert (U64.v other > U64.v obj);
    if is_blue other major then
      // Blue skip: heap unchanged, field trivially preserved
      update_all_objects_aux_after_preserves_field major objs fwd (idx + 1) obj j
    else if is_no_scan other major then
      // No-scan skip: heap unchanged, field trivially preserved
      update_all_objects_aux_after_preserves_field major objs fwd (idx + 1) obj j
    else begin
      let wz_other = U64.v (wosize_of_object other major) in
      hd_address_spec other;
      // obj + j*8 < obj + wz_obj*8 < other (by objects_separated, since obj < other and both in objs)
      let wz_obj = U64.v (wosize_of_object obj major) in
      objects_separated zero_addr major obj other;
      assert (U64.v obj + (wz_obj + 1) * 8 <= U64.v other);
      assert (U64.v obj + j * 8 < U64.v other);
      let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
      assert (forall (k:nat). k < wz_other ==>
        (U64.v other + k * 8 + 8 <= heap_size /\ (U64.v other + k * 8) % 8 == 0));
      update_object_pointers_preserves_addr_below major other wz_other fwd 0 field_addr;
      let major' = update_object_pointers major other wz_other fwd 0 in
      update_object_pointers_preserves_objects major other wz_other fwd 0;
      assert (objects zero_addr major' == objs);
      // Establish well_formed_heap_part1 major'
      let aux_wfh (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr major'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
      = hd_address_spec h;
        if h = other then begin
          update_object_pointers_preserves_self_header major other wz_other fwd 0;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else if U64.v h > U64.v other then begin
          update_object_pointers_preserves_other_header major other wz_other fwd 0 h;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else begin
          update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address h);
          wosize_of_object_spec h major;
          wosize_of_object_spec h major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      // wosize of obj is unchanged: hd_address obj < other, so header is preserved
      hd_address_spec obj;
      update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address obj);
      wosize_of_object_spec obj major;
      wosize_of_object_spec obj major';
      update_all_objects_aux_after_preserves_field major' objs fwd (idx + 1) obj j
    end
  end
#pop-options

/// Main induction: update_all_objects_aux computes the expected field effect.
#push-options "--z3rlimit 25 --fuel 1 --z3refresh"
let rec update_all_objects_aux_field_effect
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map)
  (idx: nat) (obj: obj_addr) (j: nat) (pos: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem obj objs /\
      pos < Seq.length objs /\ Seq.index objs pos == obj /\
      idx <= pos /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      is_blue obj major = false /\
      is_no_scan obj major = false /\
      (forall (k:nat). k >= idx /\ k < pos ==>
        U64.v (Seq.index objs k) < U64.v obj))
    (ensures
      (let updated = update_all_objects_aux major objs fwd idx in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_raw = read_word major field_addr in
       let old_val = to_minor_offset old_raw in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_raw)))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else if idx = pos then begin
    // Processing obj itself
    let wz = U64.v (wosize_of_object obj major) in
    hd_address_spec obj;
    assert (forall (k:nat). k < wz ==>
      (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0));
    update_object_pointers_field_self major obj wz fwd 0 j;
    let major' = update_object_pointers major obj wz fwd 0 in
    update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objs);
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = obj then begin
        update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else if U64.v h > U64.v obj then begin
        update_object_pointers_preserves_other_header major obj wz fwd 0 h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
        wosize_of_object_spec h major;
        wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    update_object_pointers_preserves_self_header major obj wz fwd 0;
    wosize_of_object_spec obj major;
    wosize_of_object_spec obj major';
    // Remaining objects (pos+1..) are all > obj — they don't change field j
    objects_above_after major obj pos;
    let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
    update_all_objects_aux_after_preserves_field major' objs fwd (idx + 1) obj j
  end else begin
    // idx < pos: processing an object before obj (which has lower address)
    let other = Seq.index objs idx in
    assert (U64.v other < U64.v obj);
    if is_blue other major then
      // Blue skip: heap unchanged, recurse
      update_all_objects_aux_field_effect major objs fwd (idx + 1) obj j pos
    else if is_no_scan other major then
      // No-scan skip: heap unchanged, recurse
      update_all_objects_aux_field_effect major objs fwd (idx + 1) obj j pos
    else begin
      let wz_other = U64.v (wosize_of_object other major) in
      hd_address_spec other;
      // other's body is [other, other + wz_other*8), and by objects_separated,
      // other + (wz_other+1)*8 <= obj, so obj + j*8 >= obj > other + wz_other*8
      objects_separated zero_addr major other obj;
      let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
      assert (U64.v field_addr >= U64.v other + wz_other * 8);
      assert (forall (k:nat). k < wz_other ==>
        (U64.v other + k * 8 + 8 <= heap_size /\ (U64.v other + k * 8) % 8 == 0));
      update_object_pointers_preserves_addr_above major other wz_other fwd 0 field_addr;
      let major' = update_object_pointers major other wz_other fwd 0 in
      update_object_pointers_preserves_objects major other wz_other fwd 0;
      assert (objects zero_addr major' == objs);
      let aux_wfh (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr major'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
      = hd_address_spec h;
        if h = other then begin
          update_object_pointers_preserves_self_header major other wz_other fwd 0;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else if U64.v h > U64.v other then begin
          update_object_pointers_preserves_other_header major other wz_other fwd 0 h;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else begin
          update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address h);
          wosize_of_object_spec h major;
          wosize_of_object_spec h major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      // wosize of obj preserved (obj > other, so header of obj preserved)
      hd_address_spec obj;
      // obj > other + wz_other*8, both multiples of 8, so obj >= other + wz_other*8 + 8
      // hence hd_address obj = obj - 8 >= other + wz_other*8
      assert (U64.v (hd_address obj) >= U64.v other + wz_other * 8);
      update_object_pointers_preserves_addr_above major other wz_other fwd 0 (hd_address obj);
      // Explicitly chain: header preserved → color preserved → is_blue preserved
      color_of_object_spec obj major;
      color_of_object_spec obj major';
      is_blue_iff obj major;
      is_blue_iff obj major';
      // Also chain: header preserved → tag preserved → is_no_scan preserved
      is_no_scan_spec obj major;
      is_no_scan_spec obj major';
      tag_of_object_spec obj major;
      tag_of_object_spec obj major';
      wosize_of_object_spec obj major;
      wosize_of_object_spec obj major';
      update_all_objects_aux_field_effect major' objs fwd (idx + 1) obj j pos
    end
  end
#pop-options

/// Top-level: update_major_pointers field effect
let update_major_pointers_field_effect
  (major: heap) (fwd: forwarding_map) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      is_blue obj major = false /\
      is_no_scan obj major = false)
    (ensures
      (let updated = update_major_pointers major fwd in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_raw = read_word major field_addr in
       let old_val = to_minor_offset old_raw in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_raw))) =
  let objs = objects zero_addr major in
  let pos = seq_index_of objs obj in
  objects_below_before major obj pos;
  update_all_objects_aux_field_effect major objs fwd 0 obj j pos

/// update_major_pointers establishes well_formed_heap_part2 (pointer closure).
/// Uses pointer_closure_modulo_fwd (weaker than full part2) + fwd_all_targets_valid.
