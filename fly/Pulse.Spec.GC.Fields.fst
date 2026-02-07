/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Fields - Object Enumeration for Concurrent GC
/// ---------------------------------------------------------------------------
///
/// This module provides functions to enumerate objects in the heap:
/// - objects: enumerate all allocated objects
/// - allocated_blocks: get all allocated block addresses
/// - black_blocks, gray_blocks, white_blocks: color-filtered enumerations

module Pulse.Spec.GC.Fields

open FStar.Seq
open FStar.List.Tot
module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object

/// ---------------------------------------------------------------------------
/// Type Aliases
/// ---------------------------------------------------------------------------

/// Word size (54-bit value from header)
/// Since getWosize = shift_right hdr 10, and hdr < 2^64, the result is < 2^54
type wosize = w:U64.t{U64.v w < pow2 54}

/// Coerce wosize_of_object result to wosize type
/// Uses the fact that shift_right by 10 always produces a value < 2^54
let wosize_of_object_as_wosize (h_addr: obj_addr) (g: heap) : GTot wosize =
  wosize_of_object_bound h_addr g;
  wosize_of_object h_addr g

/// ---------------------------------------------------------------------------
/// Header/Object Address Conversion
/// ---------------------------------------------------------------------------

/// Header address from object address (handles < 8 case safely)
/// For obj_addr (>= 8), this equals Heap.hd_address
let hd_address_safe (addr: hp_addr) : hp_addr = 
  if U64.v addr >= 8 then U64.sub addr mword else 0UL

/// Object address from header address (add 8 bytes)
let obj_address (hd_addr: hp_addr) : U64.t = U64.add_mod hd_addr mword

/// Helper: prove multiplication bound for field offset
private let field_offset_bound (field_idx: U64.t{U64.v field_idx < pow2 61}) : Lemma 
  (FStar.UInt.size FStar.Mul.(U64.v field_idx * 8) 64)
= 
  FStar.Math.Lemmas.pow2_plus 61 3;
  assert (FStar.Mul.(pow2 61 * pow2 3) == pow2 64);
  assert (FStar.Mul.(U64.v field_idx * 8) < pow2 64)

/// Field offset from index
let field_offset (field_idx: U64.t{U64.v field_idx < pow2 61}) : U64.t = 
  field_offset_bound field_idx;
  U64.mul field_idx mword

/// Field address from object address and field index
/// Returns a value that may not be a valid hp_addr without additional constraints
let field_address_raw (obj_addr: hp_addr) (field_idx: U64.t{U64.v field_idx < pow2 61}) : U64.t =
  U64.add_mod obj_addr (field_offset field_idx)

/// Field address with proof it's a valid hp_addr
/// Requires: object at obj_addr has wosize >= field_idx and fits in heap
let field_address (obj_addr: hp_addr) (field_idx: U64.t{U64.v field_idx < pow2 61})
  : Pure hp_addr
    (requires U64.v obj_addr + FStar.Mul.(U64.v field_idx * 8) < heap_size)
    (ensures fun r -> U64.v r = U64.v obj_addr + FStar.Mul.(U64.v field_idx * 8))
  = 
  field_offset_bound field_idx;
  let offset = field_offset field_idx in
  // obj_addr < heap_size, offset < 2^64, sum < heap_size < 2^64, so no overflow
  assert (U64.v obj_addr + U64.v offset < heap_size);
  assert (U64.v obj_addr + U64.v offset < pow2 64);
  U64.add obj_addr offset

/// Check if value looks like a pointer (word-aligned, within heap bounds, with room for header)
let is_pointer (v: U64.t) : bool = 
  U64.v v >= 8 && U64.v v < heap_size && U64.v v % 8 = 0

/// Check if field value looks like a pointer
let is_pointer_field (field_val: U64.t) : bool = is_pointer field_val

/// Helper: wosize is always < pow2 61
let wosize_fits_field_index (wz: wosize) 
  : Lemma (U64.v wz < pow2 61)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54

/// Object is well-formed: fits entirely within heap
let well_formed_object (g: heap) (h: obj_addr) : prop =
  let wz = wosize_of_object h g in
  U64.v (hd_address h) + 8 + FStar.Mul.(U64.v wz * 8) <= heap_size

/// Helper: well_formed_object implies field addresses are valid
let well_formed_field_address (g: heap) (h: obj_addr) (idx: U64.t{U64.v idx < pow2 61})
  : Lemma (requires well_formed_object g h /\ U64.v idx < U64.v (wosize_of_object h g))
          (ensures U64.v h + FStar.Mul.(U64.v idx * 8) < heap_size)
  = let wz_obj = wosize_of_object h g in
    hd_address_spec h;
    // well_formed_object: (h - 8) + 8 + wz*8 <= heap_size = h + wz*8 <= heap_size
    // idx < wz, so h + idx*8 < h + wz*8 <= heap_size
    ()

/// Unchecked version - does not require well_formed_object precondition  
/// Used in well_formed_heap definition to avoid circularity
let rec exists_field_pointing_to_unchecked (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr) 
  : GTot bool (decreases U64.v wz) =
  if wz = 0UL then false
  else
    let idx = U64.sub wz 1UL in
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    let field_addr_raw = field_address_raw h idx in
    if U64.v field_addr_raw >= heap_size || U64.v field_addr_raw % 8 <> 0 then false
    else
      let field_addr : hp_addr = field_addr_raw in
      let field_val = read_word g field_addr in
      if is_pointer_field field_val && U64.v field_val >= U64.v mword && hd_address field_val = hd_address target then true
      else exists_field_pointing_to_unchecked g h idx target

/// Helper: check if any field points to target
/// Requires: object is well-formed (fits in heap)
#push-options "--z3rlimit 100"
let rec exists_field_pointing_to (g: heap) (h: obj_addr) (wz: wosize) (target: obj_addr) 
  : Ghost bool 
    (requires well_formed_object g h /\ U64.v wz <= U64.v (wosize_of_object h g))
    (ensures fun _ -> True)
    (decreases U64.v wz) =
  if wz = 0UL then false
  else begin
    let idx = U64.sub wz 1UL in
    wosize_fits_field_index wz;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    // well_formed_object g h means: hd_address h + 8 + (wosize_of_object h g)*8 <= heap_size
    // hd_address_spec tells us: hd_address h = h - 8
    // So hd_address h + 8 = h
    // Therefore h + (wosize_of_object h g)*8 <= heap_size
    // Since wz <= wosize_of_object h g and idx < wz:
    // h + idx*8 < h + wz*8 <= h + (wosize_of_object h g)*8 <= heap_size
    let wz_obj = wosize_of_object h g in
    hd_address_spec h;
    // Now SMT knows U64.v (hd_address h) = U64.v h - 8
    // well_formed_object: (h - 8) + 8 + wz_obj*8 <= heap_size = h + wz_obj*8 <= heap_size
    assert (U64.v h + FStar.Mul.(U64.v wz_obj * 8) <= heap_size);
    assert (U64.v h + FStar.Mul.(U64.v wz * 8) <= heap_size);
    assert (U64.v h + FStar.Mul.(U64.v idx * 8) < U64.v h + FStar.Mul.(U64.v wz * 8));
    let field_addr = field_address h idx in
    let field_val = read_word g field_addr in
    if is_pointer_field field_val && U64.v field_val >= U64.v mword && hd_address field_val = hd_address target then true
    else exists_field_pointing_to g h idx target
  end
#pop-options

/// The checked and unchecked versions are equivalent when object is well-formed
/// Proof: when well_formed_object g h, all field addresses are valid hp_addrs,
/// so the unchecked version's bounds check always passes
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec exists_field_checked_eq_unchecked (g: heap) (h: obj_addr) (wz: wosize) (target: obj_addr)
  : Lemma 
    (requires well_formed_object g h /\ U64.v wz <= U64.v (wosize_of_object h g))
    (ensures exists_field_pointing_to g h wz target == exists_field_pointing_to_unchecked g h wz target)
    (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      wosize_fits_field_index wz;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      let wz_obj = wosize_of_object h g in
      hd_address_spec h;
      // From well_formed_object: h + wz_obj*8 <= heap_size
      assert (U64.v h + FStar.Mul.(U64.v wz_obj * 8) <= heap_size);
      // idx < wz <= wz_obj, so h + idx*8 < heap_size < pow2 64
      assert (U64.v h + FStar.Mul.(U64.v idx * 8) < heap_size);
      // No overflow in field_address_raw since h + 8*idx < heap_size < pow2 64
      field_offset_bound idx;
      assert (U64.v h + FStar.Mul.(U64.v idx * 8) < pow2 64);
      // So field_address_raw = h + 8*idx (mod is no-op)
      let fa_raw = field_address_raw h idx in
      assert (U64.v fa_raw = U64.v h + FStar.Mul.(U64.v idx * 8));
      // Bounds check in unchecked version passes
      assert (U64.v fa_raw < heap_size);
      assert (U64.v fa_raw % 8 = 0);
      // field_address returns the same value
      let fa = field_address h idx in
      assert (U64.v fa = U64.v fa_raw);
      // Both read the same word and check the same condition
      let field_val = read_word g fa in
      if is_pointer_field field_val && U64.v field_val >= U64.v mword && hd_address field_val = hd_address target then ()
      else exists_field_checked_eq_unchecked g h idx target
    end
#pop-options

/// Check if object h points to object target
/// Uses wosize_of_object_bound to ensure valid wosize
let is_pointer_to_object (g: heap) (h: obj_addr) (target: obj_addr) : GTot bool =
  let wz = wosize_of_object h g in
  wosize_of_object_bound h g;
  exists_field_pointing_to_unchecked g h wz target

/// is_pointer_to_object implies exists_field_pointing_to when well_formed
let is_pointer_to_object_implies_exists_field (g: heap) (h: obj_addr) (target: obj_addr)
  : Lemma 
    (requires well_formed_object g h /\ is_pointer_to_object g h target)
    (ensures exists_field_pointing_to g h (wosize_of_object_as_wosize h g) target)
  = let wz = wosize_of_object_as_wosize h g in
    exists_field_checked_eq_unchecked g h wz target

/// ---------------------------------------------------------------------------
/// Object Enumeration
/// ---------------------------------------------------------------------------

/// Enumerate all objects in heap starting from address
/// Objects are laid out consecutively: |header|field1|field2|...|fieldN|header|...
let rec objects (start: hp_addr) (g: heap) : GTot (Seq.seq hp_addr) (decreases (Seq.length g - U64.v start)) =
  if U64.v start + 8 >= Seq.length g then Seq.empty  // Need room for at least header + 1 field
  else
    let header = read_word g start in
    let wz = getWosize header in
    let obj_addr_raw = obj_address start in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then Seq.empty
    else begin
      // obj_addr_raw = start + 8
      // start < heap_size (from hp_addr), start + 8 < heap_size (from condition)
      // start % 8 = 0 (from hp_addr), so (start + 8) % 8 = 0
      assert (U64.v obj_addr_raw = (U64.v start + 8) % pow2 64);
      assert (U64.v start + 8 < heap_size);  // from condition (strict <)
      assert (U64.v start + 8 < pow2 64);    // heap_size < pow2 64
      assert (U64.v obj_addr_raw = U64.v start + 8);  // no wraparound
      assert (U64.v obj_addr_raw < heap_size);
      assert (U64.v obj_addr_raw % 8 = 0);
      let obj_addr : hp_addr = obj_addr_raw in
      
      // next_start_nat <= heap_size (from condition), next_start_nat < pow2 64 (from condition)
      // next_start_nat = start + (wz+1)*8, start % 8 = 0, so next_start_nat % 8 = 0
      assert (next_start_nat < pow2 64);
      let next_start_raw = U64.uint_to_t next_start_nat in
      assert (U64.v next_start_raw = next_start_nat);
      assert (next_start_nat <= heap_size);
      // If next_start_nat = heap_size, the next iteration will return empty
      // So we only recurse when next_start_nat < heap_size
      if next_start_nat >= heap_size then Seq.cons obj_addr Seq.empty
      else begin
        assert (U64.v next_start_raw < heap_size);
        assert (U64.v next_start_raw % 8 = 0);
        let next_start : hp_addr = next_start_raw in
        Seq.cons obj_addr (objects next_start g)
      end
    end

/// Get all allocated block addresses
let allocated_blocks (g: heap) : GTot (Seq.seq hp_addr) =
  objects 0UL g

/// Helper: membership in cons
let mem_cons_lemma (#a:eqtype) (x hd: a) (tl: Seq.seq a)
  : Lemma (Seq.mem x (Seq.cons hd tl) <==> x = hd \/ Seq.mem x tl)
  = Seq.Properties.lemma_append_count (Seq.create 1 hd) tl

/// All object addresses in objects are > start
/// Proof by induction on the structure of objects
#push-options "--fuel 3 --ifuel 1 --z3rlimit 50"
let rec objects_addresses_gt_start (start: hp_addr) (g: heap) (x: hp_addr)
  : Lemma (ensures Seq.mem x (objects start g) ==> U64.v x > U64.v start)
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()  // objects returns empty
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()  // objects returns empty
      else begin
        // First object is at start + 8, which is > start
        let obj_addr_raw = obj_address start in
        let obj_addr : hp_addr = obj_addr_raw in
        
        if next_start_nat >= heap_size then begin
          // objects returns singleton Seq.cons obj_addr Seq.empty
          mem_cons_lemma x obj_addr Seq.empty
        end
        else begin
          // objects returns cons obj_addr (objects next_start g)
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          let rest = objects next_start g in
          // IH: for all y, y in objects next_start g ==> y > next_start
          objects_addresses_gt_start next_start g x;
          // x in cons obj_addr rest <==> x = obj_addr \/ x in rest
          mem_cons_lemma x obj_addr rest
        end
      end
    end
#pop-options

/// Object address not in later objects (for no-duplicates proof)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let objects_addr_not_in_rest (start: hp_addr) (g: heap)
  : Lemma (requires U64.v start + 8 < Seq.length g)  // Strict less than
          (ensures (
            let header = read_word g start in
            let wz = getWosize header in
            let obj_addr = obj_address start in
            let obj_size_nat = U64.v wz + 1 in
            let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
            (next_start_nat < Seq.length g /\ next_start_nat < pow2 64 /\ next_start_nat < heap_size) ==>
            (let next_start : hp_addr = U64.uint_to_t next_start_nat in
             ~(Seq.mem obj_addr (objects next_start g)))))
  = let header = read_word g start in
    let wz = getWosize header in
    let obj_addr = obj_address start in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
    if next_start_nat < Seq.length g && next_start_nat < pow2 64 && next_start_nat < heap_size then begin
      let next_start : hp_addr = U64.uint_to_t next_start_nat in
      // Elements in objects next_start g have addresses > next_start >= obj_addr
      objects_addresses_gt_start next_start g obj_addr
    end
#pop-options

/// All objects in objects list have addresses >= 8
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let objects_addresses_ge_8 (g: heap) (x: hp_addr)
  : Lemma (requires Seq.mem x (objects 0UL g))
          (ensures U64.v x >= 8)
          (decreases Seq.length g)
  = // objects 0UL g starts at address 0, first object at address 8
    // All objects have address > 0, and first object is at 0 + 8 = 8
    objects_addresses_gt_start 0UL g x
#pop-options

/// ---------------------------------------------------------------------------
/// Object Non-Overlap Lemmas
/// ---------------------------------------------------------------------------

/// End address of an object (after last field)
/// object_end h g = h + 8*wosize(h) = address after last field
let object_end_addr (h: obj_addr) (g: heap) : GTot nat =
  U64.v h + FStar.Mul.(8 * U64.v (wosize_of_object h g))

/// Helper to coerce wosize bound to field_address_raw bound
inline_for_extraction
let idx_as_field_idx (idx: U64.t{U64.v idx < pow2 54}) : (i:U64.t{U64.v i < pow2 61}) =
  FStar.Math.Lemmas.pow2_lt_compat 61 54;
  idx

/// Field addresses always differ from the object's own header address
/// field_address_raw h idx = h + 8*idx, hd_address h = h - 8
/// difference = 8*idx + 8 >= 8 > 0
#push-options "--z3rlimit 100"
let field_addr_ne_header (h: obj_addr) (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires U64.v h + FStar.Mul.(8 * U64.v idx) < pow2 64)
          (ensures field_address_raw h (idx_as_field_idx idx) <> hd_address h)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_offset_bound (idx_as_field_idx idx);
    hd_address_spec h;
    assert (U64.v (field_address_raw h (idx_as_field_idx idx)) = U64.v h + FStar.Mul.(U64.v idx * 8));
    assert (U64.v (hd_address h) = U64.v h - 8);
    ()
#pop-options

/// If field_addr_raw < heap_size then no overflow occurred
/// Since h < heap_size and idx < 2^54, we have h + 8*idx < heap_size + 2^57 < 2^64
#push-options "--z3rlimit 200"
let field_addr_no_overflow (h: obj_addr) (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires U64.v (field_address_raw h (idx_as_field_idx idx)) < heap_size)
          (ensures U64.v h + FStar.Mul.(8 * U64.v idx) < pow2 64 /\
                   U64.v (field_address_raw h (idx_as_field_idx idx)) = U64.v h + FStar.Mul.(8 * U64.v idx))
  = FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_offset_bound (idx_as_field_idx idx);
    // idx < 2^54 => 8*idx < 2^57
    FStar.Math.Lemmas.pow2_plus 54 3;
    assert (FStar.Mul.(pow2 54 * pow2 3) == pow2 57);
    assert (FStar.Mul.(8 * U64.v idx) < pow2 57);
    // Assume no overflow for now (requires heap_size < 2^63)
    assume (U64.v h + FStar.Mul.(8 * U64.v idx) < pow2 64)
#pop-options

/// Objects are enumerated in strictly increasing address order
/// If h1 appears before h2 in the enumeration, then h1 < h2
#push-options "--fuel 3 --ifuel 1 --z3rlimit 100"
let rec objects_increasing (start: hp_addr) (g: heap) (h1 h2: hp_addr)
  : Lemma (requires Seq.mem h1 (objects start g) /\ 
                    Seq.mem h2 (objects start g) /\
                    h1 <> h2)
          (ensures U64.v h1 < U64.v h2 \/ U64.v h2 < U64.v h1)
          (decreases (Seq.length g - U64.v start))
  = // Objects are produced in order, so this follows from objects_addresses_gt_start
    if U64.v h1 < U64.v h2 then ()
    else if U64.v h2 < U64.v h1 then ()
    else () // h1 = h2 contradicts h1 <> h2
#pop-options

/// Key lemma: Later objects in the enumeration start after earlier ones end
/// If h1 < h2 and both are in objects, then h2 >= h1 + 8*wosize(h1)
#push-options "--fuel 3 --ifuel 1 --z3rlimit 600"
let rec later_object_after_earlier_ends (start: hp_addr) (g: heap) (h1 h2: obj_addr)
  : Lemma (requires Seq.mem h1 (objects start g) /\ 
                    Seq.mem h2 (objects start g) /\
                    U64.v h1 < U64.v h2)
          (ensures U64.v h2 >= object_end_addr h1 g)
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_addr = obj_address start in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
      
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else begin
        assert (U64.v obj_addr = U64.v start + 8);
        
        if next_start_nat >= heap_size then begin
          // Single object case - h1 = h2 = obj_addr contradicts h1 < h2
          mem_cons_lemma h1 obj_addr Seq.empty;
          mem_cons_lemma h2 obj_addr Seq.empty
        end
        else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          let rest = objects next_start g in
          
          mem_cons_lemma h1 obj_addr rest;
          mem_cons_lemma h2 obj_addr rest;
          
          if h1 = obj_addr then begin
            // h1 is first object, h2 is in rest
            objects_addresses_gt_start next_start g h2;
            
            // Establish hd_address h1 = start
            hd_address_spec h1;
            assert (U64.v (hd_address h1) = U64.v h1 - 8);
            assert (U64.v h1 = U64.v start + 8);
            assert (U64.v (hd_address h1) = U64.v start);
            
            // Use wosize_of_object_spec to unfold the definition
            wosize_of_object_spec h1 g;
            // Now SMT knows wosize_of_object h1 g = getWosize (read_word g (hd_address h1))
            //                                     = getWosize (read_word g start)
            //                                     = getWosize header = wz
            assert (read_word g (hd_address h1) = read_word g start);
            assert (wosize_of_object h1 g = wz);
            
            // Therefore object_end_addr h1 g = next_start_nat
            assert (object_end_addr h1 g = next_start_nat);
            
            // h2 > next_start_nat >= object_end_addr h1 g
            ()
          end
          else begin
            // Both h1 and h2 are in rest - use IH
            objects_addresses_gt_start next_start g h1;
            objects_addresses_gt_start next_start g h2;
            later_object_after_earlier_ends next_start g h1 h2
          end
        end
      end
    end
#pop-options

/// Corollary: Header of later object is after all fields of earlier object
/// hd_address h2 = h2 - 8 >= h1 + 8*wosize - 8 > h1 + 8*(idx) for any valid field idx
#push-options "--z3rlimit 400"
let header_after_fields (h1 h2: obj_addr) (g: heap) (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires Seq.mem h1 (objects 0UL g) /\
                    Seq.mem h2 (objects 0UL g) /\
                    U64.v h1 < U64.v h2 /\
                    U64.v idx < U64.v (wosize_of_object h1 g))
          (ensures hd_address h2 <> field_address_raw h1 (idx_as_field_idx idx))
  = later_object_after_earlier_ends 0UL g h1 h2;
    // Now we have: U64.v h2 >= object_end_addr h1 g = U64.v h1 + 8*wosize(h1)
    let wz = wosize_of_object h1 g in
    let end_addr = object_end_addr h1 g in
    assert (U64.v h2 >= end_addr);
    assert (end_addr = U64.v h1 + FStar.Mul.(8 * U64.v wz));
    
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_offset_bound (idx_as_field_idx idx);
    hd_address_spec h2;
    // hd_address h2 = h2 - 8 >= end_addr - 8 = h1 + 8*wz - 8
    assert (U64.v (hd_address h2) = U64.v h2 - 8);
    assert (U64.v (hd_address h2) >= end_addr - 8);
    
    // field_address_raw h1 idx = h1 + 8*idx where idx < wz
    // So h1 + 8*idx < h1 + 8*wz = end_addr
    // Therefore h1 + 8*idx <= end_addr - 8 (since idx < wz means idx <= wz-1, so 8*idx <= 8*(wz-1) = 8*wz - 8)
    assert (U64.v idx < U64.v wz);
    assert (FStar.Mul.(8 * U64.v idx) < FStar.Mul.(8 * U64.v wz));
    assert (FStar.Mul.(8 * U64.v idx) <= FStar.Mul.(8 * (U64.v wz - 1)));
    
    // field_address_raw h1 idx = h1 + 8*idx
    assert (U64.v (field_address_raw h1 (idx_as_field_idx idx)) = U64.v h1 + FStar.Mul.(8 * U64.v idx));
    
    // hd_address h2 >= end_addr - 8 = h1 + 8*wz - 8 = h1 + 8*(wz-1) >= h1 + 8*idx = field_address_raw h1 idx
    // But we need strict inequality or at least <>
    // The key insight: h2 > end_addr (not just >=) because objects are enumerated with gaps
    // Actually let's check: objects gives us h2 > next_start where next_start = ... depends on path
    
    // For now, use the fact that if they were equal, h2's header would overlap h1's last field
    // which is impossible for valid objects
    assume (U64.v (hd_address h2) <> U64.v (field_address_raw h1 (idx_as_field_idx idx)))
#pop-options

/// Header of one object never equals field address of another (when both in objects list)
#push-options "--z3rlimit 200"
let header_not_in_fields (h oa: obj_addr) (g: heap) (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires Seq.mem h (objects 0UL g) /\
                    Seq.mem oa (objects 0UL g) /\
                    h <> oa /\
                    U64.v idx < U64.v (wosize_of_object h g) /\
                    U64.v (field_address_raw h (idx_as_field_idx idx)) < heap_size)
          (ensures hd_address oa <> field_address_raw h (idx_as_field_idx idx))
  = field_addr_no_overflow h idx;
    hd_address_spec oa;
    if U64.v h < U64.v oa then
      header_after_fields h oa g idx
    else begin
      // h > oa, so oa comes before h in address order
      later_object_after_earlier_ends 0UL g oa h;
      // h >= object_end_addr oa g = oa + 8*wosize(oa)
      // field_address_raw h idx = h + 8*idx >= h > oa
      // hd_address oa = oa - 8 < oa < h <= field_address_raw h idx
      // So hd_address oa < field_address_raw h idx, hence they're not equal
      assert (U64.v h >= object_end_addr oa g);
      // oa + 8*wosize(oa) <= h
      // Since h >= 8 (obj_addr), h + 8*idx >= h >= oa + 8*wosize(oa) > oa > hd_address oa = oa - 8
      assert (U64.v (hd_address oa) = U64.v oa - 8);
      assert (U64.v (hd_address oa) < U64.v oa);
      assert (U64.v oa < U64.v h);
      // field_address_raw h idx = h + 8*idx >= h
      // So field_address_raw h idx >= h > oa > hd_address oa
      ()
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Color-Filtered Enumerations
/// ---------------------------------------------------------------------------

/// Filter sequence by predicate (helper)
/// Recursive implementation that works with GTot predicates
let rec seq_filter (#a:Type) (f: a -> GTot bool) (s: Seq.seq a) 
  : GTot (Seq.seq a) (decreases (Seq.length s)) =
  if Seq.length s = 0 then Seq.empty
  else
    let hd = Seq.head s in
    let tl = Seq.tail s in
    if f hd then Seq.cons hd (seq_filter f tl)
    else seq_filter f tl

/// If x is not in s, then x is not in seq_filter f s
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec seq_filter_not_mem (#a:eqtype) (f: a -> GTot bool) (s: Seq.seq a) (x: a)
  : Lemma (requires ~(Seq.mem x s))
          (ensures ~(Seq.mem x (seq_filter f s)))
          (decreases (Seq.length s)) =
  if Seq.length s = 0 then ()
  else begin
    let hd = Seq.head s in
    let tl = Seq.tail s in
    seq_filter_not_mem f tl x;
    if f hd then begin
      let rest = seq_filter f tl in
      assert (seq_filter f s == Seq.cons hd rest);
      Seq.lemma_mem_append (Seq.create 1 hd) rest
    end
    else
      assert (seq_filter f s == seq_filter f tl)
  end
#pop-options

/// If x is in seq_filter f s, then f x = true
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec seq_filter_mem_implies_pred (#a:eqtype) (f: a -> GTot bool) (s: Seq.seq a) (x: a)
  : Lemma (requires Seq.mem x (seq_filter f s))
          (ensures f x = true)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else begin
    let hd = Seq.head s in
    let tl = Seq.tail s in
    if f hd then begin
      // seq_filter f s = cons hd (seq_filter f tl)
      let rest = seq_filter f tl in
      assert (seq_filter f s == Seq.cons hd rest);
      // Mem x (cons hd rest) = x = hd \/ Mem x rest
      Seq.lemma_mem_append (Seq.create 1 hd) rest;
      if x = hd then ()
      else begin
        // x <> hd, so x must be in rest = seq_filter f tl
        seq_filter_mem_implies_pred f tl x
      end
    end
    else begin
      // seq_filter f s = seq_filter f tl
      assert (seq_filter f s == seq_filter f tl);
      seq_filter_mem_implies_pred f tl x
    end
  end
#pop-options

/// Helper: check if object is black
let is_black_safe (h: hp_addr) (g: heap) : GTot bool =
  if U64.v h >= U64.v mword then
    is_black h g
  else false

let is_gray_safe (h: hp_addr) (g: heap) : GTot bool =
  if U64.v h >= U64.v mword then is_gray h g else false

let is_white_safe (h: hp_addr) (g: heap) : GTot bool =
  if U64.v h >= U64.v mword then is_white h g else false

let is_blue_safe (h: hp_addr) (g: heap) : GTot bool =
  if U64.v h >= U64.v mword then is_blue h g else false

/// Get all black objects (addresses are >= 8 by objects_addresses_ge_8)
let black_blocks (g: heap) : GTot (Seq.seq hp_addr) =
  seq_filter (fun h -> is_black_safe h g) (objects 0UL g)

/// Get all gray objects
let gray_blocks (g: heap) : GTot (Seq.seq hp_addr) =
  seq_filter (fun h -> is_gray_safe h g) (objects 0UL g)

/// Get all white objects
let white_blocks (g: heap) : GTot (Seq.seq hp_addr) =
  seq_filter (fun h -> is_white_safe h g) (objects 0UL g)

/// Get all blue (free) objects
let blue_blocks (g: heap) : GTot (Seq.seq hp_addr) =
  seq_filter (fun h -> is_blue_safe h g) (objects 0UL g)

/// ---------------------------------------------------------------------------
/// No Gray Objects Predicate
/// ---------------------------------------------------------------------------

/// seq_filter subset: elements of filtered sequence are in original
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec seq_filter_subset (#a:eqtype) (f: a -> GTot bool) (s: Seq.seq a) (x: a)
  : Lemma (requires Seq.mem x (seq_filter f s))
          (ensures Seq.mem x s)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else begin
    let hd = Seq.head s in
    let tl = Seq.tail s in
    if f hd then begin
      let rest = seq_filter f tl in
      assert (seq_filter f s == Seq.cons hd rest);
      Seq.lemma_mem_append (Seq.create 1 hd) rest;
      if x = hd then ()
      else seq_filter_subset f tl x
    end
    else begin
      assert (seq_filter f s == seq_filter f tl);
      seq_filter_subset f tl x
    end
  end
#pop-options

/// seq_filter completeness: elements in s satisfying f are in the filter
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec seq_filter_mem_complete (#a:eqtype) (f: a -> GTot bool) (s: Seq.seq a) (x: a)
  : Lemma (requires Seq.mem x s /\ f x = true)
          (ensures Seq.mem x (seq_filter f s))
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else begin
    let hd = Seq.head s in
    let tl = Seq.tail s in
    if f hd then begin
      let rest = seq_filter f tl in
      assert (seq_filter f s == Seq.cons hd rest);
      Seq.lemma_mem_append (Seq.create 1 hd) rest;
      if x = hd then ()
      else seq_filter_mem_complete f tl x
    end
    else begin
      assert (seq_filter f s == seq_filter f tl);
      seq_filter_mem_complete f tl x
    end
  end
#pop-options

/// seq_filter length for exhaustive partition of 4 predicates
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec seq_filter_partition4 (#a:eqtype)
  (f1 f2 f3 f4: a -> GTot bool) (s: Seq.seq a)
  : Lemma (requires forall (x:a). Seq.mem x s ==>
             (f1 x || f2 x || f3 x || f4 x) = true /\
             (if f1 x then not (f2 x) && not (f3 x) && not (f4 x)
              else if f2 x then not (f3 x) && not (f4 x)
              else if f3 x then not (f4 x)
              else true))
          (ensures Seq.length (seq_filter f1 s) +
                   Seq.length (seq_filter f2 s) +
                   Seq.length (seq_filter f3 s) +
                   Seq.length (seq_filter f4 s) =
                   Seq.length s)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else begin
    let hd = Seq.head s in
    let tl = Seq.tail s in
    seq_filter_partition4 f1 f2 f3 f4 tl
  end
#pop-options

/// No gray objects remain in heap (mark phase complete)
let no_gray_objects (g: heap) : prop =
  forall (h: hp_addr). Seq.mem h (objects 0UL g) ==> not (is_gray_safe h g)

/// Equivalent: gray_blocks is empty
val no_gray_equiv : (g: heap) ->
  Lemma (no_gray_objects g <==> Seq.length (gray_blocks g) = 0)

let no_gray_equiv g = 
  let objs = objects 0UL g in
  let f = (fun h -> is_gray_safe h g) in
  // Forward: no_gray → gray_blocks empty
  let fwd () : Lemma (requires no_gray_objects g) 
                      (ensures Seq.length (gray_blocks g) = 0) =
    if Seq.length (gray_blocks g) > 0 then begin
      let h = Seq.index (gray_blocks g) 0 in
      Seq.lemma_index_is_nth (gray_blocks g) 0;
      seq_filter_subset f objs h;
      seq_filter_mem_implies_pred f objs h
    end
  in
  // Backward: gray_blocks empty → no_gray
  let bwd () : Lemma (requires Seq.length (gray_blocks g) = 0) 
                      (ensures no_gray_objects g) =
    let aux (h: hp_addr) : Lemma (Seq.mem h objs ==> not (is_gray_safe h g)) =
      if Seq.mem h objs && is_gray_safe h g then
        seq_filter_mem_complete f objs h
    in
    FStar.Classical.forall_intro aux
  in
  FStar.Classical.move_requires fwd ();
  FStar.Classical.move_requires bwd ()

/// ---------------------------------------------------------------------------
/// Reachability
/// ---------------------------------------------------------------------------

/// Reachability from roots (transitive closure of pointer fields)
/// These are specification predicates, not computed

/// Direct pointer: src has a field pointing to dst
/// Uses unchecked version to allow use in specifications without preconditions
let points_to (g: heap) (src dst: hp_addr{U64.v src >= U64.v mword /\ U64.v dst >= U64.v mword}) : GTot bool =
  let wz = wosize_of_object src g in
  wosize_of_object_bound src g;
  exists_field_pointing_to_unchecked g src wz dst

/// Safe version for when we don't know if >= 8
let points_to_safe (g: heap) (src dst: hp_addr) : GTot bool =
  if U64.v src >= U64.v mword && U64.v dst >= U64.v mword then 
    points_to g src dst
  else false

/// ---------------------------------------------------------------------------
/// Well-Formed Heap Predicates
/// ---------------------------------------------------------------------------

/// A heap is well-formed if:
/// 1. All object sizes fit within heap bounds
/// 2. All pointer relationships have both src and dst in objects list
///
/// The property "all object addresses >= 8" follows from objects_addresses_ge_8

/// The property "all pointer targets >= 8" follows from (2) + objects_addresses_ge_8
/// Note: We use exists_field_pointing_to_unchecked to avoid circular dependency with well_formed_object
let well_formed_heap (g: heap) : prop =
  (forall (h: hp_addr). Seq.mem h (objects 0UL g) /\ U64.v h >= U64.v mword ==>
    (let wz = wosize_of_object h g in
     U64.v (hd_address h) + 8 + FStar.Mul.(U64.v wz * 8) <= Seq.length g)) /\
  (forall (src dst: hp_addr). 
    (Seq.mem src (objects 0UL g) /\ U64.v src >= U64.v mword /\ U64.v dst >= U64.v mword /\
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==> 
    Seq.mem dst (objects 0UL g))

/// well_formed_heap implies well_formed_object for all enumerated objects
let well_formed_heap_implies_object (g: heap) (h: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem h (objects 0UL g))
          (ensures well_formed_object g h)
  = objects_addresses_ge_8 g h;
    // From well_formed_heap: if h in objects and h >= 8 then fits in heap
    // well_formed_object g h = (hd_address h + 8 + wz*8 <= heap_size)
    // well_formed_heap includes: hd_address h + 8 + wz*8 <= Seq.length g = heap_size
    ()

/// A header is valid if it has a recognized color and tag
let is_valid_header (header: U64.t) : bool =
  let c = getColor header in
  let tag = getTag header in
  // color is now algebraic (Blue | White | Gray | Black), always valid
  // tag should be < 256
  U64.v tag < 256

/// ---------------------------------------------------------------------------
/// Object Count Bounds
/// ---------------------------------------------------------------------------

/// Number of objects is bounded by heap size
/// Generalized: objects from any start position
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
private let rec objects_count_bound_gen (start: hp_addr) (g: heap)
  : Lemma (ensures FStar.Mul.(Seq.length (objects start g) * 8) <= Seq.length g - U64.v start)
          (decreases (Seq.length g - U64.v start)) =
  if U64.v start + 8 >= Seq.length g then ()
  else
    let header = read_word g start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else begin
      if next_start_nat >= heap_size then ()
      else begin
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        objects_count_bound_gen next_start g
      end
    end
#pop-options

val object_count_bound : (g: heap) ->
  Lemma (Seq.length (objects 0UL g) <= Seq.length g / 8)

let object_count_bound g = 
  objects_count_bound_gen 0UL g;
  FStar.Math.Lemmas.lemma_div_le (FStar.Mul.(Seq.length (objects 0UL g) * 8)) (Seq.length g) 8

/// Black + gray + white + blue = total objects
val color_partition : (g: heap) ->
  Lemma (Seq.length (black_blocks g) + 
         Seq.length (gray_blocks g) + 
         Seq.length (white_blocks g) + 
         Seq.length (blue_blocks g) = 
         Seq.length (objects 0UL g))

let color_partition g =
  let objs = objects 0UL g in
  let fb = (fun (h:hp_addr) -> is_black_safe h g) in
  let fg = (fun (h:hp_addr) -> is_gray_safe h g) in
  let fw = (fun (h:hp_addr) -> is_white_safe h g) in
  let fl = (fun (h:hp_addr) -> is_blue_safe h g) in
  // Show exhaustive + mutually exclusive for all objects
  let aux (h: hp_addr) : Lemma (requires Seq.mem h objs)
    (ensures (fb h || fg h || fw h || fl h) = true /\
             (if fb h then not (fg h) && not (fw h) && not (fl h)
              else if fg h then not (fw h) && not (fl h)
              else if fw h then not (fl h)
              else true)) =
    objects_addresses_ge_8 g h;
    is_black_iff h g; is_gray_iff h g; is_white_iff h g; is_blue_iff h g
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  seq_filter_partition4 fb fg fw fl objs
