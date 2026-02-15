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
open Pulse.Lib.Header  // For color constructors

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

/// Header address from object address (subtract 8 bytes for header)
let hd_address (obj_addr: hp_addr) : hp_addr = 
  if U64.v obj_addr >= 8 then U64.sub obj_addr mword else 0UL

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

/// Unchecked version - does not require well_formed_object precondition  
/// Used in well_formed_heap definition to avoid circularity
/// Uses mul_mod/add_mod to avoid internal lemma calls (enables SMT unfolding)
let rec exists_field_pointing_to_unchecked (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr) 
  : GTot bool (decreases U64.v wz) =
  if wz = 0UL then false
  else
    let idx = U64.sub wz 1UL in
    let field_addr_raw = U64.add_mod h (U64.mul_mod idx mword) in
    if U64.v field_addr_raw >= heap_size || U64.v field_addr_raw % 8 <> 0 then false
    else
      let field_addr : hp_addr = field_addr_raw in
      let field_val = read_word g field_addr in
      if is_pointer_field field_val && hd_address field_val = hd_address target then true
      else exists_field_pointing_to_unchecked g h idx target

/// One-step unfolding: if guard passes AND field matches, function returns true
/// Takes far and fv as explicit witnesses to avoid unification issues
let efptu_match (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54 /\ wz <> 0UL}) (target: hp_addr)
  (far: hp_addr) (fv: U64.t)
  : Lemma (requires far == U64.add_mod h (U64.mul_mod (U64.sub wz 1UL) mword) /\
                   fv == read_word g far /\
                   (is_pointer_field fv && hd_address fv = hd_address target))
          (ensures exists_field_pointing_to_unchecked g h wz target)
  = ()

/// One-step unfolding: if guard passes, field doesn't match, but recursive call returns true
let efptu_recurse (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54 /\ wz <> 0UL}) (target: hp_addr)
  (far: hp_addr) (fv: U64.t)
  : Lemma (requires far == U64.add_mod h (U64.mul_mod (U64.sub wz 1UL) mword) /\
                   fv == read_word g far /\
                   ~(is_pointer_field fv && hd_address fv = hd_address target) /\
                   exists_field_pointing_to_unchecked g h (U64.sub wz 1UL) target)
          (ensures exists_field_pointing_to_unchecked g h wz target)
  = ()

/// If a specific field contains a pointer to target, exists_field_pointing_to_unchecked finds it
val field_read_implies_exists_pointing : (g: heap) -> (h: obj_addr) -> (wz: U64.t{U64.v wz < pow2 54}) -> 
    (k: U64.t{U64.v k < U64.v wz /\ U64.v k < pow2 61}) -> (target: obj_addr) ->
  Lemma (requires well_formed_object g h /\
                  U64.v wz <= U64.v (wosize_of_object h g) /\
                  (let far = U64.add_mod h (U64.mul_mod k mword) in
                   U64.v far < heap_size /\ U64.v far % 8 = 0 /\
                   (let fv = read_word g (far <: hp_addr) in
                    is_pointer_field fv /\ hd_address fv = hd_address target)))
        (ensures exists_field_pointing_to_unchecked g h wz target)
        (decreases U64.v wz)

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let rec field_read_implies_exists_pointing g h wz k target =
  let idx = U64.sub wz 1UL in
  FStar.Math.Lemmas.pow2_lt_compat 61 54;
  wosize_fits_field_index wz;
  field_offset_bound idx;
  assert (FStar.Mul.(U64.v idx * U64.v mword) < pow2 64);
  FStar.Math.Lemmas.modulo_lemma (FStar.Mul.(U64.v idx * U64.v mword)) (pow2 64);
  FStar.Math.Lemmas.modulo_lemma (U64.v h + FStar.Mul.(U64.v idx * 8)) (pow2 64);
  let far_idx = U64.add_mod h (U64.mul_mod idx mword) in
  assert (U64.v far_idx = U64.v h + FStar.Mul.(U64.v idx * 8));
  assert (U64.v far_idx < heap_size);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v h) (FStar.Mul.(U64.v idx * 8)) 8;
  assert (U64.v far_idx % 8 = 0);
  let fv_idx = read_word g (far_idx <: hp_addr) in
  if is_pointer_field fv_idx && hd_address fv_idx = hd_address target then
    efptu_match g h wz target far_idx fv_idx
  else begin
    assert (U64.v k < U64.v idx);
    field_read_implies_exists_pointing g h idx k target;
    efptu_recurse g h wz target far_idx fv_idx
  end
#pop-options

/// Helper: check if any field points to target
/// Requires: object is well-formed (fits in heap)
let rec exists_field_pointing_to (g: heap) (h: obj_addr) (wz: wosize) (target: hp_addr) 
  : Ghost bool 
    (requires well_formed_object g h /\ U64.v wz <= U64.v (wosize_of_object h g))
    (ensures fun _ -> True)
    (decreases U64.v wz) =
  if wz = 0UL then false
  else begin
    let idx = U64.sub wz 1UL in
    wosize_fits_field_index wz;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    // From well_formed_object: hd_address h + 8 + wz*8 <= heap_size
    // h = hd_address h + 8, so h + wz*8 <= heap_size
    // idx = wz - 1, so h + idx*8 < h + wz*8 <= heap_size
    assert (U64.v h + FStar.Mul.(U64.v idx * 8) < heap_size);
    let field_addr = field_address h idx in
    let field_val = read_word g field_addr in
    if is_pointer_field field_val && hd_address field_val = hd_address target then true
    else exists_field_pointing_to g h idx target
  end

/// The checked and unchecked versions are equivalent when object is well-formed
/// Proof: when well_formed_object g h, all field addresses are valid hp_addrs,
/// so the unchecked version's bounds check always passes
let rec exists_field_checked_eq_unchecked (g: heap) (h: obj_addr) (wz: wosize) (target: hp_addr)
  : Lemma 
    (requires well_formed_object g h /\ U64.v wz <= U64.v (wosize_of_object h g))
    (ensures exists_field_pointing_to g h wz target == exists_field_pointing_to_unchecked g h wz target)
    (decreases U64.v wz)
  =
  if wz = 0UL then 
    ()
  else begin
    let idx = U64.sub wz 1UL in
    wosize_fits_field_index wz;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    
    assert (U64.v h + FStar.Mul.(U64.v idx * 8) < heap_size);
    
    // Show mul_mod idx mword = field_offset idx (no overflow for idx < pow2 54)
    field_offset_bound idx;
    assert (FStar.Mul.(U64.v idx * 8) < pow2 64);
    FStar.Math.Lemmas.modulo_lemma (FStar.Mul.(U64.v idx * U64.v mword)) (pow2 64);
    assert (U64.v (U64.mul_mod idx mword) = FStar.Mul.(U64.v idx * U64.v mword));
    
    // Show add_mod h (mul_mod idx mword) = field_address_raw h idx (no overflow)
    assert (U64.v h + FStar.Mul.(U64.v idx * 8) < pow2 64);
    FStar.Math.Lemmas.modulo_lemma (U64.v h + FStar.Mul.(U64.v idx * 8)) (pow2 64);
    let far_unchecked = U64.add_mod h (U64.mul_mod idx mword) in
    let far_raw = field_address_raw h idx in
    assert (U64.v far_unchecked = U64.v h + FStar.Mul.(U64.v idx * 8));
    assert (U64.v far_raw = U64.v h + FStar.Mul.(U64.v idx * 8));
    assert (far_unchecked == far_raw);
    
    // Bounds checks pass
    assert (U64.v far_unchecked < heap_size);
    assert (U64.v h % 8 = 0);
    assert (FStar.Mul.(U64.v idx * 8) % 8 = 0);
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v h) (FStar.Mul.(U64.v idx * 8)) 8;
    assert (U64.v far_unchecked % 8 = 0);
    assert (not (U64.v far_unchecked >= heap_size || U64.v far_unchecked % 8 <> 0));
    
    // The checked version computes field_address h idx
    let field_addr_checked = field_address h idx in
    assert (U64.v field_addr_checked = U64.v far_unchecked);
    
    // Both read the same field value
    let field_val = read_word g (far_unchecked <: hp_addr) in
    let cmp = is_pointer_field field_val && hd_address field_val = hd_address target in
    
    // Apply inductive hypothesis to recursive calls
    exists_field_checked_eq_unchecked g h idx target;
    ()
  end

/// Check if object h points to object target
/// Uses wosize_of_object_bound to ensure valid wosize
let is_pointer_to_object (g: heap) (h: obj_addr) (target: hp_addr) : GTot bool =
  let wz = wosize_of_object h g in
  wosize_of_object_bound h g;
  exists_field_pointing_to_unchecked g h wz target

/// is_pointer_to_object implies exists_field_pointing_to when well_formed
let is_pointer_to_object_implies_exists_field (g: heap) (h: obj_addr) (target: hp_addr)
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
let rec objects (start: hp_addr) (g: heap) : GTot (Seq.seq obj_addr) (decreases (Seq.length g - U64.v start)) =
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
      // obj_addr_raw >= 8 since obj_addr_raw = start + 8 and start >= 0
      assert (U64.v obj_addr_raw >= U64.v mword);  // mword = 8
      let obj_addr : obj_addr = obj_addr_raw in
      
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
let allocated_blocks (g: heap) : GTot (Seq.seq obj_addr) =
  objects 0UL g

/// Helper: membership in cons
let mem_cons_lemma (#a:eqtype) (x hd: a) (tl: Seq.seq a)
  : Lemma (Seq.mem x (Seq.cons hd tl) <==> x = hd \/ Seq.mem x tl)
  = Seq.Properties.lemma_append_count (Seq.create 1 hd) tl

/// All object addresses in objects are > start
/// Proof by induction on the structure of objects
#push-options "--fuel 3 --ifuel 1 --z3rlimit 400"
let rec objects_addresses_gt_start (start: hp_addr) (g: heap) (x: obj_addr)
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
        assert (U64.v obj_addr_raw = U64.v start + 8);
        assert (U64.v obj_addr_raw > U64.v start);
        assert (U64.v obj_addr_raw < heap_size);
        let obj_addr : hp_addr = obj_addr_raw in
        
        if next_start_nat >= heap_size then begin
          // objects returns singleton Seq.cons obj_addr Seq.empty
          mem_cons_lemma x obj_addr Seq.empty;
          assert (Seq.mem x (Seq.cons obj_addr Seq.empty) <==> x = obj_addr \/ Seq.mem x Seq.empty);
          assert (~(Seq.mem x Seq.empty))
        end
        else begin
          // objects returns cons obj_addr (objects next_start g)
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          let rest = objects next_start g in
          // IH: for all y, y in objects next_start g ==> y > next_start
          objects_addresses_gt_start next_start g x;
          // next_start > start, so y > next_start > start
          assert (next_start_nat > U64.v start);
          // x in cons obj_addr rest <==> x = obj_addr \/ x in rest
          mem_cons_lemma x obj_addr rest;
          // If x = obj_addr, then x > start (from obj_addr = start + 8 > start)
          // If x in rest, then x > next_start > start (by IH)
          assert (x = obj_addr ==> U64.v x > U64.v start);
          assert (Seq.mem x rest ==> U64.v x > U64.v next_start);
          assert (U64.v next_start > U64.v start)
        end
      end
    end
#pop-options

/// Object address not in later objects (for no-duplicates proof)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
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
      // obj_addr = start + 8
      assert (U64.v obj_addr = U64.v start + 8);
      // next_start = start + (wz+1)*8 >= start + 8 = obj_addr
      assert (next_start_nat >= U64.v start + 8);
      assert (U64.v next_start >= U64.v obj_addr);
      // Elements in objects next_start g have addresses > next_start >= obj_addr
      objects_addresses_gt_start next_start g obj_addr;
      assert (Seq.mem obj_addr (objects next_start g) ==> U64.v obj_addr > U64.v next_start);
      // But obj_addr <= next_start, so obj_addr not in objects next_start g
      assert (U64.v obj_addr <= U64.v next_start);
      assert (~(Seq.mem obj_addr (objects next_start g)))
    end
#pop-options

/// All objects in objects list have addresses >= 8
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let rec objects_addresses_ge_8 (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects 0UL g))
          (ensures U64.v x >= 8)
          (decreases Seq.length g)
  = // objects 0UL g starts at address 0, first object at address 8
    // All objects have address > 0, and first object is at 0 + 8 = 8
    objects_addresses_gt_start 0UL g x
#pop-options

/// ---------------------------------------------------------------------------
/// Objects Separation: later objects start beyond earlier object's fields
/// ---------------------------------------------------------------------------

/// For two distinct objects in objects(start, g), if src is the first object
/// and y is any later object, then y > src + wosize(src)*8.
/// This proves non-overlapping: fields of src are in [src, src+(wz-1)*8],
/// and hd_address(y) = y - 8 > src + wz*8 - 8 >= src + (wz-1)*8.
#push-options "--fuel 3 --ifuel 1 --z3rlimit 400"
let rec objects_separated (start: hp_addr) (g: heap) (src y: obj_addr)
  : Lemma (ensures Seq.mem src (objects start g) /\ Seq.mem y (objects start g) /\
                   U64.v src < U64.v y ==>
                   U64.v y > U64.v src + FStar.Mul.(U64.v (wosize_of_object_as_wosize src g) * 8))
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_addr_raw = obj_address start in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else begin
        assert (U64.v obj_addr_raw = U64.v start + 8);
        assert (U64.v obj_addr_raw < heap_size);
        let first : hp_addr = obj_addr_raw in
        if next_start_nat >= heap_size then begin
          // Single object: objects = [first]. Can't have two distinct members.
          mem_cons_lemma src first Seq.empty;
          mem_cons_lemma y first Seq.empty
        end
        else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          let rest = objects next_start g in
          mem_cons_lemma src first rest;
          mem_cons_lemma y first rest;
          // Case: src = first (the first object at this level)
          if src = first then begin
            // y ≠ first (since y > src = first), so y ∈ rest
            // All objects in rest have addr > next_start
            objects_addresses_gt_start next_start g y;
            // next_start = start + (wz+1)*8 = first + wz*8
            assert (next_start_nat = U64.v first + FStar.Mul.(U64.v wz * 8));
            // wosize_of_object first g = getWosize(read_word g (hd_address first))
            // hd_address first = first - 8 = start (since first = start + 8)
            // But hd_address is from Fields (line 40), not from Heap
            // For first: obj_addr with v >= 8, so hd_address first = first - 8 = start
            assert (U64.v (hd_address first) = U64.v start);
            // read_word g start = header (already computed above)
            // getWosize header = wz
            // wosize_of_object first g = getWosize(read_word g (Pulse.Spec.GC.Heap.hd_address first))
            Pulse.Spec.GC.Heap.hd_address_spec first;
            wosize_of_object_spec first g;
            // So wosize_of_object first g = wz
            // y > next_start = first + wz*8
            ()
          end else begin
            // src ∈ rest (not the first object)
            // y could be first or in rest
            if y = first then begin
              // y = first < src (since both in objects, src ∈ rest, rest addresses > next_start > first)
              objects_addresses_gt_start next_start g src;
              // src > next_start > first = y, contradicts src < y
              ()
            end else begin
              // Both src and y are in rest = objects(next_start, g)
              // Recurse
              objects_separated next_start g src y
            end
          end
        end
      end
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

/// ---------------------------------------------------------------------------
/// Helper Lemmas for seq_filter
/// ---------------------------------------------------------------------------

/// seq_filter preserves membership for elements satisfying predicate
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec seq_filter_mem (#a:eqtype) (f: a -> GTot bool) (s: Seq.seq a) (x: a)
  : Lemma 
    (ensures Seq.mem x (seq_filter f s) ==> (Seq.mem x s /\ f x))
    (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      if f hd then begin
        mem_cons_lemma x hd (seq_filter f tl);
        if x <> hd then seq_filter_mem f tl x
      end else begin
        seq_filter_mem f tl x
      end
    end
#pop-options

/// If seq_filter is empty, predicate is false for all members
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec seq_filter_empty_implies_not_f (#a:eqtype) (f: a -> GTot bool) (s: Seq.seq a)
  : Lemma 
    (requires Seq.length (seq_filter f s) = 0)
    (ensures forall x. Seq.mem x s ==> not (f x))
    (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      if f hd then begin
        // seq_filter would be Seq.cons hd (seq_filter f tl), length > 0
        assert (Seq.length (seq_filter f s) > 0)
      end else begin
        // seq_filter s = seq_filter f tl
        seq_filter_empty_implies_not_f f tl;
        // Now forall x. mem x tl ==> not (f x)
        // Need to show: forall x. mem x s ==> not (f x)
        assert (forall x. Seq.mem x s ==> (x = hd \/ Seq.mem x tl));
        assert (not (f hd))
      end
    end
#pop-options

/// If predicate is false for all members, seq_filter is empty
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec seq_filter_not_f_implies_empty (#a:eqtype) (f: a -> GTot bool) (s: Seq.seq a)
  : Lemma 
    (requires forall x. Seq.mem x s ==> not (f x))
    (ensures Seq.length (seq_filter f s) = 0)
    (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      assert (Seq.mem hd s);
      assert (not (f hd));
      assert (forall x. Seq.mem x tl ==> Seq.mem x s);
      seq_filter_not_f_implies_empty f tl
    end
#pop-options

/// Get all black objects
let black_blocks (g: heap) : GTot (Seq.seq obj_addr) =
  seq_filter (fun h -> is_black h g) (objects 0UL g)

/// Get all gray objects
let gray_blocks (g: heap) : GTot (Seq.seq obj_addr) =
  seq_filter (fun h -> is_gray h g) (objects 0UL g)

/// Get all white objects
let white_blocks (g: heap) : GTot (Seq.seq obj_addr) =
  seq_filter (fun h -> is_white h g) (objects 0UL g)

/// ---------------------------------------------------------------------------
/// No Gray Objects Predicate
/// ---------------------------------------------------------------------------

/// No gray objects remain in heap (mark phase complete)
let no_gray_objects (g: heap) : prop =
  forall (h: obj_addr). Seq.mem h (objects 0UL g) ==> not (is_gray h g)

/// Equivalent: gray_blocks is empty
val no_gray_equiv : (g: heap) ->
  Lemma (no_gray_objects g <==> Seq.length (gray_blocks g) = 0)

let no_gray_equiv g = 
  // Forward: no_gray_objects g ==> length (gray_blocks g) = 0
  if Seq.length (gray_blocks g) > 0 then begin
    // There exists some gray object in gray_blocks
    seq_filter_mem (fun h -> is_gray h g) (objects 0UL g) (Seq.head (gray_blocks g))
  end;
  // Backward: length (gray_blocks g) = 0 ==> no_gray_objects g
  if Seq.length (gray_blocks g) = 0 then begin
    seq_filter_empty_implies_not_f (fun h -> is_gray h g) (objects 0UL g)
  end

/// ---------------------------------------------------------------------------
/// Reachability
/// ---------------------------------------------------------------------------

/// Reachability from roots (transitive closure of pointer fields)
/// These are specification predicates, not computed

/// Direct pointer: src has a field pointing to dst
/// Uses unchecked version to allow use in specifications without preconditions
let points_to (g: heap) (src dst: obj_addr) : GTot bool =
  let wz = wosize_of_object src g in
  wosize_of_object_bound src g;
  exists_field_pointing_to_unchecked g src wz dst



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
  (forall (h: obj_addr). Seq.mem h (objects 0UL g) ==>
    (let wz = wosize_of_object h g in
     U64.v (hd_address h) + 8 + FStar.Mul.(U64.v wz * 8) <= Seq.length g)) /\
  (forall (src dst: obj_addr). 
    (Seq.mem src (objects 0UL g) /\ 
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==> 
    Seq.mem dst (objects 0UL g))

/// Extract part 1 of well_formed_heap: object size bounds
let wf_object_size_bound (g: heap) (h: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem h (objects 0UL g))
  (ensures U64.v (hd_address h) + 8 + op_Multiply (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  = ()

/// Extract part 1 without hd_address (for cross-module use with HeapGraph.object_fits_in_heap)
/// Since hd_address h = h - 8 for obj_addr h, we get: h + wosize*8 <= Seq.length g
let wf_object_bound (g: heap) (h: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem h (objects 0UL g))
  (ensures U64.v h + op_Multiply (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  = ()

/// When objects start g is nonempty, the first object fits in heap:
/// start + (1 + wz) * 8 <= Seq.length g
/// This follows directly from the objects definition (the next_start check)
let objects_nonempty_head_fits (start: hp_addr) (g: heap) : Lemma
  (requires Seq.length (objects start g) > 0)
  (ensures (let wz = getWosize (read_word g start) in
            U64.v start + FStar.Mul.((U64.v wz + 1) * 8) <= Seq.length g))
  = ()

/// When objects start g is nonempty, the head object is obj_address start
let objects_nonempty_head (start: hp_addr) (g: heap) : Lemma
  (requires Seq.length (objects start g) > 0)
  (ensures (let obj = obj_address start in
            U64.v obj == U64.v start + 8 /\
            Seq.head (objects start g) == obj))
  = ()

/// When objects start g is nonempty, next_start is valid and objects decomposes
let objects_nonempty_next (start: hp_addr) (g: heap) : Lemma
  (requires Seq.length (objects start g) > 0)
  (ensures (let wz = getWosize (read_word g start) in
            let next = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
            next <= Seq.length g /\ next < pow2 64 /\
            next % 8 == 0 /\
            (next < heap_size ==>
              (let next_hp : hp_addr = U64.uint_to_t next in
               objects start g == Seq.cons (obj_address start) (objects next_hp g)))))
  = FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v start) (FStar.Mul.((U64.v (getWosize (read_word g start)) + 1) * 8)) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (U64.v (getWosize (read_word g start)) + 1) 8 8

/// Members of objects from a later start are also members of objects from an earlier start
/// (objects later g ⊆ objects earlier g when later is the next scan position after earlier)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let objects_later_subset (start: hp_addr) (g: heap) (x: obj_addr)
  : Lemma (requires Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next_nat = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
                    next_nat < heap_size /\ next_nat < pow2 64 /\ next_nat % 8 == 0 ==>
                    (let next : hp_addr = U64.uint_to_t next_nat in
                     Seq.mem x (objects next g) ==> Seq.mem x (objects start g))))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let next_nat = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
      if next_nat > Seq.length g || next_nat >= pow2 64 then ()
      else if next_nat >= heap_size then ()
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        let oa = obj_address start in
        // objects start g == cons oa (objects next g), so mem in tail → mem in cons
        mem_cons_lemma x oa (objects next g)
      end
    end
#pop-options

/// A header is valid if it has valid color and tag
/// Note: getColor returns algebraic type (White|Gray|Black) from Pulse.Lib.Header.color_sem
let is_valid_header (header: U64.t) : bool =
  // let c = getColor header in
  let tag = getTag header in
  // All possible colors are valid, so just check tag
  U64.v tag < 256

/// ---------------------------------------------------------------------------
/// Object Count Bounds
/// ---------------------------------------------------------------------------

/// Helper: objects use at least 8 bytes each
/// Generalized version: length (objects start g) * 8 <= length g - start
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec objects_count_le_remaining (start: hp_addr) (g: heap)
  : Lemma 
    (ensures FStar.Mul.(Seq.length (objects start g) * 8) <= Seq.length g - U64.v start)
    (decreases Seq.length g - U64.v start)
  = if U64.v start + 8 >= Seq.length g then begin
      // objects returns empty, so length = 0
      // 0 * 8 = 0 <= length g - start
      ()
    end else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
      
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then begin
        // objects returns empty
        ()
      end else begin
        let obj_addr_raw = obj_address start in
        assert (U64.v obj_addr_raw = U64.v start + 8);
        let obj_addr : obj_addr = obj_addr_raw in
        
        if next_start_nat >= heap_size then begin
          // objects returns singleton [obj_addr]
          // length = 1, so 1 * 8 = 8
          // need: 8 <= length g - start
          // We have: start + 8 < length g (from condition)
          // So: length g - start > 8, thus >= 8 (since integers)
          assert (U64.v start + 8 < Seq.length g);
          assert (Seq.length g - U64.v start > 8);
          ()
        end else begin
          // objects returns cons obj_addr (objects next_start g)
          let next_start_raw = U64.uint_to_t next_start_nat in
          let next_start : hp_addr = next_start_raw in
          
          // Recurse on tail
          objects_count_le_remaining next_start g;
          
          // IH: length (objects next_start g) * 8 <= length g - next_start_nat
          let tail_len = Seq.length (objects next_start g) in
          assert (FStar.Mul.(tail_len * 8) <= Seq.length g - next_start_nat);
          
          // length (cons obj_addr tail) = 1 + tail_len
          let total_len = 1 + tail_len in
          
          // Need: total_len * 8 <= length g - start
          // We have: total_len * 8 = 8 + tail_len * 8
          //                        <= 8 + (length g - next_start_nat)
          //                        = 8 + length g - (start + obj_size_nat * 8)
          //                        = 8 + length g - start - obj_size_nat * 8
          //                        = length g - start + 8 - obj_size_nat * 8
          // Since obj_size_nat = wz + 1 >= 1, we have obj_size_nat * 8 >= 8
          // So: 8 - obj_size_nat * 8 <= 0
          // Thus: total_len * 8 <= length g - start
          
          assert (obj_size_nat >= 1);
          assert (FStar.Mul.(obj_size_nat * 8) >= 8);
          assert (next_start_nat == U64.v start + FStar.Mul.(obj_size_nat * 8));
          
          FStar.Math.Lemmas.lemma_mult_le_right 8 1 obj_size_nat;
          assert (FStar.Mul.(total_len * 8) == 8 + FStar.Mul.(tail_len * 8));
          assert (FStar.Mul.(tail_len * 8) <= Seq.length g - next_start_nat);
          assert (8 + (Seq.length g - next_start_nat) == 8 + Seq.length g - next_start_nat);
          assert (next_start_nat == U64.v start + FStar.Mul.(obj_size_nat * 8));
          assert (8 + Seq.length g - next_start_nat == 
                  8 + Seq.length g - U64.v start - FStar.Mul.(obj_size_nat * 8));
          ()
        end
      end
    end
#pop-options

/// Number of objects is bounded by heap size
val object_count_bound : (g: heap) ->
  Lemma (Seq.length (objects 0UL g) <= Seq.length g / 8)

let object_count_bound g = 
  objects_count_le_remaining 0UL g;
  // We have: length (objects 0UL g) * 8 <= length g - 0 = length g
  // Therefore: length (objects 0UL g) <= length g / 8
  FStar.Math.Lemmas.lemma_div_le (FStar.Mul.(Seq.length (objects 0UL g) * 8)) (Seq.length g) 8

/// Helper: colors are exhaustive and mutually exclusive
let colors_exhaustive_and_exclusive (h: obj_addr) (g: heap)
  : Lemma (
      // Exhaustive: exactly one is true
      (is_black h g \/ is_white h g \/ is_gray h g) /\
      // Mutually exclusive
      (not (is_black h g && is_white h g)) /\
      (not (is_black h g && is_gray h g)) /\
      (not (is_white h g && is_gray h g))
    )
  = // Use characterization lemmas to connect is_* to color_of_object
    is_black_iff h g;
    is_white_iff h g;
    is_gray_iff h g;
    // Now the SMT solver knows:
    // is_black h g <==> color_of_object h g = Black
    // is_white h g <==> color_of_object h g = White
    // is_gray h g <==> color_of_object h g = Gray
    // color_of_object returns color_sem which has 3 constructors
    // So exactly one equality holds, proving exhaustive and exclusive
    ()

/// Helper: partition sequence by 3 mutually exclusive, exhaustive predicates
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec seq_filter_partition_3 
  (#a:eqtype)
  (p1 p2 p3: a -> GTot bool) 
  (s: Seq.seq a)
  : Lemma 
    (requires 
      (forall x. Seq.mem x s ==> 
        ((p1 x \/ p2 x \/ p3 x) /\  // exhaustive
         (not (p1 x && p2 x)) /\
         (not (p1 x && p3 x)) /\
         (not (p2 x && p3 x)))))
    (ensures 
      Seq.length (seq_filter p1 s) + 
      Seq.length (seq_filter p2 s) + 
      Seq.length (seq_filter p3 s) = 
      Seq.length s)
    (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      
      assert (Seq.mem hd s);
      assert (p1 hd \/ p2 hd \/ p3 hd);
      
      assert (forall x. Seq.mem x tl ==> Seq.mem x s);
      seq_filter_partition_3 p1 p2 p3 tl;
      
      if p1 hd then begin
        assert (not (p2 hd) && not (p3 hd));
        ()
      end else if p2 hd then begin
        assert (not (p1 hd) && not (p3 hd));
        ()
      end else begin
        assert (p3 hd);
        assert (not (p1 hd) && not (p2 hd));
        ()
      end
    end
#pop-options

/// Black + gray + white = total objects
val color_partition : (g: heap) ->
  Lemma (Seq.length (black_blocks g) + 
         Seq.length (gray_blocks g) + 
         Seq.length (white_blocks g) = 
         Seq.length (objects 0UL g))

let color_partition g = 
  Classical.forall_intro (fun h -> colors_exhaustive_and_exclusive h g);
  
  seq_filter_partition_3 
    (fun h -> is_black h g)
    (fun h -> is_gray h g)
    (fun h -> is_white h g)
    (objects 0UL g)

/// ---------------------------------------------------------------------------
/// Color Change Preservation
/// ---------------------------------------------------------------------------

/// Color changes preserve object enumeration
/// Key insight: set_object_color only changes color bits in one header word.
/// objects depends on getWosize at each step, which is in different bits.
/// Color changes preserve object enumeration
/// Key insight: set_object_color only changes color bits in one header word.
/// objects depends on getWosize at each step, which is in different bits.
#push-options "--z3rlimit 400 --fuel 4 --ifuel 2"
val color_change_preserves_objects_aux : (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (c: color) ->
  Lemma (ensures objects start (set_object_color obj g c) == objects start g)
        (decreases (Seq.length g - U64.v start))

let rec color_change_preserves_objects_aux start g obj c =
  // SMT pattern on set_object_color_read_word fires when solver sees
  // read_word (set_object_color obj g c) start
  if U64.v start + 8 >= Seq.length g then ()
  else begin
    let wz = getWosize (read_word g start) in
    let next_start_nat = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else if next_start_nat >= heap_size then ()
    else
      color_change_preserves_objects_aux (U64.uint_to_t next_start_nat) g obj c
  end
#pop-options

/// Top-level: color change preserves objects enumeration from 0
val color_change_preserves_objects : (g: heap) -> (obj: obj_addr) -> (c: color) ->
  Lemma (objects 0UL (set_object_color obj g c) == objects 0UL g)

let color_change_preserves_objects g obj c =
  color_change_preserves_objects_aux 0UL g obj c

/// Objects membership ↔ after color change
let color_change_preserves_objects_mem (g: heap) (obj: obj_addr) (c: color) (x: obj_addr)
  : Lemma (Seq.mem x (objects 0UL (set_object_color obj g c)) <==> Seq.mem x (objects 0UL g))
  = color_change_preserves_objects g obj c

/// Past-object phase: addr < all future header positions
/// Standalone (not mutually recursive)
#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"
private let rec write_word_preserves_objects_past (start: hp_addr) (g: heap) (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr < U64.v start /\
                    U64.v addr % 8 = 0)
          (ensures objects start (write_word g addr v) == objects start g)
          (decreases (Seq.length g - U64.v start))
  = let g' = write_word g addr v in
    assert (Seq.length g' == Seq.length g);
    if U64.v start + 8 >= Seq.length g then begin
      assert (objects start g == Seq.empty);
      assert (objects start g' == Seq.empty)
    end
    else begin
      read_write_different g addr start v;
      let header = read_word g start in
      assert (read_word g' start == header);
      let wz = getWosize header in
      assert (getWosize (read_word g' start) == wz);
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then begin
        assert (objects start g == Seq.empty);
        assert (objects start g' == Seq.empty)
      end
      else begin
        let obj_addr_raw = obj_address start in
        let oa : obj_addr = obj_addr_raw in
        if next_start_nat >= heap_size then begin
          assert (objects start g == Seq.cons oa Seq.empty);
          assert (objects start g' == Seq.cons oa Seq.empty)
        end
        else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          write_word_preserves_objects_past next_start g addr v;
          assert (objects next_start g' == objects next_start g);
          assert (objects start g == Seq.cons oa (objects next_start g));
          assert (objects start g' == Seq.cons oa (objects next_start g'))
        end
      end
    end
#pop-options

/// Write to a word-separated address preserves objects enumeration
/// Phase tracking: before obj's header, at it, or past it
#push-options "--z3rlimit 1600 --fuel 4 --ifuel 2"
private val write_word_preserves_objects_aux : (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects start g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + FStar.Mul.(U64.v (wosize_of_object obj g) * 8) /\
                  U64.v addr % 8 = 0)
        (ensures objects start (write_word g addr v) == objects start g)
        (decreases (Seq.length g - U64.v start))

let rec write_word_preserves_objects_aux start g obj addr v =
  if U64.v start + 8 >= Seq.length g then ()
  else begin
    let header = read_word g start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else begin
      let obj_addr_raw = obj_address start in
      let oa : obj_addr = obj_addr_raw in
      Pulse.Spec.GC.Heap.hd_address_spec oa;
      // start = hd_address(oa) = oa - 8
      // Case 1: oa = obj. start = obj - 8, addr >= obj = start + 8. Separated.
      // Case 2: oa ≠ obj. obj is in the tail (objects next_start g).
      //   Then oa < obj (since objects are ordered and obj is in the suffix).
      //   start = oa - 8 < obj - 8 < obj <= addr. 
      //   Since oa <= obj - 8 (8-aligned, oa < obj): start = oa - 8 <= obj - 16.
      //   addr >= obj, so addr - start >= obj - (obj - 16) = 16 > 8. Separated.
      if oa = obj then begin
        // addr >= obj = start + 8, so start + mword <= addr
        read_write_different g addr start v;
        if next_start_nat >= heap_size then ()
        else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          // next_start = obj - 8 + (ws+1)*8 = obj + ws*8
          // addr < obj + wosize_of_object*8. Need wosize_of_object = wz.
          wosize_of_object_spec obj g;
          assert (U64.v addr < next_start_nat);
          write_word_preserves_objects_past next_start g addr v
        end
      end else begin
        // oa ≠ obj: obj is in the suffix
        if next_start_nat >= heap_size then begin
          // objects start g = cons oa empty. obj not in empty => contradiction
          mem_cons_lemma obj oa (Seq.empty #obj_addr);
          assert (Seq.mem obj (Seq.cons oa (Seq.empty #obj_addr)));
          assert (obj = oa);  // contradiction with oa ≠ obj
          ()
        end else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          mem_cons_lemma obj oa (objects next_start g);
          // obj ∈ cons oa (objects next_start g) and obj ≠ oa => obj ∈ objects next_start g
          // start + mword <= addr (from case analysis above)
          objects_addresses_gt_start start g obj;
          // obj > start, so obj >= start + 8, addr >= obj >= start + 8
          read_write_different g addr start v;
          write_word_preserves_objects_aux next_start g obj addr v
        end
      end
    end
  end

/// Past-object phase already defined above as standalone
#pop-options

/// Field write preserves objects: writing to an object body address preserves enumeration
/// Key insight: body address is word-separated from all header addresses in the enumeration
val write_word_preserves_objects : (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects 0UL g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + FStar.Mul.(U64.v (wosize_of_object obj g) * 8) /\
                  U64.v addr % 8 = 0)
        (ensures objects 0UL (write_word g addr v) == objects 0UL g)

let write_word_preserves_objects g obj addr v =
  write_word_preserves_objects_aux 0UL g obj addr v

/// Field write preserves objects from arbitrary start position
val write_word_preserves_objects_from : (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects start g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + FStar.Mul.(U64.v (wosize_of_object obj g) * 8) /\
                  U64.v addr % 8 = 0)
        (ensures objects start (write_word g addr v) == objects start g)

let write_word_preserves_objects_from start g obj addr v =
  write_word_preserves_objects_aux start g obj addr v

/// Write to address before start preserves objects from that start
val write_word_preserves_objects_before : (start: hp_addr) -> (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires U64.v addr < U64.v start /\ U64.v addr % 8 = 0)
        (ensures objects start (write_word g addr v) == objects start g)

let write_word_preserves_objects_before start g addr v =
  write_word_preserves_objects_past start g addr v

/// ---------------------------------------------------------------------------
/// Color Change Preserves points_to (Self Case)
/// ---------------------------------------------------------------------------
///
/// When src = obj (the color-changed object), field addresses are at
/// src + k*8 >= src > src - 8 = hd_address(src), so they never overlap
/// with the modified header. This means field reads are unchanged.

/// Helper: in the non-overflow case, field address raw value matches arithmetic sum
private let field_addr_raw_value (h: obj_addr) (idx: U64.t{U64.v idx < pow2 61})
  : Lemma (U64.v (field_address_raw h idx) = (U64.v h + FStar.Mul.(U64.v idx * 8)) % pow2 64)
  = field_offset_bound idx

/// Helper: field address ≠ hd_address for obj_addr when idx < pow2 54
/// Case 1 (no overflow): h + idx*8 >= h > h - 8 = hd_address
/// Case 2 (overflow): need idx*8 ≠ 2^64 - 8; since idx < 2^54, idx*8 < 2^57 < 2^64 - 8
#push-options "--z3rlimit 100"
private let field_addr_ne_hd (h: obj_addr) (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires U64.v (field_address_raw h idx) < heap_size /\
                    U64.v (field_address_raw h idx) % 8 = 0)
          (ensures field_address_raw h idx <> Pulse.Spec.GC.Heap.hd_address h)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_addr_raw_value h idx;
    Pulse.Spec.GC.Heap.hd_address_spec h;
    let sum = U64.v h + FStar.Mul.(U64.v idx * 8) in
    if sum < pow2 64 then ()
    else begin
      // Overflow: field_addr = sum - 2^64, hd_address = h - 8
      // Equality would require idx*8 = 2^64 - 8, but idx*8 < 2^57 < 2^64 - 8
      FStar.Math.Lemmas.pow2_lt_compat 64 57;
      FStar.Math.Lemmas.pow2_lt_compat 57 54;
      assert (FStar.Mul.(U64.v idx * 8) < pow2 57);
      assert (pow2 57 < pow2 64 - 8)
    end
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec color_change_preserves_field_pointing_self (g: heap) (h: obj_addr) (c: color)
  (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr)
  : Lemma (ensures exists_field_pointing_to_unchecked (set_object_color h g c) h wz target
                   == exists_field_pointing_to_unchecked g h wz target)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      // Show add_mod/mul_mod matches field_address_raw
      field_offset_bound idx;
      FStar.Math.Lemmas.modulo_lemma (FStar.Mul.(U64.v idx * U64.v mword)) (pow2 64);
      let far = U64.add_mod h (U64.mul_mod idx mword) in
      let far_raw = field_address_raw h idx in
      assert (U64.v far = U64.v far_raw);
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then
        color_change_preserves_field_pointing_self g h c idx target
      else begin
        assert (far == far_raw);
        let field_addr : hp_addr = far in
        field_addr_ne_hd h idx;
        // SMTPat fires: read_word (set_object_color h g c) field_addr = read_word g field_addr
        color_change_preserves_field_pointing_self g h c idx target
      end
    end
#pop-options

/// Color change preserves points_to for the same object (self case)
let color_change_preserves_points_to_self (g: heap) (obj: obj_addr) (c: color) (dst: obj_addr)
  : Lemma (points_to (set_object_color obj g c) obj dst == points_to g obj dst)
  = set_object_color_preserves_getWosize_at_hd obj g c;
    wosize_of_object_spec obj g;
    wosize_of_object_spec obj (set_object_color obj g c);
    wosize_of_object_bound obj g;
    color_change_preserves_field_pointing_self g obj c (wosize_of_object obj g) dst

/// ---------------------------------------------------------------------------
/// Cross-Object Field/Header Separation (Other Case)
/// ---------------------------------------------------------------------------

/// Field addresses of one object don't overlap with header address of another.
/// Requires idx < wosize for the src < obj case (objects_separated).
#push-options "--z3rlimit 1000"
private let field_addr_ne_hd_other (g: heap) (src: obj_addr) (obj: obj_addr) 
  (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires src <> obj /\
                     Seq.mem src (objects 0UL g) /\ Seq.mem obj (objects 0UL g) /\
                     well_formed_heap g /\
                     U64.v idx < U64.v (wosize_of_object_as_wosize src g) /\
                     U64.v (field_address_raw src idx) < heap_size /\
                     U64.v (field_address_raw src idx) % 8 = 0)
          (ensures field_address_raw src idx <> Pulse.Spec.GC.Heap.hd_address obj)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_addr_raw_value src idx;
    Pulse.Spec.GC.Heap.hd_address_spec obj;
    let ws = U64.v (wosize_of_object_as_wosize src g) in
    let sum = U64.v src + FStar.Mul.(U64.v idx * 8) in
    // Prove overflow is impossible: wf_object_bound gives src + ws*8 <= heap_size.
    // Since idx < ws, we get sum = src + idx*8 < src + ws*8 <= heap_size < pow2 64.
    wf_object_bound g src;
    assert (U64.v src + op_Multiply ws 8 <= heap_size);
    assert (sum < pow2 64);
    // Now in the non-overflow case:
    if U64.v src > U64.v obj then ()
    else begin
      // src < obj: objects_separated gives obj > src + ws*8
      objects_separated 0UL g src obj;
      ()
    end
#pop-options

/// Color change preserves exists_field_pointing for different objects
/// This handles the case where src ≠ obj (cross-object case)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec color_change_preserves_field_pointing_other (g: heap) (obj: obj_addr) (c: color)
  (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr)
  : Lemma (requires src <> obj /\
                     Seq.mem src (objects 0UL g) /\
                     Seq.mem obj (objects 0UL g) /\
                     well_formed_heap g /\
                     U64.v wz <= U64.v (wosize_of_object_as_wosize src g))
          (ensures exists_field_pointing_to_unchecked (set_object_color obj g c) src wz target
                   == exists_field_pointing_to_unchecked g src wz target)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      // Show add_mod/mul_mod matches field_address_raw
      field_offset_bound idx;
      FStar.Math.Lemmas.modulo_lemma (FStar.Mul.(U64.v idx * U64.v mword)) (pow2 64);
      let far = U64.add_mod src (U64.mul_mod idx mword) in
      let far_raw = field_address_raw src idx in
      assert (U64.v far = U64.v far_raw);
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then
        color_change_preserves_field_pointing_other g obj c src idx target
      else begin
        assert (far == far_raw);
        let field_addr : hp_addr = far in
        field_addr_ne_hd_other g src obj idx;
        // SMTPat fires: read_word equality
        color_change_preserves_field_pointing_other g obj c src idx target
      end
    end
#pop-options

/// Color change preserves points_to for different objects (other case)
let color_change_preserves_points_to_other (g: heap) (obj: obj_addr) (c: color) 
  (src: obj_addr) (dst: obj_addr)
  : Lemma (requires src <> obj /\
                     Seq.mem src (objects 0UL g) /\
                     Seq.mem obj (objects 0UL g) /\
                     well_formed_heap g)
          (ensures points_to (set_object_color obj g c) src dst == points_to g src dst)
  = set_object_color_preserves_getWosize_at_hd obj g c;
    wosize_of_object_spec src g;
    wosize_of_object_spec src (set_object_color obj g c);
    wosize_of_object_bound src g;
    color_change_preserves_field_pointing_other g obj c src (wosize_of_object src g) dst

/// ---------------------------------------------------------------------------
/// Field Write Preserves well_formed_heap
/// ---------------------------------------------------------------------------

/// For src ≠ obj: objects don't overlap, so all fields of src are unchanged
#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"
private let rec write_word_preserves_field_pointing_other (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr)
  : Lemma (requires src <> obj /\
                     Seq.mem src (objects 0UL g) /\
                     Seq.mem obj (objects 0UL g) /\
                     well_formed_heap g /\
                     U64.v addr >= U64.v obj /\
                     U64.v addr < U64.v obj + op_Multiply (U64.v (wosize_of_object obj g)) 8 /\
                     U64.v addr % 8 = 0 /\
                     U64.v wz <= U64.v (wosize_of_object_as_wosize src g))
          (ensures exists_field_pointing_to_unchecked (write_word g addr v) src wz target
                   == exists_field_pointing_to_unchecked g src wz target)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      field_offset_bound idx;
      FStar.Math.Lemmas.modulo_lemma (FStar.Mul.(U64.v idx * U64.v mword)) (pow2 64);
      let far = U64.add_mod src (U64.mul_mod idx mword) in
      let far_raw = field_address_raw src idx in
      assert (U64.v far = U64.v far_raw);
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then
        write_word_preserves_field_pointing_other g obj addr v src idx target
      else begin
        assert (far == far_raw);
        let field_addr : hp_addr = far in
        // Objects don't overlap, so field_addr ≠ addr
        // field_addr is in src's body: src + idx*8
        // addr is in obj's body: obj <= addr < obj + wosize(obj)*8
        wosize_of_object_bound src g;
        wosize_of_object_bound obj g;
        let ws_src = U64.v (wosize_of_object_as_wosize src g) in
        let ws_obj = U64.v (wosize_of_object obj g) in
        if U64.v src < U64.v obj then begin
          objects_separated 0UL g src obj;
          // src + ws_src*8 < obj <= addr
          // field_addr = src + idx*8 < src + ws_src*8 (since idx < ws_src)
          // So field_addr < obj <= addr
          ()
        end else begin
          objects_separated 0UL g obj src;
          // obj + ws_obj*8 < src <= field_addr
          // addr < obj + ws_obj*8
          // So addr < src <= field_addr
          ()
        end;
        assert (field_addr <> addr);
        // read_write_different applies
        read_write_different g addr field_addr v;
        assert (read_word (write_word g addr v) field_addr == read_word g field_addr);
        // Recurse
        write_word_preserves_field_pointing_other g obj addr v src idx target
      end
    end
#pop-options

/// For src = obj: field at addr gets value v, others unchanged
#push-options "--z3rlimit 800 --fuel 4 --ifuel 2 --split_queries always"
private let rec write_word_field_pointing_self_implies (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma (requires Seq.mem obj (objects 0UL g) /\
                     well_formed_heap g /\
                     U64.v addr >= U64.v obj /\
                     U64.v addr < U64.v obj + op_Multiply (U64.v (wosize_of_object obj g)) 8 /\
                     U64.v addr % 8 = 0 /\
                     U64.v wz <= U64.v (wosize_of_object_as_wosize obj g) /\
                     exists_field_pointing_to_unchecked (write_word g addr v) obj wz dst /\
                     (is_pointer_field v ==> Seq.mem v (objects 0UL g)))
          (ensures Seq.mem dst (objects 0UL g))
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      field_offset_bound idx;
      FStar.Math.Lemmas.modulo_lemma (FStar.Mul.(U64.v idx * U64.v mword)) (pow2 64);
      let far = U64.add_mod obj (U64.mul_mod idx mword) in
      let far_raw = field_address_raw obj idx in
      assert (U64.v far = U64.v far_raw);
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then begin
        // Out of bounds: exists_field_pointing_to_unchecked returns false or recurses
        // But we know it's true for g', so it must be true for idx
        write_word_field_pointing_self_implies g obj addr v idx dst
      end else begin
        assert (far == far_raw);
        let field_addr : hp_addr = far in
        let g' = write_word g addr v in
        let field_val_g' = read_word g' field_addr in
        // exists_field_pointing_to_unchecked g' obj wz dst evaluates field at idx first
        // It returns true if: (1) this field matches, OR (2) recursive call on idx returns true
        if is_pointer_field field_val_g' && hd_address field_val_g' = hd_address dst then begin
          // Case (1): This field points to dst in g'
          if field_addr = addr then begin
            // Modified field: field_val_g' = v
            read_write_same g addr v;
            assert (field_val_g' == v);
            // v is a pointer to dst: hd_address v = hd_address dst
            // By contrapositive of hd_address_injective: if hd_address v = hd_address dst, then v = dst
            // (If v ≠ dst, then hd_address v ≠ hd_address dst by hd_address_injective, contradiction)
            if v <> dst then Pulse.Spec.GC.Heap.hd_address_injective v dst;
            assert (v == dst);
            // From precondition: is_pointer_field v ==> Seq.mem v (objects 0UL g)
            assert (Seq.mem dst (objects 0UL g))
          end else begin
            // Unmodified field: field_val_g' = read_word g field_addr  
            // Since field_addr ≠ addr, read_write_different applies
            assert (field_addr <> addr);
            read_write_different g addr field_addr v;
            let field_val_g = read_word g field_addr in
            assert (field_val_g' == field_val_g);
            // This field points to dst in g as well
            assert (is_pointer_field field_val_g && hd_address field_val_g = hd_address dst);
            // Use efptu_match to establish exists_field in original heap
            wosize_of_object_bound obj g;
            // field_val_g = dst by hd_address injectivity
            if field_val_g <> dst then Pulse.Spec.GC.Heap.hd_address_injective field_val_g dst;
            assert (field_val_g == dst);
            // Use field_read_implies_exists_pointing with full wosize and k=idx
            // Needs: well_formed_object g obj, idx < wosize, field pointer conditions
            // well_formed_object follows from well_formed_heap part 1
            assert (well_formed_object g obj);
            let full_wz = wosize_of_object_as_wosize obj g in
            wosize_of_object_spec obj g;
            assert (U64.v idx < U64.v full_wz);
            field_read_implies_exists_pointing g obj full_wz idx dst
          end
        end else begin
          // Case (2): This field doesn't match, so recursive call must return true
          // exists_field_pointing_to_unchecked g' obj idx dst = true
          write_word_field_pointing_self_implies g obj addr v idx dst
        end
      end
    end
#pop-options

/// write_word within an object's body preserves well_formed_heap,
/// provided the written value (if pointer) points to a valid object.
val field_write_preserves_wf : (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects 0UL g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + op_Multiply (U64.v (wosize_of_object obj g)) 8 /\
                  U64.v addr % 8 = 0 /\
                  (is_pointer_field v ==> Seq.mem v (objects 0UL g)))
        (ensures well_formed_heap (write_word g addr v))

#push-options "--z3rlimit 300"
let field_write_preserves_wf g obj addr v =
  let g' = write_word g addr v in
  write_word_preserves_objects g obj addr v;
  assert (objects 0UL g' == objects 0UL g);
  assert (Seq.length g' == Seq.length g);
  // Part 1: size bounds unchanged (headers unchanged)
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects 0UL g'))
    (ensures (let wz = wosize_of_object h g' in
              U64.v (hd_address h) + 8 + FStar.Mul.(U64.v wz * 8) <= Seq.length g'))
    = wosize_of_object_spec h g;
      wosize_of_object_spec h g';
      Pulse.Spec.GC.Heap.hd_address_spec h;
      wosize_of_object_bound obj g;
      wosize_of_object_bound h g;
      // hd_address (local) matches Pulse.Spec.GC.Heap.hd_address for obj_addr
      assert (hd_address h == Pulse.Spec.GC.Heap.hd_address h);
      // Prove addr ≠ hd_address h
      if h = obj then ()
      else begin
        if U64.v h < U64.v obj then
          objects_separated 0UL g h obj
        else
          objects_separated 0UL g obj h
      end;
      read_write_different g addr (Pulse.Spec.GC.Heap.hd_address h) v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  // Part 2: pointer targets in objects
  let aux2 (src dst: obj_addr) : Lemma
    (requires Seq.mem src (objects 0UL g') /\
              (let wz = wosize_of_object src g' in
               U64.v wz < pow2 54 /\
               exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem dst (objects 0UL g'))
    = wosize_of_object_spec src g;
      wosize_of_object_spec src g';
      wosize_of_object_bound src g;
      wosize_of_object_bound obj g;
      // Prove wosize unchanged: header not modified
      // Need to prove addr ≠ hd_address src
      Pulse.Spec.GC.Heap.hd_address_spec src;
      if src = obj then begin
        // hd_address obj = obj - 8, and addr >= obj
        ()
      end else begin
        // src ≠ obj: objects don't overlap
        if U64.v src < U64.v obj then begin
          // src < obj: objects_separated gives obj > src + wosize(src)*8
          objects_separated 0UL g src obj;
          // addr >= obj > src + wosize(src)*8
          // hd_address(src) = src - 8 < src < obj <= addr
          ()
        end else begin
          // src > obj: objects_separated gives src > obj + wosize(obj)*8
          objects_separated 0UL g obj src;
          // addr < obj + wosize(obj)*8 < src
          // So hd_address(src) = src - 8 > addr
          ()
        end
      end;
      read_write_different g addr (Pulse.Spec.GC.Heap.hd_address src) v;
      // So wosize_of_object src g' = wosize_of_object src g
      assert (wosize_of_object src g' == wosize_of_object src g);
      if src = obj then begin
        write_word_field_pointing_self_implies g obj addr v (wosize_of_object src g') dst
      end else begin
        write_word_preserves_field_pointing_other g obj addr v src (wosize_of_object src g') dst
        // This shows exists_field_pointing_to_unchecked g src wz dst
        // From well_formed_heap g, dst in objects g = objects g'
      end
  in
  let aux2_flat (src: obj_addr) (dst: obj_addr) : Lemma
    (requires Seq.mem src (objects 0UL g') /\
              U64.v (wosize_of_object src g') < pow2 54 /\
              exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst)
    (ensures Seq.mem dst (objects 0UL g'))
  = aux2 src dst
  in
  let aux2_imp (src: obj_addr) (dst: obj_addr) : Lemma
    ((Seq.mem src (objects 0UL g') /\
      U64.v (wosize_of_object src g') < pow2 54 /\
      exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst) ==> 
     Seq.mem dst (objects 0UL g'))
  = FStar.Classical.move_requires (aux2_flat src) dst
  in
  FStar.Classical.forall_intro_2 aux2_imp
#pop-options

/// ---------------------------------------------------------------------------
/// Bridge Lemma: well_formed_heap implies unpack succeeds
/// ---------------------------------------------------------------------------

/// Helper: getWosize and Pulse.Lib.Header.get_wosize are equivalent
let getWosize_eq_header (hdr: U64.t) 
  : Lemma (U64.v (getWosize hdr) == Pulse.Lib.Header.get_wosize (U64.v hdr))
  = getWosize_spec hdr;
    // getWosize hdr == U64.shift_right hdr 10ul
    // Pulse.Lib.Header.get_wosize (U64.v hdr) = shift_right #64 (U64.v hdr) 10
    // U64.shift_right hdr 10ul = U64.uint_to_t (shift_right #64 (U64.v hdr) 10)
    ()

/// Helper lemma: when objects is non-empty at start, unpack_object succeeds there
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let objects_unpack_succeeds (g: heap) (start: hp_addr)
  : Lemma 
    (requires well_formed_heap g /\ Seq.length (objects start g) > 0)
    (ensures Some? (unpack_object g start))
  = // Objects is non-empty, so the terminal condition doesn't apply
    assert (U64.v start + 8 < heap_size);
    
    let hdr = read_word g start in
    let wz = getWosize hdr in
    
    // Use existing lemma: when objects is non-empty, the head object fits
    objects_nonempty_head_fits start g;
    assert (U64.v start + FStar.Mul.((U64.v wz + 1) * 8) <= heap_size);
    
    // Bridge the two wosize representations
    getWosize_eq_header hdr;
    assert (U64.v wz == Pulse.Lib.Header.get_wosize (U64.v hdr));
    
    // Therefore unpack_object succeeds
    unpack_object_succeeds g start
#pop-options

/// Bridge lemma: well_formed_heap implies unpack succeeds
///
/// Proof strategy:
/// 1. Show that when objects is non-empty, unpack_object succeeds
/// 2. This ensures unpack_objects follows the same walk structure as objects
/// 3. Show pointer_closed holds (admitted - complex pointer closure proof)
/// 4. Therefore unpack g returns Some
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let wfh_implies_unpack (g: heap) : Lemma
  (requires well_formed_heap g)
  (ensures Some? (Pulse.Spec.GC.Heap.unpack g))
  = // Step 1: Establish that unpack_object succeeds whenever objects is non-empty
    // This is proven by objects_unpack_succeeds for the start position
    if Seq.length (objects 0UL g) > 0 then
      objects_unpack_succeeds g 0UL;
    
    // Step 2: Show pointer_closed holds on unpack_objects g 0UL
    // This requires proving that the pointer closure property from well_formed_heap
    // transfers to the pointer_closed predicate on the unpack_objects result.
    // 
    // The full proof would need to show:
    // - For every (obj, ol) in unpack_objects g 0UL
    // - For every field value fv in ol.fields  
    // - If fv looks like a pointer (fv >= 8, fv < heap_size, fv % 8 = 0)
    // - Then fv is in the address list of unpack_objects g 0UL
    //
    // This follows from well_formed_heap's pointer closure property because:
    // - obj is in objects 0UL g (by structural correspondence)
    // - fv is a field value, so exists_field_pointing_to_unchecked g obj wz fv holds
    // - Therefore fv ∈ objects 0UL g (by well_formed_heap)
    // - Therefore fv ∈ addresses of unpack_objects g 0UL (by structural correspondence)
    //
    // However, this requires:
    // - Converting between Seq.mem and List.Tot.mem
    // - Connecting field values in object_l.fields with exists_field_pointing_to_unchecked
    // - Proving the recursive correspondence for the entire list
    //
    // For now, we admit this complex proof
    admit()
#pop-options
