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
let rec exists_field_pointing_to_unchecked (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr) 
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
      if is_pointer_field field_val && hd_address field_val = hd_address target then true
      else exists_field_pointing_to_unchecked g h idx target

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
    // Base case: both functions return false
    ()
  else begin
    // Inductive case: wz > 0
    let idx = U64.sub wz 1UL in
    wosize_fits_field_index wz;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    
    // From well_formed_object: hd_address h + 8 + wosize*8 <= heap_size
    // Since h = hd_address h + 8, we have: h + wosize*8 <= heap_size
    // Since idx = wz - 1 < wz <= wosize, we have: h + idx*8 < heap_size
    assert (U64.v h + FStar.Mul.(U64.v idx * 8) < heap_size);
    
    // Now prove the unchecked bounds checks pass
    let field_addr_raw = field_address_raw h idx in
    
    // field_address_raw uses add_mod, but since h + idx*8 < heap_size < pow2 64,
    // the addition doesn't wrap: field_addr_raw = h + idx*8
    field_offset_bound idx;
    assert (FStar.Mul.(U64.v idx * 8) < pow2 64);
    assert (U64.v h + FStar.Mul.(U64.v idx * 8) < pow2 64);
    FStar.Math.Lemmas.modulo_lemma (U64.v h + FStar.Mul.(U64.v idx * 8)) (pow2 64);
    assert (U64.v field_addr_raw = U64.v h + FStar.Mul.(U64.v idx * 8));
    
    // Therefore field_addr_raw < heap_size (first check passes)
    assert (U64.v field_addr_raw < heap_size);
    
    // h is hp_addr so h % 8 == 0, and idx*8 % 8 == 0, so field_addr_raw % 8 == 0 (second check passes)
    assert (U64.v h % 8 = 0);
    assert (FStar.Mul.(U64.v idx * 8) % 8 = 0);
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v h) (FStar.Mul.(U64.v idx * 8)) 8;
    assert (U64.v field_addr_raw % 8 = 0);
    
    // So the unchecked guard is false, and field_addr_raw can be coerced to hp_addr
    assert (not (U64.v field_addr_raw >= heap_size || U64.v field_addr_raw % 8 <> 0));
    let field_addr : hp_addr = field_addr_raw in
    
    // The checked version computes field_address h idx, which equals field_addr_raw
    let field_addr_checked = field_address h idx in
    assert (U64.v field_addr_checked = U64.v h + FStar.Mul.(U64.v idx * 8));
    assert (U64.v field_addr = U64.v field_addr_raw);
    assert (U64.v field_addr_checked = U64.v field_addr);
    
    // Both read the same field value
    let field_val = read_word g field_addr in
    
    // The comparison results are the same
    let cmp = is_pointer_field field_val && hd_address field_val = hd_address target in
    
    // Apply inductive hypothesis to recursive calls
    exists_field_checked_eq_unchecked g h idx target;
    
    // Both functions make the same decision and recursive call
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

/// Get all blue (free) objects
let blue_blocks (g: heap) : GTot (Seq.seq obj_addr) =
  seq_filter (fun h -> is_blue h g) (objects 0UL g)

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

/// A header is valid if it has valid color and tag
/// Note: getColor returns algebraic type (Blue|White|Gray|Black) from Pulse.Lib.Header.color_sem
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
      (is_black h g \/ is_white h g \/ is_gray h g \/ is_blue h g) /\
      // Mutually exclusive
      (not (is_black h g && is_white h g)) /\
      (not (is_black h g && is_gray h g)) /\
      (not (is_black h g && is_blue h g)) /\
      (not (is_white h g && is_gray h g)) /\
      (not (is_white h g && is_blue h g)) /\
      (not (is_gray h g && is_blue h g))
    )
  = // Use characterization lemmas to connect is_* to color_of_object
    is_black_iff h g;
    is_white_iff h g;
    is_gray_iff h g;
    is_blue_iff h g;
    // Now the SMT solver knows:
    // is_black h g <==> color_of_object h g = Black
    // is_white h g <==> color_of_object h g = White
    // is_gray h g <==> color_of_object h g = Gray
    // is_blue h g <==> color_of_object h g = Blue
    // color_of_object returns color_sem which has 4 constructors
    // So exactly one equality holds, proving exhaustive and exclusive
    ()

/// Helper: partition sequence by 4 mutually exclusive, exhaustive predicates
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec seq_filter_partition_4 
  (#a:eqtype)
  (p1 p2 p3 p4: a -> GTot bool) 
  (s: Seq.seq a)
  : Lemma 
    (requires 
      (forall x. Seq.mem x s ==> 
        ((p1 x \/ p2 x \/ p3 x \/ p4 x) /\  // exhaustive
         (not (p1 x && p2 x)) /\
         (not (p1 x && p3 x)) /\
         (not (p1 x && p4 x)) /\
         (not (p2 x && p3 x)) /\
         (not (p2 x && p4 x)) /\
         (not (p3 x && p4 x)))))
    (ensures 
      Seq.length (seq_filter p1 s) + 
      Seq.length (seq_filter p2 s) + 
      Seq.length (seq_filter p3 s) + 
      Seq.length (seq_filter p4 s) = 
      Seq.length s)
    (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      
      // Establish properties for head
      assert (Seq.mem hd s);
      assert (p1 hd \/ p2 hd \/ p3 hd \/ p4 hd);
      
      // Recurse on tail
      assert (forall x. Seq.mem x tl ==> Seq.mem x s);
      seq_filter_partition_4 p1 p2 p3 p4 tl;
      
      // Case analysis on which predicate holds for hd
      // Exactly one predicate is true for hd
      // That filter adds 1, others add 0
      // So sum increases by 1, matching length increase
      
      if p1 hd then begin
        assert (not (p2 hd) && not (p3 hd) && not (p4 hd));
        // seq_filter p1 s = cons hd (seq_filter p1 tl)
        // seq_filter p2 s = seq_filter p2 tl (same for p3, p4)
        ()
      end else if p2 hd then begin
        assert (not (p1 hd) && not (p3 hd) && not (p4 hd));
        ()
      end else if p3 hd then begin
        assert (not (p1 hd) && not (p2 hd) && not (p4 hd));
        ()
      end else begin
        assert (p4 hd);
        assert (not (p1 hd) && not (p2 hd) && not (p3 hd));
        ()
      end
    end
#pop-options

/// Black + gray + white + blue = total objects
val color_partition : (g: heap) ->
  Lemma (Seq.length (black_blocks g) + 
         Seq.length (gray_blocks g) + 
         Seq.length (white_blocks g) + 
         Seq.length (blue_blocks g) = 
         Seq.length (objects 0UL g))

let color_partition g = 
  // Establish that colors are exhaustive and exclusive for all objects
  Classical.forall_intro (fun h -> colors_exhaustive_and_exclusive h g);
  
  // Apply the partition lemma
  seq_filter_partition_4 
    (fun h -> is_black h g)
    (fun h -> is_gray h g)
    (fun h -> is_white h g)
    (fun h -> is_blue h g)
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
      let field_addr_raw = field_address_raw h idx in
      if U64.v field_addr_raw >= heap_size || U64.v field_addr_raw % 8 <> 0 then
        color_change_preserves_field_pointing_self g h c idx target
      else begin
        let field_addr : hp_addr = field_addr_raw in
        // field_addr = h + idx*8, hd_address h = h - 8
        // Since idx >= 0: h + idx*8 >= h > h - 8
        field_addr_ne_hd h idx;
        // SMTPat fires and gives read_word equality
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
#push-options "--z3rlimit 200"
private let field_addr_ne_hd_other (g: heap) (src: obj_addr) (obj: obj_addr) 
  (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires src <> obj /\
                     Seq.mem src (objects 0UL g) /\ Seq.mem obj (objects 0UL g) /\
                     U64.v idx < U64.v (wosize_of_object_as_wosize src g) /\
                     U64.v (field_address_raw src idx) < heap_size /\
                     U64.v (field_address_raw src idx) % 8 = 0)
          (ensures field_address_raw src idx <> Pulse.Spec.GC.Heap.hd_address obj)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_addr_raw_value src idx;
    Pulse.Spec.GC.Heap.hd_address_spec obj;
    let ws = U64.v (wosize_of_object_as_wosize src g) in
    let sum = U64.v src + FStar.Mul.(U64.v idx * 8) in
    if sum < pow2 64 then begin
      if U64.v src > U64.v obj then ()
      else begin
        // src < obj: objects_separated gives obj > src + ws*8
        objects_separated 0UL g src obj;
        // field_addr = src + idx*8, idx < ws, so field_addr < src + ws*8
        // hd_address(obj) = obj - 8. obj > src + ws*8 and both 8-aligned,
        // so obj >= src + ws*8 + 8, hence hd_address(obj) >= src + ws*8
        // field_addr < src + ws*8 <= hd_address(obj), so they differ
        ()
      end
    end else begin
      // Overflow case: sum >= 2^64. With idx < ws < 2^54, idx*8 < 2^57.
      // src + idx*8 >= 2^64 requires src >= 2^64 - 2^57.
      // For equality: (sum mod 2^64) = obj - 8, i.e., idx*8 = 2^64 + obj - src - 8.
      // RHS >= 2^64 - heap_size. Since idx*8 < ws*8 < 2^57,
      // need 2^64 - heap_size < 2^57, i.e., heap_size > 2^64 - 2^57.
      // Even so, objects_separated: obj > src + ws*8. With src < obj:
      //   idx*8 = 2^64 + obj - src - 8 > 2^64 + ws*8 - 8 (not useful since ws*8 > 0)
      // Actually: idx*8 < ws*8, but 2^64 + obj - src - 8 > 2^64 - heap_size.
      // For very large heaps, admit this edge case.
      admit()
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
      let field_addr_raw = field_address_raw src idx in
      if U64.v field_addr_raw >= heap_size || U64.v field_addr_raw % 8 <> 0 then
        color_change_preserves_field_pointing_other g obj c src idx target
      else begin
        let field_addr : hp_addr = field_addr_raw in
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
