/// ---------------------------------------------------------------------------
/// GC.Spec.Fields - Object Enumeration for Concurrent GC
/// ---------------------------------------------------------------------------
///
/// This module provides functions to enumerate objects in the heap:
/// - objects: enumerate all allocated objects
/// - allocated_blocks: get all allocated block addresses
/// - black_blocks, gray_blocks, white_blocks: color-filtered enumerations

module GC.Spec.Fields

open FStar.Seq
open FStar.List.Tot
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header  // For color constructors

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

/// Helper: prove multiplication bound for field offset
private let field_offset_bound (field_idx: U64.t{U64.v field_idx < pow2 61}) : Lemma 
  (FStar.UInt.size (U64.v field_idx * 8) 64)
= 
  FStar.Math.Lemmas.pow2_plus 61 3;
  assert ((pow2 61 * pow2 3) == pow2 64);
  assert ((U64.v field_idx * 8) < pow2 64)

/// Field offset from index
let field_offset (field_idx: U64.t{U64.v field_idx < pow2 61}) : U64.t = 
  field_offset_bound field_idx;
  U64.mul field_idx mword

/// Field address from object address and field index
/// Returns a value that may not be a valid hp_addr without additional constraints
let field_address_raw (obj_addr: hp_addr) (field_idx: U64.t{U64.v field_idx < pow2 61}) : U64.t =
  U64.add_mod obj_addr (field_offset field_idx)
/// Check if value looks like a pointer (word-aligned, within heap bounds, with room for header)
let is_pointer (v: U64.t) : bool = 
  U64.v v >= U64.v zero_addr + U64.v mword && U64.v v < heap_size && U64.v v % U64.v mword = 0

/// Check if field value looks like a pointer
let is_pointer_field (field_val: U64.t) : bool = is_pointer field_val

/// Check if field value points to the same object as target (header comparison).
/// Uses if-then-else to establish obj_addr refinement from is_pointer_field.
let is_pointer_to (fv: U64.t) (target: obj_addr) : GTot bool =
  if is_pointer_field fv then
    hd_address fv = hd_address target
  else false

/// Helper: wosize is always < pow2 61
let wosize_fits_field_index (wz: wosize) 
  : Lemma (U64.v wz < pow2 61)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54

/// Object is well-formed: fits entirely within heap
let well_formed_object (g: heap) (h: obj_addr) : prop =
  let wz = wosize_of_object h g in
  U64.v (hd_address h) + 8 + (U64.v wz * 8) <= heap_size

/// Unchecked version - does not require well_formed_object precondition  
/// Used in well_formed_heap definition to avoid circularity
/// Uses mul_mod/add_mod to avoid internal lemma calls (enables SMT unfolding)
let rec exists_field_pointing_to_unchecked (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr) 
  : GTot bool (decreases U64.v wz) =
  if wz = 0UL then false
  else
    let idx = U64.sub wz 1UL in
    let field_addr_raw = U64.add_mod h (U64.mul_mod idx mword) in
    if U64.v field_addr_raw >= heap_size || U64.v field_addr_raw % 8 <> 0 then false
    else
      let field_addr : hp_addr = field_addr_raw in
      let field_val = read_word g field_addr in
      if is_pointer_to field_val target then true
      else exists_field_pointing_to_unchecked g h idx target

/// One-step unfolding: if guard passes AND field matches, function returns true
/// Takes far and fv as explicit witnesses to avoid unification issues
let efptu_match (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54 /\ wz <> 0UL}) (target: obj_addr)
  (far: hp_addr) (fv: U64.t)
  : Lemma (requires far == U64.add_mod h (U64.mul_mod (U64.sub wz 1UL) mword) /\
                   fv == read_word g far /\
                   is_pointer_to fv target)
          (ensures exists_field_pointing_to_unchecked g h wz target)
  = ()

/// One-step unfolding: if guard passes, field doesn't match, but recursive call returns true
let efptu_recurse (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54 /\ wz <> 0UL}) (target: obj_addr)
  (far: hp_addr) (fv: U64.t)
  : Lemma (requires far == U64.add_mod h (U64.mul_mod (U64.sub wz 1UL) mword) /\
                   fv == read_word g far /\
                   ~(is_pointer_to fv target) /\
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
                    is_pointer_to fv target)))
        (ensures exists_field_pointing_to_unchecked g h wz target)
        (decreases U64.v wz)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec field_read_implies_exists_pointing g h wz k target =
  let idx = U64.sub wz 1UL in
  FStar.Math.Lemmas.pow2_lt_compat 61 54;
  wosize_fits_field_index wz;
  field_offset_bound idx;
  assert ((U64.v idx * U64.v mword) < pow2 64);
  FStar.Math.Lemmas.modulo_lemma ((U64.v idx * U64.v mword)) (pow2 64);
  // Prove sum fits in U64 for modulo_lemma: h < heap_size < 2^30, idx*8 < 2^57
  assert (U64.v h < heap_size);
  FStar.Math.Lemmas.pow2_lt_compat 57 54;
  assert ((U64.v idx * 8) < pow2 57);
  // heap_size <= pow2 57, so h + idx*8 < pow2 57 + pow2 57 = pow2 58 < pow2 64
  assert (U64.v h < pow2 57);
  FStar.Math.Lemmas.pow2_double_sum 57;
  assert (U64.v h + (U64.v idx * 8) < pow2 58);
  FStar.Math.Lemmas.pow2_lt_compat 64 58;
  FStar.Math.Lemmas.modulo_lemma (U64.v h + (U64.v idx * 8)) (pow2 64);
  let far_idx = U64.add_mod h (U64.mul_mod idx mword) in
  assert (U64.v far_idx = U64.v h + (U64.v idx * 8));
  // well_formed_object: hd_address h + 8 + wz*8 <= heap_size, i.e. h + wz*8 <= heap_size
  hd_address_spec h;
  assert (U64.v far_idx < heap_size);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v h) ((U64.v idx * 8)) 8;
  assert (U64.v far_idx % 8 = 0);
  let fv_idx = read_word g (far_idx <: hp_addr) in
  if is_pointer_to fv_idx target then
    efptu_match g h wz target far_idx fv_idx
  else begin
    assert (U64.v k < U64.v idx);
    field_read_implies_exists_pointing g h idx k target;
    efptu_recurse g h wz target far_idx fv_idx
  end
#pop-options

/// Contrapositive of field_read_implies_exists_pointing:
/// If no field of h matches target, then exists_field_pointing_to_unchecked returns false.
let rec efptu_false_if_no_field_matches
  (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr)
  : Lemma
    (requires
      (forall (idx: nat{idx < U64.v wz}).
        (let far = U64.add_mod h (U64.mul_mod (U64.uint_to_t idx) mword) in
         U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
         ~(is_pointer_to (read_word g (far <: hp_addr)) target))))
    (ensures exists_field_pointing_to_unchecked g h wz target = false)
    (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      let far = U64.add_mod h (U64.mul_mod idx mword) in
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
      else
        efptu_false_if_no_field_matches g h idx target
    end
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
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then Seq.empty
    else begin
      // f_address start = start + 8, already typed as obj_addr
      f_address_spec start;
      let obj_addr : obj_addr = f_address start in
      
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

let objects_cons_end (start: hp_addr) (g: heap)
  : Lemma
    (requires
      U64.v start + 8 < Seq.length g /\
      (let header = read_word g start in
       let wz = getWosize header in
       let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
       next_start_nat <= Seq.length g /\
       next_start_nat < pow2 64 /\
       next_start_nat >= heap_size))
    (ensures objects start g == Seq.cons (f_address start) Seq.empty)
  =
  let header = read_word g start in
  let wz = getWosize header in
  let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
  f_address_spec start;
  assert (next_start_nat <= Seq.length g);
  assert (next_start_nat < pow2 64);
  assert (next_start_nat >= heap_size);
  ()

let objects_cons_step_to (start: hp_addr) (g: heap) (next: hp_addr)
  : Lemma
    (requires
      U64.v start + 8 < Seq.length g /\
      (let header = read_word g start in
       let wz = getWosize header in
       let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
       next_start_nat <= Seq.length g /\
       next_start_nat < pow2 64 /\
       next_start_nat < heap_size /\
       next_start_nat == U64.v next))
    (ensures objects start g == Seq.cons (f_address start) (objects next g))
  =
  let header = read_word g start in
  let wz = getWosize header in
  let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
  f_address_spec start;
  assert (next_start_nat <= Seq.length g);
  assert (next_start_nat < pow2 64);
  assert (next_start_nat < heap_size);
  assert (next_start_nat == U64.v next);
  assert (U64.uint_to_t next_start_nat == next);
  ()
/// Helper: membership in cons
let mem_cons_lemma (#a:eqtype) (x hd: a) (tl: Seq.seq a)
  : Lemma (Seq.mem x (Seq.cons hd tl) <==> x = hd \/ Seq.mem x tl)
  = Seq.Properties.lemma_append_count (Seq.create 1 hd) tl

/// All object addresses in objects are > start
/// Proof by induction on the structure of objects
#push-options "--fuel 3 --ifuel 1 --z3rlimit 100"
let rec objects_addresses_gt_start (start: hp_addr) (g: heap) (x: obj_addr)
  : Lemma (ensures Seq.mem x (objects start g) ==> U64.v x > U64.v start)
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()  // objects returns empty
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + (obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()  // objects returns empty
      else begin
        // First object is at start + 8, which is > start
        let obj_addr_raw = f_address start in
        f_address_spec start;
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
#push-options "--fuel 2 --ifuel 1 --z3rlimit 37"
let objects_addr_not_in_rest (start: hp_addr) (g: heap)
  : Lemma (requires U64.v start + 8 < Seq.length g)  // Strict less than
          (ensures (
            let header = read_word g start in
            let wz = getWosize header in
            let obj_addr = f_address start in
            let obj_size_nat = U64.v wz + 1 in
            let next_start_nat = U64.v start + (obj_size_nat * 8) in
            (next_start_nat < Seq.length g /\ next_start_nat < pow2 64 /\ next_start_nat < heap_size) ==>
            (let next_start : hp_addr = U64.uint_to_t next_start_nat in
             ~(Seq.mem obj_addr (objects next_start g)))))
  = let header = read_word g start in
    let wz = getWosize header in
    let obj_addr = f_address start in
    f_address_spec start;
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
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
/// ---------------------------------------------------------------------------
/// Objects Separation: later objects start beyond earlier object's fields
/// ---------------------------------------------------------------------------

/// For two distinct objects in objects(start, g), if src is the first object
/// and y is any later object, then y > src + wosize(src)*8.
/// This proves non-overlapping: fields of src are in [src, src+(wz-1)*8],
/// and hd_address(y) = y - 8 > src + wz*8 - 8 >= src + (wz-1)*8.
#push-options "--fuel 3 --ifuel 1 --z3rlimit 100"
let rec objects_separated (start: hp_addr) (g: heap) (src y: obj_addr)
  : Lemma (ensures Seq.mem src (objects start g) /\ Seq.mem y (objects start g) /\
                   U64.v src < U64.v y ==>
                   U64.v y > U64.v src + (U64.v (wosize_of_object_as_wosize src g) * 8))
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_addr_raw = f_address start in
      f_address_spec start;
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + (obj_size_nat * 8) in
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
            assert (next_start_nat = U64.v first + (U64.v wz * 8));
            // wosize_of_object first g = getWosize(read_word g (hd_address first))
            // hd_address first = first - 8 = start (since first = start + 8)
            hd_address_spec first;
            assert (U64.v (hd_address first) = U64.v start);
            // read_word g start = header (already computed above)
            // getWosize header = wz
            // wosize_of_object first g = getWosize(read_word g (GC.Spec.Heap.hd_address first))
            GC.Spec.Heap.hd_address_spec first;
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
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
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
/// If predicate is false for all members, seq_filter is empty
/// Get all blue objects (free-list blocks)
let blue_blocks (g: heap) : GTot (Seq.seq obj_addr) =
  seq_filter (fun h -> is_blue h g) (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// No Gray Objects Predicate
/// ---------------------------------------------------------------------------

/// No gray objects remain in heap (mark phase complete)
let no_gray_objects (g: heap) : prop =
  forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> not (is_gray h g)
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
let well_formed_heap_part1 (g: heap) : prop =
  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==>
    (let wz = wosize_of_object h g in
     U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length g))

let well_formed_heap_part4 (g: heap) : prop =
  (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(GC.Spec.Object.is_infix obj g))

/// Part 2 --- the field-closure clause --- is `opaque_to_smt`, and deliberately
/// so.  It is the clause that decides which heaps the collector is willing to
/// accept.  Sealing it means the *only* file that can see its body is this one,
/// so a change to its shape breaks a handful of accessor lemmas here rather
/// than silently reshaping proof obligations across a hundred client modules.
///
/// Cross the boundary with `wfh_part2_elim` / `well_formed_heap_part2_intro`,
/// or with the derived accessors further down (`wf_field_target_in_objects`
/// and friends).
///
/// The clause is stated on the *resolved* target.  A field may hold an interior
/// pointer to an infix object embedded in a closure --- that is how OCaml
/// represents mutually recursive functions --- and such a target is by
/// construction absent from `objects zero_addr g`, which enumerates whole
/// objects only (see part 4).  Requiring the raw target to be enumerated would
/// therefore make this clause unsatisfiable for any heap containing a mutually
/// recursive closure.  Requiring the *resolved* target --- the enclosing
/// closure, per `GC.Spec.Object.resolve_object` --- is the same requirement on
/// ordinary pointers, since `resolve_object` is the identity on non-infix
/// addresses, and the right one on interior pointers.
///
/// Part 3 is what makes this meaningful: it guarantees that `resolve_object`
/// actually reaches a valid enclosing closure rather than falling back to its
/// argument.  The two clauses must therefore be read, and changed, together.
[@@"opaque_to_smt"]
let well_formed_heap_part2 (g: heap) : prop =
  (forall (src dst: obj_addr). 
    (Seq.mem src (objects zero_addr g) /\ 
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==> 
    Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))

/// Eliminate part 2 at a single (src, dst) pair.
let wfh_part2_elim (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_part2 g /\ Seq.mem src (objects zero_addr g) /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
  = reveal_opaque (`%well_formed_heap_part2) well_formed_heap_part2

/// Introduce part 2 from the pointwise obligation.
let well_formed_heap_part2_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g)))
  : Lemma (well_formed_heap_part2 g)
  = reveal_opaque (`%well_formed_heap_part2) well_formed_heap_part2;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (Seq.mem src (objects zero_addr g) /\
         (let wz = wosize_of_object src g in
          U64.v wz < pow2 54 /\
          exists_field_pointing_to_unchecked g src wz dst)) ==>
        Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (pf src))
    in
    FStar.Classical.forall_intro aux

/// Convenience intro: if every pointer field target is *itself* enumerated,
/// part 2 follows.  This is the shape most producers of well-formed heaps
/// naturally prove, and it is sound because part 4 keeps infix objects out of
/// `objects`, so an enumerated target resolves to itself.
let well_formed_heap_part2_intro_raw (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem dst (objects zero_addr g)))
  : Lemma (requires well_formed_heap_part4 g)
          (ensures well_formed_heap_part2 g)
  = let pf' (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
      = pf src dst;
        GC.Spec.Object.resolve_non_infix dst g
    in
    well_formed_heap_part2_intro g pf'

/// Part 3 --- infix well-formedness of field targets.
///
/// This clause used to quantify over `objects zero_addr g`, where part 4 makes
/// it vacuous: no enumerated object is infix, so it constrained nothing.  The
/// obligation belongs on *field targets*, which is where an infix address can
/// actually appear, and it is precisely what gives `resolve_object` in part 2
/// its meaning: without it, `resolve_object` could silently fall back to
/// returning its (unenumerated) argument.
///
/// Note that `resolve_object` computes the parent from a mutable heap word, so
/// part 2 and part 3 must be kept in step; a model that made part 2 depend on
/// `resolve_object` without validating the parent would be trusting an
/// arbitrary field of the object graph.
[@@"opaque_to_smt"]
let well_formed_heap_part3 (g: heap) : prop =
  (forall (src dst: obj_addr).
    (Seq.mem src (objects zero_addr g) /\
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==>
    GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)

/// Eliminate part 3 at a single (src, dst) pair.
let wfh_part3_elim (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_part3 g /\ Seq.mem src (objects zero_addr g) /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = reveal_opaque (`%well_formed_heap_part3) well_formed_heap_part3

let well_formed_heap_part3_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst))
  : Lemma (well_formed_heap_part3 g)
  = reveal_opaque (`%well_formed_heap_part3) well_formed_heap_part3;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (Seq.mem src (objects zero_addr g) /\
         (let wz = wosize_of_object src g in
          U64.v wz < pow2 54 /\
          exists_field_pointing_to_unchecked g src wz dst)) ==>
        GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (pf src))
    in
    FStar.Classical.forall_intro aux

/// Convenience intro for heaps with no infix field targets at all: part 3 is
/// then vacuous.  Producers that already know their targets are enumerated
/// (hence non-infix, by part 4) can use this.
let well_formed_heap_part3_intro_no_infix (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures ~(GC.Spec.Object.is_infix dst g)))
  : Lemma (well_formed_heap_part3 g)
  = let pf' (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = pf src dst;
        GC.Spec.Object.infix_addr_wf_non_infix g (objects zero_addr g) dst
    in
    well_formed_heap_part3_intro g pf'

/// Transport parts 2 and 3 across a heap change that preserves the object
/// enumeration and every address's header interpretation.  Colour changes and
/// tag rewrites are the canonical instances: they leave `objects`, `is_infix`,
/// `is_closure`, `wosize_of_object` and hence `resolve_object` alone, so both
/// clauses carry over verbatim once the field-pointer structure is transported
/// by `fields`.
let well_formed_heap_part2_3_transport (g: heap) (g': heap)
    (fields: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g') /\
                      (let wz = wosize_of_object src g' in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g' src wz dst))
            (ensures Seq.mem src (objects zero_addr g) /\
                     (let wz = wosize_of_object src g in
                      U64.v wz < pow2 54 /\
                      exists_field_pointing_to_unchecked g src wz dst)))
  : Lemma (requires well_formed_heap_part2 g /\ well_formed_heap_part3 g /\
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (h: obj_addr).
                       GC.Spec.Object.is_infix h g' == GC.Spec.Object.is_infix h g /\
                       GC.Spec.Object.is_closure h g' == GC.Spec.Object.is_closure h g /\
                       GC.Spec.Object.wosize_of_object h g' == GC.Spec.Object.wosize_of_object h g /\
                       GC.Spec.Object.resolve_object h g' == GC.Spec.Object.resolve_object h g))
          (ensures well_formed_heap_part2 g' /\ well_formed_heap_part3 g')
  = let pf2 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g') /\
                (let wz = wosize_of_object src g' in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g' src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g') (objects zero_addr g'))
      = fields src dst;
        wfh_part2_elim g src dst
    in
    well_formed_heap_part2_intro g' pf2;
    let pf3 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g') /\
                (let wz = wosize_of_object src g' in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g' src wz dst))
      (ensures GC.Spec.Object.infix_addr_wf g' (objects zero_addr g') dst)
      = fields src dst;
        wfh_part3_elim g src dst;
        GC.Spec.Object.infix_addr_wf_congr g g' (objects zero_addr g) dst
    in
    well_formed_heap_part3_intro g' pf3

/// From a raw-membership field-closure proof plus part 4, both part 2 and
/// part 3 follow: every field target is enumerated, hence non-infix by part 4,
/// so part 3 is vacuous and part 2's `resolve_object` is the identity.
let well_formed_heap_part2_3_intro_raw (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem dst (objects zero_addr g)))
  : Lemma (requires well_formed_heap_part4 g)
          (ensures well_formed_heap_part2 g /\ well_formed_heap_part3 g)
  = well_formed_heap_part2_intro_raw g pf;
    let pf' (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures ~(GC.Spec.Object.is_infix dst g))
      = pf src dst
    in
    well_formed_heap_part3_intro_no_infix g pf'

[@@"opaque_to_smt"]
let well_formed_heap (g: heap) : prop =
  well_formed_heap_part1 g /\
  well_formed_heap_part2 g /\
  well_formed_heap_part3 g /\
  well_formed_heap_part4 g

/// No pointer field of any enumerated object holds the raw address `t`.
///
/// Needed by the field-write lemmas.  Writing a word inside an object's body
/// can clobber the *header* of an infix object, because an infix header lives
/// inside its enclosing closure's body --- unlike the header of an enumerated
/// object, which no other object's body can reach.  Since `resolve_object` and
/// `is_infix` are computed from that header, a write at `hd_address dst` for a
/// field target `dst` would invalidate parts 2 and 3.  Requiring that nothing
/// points at `f_address addr` rules this out.
let no_field_points_to_addr (g: heap) (t: nat) : prop =
  forall (src dst: obj_addr).
    (Seq.mem src (objects zero_addr g) /\
     U64.v (wosize_of_object src g) < pow2 54 /\
     exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst) ==>
    U64.v dst <> t

let no_field_points_to_addr_elim (g: heap) (t: nat) (src dst: obj_addr) : Lemma
  (requires no_field_points_to_addr g t /\ Seq.mem src (objects zero_addr g) /\
            U64.v (wosize_of_object src g) < pow2 54 /\
            exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst)
  (ensures U64.v dst <> t)
  = ()

/// The single sanctioned way to cross the `well_formed_heap` abstraction
/// boundary.  `well_formed_heap` is `opaque_to_smt`, so clients that need to
/// see its four conjuncts must unfold it; doing that with a bare
/// `reveal_opaque` scatters the unfolding across the development and makes it
/// impossible to tell which clients actually depend on which part.
///
/// Use this lemma instead of `reveal_opaque (`%well_formed_heap)
/// well_formed_heap`.  It is a biconditional, so it serves both directions:
/// decomposing a hypothesis and assembling a goal.
let wf_parts (_: unit) : Lemma
  (ensures forall (g: heap).
             well_formed_heap g <==>
             (well_formed_heap_part1 g /\
              well_formed_heap_part2 g /\
              well_formed_heap_part3 g /\
              well_formed_heap_part4 g))
  = reveal_opaque (`%well_formed_heap) well_formed_heap

/// ---------------------------------------------------------------------------
/// No-Scan Invariant
/// ---------------------------------------------------------------------------
///
/// No-scan objects (strings, bigarrays, custom blocks with tag >=
/// no_scan_tag) hold no word that looks like a managed heap pointer.
///
/// This is **not** a property of OCaml heaps, and the invariant should be read
/// as a restriction the collector imposes rather than a fact about the
/// mutator.  A `string`, a `Bytes.t`, a `Bigarray` payload or a `Custom` block
/// holds arbitrary bytes, and eight of them may perfectly well spell an
/// 8-aligned in-range address.  See `docs/no-scan-support-plan.md` for why it
/// is here and what it would take to remove.
///
/// In short: it is not needed to justify tracing.  The graph model already
/// agrees with the collector that a no-scan object has no out-edges ---
/// `GC.Spec.HeapGraph.get_pointer_fields` returns `Seq.empty` for it.  What
/// needs it is `well_formed_heap_part2`, whose antecedent runs through
/// `exists_field_pointing_to_unchecked` --- "unchecked" meaning it walks every
/// field of every object without consulting the tag --- and likewise
/// `GC.Spec.Mark.no_pointer_to_blue` via `points_to`.  Those two demand field
/// closure for words the collector never reads, and this invariant is what
/// assumes the demand away.
///
/// The invariant is restricted to non-blue objects because blue (free-list)
/// objects have their first field repurposed as the free-list pointer.  That
/// exclusion costs nothing, because free blocks are *cleared*:
/// `GC.Spec.Coalesce.flush_blue` gives every merged run a fresh header with
/// tag 0 and zeroes fields 2..wosize, leaving the free-list link as the only
/// pointer-shaped word in a free block.  So a blue object is never no-scan in a
/// coalesced heap (`GC.Spec.Coalesce.coalesce_aux_blue_tag_zero`), and blue
/// no-scan blocks exist only in the transient heap between the sweep and the
/// coalesce.
///
/// Preservation, and why the gap has never been observed:
///   - mark: only changes colors (headers), not fields -> trivially preserved
///   - sweep: freed objects become blue -> excluded from quantifier
///   - alloc: newly allocated objects have tag=0 < no_scan_tag -> not no_scan;
///            existing no_scan object fields are untouched
///
/// Read that last line again: no spec-level operation ever *creates* a no-scan
/// object.  The allocator writes tag 0, the sweep writes only a colour and a
/// link word.  So a no-scan object can only come from the initial heap, and
/// the invariant is trivially maintainable precisely because the specification
/// cannot build a counterexample -- the same shape of vacuity that
/// `docs/infix-support-plan.md` found for interior pointers.

[@@"opaque_to_smt"]
let no_scan_invariant (g: heap) : prop =
  (forall (src: obj_addr) (idx: nat).
    Seq.mem src (objects zero_addr g) /\
    is_no_scan src g /\
    ~(is_blue src g) /\
    idx < U64.v (wosize_of_object src g) /\
    U64.v src + idx * 8 < heap_size ==>
    (let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
     ~(is_pointer_field (read_word g field_addr))))

/// Extract: instantiate no_scan_invariant for a specific object and field index
let no_scan_invariant_elim (g: heap) (src: obj_addr) (idx: nat) : Lemma
  (requires no_scan_invariant g /\
            Seq.mem src (objects zero_addr g) /\
            is_no_scan src g /\
            ~(is_blue src g) /\
            idx < U64.v (wosize_of_object src g) /\
            U64.v src + idx * 8 < heap_size)
  (ensures (let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
            ~(is_pointer_field (read_word g field_addr))))
  = reveal_opaque (`%no_scan_invariant) no_scan_invariant

/// Introduce: establish no_scan_invariant from universal quantification
let no_scan_invariant_intro (g: heap) : Lemma
  (requires (forall (src: obj_addr) (idx: nat).
    Seq.mem src (objects zero_addr g) /\
    is_no_scan src g /\
    ~(is_blue src g) /\
    idx < U64.v (wosize_of_object src g) /\
    U64.v src + idx * 8 < heap_size ==>
    (let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
     ~(is_pointer_field (read_word g field_addr)))))
  (ensures no_scan_invariant g)
  = reveal_opaque (`%no_scan_invariant) no_scan_invariant
/// Pair introduction: if objects == [obj1; obj2] and neither is no_scan
let no_scan_invariant_intro_pair (g: heap) (obj1 obj2: obj_addr) : Lemma
  (requires objects zero_addr g == Seq.cons obj1 (Seq.cons obj2 Seq.empty) /\
            ~(is_no_scan obj1 g) /\ ~(is_no_scan obj2 g))
  (ensures no_scan_invariant g)
  = reveal_opaque (`%no_scan_invariant) no_scan_invariant

/// Extract part 1 of well_formed_heap: object size bounds
let wf_object_size_bound (g: heap) (h: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem h (objects zero_addr g))
  (ensures U64.v (hd_address h) + 8 + op_Star (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  = reveal_opaque (`%well_formed_heap) well_formed_heap

/// Extract part 1 without hd_address (for cross-module use with HeapGraph.object_fits_in_heap)
/// Since hd_address h = h - 8 for obj_addr h, we get: h + wosize*8 <= Seq.length g
let wf_object_bound (g: heap) (h: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem h (objects zero_addr g))
  (ensures U64.v h + op_Star (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    hd_address_spec h

/// Extract part 1 from well_formed_heap_part1 only (no full wfh needed).
/// Since hd_address h = h - 8 for obj_addr h, part1 gives: h + wosize*8 <= heap_size.
let wfh_part1_obj_bound (g: heap) (h: obj_addr) : Lemma
  (requires well_formed_heap_part1 g /\ Seq.mem h (objects zero_addr g))
  (ensures U64.v h + op_Star (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  = hd_address_spec h

/// Extract part 4: objects in the list are non-infix
let wf_objects_non_infix (g: heap) (h: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem h (objects zero_addr g))
  (ensures ~(GC.Spec.Object.is_infix h g))
  = reveal_opaque (`%well_formed_heap) well_formed_heap

/// In a well-formed heap, resolve_object is identity for objects in the list
/// (Because objects are non-infix, resolve returns self)
let wf_resolve_identity (g: heap) (x: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g))
  (ensures GC.Spec.Object.resolve_object x g == x)
  = wf_objects_non_infix g x;
    GC.Spec.Object.resolve_non_infix x g

/// `infix_wf` over the enumerated object list.  Since part 4 keeps infix
/// objects out of that list, this is vacuous --- which is exactly why part 3
/// was moved off `objects` and onto field targets.  Retained because a number
/// of downstream lemmas (`resolve_object_in_objects` and friends) are phrased
/// in terms of it.
let wf_infix_wf (g: heap) : Lemma
  (requires well_formed_heap g)
  (ensures GC.Spec.Object.infix_wf g (objects zero_addr g))
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    let pf (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g) /\ GC.Spec.Object.is_infix h g)
      (ensures (let p = GC.Spec.Object.parent_closure_addr_nat h g in
                p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                Seq.mem (U64.uint_to_t p) (objects zero_addr g) /\
                GC.Spec.Object.is_closure (U64.uint_to_t p) g))
      = ()  // part 4 makes the hypothesis contradictory
    in
    GC.Spec.Object.infix_wf_intro g (objects zero_addr g) pf

/// In a well-formed heap, the *resolved* target of a pointer field of an
/// enumerated object is itself an enumerated object.  This directly
/// instantiates well_formed_heap part 2.
///
/// The target itself need not be enumerated: it may be an interior pointer to
/// an infix object inside a closure, in which case the enclosing closure is
/// what is enumerated.  Use `wf_field_target_infix_wf` to learn that the
/// enclosing closure is valid, or `wf_field_target_in_objects_raw` when the
/// target is independently known to be non-infix.
let wf_field_target_in_objects (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    wfh_part2_elim g src dst

/// Part 3 at a field target: an infix field target has a valid enclosing closure.
let wf_field_target_infix_wf (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    wfh_part3_elim g src dst

/// A heap in which no field of an enumerated object holds an interior (infix)
/// pointer.
///
/// This is *not* part of `well_formed_heap`: the whole point of the resolved
/// formulation of parts 2 and 3 is that interior pointers into closures are
/// legal.  It is a strictly stronger, optional restriction that individual
/// collectors may impose on the heaps they handle.  Neither collector in this
/// repository imposes it: the mark-and-sweep collector never needed it, and the
/// generational collector accepts interior pointers in both the major heap and
/// the nursery (see `GC.Gen.HeapInvariant.collection_heap_shape` and the
/// interior coverage clauses of `GC.Gen.CheneyBFS.fwd_well_formed`).  The
/// predicate is retained because it is a convenient hypothesis for lemmas that
/// only make sense on interior-free heaps.
///
/// Under this restriction `well_formed_heap` part 2 collapses back to raw
/// membership (`wf_field_target_in_objects_raw`) and part 3 is vacuous.
[@@"opaque_to_smt"]
let no_infix_field_targets (g: heap) : prop =
  forall (src: obj_addr) (dst: obj_addr).
    Seq.mem src (objects zero_addr g) /\
    (let wz = wosize_of_object src g in
     U64.v wz < pow2 54 /\
     exists_field_pointing_to_unchecked g src wz dst) ==>
    ~(GC.Spec.Object.is_infix dst g)

let no_infix_field_targets_elim (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires no_infix_field_targets g /\ Seq.mem src (objects zero_addr g) /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures ~(GC.Spec.Object.is_infix dst g))
  = reveal_opaque (`%no_infix_field_targets) no_infix_field_targets

let no_infix_field_targets_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures ~(GC.Spec.Object.is_infix dst g)))
  : Lemma (no_infix_field_targets g)
  = reveal_opaque (`%no_infix_field_targets) no_infix_field_targets;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (Seq.mem src (objects zero_addr g) /\
         (let wz = wosize_of_object src g in
          U64.v wz < pow2 54 /\
          exists_field_pointing_to_unchecked g src wz dst)) ==>
        ~(GC.Spec.Object.is_infix dst g))
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (pf src))
    in
    FStar.Classical.forall_intro aux

/// `points_to` form of the elimination.
let no_infix_points_to_target (g: heap) (src dst: obj_addr) : Lemma
  (requires no_infix_field_targets g /\ Seq.mem src (objects zero_addr g) /\
            points_to g src dst)
  (ensures ~(GC.Spec.Object.is_infix dst g))
  = wosize_of_object_bound src g;
    no_infix_field_targets_elim g src dst

/// The pre-infix conclusion, recovered when the target is known non-infix.
let wf_field_target_in_objects_raw (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\
            ~(GC.Spec.Object.is_infix dst g) /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures Seq.mem dst (objects zero_addr g))
  = wf_field_target_in_objects g src dst;
    GC.Spec.Object.resolve_non_infix dst g

/// The converse of `wf_field_target_in_objects_raw`, and together with it the
/// precise statement of what `no_infix_field_targets` costs.
///
/// Before interior pointers were supported, part 2 required the *raw* field
/// value to be in `objects`; `raw` below is exactly that hypothesis.  This
/// lemma shows it entails `no_infix_field_targets`, while
/// `wf_field_target_in_objects_raw` shows the reverse.  Hence, modulo part 4,
///
///   old well_formed_heap  <==>  well_formed_heap /\ no_infix_field_targets
///
/// so a collector that assumes `no_infix_field_targets` (as the generational one
/// does, in `GC.Gen.HeapInvariant.major_heap_shape`) accepts precisely the heaps
/// it accepted before the resolved formulation --- no more, and no fewer.  The
/// clause is a relocation of an existing restriction, not a new one, and the
/// heaps it excludes are exactly those that motivated the change.
let no_infix_field_targets_from_raw (g: heap)
    (raw: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem dst (objects zero_addr g)))
  : Lemma (requires well_formed_heap_part4 g)
          (ensures no_infix_field_targets g)
  = let pf (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures ~(GC.Spec.Object.is_infix dst g))
      = raw src dst
    in
    no_infix_field_targets_intro g pf

/// ---------------------------------------------------------------------------
/// Interior pointers out of free-list cells
/// ---------------------------------------------------------------------------
///
/// `no_infix_field_targets` restricts *every* object.  Almost nothing in the
/// generational collector actually needs that: what needs it is
/// `GC.Gen.Promote.blue_fields_closed`, which is stated on the raw field value
/// and is derived from part 2 by
/// `GC.Gen.PromoteUpdate.BlueAlloc.wfh_part2_implies_blue_fields_closed`.  That
/// derivation only ever looks at *blue* (free-list) objects.
///
/// `blue_fields_non_infix` is exactly that restriction and no more: a free-list
/// cell may not hold an interior pointer.  Live objects --- white, gray and
/// black --- are unconstrained, which is what makes interior pointers between
/// mutually recursive closures expressible under the generational invariant.
///
/// It costs nothing to re-establish.  After a collection the Cheney machinery
/// proves *raw* part 2 for blue objects (they are untouched, and `objects` is
/// preserved), and `blue_fields_non_infix_from_raw` turns that straight into
/// this clause.  See `GC.Gen.HeapInvariant.major_heap_shape`.
[@@"opaque_to_smt"]
let blue_fields_non_infix (g: heap) : prop =
  forall (src: obj_addr) (dst: obj_addr).
    Seq.mem src (objects zero_addr g) /\
    GC.Spec.Object.is_blue src g /\
    (let wz = wosize_of_object src g in
     U64.v wz < pow2 54 /\
     exists_field_pointing_to_unchecked g src wz dst) ==>
    ~(GC.Spec.Object.is_infix dst g)

let blue_fields_non_infix_elim (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires blue_fields_non_infix g /\ Seq.mem src (objects zero_addr g) /\
            GC.Spec.Object.is_blue src g /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures ~(GC.Spec.Object.is_infix dst g))
  = reveal_opaque (`%blue_fields_non_infix) blue_fields_non_infix

let blue_fields_non_infix_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      GC.Spec.Object.is_blue src g /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures ~(GC.Spec.Object.is_infix dst g)))
  : Lemma (blue_fields_non_infix g)
  = reveal_opaque (`%blue_fields_non_infix) blue_fields_non_infix;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (Seq.mem src (objects zero_addr g) /\
         GC.Spec.Object.is_blue src g /\
         (let wz = wosize_of_object src g in
          U64.v wz < pow2 54 /\
          exists_field_pointing_to_unchecked g src wz dst)) ==>
        ~(GC.Spec.Object.is_infix dst g))
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (pf src))
    in
    FStar.Classical.forall_intro aux

/// The blue-only clause is a weakening of the all-objects one.
let no_infix_field_targets_weaken (g: heap) : Lemma
  (requires no_infix_field_targets g)
  (ensures blue_fields_non_infix g)
  = let pf (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                GC.Spec.Object.is_blue src g /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures ~(GC.Spec.Object.is_infix dst g))
      = no_infix_field_targets_elim g src dst
    in
    blue_fields_non_infix_intro g pf

/// Raw part 2 restricted to blue objects entails the clause.  This is how it is
/// re-established after every collection, and why it is free.
let blue_fields_non_infix_from_raw (g: heap)
    (raw: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      GC.Spec.Object.is_blue src g /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem dst (objects zero_addr g)))
  : Lemma (requires well_formed_heap_part4 g)
          (ensures blue_fields_non_infix g)
  = let pf (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                GC.Spec.Object.is_blue src g /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures ~(GC.Spec.Object.is_infix dst g))
      = raw src dst
    in
    blue_fields_non_infix_intro g pf

/// Combined: field read + pointer target → target ∈ objects.
/// Internalizes wf_object_size_bound + field_read_implies_exists_pointing + wf_field_target_in_objects.
let field_pointer_target_in_objects (g: heap) (h: obj_addr)
    (k: U64.t{U64.v k < pow2 61}) (target: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem h (objects zero_addr g) /\
                    U64.v k < U64.v (wosize_of_object h g) /\
                    (let far = U64.add_mod h (U64.mul_mod k mword) in
                     U64.v far < heap_size /\ U64.v far % 8 = 0 /\
                     (let fv = read_word g (far <: hp_addr) in
                      is_pointer_to fv target)))
          (ensures Seq.mem (GC.Spec.Object.resolve_object target g) (objects zero_addr g))
  = let wz = wosize_of_object h g in
    wosize_of_object_bound h g;
    wf_object_size_bound g h;
    field_read_implies_exists_pointing g h wz k target;
    wf_field_target_in_objects g h target

/// In a well-formed heap, pointer targets of objects are themselves in objects.
/// Bridges points_to → exists_field_pointing_to_unchecked → wf_field_target_in_objects.
let points_to_target_in_objects (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\
            points_to g src dst)
  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
  = wosize_of_object_bound src g;
    wf_field_target_in_objects g src dst

/// Part 3 at a `points_to` target: an interior pointer's target has a valid
/// enclosing closure.
let points_to_target_infix_wf (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\
            points_to g src dst)
  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = wosize_of_object_bound src g;
    wf_field_target_infix_wf g src dst

/// The pre-infix conclusion, recovered when the target is known non-infix.
let points_to_target_in_objects_raw (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\
            ~(GC.Spec.Object.is_infix dst g) /\ points_to g src dst)
  (ensures Seq.mem dst (objects zero_addr g))
  = points_to_target_in_objects g src dst;
    GC.Spec.Object.resolve_non_infix dst g

/// Derive well_formed_heap_part2 from a per-field closure property.
/// If every pointer-valued field of every object targets another object,
/// then well_formed_heap_part2 holds.
///
/// The field_closure hypothesis says: for any object src in objects, and any field index j,
/// if the field value is a pointer, then it targets an object in the objects list.
/// From this we derive that efptu(g, src, wz, dst) = false for all dst ∉ objects,
/// which is well_formed_heap_part2.
#push-options "--z3rlimit 12 --fuel 1 --ifuel 1"
let well_formed_heap_part2_from_field_closure (g: heap)
    (field_closure: (src: obj_addr) -> (j: nat) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ j < U64.v (wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g))))
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part4 g)
    (ensures well_formed_heap_part2 g /\ well_formed_heap_part3 g /\
             no_infix_field_targets g)
  = let aux (src dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr g) /\
                      U64.v (wosize_of_object src g) < pow2 54 /\
                      exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst)
            (ensures Seq.mem dst (objects zero_addr g))
    = if Seq.mem dst (objects zero_addr g) then ()
      else begin
        let wz = wosize_of_object src g in
        // wfh_part1 gives: hd_address(src) + 8 + wz * 8 <= Seq.length g = heap_size
        // i.e., (src - 8) + 8 + wz * 8 = src + wz * 8 <= heap_size
        hd_address_spec src;
        assert (U64.v src + U64.v wz * 8 <= heap_size);
        // For each field idx, show ~(is_pointer_to (read_word g field_addr) dst)
        let field_not_dst (idx: nat{idx < U64.v wz})
          : Lemma (let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
                   U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
                   ~(is_pointer_to (read_word g (far <: hp_addr)) dst))
          = let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
            // Show add_mod/mul_mod don't overflow
            assert (idx * 8 < pow2 64);
            assert (U64.v (U64.mul_mod (U64.uint_to_t idx) mword) == idx * 8);
            assert (U64.v src + idx * 8 < pow2 64);
            assert (U64.v far == U64.v src + idx * 8);
            if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
            else begin
              let fv = read_word g (far <: hp_addr) in
              if is_pointer_to fv dst then begin
                // is_pointer_to fv dst ==> is_pointer_field fv /\ hd_address fv == hd_address dst
                hd_address_spec (fv <: obj_addr);
                hd_address_spec dst;
                // hd_address fv = fv - 8, hd_address dst = dst - 8, equal ==> fv == dst
                assert (fv == dst);
                assert (is_pointer fv);
                // Instantiate field_closure with src and idx
                field_closure src idx;
                assert (Seq.mem (fv <: obj_addr) (objects zero_addr g))
                // Contradicts dst ∉ objects since fv == dst
              end else ()
            end
        in
        Classical.forall_intro field_not_dst;
        efptu_false_if_no_field_matches g src wz dst
      end
    in
    let aux_wrapped (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem dst (objects zero_addr g))
      = aux src dst
    in
    well_formed_heap_part2_intro_raw g aux_wrapped;
    // Part 3 is vacuous here: every field target is enumerated, and part 4
    // keeps infix objects out of the enumeration.
    let aux_non_infix (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures ~(GC.Spec.Object.is_infix dst g))
      = aux src dst
    in
    well_formed_heap_part3_intro_no_infix g aux_non_infix;
    no_infix_field_targets_intro g aux_non_infix
#pop-options

/// `blue_fields_non_infix` from a per-index closure proof about blue objects.
///
/// The counterpart of `well_formed_heap_part2_from_field_closure`, restricted to
/// free-list cells.  Producers that can show a blue object's pointer fields hold
/// *enumerated* addresses get the clause for free, since part 4 keeps infix
/// objects out of the enumeration.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let blue_fields_non_infix_from_field_closure (g: heap)
    (field_closure: (src: obj_addr) -> (j: nat) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      GC.Spec.Object.is_blue src g /\
                      j < U64.v (wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g))))
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part4 g)
          (ensures blue_fields_non_infix g)
  = let contra (src: obj_addr) (dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr g) /\
                      GC.Spec.Object.is_blue src g /\
                      U64.v (wosize_of_object src g) < pow2 54 /\
                      GC.Spec.Object.is_infix dst g)
            (ensures ~(exists_field_pointing_to_unchecked g src
                         (wosize_of_object src g) dst))
    = begin
        let wz = wosize_of_object src g in
        hd_address_spec src;
        assert (U64.v src + U64.v wz * 8 <= heap_size);
        let field_not_dst (idx: nat{idx < U64.v wz})
          : Lemma (let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
                   U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
                   ~(is_pointer_to (read_word g (far <: hp_addr)) dst))
          = let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
            assert (idx * 8 < pow2 64);
            assert (U64.v (U64.mul_mod (U64.uint_to_t idx) mword) == idx * 8);
            assert (U64.v src + idx * 8 < pow2 64);
            assert (U64.v far == U64.v src + idx * 8);
            if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
            else begin
              let fv = read_word g (far <: hp_addr) in
              if is_pointer_to fv dst then begin
                hd_address_spec (fv <: obj_addr);
                hd_address_spec dst;
                assert (fv == dst);
                assert (is_pointer fv);
                field_closure src idx
              end else ()
            end
        in
        Classical.forall_intro field_not_dst;
        efptu_false_if_no_field_matches g src wz dst
      end
    in
    let pf (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                GC.Spec.Object.is_blue src g /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures ~(GC.Spec.Object.is_infix dst g))
      = Classical.move_requires (contra src) dst
    in
    blue_fields_non_infix_intro g pf
#pop-options

/// Resolved analogue of `well_formed_heap_part2_from_field_closure`.
///
/// The raw version demands that every pointer-valued field hold an *enumerated*
/// address.  Part 4 keeps infix objects out of the enumeration, so that demand
/// silently forbids interior pointers, and any producer that goes through it
/// inherits the restriction.  This version demands only what parts 2 and 3
/// actually say: the field's *resolved* target is enumerated, and the raw value
/// is a well-formed infix address (trivially true when it is not infix).
///
/// It is the introduction rule for producers that walk fields index by index --
/// the Cheney collector's `update_major_pointers` is the motivating one -- and
/// want to stay infix-correct.  Note that it does *not* conclude
/// `no_infix_field_targets`, which is the whole point.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let well_formed_heap_part2_3_from_resolved_field_closure (g: heap)
    (field_closure: (src: obj_addr) -> (j: nat) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\
                      j < U64.v (wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==>
                      Seq.mem (GC.Spec.Object.resolve_object (v <: obj_addr) g)
                              (objects zero_addr g) /\
                      GC.Spec.Object.infix_addr_wf g (objects zero_addr g)
                              (v <: obj_addr))))
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part4 g)
    (ensures well_formed_heap_part2 g /\ well_formed_heap_part3 g)
  = let contra (src: obj_addr) (dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr g) /\
                      U64.v (wosize_of_object src g) < pow2 54 /\
                      ~(Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
                        GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst))
            (ensures ~(exists_field_pointing_to_unchecked g src
                         (wosize_of_object src g) dst))
    = begin
        let wz = wosize_of_object src g in
        hd_address_spec src;
        assert (U64.v src + U64.v wz * 8 <= heap_size);
        let field_not_dst (idx: nat{idx < U64.v wz})
          : Lemma (let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
                   U64.v far < heap_size /\ U64.v far % 8 == 0 ==>
                   ~(is_pointer_to (read_word g (far <: hp_addr)) dst))
          = let far = U64.add_mod src (U64.mul_mod (U64.uint_to_t idx) mword) in
            assert (idx * 8 < pow2 64);
            assert (U64.v (U64.mul_mod (U64.uint_to_t idx) mword) == idx * 8);
            assert (U64.v src + idx * 8 < pow2 64);
            assert (U64.v far == U64.v src + idx * 8);
            if U64.v far >= heap_size || U64.v far % 8 <> 0 then ()
            else begin
              let fv = read_word g (far <: hp_addr) in
              if is_pointer_to fv dst then begin
                hd_address_spec (fv <: obj_addr);
                hd_address_spec dst;
                assert (fv == dst);
                assert (is_pointer fv);
                field_closure src idx
              end else ()
            end
        in
        Classical.forall_intro field_not_dst;
        efptu_false_if_no_field_matches g src wz dst
      end
    in
    let aux (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
               GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = Classical.move_requires (contra src) dst
    in
    let aux2 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
      = aux src dst
    in
    let aux3 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = aux src dst
    in
    well_formed_heap_part2_intro g aux2;
    well_formed_heap_part3_intro g aux3
#pop-options

/// When objects start g is nonempty, the first object fits in heap:
/// start + (1 + wz) * 8 <= Seq.length g
/// This follows directly from the objects definition (the next_start check)
let objects_nonempty_head_fits (start: hp_addr) (g: heap) : Lemma
  (requires Seq.length (objects start g) > 0)
  (ensures (let wz = getWosize (read_word g start) in
            U64.v start + ((U64.v wz + 1) * 8) <= Seq.length g))
  = ()

/// When objects start g is nonempty, the head object is f_address start
let objects_nonempty_head (start: hp_addr) (g: heap) : Lemma
  (requires Seq.length (objects start g) > 0)
  (ensures (let obj = f_address start in
            U64.v obj == U64.v start + 8 /\
            Seq.head (objects start g) == obj))
  = f_address_spec start

/// When objects start g is nonempty, next_start is valid and objects decomposes
let objects_nonempty_next (start: hp_addr) (g: heap) : Lemma
  (requires Seq.length (objects start g) > 0)
  (ensures (let wz = getWosize (read_word g start) in
            let next = U64.v start + ((U64.v wz + 1) * 8) in
            next <= Seq.length g /\ next < pow2 64 /\
            next % 8 == 0 /\
            (next < heap_size ==>
              (let next_hp : hp_addr = U64.uint_to_t next in
               objects start g == Seq.cons (f_address start) (objects next_hp g)))))
  = FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v start) (((U64.v (getWosize (read_word g start)) + 1) * 8)) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (U64.v (getWosize (read_word g start)) + 1) 8 8

/// Members of objects from a later start are also members of objects from an earlier start
/// (objects later g ⊆ objects earlier g when later is the next scan position after earlier)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 25"
let objects_later_subset (start: hp_addr) (g: heap) (x: obj_addr)
  : Lemma (requires Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next_nat = U64.v start + ((U64.v wz + 1) * 8) in
                    next_nat < heap_size /\ next_nat < pow2 64 /\ next_nat % 8 == 0 ==>
                    (let next : hp_addr = U64.uint_to_t next_nat in
                     Seq.mem x (objects next g) ==> Seq.mem x (objects start g))))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let next_nat = U64.v start + ((U64.v wz + 1) * 8) in
      if next_nat > Seq.length g || next_nat >= pow2 64 then ()
      else if next_nat >= heap_size then ()
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        let oa = f_address start in
        // objects start g == cons oa (objects next g), so mem in tail → mem in cons
        mem_cons_lemma x oa (objects next g)
      end
    end
#pop-options
/// ---------------------------------------------------------------------------
/// Object Count Bounds
/// ---------------------------------------------------------------------------

/// Helper: objects use at least 8 bytes each

/// Any member of the objects walk satisfies the size bound:
/// hd_address(obj) + 8 + wosize * 8 <= Seq.length g
#push-options "--fuel 2 --ifuel 1 --z3rlimit 25"
let rec objects_member_size_bound (start: hp_addr) (g: heap) (obj: obj_addr)
  : Lemma
    (requires Seq.mem obj (objects start g))
    (ensures (
      let wz = getWosize (read_word g (hd_address obj)) in
      let obj_words = U64.v wz + 1 in
      U64.v (hd_address obj) + (obj_words * U64.v mword) <= Seq.length g))
    (decreases Seq.length g - U64.v start)
  = objects_nonempty_next start g;
    f_address_spec start;
    if f_address start = obj then begin
      hd_address_spec obj
    end
    else begin
      let wz = getWosize (read_word g start) in
      let next_nat = U64.v start + ((U64.v wz + 1) * U64.v mword) in
      if next_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t next_nat in
        Seq.lemma_tl (f_address start) (objects next g);
        objects_member_size_bound next g obj
      end
    end
#pop-options


/// Generalized version: length (objects start g) * 8 <= length g - start
#push-options "--fuel 2 --ifuel 1 --z3rlimit 12"
let rec objects_count_le_remaining (start: hp_addr) (g: heap)
  : Lemma 
    (ensures (Seq.length (objects start g) * 8) <= Seq.length g - U64.v start)
    (decreases Seq.length g - U64.v start)
  = if U64.v start + 8 >= Seq.length g then begin
      // objects returns empty, so length = 0
      // 0 * 8 = 0 <= length g - start
      ()
    end else begin
      let header = read_word g start in
      let wz = getWosize header in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + (obj_size_nat * 8) in
      
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then begin
        // objects returns empty
        ()
      end else begin
        let obj_addr_raw = f_address start in
        f_address_spec start;
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
          assert ((tail_len * 8) <= Seq.length g - next_start_nat);
          
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
          assert ((obj_size_nat * 8) >= 8);
          assert (next_start_nat == U64.v start + (obj_size_nat * 8));
          
          FStar.Math.Lemmas.lemma_mult_le_right 8 1 obj_size_nat;
          assert ((total_len * 8) == 8 + (tail_len * 8));
          assert ((tail_len * 8) <= Seq.length g - next_start_nat);
          assert (8 + (Seq.length g - next_start_nat) == 8 + Seq.length g - next_start_nat);
          assert (next_start_nat == U64.v start + (obj_size_nat * 8));
          assert (8 + Seq.length g - next_start_nat == 
                  8 + Seq.length g - U64.v start - (obj_size_nat * 8));
          ()
        end
      end
    end
#pop-options
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
  = is_black_iff h g;
    is_white_iff h g;
    is_gray_iff h g;
    is_blue_iff h g;
    ()

/// Helper: partition sequence by 3 mutually exclusive, exhaustive predicates
/// Helper: partition sequence by 4 mutually exclusive, exhaustive predicates
/// ---------------------------------------------------------------------------
/// Color Change Preservation
/// ---------------------------------------------------------------------------

/// Color changes preserve object enumeration
/// Key insight: set_object_color only changes color bits in one header word.
/// objects depends on getWosize at each step, which is in different bits.
/// Color changes preserve object enumeration
/// Key insight: set_object_color only changes color bits in one header word.
/// objects depends on getWosize at each step, which is in different bits.
#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"
val color_change_preserves_objects_aux : (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (c: color) ->
  Lemma (ensures objects start (set_object_color obj g c) == objects start g)
        (decreases (Seq.length g - U64.v start))

let rec color_change_preserves_objects_aux start g obj c =
  // SMT pattern on set_object_color_read_word fires when solver sees
  // read_word (set_object_color obj g c) start
  if U64.v start + 8 >= Seq.length g then ()
  else begin
    let wz = getWosize (read_word g start) in
    let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else if next_start_nat >= heap_size then ()
    else
      color_change_preserves_objects_aux (U64.uint_to_t next_start_nat) g obj c
  end
#pop-options

/// Top-level: color change preserves objects enumeration from 0
val color_change_preserves_objects : (g: heap) -> (obj: obj_addr) -> (c: color) ->
  Lemma (objects zero_addr (set_object_color obj g c) == objects zero_addr g)

let color_change_preserves_objects g obj c =
  color_change_preserves_objects_aux zero_addr g obj c

/// Objects membership ↔ after color change
let color_change_preserves_objects_mem (g: heap) (obj: obj_addr) (c: color) (x: obj_addr)
  : Lemma (Seq.mem x (objects zero_addr (set_object_color obj g c)) <==> Seq.mem x (objects zero_addr g))
  = color_change_preserves_objects g obj c

/// Past-object phase: addr < all future header positions
/// Standalone (not mutually recursive)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
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
      let next_start_nat = U64.v start + (obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then begin
        assert (objects start g == Seq.empty);
        assert (objects start g' == Seq.empty)
      end
      else begin
        let obj_addr_raw = f_address start in
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
#push-options "--z3rlimit 400 --fuel 4 --ifuel 2"
private val write_word_preserves_objects_aux : (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires Seq.mem obj (objects start g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
                  U64.v addr % 8 = 0)
        (ensures objects start (write_word g addr v) == objects start g)
        (decreases (Seq.length g - U64.v start))

let rec write_word_preserves_objects_aux start g obj addr v =
  if U64.v start + 8 >= Seq.length g then ()
  else begin
    let header = read_word g start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else begin
      let obj_addr_raw = f_address start in
      f_address_spec start;
      let oa : obj_addr = obj_addr_raw in
      GC.Spec.Heap.hd_address_spec oa;
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
                  Seq.mem obj (objects zero_addr g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
                  U64.v addr % 8 = 0)
        (ensures objects zero_addr (write_word g addr v) == objects zero_addr g)

let write_word_preserves_objects g obj addr v =
  write_word_preserves_objects_aux zero_addr g obj addr v
/// Field write preserves objects — variant requiring only well_formed_heap_part1.
/// Same proof as write_word_preserves_objects but with weaker precondition.
val write_word_preserves_objects_part1 : (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
                  U64.v addr % 8 = 0)
        (ensures objects zero_addr (write_word g addr v) == objects zero_addr g)

let write_word_preserves_objects_part1 g obj addr v =
  write_word_preserves_objects_aux zero_addr g obj addr v

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
  : Lemma (U64.v (field_address_raw h idx) = (U64.v h + (U64.v idx * 8)) % pow2 64)
  = field_offset_bound idx

/// Helper: field address ≠ hd_address for obj_addr when idx < pow2 54
/// Case 1 (no overflow): h + idx*8 >= h > h - 8 = hd_address
/// Case 2 (overflow): need idx*8 ≠ 2^64 - 8; since idx < 2^54, idx*8 < 2^57 < 2^64 - 8
#push-options "--z3rlimit 25"
private let field_addr_ne_hd (h: obj_addr) (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires U64.v (field_address_raw h idx) < heap_size /\
                    U64.v (field_address_raw h idx) % 8 = 0)
          (ensures field_address_raw h idx <> GC.Spec.Heap.hd_address h)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_addr_raw_value h idx;
    GC.Spec.Heap.hd_address_spec h;
    let sum = U64.v h + (U64.v idx * 8) in
    if sum < pow2 64 then ()
    else begin
      // Overflow: field_addr = sum - 2^64, hd_address = h - 8
      // Equality would require idx*8 = 2^64 - 8, but idx*8 < 2^57 < 2^64 - 8
      FStar.Math.Lemmas.pow2_lt_compat 64 57;
      FStar.Math.Lemmas.pow2_lt_compat 57 54;
      assert ((U64.v idx * 8) < pow2 57);
      assert (pow2 57 < pow2 64 - 8)
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec color_change_preserves_field_pointing_self (g: heap) (h: obj_addr) (c: color)
  (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr)
  : Lemma (ensures exists_field_pointing_to_unchecked (set_object_color h g c) h wz target
                   == exists_field_pointing_to_unchecked g h wz target)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      // Show add_mod/mul_mod matches field_address_raw
      field_offset_bound idx;
      FStar.Math.Lemmas.modulo_lemma ((U64.v idx * U64.v mword)) (pow2 64);
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
#push-options "--z3rlimit 250"
private let field_addr_ne_hd_other (g: heap) (src: obj_addr) (obj: obj_addr) 
  (idx: U64.t{U64.v idx < pow2 54})
  : Lemma (requires src <> obj /\
                     Seq.mem src (objects zero_addr g) /\ Seq.mem obj (objects zero_addr g) /\
                     well_formed_heap g /\
                     U64.v idx < U64.v (wosize_of_object_as_wosize src g) /\
                     U64.v (field_address_raw src idx) < heap_size /\
                     U64.v (field_address_raw src idx) % 8 = 0)
          (ensures field_address_raw src idx <> GC.Spec.Heap.hd_address obj)
  = FStar.Math.Lemmas.pow2_lt_compat 61 54;
    field_addr_raw_value src idx;
    GC.Spec.Heap.hd_address_spec obj;
    let ws = U64.v (wosize_of_object_as_wosize src g) in
    let sum = U64.v src + (U64.v idx * 8) in
    // Prove overflow is impossible: wf_object_bound gives src + ws*8 <= heap_size.
    // Since idx < ws, we get sum = src + idx*8 < src + ws*8 <= heap_size < pow2 64.
    wf_object_bound g src;
    assert (U64.v src + op_Star ws 8 <= heap_size);
    assert (sum < pow2 64);
    // Now in the non-overflow case:
    if U64.v src > U64.v obj then ()
    else begin
      // src < obj: objects_separated gives obj > src + ws*8
      objects_separated zero_addr g src obj;
      ()
    end
#pop-options

/// Color change preserves exists_field_pointing for different objects
/// This handles the case where src ≠ obj (cross-object case)
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec color_change_preserves_field_pointing_other (g: heap) (obj: obj_addr) (c: color)
  (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr)
  : Lemma (requires src <> obj /\
                     Seq.mem src (objects zero_addr g) /\
                     Seq.mem obj (objects zero_addr g) /\
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
      FStar.Math.Lemmas.modulo_lemma ((U64.v idx * U64.v mword)) (pow2 64);
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
                     Seq.mem src (objects zero_addr g) /\
                     Seq.mem obj (objects zero_addr g) /\
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
#push-options "--z3rlimit 75 --fuel 2 --ifuel 1"
private let rec write_word_preserves_field_pointing_other (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr)
  : Lemma (requires src <> obj /\
                     Seq.mem src (objects zero_addr g) /\
                     Seq.mem obj (objects zero_addr g) /\
                     well_formed_heap g /\
                     U64.v addr >= U64.v obj /\
                     U64.v addr < U64.v obj + op_Star (U64.v (wosize_of_object obj g)) 8 /\
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
      FStar.Math.Lemmas.modulo_lemma ((U64.v idx * U64.v mword)) (pow2 64);
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
        wf_object_size_bound g src;
        wf_object_size_bound g obj;
        wosize_of_object_bound src g;
        wosize_of_object_bound obj g;
        hd_address_spec src;
        hd_address_spec obj;
        let ws_src = U64.v (wosize_of_object_as_wosize src g) in
        let ws_obj = U64.v (wosize_of_object obj g) in
        if U64.v src < U64.v obj then begin
          objects_separated zero_addr g src obj;
          // src + ws_src*8 < obj <= addr
          // field_addr = src + idx*8 < src + ws_src*8 (since idx < ws_src)
          // So field_addr < obj <= addr
          ()
        end else begin
          objects_separated zero_addr g obj src;
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
#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"
private let rec write_word_field_pointing_self_implies (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma (requires Seq.mem obj (objects zero_addr g) /\
                     well_formed_heap g /\
                     U64.v addr >= U64.v obj /\
                     U64.v addr < U64.v obj + op_Star (U64.v (wosize_of_object obj g)) 8 /\
                     U64.v addr % 8 = 0 /\
                     U64.v wz <= U64.v (wosize_of_object_as_wosize obj g) /\
                     exists_field_pointing_to_unchecked (write_word g addr v) obj wz dst /\
                     (is_pointer_field v ==>
                        Seq.mem (GC.Spec.Object.resolve_object v g) (objects zero_addr g)))
          (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
                   ((v == dst /\ is_pointer_field v) \/
                    exists_field_pointing_to_unchecked g obj
                      (wosize_of_object_as_wosize obj g) dst))
          (decreases U64.v wz)
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      field_offset_bound idx;
      FStar.Math.Lemmas.modulo_lemma ((U64.v idx * U64.v mword)) (pow2 64);
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
        if is_pointer_to field_val_g' dst then begin
          // Case (1): This field points to dst in g'
          if field_addr = addr then begin
            // Modified field: field_val_g' = v
            read_write_same g addr v;
            assert (field_val_g' == v);
            // v is a pointer to dst: hd_address v = hd_address dst
            // By contrapositive of hd_address_injective: if hd_address v = hd_address dst, then v = dst
            // (If v ≠ dst, then hd_address v ≠ hd_address dst by hd_address_injective, contradiction)
            if v <> dst then GC.Spec.Heap.hd_address_injective v dst;
            assert (v == dst)
            // From the precondition on v, resolve_object dst g is enumerated.
          end else begin
            // Unmodified field: field_val_g' = read_word g field_addr  
            // Since field_addr ≠ addr, read_write_different applies
            assert (field_addr <> addr);
            read_write_different g addr field_addr v;
            let field_val_g = read_word g field_addr in
            assert (field_val_g' == field_val_g);
            // This field points to dst in g as well
            assert (is_pointer_to field_val_g dst);
            // Use efptu_match to establish exists_field in original heap
            wosize_of_object_bound obj g;
            // field_val_g = dst by hd_address injectivity
            if field_val_g <> dst then GC.Spec.Heap.hd_address_injective field_val_g dst;
            assert (field_val_g == dst);
            // Use field_read_implies_exists_pointing with full wosize and k=idx
            // Needs: well_formed_object g obj, idx < wosize, field pointer conditions
            // well_formed_object follows from well_formed_heap part 1
            wf_object_size_bound g obj;
            assert (well_formed_object g obj);
            let full_wz = wosize_of_object_as_wosize obj g in
            wosize_of_object_spec obj g;
            assert (U64.v idx < U64.v full_wz);
            field_read_implies_exists_pointing g obj full_wz idx dst;
            wf_field_target_in_objects g obj dst
          end
        end else begin
          // Case (2): This field doesn't match, so recursive call must return true
          // exists_field_pointing_to_unchecked g' obj idx dst = true
          write_word_field_pointing_self_implies g obj addr v idx dst
        end
      end
    end
#pop-options

/// write_word within an object's body preserves infix_wf
private let field_write_preserves_infix_wf
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v addr >= U64.v obj /\
                    U64.v addr < U64.v obj + op_Star (U64.v (wosize_of_object obj g)) 8 /\
                    U64.v addr % 8 = 0)
          (ensures GC.Spec.Object.infix_wf (write_word g addr v) (objects zero_addr (write_word g addr v)))
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    wf_infix_wf g;
    let g' = write_word g addr v in
    write_word_preserves_objects g obj addr v;
    let objs = objects zero_addr g in
    assert (objects zero_addr g' == objs);
    let header_not_addr (h: obj_addr) : Lemma
      (requires Seq.mem h objs)
      (ensures U64.v addr <> U64.v (GC.Spec.Heap.hd_address h))
      = wosize_of_object_bound obj g;
        wosize_of_object_bound h g;
        GC.Spec.Heap.hd_address_spec h;
        GC.Spec.Heap.hd_address_spec obj;
        if h = obj then ()
        else if U64.v h < U64.v obj then
          objects_separated zero_addr g h obj
        else
          objects_separated zero_addr g obj h
    in
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h objs /\ GC.Spec.Object.is_infix h g')
      (ensures (let p = GC.Spec.Object.parent_closure_addr_nat h g' in
                p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                Seq.mem (U64.uint_to_t p) objs /\
                GC.Spec.Object.is_closure (U64.uint_to_t p) g'))
      = header_not_addr h;
        read_write_different g addr (GC.Spec.Heap.hd_address h) v;
        wosize_of_object_spec h g;
        wosize_of_object_spec h g';
        GC.Spec.Object.tag_of_object_spec h g;
        GC.Spec.Object.tag_of_object_spec h g';
        GC.Spec.Object.is_infix_spec h g;
        GC.Spec.Object.is_infix_spec h g';
        assert (GC.Spec.Object.is_infix h g);
        GC.Spec.Object.parent_closure_addr_nat_spec h g;
        GC.Spec.Object.parent_closure_addr_nat_spec h g';
        GC.Spec.Object.infix_wf_elim g objs h;
        let p_nat = GC.Spec.Object.parent_closure_addr_nat h g in
        let p : obj_addr = U64.uint_to_t p_nat in
        header_not_addr p;
        read_write_different g addr (GC.Spec.Heap.hd_address p) v;
        GC.Spec.Object.tag_of_object_spec p g;
        GC.Spec.Object.tag_of_object_spec p g';
        GC.Spec.Object.is_closure_spec p g;
        GC.Spec.Object.is_closure_spec p g'
    in
    GC.Spec.Object.infix_wf_intro g' objs aux

/// Nothing can point at field 0's slot of an enumerated object.
///
/// This is the fact that makes the free-list write in `GC.Spec.Sweep` legal:
/// sweep threads the free pointer through field 0, and `field_write_preserves_wf`
/// demands that the write not clobber the header of anything a field points at.
///
/// Suppose some field pointed at `t = f_address obj`.  Part 2 puts
/// `resolve_object t g` in `objects`.
///
///   * If `t` is not infix it resolves to itself, so `t` would be enumerated ---
///     but `t`'s header is `obj` itself, so `t` would be an object starting one
///     word inside `obj`, contradicting `objects_separated`.
///   * If `t` is infix, part 3 says its offset is at least two words, so its
///     enclosing closure `p` satisfies `p <= obj - 8 < obj`, and `t` lies within
///     `p`'s fields.  Then `p`'s extent reaches past `obj`, and `p` and `obj` are
///     two distinct enumerated objects that overlap --- again impossible.
///
/// So no such field exists.  (This does *not* generalise to fields other than 0:
/// an infix object genuinely can sit at offset >= 2 of an enumerated closure.)
let no_field_points_to_field_zero (g: heap) (obj: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\
            U64.v (wosize_of_object obj g) >= 1)
  (ensures no_field_points_to_addr g (U64.v obj + 8))
  = let objs = objects zero_addr g in
    let aux (src dst: obj_addr) : Lemma
      (requires Seq.mem src objs /\
                U64.v (wosize_of_object src g) < pow2 54 /\
                exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst)
      (ensures U64.v dst <> U64.v obj + 8)
      = if U64.v dst <> U64.v obj + 8 then ()
        else begin
          wf_field_target_in_objects g src dst;
          wf_field_target_infix_wf g src dst;
          wosize_of_object_bound obj g;
          wosize_of_object_spec obj g;
          if GC.Spec.Object.is_infix dst g then begin
            GC.Spec.Object.infix_addr_wf_elim g objs dst;
            let w = U64.v (wosize_of_object dst g) in
            assert (w >= 2);
            let pn = U64.v dst - w * 8 in
            let p : obj_addr = U64.uint_to_t pn in
            assert (Seq.mem p objs);
            assert (U64.v p = pn);
            assert (U64.v p <= U64.v obj - 8);
            assert (U64.v dst < pn + U64.v (wosize_of_object p g) * 8);
            objects_separated zero_addr g p obj;
            assert (U64.v obj > pn + U64.v (wosize_of_object_as_wosize p g) * 8);
            wosize_of_object_spec p g
          end else begin
            GC.Spec.Object.resolve_non_infix dst g;
            assert (Seq.mem dst objs);
            assert (U64.v dst = U64.v obj + 8);
            objects_separated zero_addr g obj dst;
            assert (U64.v dst > U64.v obj + U64.v (wosize_of_object_as_wosize obj g) * 8);
            wosize_of_object_spec obj g
          end
        end
    in
    FStar.Classical.forall_intro_2 (fun src -> FStar.Classical.move_requires (aux src))

/// write_word within an object's body preserves well_formed_heap, provided the
/// written value (if a pointer) resolves to a valid object, and provided the
/// write does not clobber the header of anything a field points at.
///
/// The last condition is vacuous for heaps without interior pointers --- the
/// header of an enumerated object lies outside every other object's body --- but
/// it is real once field targets may be infix, since an infix header lives
/// *inside* its enclosing closure's body and is therefore writable.
val field_write_preserves_wf : (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects zero_addr g) /\
                  U64.v addr >= U64.v obj /\
                  U64.v addr < U64.v obj + op_Star (U64.v (wosize_of_object obj g)) 8 /\
                  U64.v addr % 8 = 0 /\
                  no_field_points_to_addr g (U64.v addr + 8) /\
                  U64.v v <> U64.v addr + 8 /\
                  (is_pointer_field v ==>
                     Seq.mem (GC.Spec.Object.resolve_object v g) (objects zero_addr g) /\
                     GC.Spec.Object.infix_addr_wf g (objects zero_addr g) v))
        (ensures well_formed_heap (write_word g addr v))

#push-options "--z3rlimit 75"
let field_write_preserves_wf g obj addr v =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let g' = write_word g addr v in
  write_word_preserves_objects g obj addr v;
  assert (objects zero_addr g' == objects zero_addr g);
  assert (Seq.length g' == Seq.length g);
  // Part 1: size bounds unchanged (headers unchanged)
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr g'))
    (ensures (let wz = wosize_of_object h g' in
              U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length g'))
    = wosize_of_object_spec h g;
      wosize_of_object_spec h g';
      GC.Spec.Heap.hd_address_spec h;
      wosize_of_object_bound obj g;
      wosize_of_object_bound h g;
      // Prove addr ≠ hd_address h
      if h = obj then ()
      else begin
        if U64.v h < U64.v obj then
          objects_separated zero_addr g h obj
        else
          objects_separated zero_addr g obj h
      end;
      read_write_different g addr (GC.Spec.Heap.hd_address h) v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  // Part 2: pointer targets in objects
  let aux2 (src dst: obj_addr) : Lemma
    (requires Seq.mem src (objects zero_addr g') /\
              (let wz = wosize_of_object src g' in
               U64.v wz < pow2 54 /\
               exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem (GC.Spec.Object.resolve_object dst g') (objects zero_addr g') /\
             GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst /\
             read_word g (GC.Spec.Heap.hd_address dst) ==
               read_word g' (GC.Spec.Heap.hd_address dst))
    = wosize_of_object_spec src g;
      wosize_of_object_spec src g';
      wosize_of_object_bound src g;
      wosize_of_object_bound obj g;
      // Prove wosize unchanged: header not modified
      // Need to prove addr ≠ hd_address src
      GC.Spec.Heap.hd_address_spec src;
      if src = obj then begin
        // hd_address obj = obj - 8, and addr >= obj
        ()
      end else begin
        // src ≠ obj: objects don't overlap
        if U64.v src < U64.v obj then begin
          // src < obj: objects_separated gives obj > src + wosize(src)*8
          objects_separated zero_addr g src obj;
          // addr >= obj > src + wosize(src)*8
          // hd_address(src) = src - 8 < src < obj <= addr
          ()
        end else begin
          // src > obj: objects_separated gives src > obj + wosize(obj)*8
          objects_separated zero_addr g obj src;
          // addr < obj + wosize(obj)*8 < src
          // So hd_address(src) = src - 8 > addr
          ()
        end
      end;
      read_write_different g addr (GC.Spec.Heap.hd_address src) v;
      // So wosize_of_object src g' = wosize_of_object src g
      assert (wosize_of_object src g' == wosize_of_object src g);
      // Pull the target back into the original heap.  In both branches `dst` is
      // either a field target of `g` or the freshly written value `v`; neither
      // can be `f_address addr`, so the write left `dst`'s header alone and its
      // infix status, resolution and enclosing closure are all unchanged.
      if src = obj then begin
        wosize_of_object_bound obj g;
        write_word_field_pointing_self_implies g obj addr v (wosize_of_object src g') dst;
        wosize_of_object_spec obj g;
        if is_pointer_field v && v = dst then
          // `dst` is the freshly written value; both facts come straight from
          // the precondition on `v`.
          assert (GC.Spec.Object.infix_addr_wf g (objects zero_addr g) v)
        else begin
          assert (exists_field_pointing_to_unchecked g obj (wosize_of_object obj g) dst);
          no_field_points_to_addr_elim g (U64.v addr + 8) obj dst;
          wf_field_target_infix_wf g obj dst
        end
      end else begin
        write_word_preserves_field_pointing_other g obj addr v src (wosize_of_object src g') dst;
        wf_field_target_in_objects g src dst;
        wf_field_target_infix_wf g src dst;
        no_field_points_to_addr_elim g (U64.v addr + 8) src dst
      end;
      assert (U64.v dst <> U64.v addr + 8);
      GC.Spec.Heap.hd_address_spec dst;
      read_write_different g addr (GC.Spec.Heap.hd_address dst) v;
      GC.Spec.Object.resolve_object_locality dst g g'
  in
  let aux2_flat (src: obj_addr) (dst: obj_addr) : Lemma
    (requires Seq.mem src (objects zero_addr g') /\
              U64.v (wosize_of_object src g') < pow2 54 /\
              exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst)
    (ensures Seq.mem (GC.Spec.Object.resolve_object dst g') (objects zero_addr g'))
  = aux2 src dst
  in
  well_formed_heap_part2_intro g' aux2_flat;
  // Part 3: transport infix well-formedness of every field target from g to g'.
  // Enumerated objects keep their headers (their extents are disjoint from the
  // body word being written), and the target keeps its own header as above.
  let headers_stable (o: obj_addr) : Lemma
    (requires Seq.mem o (objects zero_addr g))
    (ensures read_word g (GC.Spec.Heap.hd_address o) ==
             read_word g' (GC.Spec.Heap.hd_address o))
    = wosize_of_object_bound obj g;
      wosize_of_object_bound o g;
      GC.Spec.Heap.hd_address_spec o;
      GC.Spec.Heap.hd_address_spec obj;
      if o = obj then ()
      else if U64.v o < U64.v obj then objects_separated zero_addr g o obj
      else objects_separated zero_addr g obj o;
      read_write_different g addr (GC.Spec.Heap.hd_address o) v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires headers_stable);
  let aux3 (src: obj_addr) (dst: obj_addr) : Lemma
    (requires Seq.mem src (objects zero_addr g') /\
              (let wz = wosize_of_object src g' in
               U64.v wz < pow2 54 /\
               exists_field_pointing_to_unchecked g' src wz dst))
    (ensures GC.Spec.Object.infix_addr_wf g' (objects zero_addr g') dst)
    = aux2 src dst;
      GC.Spec.Object.infix_addr_wf_locality g g' (objects zero_addr g) dst
  in
  well_formed_heap_part3_intro g' aux3;
  // Part 4: non-infix preserved (is_infix reads header, write_word is to body)
  let aux4 (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr g'))
    (ensures ~(GC.Spec.Object.is_infix h g'))
  = // is_infix depends on tag_of_object which reads header at hd_address h
    // Show: write_word at addr doesn't change header at hd_address h
    // Therefore is_infix h g' == is_infix h g, and ~(is_infix h g) from well_formed_heap
    GC.Spec.Heap.hd_address_spec h;
    GC.Spec.Heap.hd_address_spec obj;
    if h = obj then begin
      // addr >= obj = hd_address obj + 8, so addr > hd_address obj
      // hd_address obj + mword <= addr, so they don't overlap
      GC.Spec.Heap.read_write_different g addr (GC.Spec.Heap.hd_address h) v
    end else begin
      // h ≠ obj: objects are separated, addr is within obj's body, hd_address h is outside
      wosize_of_object_bound obj g;
      wosize_of_object_bound h g;
      if U64.v h < U64.v obj then
        objects_separated zero_addr g h obj
      else
        objects_separated zero_addr g obj h;
      GC.Spec.Heap.read_write_different g addr (GC.Spec.Heap.hd_address h) v
    end;
    GC.Spec.Object.is_infix_spec h g;
    GC.Spec.Object.is_infix_spec h g';
    GC.Spec.Object.tag_of_object_spec h g;
    GC.Spec.Object.tag_of_object_spec h g'
  in
  let aux4_imp (h: obj_addr) : Lemma
    (Seq.mem h (objects zero_addr g') ==> ~(GC.Spec.Object.is_infix h g'))
  = FStar.Classical.move_requires aux4 h
  in
    FStar.Classical.forall_intro aux4_imp;
  // Reconstruct well_formed_heap for the modified heap
  reveal_opaque (`%well_formed_heap) well_formed_heap
#pop-options
