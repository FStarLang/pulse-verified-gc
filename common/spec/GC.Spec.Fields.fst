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

/// The sources whose fields the collector is obliged to keep well formed.
///
/// A no-scan object --- a `string`, a `Bytes.t`, a `Bigarray` payload, a
/// `Custom` block --- holds arbitrary bytes, and eight of them may perfectly
/// well spell an 8-aligned in-range address.  Neither the extracted C nor the
/// graph model reads such a word: `is_scannable` in the implementation and
/// `GC.Spec.HeapGraph.get_pointer_fields` both stop at the tag.  So the
/// field-closure clauses below must stop at the tag too, or they demand a
/// property of the mutator's data that OCaml does not have.
///
/// Free (blue) blocks are excluded too.  Nothing in the collector reads a free
/// block's body beyond its free-list link: mark only scans grey objects, sweep
/// and coalesce read headers and colours, the generational pointer update skips
/// blue objects, and the allocator reads the header and field 0.  So a dead
/// object's stale fields may stay in the block after it is freed --- the sweep
/// does not zero them --- and `GC.Spec.HeapGraph.get_pointer_fields` returns no
/// edges for a blue block, matching this clause.  The link word itself is
/// constrained by the free-list invariants (`fl_valid`,
/// `GC.Gen.FreeListShape.blue_link_fields_valid`), not here.
///
/// The colour dependence is one-directional in practice: colour changes made
/// by mark (white -> grey -> black) and sweep (black -> white) never involve
/// blue, sweeping white -> blue only drops obligations, and the one place a
/// blue block becomes live --- allocation --- hands out a block whose fields
/// the caller overwrites before anything reads them (`copy_fields` on
/// promotion; the runtime on direct allocation).
let fields_constrained (g: heap) (src: obj_addr) : GTot bool =
  not (GC.Spec.Object.is_no_scan src g) && not (GC.Spec.Object.is_blue src g)

/// ---------------------------------------------------------------------------
/// Well-formedness except the objects pending free
/// ---------------------------------------------------------------------------
///
/// The field-closure clauses (parts 2 and 3) are also stated *except* a set of
/// objects pending free, `pf`: objects known dead but not yet reclaimed (in the
/// middle of a sweep, the white objects in front of the cursor).  Such an
/// object is garbage left in place; its fields are never read, so they may
/// point anywhere, free blocks included.  The heap invariant knows nothing
/// about who decides what is pending: stop-the-world, and while idle or
/// marking, nothing is (`no_pending`), and a collector phase that leaves
/// garbage in place supplies its own set.
///
/// The constrained objects are those `not_freed g pf`: on the walk, not free
/// (blue), and not pending free.  The set `pf` is fixed across an operation
/// that does not reclaim anything (a field write, an allocation, a minor
/// collection), while `not_freed` is read off the heap, so newly allocated
/// objects are constrained automatically.

/// Neither free nor pending free.
let not_freed (g: heap) (pf: obj_addr -> prop) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ ~(pf x)

/// A pending set is admissible for `g` when every member is a real, non-free
/// block of the walk.
let pending_ok (g: heap) (pf: obj_addr -> prop) : prop =
  forall (x: obj_addr). pf x ==> Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)

/// Nothing is pending free: the stop-the-world (and idle, and marking) case.
/// (F* has no default arguments, so this case is a named instance.)
let no_pending (x: obj_addr) : prop = False

let no_pending_ok (g: heap) : Lemma (pending_ok g no_pending) = ()

/// Part 2 except the pending objects: every field of a not-freed, scannable
/// object points (after resolving infix pointers) at a not-freed object.
///
/// At `no_pending` this is part 2 (`well_formed_heap_part2`).
[@@"opaque_to_smt"]
let well_formed_heap_part2_except (g: heap) (pf: obj_addr -> prop) : prop =
  (forall (src dst: obj_addr).
    (not_freed g pf src /\ fields_constrained g src /\
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==>
    not_freed g pf (GC.Spec.Object.resolve_object dst g))

/// Eliminate part 2 except the pending objects at a single (src, dst) pair.
let wfh_part2_except_elim (g: heap) (pf: obj_addr -> prop) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_part2_except g pf /\ not_freed g pf src /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures not_freed g pf (GC.Spec.Object.resolve_object dst g))
  = reveal_opaque (`%well_formed_heap_part2_except) well_formed_heap_part2_except

/// Introduce part 2 except the pending objects from the pointwise obligation.
let well_formed_heap_part2_except_intro (g: heap) (pf: obj_addr -> prop)
    (h: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires not_freed g pf src /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures not_freed g pf (GC.Spec.Object.resolve_object dst g)))
  : Lemma (well_formed_heap_part2_except g pf)
  = reveal_opaque (`%well_formed_heap_part2_except) well_formed_heap_part2_except;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (not_freed g pf src /\ fields_constrained g src /\
         (let wz = wosize_of_object src g in
          U64.v wz < pow2 54 /\
          exists_field_pointing_to_unchecked g src wz dst)) ==>
        not_freed g pf (GC.Spec.Object.resolve_object dst g))
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (h src))
    in
    FStar.Classical.forall_intro aux


/// Part 2 --- the field-closure clause --- is the `no_pending` instance of
/// `well_formed_heap_part2_except`: every field of an enumerated, scannable,
/// non-free object resolves to an enumerated, non-free object.  In particular
/// nothing the collector scans points into a free block.
///
/// The except form is `opaque_to_smt`, and deliberately so.  It is the clause
/// that decides which heaps the collector is willing to accept.  Sealing it
/// means the *only* file that can see its body is this one, so a change to its
/// shape breaks a handful of accessor lemmas here rather than silently
/// reshaping proof obligations across a hundred client modules.  Cross the
/// boundary with `wfh_part2_elim` / `well_formed_heap_part2_intro`, or with the
/// derived accessors further down (`wf_field_target_in_objects`,
/// `points_to_target_not_blue` and friends).
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
let well_formed_heap_part2 (g: heap) : prop = well_formed_heap_part2_except g no_pending

/// Eliminate part 2 at a single (src, dst) pair.  (A constrained source is
/// not blue, so it is not freed.)
let wfh_part2_elim (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_part2 g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
           ~(is_blue (GC.Spec.Object.resolve_object dst g) g))
  = wfh_part2_except_elim g no_pending src dst

/// Introduce part 2 from the pointwise obligation.
let well_formed_heap_part2_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
                     ~(is_blue (GC.Spec.Object.resolve_object dst g) g)))
  : Lemma (well_formed_heap_part2 g)
  = let h (src: obj_addr) (dst: obj_addr) : Lemma
      (requires not_freed g no_pending src /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures not_freed g no_pending (GC.Spec.Object.resolve_object dst g))
      = pf src dst
    in
    well_formed_heap_part2_except_intro g no_pending h

/// Convenience intro: if every pointer field target is *itself* enumerated
/// and not free, part 2 follows.  This is the shape most producers of
/// well-formed heaps naturally prove, and it is sound because part 4 keeps
/// infix objects out of `objects`, so an enumerated target resolves to itself.
let well_formed_heap_part2_intro_raw (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g)))
  : Lemma (requires well_formed_heap_part4 g)
          (ensures well_formed_heap_part2 g)
  = let pf' (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
               ~(is_blue (GC.Spec.Object.resolve_object dst g) g))
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
///
/// It is the `no_pending` instance of `well_formed_heap_part3_except` below
/// (`well_formed_heap_part3`):
/// with nothing pending, `not_freed` is "on the walk and not blue", and
/// `fields_constrained` already excludes blue sources, so the sources checked
/// are exactly "on the walk and constrained".
///
/// Part 3 except the pending objects: the fields of a not-freed, scannable
/// object have valid interior pointers.
[@@"opaque_to_smt"]
let well_formed_heap_part3_except (g: heap) (pf: obj_addr -> prop) : prop =
  (forall (src dst: obj_addr).
    (not_freed g pf src /\ fields_constrained g src /\
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==>
    GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)

/// Eliminate part 3 except the pending objects at a single (src, dst) pair.
let wfh_part3_except_elim (g: heap) (pf: obj_addr -> prop) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_part3_except g pf /\ not_freed g pf src /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = reveal_opaque (`%well_formed_heap_part3_except) well_formed_heap_part3_except

/// Introduce part 3 except the pending objects from the pointwise obligation.
let well_formed_heap_part3_except_intro (g: heap) (pf: obj_addr -> prop)
    (h: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires not_freed g pf src /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst))
  : Lemma (well_formed_heap_part3_except g pf)
  = reveal_opaque (`%well_formed_heap_part3_except) well_formed_heap_part3_except;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (not_freed g pf src /\ fields_constrained g src /\
         (let wz = wosize_of_object src g in
          U64.v wz < pow2 54 /\
          exists_field_pointing_to_unchecked g src wz dst)) ==>
        GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (h src))
    in
    FStar.Classical.forall_intro aux

/// Part 3, with nothing pending.
let well_formed_heap_part3 (g: heap) : prop = well_formed_heap_part3_except g no_pending

/// Eliminate part 3 at a single (src, dst) pair.
let wfh_part3_elim (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_part3 g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = wfh_part3_except_elim g no_pending src dst

let well_formed_heap_part3_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst))
  : Lemma (well_formed_heap_part3 g)
  = let pf' (src: obj_addr) (dst: obj_addr) : Lemma
      (requires not_freed g no_pending src /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = pf src dst
    in
    well_formed_heap_part3_except_intro g no_pending pf'

/// Convenience intro for heaps with no infix field targets at all: part 3 is
/// then vacuous.  Producers that already know their targets are enumerated
/// (hence non-infix, by part 4) can use this.
let well_formed_heap_part3_intro_no_infix (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures ~(GC.Spec.Object.is_infix dst g)))
  : Lemma (well_formed_heap_part3 g)
  = let pf' (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = pf src dst;
        GC.Spec.Object.infix_addr_wf_non_infix g (objects zero_addr g) dst
    in
    well_formed_heap_part3_intro g pf'

/// Transport parts 2 and 3 across a heap change that preserves the object
/// enumeration and every address's header interpretation, blueness included
/// (part 2 constrains blue sources not at all and blue targets absolutely).
/// Colour changes among white, grey and black, and tag rewrites, are the
/// canonical instances: they leave `objects`, `is_infix`, `is_closure`,
/// `is_blue`, `wosize_of_object` and hence `resolve_object` alone, so both
/// clauses carry over verbatim once the field-pointer structure is transported
/// by `fields`.
let well_formed_heap_part2_3_transport (g: heap) (g': heap)
    (fields: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g') /\ fields_constrained g' src /\
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
                       GC.Spec.Object.is_no_scan h g' == GC.Spec.Object.is_no_scan h g /\
                       GC.Spec.Object.is_blue h g' == GC.Spec.Object.is_blue h g /\
                       GC.Spec.Object.wosize_of_object h g' == GC.Spec.Object.wosize_of_object h g /\
                       GC.Spec.Object.resolve_object h g' == GC.Spec.Object.resolve_object h g))
          (ensures well_formed_heap_part2 g' /\ well_formed_heap_part3 g')
  = let pf2 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g') /\ fields_constrained g' src /\
                (let wz = wosize_of_object src g' in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g' src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g') (objects zero_addr g') /\
               ~(is_blue (GC.Spec.Object.resolve_object dst g') g'))
      = fields src dst;
        wfh_part2_elim g src dst
    in
    well_formed_heap_part2_intro g' pf2;
    let pf3 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g') /\ fields_constrained g' src /\
                (let wz = wosize_of_object src g' in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g' src wz dst))
      (ensures GC.Spec.Object.infix_addr_wf g' (objects zero_addr g') dst)
      = fields src dst;
        wfh_part3_elim g src dst;
        GC.Spec.Object.infix_addr_wf_congr g g' (objects zero_addr g) dst
    in
    well_formed_heap_part3_intro g' pf3

/// Well-formedness except the objects pending free: parts 1 and 4 are about
/// the walk and unchanged; parts 2 and 3 constrain only the fields of not-freed
/// objects.  Sealed; cross the boundary with `wf_except_parts` (or `wf_parts`
/// for `well_formed_heap`).
[@@"opaque_to_smt"]
let well_formed_heap_except (g: heap) (pf: obj_addr -> prop) : prop =
  well_formed_heap_part1 g /\
  well_formed_heap_part2_except g pf /\
  well_formed_heap_part3_except g pf /\
  well_formed_heap_part4 g

let wf_except_parts (_: unit) : Lemma
  (ensures forall (g: heap) (pf: obj_addr -> prop).
             well_formed_heap_except g pf <==>
             (well_formed_heap_part1 g /\
              well_formed_heap_part2_except g pf /\
              well_formed_heap_part3_except g pf /\
              well_formed_heap_part4 g))
  = reveal_opaque (`%well_formed_heap_except) well_formed_heap_except

/// Well-formedness: the `no_pending` instance.  Stop-the-world, idle and
/// during marking nothing is pending free, so the heap is well formed when
/// every constrained object's fields resolve to enumerated, non-free objects
/// with valid interior pointers.  This is the one notion of well-formedness;
/// `well_formed_heap` is only its name.
let well_formed_heap (g: heap) : prop = well_formed_heap_except g no_pending

/// A `points_to` target of a not-freed scannable object is not freed, and a
/// valid interior pointer if it is one.
let points_to_target_except (g: heap) (pf: obj_addr -> prop) (src dst: obj_addr) : Lemma
  (requires well_formed_heap_except g pf /\ not_freed g pf src /\ fields_constrained g src /\
            points_to g src dst)
  (ensures not_freed g pf (GC.Spec.Object.resolve_object dst g) /\
           GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = wf_except_parts ();
    wosize_of_object_bound src g;
    wfh_part2_except_elim g pf src dst;
    wfh_part3_except_elim g pf src dst

/// The single sanctioned way to cross the `well_formed_heap` abstraction
/// boundary.  `well_formed_heap` is the sealed `well_formed_heap_except` at
/// `no_pending`, so clients that need to see its four conjuncts must unfold
/// it; doing that with a bare `reveal_opaque` scatters the unfolding across
/// the development and makes it impossible to tell which clients actually
/// depend on which part.
///
/// It is a biconditional, so it serves both directions: decomposing a
/// hypothesis and assembling a goal.
let wf_parts (_: unit) : Lemma
  (ensures forall (g: heap).
             well_formed_heap g <==>
             (well_formed_heap_part1 g /\
              well_formed_heap_part2 g /\
              well_formed_heap_part3 g /\
              well_formed_heap_part4 g))
  = wf_except_parts ()

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
/// field of every object without consulting the tag.  That demands field
/// closure for words the collector never reads, and this invariant is what
/// assumes the demand away.
///
/// The invariant is restricted to non-blue objects because blue (free-list)
/// objects have their first field repurposed as the free-list pointer, and the
/// rest of a free block's body is not part of the model at all
/// (`fields_constrained` excludes blue objects): the sweep
/// (`GC.Spec.FusedSweep`) leaves a dead object's stale words in the free block
/// that absorbs it.
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
  = wf_parts ()

/// Extract part 1 without hd_address (for cross-module use with HeapGraph.object_fits_in_heap)
/// Since hd_address h = h - 8 for obj_addr h, we get: h + wosize*8 <= Seq.length g
let wf_object_bound (g: heap) (h: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem h (objects zero_addr g))
  (ensures U64.v h + op_Star (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  = wf_parts ();
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
  = wf_parts ()

/// In a well-formed heap, resolve_object is identity for objects in the list
/// (Because objects are non-infix, resolve returns self)
let wf_resolve_identity (g: heap) (x: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g))
  (ensures GC.Spec.Object.resolve_object x g == x)
  = wf_objects_non_infix g x;
    GC.Spec.Object.resolve_non_infix x g

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
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
  = wf_parts ();
    wfh_part2_elim g src dst

/// Part 3 at a field target: an infix field target has a valid enclosing closure.
let wf_field_target_infix_wf (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
  = wf_parts ();
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
    Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
    (let wz = wosize_of_object src g in
     U64.v wz < pow2 54 /\
     exists_field_pointing_to_unchecked g src wz dst) ==>
    ~(GC.Spec.Object.is_infix dst g)

let no_infix_field_targets_elim (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires no_infix_field_targets g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            (let wz = wosize_of_object src g in
             U64.v wz < pow2 54 /\
             exists_field_pointing_to_unchecked g src wz dst))
  (ensures ~(GC.Spec.Object.is_infix dst g))
  = reveal_opaque (`%no_infix_field_targets) no_infix_field_targets

let no_infix_field_targets_intro (g: heap)
    (pf: (src: obj_addr) -> (dst: obj_addr) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures ~(GC.Spec.Object.is_infix dst g)))
  : Lemma (no_infix_field_targets g)
  = reveal_opaque (`%no_infix_field_targets) no_infix_field_targets;
    let aux (src: obj_addr) : Lemma
      (forall (dst: obj_addr).
        (Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
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
            fields_constrained g src /\ points_to g src dst)
  (ensures ~(GC.Spec.Object.is_infix dst g))
  = wosize_of_object_bound src g;
    no_infix_field_targets_elim g src dst

/// The pre-infix conclusion, recovered when the target is known non-infix.
let wf_field_target_in_objects_raw (g: heap) (src: obj_addr) (dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
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
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      (let wz = wosize_of_object src g in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked g src wz dst))
            (ensures Seq.mem dst (objects zero_addr g)))
  : Lemma (requires well_formed_heap_part4 g)
          (ensures no_infix_field_targets g)
  = let pf (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\
                 exists_field_pointing_to_unchecked g src wz dst))
      (ensures ~(GC.Spec.Object.is_infix dst g))
      = raw src dst
    in
    no_infix_field_targets_intro g pf

/// Combined: field read + pointer target → target ∈ objects.
/// Internalizes wf_object_size_bound + field_read_implies_exists_pointing + wf_field_target_in_objects.
let field_pointer_target_in_objects (g: heap) (h: obj_addr)
    (k: U64.t{U64.v k < pow2 61}) (target: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem h (objects zero_addr g) /\ fields_constrained g h /\
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
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            points_to g src dst)
  (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g))
  = wosize_of_object_bound src g;
    wf_field_target_in_objects g src dst

/// Part 2 at a `points_to` target: nothing a constrained object points at is
/// free.
let points_to_target_not_blue (g: heap) (src dst: obj_addr) : Lemma
  (requires well_formed_heap g /\ Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
            points_to g src dst)
  (ensures ~(is_blue (GC.Spec.Object.resolve_object dst g) g))
  = wf_parts ();
    wosize_of_object_bound src g;
    wfh_part2_elim g src dst

/// Derive well_formed_heap_part2 from a per-field closure property.
/// If every pointer-valued field of every object targets another, non-free
/// object, then well_formed_heap_part2 holds.
///
/// The field_closure hypothesis says: for any object src in objects, and any field index j,
/// if the field value is a pointer, then it targets a non-free object in the objects list.
/// From this we derive that efptu(g, src, wz, dst) = false for all dst ∉ objects,
/// which is well_formed_heap_part2.
#push-options "--z3rlimit 12 --fuel 1 --ifuel 1"
let well_formed_heap_part2_from_field_closure (g: heap)
    (field_closure: (src: obj_addr) -> (j: nat) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\ j < U64.v (wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g) /\
                                       ~(is_blue (v <: obj_addr) g))))
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part4 g)
    (ensures well_formed_heap_part2 g /\ well_formed_heap_part3 g /\
             no_infix_field_targets g)
  = let aux (src dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      U64.v (wosize_of_object src g) < pow2 54 /\
                      exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst)
            (ensures Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g))
    = if Seq.mem dst (objects zero_addr g) && not (is_blue dst g) then ()
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
                field_closure src idx
                // Contradicts the case split, since fv == dst
              end else ()
            end
        in
        Classical.forall_intro field_not_dst;
        efptu_false_if_no_field_matches g src wz dst
      end
    in
    let aux_wrapped (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g))
      = aux src dst
    in
    well_formed_heap_part2_intro_raw g aux_wrapped;
    // Part 3 is vacuous here: every field target is enumerated, and part 4
    // keeps infix objects out of the enumeration.
    let aux_non_infix (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures ~(GC.Spec.Object.is_infix dst g))
      = aux src dst
    in
    well_formed_heap_part3_intro_no_infix g aux_non_infix;
    no_infix_field_targets_intro g aux_non_infix
#pop-options

/// Resolved analogue of `well_formed_heap_part2_from_field_closure`.
///
/// The raw version demands that every pointer-valued field hold an *enumerated*
/// address.  Part 4 keeps infix objects out of the enumeration, so that demand
/// silently forbids interior pointers, and any producer that goes through it
/// inherits the restriction.  This version demands only what parts 2 and 3
/// actually say: the field's *resolved* target is enumerated and not free, and the raw value
/// is a well-formed infix address (trivially true when it is not infix).
///
/// It is the introduction rule for producers that walk fields index by index --
/// the Cheney collector's `update_major_pointers` is the motivating one -- and
/// want to stay infix-correct.  Note that it does *not* conclude
/// `no_infix_field_targets`, which is the whole point.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let well_formed_heap_part2_3_from_resolved_field_closure (g: heap)
    (field_closure: (src: obj_addr) -> (j: nat) ->
      Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      j < U64.v (wosize_of_object src g) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==>
                      Seq.mem (GC.Spec.Object.resolve_object (v <: obj_addr) g)
                              (objects zero_addr g) /\
                      ~(is_blue (GC.Spec.Object.resolve_object (v <: obj_addr) g) g) /\
                      GC.Spec.Object.infix_addr_wf g (objects zero_addr g)
                              (v <: obj_addr))))
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part4 g)
    (ensures well_formed_heap_part2 g /\ well_formed_heap_part3 g)
  = let contra (src: obj_addr) (dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                      U64.v (wosize_of_object src g) < pow2 54 /\
                      ~(Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
                        ~(is_blue (GC.Spec.Object.resolve_object dst g) g) /\
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
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
               ~(is_blue (GC.Spec.Object.resolve_object dst g) g) /\
               GC.Spec.Object.infix_addr_wf g (objects zero_addr g) dst)
      = Classical.move_requires (contra src) dst
    in
    let aux2 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                (let wz = wosize_of_object src g in
                 U64.v wz < pow2 54 /\ exists_field_pointing_to_unchecked g src wz dst))
      (ensures Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g) /\
               ~(is_blue (GC.Spec.Object.resolve_object dst g) g))
      = aux src dst
    in
    let aux3 (src: obj_addr) (dst: obj_addr) : Lemma
      (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
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
/// Heap density
/// ---------------------------------------------------------------------------

/// The objects walk never stops early: from every object header, if the next
/// position has room for a header, the walk continues there and the object at
/// that position is in the global list.  Only object header positions are
/// constrained, so the zero words inside a large block (phantom wosize-0
/// objects, not in the global walk) are excluded.
///
/// Used by both collectors: the fused sweep's walk relies on it of the marked
/// heap (`GC.Spec.FusedSweep.Inv.sweep_g0`), and the generational invariant
/// `major_heap_shape` carries it.
///
/// Opaque to SMT, so a quantifier this size stays out of the large mark and
/// sweep contexts; `reveal_opaque (`%heap_objects_dense) heap_objects_dense`
/// unfolds it where a proof needs it.
[@@"opaque_to_smt"]
let heap_objects_dense (g: heap) : prop =
  forall (start: hp_addr).
    U64.v start + 8 < heap_size ==>
    Seq.mem (f_address start) (objects zero_addr g) ==>
    Seq.length (objects start g) > 0 ==>
    (let wz = getWosize (read_word g start) in
     let next = U64.v start + ((U64.v wz + 1) * 8) in
     next + 8 < heap_size ==>
     Seq.length (objects (U64.uint_to_t next) g) > 0 /\
     Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g))
