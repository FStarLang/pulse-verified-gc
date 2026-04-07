(*
   GC.Spec.Allocator.Lemmas — Bridge proofs connecting the allocator to the GC.

   Main theorem: alloc_spec preserves well_formed_heap, so the GC can be
   called after any sequence of allocations.
*)
module GC.Spec.Allocator.Lemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq
open FStar.Mul

/// ===========================================================================
/// Section 1: Preliminary lemmas about make_header
/// ===========================================================================

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

/// Arithmetic characterization of make_header:
#push-options "--z3rlimit 400 "
private let make_header_value (wz: U64.t{U64.v wz < pow2 54})
                              (c: U64.t{U64.v c < 4})
                              (t: U64.t{U64.v t < 256})
  : Lemma (U64.v (make_header wz c t) == U64.v wz * 1024 + U64.v c * 256 + U64.v t)
  = let open FStar.UInt in
    let w = U64.v wz in
    let cv = U64.v c in
    let tv = U64.v t in
    shift_left_value_lemma #64 w 10;
    assert_norm (pow2 10 = 1024);
    assert_norm (pow2 54 * 1024 = pow2 64);
    assert (w * 1024 < pow2 64);
    FStar.Math.Lemmas.small_mod (w * 1024) (pow2 64);
    shift_left_value_lemma #64 cv 8;
    assert_norm (pow2 8 = 256);
    assert (cv * 256 < pow2 64);
    FStar.Math.Lemmas.small_mod (cv * 256) (pow2 64);
    FStar.Math.Lemmas.multiple_modulo_lemma cv 256;
    logor_disjoint #64 (cv * 256) tv 8;
    FStar.Math.Lemmas.multiple_modulo_lemma w 1024;
    assert (cv * 256 + tv <= 3 * 256 + 255);
    assert_norm (3 * 256 + 255 < 1024);
    logor_disjoint #64 (w * 1024) (cv * 256 + tv) 10
#pop-options

/// getWosize of make_header returns the original wosize
#push-options "--z3rlimit 400 "
let make_header_getWosize (wz: U64.t{U64.v wz < pow2 54})
                          (c: U64.t{U64.v c < 4})
                          (t: U64.t{U64.v t < 256})
  : Lemma (getWosize (make_header wz c t) == wz)
  = let hdr = make_header wz c t in
    getWosize_spec hdr;
    make_header_value wz c t;
    let rest = U64.v c * 256 + U64.v t in
    assert (rest < 1024);
    assert_norm (pow2 10 = 1024);
    FStar.Math.Lemmas.lemma_div_plus rest (U64.v wz) 1024;
    FStar.Math.Lemmas.small_div rest 1024;
    assert (U64.v hdr / 1024 == U64.v wz)
#pop-options

/// getTag of make_header returns the original tag
#push-options "--z3rlimit 400 "
let make_header_getTag (wz: U64.t{U64.v wz < pow2 54})
                       (c: U64.t{U64.v c < 4})
                       (t: U64.t{U64.v t < 256})
  : Lemma (U64.v (getTag (make_header wz c t)) == U64.v t)
  = getTag_spec (make_header wz c t);
    make_header_value wz c t;
    FStar.UInt.logand_mask #64 (U64.v (make_header wz c t)) 8;
    assert_norm (pow2 8 - 1 = 255);
    assert_norm (U64.v 0xFFUL = 255);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v t) (U64.v c) 256;
    FStar.Math.Lemmas.lemma_mod_plus (U64.v c * 256 + U64.v t) (U64.v wz * 4) 256;
    FStar.Math.Lemmas.small_mod (U64.v t) 256
#pop-options

/// ===========================================================================
/// Section 2: Header write with same wosize preserves objects
/// ===========================================================================

/// If getWosize is the same at every header position, objects walk is the same
private let rec wosize_eq_implies_objects_eq
  (start: hp_addr) (g g': heap)
  : Lemma (requires Seq.length g' == Seq.length g /\
                    (forall (p: hp_addr). getWosize (read_word g' p) == getWosize (read_word g p)))
          (ensures objects start g' == objects start g)
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let wz = getWosize (read_word g start) in
      let next_start_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else if next_start_nat >= heap_size then ()
      else wosize_eq_implies_objects_eq (U64.uint_to_t next_start_nat) g g'
    end

/// A write to hd_address(obj) with same getWosize preserves objects from 0
let header_write_same_wosize_preserves_objects
  (g: heap) (obj: obj_addr) (new_hdr: U64.t)
  : Lemma (requires getWosize new_hdr == getWosize (read_word g (hd_address obj)))
          (ensures objects 0UL (write_word g (hd_address obj) new_hdr) == objects 0UL g)
  = let hd = hd_address obj in
    let g' = write_word g hd new_hdr in
    hd_address_spec obj;
    let aux (p: hp_addr) : Lemma (getWosize (read_word g' p) == getWosize (read_word g p))
      = if U64.v p = U64.v hd then
          read_write_same g hd new_hdr
        else
          read_write_different g hd p new_hdr
    in
    FStar.Classical.forall_intro aux;
    wosize_eq_implies_objects_eq 0UL g g'

/// ===========================================================================
/// Section 3: exists_field_pointing_to_unchecked congruence
/// ===========================================================================

/// If all field reads of src are the same in g' and g, then efptu is the same
private let rec efptu_congruence
  (g g': heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma (requires (forall (k: nat{k < U64.v wz}).
                       let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
                       U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                       read_word g' fa == read_word g fa))
          (ensures exists_field_pointing_to_unchecked g' src wz dst ==
                   exists_field_pointing_to_unchecked g src wz dst)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      let fa = U64.add_mod src (U64.mul_mod idx mword) in
      if U64.v fa >= heap_size || U64.v fa % 8 <> 0 then ()
      else begin
        assert (U64.v idx < U64.v wz);
        efptu_congruence g' g src idx dst
      end
    end

/// Monotonicity: efptu with smaller wosize implies efptu with bigger wosize.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 0"
private let rec efptu_monotone
  (g: heap) (src: obj_addr) (small_wz: U64.t{U64.v small_wz < pow2 54}) (big_wz: U64.t{U64.v big_wz < pow2 54}) (dst: obj_addr)
  : Lemma (requires U64.v small_wz <= U64.v big_wz /\
                    well_formed_object g src /\
                    U64.v big_wz <= U64.v (wosize_of_object src g) /\
                    exists_field_pointing_to_unchecked g src small_wz dst)
          (ensures exists_field_pointing_to_unchecked g src big_wz dst)
          (decreases U64.v big_wz)
  = if big_wz = 0UL then ()
    else if small_wz = big_wz then ()
    else begin
      let idx = U64.sub big_wz 1UL in
      hd_address_spec src;
      let wz_obj = wosize_of_object src g in
      assert (U64.v src + U64.v wz_obj * 8 <= heap_size);
      assert (U64.v idx < U64.v wz_obj);
      assert (U64.v src + U64.v idx * 8 < heap_size);
      FStar.Math.Lemmas.pow2_lt_compat 57 54;
      assert (U64.v idx * 8 < pow2 57);
      FStar.Math.Lemmas.pow2_lt_compat 64 57;
      FStar.Math.Lemmas.modulo_lemma (U64.v idx * U64.v mword) (pow2 64);
      assert (U64.v (U64.mul_mod idx mword) == U64.v idx * 8);
      assert (U64.v src + U64.v idx * 8 < pow2 57 + pow2 57);
      FStar.Math.Lemmas.pow2_double_sum 57;
      FStar.Math.Lemmas.pow2_lt_compat 64 58;
      FStar.Math.Lemmas.modulo_lemma (U64.v src + U64.v idx * 8) (pow2 64);
      let fa = U64.add_mod src (U64.mul_mod idx mword) in
      assert (U64.v fa == U64.v src + U64.v idx * 8);
      assert (U64.v fa < heap_size);
      assert (U64.v fa % 8 == 0);
      let fv = read_word g (fa <: hp_addr) in
      if is_pointer_to fv dst then ()
      else efptu_monotone g src small_wz idx dst
    end
#pop-options

/// ===========================================================================
/// Section 4: Header write at hd_address(obj) doesn't change field reads
/// ===========================================================================

/// For src = obj: fields at obj + k*8 are all > hd_address obj = obj - 8
/// hd_address(obj) = obj - 8, so obj + k*8 > obj - 8 for all k >= 0.
///
/// Proof uses a custom NL step to avoid Z3 4.13.3 arith.solver 6 limitations
/// with chaining through k*8 terms.
#restart-solver
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

/// Helper: if (a * b) % n == a * b and (c + a * b) % n == c + a * b,
/// then for any x with (c + x) % n == c + x and x == (a * b) % n,
/// we get x == a * b and c + x < n.
/// This helper avoids the NL chain in the main proof.
private let mul_mod_add_mod_helper
  (k: nat) (obj_v: nat)
  : Lemma (requires k < pow2 54 /\ obj_v < pow2 57)
          (ensures (let km_v = (k * 8) % pow2 64 in
                    let fa_v = (obj_v + km_v) % pow2 64 in
                    km_v == k * 8 /\
                    fa_v == obj_v + km_v /\
                    obj_v + km_v < pow2 64))
  = FStar.Math.Lemmas.nat_times_nat_is_nat k 8;
    FStar.Math.Lemmas.lemma_mult_lt_right 8 k (pow2 54);
    assert_norm (pow2 54 * 8 == pow2 57);
    assert_norm (pow2 57 < pow2 64);
    FStar.Math.Lemmas.small_mod (k * 8) (pow2 64);
    assert_norm (pow2 57 + pow2 57 == pow2 58);
    assert_norm (pow2 58 < pow2 64);
    FStar.Math.Lemmas.small_mod (obj_v + k * 8) (pow2 64)

/// Bridge lemma: if a == c and b == d then a * b == c * d.
/// Z3 can't do this under arith.solver 6 — write it as a standalone lemma.
private let mul_cong (a b c d: nat)
  : Lemma (requires a == c /\ b == d)
          (ensures a * b == c * d)
  = ()

private let header_write_doesnt_change_own_fields_aux
  (g: heap) (obj: obj_addr) (new_hdr: U64.t) (k: nat)
  (fa: U64.t) (hd: hp_addr)
  : Lemma (requires k < U64.v (wosize_of_object obj g) /\
                    fa == U64.add_mod obj (U64.mul_mod (U64.uint_to_t k) mword) /\
                    hd == hd_address obj /\
                    U64.v fa < heap_size /\ U64.v fa % 8 == 0)
          (ensures read_word (write_word g hd new_hdr) fa == read_word g fa)
  = hd_address_spec obj;
    wosize_of_object_bound obj g;
    assert_norm (pow2 54 < pow2 64);
    // Connect U64 operations to nat arithmetic via mul_cong
    // U64.v (uint_to_t k) == k, U64.v mword == 8
    mul_cong (U64.v (U64.uint_to_t k)) (U64.v mword) k 8;
    // Now Z3 knows: U64.v (uint_to_t k) * U64.v mword == k * 8
    // So (U64.v (uint_to_t k) * U64.v mword) % pow2 64 == (k * 8) % pow2 64
    // Use helper to establish mod-arithmetic facts
    mul_mod_add_mod_helper k (U64.v obj);
    // Helper gives: (k * 8) % pow2 64 == k * 8 /\ (obj_v + k*8) % pow2 64 == obj_v + k*8
    // So U64.v (mul_mod ...) == k * 8, and U64.v fa == U64.v obj + k * 8
    // hd == obj - 8, so hd + 8 <= obj <= obj + k * 8 == fa
    assert (U64.v hd + U64.v mword <= U64.v fa);
    read_write_different g hd fa new_hdr
#pop-options

#push-options "--z3rlimit 20"
let header_write_doesnt_change_own_fields
  (g: heap) (obj: obj_addr) (new_hdr: U64.t) (k: nat)
  : Lemma (requires k < U64.v (wosize_of_object obj g))
          (ensures (let fa = U64.add_mod obj (U64.mul_mod (U64.uint_to_t k) mword) in
                    let hd = hd_address obj in
                    U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                    read_word (write_word g hd new_hdr) fa == read_word g fa))
  = wosize_of_object_bound obj g;
    assert_norm (pow2 54 < pow2 64);
    let fa = U64.add_mod obj (U64.mul_mod (U64.uint_to_t k) mword) in
    let hd = hd_address obj in
    if U64.v fa < heap_size && U64.v fa % 8 = 0
    then header_write_doesnt_change_own_fields_aux g obj new_hdr k fa hd
    else ()
#pop-options

/// For src ≠ obj: all fields of src are separated from hd_address(obj)
#push-options "--z3rlimit 30"
let header_write_doesnt_change_other_fields
  (g: heap) (obj src: obj_addr) (new_hdr: U64.t) (k: nat)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    Seq.mem src (objects 0UL g) /\
                    src <> obj /\
                    k < U64.v (wosize_of_object src g))
          (ensures (let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
                    let hd = hd_address obj in
                    U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                    read_word (write_word g hd new_hdr) fa == read_word g fa))
  = let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
    let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_spec src;
    wosize_of_object_bound src g;
    wosize_of_object_bound obj g;
    wf_object_size_bound g src;
    if U64.v fa < heap_size && U64.v fa % 8 = 0 then begin
      if U64.v src < U64.v obj then
        objects_separated 0UL g src obj
      else
        objects_separated 0UL g obj src;
      read_write_different g hd fa new_hdr
    end
#pop-options

/// ===========================================================================
/// Section 5: Exact-fit preserves well_formed_heap
/// ===========================================================================

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let alloc_exact_preserves_wf
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz < 2))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap g' /\
                    objects 0UL g' == objects 0UL g))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let new_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
    let g' = write_word g hd new_hdr in
    hd_address_spec obj;
    hd_address_bounds obj;
    getWosize_bound hdr;
    make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;

    // Objects preserved
    header_write_same_wosize_preserves_objects g obj new_hdr;

    // Access well_formed_heap parts
    reveal_opaque (`%well_formed_heap) well_formed_heap;

    // --- Part 1: size bounds ---
    let aux1 (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g'))
      (ensures (let w = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + U64.v w * 8 <= Seq.length g'))
    = wosize_of_object_spec h g;
      wosize_of_object_spec h g';
      wosize_of_object_bound h g;
      hd_address_spec h;
      if h = obj then
        read_write_same g hd new_hdr
      else begin
        if U64.v h < U64.v obj then
          objects_separated 0UL g h obj
        else
          objects_separated 0UL g obj h;
        read_write_different g hd (hd_address h) new_hdr
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux1);

    // --- Part 2: pointer targets ---
    let aux2 (src dst: obj_addr) : Lemma
      (requires Seq.mem src (objects 0UL g') /\
                (let w = wosize_of_object src g' in
                 U64.v w < pow2 54 /\
                 exists_field_pointing_to_unchecked g' src w dst))
      (ensures Seq.mem dst (objects 0UL g'))
    = wosize_of_object_spec src g;
      wosize_of_object_spec src g';
      wosize_of_object_bound src g;
      hd_address_spec src;
      if src = obj then
        read_write_same g hd new_hdr
      else begin
        if U64.v src < U64.v obj then
          objects_separated 0UL g src obj
        else
          objects_separated 0UL g obj src;
        read_write_different g hd (hd_address src) new_hdr
      end;
      let wz_src = wosize_of_object src g in
      let field_eq (k: nat{k < U64.v wz_src}) : Lemma
        (let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
         U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
         read_word g' fa == read_word g fa)
      = if src = obj then
          header_write_doesnt_change_own_fields g obj new_hdr k
        else
          header_write_doesnt_change_other_fields g obj src new_hdr k
      in
      FStar.Classical.forall_intro field_eq;
      efptu_congruence g' g src wz_src dst
    in
    let aux2_imp (src dst: obj_addr) : Lemma
      ((Seq.mem src (objects 0UL g') /\
        U64.v (wosize_of_object src g') < pow2 54 /\
        exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst) ==>
       Seq.mem dst (objects 0UL g'))
    = FStar.Classical.move_requires (aux2 src) dst
    in
    FStar.Classical.forall_intro_2 aux2_imp;

    // --- Part 3: infix_wf (vacuous: no infix objects exist) ---
    // We'll prove part 4 first (no infix objects), then use it for part 3.
    // Part 4 proof:
    let not_infix (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g'))
      (ensures ~(is_infix h g'))
    = is_infix_spec h g';
      tag_of_object_spec h g';
      hd_address_spec h;
      if h = obj then begin
        read_write_same g hd new_hdr;
        make_header_getTag (U64.uint_to_t block_wz) white_bits 0UL;
        infix_tag_val ();
        // getTag new_hdr has value 0, infix_tag has value 249
        // tag_of_object h g' = getTag (read_word g' hd) = getTag new_hdr
        // U64.v (getTag new_hdr) == 0, U64.v infix_tag == 249
        assert (tag_of_object h g' <> infix_tag)
      end else begin
        if U64.v h < U64.v obj then
          objects_separated 0UL g h obj
        else
          objects_separated 0UL g obj h;
        read_write_different g hd (hd_address h) new_hdr;
        is_infix_spec h g;
        tag_of_object_spec h g
      end
    in
    // Part 3: infix_wf holds because no object is infix
    let no_infix_pf (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g') /\ is_infix h g')
      (ensures (let p = parent_closure_addr_nat h g' in
                p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                Seq.mem (U64.uint_to_t p) (objects 0UL g') /\
                is_closure (U64.uint_to_t p) g'))
    = not_infix h  // Derives ~(is_infix h g'), contradicting requires
    in
    infix_wf_intro g' (objects 0UL g') no_infix_pf;

    // --- Part 4: no infix objects ---
    let aux4_imp (h: obj_addr) : Lemma
      (Seq.mem h (objects 0UL g') ==> ~(is_infix h g'))
    = FStar.Classical.move_requires not_infix h
    in
    FStar.Classical.forall_intro aux4_imp
#pop-options

/// ===========================================================================
/// Section 6: Split case — alloc_from_block with split preserves wf
/// ===========================================================================

/// The split case creates a new object boundary. This requires proving
/// that the new objects list is the old list with one block replaced by two.
/// This is the hardest part of the allocator-GC bridge.

/// ---------------------------------------------------------------------------
/// 6a: Helper: objects from next_hd are unchanged after split
/// ---------------------------------------------------------------------------

/// After the three writes (at hd, rem_hd, rem_obj), all of which are < next_hd,
/// the objects walk from next_hd is unchanged.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let split_next_hd_objects_eq
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2))
          (ensures (let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let block_wz = U64.v (getWosize hdr) in
                    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                    let (g3, _) = alloc_from_block g obj wz next_fp in
                    next_hd_nat < heap_size ==>
                    (let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
                     objects next_hd g3 == objects next_hd g)))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
    hd_address_spec obj;
    hd_address_bounds obj;
    wf_object_size_bound g obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    // Establish bounds for rem_hd and rem_obj
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    // block_wz >= wz + 2, so next_hd >= hd + (wz+3)*8 > rem_obj = hd + (wz+1)*8 + 8
    assert (next_hd_nat >= rem_obj_nat + 8);
    assert (rem_hd_nat < heap_size);
    assert (rem_obj_nat < heap_size);
    // Use alloc_from_block_split_normal to unfold
    alloc_from_block_split_normal g obj wz next_fp;
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd alloc_hdr in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_wz = block_wz - wz - 1 in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    let g2 = write_word g1 rem_hd rem_hdr in
    let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
    let g3 = write_word g2 rem_obj next_fp in
    if next_hd_nat < heap_size then begin
      let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
      // Chain: objects(next_hd, g3) = objects(next_hd, g2) = ... = objects(next_hd, g)
      // Each step: write_word_preserves_objects_before because write addr < next_hd
      write_word_preserves_objects_before next_hd g2 rem_obj next_fp;
      write_word_preserves_objects_before next_hd g1 rem_hd rem_hdr;
      write_word_preserves_objects_before next_hd g hd alloc_hdr
    end
#pop-options

/// ---------------------------------------------------------------------------
/// 6b-pre0: objects_nonempty_first_mem — first element is a member
/// ---------------------------------------------------------------------------

/// If objects(start, g) is non-empty (contains any h), then f_address start
/// is also a member (it's the first element).
#restart-solver
#push-options "--z3rlimit 20 --fuel 2 --ifuel 0"
private let objects_nonempty_first_mem
  (start: hp_addr) (g: heap) (h: obj_addr)
  : Lemma (requires Seq.mem h (objects start g))
          (ensures Seq.mem (f_address start) (objects start g))
  = // objects start g is non-empty, so it must be of the form
    // Seq.cons (f_address start) rest, meaning f_address start is a member
    if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let next_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        if next_nat >= heap_size then
          mem_cons_lemma first first (Seq.empty #obj_addr)
        else
          mem_cons_lemma first first (objects (U64.uint_to_t next_nat <: hp_addr) g)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// 6b-pre: objects_later_in_earlier — objects at later walk positions
/// ---------------------------------------------------------------------------

/// If h ∈ objects(later, g) and later is at a reachable object boundary from start
/// (i.e., f_address later ∈ objects start g), then h ∈ objects(start, g).
#restart-solver
#push-options "--z3rlimit 400 --fuel 3 --ifuel 1"
private let rec objects_later_in_earlier
  (start: hp_addr) (g: heap) (later: hp_addr) (h: obj_addr)
  : Lemma (requires U64.v start <= U64.v later /\
                    Seq.mem h (objects later g) /\
                    (U64.v start = U64.v later \/ Seq.mem (f_address later) (objects start g)))
          (ensures Seq.mem h (objects start g))
          (decreases (Seq.length g - U64.v start))
  = if U64.v start = U64.v later then ()
    else if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz_start = getWosize header in
      let next_nat = U64.v start + (U64.v wz_start + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then
        () //A: objects start g = Seq.empty, later >= start so objects later g = empty too
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        if next_nat >= heap_size then begin
          // objects start g = Seq.cons first Seq.empty
          // From precondition: Seq.mem (f_address later) (objects start g)
          // So f_address later = first = f_address start, meaning later = start
          // But we're in the start != later branch — contradiction
          mem_cons_lemma (f_address later) first (Seq.empty #obj_addr);
          f_address_spec later;
          assert (f_address later = first);
          assert (U64.v later = U64.v start) // contradiction with start != later
        end
        else begin
          let next_hp : hp_addr = U64.uint_to_t next_nat in
          mem_cons_lemma (f_address later) first (objects next_hp g);
          if f_address later = first then begin
            // f_address later = f_address start, so later = start — contradiction
            f_address_spec later;
            assert (U64.v later = U64.v start)
          end
          else begin
            // f_address later ∈ objects next_hp g (from mem_cons_lemma)
            // Need: next_hp <= later for the recursive call
            objects_addresses_gt_start next_hp g (f_address later);
            f_address_spec later;
            // f_address later >= f_address next_hp, i.e., later + 8 >= next_hp + 8
            assert (U64.v next_hp <= U64.v later);
            objects_later_in_earlier next_hp g later h;
            mem_cons_lemma h first (objects next_hp g)
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// 6b: split_old_mem_in_new — objects(0,g) ⊆ objects(0,g3)
/// ---------------------------------------------------------------------------

/// If h ∈ objects(start, g), then h ∈ objects(start, g3).
/// Walk from start in g; at positions before hd, g3 agrees; at hd, handle split.
#push-options "--z3rlimit 400 --fuel 2 --ifuel 0"
private let rec split_old_mem_in_new
  (start: hp_addr) (g g3: heap)
  (obj: obj_addr) (wz block_wz: nat)
  (h: obj_addr)
  : Lemma (requires
      Seq.length g3 == Seq.length g /\
      well_formed_heap g /\
      Seq.mem obj (objects 0UL g) /\
      (let hd = hd_address obj in
       let hdr = read_word g hd in
       U64.v (getWosize hdr) == block_wz /\
       block_wz >= wz /\ block_wz - wz >= 2 /\
       (let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
        let rem_obj_nat = rem_hd_nat + 8 in
        let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
        rem_hd_nat < heap_size /\
        rem_obj_nat < heap_size /\
        next_hd_nat <= heap_size /\
        // g3 agrees with g before hd
        (forall (p: hp_addr). U64.v p < U64.v hd ==> read_word g3 p == read_word g p) /\
        // g3 header at hd has wosize = wz
        getWosize (read_word g3 hd) == U64.uint_to_t wz /\
        // g3 header at rem_hd has wosize = block_wz - wz - 1
        (rem_hd_nat < heap_size ==>
          getWosize (read_word g3 (U64.uint_to_t rem_hd_nat <: hp_addr)) == U64.uint_to_t (block_wz - wz - 1)) /\
        // objects from next_hd agree
        (next_hd_nat < heap_size ==>
          objects (U64.uint_to_t next_hd_nat <: hp_addr) g3 == objects (U64.uint_to_t next_hd_nat <: hp_addr) g) /\
        // start is at or before hd
        U64.v start <= U64.v hd)) /\
      Seq.mem h (objects start g) /\
      // Loop invariant: start is a valid object boundary from 0
      (U64.v start = 0 \/ Seq.mem (f_address start) (objects 0UL g)))
    (ensures Seq.mem h (objects start g3))
    (decreases (Seq.length g - U64.v start))
  = let hd = hd_address obj in
    hd_address_spec obj;
    if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header_g = read_word g start in
      let wz_g = getWosize header_g in
      let next_nat = U64.v start + (U64.v wz_g + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        mem_cons_lemma h first
          (if next_nat >= heap_size then Seq.empty
           else objects (U64.uint_to_t next_nat <: hp_addr) g);
        if U64.v start = U64.v hd then begin
          // At the split point
          let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
          let rem_obj_nat = rem_hd_nat + 8 in
          let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
          assert (first == obj);
          // In g3: objects(hd, g3) = cons obj (objects(rem_hd, g3))
          // Need to unfold objects at hd in g3
          let header_g3 = read_word g3 hd in
          assert (getWosize header_g3 == U64.uint_to_t wz);
          let next_g3 = U64.v hd + (wz + 1) * 8 in
          assert (next_g3 == rem_hd_nat);
          if h = first then begin
            // h = obj is the head of objects(start, g3)
            // Need to show objects(start, g3) is non-empty and head = obj
            assert (U64.v start + 8 < Seq.length g3);
            assert (next_g3 <= Seq.length g3);
            assert (next_g3 < pow2 64);
            if next_g3 >= heap_size then
              mem_cons_lemma h obj (Seq.empty #obj_addr)
            else begin
              let rem_hd_hp : hp_addr = U64.uint_to_t rem_hd_nat in
              mem_cons_lemma h obj (objects rem_hd_hp g3)
            end
          end else begin
            // h ∈ objects(next_hd, g) (tail in g's walk from hd)
            // next_hd_nat < heap_size (since objects(hd,g) has more than just obj)
            assert (next_nat == next_hd_nat);
            if next_hd_nat >= heap_size then begin
              // Singleton in g: objects(hd, g) = [obj], so h = obj, contradiction
              ()
            end else begin
              let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
              assert (Seq.mem h (objects next_hd g));
              // objects(next_hd, g3) == objects(next_hd, g)
              assert (objects next_hd g3 == objects next_hd g);
              assert (Seq.mem h (objects next_hd g3));
              // Now push h into objects(rem_hd, g3) then objects(hd, g3)
              let rem_hd_hp : hp_addr = U64.uint_to_t rem_hd_nat in
              // objects(rem_hd, g3) starts with rem_obj then objects(next_hd, g3)
              f_address_spec rem_hd_hp;
              let rem_obj_addr : obj_addr = f_address rem_hd_hp in
              assert (U64.v rem_obj_addr == rem_obj_nat);
              // Unfold: objects(rem_hd, g3)
              // read_word g3 rem_hd → getWosize = block_wz - wz - 1
              // next from rem_hd in g3 = rem_hd + (block_wz-wz-1+1)*8 = rem_hd + (block_wz-wz)*8
              //                        = hd + (1+wz)*8 + (block_wz-wz)*8 = hd + 8 + block_wz*8
              //                        = hd + (block_wz+1)*8 = next_hd
              let rem_wz = block_wz - wz - 1 in
              let next_from_rem = rem_hd_nat + (rem_wz + 1) * 8 in
              assert (next_from_rem == next_hd_nat);
              // h ∈ objects(next_hd, g3), so h ∈ objects(rem_hd, g3) via mem_cons_lemma
              if next_hd_nat >= heap_size then
                mem_cons_lemma h rem_obj_addr (Seq.empty #obj_addr)
              else
                mem_cons_lemma h rem_obj_addr (objects next_hd g3);
              // h ∈ objects(rem_hd, g3), so h ∈ objects(hd, g3) via mem_cons_lemma
              mem_cons_lemma h obj (objects rem_hd_hp g3)
            end
          end
        end else begin
          // start < hd: g3 agrees with g at start
          assert (U64.v start < U64.v hd);
          assert (read_word g3 start == read_word g start);
          let header_g3 = read_word g3 start in
          assert (header_g3 == header_g);
          assert (getWosize header_g3 == wz_g);
          if h = first then begin
            // h is the head; objects(start, g3) also starts with first
            if next_nat >= heap_size then
              mem_cons_lemma h first (Seq.empty #obj_addr)
            else
              mem_cons_lemma h first (objects (U64.uint_to_t next_nat <: hp_addr) g3)
          end else begin
            // h is in tail; recurse
            if next_nat >= heap_size then ()
            else begin
              let next_hp : hp_addr = U64.uint_to_t next_nat in
              assert (Seq.mem h (objects next_hp g));
              // Prove next_nat <= hd using objects_separated + alignment
              // Step 1: first ∈ objects(0, g) via objects_later_in_earlier
              mem_cons_lemma first first
                (if next_nat >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_nat <: hp_addr) g);
              assert (Seq.mem first (objects start g));
              objects_later_in_earlier 0UL g start first;
              assert (Seq.mem first (objects 0UL g));
              // Step 2: Use objects_separated on first and obj
              hd_address_spec first;
              wosize_of_object_spec first g;
              objects_separated 0UL g first obj;
              // Gives: U64.v obj > U64.v first + U64.v wz_g * 8
              //      = (U64.v start + 8) + U64.v wz_g * 8
              // So: U64.v hd = U64.v obj - 8 > U64.v start + U64.v wz_g * 8
              // Step 3: Alignment — both hd and (start + wz_g*8) are multiples of 8
              assert (U64.v hd % 8 == 0);
              assert (U64.v start % 8 == 0);
              FStar.Math.Lemmas.cancel_mul_mod (U64.v wz_g) 8;
              assert ((U64.v start + U64.v wz_g * 8) % 8 == 0);
              assert (U64.v hd > U64.v start + U64.v wz_g * 8);
              // positive multiple of 8 is >= 8, so hd >= start + wz_g*8 + 8 = next_nat
              assert (next_nat <= U64.v hd);
              // Establish loop invariant for recursive call:
              // Need: Seq.mem (f_address next_hp) (objects 0UL g)
              // h ∈ objects next_hp g, so f_address next_hp ∈ objects next_hp g
              objects_nonempty_first_mem next_hp g h;
              // f_address next_hp ∈ objects next_hp g, so via mem_cons it's in objects start g
              mem_cons_lemma (f_address next_hp) first (objects next_hp g);
              // And from objects start g to objects 0UL g
              objects_later_in_earlier 0UL g start (f_address next_hp);
              split_old_mem_in_new next_hp g g3 obj wz block_wz h;
              mem_cons_lemma h first (objects next_hp g3)
            end
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// 6c: split_new_mem_in_old_or_rem — objects(0,g3) ⊆ objects(0,g) ∪ {rem_obj}
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 400 --fuel 2 --ifuel 0"
private let rec split_new_mem_in_old_or_rem
  (start: hp_addr) (g g3: heap)
  (obj: obj_addr) (wz block_wz: nat)
  (h: obj_addr)
  : Lemma (requires
      Seq.length g3 == Seq.length g /\
      well_formed_heap g /\
      Seq.mem obj (objects 0UL g) /\
      (let hd = hd_address obj in
       let hdr = read_word g hd in
       U64.v (getWosize hdr) == block_wz /\
       block_wz >= wz /\ block_wz - wz >= 2 /\
       (let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
        let rem_obj_nat = rem_hd_nat + 8 in
        let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
        rem_hd_nat < heap_size /\
        rem_obj_nat < heap_size /\
        next_hd_nat <= heap_size /\
        (forall (p: hp_addr). U64.v p < U64.v hd ==> read_word g3 p == read_word g p) /\
        getWosize (read_word g3 hd) == U64.uint_to_t wz /\
        (rem_hd_nat < heap_size ==>
          getWosize (read_word g3 (U64.uint_to_t rem_hd_nat <: hp_addr)) == U64.uint_to_t (block_wz - wz - 1)) /\
        (next_hd_nat < heap_size ==>
          objects (U64.uint_to_t next_hd_nat <: hp_addr) g3 == objects (U64.uint_to_t next_hd_nat <: hp_addr) g) /\
        U64.v start <= U64.v hd)) /\
      Seq.mem h (objects start g3) /\
      // Loop invariants: start is a valid object boundary from 0 in g
      (U64.v start = 0 \/ Seq.mem (f_address start) (objects 0UL g)) /\
      // obj is reachable from start in g (needed to show next_hp is a boundary)
      Seq.mem obj (objects start g))
    (ensures (let rem_hd_nat = U64.v (hd_address obj) + (1 + wz) * 8 in
              let rem_obj_nat = rem_hd_nat + 8 in
              Seq.mem h (objects start g) \/ U64.v h == rem_obj_nat))
    (decreases (Seq.length g3 - U64.v start))
  = let hd = hd_address obj in
    hd_address_spec obj;
    if U64.v start + 8 >= Seq.length g3 then ()
    else begin
      let header_g3 = read_word g3 start in
      let wz_g3 = getWosize header_g3 in
      let next_nat_g3 = U64.v start + (U64.v wz_g3 + 1) * 8 in
      if next_nat_g3 > Seq.length g3 || next_nat_g3 >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        mem_cons_lemma h first
          (if next_nat_g3 >= heap_size then Seq.empty
           else objects (U64.uint_to_t next_nat_g3 <: hp_addr) g3);
        if U64.v start = U64.v hd then begin
          // At the split point in g3: walk visits obj then rem_obj
          let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
          let rem_obj_nat = rem_hd_nat + 8 in
          let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
          assert (first == obj);
          assert (next_nat_g3 == rem_hd_nat);
          if h = first then begin
            // h = obj is also in objects(start, g) as head
            let header_g = read_word g start in
            let wz_g = getWosize header_g in
            let next_nat_g = U64.v start + (U64.v wz_g + 1) * 8 in
            assert (next_nat_g == next_hd_nat);
            if next_hd_nat >= heap_size then
              mem_cons_lemma h obj (Seq.empty #obj_addr)
            else
              mem_cons_lemma h obj (objects (U64.uint_to_t next_hd_nat <: hp_addr) g)
          end else begin
            // h ∈ objects(rem_hd, g3)
            if rem_hd_nat >= heap_size then ()
            else begin
              let rem_hd_hp : hp_addr = U64.uint_to_t rem_hd_nat in
              assert (Seq.mem h (objects rem_hd_hp g3));
              // Unfold objects at rem_hd in g3
              f_address_spec rem_hd_hp;
              let rem_obj_addr : obj_addr = f_address rem_hd_hp in
              assert (U64.v rem_obj_addr == rem_obj_nat);
              let rem_wz = block_wz - wz - 1 in
              let next_from_rem = rem_hd_nat + (rem_wz + 1) * 8 in
              assert (next_from_rem == next_hd_nat);
              mem_cons_lemma h rem_obj_addr
                (if next_hd_nat >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_hd_nat <: hp_addr) g3);
              if h = rem_obj_addr then begin
                // h = rem_obj
                assert (U64.v h == rem_obj_nat)
              end else begin
                // h ∈ objects(next_hd, g3) = objects(next_hd, g)
                if next_hd_nat >= heap_size then ()
                else begin
                  let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
                  assert (Seq.mem h (objects next_hd g3));
                  assert (objects next_hd g3 == objects next_hd g);
                  assert (Seq.mem h (objects next_hd g));
                  // Push into objects(start, g)
                  let header_g = read_word g start in
                  let next_nat_g = U64.v start + (U64.v (getWosize header_g) + 1) * 8 in
                  assert (next_nat_g == next_hd_nat);
                  mem_cons_lemma h obj (objects next_hd g)
                end
              end
            end
          end
        end else begin
          // start < hd: g3 agrees with g at start
          assert (read_word g3 start == read_word g start);
          if h = first then begin
            // h is head in both
            let header_g = read_word g start in
            let next_nat_g = U64.v start + (U64.v (getWosize header_g) + 1) * 8 in
            if next_nat_g >= heap_size then
              mem_cons_lemma h first (Seq.empty #obj_addr)
            else
              mem_cons_lemma h first (objects (U64.uint_to_t next_nat_g <: hp_addr) g)
          end else begin
            // h in tail; recurse
            if next_nat_g3 >= heap_size then ()
            else begin
              let next_hp : hp_addr = U64.uint_to_t next_nat_g3 in
              // Prove next_nat_g3 <= hd using objects_separated + alignment
              // g3 agrees with g at start (start < hd), so wz_g3 = wz in g at start
              let header_g_here = read_word g start in
              assert (header_g3 == header_g_here);
              let wz_g_here = getWosize header_g_here in
              assert (wz_g3 == wz_g_here);
              // first ∈ objects(start, g) via agreement
              mem_cons_lemma first first
                (if next_nat_g3 >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_nat_g3 <: hp_addr) g);
              assert (Seq.mem first (objects start g));
              objects_later_in_earlier 0UL g start first;
              // objects_separated gives obj > first + wz_g_here * 8
              hd_address_spec first;
              wosize_of_object_spec first g;
              objects_separated 0UL g first obj;
              // Alignment: hd > start + wz_g_here*8, both mult of 8, so hd >= next_nat_g3
              assert (U64.v hd % 8 == 0);
              assert (U64.v start % 8 == 0);
              FStar.Math.Lemmas.cancel_mul_mod (U64.v wz_g_here) 8;
              assert ((U64.v start + U64.v wz_g_here * 8) % 8 == 0);
              assert (U64.v hd > U64.v start + U64.v wz_g_here * 8);
              assert (next_nat_g3 <= U64.v hd);
              // Establish loop invariants for recursive call
              // 1. obj ∈ objects next_hp g (from obj ∈ objects start g, obj ≠ first)
              let next_nat_g = U64.v start + (U64.v wz_g_here + 1) * 8 in
              assert (next_nat_g == next_nat_g3);
              mem_cons_lemma obj first
                (if next_nat_g >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_nat_g <: hp_addr) g);
              assert (obj <> first);
              // 2. f_address next_hp ∈ objects 0UL g
              objects_nonempty_first_mem next_hp g obj;
              mem_cons_lemma (f_address next_hp) first (objects next_hp g);
              objects_later_in_earlier 0UL g start (f_address next_hp);
              split_new_mem_in_old_or_rem next_hp g g3 obj wz block_wz h;
              let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
              let rem_obj_nat = rem_hd_nat + 8 in
              if U64.v h = rem_obj_nat then ()
              else begin
                // h ∈ objects(next_hp, g), push to objects(start, g)
                let next_nat_g = U64.v start + (U64.v wz_g_here + 1) * 8 in
                assert (next_nat_g == next_nat_g3);
                mem_cons_lemma h first (objects next_hp g)
              end
            end
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// 6d: Shared precondition and fact-establishing lemmas
/// ---------------------------------------------------------------------------

let alloc_split_pre (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) : prop =
  well_formed_heap g /\
  Seq.mem obj (objects 0UL g) /\
  (let hdr = read_word g (hd_address obj) in
   let block_wz = U64.v (getWosize hdr) in
   block_wz >= wz /\ block_wz - wz >= 2) /\
  (is_pointer_field next_fp ==> Seq.mem next_fp (objects 0UL g))

/// Per-point g3 agreement: at any hp_addr p that is not one of the 3 write
/// positions, g3 returns the same read_word as g.
#restart-solver
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
private let alloc_split_g3_agrees
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (p: hp_addr)
  : Lemma (requires alloc_split_pre g obj wz next_fp /\
                    (let hd = hd_address obj in
                     let hdr = read_word g hd in
                     let block_wz = U64.v (getWosize hdr) in
                     let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                     let rem_obj_nat = rem_hd_nat + 8 in
                     U64.v p <> U64.v hd /\
                     U64.v p <> rem_hd_nat /\
                     U64.v p <> rem_obj_nat))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    read_word g3 p == read_word g p))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    wf_object_size_bound g obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    alloc_from_block_split_normal g obj wz next_fp;
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd alloc_hdr in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_wz = block_wz - wz - 1 in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    let g2 = write_word g1 rem_hd rem_hdr in
    let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
    let g3 = write_word g2 rem_obj next_fp in
    // p ≠ rem_obj, p ≠ rem_hd, p ≠ hd
    read_write_different g2 rem_obj p next_fp;
    read_write_different g1 rem_hd p rem_hdr;
    read_write_different g hd p alloc_hdr
#pop-options

/// Establish ALL common facts from alloc_split_pre.
#restart-solver
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
private let alloc_split_facts
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires alloc_split_pre g obj wz next_fp)
          (ensures (let hd = hd_address obj in
                    let hdr = read_word g hd in
                    let block_wz = U64.v (getWosize hdr) in
                    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                    let rem_obj_nat = rem_hd_nat + 8 in
                    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                    let rem_wz = block_wz - wz - 1 in
                    // Bounds
                    rem_hd_nat >= 8 /\
                    rem_obj_nat >= 16 /\
                    rem_hd_nat < heap_size /\
                    rem_obj_nat < heap_size /\
                    next_hd_nat <= heap_size /\
                    rem_hd_nat % 8 == 0 /\
                    rem_obj_nat % 8 == 0 /\
                    rem_hd_nat < pow2 64 /\
                    rem_obj_nat < pow2 64 /\
                    next_hd_nat < pow2 64 /\
                    // Wosize bounds
                    wz < pow2 54 /\
                    rem_wz < pow2 54 /\
                    // Header roundtrips
                    getWosize (make_header (U64.uint_to_t wz) white_bits 0UL) == U64.uint_to_t wz /\
                    getWosize (make_header (U64.uint_to_t rem_wz) blue_bits 0UL) == U64.uint_to_t rem_wz /\
                    // alloc_from_block result
                    (let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                     let g1 = write_word g hd alloc_hdr in
                     let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
                     let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
                     let g2 = write_word g1 rem_hd rem_hdr in
                     let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
                     let g3 = write_word g2 rem_obj next_fp in
                     alloc_from_block g obj wz next_fp == (g3, rem_obj) /\
                     Seq.length g3 == Seq.length g /\
                      // g3 header values (full read_word equalities for tag proofs)
                      read_word g3 hd == alloc_hdr /\
                      read_word g3 rem_hd == rem_hdr /\
                     // g3 header at hd
                     getWosize (read_word g3 hd) == U64.uint_to_t wz /\
                     // g3 header at rem_hd
                     getWosize (read_word g3 rem_hd) == U64.uint_to_t rem_wz /\
                     // objects from next_hd agree
                     (next_hd_nat < heap_size ==>
                       objects (U64.uint_to_t next_hd_nat <: hp_addr) g3 ==
                       objects (U64.uint_to_t next_hd_nat <: hp_addr) g))))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    wf_object_size_bound g obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
    let rem_wz = block_wz - wz - 1 in
    // Wosize bounds: block_wz < pow2 54, wz < block_wz, rem_wz < block_wz
    assert (wz < pow2 54);
    assert (rem_wz < pow2 54);
    // Header roundtrips
    make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
    make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
    // Unfold alloc_from_block
    alloc_from_block_split_normal g obj wz next_fp;
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd alloc_hdr in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    let g2 = write_word g1 rem_hd rem_hdr in
    let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
    let g3 = write_word g2 rem_obj next_fp in
    // g3 header at hd: read through two later writes
    read_write_different g2 rem_obj hd next_fp;
    read_write_different g1 rem_hd hd rem_hdr;
    read_write_same g hd alloc_hdr;
    // g3 header at rem_hd: read through one later write
    read_write_different g2 rem_obj rem_hd next_fp;
    read_write_same g1 rem_hd rem_hdr;
    // objects from next_hd
    split_next_hd_objects_eq g obj wz next_fp
#pop-options

/// ---------------------------------------------------------------------------
/// 6e: Sub-lemma: old objects are in new objects list
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 50 --fuel 0 --ifuel 0"
private let alloc_split_old_in_new
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires alloc_split_pre g obj wz next_fp /\
                    Seq.mem h (objects 0UL g))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    Seq.mem h (objects 0UL g3)))
  = alloc_split_facts g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
    let rem_wz = block_wz - wz - 1 in
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd alloc_hdr in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
    let g2 = write_word g1 rem_hd rem_hdr in
    let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
    let g3 = write_word g2 rem_obj next_fp in
    hd_address_spec obj;
    // Establish g3 agreement for positions before hd
    let aux_before (p: hp_addr) : Lemma
      (requires U64.v p < U64.v hd)
      (ensures read_word g3 p == read_word g p)
    = alloc_split_g3_agrees g obj wz next_fp p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
    split_old_mem_in_new 0UL g g3 obj wz block_wz h
#pop-options

/// ---------------------------------------------------------------------------
/// 6g: Sub-lemma: rem_obj is in new objects list
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 100 --fuel 2 --ifuel 0"
private let alloc_split_rem_in_objects
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires alloc_split_pre g obj wz next_fp)
          (ensures (let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
                    is_pointer_field rem_fp /\
                    (is_pointer_field rem_fp ==> Seq.mem rem_fp (objects 0UL g3))))
  = alloc_split_facts g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
    let rem_wz = block_wz - wz - 1 in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let g3 = fst (alloc_from_block g obj wz next_fp) in
    hd_address_spec obj;
    f_address_spec rem_hd;
    let rem_obj_addr : obj_addr = f_address rem_hd in
    // rem_obj is in objects(rem_hd, g3) as the head element
    if next_hd_nat >= heap_size then
      mem_cons_lemma rem_obj_addr rem_obj_addr (Seq.empty #obj_addr)
    else begin
      let next_hd_hp : hp_addr = U64.uint_to_t next_hd_nat in
      mem_cons_lemma rem_obj_addr rem_obj_addr (objects next_hd_hp g3)
    end;
    // rem_obj ∈ objects(rem_hd, g3) → ∈ objects(hd, g3) via mem_cons_lemma
    mem_cons_lemma rem_obj_addr obj (objects rem_hd g3);
    // Need obj ∈ objects(0, g3) to satisfy objects_later_in_earlier precondition
    // f_address hd = f_address (hd_address obj) = obj
    alloc_split_old_in_new g obj wz next_fp obj;
    f_address_spec hd;
    // objects(hd, g3) ⊆ objects(0, g3) via objects_later_in_earlier
    objects_later_in_earlier 0UL g3 hd rem_obj_addr
#pop-options

/// ---------------------------------------------------------------------------
/// 6h: wf Part 1: size bounds in g3
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 50 --fuel 0 --ifuel 0"
private let alloc_split_wf_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires alloc_split_pre g obj wz next_fp)
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part1 g3))
  = alloc_split_facts g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let rem_wz = block_wz - wz - 1 in
    let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
    let rem_obj_addr : obj_addr = U64.uint_to_t rem_obj_nat in
    let (g3, _) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g3))
      (ensures (let w = wosize_of_object h g3 in
                U64.v (hd_address h) + 8 + U64.v w * 8 <= Seq.length g3))
    = wosize_of_object_spec h g3;
      hd_address_spec h;
      // Three cases: h = obj, h = rem_obj_addr, or h is from the old heap
      if h = obj then begin
        // wosize in g3 = wz. hd + 8 + wz*8 <= hd + (block_wz+1)*8 <= heap_size
        read_write_different (fst (alloc_from_block g obj wz next_fp)) (U64.uint_to_t rem_obj_nat <: hp_addr) hd next_fp;
        ()
      end else if h = rem_obj_addr then begin
        // wosize in g3 = rem_wz. rem_hd + 8 + rem_wz*8 = hd + (block_wz+1)*8 <= heap_size
        ()
      end else begin
        // h is from old objects. Its header is unchanged.
        // h ∈ objects(0, g) by split_new_mem_in_old_or_rem
        let aux_before (p: hp_addr) : Lemma
          (requires U64.v p < U64.v hd)
          (ensures read_word g3 p == read_word g p)
        = alloc_split_g3_agrees g obj wz next_fp p
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
        split_new_mem_in_old_or_rem 0UL g g3 obj wz block_wz h;
        // h ∈ objects(0, g) (since h ≠ rem_obj_addr)
        assert (Seq.mem h (objects 0UL g));
        // Header of h is unchanged (h ≠ obj, h ≠ rem_obj_addr, so hd_address h ≠ hd, rem_hd)
        hd_address_spec h;
        wosize_of_object_spec h g;
        wosize_of_object_spec obj g;
        if U64.v h < U64.v obj then begin
          objects_separated 0UL g h obj;
          alloc_split_g3_agrees g obj wz next_fp (hd_address h)
        end else begin
          objects_separated 0UL g obj h;
          // h > obj + wosize_of_object obj g * 8 = obj + block_wz * 8
          // hd_address h = h - 8 > obj + block_wz*8 - 8 = hd + block_wz*8
          // hd + block_wz*8 >= hd + (wz+2)*8 > rem_obj_nat > rem_hd_nat > hd
          assert (U64.v (hd_address h) > U64.v hd + block_wz * 8 - 8);
          assert (U64.v (hd_address h) <> U64.v hd);
          assert (U64.v (hd_address h) <> rem_hd_nat);
          assert (U64.v (hd_address h) <> rem_obj_nat);
          alloc_split_g3_agrees g obj wz next_fp (hd_address h)
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// 6i: wf Part 2 for obj: pointer targets of obj in g3
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 100 --fuel 0 --ifuel 0"
private let alloc_split_wf_part2_obj
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (dst: obj_addr)
  : Lemma (requires alloc_split_pre g obj wz next_fp /\
                    (let (g3, _) = alloc_from_block g obj wz next_fp in
                     let wz_obj = wosize_of_object obj g3 in
                     U64.v wz_obj < pow2 54 /\
                     exists_field_pointing_to_unchecked g3 obj wz_obj dst))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    Seq.mem dst (objects 0UL g3)))
  = alloc_split_facts g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let (g3, _) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    wosize_of_object_spec obj g3;
    wosize_of_object_spec obj g;
    wosize_of_object_bound obj g;
    let wz_obj_g3 = wosize_of_object obj g3 in
    // wz_obj_g3 = getWosize(read_word g3 hd) = U64.uint_to_t wz
    // Fields of obj in g3 (indices 0..wz-1) are unchanged from g (writes at hd, rem_hd, rem_obj don't overlap)
    let field_eq (k: nat{k < U64.v wz_obj_g3}) : Lemma
      (let fa = U64.add_mod obj (U64.mul_mod (U64.uint_to_t k) mword) in
       U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
       read_word g3 fa == read_word g fa)
    = let fa = U64.add_mod obj (U64.mul_mod (U64.uint_to_t k) mword) in
      if U64.v fa < heap_size && U64.v fa % 8 = 0 then begin
        let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
        let rem_obj_nat = rem_hd_nat + 8 in
        // fa = obj + k*8, hd = obj - 8. fa >= obj > hd, so fa ≠ hd.
        // fa < obj + wz*8 (since k < wz). rem_hd = obj + wz*8, rem_obj = obj + (wz+1)*8.
        // So fa < rem_hd and fa < rem_obj. Also fa ≥ obj > hd.
        FStar.Math.Lemmas.pow2_lt_compat 57 54;
        FStar.Math.Lemmas.pow2_lt_compat 64 57;
        FStar.Math.Lemmas.modulo_lemma (k * U64.v mword) (pow2 64);
        FStar.Math.Lemmas.pow2_double_sum 57;
        FStar.Math.Lemmas.pow2_lt_compat 64 58;
        FStar.Math.Lemmas.modulo_lemma (U64.v obj + k * 8) (pow2 64);
        assert (U64.v fa == U64.v obj + k * 8);
        alloc_split_g3_agrees g obj wz next_fp (fa <: hp_addr)
      end
    in
    FStar.Classical.forall_intro field_eq;
    // efptu(g3, obj, wz_obj_g3, dst) → efptu(g, obj, wz_obj_g3, dst) [by congruence]
    efptu_congruence g3 g obj wz_obj_g3 dst;
    // wz_obj_g3 <= block_wz = wosize_of_object obj g
    // efptu(g, obj, wz_obj_g3, dst) → efptu(g, obj, wosize_of_object obj g, dst) [by monotone]
    wf_object_size_bound g obj;
    efptu_monotone g obj wz_obj_g3 (wosize_of_object obj g) dst;
    // dst ∈ objects(0, g) [by well_formed_heap part 2]
    wf_field_target_in_objects g obj dst;
    // dst ∈ objects(0, g3) [by old ⊆ new]
    alloc_split_old_in_new g obj wz next_fp dst
#pop-options

/// ---------------------------------------------------------------------------
/// 6j: wf Part 2 for rem_obj: pointer targets of rem_obj in g3
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 200 --fuel 1 --ifuel 0"
private let rec alloc_split_wf_part2_rem_aux
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (dst: obj_addr)
  (cur_wz: U64.t{U64.v cur_wz < pow2 54})
  : Lemma (requires alloc_split_pre g obj wz next_fp /\
                    (let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
                     is_pointer_field rem_fp /\
                     (is_pointer_field rem_fp ==>
                      (let rem_obj : obj_addr = rem_fp in
                       U64.v cur_wz <= U64.v (wosize_of_object rem_obj g3) /\
                       exists_field_pointing_to_unchecked g3 rem_obj cur_wz dst))))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    Seq.mem dst (objects 0UL g3)))
          (decreases U64.v cur_wz)
  = alloc_split_facts g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
    let rem_obj : obj_addr = rem_fp in
    hd_address_spec obj;
    hd_address_spec rem_obj;
    wosize_of_object_spec rem_obj g3;
    wosize_of_object_bound obj g;
    wf_object_size_bound g obj;
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    if cur_wz = 0UL then ()
    else begin
      let idx = U64.sub cur_wz 1UL in
      FStar.Math.Lemmas.pow2_lt_compat 57 54;
      FStar.Math.Lemmas.pow2_lt_compat 64 57;
      FStar.Math.Lemmas.modulo_lemma (U64.v idx * U64.v mword) (pow2 64);
      FStar.Math.Lemmas.pow2_double_sum 57;
      FStar.Math.Lemmas.pow2_lt_compat 64 58;
      FStar.Math.Lemmas.modulo_lemma (U64.v rem_obj + U64.v idx * 8) (pow2 64);
      let fa = U64.add_mod rem_obj (U64.mul_mod idx mword) in
      assert (U64.v fa == U64.v rem_obj + U64.v idx * 8);
      if U64.v fa >= heap_size || U64.v fa % 8 <> 0 then
        alloc_split_wf_part2_rem_aux g obj wz next_fp dst idx
      else begin
        let fv = read_word g3 (fa <: hp_addr) in
        if is_pointer_to fv dst then begin
          // fa = rem_obj + idx*8 = obj + (wz+1)*8 + idx*8 = obj + (wz+1+idx)*8
          // If idx = 0: fa = rem_obj. read_word g3 rem_obj = next_fp.
          // fv = next_fp, and is_pointer_to next_fp dst means dst = next_fp.
          // By precondition: is_pointer_field next_fp ==> next_fp ∈ objects(0,g).
          // So dst ∈ objects(0,g) → dst ∈ objects(0,g3).
          // If idx > 0: fa = obj + (wz+1+idx)*8, which is > rem_obj.
          // read_word g3 fa = read_word g fa (since fa ≠ hd, rem_hd, rem_obj).
          // In g, this is field (wz+1+idx) of original obj.
          // fv was a pointer to dst in g too, so dst ∈ objects(0,g) → objects(0,g3).
          if U64.v idx = 0 then begin
            // fa = rem_obj. fv = next_fp (was written there).
            // is_pointer_to fv dst → hd_address fv = hd_address dst → fv = dst
            if fv <> dst then hd_address_injective fv dst;
            assert (fv == dst);
            // fv = next_fp, so dst = next_fp. is_pointer_field next_fp is true.
            // By precondition of alloc_split_pre: next_fp ∈ objects(0,g).
            alloc_split_old_in_new g obj wz next_fp dst
          end else begin
            // fa > rem_obj. fa ≠ hd, rem_hd, rem_obj. So read_word g3 fa = read_word g fa.
            alloc_split_g3_agrees g obj wz next_fp (fa <: hp_addr);
            assert (read_word g3 (fa <: hp_addr) == read_word g (fa <: hp_addr));
            // In g: fa = obj + (wz+1+idx)*8. This is field (wz+1+idx) of original obj.
            // wz+1+idx < wz + 1 + (block_wz - wz - 1) = block_wz.
            // So this is a valid field of original obj.
            let field_idx = U64.uint_to_t (wz + 1 + U64.v idx) in
            // field_read_implies_exists_pointing: field_idx points to dst in g → efptu
            FStar.Math.Lemmas.modulo_lemma (U64.v obj + (wz + 1 + U64.v idx) * 8) (pow2 64);
            FStar.Math.Lemmas.modulo_lemma ((wz + 1 + U64.v idx) * U64.v mword) (pow2 64);
            let fa2 = U64.add_mod obj (U64.mul_mod field_idx mword) in
            assert (U64.v fa2 == U64.v obj + (wz + 1 + U64.v idx) * 8);
            assert (U64.v fa == U64.v fa2);
            // Establish field_idx refinement for field_read_implies_exists_pointing
            assert (U64.v idx < block_wz - wz - 1);
            assert (wz + 1 + U64.v idx < block_wz);
            wosize_of_object_spec obj g;
            assert (U64.v field_idx < U64.v (wosize_of_object obj g));
            FStar.Math.Lemmas.pow2_lt_compat 61 54;
            assert (U64.v field_idx < pow2 61);
            field_read_implies_exists_pointing g obj (wosize_of_object obj g) field_idx dst;
            wf_field_target_in_objects g obj dst;
            alloc_split_old_in_new g obj wz next_fp dst
          end
        end else
          alloc_split_wf_part2_rem_aux g obj wz next_fp dst idx
      end
    end
#pop-options

#restart-solver
#push-options "--split_queries always --z3rlimit 50 --fuel 0 --ifuel 0"
private let alloc_split_wf_part2_rem
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (dst: obj_addr)
  : Lemma (requires alloc_split_pre g obj wz next_fp /\
                    (let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
                     is_pointer_field rem_fp /\
                     (is_pointer_field rem_fp ==>
                      (let rem_obj : obj_addr = rem_fp in
                       Seq.mem rem_obj (objects 0UL g3) /\
                       (let wz_rem = wosize_of_object rem_obj g3 in
                        U64.v wz_rem < pow2 54 /\
                        exists_field_pointing_to_unchecked g3 rem_obj wz_rem dst)))))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    Seq.mem dst (objects 0UL g3)))
  = alloc_split_facts g obj wz next_fp;
    let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
    let rem_obj : obj_addr = rem_fp in
    let wz_rem = wosize_of_object rem_obj g3 in
    alloc_split_wf_part2_rem_aux g obj wz next_fp dst wz_rem
#pop-options

/// ---------------------------------------------------------------------------
/// 6k: wf Part 2 for other objects
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 100 --fuel 0 --ifuel 0"
private let alloc_split_wf_part2_other
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (src dst: obj_addr)
  : Lemma (requires alloc_split_pre g obj wz next_fp /\
                    (let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
                     let rem_obj = rem_fp in
                     src <> obj /\ src <> rem_obj /\
                     Seq.mem src (objects 0UL g3) /\
                     (let wz_src = wosize_of_object src g3 in
                      U64.v wz_src < pow2 54 /\
                      exists_field_pointing_to_unchecked g3 src wz_src dst)))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    Seq.mem dst (objects 0UL g3)))
  = alloc_split_facts g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let (g3, _rem_fp) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    hd_address_spec src;
    wosize_of_object_spec src g3;
    wosize_of_object_spec src g;
    wosize_of_object_bound src g;
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    // src ∈ objects(0, g3) and src ≠ obj and src ≠ rem_obj
    // → src ∈ objects(0, g) [by split_new_mem_in_old_or_rem]
    let aux_before (p: hp_addr) : Lemma
      (requires U64.v p < U64.v hd)
      (ensures read_word g3 p == read_word g p)
    = alloc_split_g3_agrees g obj wz next_fp p
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
    split_new_mem_in_old_or_rem 0UL g g3 obj wz block_wz src;
    assert (Seq.mem src (objects 0UL g));
    // src's header is at hd_address(src), which ≠ hd and ≠ rem_hd
    // (because src ≠ obj and src ≠ rem_obj, and objects are non-overlapping)
    wosize_of_object_spec obj g;
    if U64.v src < U64.v obj then begin
      objects_separated 0UL g src obj
    end else begin
      objects_separated 0UL g obj src;
      assert (U64.v src > U64.v obj + U64.v (wosize_of_object_as_wosize obj g) * 8);
      assert (U64.v (hd_address src) > U64.v hd + block_wz * 8 - 8);
      assert (U64.v (hd_address src) <> U64.v hd);
      assert (U64.v (hd_address src) <> rem_hd_nat);
      assert (U64.v (hd_address src) <> rem_obj_nat)
    end;
    alloc_split_g3_agrees g obj wz next_fp (hd_address src);
    assert (wosize_of_object src g3 == wosize_of_object src g);
    // All fields of src in g3 are the same as in g
    // (fields of src are in src's body, which doesn't overlap with the 3 write positions)
    let wz_src = wosize_of_object src g in
    wf_object_size_bound g src;
    let field_eq (k: nat{k < U64.v wz_src}) : Lemma
      (let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
       U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
       read_word g3 fa == read_word g fa)
    = if src = obj then ()
      else
        header_write_doesnt_change_other_fields g obj src
          (make_header (U64.uint_to_t wz) white_bits 0UL) k;
        // Actually that's for a single write. We need to show for all 3 writes.
        // Better: just use alloc_split_g3_agrees for each field address.
        let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
        if U64.v fa < heap_size && U64.v fa % 8 = 0 then
          alloc_split_g3_agrees g obj wz next_fp (fa <: hp_addr)
    in
    FStar.Classical.forall_intro field_eq;
    efptu_congruence g3 g src wz_src dst;
    // dst ∈ objects(0, g)
    wf_field_target_in_objects g src dst;
    // dst ∈ objects(0, g3)
    alloc_split_old_in_new g obj wz next_fp dst
#pop-options

/// ---------------------------------------------------------------------------
/// 6l: wf Part 4: no infix objects in g3
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 50 --fuel 0 --ifuel 0"
private let alloc_split_wf_part4
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires alloc_split_pre g obj wz next_fp)
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part4 g3))
  = alloc_split_facts g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let rem_obj_addr : obj_addr = U64.uint_to_t rem_obj_nat in
    let (g3, _) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    let not_infix (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g3))
      (ensures ~(is_infix h g3))
    = is_infix_spec h g3;
      tag_of_object_spec h g3;
      hd_address_spec h;
      if h = obj then begin
        // Tag = 0 (from make_header ... 0UL), infix_tag = 249
        make_header_getTag (U64.uint_to_t wz) white_bits 0UL;
        infix_tag_val ();
        assert (tag_of_object h g3 <> infix_tag)
      end else if h = rem_obj_addr then begin
        // Tag = 0 (from make_header ... 0UL), infix_tag = 249
        make_header_getTag (U64.uint_to_t (block_wz - wz - 1)) blue_bits 0UL;
        infix_tag_val ();
        assert (tag_of_object h g3 <> infix_tag)
      end else begin
        // h from original objects: header unchanged, so is_infix unchanged
        let aux_before (p: hp_addr) : Lemma
          (requires U64.v p < U64.v hd)
          (ensures read_word g3 p == read_word g p)
        = alloc_split_g3_agrees g obj wz next_fp p
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
        split_new_mem_in_old_or_rem 0UL g g3 obj wz block_wz h;
        assert (Seq.mem h (objects 0UL g));
        wosize_of_object_spec obj g;
        if U64.v h < U64.v obj then begin
          objects_separated 0UL g h obj
        end else begin
          objects_separated 0UL g obj h;
          assert (U64.v h > U64.v obj + U64.v (wosize_of_object_as_wosize obj g) * 8);
          assert (U64.v (hd_address h) > U64.v hd + block_wz * 8 - 8);
          assert (U64.v (hd_address h) <> U64.v hd);
          assert (U64.v (hd_address h) <> rem_hd_nat);
          assert (U64.v (hd_address h) <> rem_obj_nat)
        end;
        alloc_split_g3_agrees g obj wz next_fp (hd_address h);
        is_infix_spec h g;
        tag_of_object_spec h g
      end
    in
    let not_infix_imp (h: obj_addr) : Lemma
      (Seq.mem h (objects 0UL g3) ==> ~(is_infix h g3))
    = FStar.Classical.move_requires not_infix h
    in
    FStar.Classical.forall_intro not_infix_imp
#pop-options

/// ---------------------------------------------------------------------------
/// 6m: alloc_split_preserves_wf — orchestrator
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let alloc_split_preserves_wf
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2) /\
                    (is_pointer_field next_fp ==> Seq.mem next_fp (objects 0UL g)))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap g3))
  = alloc_split_facts g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    let rem_obj_addr : obj_addr = U64.uint_to_t rem_obj_nat in
    let (g3, rem_fp) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;

    // Part 1: size bounds
    alloc_split_wf_part1 g obj wz next_fp;

    // Part 2: pointer targets
    alloc_split_rem_in_objects g obj wz next_fp;
    let aux2 (src dst: obj_addr) : Lemma
      (requires Seq.mem src (objects 0UL g3) /\
                U64.v (wosize_of_object src g3) < pow2 54 /\
                exists_field_pointing_to_unchecked g3 src (wosize_of_object src g3) dst)
      (ensures Seq.mem dst (objects 0UL g3))
    = if src = obj then
        alloc_split_wf_part2_obj g obj wz next_fp dst
      else if src = rem_fp then
        alloc_split_wf_part2_rem g obj wz next_fp dst
      else
        alloc_split_wf_part2_other g obj wz next_fp src dst
    in
    let aux2_imp (src dst: obj_addr) : Lemma
      ((Seq.mem src (objects 0UL g3) /\
        U64.v (wosize_of_object src g3) < pow2 54 /\
        exists_field_pointing_to_unchecked g3 src (wosize_of_object src g3) dst) ==>
       Seq.mem dst (objects 0UL g3))
    = FStar.Classical.move_requires (aux2 src) dst
    in
    FStar.Classical.forall_intro_2 aux2_imp;

    // Part 4: no infix
    alloc_split_wf_part4 g obj wz next_fp;

    // Part 3: infix_wf (vacuous since no objects are infix)
    let no_infix_pf (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g3) /\ is_infix h g3)
      (ensures (let p = parent_closure_addr_nat h g3 in
                p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                Seq.mem (U64.uint_to_t p) (objects 0UL g3) /\
                is_closure (U64.uint_to_t p) g3))
    = ()  // Vacuous: part4 proves ~(is_infix h g3)
    in
    infix_wf_intro g3 (objects 0UL g3) no_infix_pf;

    reveal_opaque (`%well_formed_heap) well_formed_heap
#pop-options

/// ===========================================================================
/// Section 7: alloc_from_block preserves well_formed_heap (combining cases)
/// ===========================================================================

let alloc_from_block_preserves_wf
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz) /\
                    (is_pointer_field next_fp ==> Seq.mem next_fp (objects 0UL g)))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap g'))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    if block_wz - wz >= 2 then
      alloc_split_preserves_wf g obj wz next_fp
    else
      alloc_exact_preserves_wf g obj wz next_fp

/// ===========================================================================
/// Section 8: alloc_search preserves well_formed_heap
/// ===========================================================================

/// Free-list validity: every node in the free list is a member of objects 0UL g.
/// This is an invariant maintained by sweep and allocation.
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_valid (g: heap) (fp: U64.t) (fuel: nat) : Tot prop (decreases fuel) =
  if fuel = 0 then True
  else if fp = 0UL then True
  else if U64.v fp < U64.v mword then True
  else if U64.v fp >= heap_size then True
  else if U64.v fp % U64.v mword <> 0 then True
  else
    Seq.mem fp (objects 0UL g) /\
    U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
    (let hd = hd_address (fp <: obj_addr) in
     let next_fp = read_word g (fp <: obj_addr) in
     U64.v hd + 16 <= heap_size ==>
     next_fp <> fp /\  // no self-loops in the free list
     fl_valid g next_fp (fuel - 1))
#pop-options

/// If fl_valid, cur_fp is a member of objects
let fl_valid_gives_mem (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    fl_valid g fp fuel)
          (ensures Seq.mem fp (objects 0UL g))
  = ()

/// If fl_valid, cur_fp has wosize >= 1
let fl_valid_gives_wosize (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    fl_valid g fp fuel)
          (ensures U64.v (wosize_of_object (fp <: obj_addr) g) >= 1)
  = ()

/// fl_valid for next node
let fl_valid_next (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    fl_valid g fp fuel)
          (ensures (let obj : obj_addr = fp in
                    let hd = hd_address obj in
                    U64.v hd + 16 <= heap_size ==>
                    read_word g obj <> fp /\
                    fl_valid g (read_word g obj) (fuel - 1)))
  = ()

/// next_fp (link to next free block) is in objects if it's a valid pointer
let next_fp_in_objects (g: heap) (obj: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    U64.v (wosize_of_object obj g) >= 1 /\
                    (let hd = hd_address obj in
                     U64.v hd + 16 <= heap_size))
          (ensures (let next = read_word g obj in
                    is_pointer_field next ==>
                    Seq.mem next (objects 0UL g)))
  = let hd = hd_address obj in
    let next = read_word g obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    if is_pointer_field next then begin
      // next = read_word g obj, obj is field 0 of obj
      // obj has wosize >= 1 (since hd + 16 <= heap_size means hd + 8 + 8 <= heap_size,
      // i.e., obj + 8 <= heap_size, which means wosize >= 1)
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      wf_object_size_bound g obj;
      // read_word g obj is the value at field index 0 of obj
      // is_pointer_to next target means hd_address next = hd_address target
      // We need: next ∈ objects(0, g)
      // Use: field 0 of obj is at obj, and read_word g obj = next.
      // is_pointer_field next means next is a valid obj_addr.
      // By wf_field_target_in_objects: if efptu(g, obj, wosize, next), then next ∈ objects.
      // Need to show efptu(g, obj, wosize, next).
      // field_read_implies_exists_pointing: if read_word at field k is a pointer to target,
      // then efptu finds it.
      // Field 0 at address obj + 0*8 = obj. read_word g obj = next.
      // is_pointer_to next next = (is_pointer_field next && hd_address next = hd_address next) = true
      field_read_implies_exists_pointing g obj (wosize_of_object obj g) 0UL next;
      wf_field_target_in_objects g obj next
    end

/// alloc_from_block preserves objects membership and returns rem_fp in objects
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let alloc_from_block_objects_facts
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz) /\
                    (is_pointer_field next_fp ==> Seq.mem next_fp (objects 0UL g)))
          (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                    // Old objects are preserved
                    (forall (h: obj_addr). Seq.mem h (objects 0UL g) ==> Seq.mem h (objects 0UL g')) /\
                    // rem_fp, if a valid pointer, is in objects(0, g')
                    (is_pointer_field rem_fp ==> Seq.mem rem_fp (objects 0UL g'))))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let (g', rem_fp) = alloc_from_block g obj wz next_fp in
    if block_wz - wz >= 2 then begin
      // Split case
      alloc_split_facts g obj wz next_fp;
      // Old objects preserved
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects 0UL g))
        (ensures Seq.mem h (objects 0UL g'))
      = alloc_split_old_in_new g obj wz next_fp h
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      // rem_fp is in objects(0, g')
      alloc_split_rem_in_objects g obj wz next_fp
    end else begin
      // Exact fit case: objects are the same, rem_fp = next_fp
      alloc_exact_preserves_wf g obj wz next_fp;
      // In exact fit: alloc_from_block returns (write_word g hd new_hdr, next_fp)
      // objects are preserved (header_write_same_wosize_preserves_objects)
      let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
      make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj alloc_hdr;
      // rem_fp = next_fp. If pointer, in objects(0,g) = objects(0,g').
      ()
    end
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let rec alloc_search_preserves_wf
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g cur_fp fuel /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects 0UL g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    well_formed_heap r.heap_out))
          (decreases fuel)
  = if fuel = 0 then ()
    else if cur_fp = 0UL then ()
    else if U64.v cur_fp < U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      assert (Seq.mem obj (objects 0UL g));
      assert (U64.v (wosize_of_object obj g) >= 1);
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found: alloc_from_block preserves wf
        if U64.v hd + 16 <= heap_size then
          next_fp_in_objects g obj;
        alloc_from_block_preserves_wf g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Handle prev_fp update
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          // prev ∈ objects(0, g') (old objects preserved)
          alloc_from_block_objects_facts g obj wz next_fp;
          assert (Seq.mem prev (objects 0UL g'));
          // wosize(prev, g) >= 1 from precondition
          assert (U64.v (wosize_of_object prev g) >= 1);
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          wf_object_size_bound g prev;
          // wosize(prev, g') = wosize(prev, g) since prev's header is unchanged
          hd_address_spec prev;
          wosize_of_object_spec obj g;
          // Show prev's header is unchanged from g to g'
          hd_address_spec prev;
          wosize_of_object_spec obj g;
          if block_wz - wz >= 2 then begin
            // Split case: 3 writes at hd, rem_hd, rem_obj
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated 0UL g prev obj;
              assert (U64.v (hd_address prev) < U64.v hd);
              assert (rem_hd_nat > U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat)
            end else begin
              objects_separated 0UL g obj prev;
              assert (U64.v prev > U64.v obj + U64.v (wosize_of_object_as_wosize obj g) * 8);
              assert (U64.v (hd_address prev) > U64.v hd + block_wz * 8 - 8);
              assert (U64.v (hd_address prev) <> U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat)
            end;
            alloc_split_g3_agrees g obj wz next_fp (hd_address prev)
          end else begin
            // Exact fit: only write at hd
            // prev ≠ obj from precondition (prev_fp <> cur_fp)
            assert (prev <> obj);
            if U64.v prev < U64.v obj then
              objects_separated 0UL g prev obj
            else begin
              assert (U64.v prev > U64.v obj); // from prev ≠ obj
              objects_separated 0UL g obj prev
            end;
            assert (U64.v (hd_address prev) <> U64.v hd);
            let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
            assert (fst (alloc_from_block g obj wz next_fp) == write_word g hd alloc_hdr);
            read_write_different g hd (hd_address prev) alloc_hdr
          end;
          wosize_of_object_spec prev g';
          assert (wosize_of_object prev g' == wosize_of_object prev g);
          // new_fp: either rem_fp (pointer) or 0UL
          // is_pointer_field new_fp ==> Seq.mem new_fp (objects 0UL g')
          alloc_from_block_objects_facts g obj wz next_fp;
          // field_write_preserves_wf: prev ∈ objects(0,g'), addr=prev within body, new_fp ok
          field_write_preserves_wf g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        // Advance: same heap, recurse
        fl_valid_next g cur_fp fuel;
        // cur_fp ≠ next_fp: if hd+16>heap_size, next_fp=0UL≠cur_fp;
        // otherwise fl_valid_next gives read_word g obj ≠ cur_fp
        assert (cur_fp <> next_fp);
        // cur_fp becomes prev_fp; wosize(cur_fp, g) >= 1 from fl_valid_gives_wosize
        alloc_search_preserves_wf g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ===========================================================================
/// Section 9: Top-level theorem
/// ===========================================================================

let alloc_spec_preserves_wf (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    well_formed_heap r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_wf g fp 0UL fp wz (heap_size / U64.v mword)

/// fl_valid introduction forms
let fl_valid_null (g: heap) (fuel: nat)
  : Lemma (requires fuel > 0)
          (ensures fl_valid g 0UL fuel)
  = ()

let fl_valid_step (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    Seq.mem fp (objects 0UL g) /\
                    U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
                    (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
                      read_word g (fp <: obj_addr) <> fp /\
                      fl_valid g (read_word g (fp <: obj_addr)) (fuel - 1)))
          (ensures fl_valid g fp fuel)
  = ()

/// fl_valid weakening: more fuel implies less fuel
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_valid_weaken (g: heap) (fp: U64.t) (fuel_strong fuel_weak: nat)
  : Lemma (requires fl_valid g fp fuel_strong /\ fuel_weak <= fuel_strong)
          (ensures fl_valid g fp fuel_weak)
          (decreases fuel_weak)
  = if fuel_weak = 0 then ()
    else if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      if U64.v hd + 16 <= heap_size then
        fl_valid_weaken g (read_word g obj) (fuel_strong - 1) (fuel_weak - 1)
      else ()
    end
#pop-options

/// Transfer fl_valid from g to g' with the same fuel
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_valid_transfer (g g': heap) (fp: U64.t) (fuel: nat)
  : Lemma
    (requires fl_valid g fp fuel /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects 0UL g)) ==>
                 (Seq.mem a (objects 0UL g') /\
                  (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 ==>
                    U64.v (wosize_of_object (a <: obj_addr) g') >= 1) /\
                  (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                   U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr)))))
    (ensures fl_valid g' fp fuel)
    (decreases fuel)
  = if fuel = 0 then ()
    else if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      if U64.v hd + 16 <= heap_size then begin
        let link = read_word g obj in
        fl_valid_transfer g g' link (fuel - 1)
      end
      else ()
    end
#pop-options

/// Chain termination: the free-list chain from fp hits a base case within `steps` iterations.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_terminates (g: heap) (fp: U64.t) (steps: nat) : Tot bool (decreases steps) =
  if fp = 0UL then true
  else if U64.v fp < U64.v mword then true
  else if U64.v fp >= heap_size then true
  else if U64.v fp % U64.v mword <> 0 then true
  else if steps = 0 then false
  else
    let hd = hd_address (fp <: obj_addr) in
    if U64.v hd + 16 > heap_size then true
    else fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1)
#pop-options

/// Terminal base cases for fl_chain_terminates
let fl_chain_terminates_terminal (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fp = 0UL \/ U64.v fp < U64.v mword \/ U64.v fp >= heap_size \/ U64.v fp % U64.v mword <> 0)
          (ensures fl_chain_terminates g fp steps = true)
  = ()

/// If fl_valid holds AND the chain terminates within fuel steps,
/// then fl_valid holds for any fuel'.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_valid_any_fuel (g: heap) (fp: U64.t) (fuel fuel': nat)
  : Lemma
    (requires fl_valid g fp fuel /\ fl_chain_terminates g fp fuel)
    (ensures fl_valid g fp fuel')
    (decreases fuel')
  = if fuel' = 0 then ()
    else if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      if U64.v hd + 16 <= heap_size then begin
        let link = read_word g obj in
        fl_valid_any_fuel g link (fuel - 1) (fuel' - 1)
      end
      else ()
    end
#pop-options

/// Chain termination transfers when links are preserved
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_terminates_transfer (g g': heap) (fp: U64.t) (steps: nat)
  : Lemma
    (requires fl_chain_terminates g fp steps /\
              fl_valid g fp steps /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects 0UL g)) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures fl_chain_terminates g' fp steps)
    (decreases steps)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      if U64.v hd + 16 <= heap_size then begin
        let link = read_word g obj in
        fl_chain_terminates_transfer g g' link (steps - 1)
      end
      else ()
    end
#pop-options

/// Chain termination monotonicity: more steps suffice
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_terminates_weaken (g: heap) (fp: U64.t) (s1 s2: nat)
  : Lemma (requires fl_chain_terminates g fp s1 /\ s2 >= s1)
          (ensures fl_chain_terminates g fp s2)
          (decreases s1)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if s1 = 0 then ()  // s1 = 0 means fl_chain_terminates is false; vacuous
    else begin
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else fl_chain_terminates_weaken g (read_word g (fp <: obj_addr)) (s1 - 1) (s2 - 1)
    end
#pop-options

/// Chain termination introduction: fp → next terminates if next terminates
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let fl_chain_terminates_step (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    (let hd = hd_address (fp <: obj_addr) in
                     U64.v hd + 16 <= heap_size ==>
                     fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1)))
          (ensures fl_chain_terminates g fp steps)
  = ()
#pop-options

/// A 2-cycle in the free list contradicts fl_chain_terminates.
/// If a → b → a (with both valid nodes and hd + 16 <= heap_size), then
/// fl_chain_terminates g a n = false for all n.
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_2cycle_not_terminates
  (g: heap) (a b: U64.t) (n: nat)
  : Lemma (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                    U64.v b >= U64.v mword /\ U64.v b < heap_size /\ U64.v b % U64.v mword = 0 /\
                    a <> b /\
                    U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size /\
                    U64.v (hd_address (b <: obj_addr)) + 16 <= heap_size /\
                    read_word g (a <: obj_addr) = b /\
                    read_word g (b <: obj_addr) = a)
          (ensures fl_chain_terminates g a n = false)
          (decreases n)
  = if n = 0 then ()
    else begin
      // fl_chain_terminates g a n: a is valid, hd+16<=hs, link = b. Recurse on b with n-1.
      // fl_chain_terminates g b (n-1): b is valid, hd+16<=hs, link = a. Recurse on a with n-2.
      if n >= 2 then
        fl_chain_2cycle_not_terminates g a b (n - 2)
      else begin
        // n = 1: fl_chain_terminates g a 1 unfolds to fl_chain_terminates g b 0 = false
        ()
      end
    end
#pop-options

/// Chain termination splice: analogous to fl_valid_splice for chain termination.
/// The tail at splice_point terminates in `tail_steps` steps.
/// The ensures gives `steps + tail_steps` because at the splice point, the
/// chain "consumes" some prefix steps then uses all tail_steps for the new tail.
#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec fl_chain_terminates_splice
  (g g_new: heap) (fp splice_point: U64.t) (steps tail_steps: nat)
  : Lemma
    (requires fl_chain_terminates g fp steps /\
              fl_valid g fp steps /\
              // Links preserved for non-splice nodes
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects 0UL g)) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size /\
                  a <> splice_point ==>
                   read_word g_new (a <: obj_addr) == read_word g (a <: obj_addr))) /\
              // At splice point, new tail terminates
              (U64.v splice_point >= U64.v mword /\ U64.v splice_point < heap_size /\
               U64.v splice_point % U64.v mword = 0 /\
               U64.v (hd_address (splice_point <: obj_addr)) + 16 <= heap_size ==>
                fl_chain_terminates g_new (read_word g_new (splice_point <: obj_addr)) tail_steps))
    (ensures fl_chain_terminates g_new fp (steps + tail_steps))
    (decreases steps)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if steps = 0 then ()
    else begin
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else begin
        if fp = splice_point then begin
          // At splice point: tail terminates in tail_steps.
          // Need fl_chain_terminates g_new (link_new) (steps + tail_steps - 1)
          // Have fl_chain_terminates g_new (link_new) tail_steps
          // steps >= 1 so steps + tail_steps - 1 >= tail_steps ✓
          fl_chain_terminates_weaken g_new (read_word g_new (splice_point <: obj_addr)) tail_steps (steps + tail_steps - 1)
        end
        else begin
          let link = read_word g (fp <: obj_addr) in
          assert (read_word g_new (fp <: obj_addr) == link);
          fl_chain_terminates_splice g g_new link splice_point (steps - 1) tail_steps
          // Gives fl_chain_terminates g_new link ((steps-1) + tail_steps)
          // = fl_chain_terminates g_new link (steps + tail_steps - 1)
          // which is exactly what's needed
        end
      end
    end
#pop-options

/// Writing at a field position (body of an object with wosize >= 1) preserves fl_valid.
/// The write doesn't change any header, so objects and wosize are preserved.
/// At the write position, the new link may differ but we require no self-loop.
/// Since fl_valid at fuel=0 is True, even cyclic chains through the write position are fine.
///
/// Strategy: prove fl_valid g' fp fuel by induction on fuel, using:
///   - For fp ≠ p: fl_valid g fp fuel gives all needed properties, link unchanged
///   - For fp = p: properties from g (mem, wosize), new link = v ≠ p, recurse on v
///   Both cases recurse with fuel-1, and fuel=0 gives True.
///
/// The precondition provides fl_valid g fp fuel which ensures:
///   - Every node visited (except possibly at p) has mem, wosize>=1, no-self-loop in g
///   - These transfer to g' because only p's body value changed
/// At p: we use the explicit mem/wosize/no-self-loop from the precondition.
///
/// For the chain from v (the new link at p): we need fl_valid g' v (fuel-1).
/// We also require fl_valid g' v tail_fuel (as a separate input) to handle
/// the case where the chain diverges at p.
#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec fl_valid_field_write
  (g: heap) (p: obj_addr) (v: U64.t) (fp: U64.t) (fuel tail_fuel: nat)
  : Lemma
    (requires fl_valid g fp fuel /\
              well_formed_heap g /\
              Seq.mem p (objects 0UL g) /\
              U64.v (wosize_of_object p g) >= 1 /\
              v <> p /\
              fl_valid (write_word g (p <: hp_addr) v) v tail_fuel /\
              tail_fuel >= fuel)
    (ensures fl_valid (write_word g (p <: hp_addr) v) fp fuel)
    (decreases fuel)
  = let g' = write_word g (p <: hp_addr) v in
    if fuel = 0 then ()
    else if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else begin
      let obj_fp : obj_addr = fp in
      let hd_fp = hd_address obj_fp in
      // objects preserved by field write
      wf_object_size_bound g p;
      wosize_of_object_bound p g;
      write_word_preserves_objects g p (p <: hp_addr) v;
      assert (objects 0UL g' == objects 0UL g);
      assert (Seq.mem fp (objects 0UL g'));
      // wosize preserved: hd_fp ≠ p (the write position)
      hd_address_spec obj_fp;
      if U64.v fp <> U64.v p then begin
        if U64.v fp > U64.v p then
          objects_separated 0UL g p obj_fp
        else
          objects_separated 0UL g obj_fp p
      end;
      read_write_different g (p <: hp_addr) (hd_fp <: hp_addr) v;
      wosize_of_object_spec obj_fp g;
      wosize_of_object_spec obj_fp g';
      assert (U64.v (wosize_of_object obj_fp g') >= 1);
      if U64.v hd_fp + 16 <= heap_size then begin
        if fp = p then begin
          // At the write point: link = v, v ≠ p ✓
          read_write_same g (p <: hp_addr) v;
          // fl_valid g' v (fuel-1) from fl_valid_weaken of tail_fuel
          fl_valid_weaken g' v tail_fuel (fuel - 1)
        end else begin
          // fp ≠ p: link unchanged
          read_write_different g (p <: hp_addr) (obj_fp <: hp_addr) v;
          fl_valid_field_write g p v (read_word g obj_fp) (fuel - 1) tail_fuel
        end
      end
      else ()
    end
#pop-options

/// Establish fl_valid g2 v fuel where g2 = write_word g p v, by strong induction.
/// Breaks the circularity in fl_valid_field_write: at the write point p, the new link
/// is v, and we need fl_valid g2 v (fuel-1). By strong induction, this is the IH.
#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec fl_valid_field_write_tail
  (g: heap) (p: obj_addr) (v: U64.t) (fuel: nat)
  : Lemma
    (requires well_formed_heap g /\
              Seq.mem p (objects 0UL g) /\
              U64.v (wosize_of_object p g) >= 1 /\
              v <> p /\
              fl_valid g v fuel)
    (ensures fl_valid (write_word g (p <: hp_addr) v) v fuel)
    (decreases fuel)
  = let g' = write_word g (p <: hp_addr) v in
    if fuel = 0 then ()
    else if v = 0UL then ()
    else if U64.v v < U64.v mword then ()
    else if U64.v v >= heap_size then ()
    else if U64.v v % U64.v mword <> 0 then ()
    else begin
      let obj_v : obj_addr = v in
      let hd_v = hd_address obj_v in
      // objects preserved
      wf_object_size_bound g p;
      wosize_of_object_bound p g;
      write_word_preserves_objects g p (p <: hp_addr) v;
      assert (objects 0UL g' == objects 0UL g);
      // wosize preserved at v: hd_v ≠ p
      hd_address_spec obj_v;
      if U64.v v <> U64.v p then begin
        if U64.v v > U64.v p then
          objects_separated 0UL g p obj_v
        else
          objects_separated 0UL g obj_v p
      end;
      read_write_different g (p <: hp_addr) (hd_v <: hp_addr) v;
      wosize_of_object_spec obj_v g;
      wosize_of_object_spec obj_v g';
      if U64.v hd_v + 16 <= heap_size then begin
        // v ≠ p, so link at v unchanged: read_word g' v = read_word g v
        read_write_different g (p <: hp_addr) (obj_v <: hp_addr) v;
        let link = read_word g obj_v in
        assert (read_word g' obj_v == link);
        // link ≠ v (from fl_valid g v fuel, no self-loop)
        assert (link <> v);
        // Need: fl_valid g' link (fuel-1)
        // Use fl_valid_field_write with tail = fl_valid g' v (fuel-1) from IH
        // IH: fl_valid g' v (fuel-1) by fl_valid_field_write_tail g p v (fuel-1)
        //   requires fl_valid g v (fuel-1). Get this from fl_valid_weaken.
        fl_valid_weaken g v fuel (fuel - 1);
        fl_valid_field_write_tail g p v (fuel - 1);
        // Now have fl_valid g' v (fuel-1)
        // Use fl_valid_field_write to get fl_valid g' link (fuel-1)
        fl_valid_field_write g p v link (fuel - 1) (fuel - 1)
      end
      else ()
    end
#pop-options


/// ===========================================================================
/// Section F: alloc_search preserves fl_valid
/// ===========================================================================

/// Helper: for the split case, establish the fl_valid_transfer quantifier.
/// For all objects a in objects(0,g) with wosize >= 1:
///   - a ∈ objects(0,g')
///   - wosize(a,g') >= 1
///   - link preserved: read_word g' a == read_word g a
#restart-solver
#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"
private let alloc_split_fl_transfer_pre
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (a: obj_addr)
  : Lemma (requires alloc_split_pre g obj wz next_fp /\
                    wz >= 1 /\
                    Seq.mem a (objects 0UL g) /\
                    U64.v a >= U64.v mword /\
                    U64.v a < heap_size /\
                    U64.v a % U64.v mword = 0)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    Seq.mem a (objects 0UL g') /\
                    (U64.v (wosize_of_object a g) >= 1 ==>
                      U64.v (wosize_of_object a g') >= 1) /\
                    (U64.v (wosize_of_object a g) >= 1 /\
                     U64.v (hd_address a) + 16 <= heap_size ==>
                      read_word g' a == read_word g a)))
  = alloc_split_facts g obj wz next_fp;
    alloc_from_block_objects_facts g obj wz next_fp;
    let (g', _) = alloc_from_block g obj wz next_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    hd_address_spec obj;
    hd_address_bounds obj;
    wf_object_size_bound g obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    if U64.v (wosize_of_object a g) >= 1 then begin
      hd_address_spec a;
      wosize_of_object_spec a g;
      wosize_of_object_bound a g;
      wf_object_size_bound g a;
      if a = obj then begin
        // Header changed to alloc_hdr with wosize = wz >= 1.
        // Link at a (= obj): obj ∉ {hd, rem_hd, rem_obj} since
        //   hd = obj - 8 ≠ obj; rem_hd > obj; rem_obj > obj
        assert (U64.v obj <> U64.v hd);  // hd = obj - 8 < obj
        assert (wz >= 1);
        assert (rem_hd_nat == U64.v hd + (1 + wz) * 8);
        assert ((1 + wz) * 8 >= 16);
        assert (rem_hd_nat >= U64.v hd + 16);
        assert (rem_hd_nat >= U64.v obj + 8);
        assert (U64.v obj <> rem_hd_nat);
        assert (rem_obj_nat > rem_hd_nat);
        assert (U64.v obj <> rem_obj_nat);
        // Link preservation: read_word g' obj == read_word g obj
        alloc_split_g3_agrees g obj wz next_fp (obj <: hp_addr);
        // Prove wosize(obj, g') = wz >= 1
        // Reconstruct intermediate heaps to trace read_word g' hd
        alloc_from_block_split_normal g obj wz next_fp;
        let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd alloc_hdr in
        let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
        let rem_wz = block_wz - wz - 1 in
        let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
        let g2 = write_word g1 rem_hd rem_hdr in
        let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
        let g3 = write_word g2 rem_obj next_fp in
        // read_word g' hd = alloc_hdr (tracing through writes)
        read_write_different g2 rem_obj hd next_fp;
        read_write_different g1 rem_hd hd rem_hdr;
        read_write_same g hd alloc_hdr;
        make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
        wosize_of_object_spec obj g3
      end else begin
        // a ≠ obj: objects_separated ensures a's header & body are outside obj's span
        if U64.v a < U64.v obj then begin
          objects_separated 0UL g a obj;
          // a + wosize(a)*8 < obj, so a ≤ obj - 16 (since wosize >= 1, aligned)
          // hd_address(a) = a - 8 ≤ obj - 24 < hd = obj - 8 < rem_hd < rem_obj
          // a ≤ obj - 16 < obj - 8 = hd < rem_hd < rem_obj
          alloc_split_g3_agrees g obj wz next_fp (hd_address a);
          alloc_split_g3_agrees g obj wz next_fp (a <: hp_addr);
          wosize_of_object_spec a g;
          wosize_of_object_spec a g'
        end else begin
          objects_separated 0UL g obj a;
          // a > obj + block_wz*8, so a >= obj + block_wz*8 + 8 (aligned)
          // hd_address(a) = a - 8 >= obj + block_wz*8 = hd + (block_wz+1)*8
          // All writes at hd, rem_hd, rem_obj are below hd + (block_wz+1)*8
          alloc_split_g3_agrees g obj wz next_fp (hd_address a);
          alloc_split_g3_agrees g obj wz next_fp (a <: hp_addr);
          wosize_of_object_spec a g;
          wosize_of_object_spec a g'
        end
      end
    end else ()
#pop-options

/// Helper: for the exact-fit case, establish the fl_valid_transfer quantifier.
#restart-solver
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
private let alloc_exact_fl_transfer_pre
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz < 2) /\
                    Seq.mem a (objects 0UL g) /\
                    U64.v a >= U64.v mword /\
                    U64.v a < heap_size /\
                    U64.v a % U64.v mword = 0)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    Seq.mem a (objects 0UL g') /\
                    (U64.v (wosize_of_object a g) >= 1 ==>
                      U64.v (wosize_of_object a g') >= 1) /\
                    (U64.v (wosize_of_object a g) >= 1 /\
                     U64.v (hd_address a) + 16 <= heap_size ==>
                      read_word g' a == read_word g a)))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
    let g' = write_word g hd alloc_hdr in
    hd_address_spec obj;
    hd_address_bounds obj;
    getWosize_bound hdr;
    make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
    header_write_same_wosize_preserves_objects g obj alloc_hdr;
    // objects(0, g') == objects(0, g)
    alloc_exact_preserves_wf g obj wz next_fp;
    if U64.v (wosize_of_object a g) >= 1 then begin
      hd_address_spec a;
      wosize_of_object_spec a g;
      wosize_of_object_bound a g;
      wf_object_size_bound g a;
      if a = obj then begin
        // Header changed but wosize preserved (block_wz = block_wz)
        read_write_same g hd alloc_hdr;
        read_write_different g hd (a <: hp_addr) alloc_hdr;
        wosize_of_object_spec a g'
      end else begin
        // a ≠ obj: header at hd_address(a) ≠ hd, and a ≠ hd
        if U64.v a < U64.v obj then
          objects_separated 0UL g a obj
        else
          objects_separated 0UL g obj a;
        read_write_different g hd (hd_address a) alloc_hdr;
        read_write_different g hd (a <: hp_addr) alloc_hdr;
        wosize_of_object_spec a g;
        wosize_of_object_spec a g'
      end
    end else ()
#pop-options

/// The main recursive proof: alloc_search preserves fl_valid.
#restart-solver
#push-options "--z3rlimit 400 --fuel 1 --ifuel 0"
let rec alloc_search_preserves_fl_valid
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    fl_valid g head_fp (heap_size / U64.v mword) /\
                    wz >= 1 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects 0UL g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
                       U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
                       read_word g (prev_fp <: obj_addr) = cur_fp)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    fl_valid r.heap_out r.fp_out (heap_size / U64.v mword)))
          (decreases fuel)
  = let big_fuel = heap_size / U64.v mword in
    if fuel = 0 then ()
    // Base cases: result = {g, head_fp, 0UL}. fl_valid g head_fp big_fuel from precondition.
    else if cur_fp = 0UL then ()
    else if U64.v cur_fp < U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      fl_valid_next g cur_fp fuel;
      assert (Seq.mem obj (objects 0UL g));
      assert (U64.v (wosize_of_object obj g) >= 1);
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      wf_object_size_bound g obj;
      getWosize_bound hdr;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      // hd + 16 always <= heap_size for valid objects: obj >= 8, obj < 1024, aligned to 8
      // So hd = obj - 8, hd + 16 = obj + 8 <= heap_size
      assert (U64.v hd + 16 <= heap_size);
      // fl_valid g next_fp (fuel-1) from fl_valid_next
      assert (fl_valid g next_fp (fuel - 1));
      // fl_chain_terminates g next_fp (fuel-1) from fl_chain_terminates g cur_fp fuel
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        next_fp_in_objects g obj;
        alloc_from_block_preserves_wf g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Upgrade fl_valid g next_fp (fuel-1) to fl_valid g next_fp big_fuel
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        assert (fl_valid g next_fp big_fuel);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0UL: fp_out = new_fp =====
          if block_wz - wz >= 2 then begin
            // ===== Split case: new_fp = rem_obj =====
            alloc_split_facts g obj wz next_fp;
            alloc_from_block_objects_facts g obj wz next_fp;
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_wz = block_wz - wz - 1 in
            // new_fp = rem_obj from alloc_split_facts
            // rem_obj ∈ objects(0, g') from alloc_from_block_objects_facts
            assert (is_pointer_field new_fp ==> Seq.mem new_fp (objects 0UL g'));
            // Transfer fl_valid g next_fp big_fuel to g'
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects 0UL g))
              (ensures Seq.mem a (objects 0UL g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer g g' next_fp big_fuel;
            assert (fl_valid g' next_fp big_fuel);
            fl_valid_weaken g' next_fp big_fuel (big_fuel - 1);
            // Build fl_valid g' new_fp big_fuel via fl_valid_step
            // new_fp = rem_obj:
            //   rem_obj ∈ objects(0, g') ✓
            //   wosize(rem_obj, g') = rem_wz >= 1 ✓ (block_wz - wz >= 2 => rem_wz >= 1)
            //   hd(rem_obj) + 16 <= heap_size: rem_hd + 16 = rem_obj + 8 <= heap_size ✓
            //   link(rem_obj, g') = next_fp (written by alloc_from_block)
            //   next_fp ≠ rem_obj: from objects_separated (rem_obj is interior to obj's old block)
            //   fl_valid g' next_fp (big_fuel - 1) ✓
            // Need to show rem_obj is valid and call fl_valid_step
            assert (Seq.mem new_fp (objects 0UL g'));
            // Reconstruct intermediate heaps to read back new_fp's fields
            let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
            let g1 = write_word g hd alloc_hdr in
            let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
            let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
            let g2 = write_word g1 rem_hd rem_hdr in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            let g3 = write_word g2 rem_obj next_fp in
            assert (g' == g3);
            assert (new_fp == rem_obj);
            // 1. read_word g' new_fp = next_fp (link to tail)
            read_write_same g2 rem_obj next_fp;
            assert (read_word g' new_fp == next_fp);
            // 2. wosize_of_object new_fp g' = rem_wz >= 1
            //    hd_address(rem_obj) = rem_hd (since rem_obj = rem_hd + 8)
            hd_address_spec (rem_obj <: obj_addr);
            assert (hd_address (rem_obj <: obj_addr) == rem_hd);
            // read_word g' rem_hd = rem_hdr (via trace through writes)
            read_write_different g2 rem_obj rem_hd next_fp;
            read_write_same g1 rem_hd rem_hdr;
            assert (read_word g' rem_hd == rem_hdr);
            wosize_of_object_spec (new_fp <: obj_addr) g';
            make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
            assert (U64.v (wosize_of_object (new_fp <: obj_addr) g') == rem_wz);
            assert (rem_wz >= 1);
            // 3. new_fp is a valid object address
            assert (U64.v new_fp == rem_obj_nat);
            assert (rem_obj_nat >= 16);
            assert (U64.v new_fp >= U64.v mword);
            assert (U64.v new_fp < heap_size);
            assert (U64.v new_fp % U64.v mword == 0);
            // 4. hd_address(new_fp) + 16 <= heap_size
            //    hd_address(new_fp) = rem_hd, rem_hd + 16 = rem_obj + 8
            //    next_hd = hd + (block_wz+1)*8 <= heap_size (from wf_object_size_bound)
            //    rem_obj + 8 = hd + (wz+3)*8 <= hd + (block_wz+1)*8 since block_wz >= wz+2
            let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
            assert (next_hd_nat <= heap_size);
            assert (rem_obj_nat + 8 <= next_hd_nat);
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            // 5. next_fp <> new_fp: next_fp is either terminal or in objects(0,g)
            //    If terminal (0, < mword, >= heap_size, unaligned): can't equal rem_obj
            //    If in objects: objects_separated gives it's outside obj's block,
            //    but rem_obj is inside obj's block, so they differ
            assert (next_fp <> cur_fp);  // from fl_valid_next
            (if next_fp = 0UL then ()
             else if U64.v next_fp < U64.v mword then ()
             else if U64.v next_fp >= heap_size then ()
             else if U64.v next_fp % U64.v mword <> 0 then ()
             else begin
               // next_fp is valid and in objects(0,g)
               next_fp_in_objects g obj;
               assert (Seq.mem next_fp (objects 0UL g));
               // rem_obj is in [obj+8, obj+block_wz*8) (interior of obj's block)
               // next_fp is either before obj or after obj's block
               if U64.v next_fp < U64.v obj then begin
                 // next_fp < obj < rem_obj
                 assert (U64.v next_fp < U64.v new_fp)
               end else begin
                 // next_fp > obj: objects_separated gives next_fp > obj + wosize*8
                 objects_separated 0UL g obj (next_fp <: obj_addr);
                 assert (U64.v next_fp > U64.v obj + block_wz * 8);
                 // rem_obj = hd + (1+wz)*8 + 8 = obj + wz*8 + 8 < obj + block_wz*8
                 assert (U64.v new_fp < U64.v obj + block_wz * 8);
                 assert (U64.v next_fp > U64.v new_fp)
               end
             end);
            assert (next_fp <> new_fp);
            // 6. Build fl_valid g' new_fp big_fuel via fl_valid_step
            fl_valid_step g' new_fp big_fuel
          end else begin
            // ===== Exact-fit case: new_fp = next_fp =====
            alloc_exact_preserves_wf g obj wz next_fp;
            // Transfer fl_valid g next_fp big_fuel to g'
            // Use obj_addr parameter to avoid subtyping issues in ensures
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects 0UL g))
              (ensures Seq.mem a (objects 0UL g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer g g' next_fp big_fuel;
            // fp_out = new_fp = next_fp (in exact fit, alloc_from_block returns (g1, next_fp))
            // fl_valid g' next_fp big_fuel ✓
            ()
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp ≠ 0UL: fp_out = head_fp, heap_out = write_word g' prev_fp new_fp =====
          // g2 = write_word g' prev_fp new_fp, result = {g2, head_fp}
          let prev_obj : obj_addr = prev_fp in
          let g2 = write_word g' (prev_obj <: hp_addr) new_fp in
          //
          // Step 1: Establish fl_valid g' head_fp big_fuel via transfer from g
          // Step 2: Establish fl_valid g' new_fp big_fuel
          // Step 3: prev_fp ∈ objects(0, g') with wosize >= 1
          // Step 4: new_fp ≠ prev_fp
          // Step 5: fl_valid g2 new_fp big_fuel via fl_valid_field_write_tail
          // Step 6: fl_valid g2 head_fp big_fuel via fl_valid_field_write
          //
          if block_wz - wz >= 2 then begin
            // ----- Split sub-case -----
            alloc_split_facts g obj wz next_fp;
            alloc_from_block_objects_facts g obj wz next_fp;
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            let rem_wz = block_wz - wz - 1 in
            // Step 1: Transfer fl_valid from g to g' for head_fp
            let transfer_aux_s (a: obj_addr) : Lemma
              (requires Seq.mem a (objects 0UL g))
              (ensures Seq.mem a (objects 0UL g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_s);
            fl_valid_transfer g g' head_fp big_fuel;
            assert (fl_valid g' head_fp big_fuel);
            // Step 2: Build fl_valid g' new_fp big_fuel (same as prev_fp=0 split case)
            fl_valid_transfer g g' next_fp big_fuel;
            fl_valid_weaken g' next_fp big_fuel (big_fuel - 1);
            assert (Seq.mem new_fp (objects 0UL g'));
            // Reconstruct intermediate heaps
            let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
            let g1 = write_word g hd alloc_hdr in
            let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
            let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
            let g2_tmp = write_word g1 rem_hd rem_hdr in
            let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
            let g3 = write_word g2_tmp rem_obj next_fp in
            assert (g' == g3);
            assert (new_fp == rem_obj);
            // wosize of new_fp in g': need wosize_of_object new_fp g' >= 1
            make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
            // The header at rem_hd in g' is rem_hdr
            // rem_hd = hd_address(rem_obj), so wosize_of_object rem_obj g' = getWosize(read_word g' rem_hd)
            // read_word g' rem_hd: written as g2_tmp = write_word g1 rem_hd rem_hdr, then
            //   g3 = write_word g2_tmp rem_obj next_fp. Since rem_obj ≠ rem_hd (rem_obj = rem_hd + 8),
            //   read_word g3 rem_hd = read_word g2_tmp rem_hd = rem_hdr
            read_write_different g2_tmp rem_obj rem_hd next_fp;
            assert (read_word g' rem_hd == rem_hdr);
            hd_address_spec (new_fp <: obj_addr);
            assert (hd_address (new_fp <: obj_addr) == rem_hd);
            wosize_of_object_spec (new_fp <: obj_addr) g';
            assert (rem_wz >= 1);
            assert (U64.v (wosize_of_object (new_fp <: obj_addr) g') >= 1);
            // read_word g' new_fp = next_fp (written as last step of alloc_from_block)
            read_write_same g2_tmp rem_obj next_fp;
            assert (read_word g' (new_fp <: obj_addr) == next_fp);
            // next_fp ≠ new_fp
            (if next_fp = 0UL then ()
             else if U64.v next_fp < U64.v mword then ()
             else if U64.v next_fp >= heap_size then ()
             else if U64.v next_fp % U64.v mword <> 0 then ()
             else begin
               if U64.v next_fp <= U64.v obj then begin
                 objects_separated 0UL g (next_fp <: obj_addr) obj;
                 assert (U64.v obj > U64.v next_fp + U64.v (wosize_of_object (next_fp <: obj_addr) g) * 8);
                 assert (U64.v new_fp < U64.v obj + block_wz * 8);
                 assert (U64.v next_fp < U64.v obj);
                 assert (U64.v new_fp >= U64.v obj)
               end else begin
                 objects_separated 0UL g obj (next_fp <: obj_addr);
                 assert (U64.v next_fp > U64.v obj + block_wz * 8);
                 assert (U64.v new_fp < U64.v obj + block_wz * 8)
               end
             end);
            assert (next_fp <> new_fp);
            fl_valid_step g' new_fp big_fuel;
            assert (fl_valid g' new_fp big_fuel);
            // Step 3: prev_fp ∈ objects(0, g') with wosize >= 1
            // prev_fp ∈ objects(0, g) from precondition, transfer preserves
            assert (Seq.mem prev_fp (objects 0UL g'));
            // wosize preserved: alloc_split_fl_transfer_pre gives it
            alloc_split_fl_transfer_pre g obj wz next_fp prev_obj;
            assert (U64.v (wosize_of_object prev_obj g') >= 1);
            // Step 4: new_fp ≠ prev_fp
            // new_fp = rem_obj, which is interior to obj's old block
            // prev_fp ≠ cur_fp (= obj) from precondition, and prev_fp is a different object
            // prev_fp < obj or prev_fp > obj + block_wz * 8
            // new_fp ∈ [obj + wz*8 + 8, obj + block_wz * 8) ⊂ obj's block
            // So new_fp ≠ prev_fp
            (if U64.v prev_fp <= U64.v obj then begin
               objects_separated 0UL g prev_obj obj;
               // prev_fp + wosize(prev_fp)*8 < obj, and new_fp >= obj
               assert (U64.v new_fp > U64.v prev_fp)
             end else begin
               objects_separated 0UL g obj prev_obj;
               // obj + block_wz * 8 < prev_fp, and new_fp < obj + block_wz*8
               assert (U64.v prev_fp > U64.v obj + block_wz * 8);
               assert (U64.v new_fp < U64.v obj + block_wz * 8);
               assert (U64.v new_fp < U64.v prev_fp)
             end);
            assert (new_fp <> prev_fp);
            // Step 5: fl_valid g2 new_fp big_fuel via fl_valid_field_write_tail
            fl_valid_field_write_tail g' prev_obj new_fp big_fuel;
            assert (fl_valid g2 new_fp big_fuel);
            // Step 6: fl_valid g2 head_fp big_fuel via fl_valid_field_write
            fl_valid_field_write g' prev_obj new_fp head_fp big_fuel big_fuel
          end else begin
            // ----- Exact-fit sub-case -----
            alloc_exact_preserves_wf g obj wz next_fp;
            // Step 1: Transfer fl_valid from g to g' for head_fp
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects 0UL g))
              (ensures Seq.mem a (objects 0UL g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            fl_valid_transfer g g' head_fp big_fuel;
            assert (fl_valid g' head_fp big_fuel);
            // Step 2: fl_valid g' new_fp big_fuel
            // In exact-fit: new_fp = next_fp (alloc_from_block returns (g1, next_fp))
            fl_valid_transfer g g' next_fp big_fuel;
            assert (fl_valid g' new_fp big_fuel);
            // Step 3: prev_fp ∈ objects(0, g') with wosize >= 1
            assert (Seq.mem prev_fp (objects 0UL g'));
            alloc_exact_fl_transfer_pre g obj wz next_fp prev_obj;
            assert (U64.v (wosize_of_object prev_obj g') >= 1);
            // Step 4: new_fp ≠ prev_fp
            // In exact-fit, new_fp = next_fp = read_word g cur_fp.
            // We have: read_word g prev_fp = cur_fp (precondition).
            // If next_fp = prev_fp, then chain is prev_fp → cur_fp → prev_fp (2-cycle).
            // fl_chain_terminates g next_fp (fuel-1) contradicts this cycle.
            (if new_fp = prev_fp then begin
              // next_fp = prev_fp creates a 2-cycle: prev_fp → cur_fp → prev_fp
              assert (read_word g (prev_fp <: obj_addr) == cur_fp);
              assert (read_word g obj == next_fp);
              assert (next_fp == prev_fp);
              fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
              assert (fl_chain_terminates g next_fp (fuel - 1) = false);
              // But we proved fl_chain_terminates g next_fp (fuel-1) = true
              assert false
            end else ());
            assert (new_fp <> prev_fp);
            // Step 5: fl_valid g2 new_fp big_fuel via fl_valid_field_write_tail
            fl_valid_field_write_tail g' prev_obj new_fp big_fuel;
            // Step 6: fl_valid g2 head_fp big_fuel via fl_valid_field_write
            fl_valid_field_write g' prev_obj new_fp head_fp big_fuel big_fuel
          end
        end
        else ()
      end
      else begin
        // ===== Advance: block too small, continue search =====
        // cur_fp becomes prev_fp; wosize(cur_fp, g) >= 1 from fl_valid_gives_wosize
        // cur_fp ≠ next_fp: from fl_valid_next (no self-loop)
        assert (cur_fp <> next_fp);
        // New precondition: read_word g cur_fp = next_fp
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        alloc_search_preserves_fl_valid g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ===========================================================================
/// Section G: Top-level theorem — alloc_spec preserves fl_valid
/// ===========================================================================

let alloc_spec_preserves_fl_valid (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword) /\
                    fl_chain_terminates g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    fl_valid r.heap_out r.fp_out (heap_size / U64.v mword)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_fl_valid g fp 0UL fp wz (heap_size / U64.v mword)


/// ===========================================================================
/// Section H: alloc_spec preserves no_black_objects
/// ===========================================================================

module Header = GC.Lib.Header
open GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Helper: make_header get_color roundtrip
/// ---------------------------------------------------------------------------

/// The color bits of make_header faithfully store the given color value
#restart-solver
#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"
private let make_header_getColor (wz: U64.t{U64.v wz < pow2 54})
                                  (c: U64.t{U64.v c < 4})
                                  (t: U64.t{U64.v t < 256})
  : Lemma (Header.get_color (U64.v (make_header wz c t)) == U64.v c)
  = let hdr = make_header wz c t in
    make_header_value wz c t;
    Header.get_color_val (U64.v hdr);
    FStar.UInt.shift_right_value_lemma #64 (U64.v hdr) 8;
    assert_norm (pow2 8 = 256);
    FStar.Math.Lemmas.lemma_div_plus (U64.v c * 256 + U64.v t) (U64.v wz * 4) 256;
    FStar.Math.Lemmas.lemma_div_plus (U64.v t) (U64.v c) 256;
    FStar.Math.Lemmas.small_div (U64.v t) 256;
    FStar.UInt.logand_mask #64 (U64.v wz * 4 + U64.v c) 2;
    assert_norm (pow2 2 - 1 = 3);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v c) (U64.v wz) 4;
    FStar.Math.Lemmas.small_mod (U64.v c) 4
#pop-options

/// make_header with white_bits produces White color
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let make_header_color_white (wz: U64.t{U64.v wz < pow2 54})
  : Lemma (getColor (make_header wz white_bits 0UL) == Header.White)
  = let hdr = make_header wz white_bits 0UL in
    getColor_raw hdr;
    make_header_getColor wz white_bits 0UL
#pop-options

/// make_header with blue_bits produces Blue color
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let make_header_color_blue (wz: U64.t{U64.v wz < pow2 54})
  : Lemma (getColor (make_header wz blue_bits 0UL) == Header.Blue)
  = let hdr = make_header wz blue_bits 0UL in
    getColor_raw hdr;
    make_header_getColor wz blue_bits 0UL
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: field write preserves no_black_objects
/// ---------------------------------------------------------------------------

/// Writing to a field (body address) of an object preserves no_black_objects.
#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let field_write_preserves_no_black
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    U64.v addr >= U64.v obj /\
                    U64.v addr < U64.v obj + U64.v (wosize_of_object obj g) * 8 /\
                    U64.v addr % 8 = 0)
          (ensures no_black_objects (write_word g addr v))
  = let g' = write_word g addr v in
    write_word_preserves_objects g obj addr v;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g'))
      (ensures ~(is_black h g'))
    = assert (Seq.mem h (objects 0UL g));
      hd_address_spec h;
      hd_address_spec obj;
      if U64.v h <= U64.v obj then begin
        read_write_different g addr (hd_address h) v;
        color_of_header_eq h g g'
      end else begin
        objects_separated 0UL g obj h;
        read_write_different g addr (hd_address h) v;
        color_of_header_eq h g g'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block preserves no_black_objects
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--split_queries always --z3rlimit 100 --fuel 0 --ifuel 0"
private let alloc_from_block_preserves_no_black
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz) /\
                    (is_pointer_field next_fp ==> Seq.mem next_fp (objects 0UL g)))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    no_black_objects g'))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let hd = hd_address obj in
    let (g', rem_fp) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    if block_wz - wz >= 2 then begin
      // Split case
      alloc_split_facts g obj wz next_fp;
      let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
      let rem_obj_nat = rem_hd_nat + 8 in
      let rem_wz = block_wz - wz - 1 in
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj_addr : obj_addr = U64.uint_to_t rem_obj_nat in
      let aux_before (p: hp_addr) : Lemma
        (requires U64.v p < U64.v hd)
        (ensures read_word g' p == read_word g p)
      = alloc_split_g3_agrees g obj wz next_fp p
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
      make_header_color_white (U64.uint_to_t wz);
      make_header_color_blue (U64.uint_to_t rem_wz);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects 0UL g'))
        (ensures ~(is_black h g'))
      = split_new_mem_in_old_or_rem 0UL g g' obj wz block_wz h;
        if U64.v h = rem_obj_nat then begin
          hd_address_spec rem_obj_addr;
          color_of_object_spec rem_obj_addr g';
          is_black_iff rem_obj_addr g'
        end else begin
          assert (Seq.mem h (objects 0UL g));
          if h = obj then begin
            color_of_object_spec obj g';
            is_black_iff obj g'
          end else begin
            hd_address_spec h;
            if U64.v h < U64.v obj then begin
              objects_separated 0UL g h obj;
              assert (U64.v (hd_address h) < U64.v hd);
              alloc_split_g3_agrees g obj wz next_fp (hd_address h)
            end else begin
              objects_separated 0UL g obj h;
              assert (U64.v (hd_address h) > U64.v hd + block_wz * 8);
              assert (U64.v (hd_address h) <> U64.v hd);
              assert (U64.v (hd_address h) <> rem_hd_nat);
              assert (U64.v (hd_address h) <> rem_obj_nat);
              alloc_split_g3_agrees g obj wz next_fp (hd_address h)
            end;
            color_of_header_eq h g g'
          end
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else begin
      // Exact fit case
      let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
      make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj alloc_hdr;
      read_write_same g hd alloc_hdr;
      make_header_color_white (U64.uint_to_t block_wz);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects 0UL g'))
        (ensures ~(is_black h g'))
      = assert (Seq.mem h (objects 0UL g));
        if h = obj then begin
          color_of_object_spec obj g';
          is_black_iff obj g'
        end else begin
          hd_address_spec h;
          if U64.v h < U64.v obj then
            objects_separated 0UL g h obj
          else
            objects_separated 0UL g obj h;
          read_write_different g hd (hd_address h) alloc_hdr;
          color_of_header_eq h g g'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_search preserves no_black_objects
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let rec alloc_search_preserves_no_black
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    fl_valid g cur_fp fuel /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects 0UL g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    no_black_objects r.heap_out))
          (decreases fuel)
  = if fuel = 0 then ()
    else if cur_fp = 0UL then ()
    else if U64.v cur_fp < U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      assert (Seq.mem obj (objects 0UL g));
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        if U64.v hd + 16 <= heap_size then
          next_fp_in_objects g obj;
        alloc_from_block_preserves_no_black g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          alloc_from_block_objects_facts g obj wz next_fp;
          assert (Seq.mem prev (objects 0UL g'));
          alloc_from_block_preserves_wf g obj wz next_fp;
          hd_address_spec prev;
          wosize_of_object_spec prev g;
          wosize_of_object_spec obj g;
          wosize_of_object_bound prev g;
          wf_object_size_bound g prev;
          if block_wz - wz >= 2 then begin
            let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
            let rem_obj_nat = rem_hd_nat + 8 in
            if U64.v prev < U64.v obj then begin
              objects_separated 0UL g prev obj;
              assert (U64.v (hd_address prev) < U64.v hd);
              assert (rem_hd_nat > U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat);
              alloc_split_g3_agrees g obj wz next_fp (hd_address prev)
            end else begin
              objects_separated 0UL g obj prev;
              assert (U64.v (hd_address prev) > U64.v hd + block_wz * 8 - 8);
              assert (U64.v (hd_address prev) <> U64.v hd);
              assert (U64.v (hd_address prev) <> rem_hd_nat);
              assert (U64.v (hd_address prev) <> rem_obj_nat);
              alloc_split_g3_agrees g obj wz next_fp (hd_address prev)
            end
          end else begin
            assert (prev <> obj);
            if U64.v prev < U64.v obj then
              objects_separated 0UL g prev obj
            else
              objects_separated 0UL g obj prev;
            assert (U64.v (hd_address prev) <> U64.v hd);
            let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
            assert (fst (alloc_from_block g obj wz next_fp) == write_word g hd alloc_hdr);
            read_write_different g hd (hd_address prev) alloc_hdr
          end;
          wosize_of_object_spec prev g';
          assert (wosize_of_object prev g' == wosize_of_object prev g);
          field_write_preserves_no_black g' prev (prev <: hp_addr) new_fp
        end
        else ()
      end
      else begin
        fl_valid_next g cur_fp fuel;
        assert (cur_fp <> next_fp);
        alloc_search_preserves_no_black g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: alloc_spec preserves no_black_objects
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_no_black (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires no_black_objects g /\
                    well_formed_heap g /\
                    fl_valid g fp (heap_size / U64.v mword))
          (ensures (let r = alloc_spec g fp requested_wz in
                    no_black_objects r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_no_black g fp 0UL fp wz (heap_size / U64.v mword)

#pop-options // Module-level z3rlimit 20
