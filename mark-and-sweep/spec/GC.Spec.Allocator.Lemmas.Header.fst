(*
   GC.Spec.Allocator.Lemmas.Header — Foundation lemmas for allocator proofs.

   Section 1: make_header arithmetic
   Section 2: Header write preserves objects
   Section 3: efptu congruence/monotonicity
   Section 4: Header write field independence
*)
module GC.Spec.Allocator.Lemmas.Header

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Module-level default
#push-options "--z3rlimit 20 --z3refresh"

/// ===========================================================================
/// Section 1: Preliminary lemmas about make_header
/// ===========================================================================

/// Arithmetic characterization of make_header:
#push-options "--z3rlimit 400 "
let make_header_value (wz: U64.t{U64.v wz < pow2 54})
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
          (ensures objects zero_addr (write_word g (hd_address obj) new_hdr) == objects zero_addr g)
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
    wosize_eq_implies_objects_eq zero_addr g g'

/// ===========================================================================
/// Section 3: exists_field_pointing_to_unchecked congruence
/// ===========================================================================

/// If all field reads of src are the same in g' and g, then efptu is the same
let rec efptu_congruence
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
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let rec efptu_monotone
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
                    Seq.mem obj (objects zero_addr g) /\
                    Seq.mem src (objects zero_addr g) /\
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
        objects_separated zero_addr g src obj
      else
        objects_separated zero_addr g obj src;
      read_write_different g hd fa new_hdr
    end
#pop-options
#pop-options
