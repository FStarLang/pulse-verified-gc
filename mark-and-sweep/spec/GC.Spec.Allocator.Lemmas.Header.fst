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
#push-options "--z3rlimit 200"
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
#push-options "--z3rlimit 200"
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
#push-options "--z3rlimit 200"
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
/// Monotonicity: efptu with smaller wosize implies efptu with bigger wosize.
/// ===========================================================================
/// Section 4: Header write at hd_address(obj) doesn't change field reads
/// ===========================================================================

/// For src = obj: fields at obj + k*8 are all > hd_address obj = obj - 8
/// hd_address(obj) = obj - 8, so obj + k*8 > obj - 8 for all k >= 0.
///
/// Proof uses a custom NL step to avoid Z3 4.13.3 arith.solver 6 limitations
/// with chaining through k*8 terms.
#restart-solver
/// For src ≠ obj: all fields of src are separated from hd_address(obj)
#pop-options
