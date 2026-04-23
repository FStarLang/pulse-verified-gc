/// ---------------------------------------------------------------------------
/// TestCombined — Combined induction: fused_aux == coalesce_aux
///                with separate working heaps agreeing below a bound
/// ---------------------------------------------------------------------------

module GC.Spec.SweepCoalesce.Induction

open FStar.Seq
open FStar.Mul
module U64 = FStar.UInt64
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header

module SpecCoalesce = GC.Spec.Coalesce
module SCH = GC.Spec.SweepCoalesce.Helpers
module SCF = GC.Spec.SweepCoalesce.FlushAgree
module HeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator

open GC.Spec.SweepCoalesce.Defs

#set-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always --warn_error -321"

/// ========================================================================
/// Predicates
/// ========================================================================

let rec objs_well_separated (g: heap) (objs: seq obj_addr)
  : GTot prop (decreases Seq.length objs)
  = if Seq.length objs <= 1 then True
    else
      (forall (x: obj_addr). Seq.mem x (Seq.tail objs) ==>
        U64.v x > U64.v (Seq.head objs) +
                  U64.v (wosize_of_object (Seq.head objs) g) * 8) /\
      objs_well_separated g (Seq.tail objs)

let rec objs_contiguous (g: heap) (objs: seq obj_addr)
  : GTot prop (decreases Seq.length objs)
  = if Seq.length objs <= 1 then True
    else
      U64.v (Seq.head (Seq.tail objs)) ==
        U64.v (Seq.head objs) + (U64.v (wosize_of_object (Seq.head objs) g) + 1) * 8 /\
      objs_contiguous g (Seq.tail objs)

/// ========================================================================
/// Helper 1: zero_fields reads 0UL within its range
/// ========================================================================

#push-options "--z3rlimit 30"
let rec zero_fields_read_within
    (g: heap) (start: U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires
      U64.v start + n * 8 <= heap_size /\
      U64.v start % 8 == 0 /\
      U64.v addr >= U64.v start /\
      U64.v addr < U64.v start + n * 8)
    (ensures read_word (Alloc.zero_fields g start n) addr == 0UL)
    (decreases n)
  = if n = 0 then ()
    else begin
      let start_hp : hp_addr = start in
      let g' = write_word g start_hp 0UL in
      if U64.v addr = U64.v start then begin
        read_write_same g start_hp 0UL;
        let next = U64.uint_to_t (U64.v start + 8) in
        SpecCoalesce.zero_fields_preserves_before g' next (n - 1) addr
      end else begin
        let next = U64.uint_to_t (U64.v start + 8) in
        read_write_different g start_hp addr 0UL;
        zero_fields_read_within g' next (n - 1) addr
      end
    end
#pop-options

/// ========================================================================
/// Helper 2: flush_blue produces fp at field 1
/// ========================================================================

#push-options "--z3rlimit 100 --fuel 2"
private let flush_blue_field1_spec
    (g: heap) (fb: obj_addr) (rw: nat) (fp: U64.t)
  : Lemma
    (requires
      rw >= 2 /\
      rw - 1 < pow2 54 /\
      U64.v (hd_address fb) + rw * 8 <= heap_size /\
      Seq.length g == heap_size)
    (ensures read_word (fst (SpecCoalesce.flush_blue g fb rw fp)) fb == fp)
  = let hd = hd_address fb in
    hd_address_spec fb;
    let wz = rw - 1 in
    ML.pow2_lt_compat 64 54;
    let wz_u64 : wosize = U64.uint_to_t wz in
    let hdr = makeHeader wz_u64 Blue 0UL in
    let g1 = write_word g hd hdr in
    assert (U64.v hd + U64.v mword * 2 <= heap_size);
    assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
    let field1_addr : hp_addr = U64.add (hd_address fb) (U64.mul mword 1UL) in
    assert (U64.v field1_addr == U64.v fb);
    read_write_different g hd field1_addr hdr;
    let g2 = HeapGraph.set_field g1 fb 1UL fp in
    read_write_same g1 field1_addr fp;
    let zero_start_nat = U64.v fb + 8 in
    if wz >= 2 && zero_start_nat < pow2 64 then begin
      let zero_start = U64.uint_to_t zero_start_nat in
      assert (U64.v field1_addr + U64.v mword <= U64.v zero_start);
      SpecCoalesce.zero_fields_preserves_before g2 zero_start (wz - 1) field1_addr
    end else ()
#pop-options

/// ========================================================================
/// Helper 3: flush_blue produces 0UL at zero-field positions
/// ========================================================================

#push-options "--z3rlimit 100 --fuel 2"
private let flush_blue_zero_spec
    (g: heap) (fb: obj_addr) (rw: nat) (fp: U64.t) (a: hp_addr)
  : Lemma
    (requires
      rw >= 3 /\
      rw - 1 < pow2 54 /\
      U64.v (hd_address fb) + rw * 8 <= heap_size /\
      Seq.length g == heap_size /\
      U64.v a >= U64.v fb + 8 /\
      U64.v a < U64.v fb + (rw - 1) * 8)
    (ensures read_word (fst (SpecCoalesce.flush_blue g fb rw fp)) a == 0UL)
  = let hd = hd_address fb in
    hd_address_spec fb;
    let wz = rw - 1 in
    ML.pow2_lt_compat 64 54;
    let wz_u64 : wosize = U64.uint_to_t wz in
    let hdr = makeHeader wz_u64 Blue 0UL in
    let g1 = write_word g hd hdr in
    assert (U64.v hd + U64.v mword * 2 <= heap_size);
    assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
    let g2 = HeapGraph.set_field g1 fb 1UL fp in
    let zero_start_nat = U64.v fb + 8 in
    assert (zero_start_nat < pow2 64);
    let zero_start = U64.uint_to_t zero_start_nat in
    zero_fields_read_within g2 zero_start (wz - 1) a
#pop-options

/// ========================================================================
/// Helper 4: flush_blue agrees inside the flush range
/// ========================================================================

#push-options "--z3rlimit 50 --fuel 2"
let flush_blue_inside_agree
    (h1 h2: heap) (fb: obj_addr) (rw: nat) (fp: U64.t) (a: hp_addr)
  : Lemma
    (requires
      rw > 0 /\
      rw - 1 < pow2 54 /\
      U64.v (hd_address fb) + rw * 8 <= heap_size /\
      Seq.length h1 == heap_size /\ Seq.length h2 == heap_size /\
      U64.v a >= U64.v (hd_address fb) /\
      U64.v a + 8 <= U64.v (hd_address fb) + rw * 8)
    (ensures
      read_word (fst (SpecCoalesce.flush_blue h1 fb rw fp)) a ==
      read_word (fst (SpecCoalesce.flush_blue h2 fb rw fp)) a)
  = hd_address_spec fb;
    let hd = hd_address fb in
    if U64.v a = U64.v hd then begin
      SpecCoalesce.flush_blue_header_spec h1 fb rw fp;
      SpecCoalesce.flush_blue_header_spec h2 fb rw fp
    end else if U64.v a = U64.v fb then begin
      assert (rw >= 2);
      flush_blue_field1_spec h1 fb rw fp;
      flush_blue_field1_spec h2 fb rw fp
    end else begin
      assert (U64.v a >= U64.v fb + 8);
      assert (rw >= 3);
      assert (U64.v a < U64.v fb + (rw - 1) * 8);
      flush_blue_zero_spec h1 fb rw fp a;
      flush_blue_zero_spec h2 fb rw fp a
    end
#pop-options

/// ========================================================================
/// Helper 5: flush_blue preserves outside for a pair of heaps
/// ========================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let flush_pair_preserves_outside
    (h1 h2: heap) (fb: U64.t) (rw: nat) (fp: U64.t) (addr: hp_addr)
  : Lemma
    (requires rw > 0 /\
      U64.v fb >= U64.v mword /\
      U64.v fb < heap_size /\
      U64.v fb % U64.v mword == 0 /\
      (U64.v addr + U64.v mword <= U64.v fb - U64.v mword \/
       U64.v addr >= U64.v fb - U64.v mword + rw * U64.v mword))
    (ensures
      read_word (fst (SpecCoalesce.flush_blue h1 fb rw fp)) addr == read_word h1 addr /\
      read_word (fst (SpecCoalesce.flush_blue h2 fb rw fp)) addr == read_word h2 addr)
  = SpecCoalesce.flush_blue_preserves_outside h1 fb rw fp addr;
    SpecCoalesce.flush_blue_preserves_outside h2 fb rw fp addr
#pop-options

/// Helper 5b: flush_blue preserves outside — specialized for addresses
/// above the flush range (addr >= fb + rw * 8). Clean precondition
/// using literal 8 to avoid quantifier issues in complex caller contexts.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let flush_pair_above
    (h1 h2: heap) (fb: U64.t) (rw: nat) (fp: U64.t) (addr: hp_addr)
  : Lemma
    (requires rw > 0 /\
      U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\ U64.v fb % U64.v mword == 0 /\
      U64.v addr >= U64.v fb + rw * 8)
    (ensures
      read_word (fst (SpecCoalesce.flush_blue h1 fb rw fp)) addr == read_word h1 addr /\
      read_word (fst (SpecCoalesce.flush_blue h2 fb rw fp)) addr == read_word h2 addr)
  = flush_pair_preserves_outside h1 h2 fb rw fp addr
#pop-options

/// Helper 5c: else-branch proof — address past object body.
/// Extracted to top-level to avoid quantifier context pollution from
/// the forall-quantified conditions in black_case_below_ok.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
private let black_case_past_body
    (g: heap) (h_f h_c: heap) (obj: obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
    (a: hp_addr)
  : Lemma
    (requires
      is_black obj g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      U64.v a >= U64.v obj + U64.v (wosize_of_object obj g) * 8 /\
      (rw > 0 ==>
        (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
         U64.v fb % U64.v mword == 0 /\
         U64.v obj >= U64.v fb + rw * 8 /\
         U64.v a >= U64.v fb + rw * 8)) /\
      read_word h_f a == read_word h_c a /\
      is_white obj h_c /\
      getWosize (read_word h_f (hd_address obj)) == getWosize (read_word h_c (hd_address obj)) /\
      getTag (read_word h_f (hd_address obj)) == getTag (read_word h_c (hd_address obj)))
    (ensures
      read_word (makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp))) a ==
      read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) a)
  = let hd_obj = hd_address obj in
    hd_address_spec obj;
    SpecCoalesce.flush_blue_preserves_outside h_f fb rw fp a;
    SpecCoalesce.flush_blue_preserves_outside h_c fb rw fp a;
    SpecCoalesce.flush_blue_preserves_outside h_f fb rw fp hd_obj;
    let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    makeWhite_spec obj h_f';
    SCH.colorHeader_same_wz_tag (read_word h_f hd_obj) (read_word h_c hd_obj) White;
    is_white_iff obj h_c;
    color_of_object_spec obj h_c;
    read_write_different h_f' hd_obj a
      (colorHeader (read_word h_f' hd_obj) White)
#pop-options

/// ========================================================================
/// Black-case helper lemmas — each is pointwise (no forall_intro inside).
/// The universalization happens in combined_proof via forall_intro on
/// thin local wrappers that just call these top-level helpers.
/// ========================================================================

/// Pointwise: for a single address below the new bound, h_f'' and h_c' agree
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let black_case_below_ok
  (g: heap) (h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  (a: hp_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      (* 4 *) (let bound = if rw > 0 then U64.v fb - 8
                            else U64.v (hd_address (Seq.head objs)) in
               forall (a: hp_addr). U64.v a + 8 <= bound ==> read_word h_f a == read_word h_c a) /\
      (* 5 *) (forall (a: hp_addr).
                (rw = 0 \/ U64.v a >= U64.v fb - 8 + rw * 8) /\
                (forall (x: obj_addr). Seq.mem x objs ==>
                  U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8) ==>
                read_word h_f a == read_word h_c a) /\
      (* 6 *) (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==>
                getWosize (read_word h_f (hd_address x)) == getWosize (read_word h_c (hd_address x)) /\
                getTag (read_word h_f (hd_address x)) == getTag (read_word h_c (hd_address x))) /\
      (* 7 *) (forall (x: obj_addr) (a: hp_addr).
                Seq.mem x objs /\ is_black x g /\
                U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                read_word h_f a == read_word h_c a) /\
      (* 8 *) (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==> is_white x h_c) /\
      (* 9 *) (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x >= U64.v fb + rw * 8)) /\
      (* 10 *) (rw > 0 ==>
                (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                 U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
                 U64.v fb - 8 + rw * 8 <= heap_size)) /\
      (* 12 *) objs_contiguous g objs /\
      (* 13 *) (rw > 0 /\ Seq.length objs > 0 ==>
                U64.v fb + rw * 8 == U64.v (Seq.head objs)) /\
      (* 14 *) (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
      (* bound on a *)
      (let rest = Seq.tail objs in
       let new_bound = if Seq.length rest > 0
                       then U64.v (hd_address (Seq.head rest))
                       else heap_size in
       U64.v a + 8 <= new_bound))
    (ensures
      (let obj = Seq.head objs in
       read_word (makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp))) a ==
       read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) a))
  = let obj = Seq.head objs in
    hd_address_spec obj;
    let hd_obj = hd_address obj in
    let wz_obj = U64.v (wosize_of_object obj g) in
    // Check "past body" case FIRST in a clean Z3 context (no flush_blue terms yet).
    // Branches 1-5 all have a < obj + wz * 8, so this cleanly separates branch 6.
    if U64.v a >= U64.v obj + wz_obj * 8 then begin
      // Branch 6: a past the body of obj.
      // When rest is non-empty, this branch is unreachable (contiguity contradiction).
      // When rest is empty, objs is a singleton and condition 5 applies.
      let rest = Seq.tail objs in
      if Seq.length rest > 0 then begin
        // Derive contradiction: contiguity says next obj starts right after body+header
        let next_obj = Seq.head rest in
        // next_obj = obj + (wz + 1) * 8 from objs_contiguous
        // hd_address(next_obj) = next_obj - 8 = obj + wz * 8
        // Bound says a + 8 <= hd_address(next_obj) = obj + wz * 8
        // But we have a >= obj + wz * 8: contradiction
        hd_address_spec next_obj;
        assert false
      end
      else begin
        // objs is a singleton: head is the only member
        assert (read_word h_f a == read_word h_c a);
        black_case_past_body g h_f h_c obj fb rw fp a
      end
    end
    else begin
      // Branches 1-5: a is within or before the object.
      // Now safe to introduce heavy flush_blue / makeWhite terms.
      let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
      let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
      makeWhite_spec obj h_f';
      let h_f'' = makeWhite obj h_f' in
      SpecCoalesce.flush_blue_preserves_outside h_f fb rw fp hd_obj;
      SpecCoalesce.flush_blue_preserves_outside h_c fb rw fp hd_obj;
      // Header agreement
      SCH.colorHeader_same_wz_tag (read_word h_f hd_obj) (read_word h_c hd_obj) White;
      is_white_iff obj h_c;
      color_of_object_spec obj h_c;
      SCH.colorHeader_idempotent (read_word h_c hd_obj) White;
      // Case split on a
      if rw > 0 && U64.v a + 8 <= U64.v fb - 8 then begin
        flush_pair_preserves_outside h_f h_c fb rw fp a;
        read_write_different h_f' hd_obj a
          (colorHeader (read_word h_f' hd_obj) White)
      end
      else if rw = 0 && U64.v a + 8 <= U64.v hd_obj then begin
        read_write_different h_f' hd_obj a
          (colorHeader (read_word h_f' hd_obj) White)
      end
      else if rw > 0 && U64.v a >= U64.v fb - 8 &&
              U64.v a + 8 <= U64.v fb - 8 + rw * 8 then begin
        let fb_obj : obj_addr = fb in
        hd_address_spec fb_obj;
        flush_blue_inside_agree h_f h_c fb_obj rw fp a;
        read_write_different h_f' hd_obj a
          (colorHeader (read_word h_f' hd_obj) White)
      end
      else if U64.v a = U64.v hd_obj then
        ()
      else begin
        // Branch 5: a inside body
        assert (U64.v a >= U64.v obj /\ U64.v a + 8 <= U64.v obj + wz_obj * 8);
        (if rw > 0 then
          flush_pair_preserves_outside h_f h_c fb rw fp a
        else ());
        assert (read_word h_f a == read_word h_c a);
        read_write_different h_f' hd_obj a
          (colorHeader (read_word h_f' hd_obj) White)
      end
    end
#pop-options

/// Pointwise: for a single address past all rest objects, h_f'' and h_c' agree
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let black_case_above_ok
  (g: heap) (h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  (a: hp_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      (* 5 *) (forall (a: hp_addr).
                (rw = 0 \/ U64.v a >= U64.v fb - 8 + rw * 8) /\
                (forall (x: obj_addr). Seq.mem x objs ==>
                  U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8) ==>
                read_word h_f a == read_word h_c a) /\
      (* 9 *) (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x >= U64.v fb + rw * 8)) /\
      (* 10 *) (rw > 0 ==>
                (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                 U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
                 U64.v fb - 8 + rw * 8 <= heap_size)) /\
      (* 11 *) objs_well_separated g objs /\
      (* 14 *) (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
      (* below_ok result — needed for rest-empty case *)
      (let obj = Seq.head objs in
       let rest = Seq.tail objs in
       let nb = if Seq.length rest > 0
                then U64.v (hd_address (Seq.head rest))
                else heap_size in
       forall (b: hp_addr). U64.v b + 8 <= nb ==>
         read_word (makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp))) b ==
         read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) b) /\
      (* a past rest objects *)
      (forall (x: obj_addr). Seq.mem x (Seq.tail objs) ==>
        U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8))
    (ensures
      (let obj = Seq.head objs in
       read_word (makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp))) a ==
       read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) a))
  = let obj = Seq.head objs in
    let rest = Seq.tail objs in
    hd_address_spec obj;
    let hd_obj = hd_address obj in
    let wz_obj = U64.v (wosize_of_object obj g) in
    let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
    makeWhite_spec obj h_f';
    let h_f'' = makeWhite obj h_f' in
    SpecCoalesce.flush_blue_preserves_outside h_f fb rw fp hd_obj;
    SpecCoalesce.flush_blue_preserves_outside h_c fb rw fp hd_obj;
    if Seq.length rest > 0 then begin
      let hd_rest = Seq.head rest in
      assert (Seq.mem hd_rest rest);
      assert (U64.v a >= U64.v hd_rest + U64.v (wosize_of_object hd_rest g) * 8);
      assert (U64.v hd_rest > U64.v obj + wz_obj * 8);
      assert (U64.v a > U64.v obj + wz_obj * 8)
    end else ();
    (if Seq.length rest > 0 then begin
      assert (U64.v a > U64.v obj + wz_obj * 8);
      assert (forall (x:obj_addr). Seq.mem x objs ==>
        U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8)
    end else ());
    (if Seq.length rest > 0 then begin
      (if rw > 0 then begin
        assert (U64.v obj >= U64.v fb + rw * 8);
        assert (U64.v a >= U64.v fb - 8 + rw * 8);
        flush_pair_preserves_outside h_f h_c fb rw fp a
      end else ());
      assert (U64.v a > U64.v hd_obj);
      read_write_different h_f' hd_obj a
        (colorHeader (read_word h_f' hd_obj) White)
    end else ())
#pop-options

/// Pointwise: for a single black rest object, header match + white in h_c'
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let black_case_rest_headers
  (g: heap) (h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  (x: obj_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      (* 6 *) (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==>
                getWosize (read_word h_f (hd_address x)) == getWosize (read_word h_c (hd_address x)) /\
                getTag (read_word h_f (hd_address x)) == getTag (read_word h_c (hd_address x))) /\
      (* 8 *) (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==> is_white x h_c) /\
      (* 9 *) (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x >= U64.v fb + rw * 8)) /\
      (* 10 *) (rw > 0 ==>
                (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                 U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
                 U64.v fb - 8 + rw * 8 <= heap_size)) /\
      (* 11 *) objs_well_separated g objs /\
      (* 14 *) (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
      Seq.mem x (Seq.tail objs) /\ is_black x g)
    (ensures
      (let obj = Seq.head objs in
       let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
       let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
       let h_f'' = makeWhite obj h_f' in
       getWosize (read_word h_f'' (hd_address x)) == getWosize (read_word h_c' (hd_address x)) /\
       getTag (read_word h_f'' (hd_address x)) == getTag (read_word h_c' (hd_address x)) /\
       is_white x h_c'))
  = let obj = Seq.head objs in
    hd_address_spec obj;
    let hd_obj = hd_address obj in
    let wz_obj = U64.v (wosize_of_object obj g) in
    let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
    makeWhite_spec obj h_f';
    SpecCoalesce.flush_blue_preserves_outside h_f fb rw fp hd_obj;
    SpecCoalesce.flush_blue_preserves_outside h_c fb rw fp hd_obj;
    hd_address_spec x;
    let hd_x = hd_address x in
    assert (Seq.mem x objs);
    assert (U64.v x > U64.v obj + wz_obj * 8);
    assert (U64.v hd_x > U64.v obj + wz_obj * 8 - 8);
    assert (U64.v hd_x >= U64.v obj + wz_obj * 8);
    assert (U64.v hd_x > U64.v hd_obj);
    (if rw > 0 then
      flush_pair_preserves_outside h_f h_c fb rw fp hd_x
    else ());
    read_write_different h_f' hd_obj hd_x
      (colorHeader (read_word h_f' hd_obj) White);
    color_of_header_eq x h_c' h_c
#pop-options

/// Pointwise: for a single body word of a black rest object, h_f'' and h_c' agree
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let black_case_body_agree_aux
  (g: heap) (h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  (x: obj_addr) (a: hp_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      (* 7 *) (forall (x: obj_addr) (a: hp_addr).
                Seq.mem x objs /\ is_black x g /\
                U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                read_word h_f a == read_word h_c a) /\
      (* 9 *) (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x >= U64.v fb + rw * 8)) /\
      (* 10 *) (rw > 0 ==>
                (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                 U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
                 U64.v fb - 8 + rw * 8 <= heap_size)) /\
      (* 11 *) objs_well_separated g objs /\
      (* 14 *) (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
      Seq.mem x (Seq.tail objs) /\ is_black x g /\
      U64.v a >= U64.v x /\
      U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8)
    (ensures
      (let obj = Seq.head objs in
       read_word (makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp))) a ==
       read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) a))
  = let obj = Seq.head objs in
    hd_address_spec obj;
    let hd_obj = hd_address obj in
    let wz_obj = U64.v (wosize_of_object obj g) in
    let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    makeWhite_spec obj h_f';
    SpecCoalesce.flush_blue_preserves_outside h_f fb rw fp hd_obj;
    SpecCoalesce.flush_blue_preserves_outside h_c fb rw fp hd_obj;
    assert (Seq.mem x objs);
    assert (U64.v x > U64.v obj + wz_obj * 8);
    assert (U64.v a >= U64.v x /\ U64.v x > U64.v obj + wz_obj * 8);
    assert (U64.v a > U64.v hd_obj);
    (if rw > 0 then
      flush_pair_preserves_outside h_f h_c fb rw fp a
    else ());
    read_write_different h_f' hd_obj a
      (colorHeader (read_word h_f' hd_obj) White);
    assert (read_word h_f a == read_word h_c a)
#pop-options

/// For a given black rest object, universalize body agreement over addresses.
/// Uses forall_intro on the top-level black_case_body_agree_aux (trivial VC).
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let black_case_body_agree
  (g: heap) (h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  (x: obj_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      (forall (x: obj_addr) (a: hp_addr).
        Seq.mem x objs /\ is_black x g /\
        U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
        read_word h_f a == read_word h_c a) /\
      (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
        U64.v x >= U64.v fb + rw * 8)) /\
      (rw > 0 ==>
        (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
         U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
         U64.v fb - 8 + rw * 8 <= heap_size)) /\
      objs_well_separated g objs /\
      (forall (x: obj_addr). Seq.mem x objs ==>
        U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
      Seq.mem x (Seq.tail objs) /\ is_black x g)
    (ensures
      (let obj = Seq.head objs in
       forall (a: hp_addr).
         U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
         read_word (makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp))) a ==
         read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) a))
  = // Thin wrapper calling the top-level pointwise lemma — trivial VC for forall_intro
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (black_case_body_agree_aux g h_f h_c objs fb rw fp x))
#pop-options

/// ========================================================================
/// Non-black case helper: geometric condition for rest objects
/// ========================================================================
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let nonblack_case_geo_ok
    (g: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (x: obj_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      (let obj = Seq.head objs in
       let ws = U64.v (wosize_of_object obj g) in
       let new_fb = if rw = 0 then U64.v obj else U64.v fb in
       let new_rw = rw + ws + 1 in
       Seq.mem x (Seq.tail objs) /\
       (forall (y: obj_addr). Seq.mem y (Seq.tail objs) ==>
         U64.v y > U64.v obj + ws * 8) /\
       U64.v obj % 8 == 0 /\
       (rw > 0 ==> U64.v obj >= U64.v fb + rw * 8)))
    (ensures
      (let obj = Seq.head objs in
       let ws = U64.v (wosize_of_object obj g) in
       let new_fb = if rw = 0 then U64.v obj else U64.v fb in
       let new_rw = rw + ws + 1 in
       U64.v x >= new_fb + new_rw * 8))
  = let obj = Seq.head objs in
    let ws = U64.v (wosize_of_object obj g) in
    assert (U64.v x > U64.v obj + ws * 8);
    assert (U64.v x % 8 == 0);
    assert (U64.v obj % 8 == 0);
    ML.cancel_mul_mod ws 8;
    ML.modulo_addition_lemma 0 8 ws;
    assert ((U64.v obj + ws * 8) % 8 == 0);
    assert (U64.v x >= U64.v obj + ws * 8 + 8);
    ML.distributivity_add_left ws 1 8;
    assert (U64.v x >= U64.v obj + (ws + 1) * 8);
    if rw = 0 then ()
    else begin
      assert (U64.v obj >= U64.v fb + rw * 8);
      ML.distributivity_add_left rw (ws + 1) 8
    end
#pop-options

/// ========================================================================
/// Black case concluder: combines IH with one-step unfolding in a clean context
/// ========================================================================
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let black_case_conclude
    (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      ~(is_blue (Seq.head objs) gs) /\
      wosize_of_object (Seq.head objs) g == wosize_of_object (Seq.head objs) gs /\
      (let obj = Seq.head objs in
       let rest = Seq.tail objs in
       let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
       let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
       let fp' = snd (SpecCoalesce.flush_blue h_f fb rw fp) in
       let h_f'' = makeWhite obj h_f' in
       fp' == snd (SpecCoalesce.flush_blue h_c fb rw fp) /\
       fused_aux g h_f'' rest 0UL 0 fp' ==
       SpecCoalesce.coalesce_aux gs h_c' rest 0UL 0 fp'))
    (ensures
      fused_aux g h_f objs fb rw fp ==
      SpecCoalesce.coalesce_aux gs h_c objs fb rw fp)
  = ()
#pop-options

/// ========================================================================
/// Main theorem
/// ========================================================================

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"

let rec combined_proof
  (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  : Lemma
    (requires
      (* 1. Sizes *)
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\

      (* 2. Color correspondence *)
      (forall (x: obj_addr). Seq.mem x objs ==>
        (is_black x g <==> ~(is_blue x gs))) /\

      (* 3. Wosize correspondence *)
      (forall (x: obj_addr). Seq.mem x objs ==>
        wosize_of_object x g == wosize_of_object x gs) /\

      (* 4. Agree below bound *)
      (let bound = if rw > 0 then U64.v fb - 8
                   else if Seq.length objs > 0 then U64.v (hd_address (Seq.head objs))
                   else heap_size in
       forall (a: hp_addr). U64.v a + 8 <= bound ==> read_word h_f a == read_word h_c a) /\

      (* 5. Agree above *)
      (forall (a: hp_addr).
        (rw = 0 \/ U64.v a >= U64.v fb - 8 + rw * 8) /\
        (forall (x: obj_addr). Seq.mem x objs ==>
          U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8) ==>
        read_word h_f a == read_word h_c a) /\

      (* 6. Black header wosize/tag match *)
      (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==>
        getWosize (read_word h_f (hd_address x)) == getWosize (read_word h_c (hd_address x)) /\
        getTag (read_word h_f (hd_address x)) == getTag (read_word h_c (hd_address x))) /\

      (* 7. Black bodies agree *)
      (forall (x: obj_addr) (a: hp_addr).
        Seq.mem x objs /\ is_black x g /\
        U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
        read_word h_f a == read_word h_c a) /\

      (* 8. Black objects white in h_c *)
      (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==>
        is_white x h_c) /\

      (* 9. Geometric *)
      (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
        U64.v x >= U64.v fb + rw * 8)) /\

      (* 10. fb validity *)
      (rw > 0 ==>
        (U64.v fb >= U64.v mword /\
         U64.v fb < heap_size /\
         U64.v fb % U64.v mword == 0 /\
         rw - 1 < pow2 54 /\
         U64.v fb - 8 + rw * 8 <= heap_size)) /\

      (* 11. Well-separated *)
      objs_well_separated g objs /\

      (* 12. Contiguous *)
      objs_contiguous g objs /\

      (* 13. Run-object contiguity *)
      (rw > 0 /\ Seq.length objs > 0 ==>
        U64.v fb + rw * 8 == U64.v (Seq.head objs)) /\

      (* 14. Objects fit *)
      (forall (x: obj_addr). Seq.mem x objs ==>
        U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size))

    (ensures
      fused_aux g h_f objs fb rw fp ==
      SpecCoalesce.coalesce_aux gs h_c objs fb rw fp)

    (decreases Seq.length objs)

  = if Seq.length objs = 0 then begin
      // ============================================================
      // BASE CASE: both sides reduce to flush_blue
      // ============================================================
      if rw = 0 then begin
        let aux (a: hp_addr) : Lemma (read_word h_f a == read_word h_c a) = () in
        FStar.Classical.forall_intro aux;
        SCF.heaps_word_agree_implies_equal h_f h_c
      end else begin
        let aux (a: hp_addr)
          : Lemma
            (requires rw = 0 \/
                      U64.v a + U64.v mword <= U64.v fb - U64.v mword \/
                      U64.v a >= U64.v fb - U64.v mword + rw * U64.v mword)
            (ensures read_word h_f a == read_word h_c a)
          = ()
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        SCF.flush_blue_pair_agree h_f h_c fb rw fp
      end

    end else begin
      let obj = Seq.head objs in
      let rest = Seq.tail objs in

      if is_black obj g then begin
        // ============================================================
        // BLACK CASE — thin wrappers calling top-level helpers
        // ============================================================
        assert (~(is_blue obj gs));

        hd_address_spec obj;

        let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
        let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
        let fp'_f = snd (SpecCoalesce.flush_blue h_f fb rw fp) in
        let fp'_c = snd (SpecCoalesce.flush_blue h_c fb rw fp) in

        SCH.flush_blue_snd_heap_independent h_f h_c fb rw fp;
        assert (fp'_f == fp'_c);
        let fp' = fp'_f in

        SpecCoalesce.flush_blue_preserves_length h_f fb rw fp;
        SpecCoalesce.flush_blue_preserves_length h_c fb rw fp;

        let h_f'' = makeWhite obj h_f' in

        // Cond 4: Agree below new bound — thin wrapper over top-level helper
        let below_ok (a: hp_addr)
          : Lemma
            (requires
              (let nb = if Seq.length rest > 0
                        then U64.v (hd_address (Seq.head rest))
                        else heap_size in
               U64.v a + 8 <= nb))
            (ensures read_word h_f'' a == read_word h_c' a)
          = black_case_below_ok g h_f h_c objs fb rw fp a
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires below_ok);

        // Cond 5: Agree above — thin wrapper over top-level helper
        let above_ok (a: hp_addr)
          : Lemma
            (requires
              (forall (x: obj_addr). Seq.mem x rest ==>
                U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8))
            (ensures read_word h_f'' a == read_word h_c' a)
          = black_case_above_ok g h_f h_c objs fb rw fp a
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires above_ok);

        // Conds 6,8: header match + white in h_c' for rest
        let rest_hdr (x: obj_addr)
          : Lemma
            (requires Seq.mem x rest /\ is_black x g)
            (ensures
              getWosize (read_word h_f'' (hd_address x)) == getWosize (read_word h_c' (hd_address x)) /\
              getTag (read_word h_f'' (hd_address x)) == getTag (read_word h_c' (hd_address x)) /\
              is_white x h_c')
          = black_case_rest_headers g h_f h_c objs fb rw fp x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires rest_hdr);

        // Cond 7: black bodies agree in h_f'' and h_c' for rest
        let body_ok (x: obj_addr)
          : Lemma
            (requires Seq.mem x rest /\ is_black x g)
            (ensures forall (a: hp_addr).
              U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
              read_word h_f'' a == read_word h_c' a)
          = black_case_body_agree g h_f h_c objs fb rw fp x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires body_ok);

        // IH + concluder
        combined_proof g gs h_f'' h_c' rest 0UL 0 fp';
        black_case_conclude g gs h_f h_c objs fb rw fp

      end else begin
        // ============================================================
        // NON-BLACK CASE
        // ============================================================
        assert (is_blue obj gs);

        let ws = U64.v (wosize_of_object obj g) in
        let new_fb : U64.t = if rw = 0 then obj else fb in
        let new_rw = rw + ws + 1 in

        hd_address_spec obj;

        // Geometric for rest — thin wrapper over top-level helper
        let geo_ok (x: obj_addr)
          : Lemma
            (requires Seq.mem x rest)
            (ensures U64.v x >= U64.v new_fb + new_rw * 8)
          = nonblack_case_geo_ok g objs fb rw x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires geo_ok);

        // fb validity for new run
        assert (new_rw > 0);
        (if rw = 0 then begin
          assert (U64.v obj >= U64.v mword);
          assert (U64.v obj < heap_size);
          assert (U64.v obj % U64.v mword == 0);
          assert (ws * 8 <= heap_size);
          ML.lemma_div_le (ws * 8) heap_size 8;
          ML.cancel_mul_div ws 8;
          assert (ws <= heap_size / 8);
          // new_rw - 1 = ws, need ws < pow2 54
          // heap_size < pow2 57 so heap_size / pow2 3 < pow2 54
          ML.lemma_div_lt_nat heap_size 57 3;
          assert_norm (pow2 3 == 8);
          assert_norm (57 - 3 == 54);
          assert (heap_size / 8 < pow2 54);
          assert (ws < pow2 54);
          // also need: new_fb - 8 + new_rw * 8 <= heap_size
          // new_fb = obj, new_rw = ws + 1
          ML.distributivity_add_left ws 1 8;
          assert (U64.v obj - 8 + new_rw * 8 == U64.v obj + ws * 8);
          ()
        end else begin
          assert (U64.v fb + rw * 8 == U64.v obj);
          assert (U64.v obj + ws * 8 <= heap_size);
          ML.distributivity_add_left rw (ws + 1) 8;
          assert (U64.v fb - 8 + new_rw * 8 == U64.v obj + ws * 8);
          assert (U64.v fb - 8 + new_rw * 8 <= heap_size);
          // new_rw - 1 = rw + ws, need rw + ws < pow2 54
          // new_fb = fb, fb >= 8, so new_rw * 8 <= heap_size
          assert (U64.v fb >= 8);
          assert (new_rw * 8 <= heap_size);
          ML.lemma_div_le (new_rw * 8) heap_size 8;
          ML.cancel_mul_div new_rw 8;
          assert (new_rw <= heap_size / 8);
          ML.lemma_div_lt_nat heap_size 57 3;
          assert_norm (pow2 3 == 8);
          assert_norm (57 - 3 == 54);
          assert (heap_size / 8 < pow2 54);
          assert (new_rw - 1 < pow2 54);
          ()
        end);

        // Cond 13 for rest: run-object contiguity
        (if Seq.length rest > 0 then begin
          if rw = 0 then begin
            ML.distributivity_add_left ws 1 8;
            assert (U64.v new_fb + new_rw * 8 == U64.v obj + (ws + 1) * 8)
          end else begin
            assert (U64.v fb + rw * 8 == U64.v obj);
            ML.distributivity_add_left rw (ws + 1) 8;
            assert (U64.v new_fb + new_rw * 8 == U64.v obj + (ws + 1) * 8)
          end
        end else ());

        // IH
        combined_proof g gs h_f h_c rest new_fb new_rw fp

      end
    end

#pop-options
