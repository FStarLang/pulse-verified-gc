/// ---------------------------------------------------------------------------
/// GC.Gen.MinorHeap — Implementation of bump-pointer minor heap spec
/// ---------------------------------------------------------------------------

module GC.Gen.MinorHeap

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Gen.Base
module SpecHeap = GC.Spec.Heap

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let minor_read_word_zero_heap
  (addr: U64.t{U64.v addr + 8 <= minor_heap_size /\ U64.v addr % 8 == 0})
  : Lemma (minor_read_word (Seq.create minor_heap_size 0uy) addr == 0UL)
  =
  assert (Seq.index (Seq.create minor_heap_size 0uy) (U64.v addr) == 0uy);
  assert (Seq.index (Seq.create minor_heap_size 0uy) (U64.v addr + 1) == 0uy);
  assert (Seq.index (Seq.create minor_heap_size 0uy) (U64.v addr + 2) == 0uy);
  assert (Seq.index (Seq.create minor_heap_size 0uy) (U64.v addr + 3) == 0uy);
  assert (Seq.index (Seq.create minor_heap_size 0uy) (U64.v addr + 4) == 0uy);
  assert (Seq.index (Seq.create minor_heap_size 0uy) (U64.v addr + 5) == 0uy);
  assert (Seq.index (Seq.create minor_heap_size 0uy) (U64.v addr + 6) == 0uy);
  assert (Seq.index (Seq.create minor_heap_size 0uy) (U64.v addr + 7) == 0uy);
  assert_norm (minor_combine_bytes 0uy 0uy 0uy 0uy 0uy 0uy 0uy 0uy == 0UL)
#pop-options

/// ---------------------------------------------------------------------------
/// Chain validity (implements the val from .fsti)
/// ---------------------------------------------------------------------------

/// Helper: next_pos is 8-aligned when pos is 8-aligned
private let next_pos_mod8 (pos: nat{pos % 8 == 0}) (wz: nat)
  : Lemma (ensures (pos + (wz + 1) * 8) % 8 == 0) =
  FStar.Math.Lemmas.modulo_addition_lemma pos 8 (wz + 1)

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec minor_chain_valid (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : GTot bool (decreases (bump - pos)) =
  if pos + 8 > bump then true
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    if wz = 0 then false
    else
      let next_pos = pos + (wz + 1) * 8 in
      next_pos_mod8 pos wz;
      if next_pos > bump then false
      else minor_chain_valid data next_pos bump
  end
#pop-options

/// Chain no-infix: same walk structure, checks tag <> 249 at each header position.
/// Where chain_valid returns false (wz=0 or overflow), no_infix is vacuously true.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec minor_chain_no_infix (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : GTot bool (decreases (bump - pos)) =
  if pos + 8 > bump then true
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    let tag = U64.v (U64.logand hdr 0xFFUL) in
    if wz = 0 then true
    else
      let next_pos = pos + (wz + 1) * 8 in
      next_pos_mod8 pos wz;
      if next_pos > bump then true
      else tag <> 249 && minor_chain_no_infix data next_pos bump
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Initial state
/// ---------------------------------------------------------------------------

let minor_init (data: minor_heap) : Tot (ms:minor_state{minor_wf ms /\ U64.v ms.bump == 0}) =
  { data = data; bump = 0UL }

/// ---------------------------------------------------------------------------
/// Header construction
/// ---------------------------------------------------------------------------

let make_minor_header (wosize: nat{wosize > 0 /\ wosize < pow2 54})
                      (tag: nat{tag < 256}) : U64.t =
  assert_norm (pow2 54 < pow2 64);
  let wz = U64.uint_to_t wosize in
  let t = U64.uint_to_t tag in
  U64.logor (U64.shift_left wz 10ul) t

/// ---------------------------------------------------------------------------
/// Bump allocation
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let minor_alloc_spec (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                     (tag: nat{tag < 256 /\ tag <> 249})
  : Tot minor_alloc_result =
  if not (minor_can_alloc ms wosize) || U64.v ms.bump % 8 <> 0 then
    { ms_out = ms; obj_addr = 0UL }
  else begin
    assert_norm (pow2 57 < pow2 64);
    GC.Gen.Base.max_young_object_fits ();
    assert ((wosize + 1) * 8 <= minor_heap_size);
    assert (minor_heap_size < pow2 57);
    assert_norm (pow2 57 == 8 * pow2 54);
    assert (wosize < pow2 54);
    let hdr = make_minor_header wosize tag in
    let new_bump = U64.v ms.bump + (wosize + 1) * 8 in
    let data' = minor_write_word ms.data ms.bump hdr in
    let obj_offset = U64.v ms.bump + 8 in
    let ms' = { data = data'; bump = U64.uint_to_t new_bump } in
    { ms_out = ms'; obj_addr = U64.uint_to_t obj_offset }
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Object enumeration
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec minor_objects_aux (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : GTot (seq U64.t) (decreases (bump - pos)) =
  if pos + 8 > bump then Seq.empty
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    if wz = 0 then Seq.empty
    else
      let next_pos = pos + (wz + 1) * 8 in
      if next_pos > bump then Seq.empty
      else begin
        assert (wz >= 1);
        assert ((wz + 1) * 8 >= 2 * 8);
        Seq.cons (U64.uint_to_t (pos + 8)) (minor_objects_aux data next_pos bump)
      end
  end
#pop-options

let minor_objects (ms: minor_state) : GTot (seq U64.t) =
  if U64.v ms.bump > minor_heap_size || U64.v ms.bump % 8 <> 0 then Seq.empty
  else minor_objects_aux ms.data 0 (U64.v ms.bump)

/// ---------------------------------------------------------------------------
/// Read-write helpers
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let minor_read_write_different 
  (h: minor_heap) 
  (a1: U64.t{U64.v a1 + 8 <= minor_heap_size /\ U64.v a1 % 8 == 0})
  (a2: U64.t{U64.v a2 + 8 <= minor_heap_size /\ U64.v a2 % 8 == 0})
  (v: U64.t)
  : Lemma (requires U64.v a1 <> U64.v a2)
          (ensures minor_read_word (minor_write_word h a1 v) a2 == minor_read_word h a2) =
  let a1v = U64.v a1 in
  let a2v = U64.v a2 in
  assert (a1v + 8 <= a2v \/ a2v + 8 <= a1v);
  let h' = minor_write_word h a1 v in
  assert (Seq.index h' (a2v + 0) == Seq.index h (a2v + 0));
  assert (Seq.index h' (a2v + 1) == Seq.index h (a2v + 1));
  assert (Seq.index h' (a2v + 2) == Seq.index h (a2v + 2));
  assert (Seq.index h' (a2v + 3) == Seq.index h (a2v + 3));
  assert (Seq.index h' (a2v + 4) == Seq.index h (a2v + 4));
  assert (Seq.index h' (a2v + 5) == Seq.index h (a2v + 5));
  assert (Seq.index h' (a2v + 6) == Seq.index h (a2v + 6));
  assert (Seq.index h' (a2v + 7) == Seq.index h (a2v + 7))
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let minor_read_write_same
  (h: minor_heap) 
  (a: U64.t{U64.v a + 8 <= minor_heap_size /\ U64.v a % 8 == 0})
  (v: U64.t)
  : Lemma (ensures minor_read_word (minor_write_word h a v) a == v) =
  SpecHeap.combine_decompose_identity v
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let make_header_wosize (wosize: nat{wosize > 0 /\ wosize < pow2 54})
                       (tag: nat{tag < 256})
  : Lemma (U64.v (U64.shift_right (make_minor_header wosize tag) 10ul) == wosize) =
  assert_norm (pow2 54 < pow2 64);
  assert_norm (pow2 10 == 1024);
  let wz = U64.uint_to_t wosize in
  let t = U64.uint_to_t tag in
  assert_norm (pow2 54 * pow2 10 == pow2 64);
  FStar.UInt.logor_disjoint #64 (U64.v (U64.shift_left wz 10ul)) (U64.v t) 10;
  FStar.Math.Lemmas.lemma_div_plus tag wosize 1024;
  FStar.Math.Lemmas.small_div tag 1024
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let make_header_tag (wosize: nat{wosize > 0 /\ wosize < pow2 54})
                    (tag: nat{tag < 256})
  : Lemma (U64.v (U64.logand (make_minor_header wosize tag) 0xFFUL) == tag) =
  assert_norm (pow2 54 < pow2 64);
  assert_norm (pow2 10 == 1024);
  let wz = U64.uint_to_t wosize in
  let t = U64.uint_to_t tag in
  assert_norm (pow2 54 * pow2 10 == pow2 64);
  // wosize << 10 has low 10 bits = 0, so low 8 bits = 0
  // logor with t (< 256) gives low 8 bits = t
  FStar.UInt.logor_disjoint #64 (U64.v (U64.shift_left wz 10ul)) (U64.v t) 10;
  // logand with 0xFF extracts low 8 bits
  FStar.UInt.logand_le #64 (U64.v (make_minor_header wosize tag)) 255;
  // (wosize * 1024 + tag) % 256 == tag since tag < 256
  FStar.Math.Lemmas.lemma_mod_plus tag wosize 1024;
  assert_norm (1024 % 256 == 0);
  FStar.Math.Lemmas.modulo_division_lemma tag 256 4;
  assert (U64.v (make_minor_header wosize tag) % 256 == tag);
  FStar.UInt.logand_mask #64 (U64.v (make_minor_header wosize tag)) 8
#pop-options

/// ---------------------------------------------------------------------------
/// Chain validity helpers
/// ---------------------------------------------------------------------------

/// If data1 and data2 agree below bump, chain_valid transfers
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_chain_valid_read_eq
  (data1 data2: minor_heap)
  (pos: nat{pos % 8 == 0})
  (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Lemma (requires (forall (i:nat). i < bump ==> Seq.index data1 i == Seq.index data2 i) /\
                    minor_chain_valid data1 pos bump == true)
          (ensures minor_chain_valid data2 pos bump == true)
          (decreases (bump - pos)) =
  if pos + 8 > bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr1 = minor_read_word data1 (U64.uint_to_t pos) in
    let hdr2 = minor_read_word data2 (U64.uint_to_t pos) in
    assert (hdr1 == hdr2);
    let wz = U64.v (U64.shift_right hdr1 10ul) in
    assert (wz > 0);  // from chain_valid == true
    let next_pos = pos + (wz + 1) * 8 in
    FStar.Math.Lemmas.modulo_addition_lemma pos 8 (wz + 1);
    assert (next_pos % 8 == 0);
    assert (next_pos <= bump);  // from chain_valid == true
    minor_chain_valid_read_eq data1 data2 next_pos bump
  end
#pop-options

/// Writing at old_bump preserves chain_valid from 0 to old_bump
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let minor_chain_valid_write_preserved
  (data: minor_heap)
  (old_bump: nat{old_bump <= minor_heap_size /\ old_bump % 8 == 0})
  (addr: U64.t{U64.v addr == old_bump /\ U64.v addr + 8 <= minor_heap_size})
  (v: U64.t)
  : Lemma (requires minor_chain_valid data 0 old_bump == true)
          (ensures minor_chain_valid (minor_write_word data addr v) 0 old_bump == true) =
  let data' = minor_write_word data addr v in
  assert (forall (i:nat). i < old_bump ==> Seq.index data' i == Seq.index data i);
  minor_chain_valid_read_eq data data' 0 old_bump
#pop-options

/// Establish pow2 bound needed for U64.uint_to_t calls in preconditions
let minor_pow2_bound : squash (pow2 57 < pow2 64 /\ minor_heap_size < pow2 64) =
  assert_norm (pow2 57 < pow2 64)

/// Helper: unfold one level of minor_chain_valid to extract consequences
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let minor_chain_valid_unfold
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Lemma (requires pos + 8 <= bump /\ minor_chain_valid data pos bump == true)
          (ensures (let hdr = minor_read_word data (U64.uint_to_t pos) in
                    let wz = U64.v (U64.shift_right hdr 10ul) in
                    wz > 0 /\ pos + (wz + 1) * 8 <= bump /\
                    (pos + (wz + 1) * 8) % 8 == 0)) =
  assert_norm (pow2 57 < pow2 64);
  let hdr = minor_read_word data (U64.uint_to_t pos) in
  let wz = U64.v (U64.shift_right hdr 10ul) in
  next_pos_mod8 pos wz
#pop-options

/// Extend chain_valid: if chain_valid from pos to old_bump,
/// and at old_bump there's a valid header pointing to new_bump,
/// then chain_valid from pos to new_bump.
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_chain_valid_extend_aux
  (data: minor_heap)
  (pos: nat{pos % 8 == 0})
  (old_bump: nat{old_bump <= minor_heap_size /\ old_bump % 8 == 0})
  (new_bump: nat{new_bump <= minor_heap_size /\ new_bump % 8 == 0 /\ new_bump > old_bump})
  (hdr: U64.t)
  : Lemma (requires (let wz = U64.v (U64.shift_right hdr 10ul) in
                     wz > 0 /\ old_bump + (wz + 1) * 8 == new_bump /\
                     old_bump + 8 <= minor_heap_size /\
                     pos <= old_bump /\
                     minor_chain_valid data pos old_bump == true /\
                     minor_read_word data (U64.uint_to_t old_bump) == hdr))
          (ensures minor_chain_valid data pos new_bump == true)
          (decreases (old_bump - pos)) =
  assert_norm (pow2 57 < pow2 64);
  if pos = old_bump then ()
  else begin
    // pos < old_bump, so pos + 8 <= old_bump
    assert (pos < old_bump);
    assert (pos + 8 <= old_bump);
    // Unfold chain_valid at pos: wz_pos > 0, next_pos <= old_bump, chain_valid next_pos old_bump
    let hdr_at_pos = minor_read_word data (U64.uint_to_t pos) in
    let wz_pos = U64.v (U64.shift_right hdr_at_pos 10ul) in
    let next_pos = pos + (wz_pos + 1) * 8 in
    // These facts come from unfolding minor_chain_valid data pos old_bump
    assert (wz_pos > 0);
    assert (next_pos <= old_bump);
    FStar.Math.Lemmas.modulo_addition_lemma pos 8 (wz_pos + 1);
    assert (next_pos % 8 == 0);
    minor_chain_valid_extend_aux data next_pos old_bump new_bump hdr
  end
#pop-options

let minor_chain_valid_extend
  (data: minor_heap)
  (old_bump: nat{old_bump <= minor_heap_size /\ old_bump % 8 == 0})
  (new_bump: nat{new_bump <= minor_heap_size /\ new_bump % 8 == 0 /\ new_bump > old_bump})
  (hdr: U64.t)
  : Lemma (requires (let wz = U64.v (U64.shift_right hdr 10ul) in
                     wz > 0 /\ old_bump + (wz + 1) * 8 == new_bump /\
                     old_bump + 8 <= minor_heap_size /\
                     minor_chain_valid data 0 old_bump == true /\
                     minor_read_word data (U64.uint_to_t old_bump) == hdr))
          (ensures minor_chain_valid data 0 new_bump == true) =
  minor_chain_valid_extend_aux data 0 old_bump new_bump hdr

/// ---------------------------------------------------------------------------
/// Chain no-infix helpers (parallel to chain_valid helpers)
/// ---------------------------------------------------------------------------

/// If data1 and data2 agree below bump, no_infix transfers
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_chain_no_infix_read_eq
  (data1 data2: minor_heap)
  (pos: nat{pos % 8 == 0})
  (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Lemma (requires (forall (i:nat). i < bump ==> Seq.index data1 i == Seq.index data2 i) /\
                    minor_chain_no_infix data1 pos bump == true)
          (ensures minor_chain_no_infix data2 pos bump == true)
          (decreases (bump - pos)) =
  if pos + 8 > bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr1 = minor_read_word data1 (U64.uint_to_t pos) in
    let hdr2 = minor_read_word data2 (U64.uint_to_t pos) in
    assert (hdr1 == hdr2);
    let wz = U64.v (U64.shift_right hdr1 10ul) in
    if wz = 0 then ()
    else begin
      let next_pos = pos + (wz + 1) * 8 in
      FStar.Math.Lemmas.modulo_addition_lemma pos 8 (wz + 1);
      if next_pos > bump then ()
      else minor_chain_no_infix_read_eq data1 data2 next_pos bump
    end
  end
#pop-options

/// Writing at old_bump preserves no_infix from 0 to old_bump
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let minor_chain_no_infix_write_preserved
  (data: minor_heap)
  (old_bump: nat{old_bump <= minor_heap_size /\ old_bump % 8 == 0})
  (addr: U64.t{U64.v addr == old_bump /\ U64.v addr + 8 <= minor_heap_size})
  (v: U64.t)
  : Lemma (requires minor_chain_no_infix data 0 old_bump == true)
          (ensures minor_chain_no_infix (minor_write_word data addr v) 0 old_bump == true) =
  let data' = minor_write_word data addr v in
  assert (forall (i:nat). i < old_bump ==> Seq.index data' i == Seq.index data i);
  minor_chain_no_infix_read_eq data data' 0 old_bump
#pop-options

/// Extend no_infix: if no_infix from pos to old_bump, and the header at old_bump
/// has tag <> 249, then no_infix extends to new_bump.
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_chain_no_infix_extend_aux
  (data: minor_heap)
  (pos: nat{pos % 8 == 0})
  (old_bump: nat{old_bump <= minor_heap_size /\ old_bump % 8 == 0})
  (new_bump: nat{new_bump <= minor_heap_size /\ new_bump % 8 == 0 /\ new_bump > old_bump})
  (hdr: U64.t)
  : Lemma (requires (let wz = U64.v (U64.shift_right hdr 10ul) in
                     let tag = U64.v (U64.logand hdr 0xFFUL) in
                     wz > 0 /\ old_bump + (wz + 1) * 8 == new_bump /\
                     old_bump + 8 <= minor_heap_size /\
                     pos <= old_bump /\
                     tag <> 249 /\
                     minor_chain_valid data pos old_bump == true /\
                     minor_chain_no_infix data pos old_bump == true /\
                     minor_read_word data (U64.uint_to_t old_bump) == hdr))
          (ensures minor_chain_no_infix data pos new_bump == true)
          (decreases (old_bump - pos)) =
  assert_norm (pow2 57 < pow2 64);
  if pos = old_bump then ()
  else begin
    assert (pos < old_bump);
    assert (pos + 8 <= old_bump);
    let hdr_at_pos = minor_read_word data (U64.uint_to_t pos) in
    let wz_pos = U64.v (U64.shift_right hdr_at_pos 10ul) in
    let next_pos = pos + (wz_pos + 1) * 8 in
    assert (wz_pos > 0);
    assert (next_pos <= old_bump);
    FStar.Math.Lemmas.modulo_addition_lemma pos 8 (wz_pos + 1);
    assert (next_pos % 8 == 0);
    minor_chain_no_infix_extend_aux data next_pos old_bump new_bump hdr
  end
#pop-options

let minor_chain_no_infix_extend
  (data: minor_heap)
  (old_bump: nat{old_bump <= minor_heap_size /\ old_bump % 8 == 0})
  (new_bump: nat{new_bump <= minor_heap_size /\ new_bump % 8 == 0 /\ new_bump > old_bump})
  (hdr: U64.t)
  : Lemma (requires (let wz = U64.v (U64.shift_right hdr 10ul) in
                     let tag = U64.v (U64.logand hdr 0xFFUL) in
                     wz > 0 /\ old_bump + (wz + 1) * 8 == new_bump /\
                     old_bump + 8 <= minor_heap_size /\
                     tag <> 249 /\
                     minor_chain_valid data 0 old_bump == true /\
                     minor_chain_no_infix data 0 old_bump == true /\
                     minor_read_word data (U64.uint_to_t old_bump) == hdr))
          (ensures minor_chain_no_infix data 0 new_bump == true) =
  minor_chain_no_infix_extend_aux data 0 old_bump new_bump hdr

/// ---------------------------------------------------------------------------
/// Object walk structural lemmas
/// ---------------------------------------------------------------------------

/// Every element in the walk is a valid object address
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_objects_aux_valid (data: minor_heap) (pos: nat{pos % 8 == 0}) 
                                 (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
                                 (x: U64.t)
  : Lemma (requires Seq.mem x (minor_objects_aux data pos bump))
          (ensures U64.v x >= 8 /\ U64.v x < minor_heap_size /\ U64.v x % 8 == 0)
          (decreases (bump - pos)) =
  if pos + 8 > bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    if wz = 0 then ()
    else begin
      let next_pos = pos + (wz + 1) * 8 in
      next_pos_mod8 pos wz;
      if next_pos > bump then ()
      else begin
        let obj_addr = U64.uint_to_t (pos + 8) in
        let tail = minor_objects_aux data next_pos bump in
        FStar.Seq.Properties.mem_cons obj_addr tail;
        if x = obj_addr then begin
          FStar.Math.Lemmas.lemma_mult_le_right 8 2 (wz + 1);
          FStar.Math.Lemmas.modulo_addition_lemma pos 8 1
        end else
          minor_objects_aux_valid data next_pos bump x
      end
    end
  end
#pop-options

let minor_objects_valid (ms: minor_state) (x: U64.t)
  : Lemma (requires Seq.mem x (minor_objects ms))
          (ensures U64.v x >= 8 /\ U64.v x < minor_heap_size /\ U64.v x % 8 == 0) =
  if U64.v ms.bump > minor_heap_size || U64.v ms.bump % 8 <> 0 then ()
  else minor_objects_aux_valid ms.data 0 (U64.v ms.bump) x

/// Tag of a minor header is always < 256 (logand with 0xFF)
let minor_tag_bound (ms: minor_state) (obj: U64.t)
  : Lemma (minor_tag ms obj < 256)
  = if U64.v obj >= 8 && U64.v obj < minor_heap_size then
      let hdr_addr = U64.v obj - 8 in
      if hdr_addr + 8 <= minor_heap_size && hdr_addr % 8 = 0 then
        let hdr = minor_read_word ms.data (U64.uint_to_t hdr_addr) in
        FStar.UInt.logand_le #64 (U64.v hdr) 255
      else ()
    else ()

/// ---------------------------------------------------------------------------
/// Wosize bound for minor objects
/// ---------------------------------------------------------------------------

/// Objects returned by minor_objects_aux have wosize < minor_heap_size.
/// Proof: at each step, pos + (wz+1)*8 <= bump <= minor_heap_size,
/// so wz+1 <= minor_heap_size/8, thus wz < minor_heap_size.
#push-options "--fuel 2 --ifuel 0 --z3rlimit 60"
private let rec minor_objects_aux_wosize_bound_raw
  (data: minor_heap) (pos: nat{pos % 8 == 0})
  (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  (x: U64.t)
  : Lemma (requires Seq.mem x (minor_objects_aux data pos bump) /\
                    U64.v x >= 8 /\ U64.v x < minor_heap_size /\ U64.v x % 8 == 0)
          (ensures (let hdr_addr = U64.v x - 8 in
                    hdr_addr >= 0 /\
                    hdr_addr + 8 <= minor_heap_size /\
                    hdr_addr % 8 == 0 /\
                    (let hdr = minor_read_word data (U64.uint_to_t hdr_addr) in
                     (U64.v (U64.shift_right hdr 10ul) + 1) * 8 <= minor_heap_size)))
          (decreases (bump - pos)) =
  if pos + 8 > bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    if wz = 0 then ()
    else begin
      let next_pos = pos + (wz + 1) * 8 in
      next_pos_mod8 pos wz;
      if next_pos > bump then ()
      else begin
        let obj_addr = U64.uint_to_t (pos + 8) in
        let tail = minor_objects_aux data next_pos bump in
        FStar.Seq.Properties.mem_cons obj_addr tail;
        if x = obj_addr then begin
          // x = obj_addr = pos + 8, so hdr_addr = pos
          // wz read from header at pos, and next_pos = pos + (wz+1)*8 <= bump <= minor_heap_size
          assert (U64.v x - 8 == pos);
          assert (pos + (wz + 1) * 8 <= minor_heap_size)
        end else begin
          minor_objects_aux_valid data next_pos bump x;
          minor_objects_aux_wosize_bound_raw data next_pos bump x
        end
      end
    end
  end
#pop-options

/// infix_parent_value: unfolds infix_parent definition and proves the value
let infix_parent_value (ms: minor_state) (addr: U64.t)
  : Lemma (requires is_infix_in_minor ms addr /\ minor_infix_wf ms)
          (ensures U64.v (infix_parent ms addr) == U64.v addr - minor_wosize ms addr * 8) =
  reveal_opaque (`%minor_infix_wf) (minor_infix_wf ms);
  let wz = minor_wosize ms addr in
  let off = wz * 8 in
  // From minor_infix_wf: wz * 8 <= U64.v addr - 8, hence off <= U64.v addr
  assert (off <= U64.v addr);
  // infix_parent takes the `then` branch, returning uint_to_t (v addr - off)
  assert (infix_parent ms addr == U64.uint_to_t (U64.v addr - off));
  // The value is in range [0, 2^64), so the roundtrip works
  assert (U64.v addr - off >= 0);
  assert (U64.v addr - off < pow2 64)

let infix_parent_in_minor_objects (ms: minor_state) (addr: U64.t)
  : Lemma (requires is_infix_in_minor ms addr /\ minor_infix_wf ms)
          (ensures (let parent = infix_parent ms addr in
                    Seq.mem parent (minor_objects ms) /\
                    U64.v parent >= 8 /\
                    U64.v parent % 8 == 0 /\
                    U64.v addr - U64.v parent < minor_wosize ms parent * 8)) =
  reveal_opaque (`%minor_infix_wf) (minor_infix_wf ms)

/// Infix sub-objects (tag=249) are never in minor_objects (when minor_wf holds).
/// Proved by induction on minor_objects_aux using minor_chain_no_infix.
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
private let rec minor_objects_aux_no_infix
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  (x: U64.t)
  : Lemma (requires Seq.mem x (minor_objects_aux data pos bump) /\
                    minor_chain_valid data pos bump == true /\
                    minor_chain_no_infix data pos bump == true)
          (ensures (let xv = U64.v x in
                    xv >= 8 /\ xv < minor_heap_size /\
                    (let hdr_pos = xv - 8 in
                     hdr_pos + 8 <= minor_heap_size /\ hdr_pos % 8 == 0 /\
                     U64.v (U64.logand (minor_read_word data (U64.uint_to_t hdr_pos)) 0xFFUL) <> 249)))
          (decreases (bump - pos)) =
  if pos + 8 > bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    let tag = U64.v (U64.logand hdr 0xFFUL) in
    // From chain_valid: wz > 0
    assert (wz > 0);
    let next_pos = pos + (wz + 1) * 8 in
    next_pos_mod8 pos wz;
    // From chain_valid: next_pos <= bump
    assert (next_pos <= bump);
    // From no_infix: tag <> 249
    assert (tag <> 249);
    let obj_addr = U64.uint_to_t (pos + 8) in
    let tail = minor_objects_aux data next_pos bump in
    FStar.Seq.Properties.mem_cons obj_addr tail;
    if x = obj_addr then begin
      // x = pos + 8, so hdr_pos = pos
      FStar.Math.Lemmas.lemma_mult_le_right 8 2 (wz + 1);
      FStar.Math.Lemmas.modulo_addition_lemma pos 8 1;
      assert (U64.v x == pos + 8);
      assert (U64.v x - 8 == pos);
      assert (U64.v (U64.logand (minor_read_word data (U64.uint_to_t pos)) 0xFFUL) <> 249)
    end else begin
      // x is in the tail
      minor_objects_aux_no_infix data next_pos bump x
    end
  end
#pop-options

let minor_objects_not_infix (ms: minor_state) (addr: U64.t)
  : Lemma (requires minor_wf ms /\ Seq.mem addr (minor_objects ms))
          (ensures minor_tag ms addr <> 249) =
  if U64.v ms.bump > minor_heap_size || U64.v ms.bump % 8 <> 0 then ()
  else begin
    minor_objects_aux_no_infix ms.data 0 (U64.v ms.bump) addr;
    minor_objects_aux_valid ms.data 0 (U64.v ms.bump) addr;
    // minor_tag reads the header at addr - 8 and extracts tag via logand 0xFF
    // minor_objects_aux_no_infix proves that tag <> 249 at that position
    ()
  end

let minor_objects_wosize_bound (ms: minor_state) (obj: U64.t)
  : Lemma (requires Seq.mem obj (minor_objects ms))
          (ensures (minor_wosize ms obj + 1) * 8 <= minor_heap_size) =
  if U64.v ms.bump > minor_heap_size || U64.v ms.bump % 8 <> 0 then ()
  else begin
    minor_objects_aux_valid ms.data 0 (U64.v ms.bump) obj;
    minor_objects_aux_wosize_bound_raw ms.data 0 (U64.v ms.bump) obj
  end

/// Walk produces same results when data agrees below bump
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_objects_aux_data_eq
  (data1 data2: minor_heap)
  (pos: nat{pos % 8 == 0})
  (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Lemma (requires (forall (i:nat). i < bump ==> Seq.index data1 i == Seq.index data2 i))
          (ensures minor_objects_aux data1 pos bump == minor_objects_aux data2 pos bump)
          (decreases (bump - pos)) =
  if pos + 8 > bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr1 = minor_read_word data1 (U64.uint_to_t pos) in
    let hdr2 = minor_read_word data2 (U64.uint_to_t pos) in
    assert (hdr1 == hdr2);
    let wz = U64.v (U64.shift_right hdr1 10ul) in
    if wz = 0 then ()
    else begin
      let next_pos = pos + (wz + 1) * 8 in
      next_pos_mod8 pos wz;
      if next_pos > bump then ()
      else minor_objects_aux_data_eq data1 data2 next_pos bump
    end
  end
#pop-options

/// If chain_valid from pos to both old_bump and new_bump (>=old_bump),
/// everything in the walk with old_bump is also in the walk with new_bump
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_objects_aux_subset
  (data: minor_heap)
  (pos: nat{pos % 8 == 0})
  (old_bump: nat{old_bump <= minor_heap_size /\ old_bump % 8 == 0})
  (new_bump: nat{new_bump <= minor_heap_size /\ new_bump % 8 == 0 /\ new_bump >= old_bump})
  (x: U64.t)
  : Lemma (requires minor_chain_valid data pos old_bump == true /\
                    minor_chain_valid data pos new_bump == true /\
                    Seq.mem x (minor_objects_aux data pos old_bump))
          (ensures Seq.mem x (minor_objects_aux data pos new_bump))
          (decreases (old_bump - pos)) =
  if pos + 8 > old_bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    assert (wz > 0);
    let next_pos = pos + (wz + 1) * 8 in
    assert (next_pos <= old_bump);
    next_pos_mod8 pos wz;
    assert (next_pos <= new_bump);
    let obj = U64.uint_to_t (pos + 8) in
    let tail_old = minor_objects_aux data next_pos old_bump in
    FStar.Seq.Properties.mem_cons obj tail_old;
    let tail_new = minor_objects_aux data next_pos new_bump in
    FStar.Seq.Properties.mem_cons obj tail_new;
    if x = obj then ()
    else minor_objects_aux_subset data next_pos old_bump new_bump x
  end
#pop-options

/// Walk from pos reaches old_bump and produces (old_bump + 8)
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_objects_aux_reaches_bump
  (data: minor_heap)
  (pos: nat{pos % 8 == 0})
  (old_bump: nat{old_bump <= minor_heap_size /\ old_bump % 8 == 0})
  (new_bump: nat{new_bump <= minor_heap_size /\ new_bump % 8 == 0 /\ new_bump > old_bump})
  : Lemma (requires minor_chain_valid data pos old_bump == true /\
                    minor_chain_valid data pos new_bump == true /\
                    pos <= old_bump /\
                    old_bump + 8 <= new_bump)
          (ensures Seq.mem (U64.uint_to_t (old_bump + 8)) (minor_objects_aux data pos new_bump))
          (decreases (old_bump - pos)) =
  assert_norm (pow2 57 < pow2 64);
  if pos = old_bump then begin
    // Walk with new_bump at pos: pos + 8 <= new_bump
    // chain_valid data pos new_bump gives wz > 0 and next <= new_bump
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    assert (wz > 0);
    let next_pos = pos + (wz + 1) * 8 in
    assert (next_pos <= new_bump);
    next_pos_mod8 pos wz;
    // Walk produces (pos + 8) = (old_bump + 8) as first element
    let obj = U64.uint_to_t (pos + 8) in
    let tail = minor_objects_aux data next_pos new_bump in
    FStar.Seq.Properties.mem_cons obj tail
  end else begin
    // pos < old_bump, and both are 8-aligned, so pos + 8 <= old_bump
    // pos <= old_bump from precond, pos ≠ old_bump from else, both % 8 = 0
    FStar.Math.Lemmas.modulo_lemma 1 8;
    assert (pos + 8 <= old_bump);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    // chain_valid data pos old_bump: wz > 0, next <= old_bump
    assert (wz > 0);
    let next_pos = pos + (wz + 1) * 8 in
    assert (next_pos <= old_bump);
    next_pos_mod8 pos wz;
    assert (next_pos <= new_bump);
    // By IH: (old_bump + 8) is in walk from next_pos with new_bump
    minor_objects_aux_reaches_bump data next_pos old_bump new_bump;
    // Walk from pos = cons (pos+8) (walk from next_pos)
    let obj = U64.uint_to_t (pos + 8) in
    let tail = minor_objects_aux data next_pos new_bump in
    FStar.Seq.Properties.mem_cons obj tail
  end
#pop-options

/// For objects in the walk with chain_valid, their next_pos <= bump
#push-options "--fuel 3 --ifuel 0 --z3rlimit 200 --split_queries always --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let rec minor_objects_aux_next_bound
  (data: minor_heap)
  (pos: nat{pos % 8 == 0})
  (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  (x: U64.t)
  : Lemma (requires minor_chain_valid data pos bump == true /\
                    Seq.mem x (minor_objects_aux data pos bump))
          (ensures (let xv = U64.v x in
                    xv >= 8 /\ (xv - 8) % 8 == 0 /\ (xv - 8) + 8 <= minor_heap_size /\
                    (let hdr_pos = xv - 8 in
                     let hdr = minor_read_word data (U64.uint_to_t hdr_pos) in
                     let wz = U64.v (U64.shift_right hdr 10ul) in
                     wz > 0 /\ hdr_pos + (wz + 1) * 8 <= bump)))
          (decreases (bump - pos)) =
  assert_norm (pow2 57 < pow2 64);
  if pos + 8 > bump then ()
  else begin
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    assert (wz > 0);
    let next_pos = pos + (wz + 1) * 8 in
    next_pos_mod8 pos wz;
    assert (next_pos <= bump);
    let obj = U64.uint_to_t (pos + 8) in
    let tail = minor_objects_aux data next_pos bump in
    FStar.Seq.Properties.mem_cons obj tail;
    if x = obj then begin
      assert (U64.v x == pos + 8);
      assert (U64.v x - 8 == pos);
      assert (pos + (wz + 1) * 8 <= bump)
    end else
      minor_objects_aux_next_bound data next_pos bump x
  end
#pop-options

#push-options "--fuel 3 --ifuel 0 --z3rlimit 200 --split_queries always --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let minor_objects_body_bound (ms: minor_state) (obj: U64.t)
  : Lemma (requires minor_wf ms /\ Seq.mem obj (minor_objects ms))
          (ensures minor_wosize ms obj > 0 /\
                   U64.v obj + minor_wosize ms obj * 8 <= minor_heap_size /\
                   minor_wosize ms obj < minor_heap_size)
  =
  minor_objects_aux_next_bound ms.data 0 (U64.v ms.bump) obj;
  let xv = U64.v obj in
  let hdr_pos = xv - 8 in
  let hdr = minor_read_word ms.data (U64.uint_to_t hdr_pos) in
  let wz = U64.v (U64.shift_right hdr 10ul) in
  assert (wz > 0);
  assert (hdr_pos + (wz + 1) * 8 <= U64.v ms.bump);
  assert (xv + wz * 8 <= U64.v ms.bump);
  assert (U64.v ms.bump <= minor_heap_size)
#pop-options

/// ---------------------------------------------------------------------------
/// Main proofs
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let minor_alloc_success_layout (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                               (tag: nat{tag < 256 /\ tag <> 249})
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize)
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    res.obj_addr == U64.uint_to_t (U64.v ms.bump + 8) /\
                    U64.v res.ms_out.bump == U64.v ms.bump + (wosize + 1) * 8)) =
  assert (U64.v ms.bump % 8 == 0);
  assert (not (minor_can_alloc ms wosize) == false);
  assert (U64.v ms.bump % 8 <> 0 == false);
  assert ((not (minor_can_alloc ms wosize)) || U64.v ms.bump % 8 <> 0 == false);
  assert_norm (pow2 57 < pow2 64);
  GC.Gen.Base.max_young_object_fits ();
  assert ((wosize + 1) * 8 <= minor_heap_size);
  assert (minor_heap_size < pow2 57);
  assert_norm (pow2 57 == 8 * pow2 54);
  assert (wosize < pow2 54)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let minor_alloc_success_wosize (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                               (tag: nat{tag < 256 /\ tag <> 249})
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize)
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    minor_wosize res.ms_out res.obj_addr == wosize)) =
  minor_alloc_success_layout ms wosize tag;
  assert_norm (pow2 57 < pow2 64);
  GC.Gen.Base.max_young_object_fits ();
  assert (minor_heap_size < pow2 57);
  assert_norm (pow2 57 == 8 * pow2 54);
  assert (wosize < pow2 54);
  let hdr = make_minor_header wosize tag in
  let res = minor_alloc_spec ms wosize tag in
  assert (res.obj_addr == U64.uint_to_t (U64.v ms.bump + 8));
  assert (U64.v res.obj_addr == U64.v ms.bump + 8);
  assert (U64.v res.obj_addr >= 8);
  assert (U64.v res.obj_addr < minor_heap_size);
  assert (U64.v res.obj_addr - 8 == U64.v ms.bump);
  minor_read_write_same ms.data ms.bump hdr;
  make_header_wosize wosize tag
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let minor_alloc_success_tag (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                            (tag: nat{tag < 256 /\ tag <> 249})
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize)
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    minor_tag res.ms_out res.obj_addr == tag)) =
  minor_alloc_success_layout ms wosize tag;
  assert_norm (pow2 57 < pow2 64);
  GC.Gen.Base.max_young_object_fits ();
  assert (minor_heap_size < pow2 57);
  assert_norm (pow2 57 == 8 * pow2 54);
  assert (wosize < pow2 54);
  let hdr = make_minor_header wosize tag in
  let res = minor_alloc_spec ms wosize tag in
  assert (res.obj_addr == U64.uint_to_t (U64.v ms.bump + 8));
  assert (U64.v res.obj_addr == U64.v ms.bump + 8);
  assert (U64.v res.obj_addr >= 8);
  assert (U64.v res.obj_addr < minor_heap_size);
  assert (U64.v res.obj_addr - 8 == U64.v ms.bump);
  minor_read_write_same ms.data ms.bump hdr;
  make_header_tag wosize tag
#pop-options

#push-options "--fuel 3 --ifuel 0 --z3rlimit 150 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let minor_alloc_adds_object (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                            (tag: nat{tag < 256 /\ tag <> 249})
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize)
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    minor_wf res.ms_out /\
                    res.obj_addr <> 0UL /\
                    Seq.mem res.obj_addr (minor_objects res.ms_out))) =
  assert_norm (pow2 57 < pow2 64);
  assert_norm (pow2 57 == 8 * pow2 54);
  GC.Gen.Base.max_young_object_fits ();
  let old_bump = U64.v ms.bump in
  let new_bump = old_bump + (wosize + 1) * 8 in
  assert (wosize < pow2 54);
  let hdr = make_minor_header wosize tag in
  let data' = minor_write_word ms.data ms.bump hdr in
  
  // Show chain_valid for new state (data', new_bump)
  minor_chain_valid_write_preserved ms.data old_bump ms.bump hdr;
  minor_read_write_same ms.data ms.bump hdr;
  make_header_wosize wosize tag;
  make_header_tag wosize tag;
  next_pos_mod8 old_bump wosize;
  assert (new_bump % 8 == 0);
  // Now: minor_read_word data' ms.bump == hdr
  // And: U64.v (shift_right hdr 10ul) == wosize > 0
  // And: old_bump + (wosize+1)*8 == new_bump
  // And: minor_chain_valid data' 0 old_bump == true
  FStar.Math.Lemmas.lemma_mult_le_right 8 2 (wosize + 1);
  assert (new_bump > old_bump);
  minor_chain_valid_extend data' old_bump new_bump hdr;
  // Now: minor_chain_valid data' 0 new_bump == true
  
  // Show chain_no_infix for new state
  minor_chain_no_infix_write_preserved ms.data old_bump ms.bump hdr;
  assert (U64.v (U64.logand hdr 0xFFUL) == tag);
  assert (tag <> 249);
  minor_chain_no_infix_extend data' old_bump new_bump hdr;
  // Now: minor_chain_no_infix data' 0 new_bump == true
  
  // obj_addr <> 0UL
  assert (old_bump + 8 >= 8);
  
  // Seq.mem obj_addr (minor_objects res.ms_out)
  // The walk from 0 to new_bump reaches old_bump and produces (old_bump + 8)
  assert (new_bump <= minor_heap_size);
  minor_objects_aux_reaches_bump data' 0 old_bump new_bump
#pop-options

#push-options "--fuel 3 --ifuel 0 --z3rlimit 150 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"
let minor_alloc_preserves_existing (ms: minor_state) 
                                    (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                                    (tag: nat{tag < 256 /\ tag <> 249})
                                    (x: U64.t)
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize /\
                    Seq.mem x (minor_objects ms))
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    Seq.mem x (minor_objects res.ms_out) /\
                    minor_wosize res.ms_out x == minor_wosize ms x /\
                    (forall (i:nat). i < minor_wosize ms x ==>
                      minor_read_field res.ms_out x i == minor_read_field ms x i))) =
  assert_norm (pow2 57 < pow2 64);
  assert_norm (pow2 57 == 8 * pow2 54);
  GC.Gen.Base.max_young_object_fits ();
  let old_bump = U64.v ms.bump in
  let new_bump = old_bump + (wosize + 1) * 8 in
  assert (wosize < pow2 54);
  next_pos_mod8 old_bump wosize;
  FStar.Math.Lemmas.lemma_mult_le_right 8 2 (wosize + 1);
  let hdr = make_minor_header wosize tag in
  let data' = minor_write_word ms.data ms.bump hdr in
  
  // Establish chain_valid for new state
  minor_chain_valid_write_preserved ms.data old_bump ms.bump hdr;
  minor_read_write_same ms.data ms.bump hdr;
  make_header_wosize wosize tag;
  minor_chain_valid_extend data' old_bump new_bump hdr;
  
  // Part 1: Seq.mem x (minor_objects res.ms_out)
  minor_objects_aux_data_eq ms.data data' 0 old_bump;
  minor_objects_aux_subset data' 0 old_bump new_bump x;
  
  // Part 2: minor_wosize preservation
  minor_objects_valid ms x;
  let xv = U64.v x in
  let hdr_addr = xv - 8 in
  minor_objects_aux_next_bound ms.data 0 old_bump x;
  assert (hdr_addr + 8 <= minor_heap_size);
  assert (hdr_addr < old_bump);
  minor_read_write_different ms.data ms.bump (U64.uint_to_t hdr_addr) hdr;
  
  // Part 3: field preservation — delegate to extracted helper
  let hdr_x = minor_read_word ms.data (U64.uint_to_t hdr_addr) in
  let wz_x = U64.v (U64.shift_right hdr_x 10ul) in
  let aux (i:nat) : Lemma (requires i < wz_x)
                           (ensures minor_read_field {data=data'; bump=U64.uint_to_t new_bump} x i ==
                                   minor_read_field ms x i) =
    // The field read only depends on data and x, not on bump
    FStar.Math.Lemmas.lemma_mult_le_right 8 (i + 2) (wz_x + 1);
    let byte_offset = xv + i * 8 in
    assert (byte_offset + 8 <= old_bump);
    // byte_offset = hdr_addr + (i+1)*8, so byte_offset % 8 == hdr_addr % 8 == 0
    assert (byte_offset == hdr_addr + (i + 1) * 8);
    FStar.Math.Lemmas.modulo_addition_lemma hdr_addr 8 (i + 1);
    assert (byte_offset % 8 == 0);
    minor_read_write_different ms.data ms.bump (U64.uint_to_t byte_offset) hdr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let minor_alloc_preserves_word_outside_header
  (ms: minor_state)
  (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
  (tag: nat{tag < 256 /\ tag <> 249})
  (addr: U64.t{U64.v addr + 8 <= minor_heap_size /\ U64.v addr % 8 == 0})
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize /\
                    U64.v addr <> U64.v ms.bump)
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    minor_read_word res.ms_out.data addr == minor_read_word ms.data addr))
  =
  minor_alloc_success_layout ms wosize tag;
  assert_norm (pow2 57 < pow2 64);
  GC.Gen.Base.max_young_object_fits ();
  assert (minor_heap_size < pow2 57);
  assert_norm (pow2 57 == 8 * pow2 54);
  assert (wosize < pow2 54);
  let hdr = make_minor_header wosize tag in
  minor_read_write_different ms.data ms.bump addr hdr
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let minor_alloc_fresh_field_read
  (ms: minor_state)
  (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
  (tag: nat{tag < 256 /\ tag <> 249})
  (j: nat)
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize /\ j < wosize)
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    let field_addr = U64.uint_to_t (U64.v ms.bump + 8 + j * 8) in
                    minor_read_field res.ms_out res.obj_addr j ==
                    minor_read_word ms.data field_addr))
  =
  minor_alloc_success_layout ms wosize tag;
  assert (U64.v ms.bump + (wosize + 1) * 8 <= minor_heap_size);
  FStar.Math.Lemmas.lemma_mult_le_right 8 (j + 1) wosize;
  assert ((j + 1) * 8 <= wosize * 8);
  let field_nat = U64.v ms.bump + 8 + j * 8 in
  assert (field_nat + 8 <= minor_heap_size);
  assert (field_nat % 8 == 0);
  assert (field_nat < pow2 64);
  let field_addr = U64.uint_to_t field_nat in
  assert (U64.v field_addr == field_nat);
  assert (U64.v field_addr <> U64.v ms.bump);
  minor_alloc_preserves_word_outside_header ms wosize tag field_addr;
  let res = minor_alloc_spec ms wosize tag in
  assert (U64.v res.obj_addr == U64.v ms.bump + 8);
  assert (U64.v res.obj_addr + j * 8 == field_nat)
#pop-options

/// ---------------------------------------------------------------------------
/// Reset
/// ---------------------------------------------------------------------------

let minor_reset (ms: minor_state)
  : Tot (ms':minor_state{
      minor_wf ms' /\
      U64.v ms'.bump == 0 /\
      ms'.data == Seq.create minor_heap_size 0uy
    })
  =
  { data = Seq.create minor_heap_size 0uy; bump = 0UL }

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let zeroed_minor_read_word (addr: U64.t)
  : Lemma (requires U64.v addr + 8 <= minor_heap_size /\
                    U64.v addr % 8 == 0)
          (ensures minor_read_word (Seq.create minor_heap_size 0uy) addr == 0UL)
  =
  FStar.Seq.Base.lemma_index_create minor_heap_size 0uy (U64.v addr);
  FStar.Seq.Base.lemma_index_create minor_heap_size 0uy (U64.v addr + 1);
  FStar.Seq.Base.lemma_index_create minor_heap_size 0uy (U64.v addr + 2);
  FStar.Seq.Base.lemma_index_create minor_heap_size 0uy (U64.v addr + 3);
  FStar.Seq.Base.lemma_index_create minor_heap_size 0uy (U64.v addr + 4);
  FStar.Seq.Base.lemma_index_create minor_heap_size 0uy (U64.v addr + 5);
  FStar.Seq.Base.lemma_index_create minor_heap_size 0uy (U64.v addr + 6);
  FStar.Seq.Base.lemma_index_create minor_heap_size 0uy (U64.v addr + 7);
  assert_norm (minor_combine_bytes 0uy 0uy 0uy 0uy 0uy 0uy 0uy 0uy == 0UL)

let minor_reset_wosize_zero (ms: minor_state) (addr: U64.t)
  : Lemma (ensures minor_wosize (minor_reset ms) addr == 0)
  =
  if U64.v addr >= 8 && U64.v addr < minor_heap_size then begin
    let hdr_addr = U64.v addr - 8 in
    if hdr_addr + 8 <= minor_heap_size && hdr_addr % 8 = 0 then begin
      assert_norm (pow2 57 < pow2 64);
      assert (hdr_addr < pow2 64);
      let h = U64.uint_to_t hdr_addr in
      assert (U64.v h == hdr_addr);
      assert (U64.v h + 8 <= minor_heap_size);
      assert (U64.v h % 8 == 0);
      zeroed_minor_read_word h;
      assert (minor_read_word (Seq.create minor_heap_size 0uy) h == 0UL);
      assert (minor_wosize (minor_reset ms) addr == 0)
    end
  end

let minor_reset_objects_empty (ms: minor_state)
  : Lemma (ensures minor_objects (minor_reset ms) == Seq.empty)
  = ()

let minor_reset_objects_not_mem (ms: minor_state) (addr: U64.t)
  : Lemma (ensures ~(Seq.mem addr (minor_objects (minor_reset ms))))
  =
  minor_reset_objects_empty ms;
  assert_norm (Seq.count addr Seq.empty == 0)

private let minor_reset_tag_zero (ms: minor_state) (addr: U64.t)
  : Lemma (ensures minor_tag (minor_reset ms) addr == 0)
  =
  if U64.v addr >= 8 && U64.v addr < minor_heap_size then begin
    let hdr_addr = U64.v addr - 8 in
    if hdr_addr + 8 <= minor_heap_size && hdr_addr % 8 = 0 then begin
      assert_norm (pow2 57 < pow2 64);
      assert (hdr_addr < pow2 64);
      let h = U64.uint_to_t hdr_addr in
      assert (U64.v h == hdr_addr);
      assert (U64.v h + 8 <= minor_heap_size);
      assert (U64.v h % 8 == 0);
      zeroed_minor_read_word h;
      assert (minor_read_word (Seq.create minor_heap_size 0uy) h == 0UL);
      assert (minor_tag (minor_reset ms) addr == U64.v (U64.logand 0UL 0xFFUL));
      assert_norm (U64.v (U64.logand 0UL 0xFFUL) == 0)
    end
  end

let minor_reset_no_infix (ms: minor_state) (addr: U64.t)
  : Lemma (ensures ~(is_infix_in_minor (minor_reset ms) addr))
  =
  minor_reset_tag_zero ms addr
#pop-options

/// Each minor object consumes at least 16 bytes (8 header + 8 body with wosize >= 1),
/// so |minor_objects| <= bump / 16 <= minor_heap_size / 16.
#push-options "--fuel 4 --ifuel 0 --z3rlimit 40 --using_facts_from '* -FStar.UInt.to_vec -FStar.BitVector'"

/// Pure counting function matching minor_objects_aux structure
private let rec minor_objects_aux_count
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : GTot nat (decreases (bump - pos))
  =
  if pos + 8 > bump then 0
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    if wz = 0 then 0
    else
      let next_pos = pos + (wz + 1) * 8 in
      if next_pos > bump then 0
      else 1 + minor_objects_aux_count data next_pos bump
  end

/// Count equals Seq.length
private let rec minor_objects_aux_count_eq_length
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Lemma (ensures minor_objects_aux_count data pos bump == Seq.length (minor_objects_aux data pos bump))
          (decreases (bump - pos))
  =
  if pos + 8 > bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    if wz = 0 then ()
    else
      let next_pos = pos + (wz + 1) * 8 in
      if next_pos > bump then ()
      else begin
        minor_objects_aux_count_eq_length data next_pos bump;
        Seq.Base.lemma_len_append (Seq.create 1 (U64.uint_to_t (pos + 8))) (minor_objects_aux data next_pos bump)
      end
  end

/// Count that uses chain_valid, simpler recursive structure
private let rec minor_chain_count
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Pure nat (requires minor_chain_valid data pos bump == true)
             (ensures fun _ -> True)
             (decreases (bump - pos))
  =
  if pos + 8 > bump then 0
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    let next_pos = pos + (wz + 1) * 8 in
    1 + minor_chain_count data next_pos bump
  end

/// Count bound — return refined type instead of Lemma to avoid WP encoding issues
private let rec minor_chain_count_bounded
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Pure (n:nat{16 * n <= bump - pos})
         (requires minor_chain_valid data pos bump == true /\ pos <= bump)
         (ensures fun n -> n == minor_chain_count data pos bump)
         (decreases (bump - pos))
  =
  if pos + 8 > bump then 0
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    let next_pos = pos + (wz + 1) * 8 in
    next_pos_mod8 pos wz;
    let tail_count = minor_chain_count_bounded data next_pos bump in
    1 + tail_count
  end

/// Wrapper lemma
private let minor_chain_count_bound
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Lemma (requires minor_chain_valid data pos bump == true /\ pos <= bump)
          (ensures 16 * minor_chain_count data pos bump <= bump - pos)
  = let _ = minor_chain_count_bounded data pos bump in ()

/// Chain count equals objects_aux count
private let rec minor_chain_count_eq
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Lemma (requires minor_chain_valid data pos bump == true)
          (ensures minor_chain_count data pos bump == minor_objects_aux_count data pos bump)
          (decreases (bump - pos))
  =
  if pos + 8 > bump then ()
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    let next_pos = pos + (wz + 1) * 8 in
    next_pos_mod8 pos wz;
    minor_chain_count_eq data next_pos bump
  end

/// Combine: bound on Seq.length
private let minor_objects_aux_count_bound
  (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : Lemma (requires minor_chain_valid data pos bump == true /\ pos <= bump)
          (ensures 16 * Seq.length (minor_objects_aux data pos bump) <= bump - pos)
  =
  minor_chain_count_bound data pos bump;
  minor_chain_count_eq data pos bump;
  minor_objects_aux_count_eq_length data pos bump
#pop-options

let minor_objects_count_bound (ms: minor_state)
  : Lemma (requires minor_wf ms)
          (ensures Seq.length (minor_objects ms) <= minor_heap_size / 16 /\
                   Seq.length (minor_objects ms) < minor_heap_size / 8)
  =
  minor_objects_aux_count_bound ms.data 0 (U64.v ms.bump);
  // 16 * |minor_objects ms| <= bump - 0 = bump <= minor_heap_size
  // So |minor_objects ms| <= minor_heap_size / 16
  FStar.Math.Lemmas.lemma_div_le (16 * Seq.length (minor_objects ms)) minor_heap_size 16;
  assert_norm (minor_heap_size / 16 < minor_heap_size / 8)

/// ---------------------------------------------------------------------------
/// Zero Bump Lemma (for SPOT)
/// ---------------------------------------------------------------------------

/// When bump is 0, there are no objects
let minor_objects_zero_bump (ms: minor_state)
  : Lemma (requires U64.v ms.bump == 0)
          (ensures minor_objects ms == Seq.empty)
  = // When bump==0, minor_objects calls minor_objects_aux data 0 0
    // The definition checks: if pos + 8 > bump, i.e., if 0 + 8 > 0
    // which is true, so it returns Seq.empty
    assert_norm (0 + 8 > 0);
    ()
