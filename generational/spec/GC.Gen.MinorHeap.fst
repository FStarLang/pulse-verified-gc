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
      if next_pos > bump then false
      else minor_chain_valid data next_pos bump
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
                     (tag: nat{tag < 256})
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

/// ---------------------------------------------------------------------------
/// Chain validity helpers
/// ---------------------------------------------------------------------------

/// If data1 and data2 agree below bump, chain_valid transfers
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120"
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
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120"
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
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120"
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
/// Object walk structural lemmas
/// ---------------------------------------------------------------------------

/// Every element in the walk is a valid object address
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120"
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

let minor_objects_wosize_bound (ms: minor_state) (obj: U64.t)
  : Lemma (requires Seq.mem obj (minor_objects ms))
          (ensures (minor_wosize ms obj + 1) * 8 <= minor_heap_size) =
  if U64.v ms.bump > minor_heap_size || U64.v ms.bump % 8 <> 0 then ()
  else begin
    minor_objects_aux_valid ms.data 0 (U64.v ms.bump) obj;
    minor_objects_aux_wosize_bound_raw ms.data 0 (U64.v ms.bump) obj
  end

/// Walk produces same results when data agrees below bump
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120"
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
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120"
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
#push-options "--fuel 3 --ifuel 0 --z3rlimit 120"
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
#push-options "--fuel 3 --ifuel 0 --z3rlimit 200 --split_queries always"
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

/// ---------------------------------------------------------------------------
/// Main proofs
/// ---------------------------------------------------------------------------

#push-options "--fuel 3 --ifuel 0 --z3rlimit 150"
let minor_alloc_adds_object (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                            (tag: nat{tag < 256})
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
  // Now: minor_read_word data' ms.bump == hdr
  // And: U64.v (shift_right hdr 10ul) == wosize > 0
  // And: old_bump + (wosize+1)*8 == new_bump
  // And: minor_chain_valid data' 0 old_bump == true
  minor_chain_valid_extend data' old_bump new_bump hdr;
  // Now: minor_chain_valid data' 0 new_bump == true
  
  // obj_addr <> 0UL
  assert (old_bump + 8 >= 8);
  
  // Seq.mem obj_addr (minor_objects res.ms_out)
  // The walk from 0 to new_bump reaches old_bump and produces (old_bump + 8)
  assert (new_bump <= minor_heap_size);
  next_pos_mod8 old_bump wosize;
  assert (new_bump % 8 == 0);
  FStar.Math.Lemmas.lemma_mult_le_right 8 2 (wosize + 1);
  assert (new_bump > old_bump);
  minor_objects_aux_reaches_bump data' 0 old_bump new_bump
#pop-options

#push-options "--fuel 3 --ifuel 0 --z3rlimit 150"
let minor_alloc_preserves_existing (ms: minor_state) 
                                    (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                                    (tag: nat{tag < 256})
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
  // data' agrees with ms.data below old_bump
  minor_objects_aux_data_eq ms.data data' 0 old_bump;
  // x is in walk from 0 to old_bump in data'
  // Everything in walk to old_bump is also in walk to new_bump (subset)
  minor_objects_aux_subset data' 0 old_bump new_bump x;
  
  // Part 2: minor_wosize preservation
  minor_objects_valid ms x;
  let xv = U64.v x in
  let hdr_addr = xv - 8 in
  // Show hdr is below old_bump
  minor_objects_aux_next_bound ms.data 0 old_bump x;
  // From next_bound: wz > 0 and hdr_addr + (wz+1)*8 <= old_bump
  // So hdr_addr + 16 <= old_bump, meaning hdr_addr <= old_bump - 16 < old_bump
  assert (hdr_addr + 8 <= minor_heap_size);
  assert (hdr_addr < old_bump);
  // Write is at old_bump, header is at hdr_addr < old_bump, so they don't overlap
  minor_read_write_different ms.data ms.bump (U64.uint_to_t hdr_addr) hdr;
  // minor_read_word data' (uint_to_t hdr_addr) == minor_read_word ms.data (uint_to_t hdr_addr)
  
  // Part 3: field preservation
  let hdr_x = minor_read_word ms.data (U64.uint_to_t hdr_addr) in
  let wz_x = U64.v (U64.shift_right hdr_x 10ul) in
  // From next_bound: hdr_addr + (wz_x + 1) * 8 <= old_bump
  let aux (i:nat) : Lemma (requires i < wz_x) 
                           (ensures minor_read_field {data=data'; bump=U64.uint_to_t new_bump} x i == 
                                   minor_read_field ms x i) =
    let byte_offset = xv + i * 8 in
    // byte_offset + 8 = hdr_addr + (i+2)*8 <= hdr_addr + (wz_x+1)*8 <= old_bump
    FStar.Math.Lemmas.lemma_mult_le_right 8 (i + 2) (wz_x + 1);
    assert (byte_offset + 8 <= old_bump);
    FStar.Math.Lemmas.modulo_addition_lemma hdr_addr 8 (i + 1);
    assert (byte_offset % 8 == 0);
    minor_read_write_different ms.data ms.bump (U64.uint_to_t byte_offset) hdr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Reset
/// ---------------------------------------------------------------------------

let minor_reset (ms: minor_state) : Tot (ms':minor_state{minor_wf ms' /\ U64.v ms'.bump == 0}) =
  { data = ms.data; bump = 0UL }
