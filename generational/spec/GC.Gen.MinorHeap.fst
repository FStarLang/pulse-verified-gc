/// ---------------------------------------------------------------------------
/// GC.Gen.MinorHeap — Implementation of bump-pointer minor heap spec
/// ---------------------------------------------------------------------------

module GC.Gen.MinorHeap

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Gen.Base

/// ---------------------------------------------------------------------------
/// Initial state
/// ---------------------------------------------------------------------------

let minor_init (data: minor_heap) : GTot (ms:minor_state{minor_wf ms /\ U64.v ms.bump == 0}) =
  { data = data; bump = 0UL }

/// ---------------------------------------------------------------------------
/// Header construction (same layout as major heap)
/// ---------------------------------------------------------------------------

/// Build a header word: wosize in bits 10-63, color in bits 8-9, tag in bits 0-7
let make_minor_header (wosize: nat{wosize > 0 /\ wosize < pow2 54})
                      (tag: nat{tag < 256}) : U64.t =
  assert_norm (pow2 54 < pow2 64);
  let wz = U64.uint_to_t wosize in
  let t = U64.uint_to_t tag in
  // wosize << 10 | 0 (white color) | tag
  U64.logor (U64.shift_left wz 10ul) t

/// ---------------------------------------------------------------------------
/// Bump allocation
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let minor_alloc_spec (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                     (tag: nat{tag < 256})
  : GTot minor_alloc_result =
  if not (minor_can_alloc ms wosize) || U64.v ms.bump % 8 <> 0 then
    { ms_out = ms; obj_addr = 0UL }
  else begin
    assert_norm (pow2 57 < pow2 64);
    // minor_heap_size < pow2 57 (from fsti refinement)
    // new_bump <= minor_heap_size (from minor_can_alloc)
    // Therefore new_bump < pow2 64
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

/// Walk from position 0 up to bump, reading headers to determine object sizes
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
        // Termination: wz >= 1, so (wz+1)*8 >= 16, so next_pos >= pos + 16 > pos
        // Therefore bump - next_pos < bump - pos
        assert (wz >= 1);
        assert ((wz + 1) * 8 >= 2 * 8);
        let obj_addr = pos + 8 in
        Seq.cons (U64.uint_to_t obj_addr) (minor_objects_aux data next_pos bump)
      end
  end
#pop-options

let minor_objects (ms: minor_state) : GTot (seq U64.t) =
  if U64.v ms.bump > minor_heap_size || U64.v ms.bump % 8 <> 0 then Seq.empty
  else minor_objects_aux ms.data 0 (U64.v ms.bump)

/// ---------------------------------------------------------------------------
/// Lemmas (admitted for now — will prove in Phase 2.3)
/// ---------------------------------------------------------------------------

let minor_objects_valid (ms: minor_state) (x: U64.t)
  : Lemma (requires Seq.mem x (minor_objects ms))
          (ensures U64.v x >= 8 /\ U64.v x < minor_heap_size /\ U64.v x % 8 == 0) =
  admit ()

let minor_alloc_adds_object (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                            (tag: nat{tag < 256})
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize)
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    minor_wf res.ms_out /\
                    res.obj_addr <> 0UL /\
                    Seq.mem res.obj_addr (minor_objects res.ms_out))) =
  admit ()

let minor_alloc_preserves_existing (ms: minor_state) 
                                    (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                                    (tag: nat{tag < 256})
                                    (x: U64.t)
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize /\
                    Seq.mem x (minor_objects ms))
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    Seq.mem x (minor_objects res.ms_out) /\
                    minor_wosize res.ms_out x == minor_wosize ms x /\
                    (forall (i:nat). i >= 1 /\ i <= minor_wosize ms x ==>
                      minor_read_field res.ms_out x i == minor_read_field ms x i))) =
  admit ()

/// ---------------------------------------------------------------------------
/// Reset
/// ---------------------------------------------------------------------------

let minor_reset (ms: minor_state) : GTot (ms':minor_state{minor_wf ms' /\ U64.v ms'.bump == 0}) =
  { data = ms.data; bump = 0UL }
