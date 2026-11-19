module GC.Gen.Run.NurseryFrame

friend GC.Gen.MinorHeap

open GC.Gen.Base
open GC.Gen.MinorHeap

module U64 = FStar.UInt64

let mod8_step (pos: nat{pos % 8 == 0}) (wz: nat) : Lemma ((pos + (wz + 1) * 8) % 8 == 0) =
  FStar.Math.Lemmas.lemma_mod_plus pos (wz + 1) 8

/// `s` is not a header the walk from `pos` visits.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let rec not_header (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
                   (s: nat) : GTot bool (decreases (bump - pos)) =
  if pos + 8 > bump then true
  else begin
    assert_norm (pow2 57 < pow2 64);
    let hdr = minor_read_word data (U64.uint_to_t pos) in
    let wz = U64.v (U64.shift_right hdr 10ul) in
    if wz = 0 then s <> pos
    else begin
      mod8_step pos wz;
      let next = pos + (wz + 1) * 8 in
      if next > bump then s <> pos else s <> pos && not_header data next bump s
    end
  end
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 20 --using_facts_from '* -FStar.UInt.to_vec -FStar.UInt.from_vec -FStar.BitVector'"
let rec write_not_header (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
                         (s: U64.t{U64.v s + 8 <= minor_heap_size /\ U64.v s % 8 == 0}) (v: U64.t)
  : Lemma (requires not_header data pos bump (U64.v s))
          (ensures minor_objects_aux (minor_write_word data s v) pos bump == minor_objects_aux data pos bump)
          (decreases (bump - pos))
  = if pos + 8 > bump then ()
    else begin
      assert_norm (pow2 57 < pow2 64);
      let hdr = minor_read_word data (U64.uint_to_t pos) in
      let wz = U64.v (U64.shift_right hdr 10ul) in
      minor_read_write_different data s (U64.uint_to_t pos) v;
      if wz = 0 then ()
      else begin
        mod8_step pos wz;
        let next = pos + (wz + 1) * 8 in
        if next > bump then ()
        else write_not_header data next bump s v
      end
    end

/// The walk from `pos` visits only headers at or after `pos`.
let rec not_header_below (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
                         (s: nat)
  : Lemma (requires s < pos) (ensures not_header data pos bump s) (decreases (bump - pos))
  = if pos + 8 > bump then ()
    else begin
      assert_norm (pow2 57 < pow2 64);
      let hdr = minor_read_word data (U64.uint_to_t pos) in
      let wz = U64.v (U64.shift_right hdr 10ul) in
      if wz = 0 then ()
      else begin
        mod8_step pos wz;
        let next = pos + (wz + 1) * 8 in
        if next > bump then () else not_header_below data next bump s
      end
    end

/// The objects of the walk from `pos` lie after `pos`.
let rec objects_after (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
                      (o: U64.t)
  : Lemma (requires Seq.mem o (minor_objects_aux data pos bump)) (ensures U64.v o >= pos + 8)
          (decreases (bump - pos))
  = if pos + 8 > bump then ()
    else begin
      assert_norm (pow2 57 < pow2 64);
      let hdr = minor_read_word data (U64.uint_to_t pos) in
      let wz = U64.v (U64.shift_right hdr 10ul) in
      if wz = 0 then ()
      else begin
        mod8_step pos wz;
        let next = pos + (wz + 1) * 8 in
        if next > bump then ()
        else begin
          Seq.Properties.mem_cons (U64.uint_to_t (pos + 8)) (minor_objects_aux data next bump);
          assert (U64.v (U64.uint_to_t (pos + 8)) == pos + 8);
          assert (minor_objects_aux data pos bump == Seq.cons (U64.uint_to_t (pos + 8)) (minor_objects_aux data next bump));
          assert (Seq.mem o (Seq.cons (U64.uint_to_t (pos + 8)) (minor_objects_aux data next bump)));
          if o = U64.uint_to_t (pos + 8) then ()
          else begin
            assert (Seq.mem o (minor_objects_aux data next bump));
            objects_after data next bump o;
            assert (U64.v o >= next + 8)
          end
        end
      end
    end

/// A word in the body of an object of the walk is not one of its headers.
let rec body_not_header (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
                        (o: U64.t) (s: nat)
  : Lemma (requires Seq.mem o (minor_objects_aux data pos bump) /\ U64.v o <= s /\
                    U64.v o >= 8 /\ U64.v o <= minor_heap_size /\ U64.v o % 8 == 0 /\
                    s < U64.v o + 8 * U64.v (U64.shift_right (minor_read_word data (U64.uint_to_t (U64.v o - 8))) 10ul))
          (ensures not_header data pos bump s)
          (decreases (bump - pos))
  = if pos + 8 > bump then ()
    else begin
      assert_norm (pow2 57 < pow2 64);
      let hdr = minor_read_word data (U64.uint_to_t pos) in
      let wz = U64.v (U64.shift_right hdr 10ul) in
      if wz = 0 then ()
      else begin
        mod8_step pos wz;
        let next = pos + (wz + 1) * 8 in
        if next > bump then ()
        else begin
          Seq.Properties.mem_cons (U64.uint_to_t (pos + 8)) (minor_objects_aux data next bump);
          assert (U64.v (U64.uint_to_t (pos + 8)) == pos + 8);
          assert (minor_objects_aux data pos bump == Seq.cons (U64.uint_to_t (pos + 8)) (minor_objects_aux data next bump));
          if o = U64.uint_to_t (pos + 8) then not_header_below data next bump s
          else begin
            objects_after data next bump o;
            body_not_header data next bump o s
          end
        end
      end
    end
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let write_body_keeps_objects ms o s v =
  assert_norm (pow2 57 < pow2 64);
  let ms' = { ms with data = minor_write_word_t ms.data s v } in
  assert (ms'.data == minor_write_word ms.data s v);
  let wz (x: U64.t) : Lemma (U64.v x <= U64.v s ==> minor_wosize ms' x == minor_wosize ms x) =
    if U64.v x >= 8 && U64.v x < minor_heap_size && U64.v x <= U64.v s && (U64.v x - 8) % 8 = 0 then
      minor_read_write_different ms.data s (U64.uint_to_t (U64.v x - 8)) v in
  FStar.Classical.forall_intro wz;
  if U64.v ms.bump > minor_heap_size || U64.v ms.bump % 8 <> 0 then ()
  else begin
    minor_objects_valid ms o;
    assert (U64.v o - 8 + 8 <= minor_heap_size /\ (U64.v o - 8) % 8 == 0);
    assert (minor_wosize ms o == U64.v (U64.shift_right (minor_read_word ms.data (U64.uint_to_t (U64.v o - 8))) 10ul));
    body_not_header ms.data 0 (U64.v ms.bump) o (U64.v s);
    write_not_header ms.data 0 (U64.v ms.bump) s v
  end
#pop-options
