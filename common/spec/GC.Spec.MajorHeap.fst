/// ---------------------------------------------------------------------------
/// GC.Spec.MajorHeap - Pure chunked major-heap model
/// ---------------------------------------------------------------------------
///
/// This module introduces the non-moving chunk abstraction used for heap
/// expansion. It intentionally lives next to the existing dense heap model:
/// existing collectors can keep using GC.Spec.Heap while new expansion proofs
/// are built around active chunk membership.

module GC.Spec.MajorHeap

open FStar.Seq

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module Obj = GC.Spec.Object

open GC.Spec.Base
open GC.Spec.Heap

type chunk_id = nat

type heap_chunk = {
  base: hp_addr;
  size: s:pos{s % U64.v mword == 0 /\ s >= 16 /\ U64.v base + s <= heap_size};
  bytes: b:seq U8.t{Seq.length b == size};
}

type major_heap = seq heap_chunk

let single_chunk_size : s:pos{s % U64.v mword == 0 /\ s >= 16 /\
                              U64.v zero_addr + s <= heap_size} =
  let s = heap_size - U64.v zero_addr in
  FStar.Math.Lemmas.lemma_mod_sub_distr heap_size (U64.v zero_addr) (U64.v mword);
  assert (s % U64.v mword == 0);
  assert (s > U64.v mword);
  assert (s >= 16);
  s

let single_chunk_of_heap (g: heap) : heap_chunk =
  let bytes = Seq.slice g (U64.v zero_addr) heap_size in
  assert (Seq.length bytes == single_chunk_size);
  { base = zero_addr; size = single_chunk_size; bytes = bytes }

let single_chunk_major_heap (g: heap) : major_heap =
  Seq.cons (single_chunk_of_heap g) Seq.empty

let chunk_start (c: heap_chunk) : nat = U64.v c.base

let chunk_end (c: heap_chunk) : nat = U64.v c.base + c.size

let chunk_contains_addr (c: heap_chunk) (addr: U64.t) : Tot bool =
  U64.v addr >= chunk_start c && U64.v addr < chunk_end c

let word_in_chunk (c: heap_chunk) (addr: U64.t) : Tot bool =
  U64.v addr >= chunk_start c && U64.v addr + U64.v mword <= chunk_end c

let obj_addr_in_chunk (c: heap_chunk) (obj: obj_addr) : Tot bool =
  U64.v obj >= chunk_start c + U64.v mword && U64.v obj < chunk_end c

let object_payload_end (obj: obj_addr) (wz: nat) : nat =
  U64.v obj + wz * U64.v mword

let object_fits_in_chunk (c: heap_chunk) (obj: obj_addr) (wz: nat) : Tot bool =
  obj_addr_in_chunk c obj && object_payload_end obj wz <= chunk_end c

let obj_addr_in_chunk_header_word (c: heap_chunk) (obj: obj_addr{obj_addr_in_chunk c obj})
  : Lemma (word_in_chunk c (hd_address obj))
  = hd_address_spec obj

let chunk_offset (c: heap_chunk) (addr: U64.t{chunk_contains_addr c addr}) : nat =
  U64.v addr - chunk_start c

let chunks_disjoint (c1 c2: heap_chunk) : Tot prop =
  chunk_end c1 <= chunk_start c2 \/ chunk_end c2 <= chunk_start c1

let chunks_disjoint_symmetric (c1 c2: heap_chunk)
  : Lemma (requires chunks_disjoint c1 c2)
          (ensures chunks_disjoint c2 c1)
  = ()

let chunks_disjoint_no_shared_addr (c1 c2: heap_chunk) (addr: U64.t)
  : Lemma (requires chunks_disjoint c1 c2 /\ chunk_contains_addr c1 addr)
          (ensures ~(chunk_contains_addr c2 addr))
  = ()

let chunk_disjoint_from_all (c: heap_chunk) (chunks: major_heap) : Tot prop =
  forall i. i < Seq.length chunks ==> chunks_disjoint c (Seq.index chunks i)

let rec chunks_pairwise_disjoint (chunks: major_heap) : Tot prop
  (decreases Seq.length chunks)
  = if Seq.length chunks = 0 then True
    else
      let hd = Seq.head chunks in
      let tl = Seq.tail chunks in
      (forall i. i < Seq.length tl ==> chunks_disjoint hd (Seq.index tl i)) /\
      chunks_pairwise_disjoint tl

let well_formed_major_heap (mh: major_heap) : Tot prop =
  chunks_pairwise_disjoint mh

let add_chunk (mh: major_heap) (c: heap_chunk) : major_heap =
  Seq.cons c mh

let add_chunk_preserves_wf (mh: major_heap) (c: heap_chunk)
  : Lemma (requires well_formed_major_heap mh /\ chunk_disjoint_from_all c mh)
          (ensures well_formed_major_heap (add_chunk mh c))
  = assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh)

let rec lookup_chunk (mh: major_heap) (addr: hp_addr) : Tot (option heap_chunk)
  (decreases Seq.length mh)
  = if Seq.length mh = 0 then None
    else
      let c = Seq.head mh in
      if chunk_contains_addr c addr then Some c else lookup_chunk (Seq.tail mh) addr

let lookup_add_chunk_hit (mh: major_heap) (c: heap_chunk)
                          (addr: hp_addr{chunk_contains_addr c addr})
  : Lemma (lookup_chunk (add_chunk mh c) addr == Some c)
  = assert (Seq.head (add_chunk mh c) == c)

let lookup_add_chunk_miss (mh: major_heap) (c: heap_chunk)
                           (addr: hp_addr{~(chunk_contains_addr c addr)})
  : Lemma (lookup_chunk (add_chunk mh c) addr == lookup_chunk mh addr)
  = assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh);
    if chunk_contains_addr c addr then assert False else ()

let chunk_disjoint_from_all_tail (c: heap_chunk) (mh: major_heap{Seq.length mh > 0})
  : Lemma (requires chunk_disjoint_from_all c mh)
          (ensures chunk_disjoint_from_all c (Seq.tail mh))
  = assert (forall i. i < Seq.length (Seq.tail mh) ==>
              Seq.index (Seq.tail mh) i == Seq.index mh (i + 1));
    assert (forall i. i < Seq.length (Seq.tail mh) ==>
              chunks_disjoint c (Seq.index (Seq.tail mh) i))

let rec lookup_chunk_disjoint_none (mh: major_heap) (c: heap_chunk)
                                  (addr: hp_addr{chunk_contains_addr c addr})
  : Lemma (requires chunk_disjoint_from_all c mh)
          (ensures lookup_chunk mh addr == None)
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then ()
    else
      let hd = Seq.head mh in
      if chunk_contains_addr hd addr then begin
        chunks_disjoint_symmetric c hd;
        chunks_disjoint_no_shared_addr hd c addr;
        assert False
      end else begin
        chunk_disjoint_from_all_tail c mh;
        lookup_chunk_disjoint_none (Seq.tail mh) c addr
      end

let read_word_in_chunk (c: heap_chunk) (addr: hp_addr{word_in_chunk c addr}) : U64.t =
  let off = chunk_offset c addr in
  combine_bytes
    (Seq.index c.bytes off)
    (Seq.index c.bytes (off + 1))
    (Seq.index c.bytes (off + 2))
    (Seq.index c.bytes (off + 3))
    (Seq.index c.bytes (off + 4))
    (Seq.index c.bytes (off + 5))
    (Seq.index c.bytes (off + 6))
    (Seq.index c.bytes (off + 7))

let write_word_in_chunk (c: heap_chunk) (addr: hp_addr{word_in_chunk c addr}) (value: U64.t)
  : heap_chunk =
  let off = chunk_offset c addr in
  let bytes = Seq.upd c.bytes off (uint64_to_uint8 value) in
  let bytes = Seq.upd bytes (off + 1) (uint64_to_uint8 (U64.shift_right value 8ul)) in
  let bytes = Seq.upd bytes (off + 2) (uint64_to_uint8 (U64.shift_right value 16ul)) in
  let bytes = Seq.upd bytes (off + 3) (uint64_to_uint8 (U64.shift_right value 24ul)) in
  let bytes = Seq.upd bytes (off + 4) (uint64_to_uint8 (U64.shift_right value 32ul)) in
  let bytes = Seq.upd bytes (off + 5) (uint64_to_uint8 (U64.shift_right value 40ul)) in
  let bytes = Seq.upd bytes (off + 6) (uint64_to_uint8 (U64.shift_right value 48ul)) in
  let bytes = Seq.upd bytes (off + 7) (uint64_to_uint8 (U64.shift_right value 56ul)) in
  { c with bytes = bytes }

let read_word_in_major (mh: major_heap) (addr: hp_addr) : Tot (option U64.t) =
  match lookup_chunk mh addr with
  | None -> None
  | Some c ->
    if word_in_chunk c addr then Some (read_word_in_chunk c addr) else None

let rec write_word_in_major (mh: major_heap) (addr: hp_addr) (value: U64.t)
  : Tot (option major_heap) (decreases Seq.length mh)
  = if Seq.length mh = 0 then None
    else
      let c = Seq.head mh in
      let tl = Seq.tail mh in
      if word_in_chunk c addr then
        Some (Seq.cons (write_word_in_chunk c addr value) tl)
      else
        match write_word_in_major tl addr value with
        | None -> None
        | Some tl' -> Some (Seq.cons c tl')

let read_word_add_chunk_hit (mh: major_heap) (c: heap_chunk)
                            (addr: hp_addr{word_in_chunk c addr})
  : Lemma (read_word_in_major (add_chunk mh c) addr == Some (read_word_in_chunk c addr))
  = lookup_add_chunk_hit mh c addr

let read_word_add_chunk_miss (mh: major_heap) (c: heap_chunk)
                             (addr: hp_addr{~(chunk_contains_addr c addr)})
  : Lemma (read_word_in_major (add_chunk mh c) addr == read_word_in_major mh addr)
  = lookup_add_chunk_miss mh c addr

let read_word_disjoint_none (mh: major_heap) (c: heap_chunk)
                            (addr: hp_addr{word_in_chunk c addr})
  : Lemma (requires chunk_disjoint_from_all c mh)
          (ensures read_word_in_major mh addr == None)
  = assert (chunk_contains_addr c addr);
    lookup_chunk_disjoint_none mh c addr

let single_chunk_read_word_compat (g: heap)
                                  (addr: hp_addr{U64.v addr >= U64.v zero_addr /\
                                                 U64.v addr + U64.v mword <= heap_size})
  : Lemma (read_word_in_major (single_chunk_major_heap g) addr == Some (read_word g addr))
  = let c = single_chunk_of_heap g in
    assert (word_in_chunk c addr);
    assert (chunk_contains_addr c addr);
    lookup_add_chunk_hit Seq.empty c addr;
    let off = chunk_offset c addr in
    assert (off + U64.v zero_addr == U64.v addr);
    read_word_spec g addr;
    assert (Seq.index c.bytes off == Seq.index g (U64.v addr));
    assert (Seq.index c.bytes (off + 1) == Seq.index g (U64.v addr + 1));
    assert (Seq.index c.bytes (off + 2) == Seq.index g (U64.v addr + 2));
    assert (Seq.index c.bytes (off + 3) == Seq.index g (U64.v addr + 3));
    assert (Seq.index c.bytes (off + 4) == Seq.index g (U64.v addr + 4));
    assert (Seq.index c.bytes (off + 5) == Seq.index g (U64.v addr + 5));
    assert (Seq.index c.bytes (off + 6) == Seq.index g (U64.v addr + 6));
    assert (Seq.index c.bytes (off + 7) == Seq.index g (U64.v addr + 7))

let next_object_start_aligned (start: hp_addr) (obj_size_words: nat)
  : Lemma (requires U64.v start % U64.v mword == 0)
          (ensures (U64.v start + obj_size_words * U64.v mword) % U64.v mword == 0)
  = assert_norm (U64.v mword == 8);
    assert (U64.v start % 8 == 0);
    FStar.Math.Lemmas.lemma_mod_plus_distr_l
      (U64.v start) (obj_size_words * 8) 8;
    FStar.Math.Lemmas.cancel_mul_mod obj_size_words 8;
    assert ((obj_size_words * 8) % 8 == 0);
    assert (((U64.v start % 8) + obj_size_words * 8) % 8 == 0);
    assert ((U64.v start + obj_size_words * 8) % 8 == 0)

let rec objects_in_chunk_from (c: heap_chunk) (start: hp_addr) : Tot (seq obj_addr)
  (decreases chunk_end c - U64.v start)
  = if U64.v start < chunk_start c then Seq.empty
    else if U64.v start + U64.v mword >= chunk_end c then Seq.empty
    else
      let header = read_word_in_chunk c start in
      let wz = Obj.getWosize header in
      let obj_size_words = U64.v wz + 1 in
      let next_start_nat = U64.v start + obj_size_words * U64.v mword in
      if next_start_nat > chunk_end c || next_start_nat >= pow2 64 then Seq.empty
      else begin
        assert (U64.v start + U64.v mword < heap_size);
        let obj_addr = f_address start in
        if next_start_nat >= chunk_end c then Seq.cons obj_addr Seq.empty
        else begin
          assert (next_start_nat < heap_size);
          assert (next_start_nat < pow2 64);
          next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          Seq.cons obj_addr (objects_in_chunk_from c next_start)
        end
      end

let objects_in_chunk (c: heap_chunk) : seq obj_addr =
  objects_in_chunk_from c c.base

let rec objects_in_chunk_from_member_in_chunk (c: heap_chunk) (start: hp_addr) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects_in_chunk_from c start))
          (ensures obj_addr_in_chunk c x)
          (decreases chunk_end c - U64.v start)
  = if U64.v start < chunk_start c then
      assert False
    else if U64.v start + U64.v mword >= chunk_end c then
      assert False
    else begin
      let header = read_word_in_chunk c start in
      let wz = Obj.getWosize header in
      let obj_size_words = U64.v wz + 1 in
      let next_start_nat = U64.v start + obj_size_words * U64.v mword in
      if next_start_nat > chunk_end c || next_start_nat >= pow2 64 then
        assert False
      else begin
        let obj_addr = f_address start in
        f_address_spec start;
        assert (U64.v obj_addr == U64.v start + U64.v mword);
        let tail =
          if next_start_nat >= chunk_end c then Seq.empty
          else begin
            assert (next_start_nat < heap_size);
            assert (next_start_nat < pow2 64);
            next_object_start_aligned start obj_size_words;
            assert (next_start_nat % U64.v mword == 0);
            let next_start : hp_addr = U64.uint_to_t next_start_nat in
            objects_in_chunk_from c next_start
          end
        in
        SeqProps.mem_cons obj_addr tail;
        if x = obj_addr then begin
          assert (U64.v x >= chunk_start c + U64.v mword);
          assert (U64.v x < chunk_end c)
        end else begin
          assert (Seq.mem x tail);
          if next_start_nat >= chunk_end c then
            assert False
          else begin
            assert (obj_size_words >= 1);
            assert (next_start_nat > U64.v start);
            let next_start : hp_addr = U64.uint_to_t next_start_nat in
            objects_in_chunk_from_member_in_chunk c next_start x
          end
        end
      end
    end

let objects_in_chunk_member_in_chunk (c: heap_chunk) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects_in_chunk c))
          (ensures obj_addr_in_chunk c x)
  = objects_in_chunk_from_member_in_chunk c c.base x

let rec major_objects (mh: major_heap) : Tot (seq obj_addr)
  (decreases Seq.length mh)
  = if Seq.length mh = 0 then Seq.empty
    else
      let c = Seq.head mh in
      Seq.append (objects_in_chunk c) (major_objects (Seq.tail mh))

let major_objects_add_chunk (mh: major_heap) (c: heap_chunk)
  : Lemma (major_objects (add_chunk mh c) == Seq.append (objects_in_chunk c) (major_objects mh))
  = assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh)

let major_objects_add_chunk_fresh (mh: major_heap) (c: heap_chunk) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects_in_chunk c))
          (ensures Seq.mem x (major_objects (add_chunk mh c)))
  = major_objects_add_chunk mh c;
    SeqProps.lemma_mem_append (objects_in_chunk c) (major_objects mh)

let major_objects_add_chunk_old (mh: major_heap) (c: heap_chunk) (x: obj_addr)
  : Lemma (requires Seq.mem x (major_objects mh))
          (ensures Seq.mem x (major_objects (add_chunk mh c)))
  = major_objects_add_chunk mh c;
    SeqProps.lemma_mem_append (objects_in_chunk c) (major_objects mh)

let rec major_objects_disjoint_from_chunk (mh: major_heap) (c: heap_chunk) (x: obj_addr)
  : Lemma (requires chunk_disjoint_from_all c mh /\ Seq.mem x (major_objects mh))
          (ensures ~(obj_addr_in_chunk c x))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then assert False
    else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      assert (major_objects mh == Seq.append (objects_in_chunk hd) (major_objects tl));
      SeqProps.lemma_mem_append (objects_in_chunk hd) (major_objects tl);
      if Seq.mem x (objects_in_chunk hd) then begin
        objects_in_chunk_member_in_chunk hd x;
        assert (chunk_contains_addr hd x);
        chunks_disjoint_symmetric c hd;
        chunks_disjoint_no_shared_addr hd c x;
        if obj_addr_in_chunk c x then begin
          assert (chunk_contains_addr c x);
          assert False
        end
      end else begin
        assert (Seq.mem x (major_objects tl));
        chunk_disjoint_from_all_tail c mh;
        major_objects_disjoint_from_chunk tl c x
      end
    end

let fresh_chunk_object_not_old (mh: major_heap) (c: heap_chunk) (x: obj_addr)
  : Lemma (requires chunk_disjoint_from_all c mh /\ Seq.mem x (objects_in_chunk c))
          (ensures ~(Seq.mem x (major_objects mh)))
  = objects_in_chunk_member_in_chunk c x;
    if Seq.mem x (major_objects mh) then begin
      major_objects_disjoint_from_chunk mh c x;
      assert False
    end

let rec lookup_chunk_contains (mh: major_heap) (addr: hp_addr) (c: heap_chunk)
  : Lemma (requires lookup_chunk mh addr == Some c)
          (ensures chunk_contains_addr c addr)
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else
      let hd = Seq.head mh in
      if chunk_contains_addr hd addr then
        assert (hd == c)
      else
        lookup_chunk_contains (Seq.tail mh) addr c
