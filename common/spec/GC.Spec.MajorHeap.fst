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
module Fields = GC.Spec.Fields

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

let pointer_in_chunk (c: heap_chunk) (v: U64.t) : Tot bool =
  U64.v v >= chunk_start c + U64.v mword &&
  U64.v v < chunk_end c &&
  U64.v v % U64.v mword = 0

let object_payload_end (obj: obj_addr) (wz: nat) : nat =
  U64.v obj + wz * U64.v mword

let object_fits_in_chunk (c: heap_chunk) (obj: obj_addr) (wz: nat) : Tot bool =
  obj_addr_in_chunk c obj && object_payload_end obj wz <= chunk_end c

let obj_addr_in_chunk_header_word (c: heap_chunk) (obj: obj_addr{obj_addr_in_chunk c obj})
  : Lemma (word_in_chunk c (hd_address obj))
  = hd_address_spec obj

let obj_addr_in_chunk_is_pointer (c: heap_chunk) (obj: obj_addr)
  : Lemma (requires obj_addr_in_chunk c obj)
          (ensures pointer_in_chunk c obj)
  = ()

let chunk_offset (c: heap_chunk) (addr: U64.t{chunk_contains_addr c addr}) : nat =
  U64.v addr - chunk_start c

let chunks_disjoint (c1 c2: heap_chunk) : Tot prop =
  chunk_end c1 <= chunk_start c2 \/ chunk_end c2 <= chunk_start c1

let chunks_disjoint_symmetric (c1 c2: heap_chunk)
  : Lemma (requires chunks_disjoint c1 c2)
          (ensures chunks_disjoint c2 c1)
  = ()

let chunks_disjoint_same_range_left (c c' other: heap_chunk)
  : Lemma (requires chunk_start c' == chunk_start c /\
                    chunk_end c' == chunk_end c /\
                    chunks_disjoint c other)
          (ensures chunks_disjoint c' other)
  = ()

let chunks_disjoint_same_range_right (other c c': heap_chunk)
  : Lemma (requires chunk_start c' == chunk_start c /\
                    chunk_end c' == chunk_end c /\
                    chunks_disjoint other c)
          (ensures chunks_disjoint other c')
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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunks_pairwise_disjoint_index
  (mh: major_heap) (i j: nat)
  : Lemma
      (requires
        chunks_pairwise_disjoint mh /\
        i < Seq.length mh /\
        j < Seq.length mh /\
        i <> j)
      (ensures chunks_disjoint (Seq.index mh i) (Seq.index mh j))
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let hd = Seq.head mh in
    let tl = Seq.tail mh in
    assert (Seq.index mh 0 == hd);
    assert (forall k. k < Seq.length tl ==> chunks_disjoint hd (Seq.index tl k));
    assert (chunks_pairwise_disjoint tl);
    if i = 0 then begin
      if j = 0 then
        assert False
      else begin
        let jm1 : k:nat{k < Seq.length tl} = j - 1 in
        assert (Seq.index mh j == Seq.index tl jm1);
        assert (chunks_disjoint hd (Seq.index tl jm1))
      end
    end else if j = 0 then begin
      let im1 : k:nat{k < Seq.length tl} = i - 1 in
      assert (Seq.index mh i == Seq.index tl im1);
      assert (chunks_disjoint hd (Seq.index tl im1));
      chunks_disjoint_symmetric hd (Seq.index tl im1)
    end else begin
      let im1 : k:nat{k < Seq.length tl} = i - 1 in
      let jm1 : k:nat{k < Seq.length tl} = j - 1 in
      assert (Seq.index mh i == Seq.index tl im1);
      assert (Seq.index mh j == Seq.index tl jm1);
      assert (im1 <> jm1);
      chunks_pairwise_disjoint_index tl im1 jm1
    end
  end
#pop-options

let chunks_disjoint_words_disjoint
  (c1 c2: heap_chunk) (a b: hp_addr)
  : Lemma
      (requires
        chunks_disjoint c1 c2 /\
        word_in_chunk c1 a /\
        word_in_chunk c2 b)
      (ensures U64.v a + U64.v mword <= U64.v b \/
               U64.v b + U64.v mword <= U64.v a)
  =
  if chunk_end c1 <= chunk_start c2 then begin
    assert (U64.v a + U64.v mword <= chunk_end c1);
    assert (chunk_start c2 <= U64.v b)
  end else begin
    assert (chunk_end c2 <= chunk_start c1);
    assert (U64.v b + U64.v mword <= chunk_end c2);
    assert (chunk_start c1 <= U64.v a)
  end

let single_chunk_major_heap_wf (g: heap)
  : Lemma (well_formed_major_heap (single_chunk_major_heap g))
  = assert (Seq.head (single_chunk_major_heap g) == single_chunk_of_heap g);
    assert (Seq.length (Seq.tail (single_chunk_major_heap g)) == 0);
    Seq.lemma_empty (Seq.tail (single_chunk_major_heap g))

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

let rec lookup_chunk_index (mh: major_heap) (addr: hp_addr) : Tot (option nat)
  (decreases Seq.length mh)
  = if Seq.length mh = 0 then None
    else
      let c = Seq.head mh in
      if chunk_contains_addr c addr then Some 0
      else
        match lookup_chunk_index (Seq.tail mh) addr with
        | None -> None
        | Some i -> Some (i + 1)

#push-options "--split_queries always"
let rec lookup_chunk_index_some (mh: major_heap) (addr: hp_addr) (i: nat)
  : Lemma (requires lookup_chunk_index mh addr == Some i)
          (ensures i < Seq.length mh /\
                   chunk_contains_addr (Seq.index mh i) addr /\
                   (forall k. k < i ==> ~(chunk_contains_addr (Seq.index mh k) addr)) /\
                   lookup_chunk mh addr == Some (Seq.index mh i))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      if chunk_contains_addr hd addr then begin
        assert (lookup_chunk_index mh addr == Some 0);
        assert (i == 0);
        assert (Seq.index mh 0 == hd);
        assert (lookup_chunk mh addr == Some hd)
      end else begin
        match lookup_chunk_index tl addr with
        | None -> assert False
        | Some j ->
          assert (i == j + 1);
          lookup_chunk_index_some tl addr j;
          assert (j < Seq.length tl);
          assert (Seq.index mh i == Seq.index tl j);
          assert (chunk_contains_addr (Seq.index mh i) addr);
          let no_prior (k: nat{k < i})
            : Lemma (~(chunk_contains_addr (Seq.index mh k) addr))
            = if k = 0 then
                assert (Seq.index mh k == hd)
              else begin
                let km1 : n:nat{n < j} = k - 1 in
                assert (Seq.index mh k == Seq.index tl km1);
                assert (~(chunk_contains_addr (Seq.index tl km1) addr))
              end
          in
          FStar.Classical.forall_intro no_prior;
          assert (forall k. k < i ==> ~(chunk_contains_addr (Seq.index mh k) addr));
          assert (lookup_chunk mh addr == lookup_chunk tl addr);
          assert (lookup_chunk tl addr == Some (Seq.index tl j))
      end
    end

let rec lookup_chunk_index_word_in_chunk (mh: major_heap) (addr: hp_addr) (i: nat)
  : Lemma
      (requires well_formed_major_heap mh /\
                i < Seq.length mh /\
                word_in_chunk (Seq.index mh i) addr)
      (ensures lookup_chunk_index mh addr == Some i)
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let hd = Seq.head mh in
    let tl = Seq.tail mh in
    assert (Seq.index mh 0 == hd);
    if i = 0 then begin
      assert (Seq.index mh i == hd);
      assert (chunk_contains_addr hd addr)
    end else begin
      assert (i > 0);
      assert (i >= 1);
      assert (i - 1 >= 0);
      assert (i - 1 < Seq.length tl);
      let im1 : n:nat{n < Seq.length tl} = i - 1 in
      assert (Seq.index mh i == Seq.index tl im1);
      assert (word_in_chunk (Seq.index tl im1) addr);
      assert (chunk_contains_addr (Seq.index tl im1) addr);
      assert (chunks_disjoint hd (Seq.index tl im1));
      if chunk_contains_addr hd addr then begin
        chunks_disjoint_no_shared_addr hd (Seq.index tl im1) addr;
        assert False
      end;
      assert (well_formed_major_heap tl);
      lookup_chunk_index_word_in_chunk tl addr im1;
      assert (lookup_chunk_index tl addr == Some im1);
      assert (lookup_chunk_index mh addr == Some (im1 + 1));
      assert (im1 + 1 == i)
    end
  end

let rec lookup_chunk_index_none (mh: major_heap) (addr: hp_addr)
  : Lemma (requires lookup_chunk_index mh addr == None)
          (ensures lookup_chunk mh addr == None /\
                   (forall k. k < Seq.length mh ==> ~(chunk_contains_addr (Seq.index mh k) addr)))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then ()
    else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      if chunk_contains_addr hd addr then
        assert False
      else begin
        lookup_chunk_index_none tl addr;
        assert (lookup_chunk mh addr == lookup_chunk tl addr);
        let no_member (k: nat{k < Seq.length mh})
          : Lemma (~(chunk_contains_addr (Seq.index mh k) addr))
          = if k = 0 then
              assert (Seq.index mh k == hd)
            else begin
              let km1 : n:nat{n < Seq.length tl} = k - 1 in
              assert (Seq.index mh k == Seq.index tl km1);
              assert (~(chunk_contains_addr (Seq.index tl km1) addr))
            end
        in
        FStar.Classical.forall_intro no_member;
        assert (forall k. k < Seq.length mh ==> ~(chunk_contains_addr (Seq.index mh k) addr))
      end
    end
#pop-options

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

let lookup_chunk_index_add_chunk_miss (mh: major_heap) (c: heap_chunk)
                                      (addr: hp_addr) (i: nat)
  : Lemma (requires ~(chunk_contains_addr c addr) /\
                    lookup_chunk_index mh addr == Some i)
          (ensures lookup_chunk_index (add_chunk mh c) addr == Some (i + 1) /\
                   i + 1 < Seq.length (add_chunk mh c) /\
                   Seq.index (add_chunk mh c) (i + 1) == Seq.index mh i /\
                   chunk_end (Seq.index (add_chunk mh c) (i + 1)) ==
                   chunk_end (Seq.index mh i))
  = lookup_chunk_index_some mh addr i;
    assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh);
    Seq.lemma_eq_elim (Seq.tail (add_chunk mh c)) mh;
    assert (lookup_chunk_index (Seq.tail (add_chunk mh c)) addr == Some i);
    assert (lookup_chunk_index (add_chunk mh c) addr == Some (i + 1))

let rec is_major_pointer (mh: major_heap) (v: U64.t) : Tot bool
  (decreases Seq.length mh)
  = if Seq.length mh = 0 then false
    else pointer_in_chunk (Seq.head mh) v || is_major_pointer (Seq.tail mh) v

let major_pointer_add_chunk_hit (mh: major_heap) (c: heap_chunk) (v: U64.t)
  : Lemma (requires pointer_in_chunk c v)
          (ensures is_major_pointer (add_chunk mh c) v)
  = assert (Seq.head (add_chunk mh c) == c)

let major_pointer_add_chunk_old (mh: major_heap) (c: heap_chunk) (v: U64.t)
  : Lemma (requires is_major_pointer mh v)
          (ensures is_major_pointer (add_chunk mh c) v)
  = assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh)

let major_pointer_add_chunk_miss (mh: major_heap) (c: heap_chunk) (v: U64.t)
  : Lemma (requires ~(pointer_in_chunk c v))
          (ensures is_major_pointer (add_chunk mh c) v == is_major_pointer mh v)
  = assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh);
    if pointer_in_chunk c v then assert False else ()

let single_chunk_major_pointer_compat (g: heap) (v: U64.t)
  : Lemma (is_major_pointer (single_chunk_major_heap g) v == Fields.is_pointer v)
  = assert (Seq.head (single_chunk_major_heap g) == single_chunk_of_heap g);
    assert (chunk_start (single_chunk_of_heap g) == U64.v zero_addr);
    assert (chunk_end (single_chunk_of_heap g) == heap_size);
    assert (Seq.length (Seq.tail (single_chunk_major_heap g)) == 0);
    Seq.lemma_empty (Seq.tail (single_chunk_major_heap g))

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

let rec lookup_chunk_some_disjoint_miss (mh: major_heap) (c fresh: heap_chunk)
                                        (addr: hp_addr)
  : Lemma (requires chunk_disjoint_from_all fresh mh /\
                    lookup_chunk mh addr == Some c)
          (ensures ~(chunk_contains_addr fresh addr))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else
      let hd = Seq.head mh in
      if chunk_contains_addr hd addr then begin
        assert (lookup_chunk mh addr == Some hd);
        assert (hd == c);
        chunks_disjoint_symmetric fresh hd;
        chunks_disjoint_no_shared_addr hd fresh addr
      end else begin
        chunk_disjoint_from_all_tail fresh mh;
        lookup_chunk_some_disjoint_miss (Seq.tail mh) c fresh addr
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

let write_word_in_chunk_preserves_range (c: heap_chunk)
                                        (addr: hp_addr{word_in_chunk c addr})
                                        (value: U64.t)
  : Lemma (chunk_start (write_word_in_chunk c addr value) == chunk_start c /\
           chunk_end (write_word_in_chunk c addr value) == chunk_end c)
  = ()

let write_word_in_chunk_preserves_word (c: heap_chunk)
                                       (addr: hp_addr{word_in_chunk c addr})
                                       (value: U64.t)
                                       (other: hp_addr)
  : Lemma (requires word_in_chunk c other)
          (ensures word_in_chunk (write_word_in_chunk c addr value) other)
  = write_word_in_chunk_preserves_range c addr value

#push-options "--z3rlimit 50"
let read_write_in_chunk_same (c: heap_chunk)
                             (addr: hp_addr{word_in_chunk c addr})
                             (value: U64.t)
  : Lemma (read_word_in_chunk (write_word_in_chunk c addr value) addr == value)
  = let c' = write_word_in_chunk c addr value in
    let off = chunk_offset c addr in
    assert (chunk_offset c' addr == off);
    assert (Seq.index c'.bytes off == uint64_to_uint8 value);
    assert (Seq.index c'.bytes (off + 1) == uint64_to_uint8 (U64.shift_right value 8ul));
    assert (Seq.index c'.bytes (off + 2) == uint64_to_uint8 (U64.shift_right value 16ul));
    assert (Seq.index c'.bytes (off + 3) == uint64_to_uint8 (U64.shift_right value 24ul));
    assert (Seq.index c'.bytes (off + 4) == uint64_to_uint8 (U64.shift_right value 32ul));
    assert (Seq.index c'.bytes (off + 5) == uint64_to_uint8 (U64.shift_right value 40ul));
    assert (Seq.index c'.bytes (off + 6) == uint64_to_uint8 (U64.shift_right value 48ul));
    assert (Seq.index c'.bytes (off + 7) == uint64_to_uint8 (U64.shift_right value 56ul));
    combine_decompose_identity value
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let read_write_in_chunk_different (c: heap_chunk)
                                  (addr1: hp_addr{word_in_chunk c addr1})
                                  (addr2: hp_addr{word_in_chunk c addr2})
                                  (value: U64.t)
  : Lemma (requires addr1 <> addr2 /\
                    (U64.v addr1 + U64.v mword <= U64.v addr2 \/
                     U64.v addr2 + U64.v mword <= U64.v addr1))
          (ensures read_word_in_chunk (write_word_in_chunk c addr1 value) addr2 ==
                   read_word_in_chunk c addr2)
  = ()
#pop-options

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

let read_word_add_chunk_disjoint_old (mh: major_heap) (fresh: heap_chunk)
                                     (addr: hp_addr) (v: U64.t)
  : Lemma (requires chunk_disjoint_from_all fresh mh /\
                    read_word_in_major mh addr == Some v)
          (ensures read_word_in_major (add_chunk mh fresh) addr == Some v)
  = match lookup_chunk mh addr with
    | None -> assert False
    | Some c ->
      lookup_chunk_some_disjoint_miss mh c fresh addr;
      read_word_add_chunk_miss mh fresh addr

#push-options "--split_queries always"
let rec read_word_in_major_at_index (mh: major_heap) (addr: hp_addr) (i: nat)
  : Lemma (requires i < Seq.length mh /\
                    word_in_chunk (Seq.index mh i) addr /\
                    (forall k. k < i ==> ~(chunk_contains_addr (Seq.index mh k) addr)))
          (ensures read_word_in_major mh addr ==
                   Some (read_word_in_chunk (Seq.index mh i) addr))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else if i = 0 then begin
      assert (Seq.index mh 0 == Seq.head mh);
      assert (chunk_contains_addr (Seq.head mh) addr);
      assert (lookup_chunk mh addr == Some (Seq.head mh))
    end else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      assert (0 < i);
      assert (Seq.index mh 0 == hd);
      assert (~(chunk_contains_addr hd addr));
      assert (lookup_chunk mh addr == lookup_chunk tl addr);
      let im1 : j:nat{j < Seq.length tl} = i - 1 in
      assert (Seq.index tl im1 == Seq.index mh i);
      assert (forall k. k < im1 ==> ~(chunk_contains_addr (Seq.index tl k) addr));
      read_word_in_major_at_index tl addr im1;
      assert (read_word_in_major mh addr == read_word_in_major tl addr)
    end
#pop-options

let read_word_in_major_at_lookup_index (mh: major_heap) (addr: hp_addr)
                                      (i: nat{i < Seq.length mh})
  : Lemma (requires lookup_chunk_index mh addr == Some i /\
                    word_in_chunk (Seq.index mh i) addr)
          (ensures read_word_in_major mh addr ==
                   Some (read_word_in_chunk (Seq.index mh i) addr))
  = lookup_chunk_index_some mh addr i;
    read_word_in_major_at_index mh addr i

let lookup_chunk_index_value (mh: major_heap) (addr: hp_addr) : nat =
  match lookup_chunk_index mh addr with
  | Some i -> i
  | None -> 0

let read_word_in_major_lookup_index (mh: major_heap) (addr: hp_addr) (v: U64.t)
  : Lemma (requires read_word_in_major mh addr == Some v)
          (ensures (let i = lookup_chunk_index_value mh addr in
                    lookup_chunk_index mh addr == Some i /\
                    i < Seq.length mh /\
                    word_in_chunk (Seq.index mh i) addr /\
                    read_word_in_chunk (Seq.index mh i) addr == v))
  = match lookup_chunk_index mh addr with
    | None ->
      lookup_chunk_index_none mh addr;
      assert (lookup_chunk mh addr == None);
      assert False
    | Some i ->
      lookup_chunk_index_some mh addr i;
      assert (lookup_chunk mh addr == Some (Seq.index mh i));
      assert (read_word_in_major mh addr ==
              (if word_in_chunk (Seq.index mh i) addr then
                 Some (read_word_in_chunk (Seq.index mh i) addr)
               else None));
      if word_in_chunk (Seq.index mh i) addr then
        assert (read_word_in_chunk (Seq.index mh i) addr == v)
      else
        assert False

let write_word_add_chunk_hit (mh: major_heap) (c: heap_chunk)
                             (addr: hp_addr{word_in_chunk c addr}) (value: U64.t)
  : Lemma (write_word_in_major (add_chunk mh c) addr value ==
           Some (add_chunk mh (write_word_in_chunk c addr value)))
  = assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh);
    Seq.lemma_eq_elim (Seq.tail (add_chunk mh c)) mh

let write_word_add_chunk_miss (mh: major_heap) (c: heap_chunk)
                              (addr: hp_addr{~(word_in_chunk c addr)}) (value: U64.t)
  : Lemma (write_word_in_major (add_chunk mh c) addr value ==
           (match write_word_in_major mh addr value with
            | None -> None
            | Some mh' -> Some (add_chunk mh' c)))
  = assert (Seq.head (add_chunk mh c) == c);
    assert (Seq.equal (Seq.tail (add_chunk mh c)) mh);
    Seq.lemma_eq_elim (Seq.tail (add_chunk mh c)) mh;
    if word_in_chunk c addr then assert False else ()

let read_word_disjoint_none (mh: major_heap) (c: heap_chunk)
                            (addr: hp_addr{word_in_chunk c addr})
  : Lemma (requires chunk_disjoint_from_all c mh)
          (ensures read_word_in_major mh addr == None)
  = assert (chunk_contains_addr c addr);
    lookup_chunk_disjoint_none mh c addr

#push-options "--z3rlimit 10 --split_queries always"
let single_chunk_byte_index_compat (g: heap)
                                   (addr: hp_addr{U64.v addr >= U64.v zero_addr /\
                                                  U64.v addr + U64.v mword <= heap_size})
                                   (k: nat{k < U64.v mword})
  : Lemma (Seq.index (single_chunk_of_heap g).bytes
             (chunk_offset (single_chunk_of_heap g) addr + k) ==
           Seq.index g (U64.v addr + k))
  =
  let c = single_chunk_of_heap g in
  assert (word_in_chunk c addr);
  let off = chunk_offset c addr in
  assert (off + U64.v zero_addr == U64.v addr);
  assert (off + k < Seq.length c.bytes);
  assert (U64.v addr + k < heap_size);
  assert (Seq.index c.bytes (off + k) ==
          Seq.index (Seq.slice g (U64.v zero_addr) heap_size) (off + k));
  assert (Seq.index (Seq.slice g (U64.v zero_addr) heap_size) (off + k) ==
          Seq.index g (U64.v zero_addr + (off + k)));
  assert (U64.v zero_addr + (off + k) == U64.v addr + k)

let single_chunk_read_word_in_chunk_compat (g: heap)
                                           (addr: hp_addr{U64.v addr >= U64.v zero_addr /\
                                                          U64.v addr + U64.v mword <= heap_size})
  : Lemma (read_word_in_chunk (single_chunk_of_heap g) addr == read_word g addr)
  = let c = single_chunk_of_heap g in
    assert (word_in_chunk c addr);
    let off = chunk_offset c addr in
    assert (off + U64.v zero_addr == U64.v addr);
    read_word_spec g addr;
    single_chunk_byte_index_compat g addr 0;
    single_chunk_byte_index_compat g addr 1;
    single_chunk_byte_index_compat g addr 2;
    single_chunk_byte_index_compat g addr 3;
    single_chunk_byte_index_compat g addr 4;
    single_chunk_byte_index_compat g addr 5;
    single_chunk_byte_index_compat g addr 6;
    single_chunk_byte_index_compat g addr 7;
    assert (Seq.index c.bytes off == Seq.index g (U64.v addr));
    assert (Seq.index c.bytes (off + 1) == Seq.index g (U64.v addr + 1));
    assert (Seq.index c.bytes (off + 2) == Seq.index g (U64.v addr + 2));
    assert (Seq.index c.bytes (off + 3) == Seq.index g (U64.v addr + 3));
    assert (Seq.index c.bytes (off + 4) == Seq.index g (U64.v addr + 4));
    assert (Seq.index c.bytes (off + 5) == Seq.index g (U64.v addr + 5));
    assert (Seq.index c.bytes (off + 6) == Seq.index g (U64.v addr + 6));
    assert (Seq.index c.bytes (off + 7) == Seq.index g (U64.v addr + 7))
#pop-options

let single_chunk_read_word_compat (g: heap)
                                  (addr: hp_addr{U64.v addr >= U64.v zero_addr /\
                                                 U64.v addr + U64.v mword <= heap_size})
  : Lemma (read_word_in_major (single_chunk_major_heap g) addr == Some (read_word g addr))
  = let c = single_chunk_of_heap g in
    assert (word_in_chunk c addr);
    assert (chunk_contains_addr c addr);
    lookup_add_chunk_hit Seq.empty c addr;
    single_chunk_read_word_in_chunk_compat g addr

#push-options "--split_queries always --z3rlimit 10"
let single_chunk_write_word_in_chunk_compat (g: heap)
                                            (addr: hp_addr{U64.v addr >= U64.v zero_addr /\
                                                           U64.v addr + U64.v mword <= heap_size})
                                            (value: U64.t)
  : Lemma (write_word_in_chunk (single_chunk_of_heap g) addr value ==
           single_chunk_of_heap (write_word g addr value))
  = let c = single_chunk_of_heap g in
    assert (word_in_chunk c addr);
    let c' = write_word_in_chunk c addr value in
    let g' = write_word g addr value in
  write_word_spec g addr value;
  let off = chunk_offset c addr in
    assert (off + U64.v zero_addr == U64.v addr);
    assert (c'.base == (single_chunk_of_heap g').base);
    assert (c'.size == (single_chunk_of_heap g').size);
    assert (Seq.length c'.bytes == Seq.length (single_chunk_of_heap g').bytes);
    let prove_i (i: nat{i < Seq.length c'.bytes})
      : Lemma (Seq.index c'.bytes i == Seq.index (single_chunk_of_heap g').bytes i)
      = let a = U64.v addr in
        Seq.lemma_index_slice g' (U64.v zero_addr) heap_size i;
        assert (i + U64.v zero_addr == U64.v zero_addr + i);
        assert (Seq.index (single_chunk_of_heap g').bytes i == Seq.index g' (i + U64.v zero_addr));
        assert (Seq.index (single_chunk_of_heap g').bytes i == Seq.index g' (U64.v zero_addr + i));
        assert (U64.v zero_addr + off == a);
        if i = off then begin
          assert (U64.v zero_addr + i == U64.v zero_addr + off);
          assert (a + 0 == a);
          assert (U64.v zero_addr + i == a);
          assert (Seq.index c'.bytes i == uint64_to_uint8 value);
          assert (Seq.index g' a == uint64_to_uint8 value)
        end else if i = off + 1 then begin
          assert (U64.v zero_addr + i == U64.v zero_addr + (off + 1));
          assert (U64.v zero_addr + (off + 1) == (U64.v zero_addr + off) + 1);
          assert (U64.v zero_addr + i == a + 1);
          assert (Seq.index c'.bytes i == uint64_to_uint8 (U64.shift_right value 8ul));
          assert (Seq.index g' (a + 1) == uint64_to_uint8 (U64.shift_right value 8ul))
        end else if i = off + 2 then begin
          assert (U64.v zero_addr + i == U64.v zero_addr + (off + 2));
          assert (U64.v zero_addr + (off + 2) == (U64.v zero_addr + off) + 2);
          assert (U64.v zero_addr + i == a + 2);
          assert (Seq.index c'.bytes i == uint64_to_uint8 (U64.shift_right value 16ul));
          assert (Seq.index g' (a + 2) == uint64_to_uint8 (U64.shift_right value 16ul))
        end else if i = off + 3 then begin
          assert (U64.v zero_addr + i == U64.v zero_addr + (off + 3));
          assert (U64.v zero_addr + (off + 3) == (U64.v zero_addr + off) + 3);
          assert (U64.v zero_addr + i == a + 3);
          assert (Seq.index c'.bytes i == uint64_to_uint8 (U64.shift_right value 24ul));
          assert (Seq.index g' (a + 3) == uint64_to_uint8 (U64.shift_right value 24ul))
        end else if i = off + 4 then begin
          assert (U64.v zero_addr + i == U64.v zero_addr + (off + 4));
          assert (U64.v zero_addr + (off + 4) == (U64.v zero_addr + off) + 4);
          assert (U64.v zero_addr + i == a + 4);
          assert (Seq.index c'.bytes i == uint64_to_uint8 (U64.shift_right value 32ul));
          assert (Seq.index g' (a + 4) == uint64_to_uint8 (U64.shift_right value 32ul))
        end else if i = off + 5 then begin
          assert (U64.v zero_addr + i == U64.v zero_addr + (off + 5));
          assert (U64.v zero_addr + (off + 5) == (U64.v zero_addr + off) + 5);
          assert (U64.v zero_addr + i == a + 5);
          assert (Seq.index c'.bytes i == uint64_to_uint8 (U64.shift_right value 40ul));
          assert (Seq.index g' (a + 5) == uint64_to_uint8 (U64.shift_right value 40ul))
        end else if i = off + 6 then begin
          assert (U64.v zero_addr + i == U64.v zero_addr + (off + 6));
          assert (U64.v zero_addr + (off + 6) == (U64.v zero_addr + off) + 6);
          assert (U64.v zero_addr + i == a + 6);
          assert (Seq.index c'.bytes i == uint64_to_uint8 (U64.shift_right value 48ul));
          assert (Seq.index g' (a + 6) == uint64_to_uint8 (U64.shift_right value 48ul))
        end else if i = off + 7 then begin
          assert (U64.v zero_addr + i == U64.v zero_addr + (off + 7));
          assert (U64.v zero_addr + (off + 7) == (U64.v zero_addr + off) + 7);
          assert (U64.v zero_addr + i == a + 7);
          assert (Seq.index c'.bytes i == uint64_to_uint8 (U64.shift_right value 56ul));
          assert (Seq.index g' (a + 7) == uint64_to_uint8 (U64.shift_right value 56ul))
        end else begin
          assert (i <> off /\ i <> off + 1 /\ i <> off + 2 /\ i <> off + 3 /\
                  i <> off + 4 /\ i <> off + 5 /\ i <> off + 6 /\ i <> off + 7);
          assert (U64.v zero_addr + i <> a /\
                  U64.v zero_addr + i <> a + 1 /\
                  U64.v zero_addr + i <> a + 2 /\
                  U64.v zero_addr + i <> a + 3 /\
                  U64.v zero_addr + i <> a + 4 /\
                  U64.v zero_addr + i <> a + 5 /\
                  U64.v zero_addr + i <> a + 6 /\
                  U64.v zero_addr + i <> a + 7);
          assert (Seq.index c'.bytes i == Seq.index c.bytes i);
          assert (Seq.index g' (U64.v zero_addr + i) == Seq.index g (U64.v zero_addr + i));
          Seq.lemma_index_slice g (U64.v zero_addr) heap_size i;
          assert (Seq.index c.bytes i == Seq.index g (i + U64.v zero_addr));
          assert (Seq.index c.bytes i == Seq.index g (U64.v zero_addr + i))
        end
    in
    FStar.Classical.forall_intro prove_i;
    assert (forall i. i < Seq.length c'.bytes ==>
              Seq.index c'.bytes i == Seq.index (single_chunk_of_heap g').bytes i);
    Seq.lemma_eq_intro c'.bytes (single_chunk_of_heap g').bytes;
    Seq.lemma_eq_elim c'.bytes (single_chunk_of_heap g').bytes
#pop-options

let single_chunk_write_word_compat (g: heap)
                                   (addr: hp_addr{U64.v addr >= U64.v zero_addr /\
                                                  U64.v addr + U64.v mword <= heap_size})
                                   (value: U64.t)
  : Lemma (write_word_in_major (single_chunk_major_heap g) addr value ==
           Some (single_chunk_major_heap (write_word g addr value)))
  = let c = single_chunk_of_heap g in
    assert (word_in_chunk c addr);
    write_word_add_chunk_hit Seq.empty c addr value;
    single_chunk_write_word_in_chunk_compat g addr value

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

let append_empty_right (#a: Type) (s: seq a)
  : Lemma (Seq.append s (Seq.empty #a) == s)
  = Seq.lemma_len_append s (Seq.empty #a);
    assert (Seq.length (Seq.append s (Seq.empty #a)) == Seq.length s);
    assert (forall i. i < Seq.length s ==> Seq.index (Seq.append s (Seq.empty #a)) i == Seq.index s i);
    Seq.lemma_eq_intro (Seq.append s (Seq.empty #a)) s;
    Seq.lemma_eq_elim (Seq.append s (Seq.empty #a)) s

let seq_upd_head (#a: Type) (s: seq a{Seq.length s > 0}) (v: a)
  : Lemma (Seq.upd s 0 v == Seq.cons v (Seq.tail s))
  = Seq.cons_head_tail s;
    assert (Seq.equal s (Seq.cons (Seq.head s) (Seq.tail s)));
    Seq.lemma_eq_elim s (Seq.cons (Seq.head s) (Seq.tail s));
    assert (Seq.length (Seq.upd s 0 v) == Seq.length (Seq.cons v (Seq.tail s)));
    assert (forall k. k < Seq.length (Seq.upd s 0 v) ==>
              Seq.index (Seq.upd s 0 v) k ==
              Seq.index (Seq.cons v (Seq.tail s)) k);
    Seq.lemma_eq_intro (Seq.upd s 0 v) (Seq.cons v (Seq.tail s));
    Seq.lemma_eq_elim (Seq.upd s 0 v) (Seq.cons v (Seq.tail s))

let seq_upd_tail (#a: Type) (s: seq a{Seq.length s > 0})
                 (i: nat{0 < i /\ i < Seq.length s}) (v: a)
  : Lemma (Seq.upd s i v ==
           Seq.cons (Seq.head s) (Seq.upd (Seq.tail s) (i - 1) v))
  = Seq.cons_head_tail s;
    assert (Seq.equal s (Seq.cons (Seq.head s) (Seq.tail s)));
    Seq.lemma_eq_elim s (Seq.cons (Seq.head s) (Seq.tail s));
    assert (Seq.length (Seq.upd s i v) ==
            Seq.length (Seq.cons (Seq.head s) (Seq.upd (Seq.tail s) (i - 1) v)));
    assert (forall k. k < Seq.length (Seq.upd s i v) ==>
              Seq.index (Seq.upd s i v) k ==
              Seq.index (Seq.cons (Seq.head s) (Seq.upd (Seq.tail s) (i - 1) v)) k);
    Seq.lemma_eq_intro
      (Seq.upd s i v)
      (Seq.cons (Seq.head s) (Seq.upd (Seq.tail s) (i - 1) v));
    Seq.lemma_eq_elim
      (Seq.upd s i v)
      (Seq.cons (Seq.head s) (Seq.upd (Seq.tail s) (i - 1) v))

#push-options "--split_queries always"
let rec write_word_in_major_at_index (mh: major_heap) (addr: hp_addr)
                                     (value: U64.t) (i: nat)
  : Lemma (requires i < Seq.length mh /\
                    word_in_chunk (Seq.index mh i) addr /\
                    (forall k. k < i ==> ~(word_in_chunk (Seq.index mh k) addr)))
          (ensures write_word_in_major mh addr value ==
                   Some (Seq.upd mh i
                     (write_word_in_chunk (Seq.index mh i) addr value)))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else if i = 0 then begin
      assert (Seq.index mh 0 == Seq.head mh);
      let c' = write_word_in_chunk (Seq.head mh) addr value in
      assert (write_word_in_major mh addr value == Some (Seq.cons c' (Seq.tail mh)));
      Seq.cons_head_tail mh;
      assert (Seq.equal mh (Seq.cons (Seq.head mh) (Seq.tail mh)));
      Seq.lemma_eq_elim mh (Seq.cons (Seq.head mh) (Seq.tail mh));
      seq_upd_head mh c'
    end else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      assert (0 < i);
      assert (Seq.index mh 0 == hd);
      assert (~(word_in_chunk hd addr));
      let im1 : j:nat{j < Seq.length tl} = i - 1 in
      assert (Seq.index tl im1 == Seq.index mh i);
      assert (forall k. k < im1 ==> ~(word_in_chunk (Seq.index tl k) addr));
      write_word_in_major_at_index tl addr value im1;
      let c' = write_word_in_chunk (Seq.index mh i) addr value in
      assert (write_word_in_major tl addr value ==
              Some (Seq.upd tl im1 c'));
      assert (write_word_in_major mh addr value ==
              Some (Seq.cons hd (Seq.upd tl im1 c')));
      seq_upd_tail mh i c';
      assert (Seq.upd mh i c' == Seq.cons hd (Seq.upd tl im1 c'))
    end
#pop-options

let write_word_in_major_at_lookup_index (mh: major_heap) (addr: hp_addr)
                                        (value: U64.t) (i: nat{i < Seq.length mh})
  : Lemma (requires lookup_chunk_index mh addr == Some i /\
                    word_in_chunk (Seq.index mh i) addr)
          (ensures write_word_in_major mh addr value ==
                   Some (Seq.upd mh i
                     (write_word_in_chunk (Seq.index mh i) addr value)))
  = lookup_chunk_index_some mh addr i;
    assert (forall k. k < i ==> ~(word_in_chunk (Seq.index mh k) addr));
    write_word_in_major_at_index mh addr value i

#push-options "--split_queries always"
let rec chunks_pairwise_disjoint_upd_same_range (mh: major_heap) (i: nat)
                                                (c': heap_chunk)
  : Lemma (requires chunks_pairwise_disjoint mh /\
                    i < Seq.length mh /\
                    chunk_start c' == chunk_start (Seq.index mh i) /\
                    chunk_end c' == chunk_end (Seq.index mh i))
          (ensures chunks_pairwise_disjoint (Seq.upd mh i c'))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else if i = 0 then begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      assert (Seq.index mh 0 == hd);
      assert (forall j. j < Seq.length tl ==> chunks_disjoint hd (Seq.index tl j));
      assert (chunks_pairwise_disjoint tl);
      assert (forall j. j < Seq.length tl ==> chunks_disjoint c' (Seq.index tl j));
      seq_upd_head mh c';
      assert (Seq.upd mh 0 c' == Seq.cons c' tl)
    end else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      let im1 : j:nat{j < Seq.length tl} = i - 1 in
      assert (0 < i);
      assert (Seq.index tl im1 == Seq.index mh i);
      assert (forall j. j < Seq.length tl ==> chunks_disjoint hd (Seq.index tl j));
      assert (chunks_pairwise_disjoint tl);
      chunks_pairwise_disjoint_upd_same_range tl im1 c';
      assert (forall j. j < Seq.length (Seq.upd tl im1 c') ==>
                chunks_disjoint hd (Seq.index (Seq.upd tl im1 c') j));
      seq_upd_tail mh i c';
      assert (Seq.upd mh i c' == Seq.cons hd (Seq.upd tl im1 c'))
    end
#pop-options

let write_word_at_index_preserves_wf (mh: major_heap) (addr: hp_addr) (value: U64.t)
                                     (i: nat)
  : Lemma (requires well_formed_major_heap mh /\
                    i < Seq.length mh /\
                    word_in_chunk (Seq.index mh i) addr)
          (ensures well_formed_major_heap
                    (Seq.upd mh i (write_word_in_chunk (Seq.index mh i) addr value)))
  = write_word_in_chunk_preserves_range (Seq.index mh i) addr value;
    chunks_pairwise_disjoint_upd_same_range mh i
      (write_word_in_chunk (Seq.index mh i) addr value)

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

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20 --split_queries always"
let rec objects_in_chunk_from_write_before_preserves
  (c: heap_chunk) (start: hp_addr)
  (addr: hp_addr{word_in_chunk c addr}) (value: U64.t)
  : Lemma (requires U64.v addr + U64.v mword <= U64.v start)
          (ensures objects_in_chunk_from
                     (write_word_in_chunk c addr value) start ==
                   objects_in_chunk_from c start)
          (decreases chunk_end c - U64.v start)
  = let c' = write_word_in_chunk c addr value in
    write_word_in_chunk_preserves_range c addr value;
    if U64.v start < chunk_start c then ()
    else if U64.v start + U64.v mword >= chunk_end c then ()
    else begin
      assert (word_in_chunk c start);
      assert (word_in_chunk c' start);
      assert (addr <> start);
      read_write_in_chunk_different c addr start value;
      assert (read_word_in_chunk c' start == read_word_in_chunk c start);
      let header = read_word_in_chunk c start in
      let wz = Obj.getWosize header in
      let obj_size_words = U64.v wz + 1 in
      let next_start_nat = U64.v start + obj_size_words * U64.v mword in
      if next_start_nat > chunk_end c || next_start_nat >= pow2 64 then ()
      else if next_start_nat >= chunk_end c then begin
        assert (next_start_nat >= chunk_end c')
      end else begin
        assert (next_start_nat < heap_size);
        assert (next_start_nat < pow2 64);
        next_object_start_aligned start obj_size_words;
        assert (next_start_nat % U64.v mword == 0);
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        assert (U64.v addr + U64.v mword <= U64.v next_start);
        objects_in_chunk_from_write_before_preserves c next_start addr value;
        assert (objects_in_chunk_from c' next_start ==
                objects_in_chunk_from c next_start)
      end
    end
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20 --split_queries always"
let objects_in_chunk_from_write_header_same_wosize_preserves
  (c: heap_chunk) (start: hp_addr{word_in_chunk c start}) (value: U64.t)
  : Lemma
      (requires
        U64.v (Obj.getWosize value) ==
        U64.v (Obj.getWosize (read_word_in_chunk c start)))
      (ensures
        objects_in_chunk_from (write_word_in_chunk c start value) start ==
        objects_in_chunk_from c start)
  =
  let c' = write_word_in_chunk c start value in
  write_word_in_chunk_preserves_range c start value;
  if U64.v start < chunk_start c then
    assert False
  else if U64.v start + U64.v mword >= chunk_end c then
    ()
  else begin
    read_write_in_chunk_same c start value;
    assert (read_word_in_chunk c' start == value);
    let old_header = read_word_in_chunk c start in
    let old_wz = Obj.getWosize old_header in
    let new_wz = Obj.getWosize value in
    let old_next = U64.v start + (U64.v old_wz + 1) * U64.v mword in
    let new_next = U64.v start + (U64.v new_wz + 1) * U64.v mword in
    assert (new_next == old_next);
    if old_next > chunk_end c || old_next >= pow2 64 then begin
      assert (new_next > chunk_end c' || new_next >= pow2 64)
    end else begin
      f_address_spec start;
      if old_next >= chunk_end c then
        assert (new_next >= chunk_end c')
      else begin
        assert (old_next < heap_size);
        assert (old_next < pow2 64);
        next_object_start_aligned start (U64.v old_wz + 1);
        assert (old_next % U64.v mword == 0);
        let next_start : hp_addr = U64.uint_to_t old_next in
        assert (U64.v start + U64.v mword <= U64.v next_start);
        objects_in_chunk_from_write_before_preserves c next_start start value;
        assert (objects_in_chunk_from c' next_start ==
                objects_in_chunk_from c next_start)
      end
    end
  end

let objects_in_chunk_from_write_current_object_payload_preserves
  (c: heap_chunk) (start: hp_addr{word_in_chunk c start})
  (addr: hp_addr{word_in_chunk c addr}) (value: U64.t)
  : Lemma
      (requires
        U64.v start + U64.v mword <= U64.v addr /\
        (let header = read_word_in_chunk c start in
         let wz = Obj.getWosize header in
         let next_start =
           U64.v start + (U64.v wz + 1) * U64.v mword in
         U64.v addr + U64.v mword <= next_start /\
         next_start <= chunk_end c /\
         next_start < pow2 64))
      (ensures
        objects_in_chunk_from (write_word_in_chunk c addr value) start ==
        objects_in_chunk_from c start)
  =
  let c' = write_word_in_chunk c addr value in
  write_word_in_chunk_preserves_range c addr value;
  if U64.v start < chunk_start c then
    assert False
  else if U64.v start + U64.v mword >= chunk_end c then
    ()
  else begin
    assert (addr <> start);
    read_write_in_chunk_different c addr start value;
    assert (read_word_in_chunk c' start == read_word_in_chunk c start);
    let header = read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let next_start_nat =
      U64.v start + (U64.v wz + 1) * U64.v mword in
    assert (next_start_nat <= chunk_end c);
    assert (next_start_nat < pow2 64);
    if next_start_nat > chunk_end c || next_start_nat >= pow2 64 then
      assert False
    else begin
      f_address_spec start;
      if next_start_nat >= chunk_end c then
        assert (next_start_nat >= chunk_end c')
      else begin
        assert (next_start_nat < heap_size);
        next_object_start_aligned start (U64.v wz + 1);
        assert (next_start_nat % U64.v mword == 0);
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        assert (U64.v addr + U64.v mword <= U64.v next_start);
        objects_in_chunk_from_write_before_preserves c next_start addr value;
        assert (objects_in_chunk_from c' next_start ==
                objects_in_chunk_from c next_start)
      end
    end
  end
#pop-options

let object_wosize_in_chunk (c: heap_chunk) (x: obj_addr) : nat =
  if word_in_chunk c (hd_address x) then
    U64.v (Obj.getWosize (read_word_in_chunk c (hd_address x)))
  else 0

let object_header_size_fits_in_chunk (c: heap_chunk) (x: obj_addr) : Tot prop =
  if word_in_chunk c (hd_address x) then
    let hdr = read_word_in_chunk c (hd_address x) in
    U64.v (hd_address x) + (1 + U64.v (Obj.getWosize hdr)) * U64.v mword <=
      chunk_end c
  else False

let rec objects_in_chunk_from_member_header_fits
  (c: heap_chunk) (start: hp_addr) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects_in_chunk_from c start))
          (ensures object_header_size_fits_in_chunk c x)
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
          hd_f_roundtrip start;
          assert (hd_address x == start);
          assert (word_in_chunk c (hd_address x));
          assert (read_word_in_chunk c (hd_address x) == header);
          assert (U64.v (hd_address x) +
                  (1 + U64.v (Obj.getWosize header)) * U64.v mword ==
                  next_start_nat);
          assert (object_header_size_fits_in_chunk c x)
        end else begin
          assert (Seq.mem x tail);
          if next_start_nat >= chunk_end c then
            assert False
          else begin
            assert (obj_size_words >= 1);
            assert (next_start_nat > U64.v start);
            let next_start : hp_addr = U64.uint_to_t next_start_nat in
            objects_in_chunk_from_member_header_fits c next_start x
          end
        end
      end
    end

let objects_in_chunk_member_header_fits (c: heap_chunk) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects_in_chunk c))
          (ensures object_header_size_fits_in_chunk c x)
  = objects_in_chunk_from_member_header_fits c c.base x

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10 --split_queries always"
let rec objects_in_chunk_from_addresses_gt_start
  (c: heap_chunk) (start: hp_addr) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects_in_chunk_from c start))
          (ensures U64.v x > U64.v start)
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
        f_address_spec start;
        let obj_addr : obj_addr = f_address start in
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
        if x = obj_addr then
          assert (U64.v x > U64.v start)
        else begin
          assert (Seq.mem x tail);
          if next_start_nat >= chunk_end c then
            assert False
          else begin
            let next_start : hp_addr = U64.uint_to_t next_start_nat in
            assert (obj_size_words >= 1);
            assert (next_start_nat > U64.v start);
            objects_in_chunk_from_addresses_gt_start c next_start x
          end
        end
      end
    end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let word_aligned_gt_at_least_mword (a b: nat)
  : Lemma (requires a % U64.v mword == 0 /\
                    b % U64.v mword == 0 /\
                    a > b)
          (ensures a >= b + U64.v mword)
  = assert (U64.v mword == 8)
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20 --split_queries always"
let rec objects_in_chunk_from_write_member_header_same_wosize_preserves
  (c: heap_chunk) (start: hp_addr) (obj: obj_addr) (value: U64.t)
  : Lemma
      (requires
        Seq.mem obj (objects_in_chunk_from c start) /\
        word_in_chunk c (hd_address obj) /\
        U64.v (Obj.getWosize value) == object_wosize_in_chunk c obj)
      (ensures
        objects_in_chunk_from
          (write_word_in_chunk c (hd_address obj) value) start ==
        objects_in_chunk_from c start)
      (decreases chunk_end c - U64.v start)
  =
  objects_in_chunk_from_member_header_fits c start obj;
  assert (object_header_size_fits_in_chunk c obj);
  assert (word_in_chunk c (hd_address obj));
  if U64.v start < chunk_start c then
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
      f_address_spec start;
      let first : obj_addr = f_address start in
      if next_start_nat >= chunk_end c then begin
        Fields.mem_cons_lemma obj first (Seq.empty #obj_addr);
        assert (obj == first);
        hd_f_roundtrip start;
        assert (hd_address obj == start);
        assert (object_wosize_in_chunk c obj == U64.v wz);
        objects_in_chunk_from_write_header_same_wosize_preserves
          c start value
      end else begin
        assert (next_start_nat < heap_size);
        next_object_start_aligned start obj_size_words;
        assert (next_start_nat % U64.v mword == 0);
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        let rest = objects_in_chunk_from c next_start in
        Fields.mem_cons_lemma obj first rest;
        if obj = first then begin
          hd_f_roundtrip start;
          assert (hd_address obj == start);
          assert (object_wosize_in_chunk c obj == U64.v wz);
          objects_in_chunk_from_write_header_same_wosize_preserves
            c start value
        end else begin
          assert (Seq.mem obj rest);
          objects_in_chunk_from_member_header_fits c next_start obj;
          assert (word_in_chunk c (hd_address obj));
          objects_in_chunk_from_addresses_gt_start c next_start obj;
          assert (U64.v obj > U64.v next_start);
          assert (U64.v obj % U64.v mword == 0);
          assert (U64.v next_start % U64.v mword == 0);
          word_aligned_gt_at_least_mword (U64.v obj) (U64.v next_start);
          assert (U64.v obj >= U64.v next_start + U64.v mword);
          assert (obj_size_words >= 1);
          assert (next_start_nat >= U64.v start + U64.v mword);
          assert (U64.v next_start >= U64.v start + U64.v mword);
          hd_address_spec obj;
          assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
          assert (U64.v start + U64.v mword <= U64.v (hd_address obj));
          read_write_in_chunk_different c (hd_address obj) start value;
          assert (read_word_in_chunk
                    (write_word_in_chunk c (hd_address obj) value) start ==
                  header);
          objects_in_chunk_from_write_member_header_same_wosize_preserves
            c next_start obj value;
          assert (objects_in_chunk_from
                    (write_word_in_chunk c (hd_address obj) value)
                    next_start ==
                  objects_in_chunk_from c next_start)
        end
      end
    end
  end

let rec objects_in_chunk_from_write_member_payload_preserves
  (c: heap_chunk) (start: hp_addr) (obj: obj_addr)
  (addr: hp_addr{word_in_chunk c addr}) (value: U64.t)
  : Lemma
      (requires
        Seq.mem obj (objects_in_chunk_from c start) /\
        U64.v obj <= U64.v addr /\
        U64.v addr + U64.v mword <=
          U64.v obj + object_wosize_in_chunk c obj * U64.v mword)
      (ensures
        objects_in_chunk_from (write_word_in_chunk c addr value) start ==
        objects_in_chunk_from c start)
      (decreases chunk_end c - U64.v start)
  =
  objects_in_chunk_from_member_header_fits c start obj;
  assert (object_header_size_fits_in_chunk c obj);
  assert (word_in_chunk c (hd_address obj));
  if U64.v start < chunk_start c then
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
      f_address_spec start;
      let first : obj_addr = f_address start in
      if next_start_nat >= chunk_end c then begin
        Fields.mem_cons_lemma obj first (Seq.empty #obj_addr);
        assert (obj == first);
        hd_f_roundtrip start;
        assert (hd_address obj == start);
        assert (object_wosize_in_chunk c obj == U64.v wz);
        assert (U64.v first == U64.v start + U64.v mword);
        FStar.Math.Lemmas.distributivity_add_left
          (U64.v wz) 1 (U64.v mword);
        assert ((U64.v wz + 1) * U64.v mword ==
                U64.v wz * U64.v mword + U64.v mword);
        FStar.Math.Lemmas.paren_add_right
          (U64.v start) (U64.v mword) (U64.v wz * U64.v mword);
        assert (next_start_nat ==
                U64.v first + U64.v wz * U64.v mword);
        assert (U64.v start + U64.v mword <= U64.v addr);
        assert (U64.v addr + U64.v mword <= next_start_nat);
        objects_in_chunk_from_write_current_object_payload_preserves
          c start addr value
      end else begin
        assert (next_start_nat < heap_size);
        next_object_start_aligned start obj_size_words;
        assert (next_start_nat % U64.v mword == 0);
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        let rest = objects_in_chunk_from c next_start in
        Fields.mem_cons_lemma obj first rest;
        if obj = first then begin
          hd_f_roundtrip start;
          assert (hd_address obj == start);
          assert (object_wosize_in_chunk c obj == U64.v wz);
          assert (U64.v first == U64.v start + U64.v mword);
          FStar.Math.Lemmas.distributivity_add_left
            (U64.v wz) 1 (U64.v mword);
          assert ((U64.v wz + 1) * U64.v mword ==
                  U64.v wz * U64.v mword + U64.v mword);
          FStar.Math.Lemmas.paren_add_right
            (U64.v start) (U64.v mword) (U64.v wz * U64.v mword);
          assert (next_start_nat ==
                  U64.v first + U64.v wz * U64.v mword);
          assert (U64.v start + U64.v mword <= U64.v addr);
          assert (U64.v addr + U64.v mword <= next_start_nat);
          objects_in_chunk_from_write_current_object_payload_preserves
            c start addr value
        end else begin
          assert (Seq.mem obj rest);
          objects_in_chunk_from_addresses_gt_start c next_start obj;
          assert (U64.v obj > U64.v next_start);
          assert (obj_size_words >= 1);
          assert (next_start_nat >= U64.v start + U64.v mword);
          assert (U64.v next_start >= U64.v start + U64.v mword);
          assert (U64.v start + U64.v mword <= U64.v obj);
          assert (U64.v start + U64.v mword <= U64.v addr);
          read_write_in_chunk_different c addr start value;
          assert (read_word_in_chunk
                    (write_word_in_chunk c addr value) start == header);
          objects_in_chunk_from_write_member_payload_preserves
            c next_start obj addr value;
          assert (objects_in_chunk_from
                    (write_word_in_chunk c addr value) next_start ==
                  objects_in_chunk_from c next_start)
        end
      end
    end
  end
#pop-options

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

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10 --split_queries always"
let objects_in_chunk_from_head_mem
  (c: heap_chunk) (start: hp_addr{U64.v start + U64.v mword < heap_size})
  : Lemma (requires U64.v start >= chunk_start c /\
                    U64.v start + U64.v mword < chunk_end c /\
                    (let header = read_word_in_chunk c start in
                     let wz = Obj.getWosize header in
                     let obj_size_words = U64.v wz + 1 in
                     let next_start_nat =
                       U64.v start + obj_size_words * U64.v mword in
                     next_start_nat <= chunk_end c /\
                     next_start_nat < pow2 64))
          (ensures Seq.mem (f_address start) (objects_in_chunk_from c start))
  = let header = read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words = U64.v wz + 1 in
    let next_start_nat = U64.v start + obj_size_words * U64.v mword in
    assert (U64.v start + U64.v mword < chunk_end c);
    assert (next_start_nat <= chunk_end c);
    assert (next_start_nat < pow2 64);
    f_address_spec start;
    let first : obj_addr = f_address start in
    if next_start_nat >= chunk_end c then
      SeqProps.mem_cons first (Seq.empty #obj_addr)
    else begin
      assert (next_start_nat < heap_size);
      next_object_start_aligned start obj_size_words;
      assert (next_start_nat % U64.v mword == 0);
      let next_start : hp_addr = U64.uint_to_t next_start_nat in
      SeqProps.mem_cons first (objects_in_chunk_from c next_start)
    end
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10 --split_queries always"
let objects_in_chunk_from_tail_mem
  (c: heap_chunk) (start: hp_addr{U64.v start + U64.v mword < heap_size})
  (next_start: hp_addr) (x: obj_addr)
  : Lemma
      (requires U64.v start >= chunk_start c /\
                U64.v start + U64.v mword < chunk_end c /\
                (let header = read_word_in_chunk c start in
                 let wz = Obj.getWosize header in
                 let obj_size_words = U64.v wz + 1 in
                 let next_start_nat =
                   U64.v start + obj_size_words * U64.v mword in
                 U64.v next_start == next_start_nat /\
                 next_start_nat < chunk_end c /\
                 next_start_nat < pow2 64 /\
                 Seq.mem x (objects_in_chunk_from c next_start)))
      (ensures Seq.mem x (objects_in_chunk_from c start))
  = let header = read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words = U64.v wz + 1 in
    let next_start_nat = U64.v start + obj_size_words * U64.v mword in
    assert (next_start_nat < chunk_end c);
    assert (next_start_nat < heap_size);
    next_object_start_aligned start obj_size_words;
    assert (next_start_nat % U64.v mword == 0);
    f_address_spec start;
    let first : obj_addr = f_address start in
    Fields.mem_cons_lemma x first (objects_in_chunk_from c next_start)
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10 --split_queries always"
let rec objects_in_chunk_from_later_in_earlier
  (c: heap_chunk) (start: hp_addr)
  (later: hp_addr{U64.v later + U64.v mword < heap_size})
  (h: obj_addr)
  : Lemma (requires U64.v start <= U64.v later /\
                    Seq.mem h (objects_in_chunk_from c later) /\
                    (U64.v start == U64.v later \/
                     Seq.mem (f_address later) (objects_in_chunk_from c start)))
          (ensures Seq.mem h (objects_in_chunk_from c start))
          (decreases chunk_end c - U64.v start)
  = if U64.v start = U64.v later then
      ()
    else if U64.v start < chunk_start c then
      assert False
    else if U64.v start + U64.v mword >= chunk_end c then
      assert False
    else begin
      let header = read_word_in_chunk c start in
      let wz_start = Obj.getWosize header in
      let obj_size_words = U64.v wz_start + 1 in
      let next_start_nat = U64.v start + obj_size_words * U64.v mword in
      if next_start_nat > chunk_end c || next_start_nat >= pow2 64 then
        assert False
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        if next_start_nat >= chunk_end c then begin
          Fields.mem_cons_lemma (f_address later) first (Seq.empty #obj_addr);
          f_address_spec later;
          assert (f_address later = first);
          assert (U64.v later = U64.v start)
        end else begin
          assert (next_start_nat < heap_size);
          next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          Fields.mem_cons_lemma (f_address later) first (objects_in_chunk_from c next_start);
          if f_address later = first then begin
            f_address_spec later;
            assert (U64.v later = U64.v start)
          end else begin
            objects_in_chunk_from_addresses_gt_start c next_start (f_address later);
            f_address_spec later;
            assert (U64.v next_start % U64.v mword == 0);
            assert (U64.v later % U64.v mword == 0);
            if U64.v next_start > U64.v later then begin
              word_aligned_gt_at_least_mword (U64.v next_start) (U64.v later);
              assert (U64.v next_start >= U64.v later + U64.v mword);
              assert (U64.v (f_address later) <= U64.v next_start);
              assert False
            end;
            assert (U64.v next_start <= U64.v later);
            objects_in_chunk_from_later_in_earlier c next_start later h;
            Fields.mem_cons_lemma h first (objects_in_chunk_from c next_start)
          end
        end
      end
    end
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20 --split_queries always"
let rec objects_in_chunk_from_separated
  (c: heap_chunk) (start: hp_addr) (src y: obj_addr)
  : Lemma (requires Seq.mem src (objects_in_chunk_from c start) /\
                    Seq.mem y (objects_in_chunk_from c start) /\
                    U64.v src < U64.v y)
          (ensures U64.v y >
                     U64.v src + object_wosize_in_chunk c src * U64.v mword)
          (decreases chunk_end c - U64.v start)
  = if U64.v start < chunk_start c then ()
    else if U64.v start + U64.v mword >= chunk_end c then ()
    else begin
      let header = read_word_in_chunk c start in
      let wz = Obj.getWosize header in
      let obj_size_words = U64.v wz + 1 in
      let next_start_nat = U64.v start + obj_size_words * U64.v mword in
      if next_start_nat > chunk_end c || next_start_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        if next_start_nat >= chunk_end c then begin
          Fields.mem_cons_lemma src first Seq.empty;
          Fields.mem_cons_lemma y first Seq.empty
        end else begin
          assert (next_start_nat < heap_size);
          assert (next_start_nat < pow2 64);
          next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          let rest = objects_in_chunk_from c next_start in
          Fields.mem_cons_lemma src first rest;
          Fields.mem_cons_lemma y first rest;
          if src = first then begin
            assert (y <> first);
            assert (Seq.mem y rest);
            objects_in_chunk_from_addresses_gt_start c next_start y;
            hd_f_roundtrip start;
            assert (hd_address first == start);
            assert (word_in_chunk c (hd_address first));
            assert (read_word_in_chunk c (hd_address first) == header);
            assert (object_wosize_in_chunk c first == U64.v wz);
            assert (U64.v first == U64.v start + U64.v mword);
            FStar.Math.Lemmas.distributivity_add_left
              (U64.v wz) 1 (U64.v mword);
            assert ((U64.v wz + 1) * U64.v mword ==
                    U64.v wz * U64.v mword + U64.v mword);
            FStar.Math.Lemmas.paren_add_right
              (U64.v start) (U64.v mword) (U64.v wz * U64.v mword);
            assert (U64.v next_start ==
                    U64.v first + U64.v wz * U64.v mword)
          end else begin
            assert (src <> first);
            assert (Seq.mem src rest);
            if y = first then begin
              objects_in_chunk_from_addresses_gt_start c next_start src;
              assert (U64.v src > U64.v next_start);
              assert (U64.v first == U64.v start + U64.v mword);
              assert (obj_size_words >= 1);
              assert (next_start_nat >= U64.v start + U64.v mword);
              assert (U64.v next_start == next_start_nat);
              assert (U64.v first <= U64.v next_start);
              assert (U64.v src > U64.v first);
              assert False
            end else begin
              assert (y <> first);
              assert (Seq.mem y rest);
              objects_in_chunk_from_separated c next_start src y
            end
          end
        end
      end
    end

let objects_in_chunk_separated (c: heap_chunk) (src y: obj_addr)
  : Lemma (requires Seq.mem src (objects_in_chunk c) /\
                    Seq.mem y (objects_in_chunk c) /\
                    U64.v src < U64.v y)
          (ensures U64.v y >
                     U64.v src + object_wosize_in_chunk c src * U64.v mword)
  = objects_in_chunk_from_separated c c.base src y
#pop-options

#push-options "--split_queries always"
let rec single_chunk_objects_from_compat
  (g: heap) (start: hp_addr{U64.v start >= U64.v zero_addr})
  : Lemma (ensures objects_in_chunk_from (single_chunk_of_heap g) start == Fields.objects start g)
          (decreases heap_size - U64.v start)
  = let c = single_chunk_of_heap g in
    assert (chunk_end c == heap_size);
    if U64.v start < chunk_start c then assert False
    else if U64.v start + U64.v mword >= chunk_end c then begin
      assert (U64.v start + 8 >= Seq.length g)
    end else begin
      single_chunk_read_word_in_chunk_compat g start;
      let header = read_word_in_chunk c start in
      let wz = Obj.getWosize header in
      let obj_size_words = U64.v wz + 1 in
      let next_start_nat = U64.v start + obj_size_words * U64.v mword in
      assert (header == read_word g start);
      assert (wz == Obj.getWosize (read_word g start));
      assert_norm (U64.v mword == 8);
      assert (next_start_nat == U64.v start + obj_size_words * 8);
      if next_start_nat > chunk_end c || next_start_nat >= pow2 64 then begin
        assert (next_start_nat > Seq.length g || next_start_nat >= pow2 64)
      end else begin
        f_address_spec start;
        let obj_addr : obj_addr = f_address start in
        assert (next_start_nat <= Seq.length g);
        let next_start_raw = U64.uint_to_t next_start_nat in
        assert (U64.v next_start_raw == next_start_nat);
        if next_start_nat >= chunk_end c then begin
          assert (next_start_nat >= heap_size)
        end else begin
          assert (next_start_nat < heap_size);
          assert (next_start_nat < pow2 64);
          next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start : hp_addr = next_start_raw in
          assert (obj_size_words >= 1);
          assert (U64.v next_start > U64.v start);
          assert (U64.v next_start >= U64.v zero_addr);
          single_chunk_objects_from_compat g next_start
        end
      end
    end
#pop-options

let single_chunk_objects_compat (g: heap)
  : Lemma (objects_in_chunk (single_chunk_of_heap g) == Fields.objects zero_addr g)
  = single_chunk_objects_from_compat g zero_addr

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

let rec major_objects_member_at_index (mh: major_heap) (i: nat) (x: obj_addr)
  : Lemma (requires i < Seq.length mh /\
                    Seq.mem x (objects_in_chunk (Seq.index mh i)))
          (ensures Seq.mem x (major_objects mh))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else begin
      let c = Seq.head mh in
      let tl = Seq.tail mh in
      assert (major_objects mh == Seq.append (objects_in_chunk c) (major_objects tl));
      if i = 0 then begin
        assert (Seq.index mh i == c);
        SeqProps.lemma_mem_append (objects_in_chunk c) (major_objects tl)
      end else begin
        assert (i > 0);
        assert (i >= 1);
        assert (i - 1 >= 0);
        assert (i - 1 < Seq.length tl);
        let im1 : n:nat{n < Seq.length tl} = i - 1 in
        assert (Seq.index mh i == Seq.index tl im1);
        major_objects_member_at_index tl im1 x;
        SeqProps.lemma_mem_append (objects_in_chunk c) (major_objects tl)
      end
    end

let rec major_objects_upd_same_chunk_objects
  (mh: major_heap) (i: nat) (c': heap_chunk)
  : Lemma
      (requires i < Seq.length mh /\
                objects_in_chunk c' == objects_in_chunk (Seq.index mh i))
      (ensures major_objects (Seq.upd mh i c') == major_objects mh)
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let c = Seq.head mh in
    let tl = Seq.tail mh in
    assert (major_objects mh ==
            Seq.append (objects_in_chunk c) (major_objects tl));
    if i = 0 then begin
      assert (Seq.index mh i == c);
      seq_upd_head mh c';
      assert (Seq.upd mh i c' == Seq.cons c' tl);
      assert (major_objects (Seq.upd mh i c') ==
              Seq.append (objects_in_chunk c') (major_objects tl))
    end else begin
      assert (i > 0);
      assert (i >= 1);
      assert (i - 1 >= 0);
      assert (i - 1 < Seq.length tl);
      let im1 : n:nat{n < Seq.length tl} = i - 1 in
      assert (Seq.index mh i == Seq.index tl im1);
      major_objects_upd_same_chunk_objects tl im1 c';
      seq_upd_tail mh i c';
      assert (Seq.upd mh i c' == Seq.cons c (Seq.upd tl im1 c'));
      assert (major_objects (Seq.upd tl im1 c') == major_objects tl);
      assert (major_objects (Seq.upd mh i c') ==
              Seq.append
                (objects_in_chunk c)
                (major_objects (Seq.upd tl im1 c')))
    end
  end

let single_chunk_major_objects_compat (g: heap)
  : Lemma (major_objects (single_chunk_major_heap g) == Fields.objects zero_addr g)
  = single_chunk_objects_compat g;
    assert (Seq.head (single_chunk_major_heap g) == single_chunk_of_heap g);
    assert (Seq.length (Seq.tail (single_chunk_major_heap g)) == 0);
    Seq.lemma_empty (Seq.tail (single_chunk_major_heap g));
    assert (Seq.tail (single_chunk_major_heap g) == Seq.empty);
    assert (major_objects (Seq.tail (single_chunk_major_heap g)) == Seq.empty);
    append_empty_right (objects_in_chunk (single_chunk_of_heap g))

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

let rec major_object_header_disjoint_from_chunk
  (mh: major_heap) (c: heap_chunk) (x: obj_addr)
  : Lemma (requires chunk_disjoint_from_all c mh /\
                    Seq.mem x (major_objects mh))
          (ensures ~(chunk_contains_addr c (hd_address x)))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then assert False
    else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      assert (major_objects mh == Seq.append (objects_in_chunk hd) (major_objects tl));
      SeqProps.lemma_mem_append (objects_in_chunk hd) (major_objects tl);
      if Seq.mem x (objects_in_chunk hd) then begin
        objects_in_chunk_member_header_fits hd x;
        assert (object_header_size_fits_in_chunk hd x);
        assert (word_in_chunk hd (hd_address x));
        assert (chunk_contains_addr hd (hd_address x));
        chunks_disjoint_symmetric c hd;
        chunks_disjoint_no_shared_addr hd c (hd_address x)
      end else begin
        assert (Seq.mem x (major_objects tl));
        chunk_disjoint_from_all_tail c mh;
        major_object_header_disjoint_from_chunk tl c x
      end
    end

#push-options "--z3rlimit 10 --split_queries always"
let rec major_objects_member_in_lookup_chunk
  (mh: major_heap) (i: nat) (x: obj_addr)
  : Lemma (requires well_formed_major_heap mh /\
                    i < Seq.length mh /\
                    chunk_contains_addr (Seq.index mh i) (hd_address x) /\
                    Seq.mem x (major_objects mh))
          (ensures Seq.mem x (objects_in_chunk (Seq.index mh i)))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      assert (major_objects mh == Seq.append (objects_in_chunk hd) (major_objects tl));
      SeqProps.lemma_mem_append (objects_in_chunk hd) (major_objects tl);
      if i = 0 then begin
        assert (Seq.index mh i == hd);
        if Seq.mem x (objects_in_chunk hd) then
          ()
        else begin
          assert (Seq.mem x (major_objects tl));
          assert (chunk_disjoint_from_all hd tl);
          major_object_header_disjoint_from_chunk tl hd x;
          assert False
        end
      end else begin
        assert (i > 0);
        assert (i >= 1);
        assert (i - 1 >= 0);
        assert (i - 1 < Seq.length tl);
        let im1 : n:nat{n < Seq.length tl} = i - 1 in
        assert (Seq.index mh i == Seq.index tl im1);
        if Seq.mem x (objects_in_chunk hd) then begin
          objects_in_chunk_member_header_fits hd x;
          assert (object_header_size_fits_in_chunk hd x);
          assert (word_in_chunk hd (hd_address x));
          assert (chunk_contains_addr hd (hd_address x));
          assert (chunks_disjoint hd (Seq.index tl im1));
          chunks_disjoint_no_shared_addr hd (Seq.index tl im1) (hd_address x);
          assert False
        end else begin
          assert (Seq.mem x (major_objects tl));
          assert (well_formed_major_heap tl);
          major_objects_member_in_lookup_chunk tl im1 x
        end
      end
    end
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 1 --ifuel 1"
let rec major_objects_member_header_read_some
  (mh: major_heap) (x: obj_addr)
  : Lemma
      (requires well_formed_major_heap mh /\
                Seq.mem x (major_objects mh))
      (ensures
        (match read_word_in_major mh (hd_address x) with
         | Some _ -> True
         | None -> False))
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let c = Seq.head mh in
    let tl = Seq.tail mh in
    let xhd = hd_address x in
    assert (major_objects mh == Seq.append (objects_in_chunk c) (major_objects tl));
    SeqProps.lemma_mem_append (objects_in_chunk c) (major_objects tl);
    if Seq.mem x (objects_in_chunk c) then begin
      objects_in_chunk_member_header_fits c x;
      assert (object_header_size_fits_in_chunk c x);
      assert (word_in_chunk c xhd);
      assert (chunk_contains_addr c xhd);
      assert (read_word_in_major mh xhd == Some (read_word_in_chunk c xhd))
    end else begin
      assert (Seq.mem x (major_objects tl));
      assert (chunk_disjoint_from_all c tl);
      major_object_header_disjoint_from_chunk tl c x;
      assert (~(chunk_contains_addr c xhd));
      assert (well_formed_major_heap tl);
      assert (Seq.length mh > 0);
      let mh_len : n:nat{1 <= n /\ n <= Seq.length mh} = Seq.length mh in
      Seq.lemma_len_slice mh 1 mh_len;
      assert (Seq.length tl < Seq.length mh);
      major_objects_member_header_read_some tl x;
      assert (read_word_in_major mh xhd == read_word_in_major tl xhd)
    end
  end

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_objects_member_field0_read_some
  (mh: major_heap) (x: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        well_formed_major_heap mh /\
        Seq.mem x (major_objects mh) /\
        read_word_in_major mh (hd_address x) == Some hdr /\
        U64.v (Obj.getWosize hdr) >= 1)
      (ensures
        (match read_word_in_major mh x with
         | Some _ -> True
         | None -> False))
  =
  let xhd = hd_address x in
  read_word_in_major_lookup_index mh xhd hdr;
  let idx = lookup_chunk_index_value mh xhd in
  assert (lookup_chunk_index mh xhd == Some idx);
  assert (idx < Seq.length mh);
  assert (word_in_chunk (Seq.index mh idx) xhd);
  assert (read_word_in_chunk (Seq.index mh idx) xhd == hdr);
  major_objects_member_in_lookup_chunk mh idx x;
  assert (Seq.mem x (objects_in_chunk (Seq.index mh idx)));
  objects_in_chunk_member_header_fits (Seq.index mh idx) x;
  assert (object_header_size_fits_in_chunk (Seq.index mh idx) x);
  hd_address_spec x;
  assert (U64.v xhd + U64.v mword == U64.v x);
  assert (U64.v mword == 8);
  assert (U64.v x + U64.v mword == U64.v xhd + 2 * U64.v mword);
  FStar.Math.Lemmas.lemma_mult_le_right
    (U64.v mword) 2 (1 + U64.v (Obj.getWosize hdr));
  assert (U64.v x + U64.v mword <=
          U64.v xhd + (1 + U64.v (Obj.getWosize hdr)) * U64.v mword);
  assert (word_in_chunk (Seq.index mh idx) x);
  lookup_chunk_index_word_in_chunk mh x idx;
  read_word_in_major_at_lookup_index mh x idx
#pop-options
#pop-options

#push-options "--z3rlimit 10 --split_queries always"
let major_objects_write_member_header_same_wosize_preserves
  (mh: major_heap) (i: nat) (obj: obj_addr) (value: U64.t)
  : Lemma
      (requires
        well_formed_major_heap mh /\
        i < Seq.length mh /\
        lookup_chunk_index mh (hd_address obj) == Some i /\
        Seq.mem obj (major_objects mh) /\
        U64.v (Obj.getWosize value) ==
          object_wosize_in_chunk (Seq.index mh i) obj)
      (ensures
        (match write_word_in_major mh (hd_address obj) value with
        | Some mh' -> major_objects mh' == major_objects mh
        | None -> False))
  =
  let c = Seq.index mh i in
  lookup_chunk_index_some mh (hd_address obj) i;
  assert (chunk_contains_addr c (hd_address obj));
  major_objects_member_in_lookup_chunk mh i obj;
  assert (Seq.mem obj (objects_in_chunk c));
  objects_in_chunk_member_header_fits c obj;
  assert (object_header_size_fits_in_chunk c obj);
  assert (word_in_chunk c (hd_address obj));
  objects_in_chunk_from_write_member_header_same_wosize_preserves
    c c.base obj value;
  let c' = write_word_in_chunk c (hd_address obj) value in
  assert (objects_in_chunk c' == objects_in_chunk c);
  write_word_in_major_at_lookup_index mh (hd_address obj) value i;
  assert (write_word_in_major mh (hd_address obj) value ==
          Some (Seq.upd mh i c'));
  major_objects_upd_same_chunk_objects mh i c';
  assert (major_objects (Seq.upd mh i c') == major_objects mh)

let major_object_payload_word_in_lookup_chunk
  (mh: major_heap) (i: nat) (obj: obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_major_heap mh /\
      i < Seq.length mh /\
      lookup_chunk_index mh (hd_address obj) == Some i /\
      Seq.mem obj (major_objects mh) /\
      U64.v obj <= U64.v addr /\
      U64.v addr + U64.v mword <=
        U64.v obj + object_wosize_in_chunk (Seq.index mh i) obj * U64.v mword)
    (ensures
      word_in_chunk (Seq.index mh i) addr /\
      lookup_chunk_index mh addr == Some i)
  =
  let c = Seq.index mh i in
  lookup_chunk_index_some mh (hd_address obj) i;
  assert (chunk_contains_addr c (hd_address obj));
  major_objects_member_in_lookup_chunk mh i obj;
  assert (Seq.mem obj (objects_in_chunk c));
  objects_in_chunk_member_header_fits c obj;
  assert (object_header_size_fits_in_chunk c obj);
  hd_address_spec obj;
  assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
  assert (chunk_start c <= U64.v (hd_address obj));
  assert (chunk_start c <= U64.v obj);
  assert (chunk_start c <= U64.v addr);
  let wz = object_wosize_in_chunk c obj in
  assert (word_in_chunk c (hd_address obj));
  assert (U64.v (hd_address obj) + (1 + wz) * U64.v mword <= chunk_end c);
  assert (U64.v obj + wz * U64.v mword <= chunk_end c);
  assert (U64.v addr + U64.v mword <= chunk_end c);
  assert (word_in_chunk c addr);
  lookup_chunk_index_word_in_chunk mh addr i

let major_objects_write_member_payload_preserves
  (mh: major_heap) (i: nat) (obj: obj_addr)
  (addr: hp_addr) (value: U64.t)
  : Lemma
      (requires
        well_formed_major_heap mh /\
        i < Seq.length mh /\
        lookup_chunk_index mh (hd_address obj) == Some i /\
        lookup_chunk_index mh addr == Some i /\
        word_in_chunk (Seq.index mh i) addr /\
        Seq.mem obj (major_objects mh) /\
        U64.v obj <= U64.v addr /\
        U64.v addr + U64.v mword <=
          U64.v obj + object_wosize_in_chunk (Seq.index mh i) obj * U64.v mword)
      (ensures
        (match write_word_in_major mh addr value with
        | Some mh' -> major_objects mh' == major_objects mh
        | None -> False))
  =
  let c = Seq.index mh i in
  lookup_chunk_index_some mh (hd_address obj) i;
  assert (chunk_contains_addr c (hd_address obj));
  major_objects_member_in_lookup_chunk mh i obj;
  assert (Seq.mem obj (objects_in_chunk c));
  objects_in_chunk_from_write_member_payload_preserves
    c c.base obj addr value;
  let c' = write_word_in_chunk c addr value in
  assert (objects_in_chunk c' == objects_in_chunk c);
  write_word_in_major_at_lookup_index mh addr value i;
  assert (write_word_in_major mh addr value ==
          Some (Seq.upd mh i c'));
  major_objects_upd_same_chunk_objects mh i c';
  assert (major_objects (Seq.upd mh i c') == major_objects mh)
#pop-options

let fresh_chunk_object_not_old (mh: major_heap) (c: heap_chunk) (x: obj_addr)
  : Lemma (requires chunk_disjoint_from_all c mh /\ Seq.mem x (objects_in_chunk c))
          (ensures ~(Seq.mem x (major_objects mh)))
  = objects_in_chunk_member_in_chunk c x;
    if Seq.mem x (major_objects mh) then begin
      major_objects_disjoint_from_chunk mh c x;
      assert False
    end

let rec major_object_is_pointer (mh: major_heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (major_objects mh))
          (ensures is_major_pointer mh x)
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then assert False
    else begin
      let c = Seq.head mh in
      let tl = Seq.tail mh in
      assert (major_objects mh == Seq.append (objects_in_chunk c) (major_objects tl));
      SeqProps.lemma_mem_append (objects_in_chunk c) (major_objects tl);
      if Seq.mem x (objects_in_chunk c) then begin
        objects_in_chunk_member_in_chunk c x;
        obj_addr_in_chunk_is_pointer c x;
        major_pointer_add_chunk_hit tl c x
      end else begin
        assert (Seq.mem x (major_objects tl));
        major_object_is_pointer tl x;
        major_pointer_add_chunk_old tl c x
      end
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
