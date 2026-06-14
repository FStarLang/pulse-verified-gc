module GC.Spec.MajorHeap.ReadFrame

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap

#set-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"

let lookup_chunk_cons_miss
    (c: MH.heap_chunk)
    (tl: MH.major_heap)
    (addr: hp_addr)
  : Lemma
      (requires ~(MH.chunk_contains_addr c addr))
      (ensures
        MH.lookup_chunk (Seq.cons c tl) addr ==
        MH.lookup_chunk tl addr)
  =
  assert (Seq.length (Seq.cons c tl) > 0);
  assert (Seq.head (Seq.cons c tl) == c);
  assert (Seq.equal (Seq.tail (Seq.cons c tl)) tl);
  Seq.lemma_eq_elim (Seq.tail (Seq.cons c tl)) tl

let read_word_in_major_cons_miss
    (c: MH.heap_chunk)
    (tl: MH.major_heap)
    (addr: hp_addr)
  : Lemma
      (requires ~(MH.chunk_contains_addr c addr))
      (ensures
        MH.read_word_in_major (Seq.cons c tl) addr ==
        MH.read_word_in_major tl addr)
  =
  lookup_chunk_cons_miss c tl addr

let read_word_in_major_cons_hit
    (c: MH.heap_chunk)
    (tl: MH.major_heap)
    (addr: hp_addr)
  : Lemma
      (requires
        MH.chunk_contains_addr c addr /\
        MH.word_in_chunk c addr)
      (ensures
        MH.read_word_in_major (Seq.cons c tl) addr ==
        Some (MH.read_word_in_chunk c addr))
  =
  assert (Seq.length (Seq.cons c tl) > 0);
  assert (Seq.head (Seq.cons c tl) == c)

let rec write_word_in_major_preserves_other_read
    (mh: MH.major_heap)
    (write_addr: hp_addr)
    (value: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v write_addr + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v write_addr))
      (ensures
        (match MH.write_word_in_major mh write_addr value with
        | Some mh' -> MH.read_word_in_major mh' read_addr == Some old
        | None -> True))
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let c = Seq.head mh in
    let tl = Seq.tail mh in
    if MH.word_in_chunk c write_addr then begin
      let c' = MH.write_word_in_chunk c write_addr value in
      MH.write_word_in_chunk_preserves_range c write_addr value;
      assert (MH.write_word_in_major mh write_addr value == Some (Seq.cons c' tl));
      if MH.chunk_contains_addr c read_addr then begin
        assert (MH.lookup_chunk mh read_addr == Some c);
        assert (MH.word_in_chunk c read_addr);
        assert (MH.read_word_in_chunk c read_addr == old);
        MH.write_word_in_chunk_preserves_word c write_addr value read_addr;
        MH.read_write_in_chunk_different c write_addr read_addr value;
        assert (MH.chunk_contains_addr c' read_addr);
        read_word_in_major_cons_hit c' tl read_addr;
        assert (MH.read_word_in_major (Seq.cons c' tl) read_addr == Some old)
      end else begin
        assert (~(MH.chunk_contains_addr c' read_addr));
        assert (MH.read_word_in_major mh read_addr == MH.read_word_in_major tl read_addr);
        assert (MH.read_word_in_major tl read_addr == Some old);
        read_word_in_major_cons_miss c' tl read_addr;
        assert (MH.read_word_in_major (Seq.cons c' tl) read_addr ==
                MH.read_word_in_major tl read_addr)
      end
    end else begin
      assert (MH.write_word_in_major mh write_addr value ==
              (match MH.write_word_in_major tl write_addr value with
              | None -> None
              | Some tl' -> Some (Seq.cons c tl')));
      if MH.chunk_contains_addr c read_addr then begin
        assert (MH.lookup_chunk mh read_addr == Some c);
        assert (MH.word_in_chunk c read_addr);
        read_word_in_major_cons_hit c tl read_addr;
        assert (MH.read_word_in_chunk c read_addr == old);
        match MH.write_word_in_major tl write_addr value with
        | None -> ()
        | Some tl' ->
          read_word_in_major_cons_hit c tl' read_addr;
          assert (MH.read_word_in_major (Seq.cons c tl') read_addr == Some old)
      end else begin
        assert (MH.read_word_in_major mh read_addr == MH.read_word_in_major tl read_addr);
        assert (MH.read_word_in_major tl read_addr == Some old);
        read_word_in_major_cons_miss c tl read_addr;
        write_word_in_major_preserves_other_read
          tl write_addr value read_addr old;
        match MH.write_word_in_major tl write_addr value with
        | None -> ()
        | Some tl' ->
          assert (MH.read_word_in_major tl' read_addr == Some old);
          read_word_in_major_cons_miss c tl' read_addr;
          assert (MH.read_word_in_major (Seq.cons c tl') read_addr ==
                  MH.read_word_in_major tl' read_addr)
      end
    end
  end

let rec write_word_in_major_preserves_other_read_back
    (mh: MH.major_heap)
    (write_addr: hp_addr)
    (value: U64.t)
    (read_addr: hp_addr)
    (old: U64.t)
  : Lemma
      (requires
        (match MH.write_word_in_major mh write_addr value with
         | Some mh' -> MH.read_word_in_major mh' read_addr == Some old
         | None -> False) /\
        (U64.v write_addr + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v write_addr))
      (ensures MH.read_word_in_major mh read_addr == Some old)
      (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let c = Seq.head mh in
    let tl = Seq.tail mh in
    if MH.word_in_chunk c write_addr then begin
      let c' = MH.write_word_in_chunk c write_addr value in
      MH.write_word_in_chunk_preserves_range c write_addr value;
      assert (MH.write_word_in_major mh write_addr value == Some (Seq.cons c' tl));
      if MH.chunk_contains_addr c' read_addr then begin
        assert (MH.chunk_contains_addr c read_addr);
        assert (MH.word_in_chunk c' read_addr);
        MH.write_word_in_chunk_preserves_word c write_addr value read_addr;
        assert (MH.word_in_chunk c read_addr);
        read_word_in_major_cons_hit c' tl read_addr;
        assert (MH.read_word_in_chunk c' read_addr == old);
        MH.read_write_in_chunk_different c write_addr read_addr value;
        assert (MH.read_word_in_chunk c read_addr == old);
        read_word_in_major_cons_hit c tl read_addr
      end else begin
        assert (~(MH.chunk_contains_addr c read_addr));
        read_word_in_major_cons_miss c' tl read_addr;
        assert (MH.read_word_in_major (Seq.cons c' tl) read_addr ==
                MH.read_word_in_major tl read_addr);
        assert (MH.read_word_in_major tl read_addr == Some old);
        read_word_in_major_cons_miss c tl read_addr
      end
    end else begin
      assert (MH.write_word_in_major mh write_addr value ==
              (match MH.write_word_in_major tl write_addr value with
               | None -> None
               | Some tl' -> Some (Seq.cons c tl')));
      if MH.chunk_contains_addr c read_addr then begin
        match MH.write_word_in_major tl write_addr value with
        | None -> assert False
        | Some tl' ->
          read_word_in_major_cons_hit c tl' read_addr;
          assert (MH.read_word_in_major (Seq.cons c tl') read_addr == Some old);
          assert (MH.word_in_chunk c read_addr);
          assert (MH.read_word_in_chunk c read_addr == old);
          read_word_in_major_cons_hit c tl read_addr
      end else begin
        read_word_in_major_cons_miss c tl read_addr;
        match MH.write_word_in_major tl write_addr value with
        | None -> assert False
        | Some tl' ->
          read_word_in_major_cons_miss c tl' read_addr;
          assert (MH.read_word_in_major tl' read_addr == Some old);
          write_word_in_major_preserves_other_read_back
            tl write_addr value read_addr old;
          assert (MH.read_word_in_major tl read_addr == Some old)
      end
    end
  end

let rec write_word_in_major_preserves_same_read
      (mh: MH.major_heap)
      (addr: hp_addr)
      (old: U64.t)
      (value: U64.t)
    : Lemma
        (requires MH.read_word_in_major mh addr == Some old)
        (ensures
          (match MH.write_word_in_major mh addr value with
           | Some mh' -> MH.read_word_in_major mh' addr == Some value
           | None -> False))
        (decreases Seq.length mh)
    =
    if Seq.length mh = 0 then
      assert False
    else begin
      let c = Seq.head mh in
      let tl = Seq.tail mh in
      if MH.word_in_chunk c addr then begin
        let c' = MH.write_word_in_chunk c addr value in
        MH.write_word_in_chunk_preserves_range c addr value;
        MH.read_write_in_chunk_same c addr value;
        assert (MH.write_word_in_major mh addr value == Some (Seq.cons c' tl));
        assert (MH.chunk_contains_addr c' addr);
        assert (MH.word_in_chunk c' addr);
        assert (MH.read_word_in_chunk c' addr == value);
        read_word_in_major_cons_hit c' tl addr
      end else begin
        if MH.chunk_contains_addr c addr then begin
          assert (MH.read_word_in_major mh addr == None);
          assert False
        end;
        assert (~(MH.chunk_contains_addr c addr));
        lookup_chunk_cons_miss c tl addr;
        read_word_in_major_cons_miss c tl addr;
        assert (MH.read_word_in_major mh addr == MH.read_word_in_major tl addr);
        assert (MH.read_word_in_major tl addr == Some old);
        assert (MH.write_word_in_major mh addr value ==
                (match MH.write_word_in_major tl addr value with
                 | None -> None
                 | Some tl' -> Some (Seq.cons c tl')));
        write_word_in_major_preserves_same_read tl addr old value;
        match MH.write_word_in_major tl addr value with
        | None -> assert False
        | Some tl' ->
          assert (MH.read_word_in_major tl' addr == Some value);
          lookup_chunk_cons_miss c tl' addr;
          read_word_in_major_cons_miss c tl' addr
      end
    end
