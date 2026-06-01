/// ---------------------------------------------------------------------------
/// GC.Spec.MajorAllocator - Chunk-aware allocation/expansion helpers
/// ---------------------------------------------------------------------------
///
/// This module starts the chunked-major allocation layer by specifying how a
/// fresh active chunk is initialized as one blue free-list block.  It is kept
/// beside the existing dense allocator while the collector is ported.

module GC.Spec.MajorAllocator

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module MH = GC.Spec.MajorHeap
module Alloc = GC.Spec.Allocator
module AllocCore = GC.Spec.Allocator.Lemmas.Core
module AllocHeader = GC.Spec.Allocator.Lemmas.Header
module Obj = GC.Spec.Object
module Header = GC.Lib.Header

open GC.Spec.Base
open GC.Spec.Heap

let chunk_word_capacity (c: MH.heap_chunk) : nat =
  c.size / U64.v mword

let fresh_chunk_wosize (c: MH.heap_chunk) : nat =
  chunk_word_capacity c - 1

let fresh_chunk_wosize_fits (c: MH.heap_chunk)
  : Lemma (fresh_chunk_wosize c < pow2 54)
  = assert (c.size < pow2 57);
    FStar.Math.Lemmas.lemma_div_lt c.size 57 3;
    assert (chunk_word_capacity c < pow2 54)

let fresh_chunk_wosize_u64 (c: MH.heap_chunk)
  : wz:U64.t{U64.v wz == fresh_chunk_wosize c /\ U64.v wz < pow2 54}
  = fresh_chunk_wosize_fits c;
    U64.uint_to_t (fresh_chunk_wosize c)

let fresh_chunk_has_block (c: MH.heap_chunk)
  : Lemma (chunk_word_capacity c >= 2)
  = FStar.Math.Lemmas.lemma_div_exact c.size (U64.v mword);
    assert (c.size == chunk_word_capacity c * U64.v mword);
    assert (U64.v mword == 8)

let fresh_chunk_wosize_nonzero (c: MH.heap_chunk)
  : Lemma (fresh_chunk_wosize c >= 1)
  = fresh_chunk_has_block c

let fresh_chunk_object (c: MH.heap_chunk) : obj_addr =
  fresh_chunk_has_block c;
  assert (U64.v c.base + U64.v mword < heap_size);
  f_address c.base

let fresh_chunk_object_word (c: MH.heap_chunk)
  : Lemma (MH.word_in_chunk c (fresh_chunk_object c))
  = fresh_chunk_has_block c;
    f_address_spec c.base;
    assert (U64.v (fresh_chunk_object c) == U64.v c.base + U64.v mword);
    assert (U64.v (fresh_chunk_object c) + U64.v mword <= MH.chunk_end c)

let fresh_chunk_object_in_chunk (c: MH.heap_chunk)
  : Lemma (MH.obj_addr_in_chunk c (fresh_chunk_object c) /\
           MH.pointer_in_chunk c (fresh_chunk_object c))
  = fresh_chunk_has_block c;
    f_address_spec c.base;
    assert (U64.v (fresh_chunk_object c) == U64.v c.base + U64.v mword);
    assert (U64.v (fresh_chunk_object c) >= MH.chunk_start c + U64.v mword);
    assert (U64.v (fresh_chunk_object c) < MH.chunk_end c);
    assert (U64.v (fresh_chunk_object c) % U64.v mword == 0)

type fresh_chunk_result (c: MH.heap_chunk) = {
  chunk_out: c2:MH.heap_chunk{MH.word_in_chunk c2 c.base /\
                              MH.word_in_chunk c2 (fresh_chunk_object c)};
  fp_out: obj_addr;
}

let init_fresh_chunk (c: MH.heap_chunk) (next_fp: U64.t)
  : Tot (fresh_chunk_result c)
  = fresh_chunk_wosize_fits c;
    fresh_chunk_has_block c;
    let wz = fresh_chunk_wosize c in
    let hdr = Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL in
    assert (MH.word_in_chunk c c.base);
    let c1 = MH.write_word_in_chunk c c.base hdr in
    let obj = fresh_chunk_object c in
    fresh_chunk_object_word c;
    MH.write_word_in_chunk_preserves_word c c.base hdr obj;
    let c2 = MH.write_word_in_chunk c1 obj next_fp in
    MH.write_word_in_chunk_preserves_word c1 obj next_fp c.base;
    MH.write_word_in_chunk_preserves_word c1 obj next_fp obj;
    { chunk_out = c2; fp_out = obj }

let init_fresh_chunk_header (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let r = init_fresh_chunk c next_fp in
           MH.read_word_in_chunk r.chunk_out c.base ==
           Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL)
  = fresh_chunk_wosize_fits c;
    let hdr = Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL in
    let c1 = MH.write_word_in_chunk c c.base hdr in
    let obj = fresh_chunk_object c in
    fresh_chunk_object_word c;
    MH.write_word_in_chunk_preserves_word c c.base hdr c.base;
    MH.write_word_in_chunk_preserves_word c c.base hdr obj;
    MH.read_write_in_chunk_same c c.base hdr;
    f_address_spec c.base;
    assert (U64.v c.base + U64.v mword <= U64.v obj);
    MH.read_write_in_chunk_different c1 obj c.base next_fp

let init_fresh_chunk_link (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let r = init_fresh_chunk c next_fp in
           r.fp_out == fresh_chunk_object c /\
           MH.read_word_in_chunk r.chunk_out r.fp_out == next_fp)
  = fresh_chunk_wosize_fits c;
    let hdr = Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL in
    let c1 = MH.write_word_in_chunk c c.base hdr in
    let obj = fresh_chunk_object c in
    fresh_chunk_object_word c;
    MH.write_word_in_chunk_preserves_word c c.base hdr obj;
    MH.read_write_in_chunk_same c1 obj next_fp

let init_fresh_chunk_header_fields (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let r = init_fresh_chunk c next_fp in
           let hdr = MH.read_word_in_chunk r.chunk_out c.base in
           Obj.getWosize hdr == fresh_chunk_wosize_u64 c /\
           Obj.getColor hdr == Header.Blue /\
           U64.v (Obj.getTag hdr) == 0)
  = fresh_chunk_wosize_fits c;
    init_fresh_chunk_header c next_fp;
    let wz = fresh_chunk_wosize_u64 c in
    let hdr = Alloc.make_header wz Alloc.blue_bits 0UL in
    AllocHeader.make_header_getWosize wz Alloc.blue_bits 0UL;
    AllocHeader.make_header_getTag wz Alloc.blue_bits 0UL;
    AllocCore.make_header_getColor wz Alloc.blue_bits 0UL;
    Obj.getColor_raw hdr

let init_fresh_chunk_preserves_range (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let r = init_fresh_chunk c next_fp in
           r.chunk_out.base == c.base /\
           r.chunk_out.size == c.size /\
           MH.chunk_start r.chunk_out == MH.chunk_start c /\
           MH.chunk_end r.chunk_out == MH.chunk_end c /\
           MH.word_in_chunk r.chunk_out c.base /\
           MH.word_in_chunk r.chunk_out (fresh_chunk_object c) /\
           MH.obj_addr_in_chunk r.chunk_out (fresh_chunk_object c) /\
           MH.pointer_in_chunk r.chunk_out (fresh_chunk_object c))
  = fresh_chunk_object_in_chunk c

let init_fresh_chunk_disjoint_from_all (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (requires MH.chunk_disjoint_from_all c mh)
          (ensures (let r = init_fresh_chunk c next_fp in
                    MH.chunk_disjoint_from_all r.chunk_out mh))
  = init_fresh_chunk_preserves_range c next_fp;
    let r = init_fresh_chunk c next_fp in
    assert (forall i. i < Seq.length mh ==>
             MH.chunks_disjoint r.chunk_out (Seq.index mh i))

#push-options "--z3rlimit 80"
let init_fresh_chunk_objects (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let r = init_fresh_chunk c next_fp in
           MH.objects_in_chunk r.chunk_out == Seq.cons r.fp_out Seq.empty)
  = init_fresh_chunk_preserves_range c next_fp;
    init_fresh_chunk_header c next_fp;
    init_fresh_chunk_header_fields c next_fp;
    init_fresh_chunk_link c next_fp;
    fresh_chunk_has_block c;
    let r = init_fresh_chunk c next_fp in
    let c2 = r.chunk_out in
    let start = c2.base in
    assert (start == c.base);
    assert (MH.chunk_end c2 == MH.chunk_end c);
    assert (MH.chunk_start c2 == MH.chunk_start c);
    assert (U64.v start + U64.v mword < MH.chunk_end c2);
    let header = MH.read_word_in_chunk c2 start in
    assert (header == Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL);
    let wz = Obj.getWosize header in
    assert (wz == fresh_chunk_wosize_u64 c);
    assert (U64.v wz == fresh_chunk_wosize c);
    FStar.Math.Lemmas.lemma_div_exact c.size (U64.v mword);
    assert (c.size == chunk_word_capacity c * U64.v mword);
    assert (U64.v mword == 8);
    let obj_size_words = U64.v wz + 1 in
    assert (obj_size_words == chunk_word_capacity c);
    let next_start_nat = U64.v start + obj_size_words * U64.v mword in
    assert (next_start_nat == MH.chunk_end c2);
    assert (next_start_nat <= MH.chunk_end c2);
    assert (next_start_nat < pow2 64);
    f_address_spec start;
    assert (f_address start == r.fp_out);
    assert (MH.objects_in_chunk c2 == Seq.cons r.fp_out Seq.empty)
#pop-options

type expand_result = {
  major_out: MH.major_heap;
  fp_out: obj_addr;
}

let expand_major_heap (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Tot expand_result =
  let r = init_fresh_chunk c next_fp in
  { major_out = MH.add_chunk mh r.chunk_out; fp_out = r.fp_out }

let expand_major_heap_wf (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (requires MH.well_formed_major_heap mh /\
                    MH.chunk_disjoint_from_all c mh)
          (ensures MH.well_formed_major_heap (expand_major_heap mh c next_fp).major_out)
  = init_fresh_chunk_disjoint_from_all mh c next_fp;
    let r = init_fresh_chunk c next_fp in
    MH.add_chunk_preserves_wf mh r.chunk_out

let expand_major_heap_old_read (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
                               (addr: hp_addr)
  : Lemma (requires ~(MH.chunk_contains_addr c addr))
          (ensures MH.read_word_in_major (expand_major_heap mh c next_fp).major_out addr ==
                   MH.read_word_in_major mh addr)
  = init_fresh_chunk_preserves_range c next_fp;
    let r = init_fresh_chunk c next_fp in
    assert (~(MH.chunk_contains_addr r.chunk_out addr));
    MH.read_word_add_chunk_miss mh r.chunk_out addr

let expand_major_heap_header (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (MH.read_word_in_major (expand_major_heap mh c next_fp).major_out c.base ==
           Some (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL))
  = init_fresh_chunk_header c next_fp;
    let r = init_fresh_chunk c next_fp in
    MH.read_word_add_chunk_hit mh r.chunk_out c.base

let expand_major_heap_link (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let er = expand_major_heap mh c next_fp in
           er.fp_out == fresh_chunk_object c /\
           MH.read_word_in_major er.major_out er.fp_out == Some next_fp)
  = init_fresh_chunk_link c next_fp;
    let r = init_fresh_chunk c next_fp in
    MH.read_word_add_chunk_hit mh r.chunk_out r.fp_out

let expand_major_heap_header_fields (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (let er = expand_major_heap mh c next_fp in
           er.fp_out == fresh_chunk_object c /\
           (match MH.read_word_in_major er.major_out c.base with
            | Some hdr ->
              Obj.getWosize hdr == fresh_chunk_wosize_u64 c /\
              Obj.getColor hdr == Header.Blue /\
              U64.v (Obj.getTag hdr) == 0
            | None -> False))
  = expand_major_heap_link mh c next_fp;
    expand_major_heap_header mh c next_fp;
    init_fresh_chunk_header_fields c next_fp

let expand_major_heap_objects (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (MH.major_objects (expand_major_heap mh c next_fp).major_out ==
           Seq.cons (fresh_chunk_object c) (MH.major_objects mh))
  = init_fresh_chunk_objects c next_fp;
    let r = init_fresh_chunk c next_fp in
    MH.major_objects_add_chunk mh r.chunk_out;
    assert (MH.objects_in_chunk r.chunk_out == Seq.cons r.fp_out Seq.empty);
    Seq.lemma_len_append (Seq.cons r.fp_out Seq.empty) (MH.major_objects mh);
    assert (forall i. i < Seq.length (Seq.cons r.fp_out (MH.major_objects mh)) ==>
             Seq.index (Seq.append (Seq.cons r.fp_out Seq.empty) (MH.major_objects mh)) i ==
             Seq.index (Seq.cons r.fp_out (MH.major_objects mh)) i);
    Seq.lemma_eq_intro
      (Seq.append (Seq.cons r.fp_out Seq.empty) (MH.major_objects mh))
      (Seq.cons r.fp_out (MH.major_objects mh));
    Seq.lemma_eq_elim
      (Seq.append (Seq.cons r.fp_out Seq.empty) (MH.major_objects mh))
      (Seq.cons r.fp_out (MH.major_objects mh))

let expand_major_heap_fresh_object (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (Seq.mem (fresh_chunk_object c) (MH.major_objects (expand_major_heap mh c next_fp).major_out))
  = expand_major_heap_objects mh c next_fp;
    SeqProps.mem_cons (fresh_chunk_object c) (MH.major_objects mh)

let expand_major_heap_old_object (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
                                (x: obj_addr)
  : Lemma (requires Seq.mem x (MH.major_objects mh))
          (ensures Seq.mem x (MH.major_objects (expand_major_heap mh c next_fp).major_out))
  = expand_major_heap_objects mh c next_fp;
    SeqProps.mem_cons (fresh_chunk_object c) (MH.major_objects mh)

let expand_major_heap_fresh_not_old (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  : Lemma (requires MH.chunk_disjoint_from_all c mh)
          (ensures ~(Seq.mem (fresh_chunk_object c) (MH.major_objects mh)))
  = init_fresh_chunk_disjoint_from_all mh c next_fp;
    init_fresh_chunk_objects c next_fp;
    let r = init_fresh_chunk c next_fp in
    SeqProps.mem_cons r.fp_out Seq.empty;
    MH.fresh_chunk_object_not_old mh r.chunk_out r.fp_out

let rec major_fl_valid (mh: MH.major_heap) (fp: U64.t) (fuel: nat) : Tot prop
  (decreases fuel)
  = if fuel = 0 then True
    else
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      if fp = 0UL then True
      else if U64.v fp < U64.v mword || U64.v fp >= heap_size ||
              U64.v fp % U64.v mword <> 0 then False
      else
        let obj : obj_addr = fp in
        MH.is_major_pointer mh fp /\
        Seq.mem obj (MH.major_objects mh) /\
        (match MH.read_word_in_major mh (hd_address obj) with
         | Some hdr -> U64.v (Obj.getWosize hdr) >= 1
         | None -> False) /\
        (match MH.read_word_in_major mh obj with
         | Some next -> next <> fp /\ major_fl_valid mh next fuel'
         | None -> False)

let major_fl_valid_zero (mh: MH.major_heap) (fp: U64.t)
  : Lemma (major_fl_valid mh fp 0)
  = ()

let major_fl_valid_null (mh: MH.major_heap) (fuel: nat)
  : Lemma (requires fuel > 0)
          (ensures major_fl_valid mh 0UL fuel)
  = ()

#push-options "--z3rlimit 80"
let expand_major_heap_fresh_fl_valid (mh: MH.major_heap) (c: MH.heap_chunk)
                                     (next_fp: U64.t) (fuel: nat)
  : Lemma (requires major_fl_valid (expand_major_heap mh c next_fp).major_out next_fp fuel /\
                    next_fp <> fresh_chunk_object c)
          (ensures major_fl_valid (expand_major_heap mh c next_fp).major_out
                    (fresh_chunk_object c) (fuel + 1))
  = fresh_chunk_object_in_chunk c;
    fresh_chunk_wosize_nonzero c;
    let er = expand_major_heap mh c next_fp in
    let fp = fresh_chunk_object c in
    expand_major_heap_fresh_object mh c next_fp;
    expand_major_heap_header mh c next_fp;
    expand_major_heap_header_fields mh c next_fp;
    expand_major_heap_link mh c next_fp;
    f_address_spec c.base;
    assert (U64.v fp >= U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    assert (MH.is_major_pointer er.major_out fp);
    assert (Seq.mem fp (MH.major_objects er.major_out));
    assert (MH.read_word_in_major er.major_out c.base ==
            Some (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL));
    assert (Obj.getWosize (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL) ==
            fresh_chunk_wosize_u64 c);
    assert (U64.v (fresh_chunk_wosize_u64 c) >= 1);
    assert (U64.v c.base + U64.v mword < heap_size);
    hd_f_roundtrip c.base;
    assert (f_address c.base == fp);
    assert (hd_address fp == c.base);
    assert (MH.read_word_in_major er.major_out fp == Some next_fp)
#pop-options
