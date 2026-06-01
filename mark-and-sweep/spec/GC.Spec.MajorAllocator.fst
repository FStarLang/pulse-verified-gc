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

#push-options "--z3rlimit 40"
let major_fl_valid_gives_pointer (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    major_fl_valid mh fp fuel)
          (ensures MH.is_major_pointer mh fp)
  = ()

let major_fl_valid_gives_mem (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    major_fl_valid mh fp fuel)
          (ensures Seq.mem (fp <: obj_addr) (MH.major_objects mh))
  = ()

let major_fl_valid_gives_wosize (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    major_fl_valid mh fp fuel)
          (ensures (match MH.read_word_in_major mh (hd_address (fp <: obj_addr)) with
                    | Some hdr -> U64.v (Obj.getWosize hdr) >= 1
                    | None -> False))
  = ()

let major_fl_valid_next (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    major_fl_valid mh fp fuel)
          (ensures (match MH.read_word_in_major mh (fp <: obj_addr) with
                    | Some next -> next <> fp /\ major_fl_valid mh next (fuel - 1)
                    | None -> False))
  = ()

let major_fl_valid_step (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    MH.is_major_pointer mh fp /\
                    Seq.mem (fp <: obj_addr) (MH.major_objects mh) /\
                    (match MH.read_word_in_major mh (hd_address (fp <: obj_addr)) with
                     | Some hdr -> U64.v (Obj.getWosize hdr) >= 1
                     | None -> False) /\
                    (match MH.read_word_in_major mh (fp <: obj_addr) with
                     | Some next -> next <> fp /\ major_fl_valid mh next (fuel - 1)
                     | None -> False))
          (ensures major_fl_valid mh fp fuel)
  = ()
#pop-options

#push-options "--z3rlimit 120"
let rec expand_major_heap_preserves_fl_valid (mh: MH.major_heap) (c: MH.heap_chunk)
                                             (new_link: U64.t) (fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_valid mh fp fuel)
          (ensures major_fl_valid (expand_major_heap mh c new_link).major_out fp fuel)
          (decreases fuel)
  = if fuel = 0 then ()
    else begin
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      if fp = 0UL then ()
      else if U64.v fp < U64.v mword || U64.v fp >= heap_size ||
              U64.v fp % U64.v mword <> 0 then
        assert False
      else begin
        let obj : obj_addr = fp in
        let r = init_fresh_chunk c new_link in
        init_fresh_chunk_disjoint_from_all mh c new_link;
        assert (major_fl_valid mh fp fuel);
        assert (MH.is_major_pointer mh fp);
        assert (Seq.mem obj (MH.major_objects mh));
        MH.major_pointer_add_chunk_old mh r.chunk_out fp;
        expand_major_heap_old_object mh c new_link obj;
        match MH.read_word_in_major mh (hd_address obj) with
        | None -> assert False
        | Some hdr ->
          MH.read_word_add_chunk_disjoint_old mh r.chunk_out (hd_address obj) hdr;
          assert (MH.read_word_in_major (expand_major_heap mh c new_link).major_out (hd_address obj) ==
                  Some hdr);
        match MH.read_word_in_major mh obj with
        | None -> assert False
        | Some next ->
          assert (next <> fp);
          expand_major_heap_preserves_fl_valid mh c new_link next fuel';
          MH.read_word_add_chunk_disjoint_old mh r.chunk_out obj next;
          assert (MH.read_word_in_major (expand_major_heap mh c new_link).major_out obj ==
                  Some next)
      end
    end
#pop-options

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

let expand_major_heap_links_fl_valid (mh: MH.major_heap) (c: MH.heap_chunk)
                                     (next_fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_valid mh next_fp fuel /\
                    next_fp <> fresh_chunk_object c)
          (ensures major_fl_valid (expand_major_heap mh c next_fp).major_out
                    (fresh_chunk_object c) (fuel + 1))
  = expand_major_heap_preserves_fl_valid mh c next_fp next_fp fuel;
    expand_major_heap_fresh_fl_valid mh c next_fp fuel

type major_alloc_result = {
  major_alloc_out: MH.major_heap;
  major_fp_out: U64.t;
  major_obj_out: U64.t;
}

let major_write_word_or_same (mh: MH.major_heap) (addr: hp_addr) (value: U64.t)
  : GTot MH.major_heap =
  match MH.write_word_in_major mh addr value with
  | Some mh' -> mh'
  | None -> mh

let major_spec_next_fp (mh: MH.major_heap) (obj: obj_addr) : GTot U64.t =
  match MH.read_word_in_major mh obj with
  | Some next -> next
  | None -> 0UL

let major_alloc_from_block (mh: MH.major_heap) (obj: obj_addr)
                           (requested_wz: nat) (next_fp: U64.t)
  : GTot (MH.major_heap & U64.t) =
  let hd = hd_address obj in
  match MH.read_word_in_major mh hd with
  | None -> (mh, next_fp)
  | Some hdr ->
    let block_wz = U64.v (Obj.getWosize hdr) in
    let leftover = block_wz - requested_wz in
    if block_wz < requested_wz then (mh, next_fp)
    else if leftover >= 2 then begin
      let alloc_hdr = Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
      let mh1 = major_write_word_or_same mh hd alloc_hdr in
      let rem_hd_nat = U64.v hd + (1 + requested_wz) * 8 in
      if rem_hd_nat >= heap_size || rem_hd_nat >= pow2 64 ||
         rem_hd_nat % 8 <> 0 then
        (mh1, next_fp)
      else
        let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
        let rem_wz = leftover - 1 in
        let rem_hdr = Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
        let mh2 = major_write_word_or_same mh1 rem_hd rem_hdr in
        let rem_obj_nat = rem_hd_nat + 8 in
        FStar.Math.Lemmas.pow2_lt_compat 64 57;
        assert_norm (pow2 57 + 8 < pow2 64);
        assert (rem_obj_nat < pow2 64);
        if rem_obj_nat >= heap_size || rem_obj_nat >= pow2 64 ||
           rem_obj_nat % 8 <> 0 then
          (mh2, U64.uint_to_t rem_obj_nat)
        else
          let rem_field : hp_addr = U64.uint_to_t rem_obj_nat in
          let mh3 = major_write_word_or_same mh2 rem_field next_fp in
          (mh3, U64.uint_to_t rem_obj_nat)
    end else begin
      let alloc_hdr = Alloc.make_header (U64.uint_to_t block_wz) Alloc.white_bits 0UL in
      let mh1 = major_write_word_or_same mh hd alloc_hdr in
      (mh1, next_fp)
    end

let rec major_alloc_search (mh: MH.major_heap) (head_fp: U64.t) (prev_fp: U64.t)
                           (cur_fp: U64.t) (requested_wz: nat) (fuel: nat)
  : GTot major_alloc_result (decreases fuel)
  = if fuel = 0 then { major_alloc_out = mh; major_fp_out = head_fp; major_obj_out = 0UL }
    else
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    if U64.v cur_fp < U64.v zero_addr + U64.v mword then
      { major_alloc_out = mh; major_fp_out = head_fp; major_obj_out = 0UL }
    else if U64.v cur_fp >= heap_size then
      { major_alloc_out = mh; major_fp_out = head_fp; major_obj_out = 0UL }
    else if U64.v cur_fp % U64.v mword <> 0 then
      { major_alloc_out = mh; major_fp_out = head_fp; major_obj_out = 0UL }
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      match MH.read_word_in_major mh hd with
      | None -> { major_alloc_out = mh; major_fp_out = head_fp; major_obj_out = 0UL }
      | Some hdr ->
        let block_wz = U64.v (Obj.getWosize hdr) in
        let next_fp = major_spec_next_fp mh obj in
        if block_wz >= requested_wz then begin
          let (mh', new_remainder_fp) = major_alloc_from_block mh obj requested_wz next_fp in
          if prev_fp = 0UL then
            { major_alloc_out = mh'; major_fp_out = new_remainder_fp; major_obj_out = cur_fp }
          else if U64.v prev_fp >= U64.v mword &&
                  U64.v prev_fp < heap_size &&
                  U64.v prev_fp % U64.v mword = 0 then
            let mh2 = major_write_word_or_same mh' (prev_fp <: hp_addr) new_remainder_fp in
            { major_alloc_out = mh2; major_fp_out = head_fp; major_obj_out = cur_fp }
          else
            { major_alloc_out = mh'; major_fp_out = new_remainder_fp; major_obj_out = cur_fp }
        end else
          major_alloc_search mh head_fp cur_fp next_fp requested_wz fuel'
    end

let major_alloc_spec_with_fuel (mh: MH.major_heap) (fp: U64.t)
                               (requested_wz: nat) (fuel: nat)
  : GTot major_alloc_result =
  let wz = Alloc.normalized_wosize requested_wz in
  major_alloc_search mh fp 0UL fp wz fuel

let major_alloc_search_fuel_0 (mh: MH.major_heap) (head prev cur: U64.t) (wz: nat)
  : Lemma (major_alloc_search mh head prev cur wz 0 ==
           { major_alloc_out = mh; major_fp_out = head; major_obj_out = 0UL })
  = ()

let major_alloc_search_invalid (mh: MH.major_heap) (head prev cur: U64.t)
                               (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    (U64.v cur < U64.v zero_addr + U64.v mword \/
                     U64.v cur >= heap_size \/
                     U64.v cur % U64.v mword <> 0))
          (ensures major_alloc_search mh head prev cur wz fuel ==
                   { major_alloc_out = mh; major_fp_out = head; major_obj_out = 0UL })
  = ()

let major_spec_next_fp_some (mh: MH.major_heap) (obj: obj_addr) (next: U64.t)
  : Lemma (requires MH.read_word_in_major mh obj == Some next)
          (ensures major_spec_next_fp mh obj == next)
  = ()

let major_spec_next_fp_none (mh: MH.major_heap) (obj: obj_addr)
  : Lemma (requires MH.read_word_in_major mh obj == None)
          (ensures major_spec_next_fp mh obj == 0UL)
  = ()

let major_write_word_or_same_some (mh mh': MH.major_heap) (addr: hp_addr) (value: U64.t)
  : Lemma (requires MH.write_word_in_major mh addr value == Some mh')
          (ensures major_write_word_or_same mh addr value == mh')
  = ()

let major_write_word_or_same_none (mh: MH.major_heap) (addr: hp_addr) (value: U64.t)
  : Lemma (requires MH.write_word_in_major mh addr value == None)
          (ensures major_write_word_or_same mh addr value == mh)
  = ()

let major_alloc_from_block_missing_header (mh: MH.major_heap) (obj: obj_addr)
                                          (wz: nat) (next: U64.t)
  : Lemma (requires MH.read_word_in_major mh (hd_address obj) == None)
          (ensures major_alloc_from_block mh obj wz next == (mh, next))
  = ()

let major_alloc_from_block_too_small (mh: MH.major_heap) (obj: obj_addr)
                                     (wz: nat) (next: U64.t) (hdr: U64.t)
  : Lemma (requires MH.read_word_in_major mh (hd_address obj) == Some hdr /\
                    U64.v (Obj.getWosize hdr) < wz)
          (ensures major_alloc_from_block mh obj wz next == (mh, next))
  = ()

let major_alloc_from_block_exact (mh: MH.major_heap) (obj: obj_addr)
                                 (wz: nat) (next: U64.t) (hdr: U64.t)
  : Lemma (requires MH.read_word_in_major mh (hd_address obj) == Some hdr /\
                    U64.v (Obj.getWosize hdr) >= wz /\
                    U64.v (Obj.getWosize hdr) - wz < 2)
          (ensures (let hd = hd_address obj in
                    let bwz = U64.v (Obj.getWosize hdr) in
                    let ahdr = Alloc.make_header (U64.uint_to_t bwz) Alloc.white_bits 0UL in
                    let mh1 = major_write_word_or_same mh hd ahdr in
                    major_alloc_from_block mh obj wz next == (mh1, next)))
  = ()

let major_alloc_from_block_split_normal (mh: MH.major_heap) (obj: obj_addr)
                                        (wz: nat) (next: U64.t) (hdr: U64.t)
  : Lemma (requires MH.read_word_in_major mh (hd_address obj) == Some hdr /\
                    (let hd = hd_address obj in
                     let bwz = U64.v (Obj.getWosize hdr) in
                     bwz >= wz /\
                     bwz - wz >= 2 /\
                     U64.v hd + (1 + wz) * 8 < heap_size /\
                     U64.v hd + (1 + wz) * 8 + 8 < heap_size /\
                     (U64.v hd + (1 + wz) * 8) % 8 == 0 /\
                     (U64.v hd + (1 + wz) * 8 + 8) % 8 == 0))
          (ensures (let hd = hd_address obj in
                    let bwz = U64.v (Obj.getWosize hdr) in
                    let ahdr = Alloc.make_header (U64.uint_to_t wz) Alloc.white_bits 0UL in
                    let mh1 = major_write_word_or_same mh hd ahdr in
                    let rhn = U64.v hd + (1 + wz) * 8 in
                    let rh : hp_addr = U64.uint_to_t rhn in
                    let rw = bwz - wz - 1 in
                    let rhdr = Alloc.make_header (U64.uint_to_t rw) Alloc.blue_bits 0UL in
                    let mh2 = major_write_word_or_same mh1 rh rhdr in
                    let ron = rhn + 8 in
                    let ro : hp_addr = U64.uint_to_t ron in
                    let mh3 = major_write_word_or_same mh2 ro next in
                    major_alloc_from_block mh obj wz next == (mh3, U64.uint_to_t ron)))
  = ()

let major_alloc_search_missing_header (mh: MH.major_heap) (head prev cur: U64.t)
                                      (wz: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    MH.read_word_in_major mh (hd_address (cur <: obj_addr)) == None)
          (ensures major_alloc_search mh head prev cur wz fuel ==
                   { major_alloc_out = mh; major_fp_out = head; major_obj_out = 0UL })
  = ()

let major_alloc_search_advance (mh: MH.major_heap) (head prev cur: U64.t)
                               (wz: nat) (fuel: nat) (hdr: U64.t)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    MH.read_word_in_major mh (hd_address (cur <: obj_addr)) == Some hdr /\
                    U64.v (Obj.getWosize hdr) < wz)
          (ensures major_alloc_search mh head prev cur wz fuel ==
                   major_alloc_search mh head cur
                     (major_spec_next_fp mh (cur <: obj_addr)) wz (fuel - 1))
  = ()

let major_alloc_search_found_head (mh: MH.major_heap) (head prev cur: U64.t)
                                  (wz: nat) (fuel: nat) (hdr: U64.t)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    prev = 0UL /\
                    MH.read_word_in_major mh (hd_address (cur <: obj_addr)) == Some hdr /\
                    U64.v (Obj.getWosize hdr) >= wz)
          (ensures (let obj : obj_addr = cur in
                    let next = major_spec_next_fp mh obj in
                    let (mh', new_fp) = major_alloc_from_block mh obj wz next in
                    major_alloc_search mh head prev cur wz fuel ==
                    { major_alloc_out = mh'; major_fp_out = new_fp; major_obj_out = cur }))
  = ()

let major_alloc_search_found_prev (mh: MH.major_heap) (head prev cur: U64.t)
                                  (wz: nat) (fuel: nat) (hdr: U64.t)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    prev <> 0UL /\
                    U64.v prev >= U64.v mword /\
                    U64.v prev < heap_size /\
                    U64.v prev % U64.v mword = 0 /\
                    MH.read_word_in_major mh (hd_address (cur <: obj_addr)) == Some hdr /\
                    U64.v (Obj.getWosize hdr) >= wz)
          (ensures (let obj : obj_addr = cur in
                    let next = major_spec_next_fp mh obj in
                    let (mh', new_fp) = major_alloc_from_block mh obj wz next in
                    let mh2 = major_write_word_or_same mh' (prev <: hp_addr) new_fp in
                    major_alloc_search mh head prev cur wz fuel ==
                    { major_alloc_out = mh2; major_fp_out = head; major_obj_out = cur }))
  = ()

#push-options "--z3rlimit 80"
let major_alloc_after_expand_returns_fresh (mh: MH.major_heap) (c: MH.heap_chunk)
                                           (next_fp: U64.t)
                                           (requested_wz fuel: nat)
  : Lemma (requires U64.v c.base >= U64.v zero_addr /\
                    Alloc.normalized_wosize requested_wz <= fresh_chunk_wosize c)
          (ensures (let er = expand_major_heap mh c next_fp in
                    let r = major_alloc_spec_with_fuel er.major_out er.fp_out requested_wz (fuel + 1) in
                    r.major_obj_out == er.fp_out))
  = let er = expand_major_heap mh c next_fp in
    let fp = er.fp_out in
    let wz = Alloc.normalized_wosize requested_wz in
    let hdr = Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL in
    expand_major_heap_header mh c next_fp;
    expand_major_heap_header_fields mh c next_fp;
    expand_major_heap_link mh c next_fp;
    fresh_chunk_object_in_chunk c;
    f_address_spec c.base;
    assert (fp == fresh_chunk_object c);
    assert (U64.v fp == U64.v c.base + U64.v mword);
    assert (U64.v fp >= U64.v zero_addr + U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    assert (U64.v c.base + U64.v mword < heap_size);
    hd_f_roundtrip c.base;
    assert (hd_address fp == c.base);
    assert (MH.read_word_in_major er.major_out (hd_address fp) == Some hdr);
    assert (Obj.getWosize hdr == fresh_chunk_wosize_u64 c);
    assert (U64.v (Obj.getWosize hdr) == fresh_chunk_wosize c);
    assert (U64.v (Obj.getWosize hdr) >= wz);
    major_alloc_search_found_head er.major_out fp 0UL fp wz (fuel + 1) hdr
#pop-options

let major_alloc_spec_expand_on_oom (mh: MH.major_heap) (fp: U64.t)
                                   (requested_wz fuel: nat)
                                   (fresh: MH.heap_chunk)
  : GTot major_alloc_result =
  let first = major_alloc_spec_with_fuel mh fp requested_wz fuel in
  if first.major_obj_out <> 0UL then first
  else
    let er = expand_major_heap mh fresh fp in
    major_alloc_spec_with_fuel er.major_out er.fp_out requested_wz (fuel + 1)

let major_alloc_expand_on_oom_returns_fresh (mh: MH.major_heap) (fp: U64.t)
                                            (requested_wz fuel: nat)
                                            (fresh: MH.heap_chunk)
  : Lemma (requires (major_alloc_spec_with_fuel mh fp requested_wz fuel).major_obj_out == 0UL /\
                    U64.v fresh.base >= U64.v zero_addr /\
                    Alloc.normalized_wosize requested_wz <= fresh_chunk_wosize fresh)
          (ensures (major_alloc_spec_expand_on_oom mh fp requested_wz fuel fresh).major_obj_out ==
                   fresh_chunk_object fresh)
  = major_alloc_after_expand_returns_fresh mh fresh fp requested_wz fuel;
    let er = expand_major_heap mh fresh fp in
    assert (er.fp_out == fresh_chunk_object fresh)
