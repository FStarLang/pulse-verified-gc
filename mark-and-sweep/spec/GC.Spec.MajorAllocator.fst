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

let chunk_size_capacity_mul (c: MH.heap_chunk)
  : Lemma (c.size == chunk_word_capacity c * U64.v mword)
  = assert (U64.v mword == 8);
    assert (c.size % 8 == 0);
    FStar.Math.Lemmas.lemma_div_exact c.size 8

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

let aligned_lt_heap_has_word_room (a: nat)
  : Lemma (requires a < heap_size /\ a % U64.v mword == 0)
          (ensures a + U64.v mword <= heap_size)
  = FStar.Math.Lemmas.lemma_div_exact a (U64.v mword);
    FStar.Math.Lemmas.lemma_div_exact heap_size (U64.v mword)

let aligned_plus_word_product (a words: nat)
  : Lemma (requires a % 8 == 0)
          (ensures (a + words * 8) % 8 == 0)
  = FStar.Math.Lemmas.lemma_mod_plus_distr_l a (words * 8) 8;
    FStar.Math.Lemmas.cancel_mul_mod words 8;
    assert ((words * 8) % 8 == 0);
    assert (((a % 8) + words * 8) % 8 == 0);
    assert ((a + words * 8) % 8 == 0)

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

#push-options "--z3rlimit 10"
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
    assert (U64.v mword == 8);
    chunk_size_capacity_mul c;
    assert (c.size == chunk_word_capacity c * U64.v mword);
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

#push-options "--z3rlimit 10"
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

let major_fl_valid_header_lookup_index (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    major_fl_valid mh fp fuel)
          (ensures (let obj : obj_addr = fp in
                    let addr = hd_address obj in
                    let i = MH.lookup_chunk_index_value mh addr in
                    MH.lookup_chunk_index mh addr == Some i /\
                    i < Seq.length mh /\
                    MH.word_in_chunk (Seq.index mh i) addr /\
                    (match MH.read_word_in_major mh addr with
                     | Some hdr ->
                       MH.read_word_in_chunk (Seq.index mh i) addr == hdr /\
                       U64.v (Obj.getWosize hdr) >= 1
                     | None -> False)))
  = major_fl_valid_gives_wosize mh fp fuel;
    let obj : obj_addr = fp in
    let addr = hd_address obj in
    match MH.read_word_in_major mh addr with
    | None -> assert False
    | Some hdr ->
      MH.read_word_in_major_lookup_index mh addr hdr

let major_fl_valid_link_lookup_index (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    major_fl_valid mh fp fuel)
          (ensures (let obj : obj_addr = fp in
                    let i = MH.lookup_chunk_index_value mh obj in
                    MH.lookup_chunk_index mh obj == Some i /\
                    i < Seq.length mh /\
                    MH.word_in_chunk (Seq.index mh i) obj /\
                    (match MH.read_word_in_major mh obj with
                     | Some next ->
                       MH.read_word_in_chunk (Seq.index mh i) obj == next /\
                       next <> fp /\
                       major_fl_valid mh next (fuel - 1)
                     | None -> False)))
  = major_fl_valid_next mh fp fuel;
    let obj : obj_addr = fp in
    match MH.read_word_in_major mh obj with
    | None -> assert False
    | Some next ->
      MH.read_word_in_major_lookup_index mh obj next

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

let rec major_fl_above_zero (mh: MH.major_heap) (fp: U64.t) (fuel: nat) : Tot prop
  (decreases fuel)
  = if fuel = 0 then True
    else
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      if fp = 0UL then True
      else if U64.v fp < U64.v zero_addr + U64.v mword ||
             U64.v fp >= heap_size ||
             U64.v fp % U64.v mword <> 0 then False
      else
        let obj : obj_addr = fp in
        match MH.read_word_in_major mh obj with
        | Some next -> major_fl_above_zero mh next fuel'
        | None -> False

let major_fl_above_zero_fuel_0 (mh: MH.major_heap) (fp: U64.t)
  : Lemma (major_fl_above_zero mh fp 0)
  = ()

let major_fl_above_zero_null (mh: MH.major_heap) (fuel: nat)
  : Lemma (requires fuel > 0)
          (ensures major_fl_above_zero mh 0UL fuel)
  = ()

let major_fl_above_zero_current (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                   fp <> 0UL /\
                   major_fl_above_zero mh fp fuel)
          (ensures U64.v fp >= U64.v zero_addr + U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword == 0)
  = ()

let major_fl_above_zero_next (mh: MH.major_heap) (fp: obj_addr)
                           (fuel: nat) (next: U64.t)
  : Lemma (requires fuel > 0 /\
                   U64.v fp >= U64.v zero_addr + U64.v mword /\
                   major_fl_above_zero mh fp fuel /\
                   MH.read_word_in_major mh fp == Some next)
          (ensures major_fl_above_zero mh next (fuel - 1))
  = ()

let major_fl_valid_above_zero_next (mh: MH.major_heap) (fp: obj_addr)
                                 (fuel: nat)
  : Lemma (requires fuel > 0 /\
                   U64.v fp >= U64.v zero_addr + U64.v mword /\
                   major_fl_valid mh fp fuel /\
                   major_fl_above_zero mh fp fuel)
          (ensures (match MH.read_word_in_major mh fp with
                   | Some next ->
                     next <> fp /\
                     major_fl_valid mh next (fuel - 1) /\
                     major_fl_above_zero mh next (fuel - 1)
                   | None -> False))
  = major_fl_valid_next mh fp fuel;
    match MH.read_word_in_major mh fp with
    | None -> assert False
    | Some next -> major_fl_above_zero_next mh fp fuel next

let rec major_fl_blocks_fit (mh: MH.major_heap) (fp: U64.t) (fuel: nat) : Tot prop
  (decreases fuel)
  = if fuel = 0 then True
    else
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      if fp = 0UL then True
      else if U64.v fp < U64.v mword || U64.v fp >= heap_size ||
              U64.v fp % U64.v mword <> 0 then False
      else
        let obj : obj_addr = fp in
        let base = hd_address obj in
        let idx = MH.lookup_chunk_index_value mh base in
        MH.lookup_chunk_index mh base == Some idx /\
        idx < Seq.length mh /\
        MH.word_in_chunk (Seq.index mh idx) base /\
        (match MH.read_word_in_major mh base with
         | Some hdr ->
           U64.v base + (1 + U64.v (Obj.getWosize hdr)) * U64.v mword <=
             MH.chunk_end (Seq.index mh idx)
         | None -> False) /\
        (match MH.read_word_in_major mh obj with
         | Some next -> major_fl_blocks_fit mh next fuel'
         | None -> False)

let major_fl_blocks_fit_null (mh: MH.major_heap) (fuel: nat)
  : Lemma (requires fuel > 0)
          (ensures major_fl_blocks_fit mh 0UL fuel)
  = ()

let major_fl_blocks_fit_current (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                   U64.v fp >= U64.v mword /\
                   U64.v fp < heap_size /\
                   U64.v fp % U64.v mword == 0 /\
                   major_fl_blocks_fit mh fp fuel)
          (ensures (let obj : obj_addr = fp in
                    let base = hd_address obj in
                    let idx = MH.lookup_chunk_index_value mh base in
                    MH.lookup_chunk_index mh base == Some idx /\
                    idx < Seq.length mh /\
                    MH.word_in_chunk (Seq.index mh idx) base /\
                    (match MH.read_word_in_major mh base with
                     | Some hdr ->
                       U64.v base +
                         (1 + U64.v (Obj.getWosize hdr)) * U64.v mword <=
                         MH.chunk_end (Seq.index mh idx)
                     | None -> False)))
  = ()

let major_fl_blocks_fit_next (mh: MH.major_heap) (fp: obj_addr)
                             (fuel: nat) (next: U64.t)
  : Lemma (requires fuel > 0 /\
                   major_fl_blocks_fit mh fp fuel /\
                   MH.read_word_in_major mh fp == Some next)
          (ensures major_fl_blocks_fit mh next (fuel - 1))
  = ()

let major_fl_head_wosize (mh: MH.major_heap) (fp: U64.t) : Tot nat =
  if fp = 0UL then 0
  else if U64.v fp < U64.v zero_addr + U64.v mword ||
          U64.v fp >= heap_size ||
          U64.v fp % U64.v mword <> 0 then 0
  else
    match MH.read_word_in_major mh (hd_address (fp <: obj_addr)) with
    | Some hdr -> U64.v (Obj.getWosize hdr)
    | None -> 0

let major_fl_head_wosize_current (mh: MH.major_heap) (fp: U64.t)
                                (fuel: nat)
  : Lemma
      (requires fuel > 0 /\
               fp <> 0UL /\
               major_fl_valid mh fp fuel /\
               major_fl_above_zero mh fp fuel)
      (ensures
        (match MH.read_word_in_major mh (hd_address (fp <: obj_addr)) with
         | Some hdr -> major_fl_head_wosize mh fp == U64.v (Obj.getWosize hdr)
         | None -> False))
  =
  major_fl_above_zero_current mh fp fuel;
  major_fl_valid_gives_wosize mh fp fuel

let major_fl_head_block_fits_current (mh: MH.major_heap) (fp: U64.t)
                                    (fuel: nat)
  : Lemma
      (requires fuel > 0 /\
               fp <> 0UL /\
               major_fl_above_zero mh fp fuel /\
               major_fl_blocks_fit mh fp fuel)
      (ensures
        (let obj : obj_addr = fp in
         let base = hd_address obj in
         let idx = MH.lookup_chunk_index_value mh base in
         MH.lookup_chunk_index mh base == Some idx /\
         idx < Seq.length mh /\
         MH.word_in_chunk (Seq.index mh idx) base /\
         (match MH.read_word_in_major mh base with
          | Some hdr ->
           U64.v base + (1 + U64.v (Obj.getWosize hdr)) * U64.v mword <=
             MH.chunk_end (Seq.index mh idx)
          | None -> False)))
  =
  major_fl_above_zero_current mh fp fuel;
  major_fl_blocks_fit_current mh fp fuel

let expand_major_heap_head_wosize (mh: MH.major_heap) (c: MH.heap_chunk)
                                  (next_fp: U64.t)
  : Lemma
      (requires U64.v c.base >= U64.v zero_addr)
      (ensures
        (let r = expand_major_heap mh c next_fp in
         major_fl_head_wosize r.major_out r.fp_out == fresh_chunk_wosize c))
  =
  fresh_chunk_object_in_chunk c;
  expand_major_heap_header_fields mh c next_fp;
  f_address_spec c.base;
  let r = expand_major_heap mh c next_fp in
  let fp = r.fp_out in
  assert (fp == fresh_chunk_object c);
  assert (U64.v fp == U64.v c.base + U64.v mword);
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  assert (U64.v fp < heap_size);
  assert (U64.v fp % U64.v mword == 0);
  assert (U64.v c.base + U64.v mword < heap_size);
  hd_f_roundtrip c.base;
  assert (hd_address fp == c.base);
  expand_major_heap_header mh c next_fp;
  assert (MH.read_word_in_major r.major_out (hd_address fp) ==
          Some (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL));
  AllocHeader.make_header_getWosize
    (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL;
  assert (Obj.getWosize
            (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL) ==
          fresh_chunk_wosize_u64 c);
  assert (U64.v (fresh_chunk_wosize_u64 c) == fresh_chunk_wosize c)

let major_alloc_demand_wosize (requested_wz: nat) : n:nat{n > 0} =
  Alloc.normalized_wosize requested_wz

let rec major_fl_capacity (mh: MH.major_heap) (fp: U64.t) (fuel: nat) : Tot nat
  (decreases fuel)
  = if fuel = 0 then 0
    else
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      if fp = 0UL then 0
      else if U64.v fp < U64.v mword || U64.v fp >= heap_size ||
              U64.v fp % U64.v mword <> 0 then 0
      else
        let obj : obj_addr = fp in
        match MH.read_word_in_major mh (hd_address obj), MH.read_word_in_major mh obj with
        | Some hdr, Some next ->
          U64.v (Obj.getWosize hdr) + major_fl_capacity mh next fuel'
        | _, _ -> 0

let major_fl_capacity_zero (mh: MH.major_heap) (fp: U64.t)
  : Lemma (major_fl_capacity mh fp 0 == 0)
  = ()

let major_fl_capacity_null (mh: MH.major_heap) (fuel: nat)
  : Lemma (requires fuel > 0)
          (ensures major_fl_capacity mh 0UL fuel == 0)
  = ()

#push-options "--z3rlimit 10"
let rec expand_major_heap_preserves_fl_capacity (mh: MH.major_heap) (c: MH.heap_chunk)
                                                (new_link: U64.t) (fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_valid mh fp fuel)
          (ensures major_fl_capacity (expand_major_heap mh c new_link).major_out fp fuel ==
                   major_fl_capacity mh fp fuel)
          (decreases fuel)
  = if fuel > 0 then begin
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      if fp = 0UL then ()
      else if U64.v fp < U64.v mword || U64.v fp >= heap_size ||
              U64.v fp % U64.v mword <> 0 then
        assert False
      else begin
        let obj : obj_addr = fp in
        let r = init_fresh_chunk c new_link in
        init_fresh_chunk_disjoint_from_all mh c new_link;
        match MH.read_word_in_major mh (hd_address obj) with
        | None -> assert False
        | Some hdr ->
          MH.read_word_add_chunk_disjoint_old mh r.chunk_out (hd_address obj) hdr;
          assert (MH.read_word_in_major (expand_major_heap mh c new_link).major_out (hd_address obj) ==
                  Some hdr);
        match MH.read_word_in_major mh obj with
        | None -> assert False
        | Some next ->
          major_fl_valid_next mh fp fuel;
          expand_major_heap_preserves_fl_capacity mh c new_link next fuel';
          MH.read_word_add_chunk_disjoint_old mh r.chunk_out obj next;
          assert (MH.read_word_in_major (expand_major_heap mh c new_link).major_out obj ==
                  Some next)
      end
    end
    else ()

let expand_major_heap_fresh_capacity (mh: MH.major_heap) (c: MH.heap_chunk)
                                     (next_fp: U64.t) (fuel: nat)
  : Lemma (major_fl_capacity (expand_major_heap mh c next_fp).major_out
             (fresh_chunk_object c) (fuel + 1) ==
           fresh_chunk_wosize c +
           major_fl_capacity (expand_major_heap mh c next_fp).major_out next_fp fuel)
  = fresh_chunk_object_in_chunk c;
    let er = expand_major_heap mh c next_fp in
    let fp = fresh_chunk_object c in
    expand_major_heap_header mh c next_fp;
    expand_major_heap_header_fields mh c next_fp;
    expand_major_heap_link mh c next_fp;
    f_address_spec c.base;
    assert (U64.v fp >= U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    assert (U64.v c.base + U64.v mword < heap_size);
    hd_f_roundtrip c.base;
    assert (hd_address fp == c.base);
    assert (MH.read_word_in_major er.major_out (hd_address fp) ==
            Some (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL));
    assert (Obj.getWosize (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL) ==
            fresh_chunk_wosize_u64 c);
    assert (U64.v (fresh_chunk_wosize_u64 c) == fresh_chunk_wosize c);
    assert (MH.read_word_in_major er.major_out fp == Some next_fp)

let expand_major_heap_links_fl_capacity (mh: MH.major_heap) (c: MH.heap_chunk)
                                        (next_fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_valid mh next_fp fuel)
          (ensures major_fl_capacity (expand_major_heap mh c next_fp).major_out
                     (fresh_chunk_object c) (fuel + 1) ==
                   fresh_chunk_wosize c + major_fl_capacity mh next_fp fuel)
  = expand_major_heap_preserves_fl_capacity mh c next_fp next_fp fuel;
    expand_major_heap_fresh_capacity mh c next_fp fuel
#pop-options

#push-options "--z3rlimit 10"
let rec expand_major_heap_preserves_fl_valid (mh: MH.major_heap) (c: MH.heap_chunk)
                                             (new_link: U64.t) (fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_valid mh fp fuel)
          (ensures major_fl_valid (expand_major_heap mh c new_link).major_out fp fuel)
          (decreases fuel)
  = if fuel > 0 then begin
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
    else ()
#pop-options

#push-options "--z3rlimit 10"
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

#push-options "--z3rlimit 10"
let rec expand_major_heap_preserves_fl_above_zero (mh: MH.major_heap) (c: MH.heap_chunk)
                                                 (new_link: U64.t) (fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_valid mh fp fuel /\
                    major_fl_above_zero mh fp fuel)
          (ensures major_fl_above_zero
                    (expand_major_heap mh c new_link).major_out fp fuel)
          (decreases fuel)
  = if fuel > 0 then begin
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      if fp = 0UL then ()
      else if U64.v fp < U64.v zero_addr + U64.v mword ||
              U64.v fp >= heap_size ||
              U64.v fp % U64.v mword <> 0 then
        assert False
      else begin
        let obj : obj_addr = fp in
        let r = init_fresh_chunk c new_link in
        init_fresh_chunk_disjoint_from_all mh c new_link;
        match MH.read_word_in_major mh obj with
        | None -> assert False
        | Some next ->
          major_fl_valid_next mh fp fuel;
          expand_major_heap_preserves_fl_above_zero mh c new_link next fuel';
          MH.read_word_add_chunk_disjoint_old mh r.chunk_out obj next;
          assert (MH.read_word_in_major
                    (expand_major_heap mh c new_link).major_out obj ==
                  Some next)
      end
    end
    else ()
#pop-options

let expand_major_heap_fresh_fl_above_zero (mh: MH.major_heap) (c: MH.heap_chunk)
                                         (next_fp: U64.t) (fuel: nat)
  : Lemma (requires U64.v c.base >= U64.v zero_addr /\
                    major_fl_above_zero
                      (expand_major_heap mh c next_fp).major_out next_fp fuel)
          (ensures major_fl_above_zero
                    (expand_major_heap mh c next_fp).major_out
                    (fresh_chunk_object c) (fuel + 1))
  = fresh_chunk_object_in_chunk c;
    let er = expand_major_heap mh c next_fp in
    let fp = fresh_chunk_object c in
    expand_major_heap_link mh c next_fp;
    f_address_spec c.base;
    assert (U64.v fp == U64.v c.base + U64.v mword);
    assert (U64.v fp >= U64.v zero_addr + U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    assert (MH.read_word_in_major er.major_out fp == Some next_fp)

let expand_major_heap_links_fl_above_zero (mh: MH.major_heap) (c: MH.heap_chunk)
                                         (next_fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_valid mh next_fp fuel /\
                    major_fl_above_zero mh next_fp fuel /\
                    U64.v c.base >= U64.v zero_addr)
          (ensures major_fl_above_zero
                    (expand_major_heap mh c next_fp).major_out
                    (fresh_chunk_object c) (fuel + 1))
  = expand_major_heap_preserves_fl_above_zero mh c next_fp next_fp fuel;
    expand_major_heap_fresh_fl_above_zero mh c next_fp fuel

#push-options "--z3rlimit 10 --split_queries always"
let rec expand_major_heap_preserves_fl_blocks_fit
  (mh: MH.major_heap) (c: MH.heap_chunk)
  (new_link: U64.t) (fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_blocks_fit mh fp fuel)
          (ensures major_fl_blocks_fit
                    (expand_major_heap mh c new_link).major_out fp fuel)
          (decreases fuel)
  = if fuel > 0 then begin
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      if fp = 0UL then ()
      else if U64.v fp < U64.v mword || U64.v fp >= heap_size ||
              U64.v fp % U64.v mword <> 0 then
        assert False
      else begin
        let obj : obj_addr = fp in
        let base = hd_address obj in
        let r = init_fresh_chunk c new_link in
        init_fresh_chunk_disjoint_from_all mh c new_link;
        major_fl_blocks_fit_current mh fp fuel;
        let idx = MH.lookup_chunk_index_value mh base in
        MH.lookup_chunk_index_some mh base idx;
        MH.lookup_chunk_some_disjoint_miss mh (Seq.index mh idx) r.chunk_out base;
        assert (~(MH.chunk_contains_addr r.chunk_out base));
        MH.lookup_chunk_index_add_chunk_miss mh r.chunk_out base idx;
        match MH.read_word_in_major mh base with
        | None -> assert False
        | Some hdr ->
          MH.read_word_add_chunk_disjoint_old mh r.chunk_out base hdr;
          assert (MH.read_word_in_major
                    (expand_major_heap mh c new_link).major_out base ==
                  Some hdr);
        match MH.read_word_in_major mh obj with
        | None -> assert False
        | Some next ->
          expand_major_heap_preserves_fl_blocks_fit mh c new_link next fuel';
          MH.read_word_add_chunk_disjoint_old mh r.chunk_out obj next;
          assert (MH.read_word_in_major
                    (expand_major_heap mh c new_link).major_out obj ==
                  Some next)
      end
    end
    else ()
#pop-options

#push-options "--z3rlimit 10"
let expand_major_heap_fresh_fl_blocks_fit
  (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t) (fuel: nat)
  : Lemma
      (requires major_fl_blocks_fit
                  (expand_major_heap mh c next_fp).major_out next_fp fuel)
      (ensures major_fl_blocks_fit
                (expand_major_heap mh c next_fp).major_out
                (fresh_chunk_object c) (fuel + 1))
  = fresh_chunk_object_in_chunk c;
    fresh_chunk_wosize_nonzero c;
    fresh_chunk_wosize_fits c;
    chunk_size_capacity_mul c;
    let er = expand_major_heap mh c next_fp in
    let fp = fresh_chunk_object c in
    expand_major_heap_fresh_object mh c next_fp;
    expand_major_heap_header mh c next_fp;
    expand_major_heap_header_fields mh c next_fp;
    expand_major_heap_link mh c next_fp;
    init_fresh_chunk_preserves_range c next_fp;
    f_address_spec c.base;
    assert (U64.v fp >= U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    hd_f_roundtrip c.base;
    assert (hd_address fp == c.base);
    assert (Seq.head er.major_out == er.major_out `Seq.index` 0);
    assert (MH.word_in_chunk (Seq.index er.major_out 0) c.base);
    assert (MH.lookup_chunk_index er.major_out c.base == Some 0);
    assert (MH.lookup_chunk_index_value er.major_out c.base == 0);
    assert (MH.read_word_in_major er.major_out c.base ==
            Some (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL));
    assert (Obj.getWosize
              (Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL) ==
            fresh_chunk_wosize_u64 c);
    assert (U64.v (fresh_chunk_wosize_u64 c) == fresh_chunk_wosize c);
    assert (fresh_chunk_wosize c == chunk_word_capacity c - 1);
    assert (chunk_word_capacity c >= 2);
    assert ((1 + U64.v (fresh_chunk_wosize_u64 c)) == chunk_word_capacity c);
    assert (c.size == chunk_word_capacity c * U64.v mword);
    assert (U64.v c.base +
            (1 + U64.v (fresh_chunk_wosize_u64 c)) * U64.v mword <=
            MH.chunk_end (Seq.index er.major_out 0));
    assert (MH.read_word_in_major er.major_out fp == Some next_fp)
#pop-options

let expand_major_heap_links_fl_blocks_fit
  (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t) (fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all c mh /\
                    major_fl_blocks_fit mh next_fp fuel)
          (ensures major_fl_blocks_fit
                    (expand_major_heap mh c next_fp).major_out
                    (fresh_chunk_object c) (fuel + 1))
  = expand_major_heap_preserves_fl_blocks_fit mh c next_fp next_fp fuel;
    expand_major_heap_fresh_fl_blocks_fit mh c next_fp fuel

type ensure_capacity_result = {
  capacity_major_out: MH.major_heap;
  capacity_fp_out: obj_addr;
  capacity_fuel_out: nat;
}

let ensure_major_capacity_spec (mh: MH.major_heap) (fp: obj_addr)
                               (fuel needed: nat) (fresh: MH.heap_chunk)
  : GTot ensure_capacity_result =
  if major_fl_capacity mh fp fuel >= needed then
    { capacity_major_out = mh; capacity_fp_out = fp; capacity_fuel_out = fuel }
  else
    let er = expand_major_heap mh fresh fp in
    { capacity_major_out = er.major_out;
      capacity_fp_out = er.fp_out;
      capacity_fuel_out = fuel + 1 }

let ensure_major_capacity_has_capacity (mh: MH.major_heap) (fp: obj_addr)
                                       (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma (requires major_fl_valid mh fp fuel /\
                    (major_fl_capacity mh fp fuel < needed ==>
                     MH.chunk_disjoint_from_all fresh mh /\
                     fresh_chunk_wosize fresh + major_fl_capacity mh fp fuel >= needed))
          (ensures (let r = ensure_major_capacity_spec mh fp fuel needed fresh in
                    major_fl_capacity r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed))
  = if major_fl_capacity mh fp fuel >= needed then ()
    else begin
      expand_major_heap_links_fl_capacity mh fresh fp fuel;
      let r = ensure_major_capacity_spec mh fp fuel needed fresh in
      assert (major_fl_capacity r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out ==
              fresh_chunk_wosize fresh + major_fl_capacity mh fp fuel)
    end

let ensure_major_capacity_fl_valid (mh: MH.major_heap) (fp: obj_addr)
                                  (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma (requires major_fl_valid mh fp fuel /\
                    (major_fl_capacity mh fp fuel < needed ==>
                     MH.chunk_disjoint_from_all fresh mh /\
                     fp <> fresh_chunk_object fresh))
          (ensures (let r = ensure_major_capacity_spec mh fp fuel needed fresh in
                    major_fl_valid r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = if major_fl_capacity mh fp fuel >= needed then ()
    else
      expand_major_heap_links_fl_valid mh fresh fp fuel

let ensure_major_capacity_fl_above_zero (mh: MH.major_heap) (fp: obj_addr)
                                       (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma (requires major_fl_valid mh fp fuel /\
                    major_fl_above_zero mh fp fuel /\
                    (major_fl_capacity mh fp fuel < needed ==>
                     MH.chunk_disjoint_from_all fresh mh /\
                     U64.v fresh.base >= U64.v zero_addr))
          (ensures (let r = ensure_major_capacity_spec mh fp fuel needed fresh in
                    major_fl_above_zero
                      r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = if major_fl_capacity mh fp fuel >= needed then ()
    else
      expand_major_heap_links_fl_above_zero mh fresh fp fuel

let ensure_major_capacity_wf (mh: MH.major_heap) (fp: obj_addr)
                             (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma (requires MH.well_formed_major_heap mh /\
                    (major_fl_capacity mh fp fuel < needed ==>
                     MH.chunk_disjoint_from_all fresh mh))
          (ensures MH.well_formed_major_heap
                    (ensure_major_capacity_spec mh fp fuel needed fresh).capacity_major_out)
  = if major_fl_capacity mh fp fuel >= needed then ()
    else
      expand_major_heap_wf mh fresh fp

let ensure_major_capacity_fl_blocks_fit (mh: MH.major_heap) (fp: obj_addr)
                                        (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma (requires major_fl_blocks_fit mh fp fuel /\
                    (major_fl_capacity mh fp fuel < needed ==>
                     MH.chunk_disjoint_from_all fresh mh))
          (ensures (let r = ensure_major_capacity_spec mh fp fuel needed fresh in
                    major_fl_blocks_fit
                      r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = if major_fl_capacity mh fp fuel >= needed then ()
    else
      expand_major_heap_links_fl_blocks_fit mh fresh fp fuel

let ensure_major_capacity_preserves_old_read
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk) (addr: hp_addr)
  : Lemma
      (requires (major_fl_capacity mh fp fuel < needed ==>
                ~(MH.chunk_contains_addr fresh addr)))
      (ensures MH.read_word_in_major
                (ensure_major_capacity_spec
                  mh fp fuel needed fresh).capacity_major_out
                addr ==
              MH.read_word_in_major mh addr)
  = if major_fl_capacity mh fp fuel >= needed then ()
    else
      expand_major_heap_old_read mh fresh fp addr

let ensure_major_head_capacity_spec (mh: MH.major_heap) (fp: U64.t)
                                    (fuel: nat) (needed: nat{needed > 0})
                                    (fresh: MH.heap_chunk)
  : GTot ensure_capacity_result =
  if major_fl_head_wosize mh fp >= needed then begin
    assert (fp <> 0UL);
    assert (U64.v fp >= U64.v zero_addr + U64.v mword);
    assert (U64.v fp < heap_size);
    assert (U64.v fp % U64.v mword == 0);
    { capacity_major_out = mh; capacity_fp_out = fp; capacity_fuel_out = fuel }
  end
  else
    let er = expand_major_heap mh fresh fp in
    { capacity_major_out = er.major_out;
      capacity_fp_out = er.fp_out;
      capacity_fuel_out = fuel + 1 }

let ensure_major_head_capacity_has_head_wosize
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires
        (major_fl_head_wosize mh fp < needed ==>
         U64.v fresh.base >= U64.v zero_addr /\
         fresh_chunk_wosize fresh >= needed))
      (ensures
        (let r = ensure_major_head_capacity_spec mh fp fuel needed fresh in
         major_fl_head_wosize r.capacity_major_out r.capacity_fp_out >= needed))
  = if major_fl_head_wosize mh fp >= needed then ()
    else
      expand_major_heap_head_wosize mh fresh fp

let ensure_major_head_capacity_fl_valid
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires major_fl_valid mh fp fuel /\
                (major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> fresh_chunk_object fresh))
      (ensures
        (let r = ensure_major_head_capacity_spec mh fp fuel needed fresh in
         major_fl_valid r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = if major_fl_head_wosize mh fp >= needed then ()
    else
      expand_major_heap_links_fl_valid mh fresh fp fuel

let ensure_major_head_capacity_fl_above_zero
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires major_fl_valid mh fp fuel /\
                major_fl_above_zero mh fp fuel /\
                (major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 U64.v fresh.base >= U64.v zero_addr))
      (ensures
        (let r = ensure_major_head_capacity_spec mh fp fuel needed fresh in
         major_fl_above_zero
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = if major_fl_head_wosize mh fp >= needed then ()
    else
      expand_major_heap_links_fl_above_zero mh fresh fp fuel

let ensure_major_head_capacity_fl_blocks_fit
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires major_fl_blocks_fit mh fp fuel /\
                (major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        (let r = ensure_major_head_capacity_spec mh fp fuel needed fresh in
         major_fl_blocks_fit
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = if major_fl_head_wosize mh fp >= needed then ()
    else
      expand_major_heap_links_fl_blocks_fit mh fresh fp fuel

let ensure_major_head_capacity_wf
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires MH.well_formed_major_heap mh /\
                (major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures MH.well_formed_major_heap
        (ensure_major_head_capacity_spec mh fp fuel needed fresh).capacity_major_out)
  = if major_fl_head_wosize mh fp >= needed then ()
    else
      expand_major_heap_wf mh fresh fp

let ensure_major_head_capacity_preserves_old_read
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk) (addr: hp_addr)
  : Lemma
      (requires
        (major_fl_head_wosize mh fp < needed ==>
         ~(MH.chunk_contains_addr fresh addr)))
      (ensures MH.read_word_in_major
                (ensure_major_head_capacity_spec
                  mh fp fuel needed fresh).capacity_major_out
                addr ==
              MH.read_word_in_major mh addr)
  = if major_fl_head_wosize mh fp >= needed then ()
    else
      expand_major_heap_old_read mh fresh fp addr

type major_alloc_result = {
  major_alloc_out: MH.major_heap;
  major_fp_out: U64.t;
  major_obj_out: U64.t;
}

let major_alloc_result_fp_in_objects (r: major_alloc_result) : Tot prop =
  exists (new_fp: obj_addr).
    new_fp == r.major_fp_out /\
    Seq.mem new_fp (MH.major_objects r.major_alloc_out)

let major_write_word_or_same (mh: MH.major_heap) (addr: hp_addr) (value: U64.t)
  : GTot MH.major_heap =
  match MH.write_word_in_major mh addr value with
  | Some mh' -> mh'
  | None -> mh

#push-options "--z3rlimit 10 --split_queries always"
let rec write_word_in_major_preserves_chunk_disjoint
  (fresh: MH.heap_chunk) (mh: MH.major_heap) (addr: hp_addr) (value: U64.t)
  : Lemma (requires MH.chunk_disjoint_from_all fresh mh)
          (ensures (match MH.write_word_in_major mh addr value with
                    | None -> True
                    | Some mh' -> MH.chunk_disjoint_from_all fresh mh'))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then ()
    else begin
      let hd = Seq.head mh in
      let tl = Seq.tail mh in
      assert (Seq.index mh 0 == hd);
      assert (Seq.equal mh (Seq.cons hd tl));
      Seq.lemma_eq_elim mh (Seq.cons hd tl);
      assert (MH.chunks_disjoint fresh hd);
      if MH.word_in_chunk hd addr then begin
        let hd' = MH.write_word_in_chunk hd addr value in
        MH.write_word_in_chunk_preserves_range hd addr value;
        MH.chunks_disjoint_same_range_right fresh hd hd';
        assert (MH.chunks_disjoint fresh hd');
        assert (MH.write_word_in_major mh addr value == Some (Seq.cons hd' tl));
        let out = Seq.cons hd' tl in
        assert (Seq.length out == Seq.length mh);
        let disj (i: nat{i < Seq.length out})
          : Lemma (MH.chunks_disjoint fresh (Seq.index out i))
          = if i > 0 then begin
              assert (i < Seq.length mh);
              assert (i - 1 < Seq.length tl);
              let im1 : n:nat{n < Seq.length tl} = i - 1 in
              assert (Seq.index out i == Seq.index tl im1);
              assert (Seq.index mh i == Seq.index tl im1);
              assert (MH.chunks_disjoint fresh (Seq.index mh i))
            end else begin
              assert (i == 0);
              assert (Seq.index out i == hd')
            end
        in
        FStar.Classical.forall_intro disj
      end else begin
        MH.chunk_disjoint_from_all_tail fresh mh;
        write_word_in_major_preserves_chunk_disjoint fresh tl addr value;
        match MH.write_word_in_major tl addr value with
        | None -> ()
        | Some tl' ->
          assert (MH.chunk_disjoint_from_all fresh tl');
          assert (MH.write_word_in_major mh addr value == Some (Seq.cons hd tl'));
          let out = Seq.cons hd tl' in
          let disj (i: nat{i < Seq.length out})
            : Lemma (MH.chunks_disjoint fresh (Seq.index out i))
            = if i > 0 then begin
                assert (i - 1 < Seq.length tl');
                let im1 : n:nat{n < Seq.length tl'} = i - 1 in
                assert (Seq.index out i == Seq.index tl' im1);
                assert (MH.chunks_disjoint fresh (Seq.index tl' im1))
              end else begin
                assert (i == 0);
                assert (Seq.index out i == hd)
              end
          in
          FStar.Classical.forall_intro disj
      end
    end

let major_write_word_or_same_preserves_chunk_disjoint
  (fresh: MH.heap_chunk) (mh: MH.major_heap) (addr: hp_addr) (value: U64.t)
  : Lemma (requires MH.chunk_disjoint_from_all fresh mh)
          (ensures MH.chunk_disjoint_from_all fresh
                    (major_write_word_or_same mh addr value))
  = write_word_in_major_preserves_chunk_disjoint fresh mh addr value;
    match MH.write_word_in_major mh addr value with
    | None -> ()
    | Some _ -> ()
#pop-options

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

#push-options "--split_queries always"
let major_write_word_or_same_single_chunk_compat (g: heap)
                                               (addr: hp_addr{U64.v addr >= U64.v zero_addr /\
                                                              U64.v addr + U64.v mword <= heap_size})
                                               (value: U64.t)
  : Lemma (major_write_word_or_same (MH.single_chunk_major_heap g) addr value ==
           MH.single_chunk_major_heap (write_word g addr value))
  = MH.single_chunk_write_word_compat g addr value;
    match MH.write_word_in_major (MH.single_chunk_major_heap g) addr value with
    | None -> assert False
    | Some mh' -> assert (mh' == MH.single_chunk_major_heap (write_word g addr value))
#pop-options

let major_spec_next_fp_single_chunk_compat (g: heap)
                                          (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma (major_spec_next_fp (MH.single_chunk_major_heap g) obj == Alloc.spec_next_fp g obj)
  = MH.single_chunk_read_word_compat g obj;
    Alloc.spec_next_fp_eq g obj;
    major_spec_next_fp_some (MH.single_chunk_major_heap g) obj (read_word g obj)

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

#push-options "--split_queries always"
let major_alloc_from_block_single_chunk_compat (g: heap)
                                             (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
                                             (wz: nat) (next: U64.t)
  : Lemma (requires (let hdr = read_word g (hd_address obj) in
                     U64.v (Obj.getWosize hdr) >= wz))
          (ensures major_alloc_from_block (MH.single_chunk_major_heap g) obj wz next ==
           (let (g', fp') = Alloc.alloc_from_block g obj wz next in
            (MH.single_chunk_major_heap g', fp')))
  = let mh = MH.single_chunk_major_heap g in
    let hd = hd_address obj in
    hd_address_spec obj;
    assert (U64.v hd >= U64.v zero_addr);
    hd_address_bounds obj;
    MH.single_chunk_read_word_compat g hd;
    let hdr = read_word g hd in
    assert (MH.read_word_in_major mh hd == Some hdr);
    let block_wz = U64.v (Obj.getWosize hdr) in
    let leftover = block_wz - wz in
    if block_wz < wz then begin
      assert False
    end else if leftover >= 2 then begin
      let alloc_hdr = Alloc.make_header (U64.uint_to_t wz) Alloc.white_bits 0UL in
      let g1 = write_word g hd alloc_hdr in
      major_write_word_or_same_single_chunk_compat g hd alloc_hdr;
      let mh1 = MH.single_chunk_major_heap g1 in
      assert (major_write_word_or_same mh hd alloc_hdr == mh1);
      let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
      aligned_plus_word_product (U64.v hd) (1 + wz);
      assert (rem_hd_nat % 8 == 0);
      if rem_hd_nat >= heap_size || rem_hd_nat >= pow2 64 ||
         rem_hd_nat % 8 <> 0 then begin
        assert (rem_hd_nat >= heap_size);
        Alloc.alloc_from_block_split_rem_hd_oob g obj wz next
      end else begin
        let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
        assert (U64.v rem_hd >= U64.v zero_addr);
        aligned_lt_heap_has_word_room rem_hd_nat;
        let rem_wz = leftover - 1 in
        let rem_hdr = Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
        let g2 = write_word g1 rem_hd rem_hdr in
        major_write_word_or_same_single_chunk_compat g1 rem_hd rem_hdr;
        let mh2 = MH.single_chunk_major_heap g2 in
        assert (major_write_word_or_same mh1 rem_hd rem_hdr == mh2);
        let rem_obj_nat = rem_hd_nat + 8 in
        FStar.Math.Lemmas.pow2_lt_compat 64 57;
        assert_norm (pow2 57 + 8 < pow2 64);
        assert (rem_obj_nat < pow2 64);
        sum_of_aligned_is_aligned rem_hd mword;
        assert (rem_obj_nat == U64.v rem_hd + U64.v mword);
        assert (rem_obj_nat % U64.v mword == 0);
        if rem_obj_nat >= heap_size || rem_obj_nat >= pow2 64 ||
           rem_obj_nat % 8 <> 0 then begin
          assert (rem_obj_nat >= heap_size);
          Alloc.alloc_from_block_split_rem_obj_oob g obj wz next
        end else begin
          let rem_field : hp_addr = U64.uint_to_t rem_obj_nat in
          assert (U64.v rem_field >= U64.v zero_addr);
          aligned_lt_heap_has_word_room rem_obj_nat;
          let g3 = write_word g2 rem_field next in
          major_write_word_or_same_single_chunk_compat g2 rem_field next;
          major_alloc_from_block_split_normal mh obj wz next hdr;
          Alloc.alloc_from_block_split_normal g obj wz next
        end
      end
    end else begin
      let alloc_hdr = Alloc.make_header (U64.uint_to_t block_wz) Alloc.white_bits 0UL in
      major_write_word_or_same_single_chunk_compat g hd alloc_hdr;
      major_alloc_from_block_exact mh obj wz next hdr;
      Alloc.alloc_from_block_exact g obj wz next
    end
#pop-options

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

let major_alloc_spec_with_fuel_head_no_oom
  (mh: MH.major_heap) (fp: U64.t) (requested_wz: nat) (fuel: nat)
  : Lemma
      (requires fuel > 0 /\
                fp <> 0UL /\
                major_fl_valid mh fp fuel /\
                major_fl_above_zero mh fp fuel /\
                major_fl_blocks_fit mh fp fuel /\
                major_fl_head_wosize mh fp >= Alloc.normalized_wosize requested_wz)
      (ensures
        (let r = major_alloc_spec_with_fuel mh fp requested_wz fuel in
         r.major_obj_out == fp /\ r.major_obj_out <> 0UL))
  =
  let wz = Alloc.normalized_wosize requested_wz in
  major_fl_above_zero_current mh fp fuel;
  major_fl_head_wosize_current mh fp fuel;
  major_fl_head_block_fits_current mh fp fuel;
  match MH.read_word_in_major mh (hd_address (fp <: obj_addr)) with
  | None -> assert False
  | Some hdr ->
    assert (major_fl_head_wosize mh fp == U64.v (Obj.getWosize hdr));
    assert (U64.v (Obj.getWosize hdr) >= wz);
    major_alloc_search_found_head mh fp 0UL fp wz fuel hdr;
    assert (major_alloc_spec_with_fuel mh fp requested_wz fuel ==
            major_alloc_search mh fp 0UL fp wz fuel)

let ensure_major_head_capacity_alloc_no_oom
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requested_wz: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 0 /\
                major_fl_valid mh fp fuel /\
                major_fl_above_zero mh fp fuel /\
                major_fl_blocks_fit mh fp fuel /\
                (major_fl_head_wosize mh fp <
                   major_alloc_demand_wosize requested_wz ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 fresh_chunk_wosize fresh >=
                   major_alloc_demand_wosize requested_wz))
      (ensures
        (let r =
           ensure_major_head_capacity_spec
             mh fp fuel (major_alloc_demand_wosize requested_wz) fresh in
         let a =
           major_alloc_spec_with_fuel
             r.capacity_major_out r.capacity_fp_out requested_wz
             r.capacity_fuel_out in
         a.major_obj_out == r.capacity_fp_out /\
         a.major_obj_out <> 0UL))
  =
  let needed = major_alloc_demand_wosize requested_wz in
  ensure_major_head_capacity_has_head_wosize mh fp fuel needed fresh;
  ensure_major_head_capacity_fl_valid mh fp fuel needed fresh;
  ensure_major_head_capacity_fl_above_zero mh fp fuel needed fresh;
  ensure_major_head_capacity_fl_blocks_fit mh fp fuel needed fresh;
  let r = ensure_major_head_capacity_spec mh fp fuel needed fresh in
  if major_fl_head_wosize mh fp >= needed then begin
    assert (r.capacity_major_out == mh);
    assert (r.capacity_fp_out == fp);
    assert (r.capacity_fuel_out == fuel);
    assert (fp <> 0UL);
    assert (U64.v fp >= U64.v mword);
    major_alloc_spec_with_fuel_head_no_oom
      r.capacity_major_out r.capacity_fp_out requested_wz r.capacity_fuel_out
  end else begin
    let er = expand_major_heap mh fresh fp in
    assert (r.capacity_major_out == er.major_out);
    assert (r.capacity_fp_out == er.fp_out);
    assert (r.capacity_fuel_out == fuel + 1);
    fresh_chunk_object_in_chunk fresh;
    f_address_spec fresh.base;
    assert (U64.v r.capacity_fp_out == U64.v fresh.base + U64.v mword);
    assert (U64.v r.capacity_fp_out >= U64.v mword);
    assert (r.capacity_fp_out <> 0UL);
    assert (r.capacity_fuel_out > 0);
    major_alloc_spec_with_fuel_head_no_oom
      r.capacity_major_out r.capacity_fp_out requested_wz r.capacity_fuel_out
  end

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

let major_alloc_search_found_prev_invalid (mh: MH.major_heap) (head prev cur: U64.t)
                                          (wz: nat) (fuel: nat) (hdr: U64.t)
  : Lemma (requires fuel > 0 /\
                    U64.v cur >= U64.v zero_addr + U64.v mword /\
                    U64.v cur < heap_size /\
                    U64.v cur % U64.v mword = 0 /\
                    prev <> 0UL /\
                    ~(U64.v prev >= U64.v mword /\
                      U64.v prev < heap_size /\
                      U64.v prev % U64.v mword = 0) /\
                    MH.read_word_in_major mh (hd_address (cur <: obj_addr)) == Some hdr /\
                    U64.v (Obj.getWosize hdr) >= wz)
          (ensures (let obj : obj_addr = cur in
                    let next = major_spec_next_fp mh obj in
                    let (mh', new_fp) = major_alloc_from_block mh obj wz next in
                    major_alloc_search mh head prev cur wz fuel ==
                    { major_alloc_out = mh'; major_fp_out = new_fp; major_obj_out = cur }))
  = ()

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let rec major_alloc_search_oom_unchanged (mh: MH.major_heap)
                                        (head prev cur: U64.t)
                                        (wz fuel: nat)
  : Lemma (requires (major_alloc_search mh head prev cur wz fuel).major_obj_out == 0UL)
          (ensures (major_alloc_search mh head prev cur wz fuel).major_alloc_out == mh)
          (decreases fuel)
  = if fuel > 0 then begin
      if U64.v cur < U64.v zero_addr + U64.v mword ||
         U64.v cur >= heap_size ||
         U64.v cur % U64.v mword <> 0 then
        major_alloc_search_invalid mh head prev cur wz fuel
      else begin
        let fuel' : f:nat{f < fuel} = fuel - 1 in
        let obj : obj_addr = cur in
        let hd = hd_address obj in
        match MH.read_word_in_major mh hd with
        | None ->
          major_alloc_search_missing_header mh head prev cur wz fuel
        | Some hdr ->
          let block_wz = U64.v (Obj.getWosize hdr) in
          if block_wz < wz then begin
            major_alloc_search_advance mh head prev cur wz fuel hdr;
            major_alloc_search_oom_unchanged
              mh head cur (major_spec_next_fp mh obj) wz fuel'
          end else begin
            zero_addr_above_2048 ();
            assert (U64.v mword == 8);
            assert (U64.v cur > 0);
            assert (cur <> 0UL);
            if prev = 0UL then
              major_alloc_search_found_head mh head prev cur wz fuel hdr
            else if U64.v prev >= U64.v mword &&
                    U64.v prev < heap_size &&
                    U64.v prev % U64.v mword = 0 then
              major_alloc_search_found_prev mh head prev cur wz fuel hdr
            else
              major_alloc_search_found_prev_invalid mh head prev cur wz fuel hdr;
            assert False
          end
      end
    end else
      major_alloc_search_fuel_0 mh head prev cur wz

let major_alloc_spec_with_fuel_oom_unchanged (mh: MH.major_heap)
                                            (fp: U64.t)
                                            (requested_wz fuel: nat)
  : Lemma (requires (major_alloc_spec_with_fuel mh fp requested_wz fuel).major_obj_out == 0UL)
          (ensures (major_alloc_spec_with_fuel mh fp requested_wz fuel).major_alloc_out == mh)
  = major_alloc_search_oom_unchanged
      mh fp 0UL fp (Alloc.normalized_wosize requested_wz) fuel
#pop-options

let major_result_of_alloc_result (r: Alloc.alloc_result) : major_alloc_result =
  { major_alloc_out = MH.single_chunk_major_heap r.heap_out;
    major_fp_out = r.fp_out;
    major_obj_out = r.obj_out }

#push-options "--split_queries always"
let rec major_alloc_search_single_chunk_compat (g: heap) (head prev cur: U64.t)
                                              (wz: nat) (fuel: nat)
  : Lemma (requires prev = 0UL \/
                    (U64.v prev >= U64.v zero_addr + U64.v mword /\
                    U64.v prev < heap_size /\
                    U64.v prev % U64.v mword = 0))
          (ensures major_alloc_search (MH.single_chunk_major_heap g) head prev cur wz fuel ==
                   major_result_of_alloc_result (Alloc.alloc_search g head prev cur wz fuel))
          (decreases fuel)
  = let mh = MH.single_chunk_major_heap g in
    if fuel = 0 then begin
      major_alloc_search_fuel_0 mh head prev cur wz;
      Alloc.alloc_search_fuel_0 g head prev cur wz
    end else if U64.v cur < U64.v zero_addr + U64.v mword ||
                U64.v cur >= heap_size ||
                U64.v cur % U64.v mword <> 0 then begin
      major_alloc_search_invalid mh head prev cur wz fuel;
      Alloc.alloc_search_invalid g head prev cur wz fuel
    end else begin
      let fuel' : f:nat{f < fuel} = fuel - 1 in
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      hd_address_spec obj;
      assert (U64.v hd >= U64.v zero_addr);
      hd_address_bounds obj;
      MH.single_chunk_read_word_compat g hd;
      let hdr = read_word g hd in
      assert (MH.read_word_in_major mh hd == Some hdr);
      let block_wz = U64.v (Obj.getWosize hdr) in
      if block_wz < wz then begin
        major_alloc_search_advance mh head prev cur wz fuel hdr;
        Alloc.alloc_search_advance g head prev cur wz fuel;
        major_spec_next_fp_single_chunk_compat g obj;
        major_alloc_search_single_chunk_compat g head cur (Alloc.spec_next_fp g obj) wz fuel'
      end else if prev = 0UL then begin
        major_alloc_search_found_head mh head prev cur wz fuel hdr;
        Alloc.alloc_search_found_head g head prev cur wz fuel;
        major_spec_next_fp_single_chunk_compat g obj;
        major_alloc_from_block_single_chunk_compat g obj wz (Alloc.spec_next_fp g obj)
      end else begin
        assert (U64.v prev >= U64.v zero_addr + U64.v mword);
        assert (U64.v prev < heap_size);
        assert (U64.v prev % U64.v mword == 0);
        assert (U64.v prev >= U64.v mword);
        major_alloc_search_found_prev mh head prev cur wz fuel hdr;
        Alloc.alloc_search_found_prev g head prev cur wz fuel;
        major_spec_next_fp_single_chunk_compat g obj;
        major_alloc_from_block_single_chunk_compat g obj wz (Alloc.spec_next_fp g obj);
        let (g', new_fp) = Alloc.alloc_from_block g obj wz (Alloc.spec_next_fp g obj) in
        let prev_addr : hp_addr = prev in
        aligned_lt_heap_has_word_room (U64.v prev);
        major_write_word_or_same_single_chunk_compat g' prev_addr new_fp
      end
    end
#pop-options

let major_alloc_spec_with_fuel_single_chunk_compat (g: heap) (fp: U64.t)
                                                  (requested_wz fuel: nat)
  : Lemma (major_alloc_spec_with_fuel (MH.single_chunk_major_heap g) fp requested_wz fuel ==
           major_result_of_alloc_result (Alloc.alloc_spec_with_fuel g fp requested_wz fuel))
  = major_alloc_search_single_chunk_compat g fp 0UL fp (Alloc.normalized_wosize requested_wz) fuel

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_head_no_split (mh: MH.major_heap) (fp: obj_addr)
                              (requested_wz fuel: nat) (hdr next_fp: U64.t)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v zero_addr + U64.v mword /\
                    MH.read_word_in_major mh (hd_address fp) == Some hdr /\
                    MH.read_word_in_major mh fp == Some next_fp /\
                    U64.v (Obj.getWosize hdr) >= Alloc.normalized_wosize requested_wz /\
                    U64.v (Obj.getWosize hdr) - Alloc.normalized_wosize requested_wz < 2)
          (ensures (let alloc_hdr =
                      Alloc.make_header (Obj.getWosize hdr) Alloc.white_bits 0UL in
                    let out = major_write_word_or_same mh (hd_address fp) alloc_hdr in
                    let r = major_alloc_spec_with_fuel mh fp requested_wz fuel in
                    r.major_alloc_out == out /\
                    r.major_fp_out == next_fp /\
                    r.major_obj_out == fp))
  = let wz = Alloc.normalized_wosize requested_wz in
    major_spec_next_fp_some mh fp next_fp;
    assert (major_spec_next_fp mh fp == next_fp);
    major_alloc_from_block_exact mh fp wz next_fp hdr;
    major_alloc_search_found_head mh fp 0UL fp wz fuel hdr
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_head_split (mh: MH.major_heap) (fp: obj_addr)
                           (requested_wz fuel: nat) (hdr next_fp: U64.t)
                           (rem_hd rem_obj: hp_addr)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v zero_addr + U64.v mword /\
                    requested_wz > 0 /\
                    MH.read_word_in_major mh (hd_address fp) == Some hdr /\
                    MH.read_word_in_major mh fp == Some next_fp /\
                    U64.v (Obj.getWosize hdr) >= requested_wz /\
                    U64.v (Obj.getWosize hdr) - requested_wz >= 2 /\
                    U64.v rem_hd == U64.v (hd_address fp) + (1 + requested_wz) * 8 /\
                    U64.v rem_obj == U64.v rem_hd + U64.v mword)
          (ensures (let alloc_hdr =
                      Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
                    let mh1 = major_write_word_or_same mh (hd_address fp) alloc_hdr in
                    let rem_wz = U64.v (Obj.getWosize hdr) - requested_wz - 1 in
                    let rem_hdr =
                      Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
                    let mh2 = major_write_word_or_same mh1 rem_hd rem_hdr in
                    let mh3 = major_write_word_or_same mh2 rem_obj next_fp in
                    let r = major_alloc_spec_with_fuel mh fp requested_wz fuel in
                    r.major_alloc_out == mh3 /\
                    r.major_fp_out == rem_obj /\
                    r.major_obj_out == fp))
  = let wz = requested_wz in
    let hd = hd_address fp in
    major_spec_next_fp_some mh fp next_fp;
    assert (major_spec_next_fp mh fp == next_fp);
    assert (Alloc.normalized_wosize requested_wz == requested_wz);
    assert (U64.v rem_hd < heap_size);
    assert (U64.v rem_hd % U64.v mword == 0);
    assert (U64.v rem_obj < heap_size);
    assert (U64.v rem_obj % U64.v mword == 0);
    assert (U64.v mword == 8);
    assert (U64.v hd + (1 + wz) * 8 < heap_size);
    assert (U64.v hd + (1 + wz) * 8 + 8 < heap_size);
    assert ((U64.v hd + (1 + wz) * 8) % 8 == 0);
    assert ((U64.v hd + (1 + wz) * 8 + 8) % 8 == 0);
    major_alloc_from_block_split_normal mh fp wz next_fp hdr;
    assert (U64.v rem_obj == U64.v hd + (1 + wz) * 8 + 8);
    assert (U64.uint_to_t (U64.v hd + (1 + wz) * 8 + 8) == rem_obj);
    major_alloc_search_found_head mh fp 0UL fp wz fuel hdr
#pop-options

#push-options "--z3rlimit 10 --split_queries always"
let major_alloc_from_block_preserves_chunk_disjoint
  (fresh: MH.heap_chunk) (mh: MH.major_heap) (obj: obj_addr)
  (requested_wz: nat) (next_fp: U64.t)
  : Lemma (requires MH.chunk_disjoint_from_all fresh mh)
          (ensures MH.chunk_disjoint_from_all fresh
                    (fst (major_alloc_from_block mh obj requested_wz next_fp)))
  = let hd = hd_address obj in
    match MH.read_word_in_major mh hd with
    | None -> ()
    | Some hdr ->
      let block_wz = U64.v (Obj.getWosize hdr) in
      let leftover = block_wz - requested_wz in
      if block_wz < requested_wz then ()
      else if leftover >= 2 then begin
        let alloc_hdr =
          Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
        let mh1 = major_write_word_or_same mh hd alloc_hdr in
        major_write_word_or_same_preserves_chunk_disjoint fresh mh hd alloc_hdr;
        let rem_hd_nat = U64.v hd + (1 + requested_wz) * 8 in
        if rem_hd_nat >= heap_size || rem_hd_nat >= pow2 64 ||
           rem_hd_nat % 8 <> 0 then ()
        else begin
          let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
          let rem_wz = leftover - 1 in
          let rem_hdr =
            Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
          let mh2 = major_write_word_or_same mh1 rem_hd rem_hdr in
          major_write_word_or_same_preserves_chunk_disjoint fresh mh1 rem_hd rem_hdr;
          let rem_obj_nat = rem_hd_nat + 8 in
          FStar.Math.Lemmas.pow2_lt_compat 64 57;
          assert_norm (pow2 57 + 8 < pow2 64);
          assert (rem_obj_nat < pow2 64);
          if rem_obj_nat >= heap_size || rem_obj_nat >= pow2 64 ||
             rem_obj_nat % 8 <> 0 then ()
          else begin
            let rem_field : hp_addr = U64.uint_to_t rem_obj_nat in
            major_write_word_or_same_preserves_chunk_disjoint
              fresh mh2 rem_field next_fp
          end
        end
      end else begin
        let alloc_hdr =
          Alloc.make_header (U64.uint_to_t block_wz) Alloc.white_bits 0UL in
        major_write_word_or_same_preserves_chunk_disjoint fresh mh hd alloc_hdr
      end
#pop-options

#push-options "--z3rlimit 10 --split_queries always"
let rec major_alloc_search_preserves_chunk_disjoint
  (fresh: MH.heap_chunk) (mh: MH.major_heap)
  (head prev cur: U64.t) (wz fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all fresh mh)
          (ensures MH.chunk_disjoint_from_all fresh
                    (major_alloc_search mh head prev cur wz fuel).major_alloc_out)
          (decreases fuel)
  = if fuel > 0 then begin
      if U64.v cur < U64.v zero_addr + U64.v mword ||
         U64.v cur >= heap_size ||
         U64.v cur % U64.v mword <> 0 then ()
      else begin
        let fuel' : f:nat{f < fuel} = fuel - 1 in
        let obj : obj_addr = cur in
        let hd = hd_address obj in
        match MH.read_word_in_major mh hd with
        | None -> ()
        | Some hdr ->
          let block_wz = U64.v (Obj.getWosize hdr) in
          let next_fp = major_spec_next_fp mh obj in
          if block_wz >= wz then begin
            let (mh', new_remainder_fp) =
              major_alloc_from_block mh obj wz next_fp in
            major_alloc_from_block_preserves_chunk_disjoint
              fresh mh obj wz next_fp;
            if prev = 0UL then ()
            else if U64.v prev >= U64.v mword &&
                    U64.v prev < heap_size &&
                    U64.v prev % U64.v mword = 0 then begin
              let prev_addr : hp_addr = prev in
              major_write_word_or_same_preserves_chunk_disjoint
                fresh mh' prev_addr new_remainder_fp
            end else ()
          end else
            major_alloc_search_preserves_chunk_disjoint
              fresh mh head cur next_fp wz fuel'
      end
    end else ()

let major_alloc_spec_with_fuel_preserves_chunk_disjoint
  (fresh: MH.heap_chunk) (mh: MH.major_heap)
  (fp: U64.t) (requested_wz fuel: nat)
  : Lemma (requires MH.chunk_disjoint_from_all fresh mh)
          (ensures MH.chunk_disjoint_from_all fresh
                    (major_alloc_spec_with_fuel
                      mh fp requested_wz fuel).major_alloc_out)
  = major_alloc_search_preserves_chunk_disjoint
      fresh mh fp 0UL fp (Alloc.normalized_wosize requested_wz) fuel
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let indexed_chunk_replace_same_range_preserves_word_no_prior
  (mh: MH.major_heap)
  (write_idx target_idx: nat)
  (replacement: MH.heap_chunk)
  (target_addr: hp_addr)
  : Lemma (requires write_idx < Seq.length mh /\
                    target_idx < Seq.length mh /\
                    MH.chunk_start replacement == MH.chunk_start (Seq.index mh write_idx) /\
                    MH.chunk_end replacement == MH.chunk_end (Seq.index mh write_idx) /\
                    MH.word_in_chunk (Seq.index mh target_idx) target_addr /\
                    (forall (k:nat). k < target_idx ==>
                      ~(MH.word_in_chunk (Seq.index mh k) target_addr)))
          (ensures (let mh' = Seq.upd mh write_idx replacement in
                    target_idx < Seq.length mh' /\
                    MH.word_in_chunk (Seq.index mh' target_idx) target_addr /\
                    (forall (k:nat). k < target_idx ==>
                      ~(MH.word_in_chunk (Seq.index mh' k) target_addr))))
  = let old = Seq.index mh write_idx in
    let mh' = Seq.upd mh write_idx replacement in
    assert (Seq.length mh' == Seq.length mh);
    if target_idx = write_idx then begin
      assert (Seq.index mh' target_idx == replacement);
      assert (Seq.index mh target_idx == old);
      assert (MH.word_in_chunk old target_addr);
      assert (MH.word_in_chunk replacement target_addr)
    end else
      assert (Seq.index mh' target_idx == Seq.index mh target_idx);
    let no_prior (k: nat{k < target_idx})
      : Lemma (~(MH.word_in_chunk (Seq.index mh' k) target_addr))
      = if k = write_idx then begin
          assert (Seq.index mh' k == replacement);
          if MH.word_in_chunk (Seq.index mh' k) target_addr then begin
            assert (MH.word_in_chunk replacement target_addr);
            assert (MH.word_in_chunk old target_addr);
            assert (Seq.index mh k == old);
            assert (MH.word_in_chunk (Seq.index mh k) target_addr);
            assert False
          end
        end else begin
          assert (Seq.index mh' k == Seq.index mh k);
          assert (~(MH.word_in_chunk (Seq.index mh k) target_addr))
        end
    in
    FStar.Classical.forall_intro no_prior
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let indexed_chunk_write_preserves_word_no_prior
  (mh: MH.major_heap)
  (write_idx target_idx: nat)
  (write_addr target_addr: hp_addr)
  (value: U64.t)
  : Lemma (requires write_idx < Seq.length mh /\
                    target_idx < Seq.length mh /\
                    MH.word_in_chunk (Seq.index mh write_idx) write_addr /\
                    MH.word_in_chunk (Seq.index mh target_idx) target_addr /\
                    (forall (k:nat). k < target_idx ==>
                      ~(MH.word_in_chunk (Seq.index mh k) target_addr)))
          (ensures (let c' =
                      MH.write_word_in_chunk
                        (Seq.index mh write_idx) write_addr value in
                    let mh' = Seq.upd mh write_idx c' in
                    target_idx < Seq.length mh' /\
                    MH.word_in_chunk (Seq.index mh' target_idx) target_addr /\
                    (forall (k:nat). k < target_idx ==>
                      ~(MH.word_in_chunk (Seq.index mh' k) target_addr))))
  = let c = Seq.index mh write_idx in
    let c' = MH.write_word_in_chunk c write_addr value in
    let mh' = Seq.upd mh write_idx c' in
    assert (Seq.length mh' == Seq.length mh);
    MH.write_word_in_chunk_preserves_range c write_addr value;
    if target_idx = write_idx then begin
      assert (Seq.index mh' target_idx == c');
      MH.write_word_in_chunk_preserves_word c write_addr value target_addr
    end else
      assert (Seq.index mh' target_idx == Seq.index mh target_idx);
    let no_prior (k: nat{k < target_idx})
      : Lemma (~(MH.word_in_chunk (Seq.index mh' k) target_addr))
      = if k = write_idx then begin
          assert (Seq.index mh' k == c');
          if MH.word_in_chunk (Seq.index mh' k) target_addr then begin
            assert (MH.word_in_chunk c' target_addr);
            assert (MH.chunk_start c' == MH.chunk_start c);
            assert (MH.chunk_end c' == MH.chunk_end c);
            assert (MH.word_in_chunk c target_addr);
            assert (MH.word_in_chunk (Seq.index mh k) target_addr);
            assert False
          end
        end else begin
          assert (Seq.index mh' k == Seq.index mh k);
          assert (~(MH.word_in_chunk (Seq.index mh k) target_addr))
        end
    in
    FStar.Classical.forall_intro no_prior
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let indexed_chunk_write_preserves_contains_no_prior
  (mh: MH.major_heap)
  (write_idx target_idx: nat)
  (write_addr target_addr: hp_addr)
  (value: U64.t)
  : Lemma (requires write_idx < Seq.length mh /\
                    target_idx < Seq.length mh /\
                    MH.word_in_chunk (Seq.index mh write_idx) write_addr /\
                    MH.chunk_contains_addr (Seq.index mh target_idx) target_addr /\
                    (forall (k:nat). k < target_idx ==>
                      ~(MH.chunk_contains_addr (Seq.index mh k) target_addr)))
          (ensures (let c' =
                      MH.write_word_in_chunk
                        (Seq.index mh write_idx) write_addr value in
                    let mh' = Seq.upd mh write_idx c' in
                    target_idx < Seq.length mh' /\
                    MH.chunk_contains_addr (Seq.index mh' target_idx) target_addr /\
                    (forall (k:nat). k < target_idx ==>
                      ~(MH.chunk_contains_addr (Seq.index mh' k) target_addr))))
  = let c = Seq.index mh write_idx in
    let c' = MH.write_word_in_chunk c write_addr value in
    let mh' = Seq.upd mh write_idx c' in
    assert (Seq.length mh' == Seq.length mh);
    MH.write_word_in_chunk_preserves_range c write_addr value;
    if target_idx = write_idx then begin
      assert (Seq.index mh' target_idx == c');
      assert (MH.chunk_start c' == MH.chunk_start c);
      assert (MH.chunk_end c' == MH.chunk_end c)
    end else
      assert (Seq.index mh' target_idx == Seq.index mh target_idx);
    let no_prior (k: nat{k < target_idx})
      : Lemma (~(MH.chunk_contains_addr (Seq.index mh' k) target_addr))
      = if k = write_idx then begin
          assert (Seq.index mh' k == c');
          if MH.chunk_contains_addr (Seq.index mh' k) target_addr then begin
            assert (MH.chunk_contains_addr c' target_addr);
            assert (MH.chunk_start c' == MH.chunk_start c);
            assert (MH.chunk_end c' == MH.chunk_end c);
            assert (MH.chunk_contains_addr c target_addr);
            assert (MH.chunk_contains_addr (Seq.index mh k) target_addr);
            assert False
          end
        end else begin
          assert (Seq.index mh' k == Seq.index mh k);
          assert (~(MH.chunk_contains_addr (Seq.index mh k) target_addr))
        end
    in
    FStar.Classical.forall_intro no_prior
#pop-options

#push-options "--z3rlimit 20 --split_queries always"
let rec chunks_pairwise_index_disjoint (mh: MH.major_heap) (i j: nat)
  : Lemma (requires MH.chunks_pairwise_disjoint mh /\
                    i < j /\ j < Seq.length mh)
          (ensures MH.chunks_disjoint (Seq.index mh i) (Seq.index mh j))
          (decreases Seq.length mh)
  = if Seq.length mh = 0 then
      assert False
    else if i = 0 then begin
      let tl = Seq.tail mh in
      let jm1 : n:nat{n < Seq.length tl} = j - 1 in
      assert (Seq.index mh 0 == Seq.head mh);
      assert (Seq.index mh j == Seq.index tl jm1);
      assert (forall (k:nat). k < Seq.length tl ==> MH.chunks_disjoint (Seq.head mh) (Seq.index tl k))
    end else begin
      let tl = Seq.tail mh in
      let im1 : n:nat{n < j - 1} = i - 1 in
      let jm1 : n:nat{n < Seq.length tl} = j - 1 in
      assert (Seq.index mh i == Seq.index tl im1);
      assert (Seq.index mh j == Seq.index tl jm1);
      assert (MH.chunks_pairwise_disjoint tl);
      chunks_pairwise_index_disjoint tl im1 jm1
    end
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let well_formed_no_prior_word_in_selected_chunk (mh: MH.major_heap)
                                                (idx: nat) (addr: hp_addr)
  : Lemma (requires MH.well_formed_major_heap mh /\
                    idx < Seq.length mh /\
                    MH.word_in_chunk (Seq.index mh idx) addr)
          (ensures forall (k:nat). k < idx ==> ~(MH.word_in_chunk (Seq.index mh k) addr))
  = let no_prior (k: nat{k < idx})
      : Lemma (~(MH.word_in_chunk (Seq.index mh k) addr))
      = chunks_pairwise_index_disjoint mh k idx;
        MH.chunks_disjoint_symmetric (Seq.index mh k) (Seq.index mh idx);
        if MH.word_in_chunk (Seq.index mh k) addr then begin
          assert (MH.chunk_contains_addr (Seq.index mh idx) addr);
          assert (MH.chunk_contains_addr (Seq.index mh k) addr);
          MH.chunks_disjoint_no_shared_addr (Seq.index mh idx) (Seq.index mh k) addr;
          assert False
        end
    in
    FStar.Classical.forall_intro no_prior
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let well_formed_no_prior_contains_selected_chunk (mh: MH.major_heap)
                                                 (idx: nat) (addr: hp_addr)
  : Lemma (requires MH.well_formed_major_heap mh /\
                    idx < Seq.length mh /\
                    MH.chunk_contains_addr (Seq.index mh idx) addr)
          (ensures forall (k:nat). k < idx ==>
                    ~(MH.chunk_contains_addr (Seq.index mh k) addr))
  = let no_prior (k: nat{k < idx})
      : Lemma (~(MH.chunk_contains_addr (Seq.index mh k) addr))
      = chunks_pairwise_index_disjoint mh k idx;
        MH.chunks_disjoint_symmetric (Seq.index mh k) (Seq.index mh idx);
        if MH.chunk_contains_addr (Seq.index mh k) addr then begin
          MH.chunks_disjoint_no_shared_addr (Seq.index mh idx) (Seq.index mh k) addr;
          assert False
        end
    in
    FStar.Classical.forall_intro no_prior
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let active_head_split_remainder_words_in_chunk (c: MH.heap_chunk)
                                               (base: hp_addr)
                                               (block_wz requested_wz: nat)
                                               (rem_hd rem_obj: hp_addr)
  : Lemma (requires MH.word_in_chunk c base /\
                    requested_wz > 0 /\
                    block_wz >= requested_wz /\
                    block_wz < pow2 54 /\
                    block_wz - requested_wz >= 2 /\
                    U64.v rem_hd == U64.v base + (1 + requested_wz) * 8 /\
                    U64.v rem_obj == U64.v rem_hd + U64.v mword /\
                    U64.v base + (1 + block_wz) * 8 <= MH.chunk_end c)
          (ensures MH.word_in_chunk c rem_hd /\
                   MH.word_in_chunk c rem_obj)
  = assert (U64.v mword == 8);
    let fw = block_wz in
    let wz = requested_wz in
    assert (wz + 2 <= fw);
    FStar.Math.Lemmas.distributivity_add_left (1 + wz) 1 8;
    assert ((1 + wz) * 8 + 8 == (wz + 2) * 8);
    FStar.Math.Lemmas.paren_add_right (U64.v base) ((1 + wz) * 8) 8;
    assert (U64.v rem_obj == U64.v base + (wz + 2) * 8);
    assert (U64.v base + (wz + 2) * 8 <= U64.v base + (1 + fw) * 8);
    assert (U64.v rem_obj <= U64.v base + (1 + fw) * 8);
    assert (U64.v rem_obj <= MH.chunk_end c);
    assert (U64.v rem_hd + U64.v mword == U64.v rem_obj);
    assert (U64.v rem_hd + U64.v mword <= MH.chunk_end c);
    assert (U64.v rem_hd >= MH.chunk_start c);
    assert (U64.v rem_obj >= MH.chunk_start c);
    assert (U64.v rem_obj + U64.v mword <= U64.v base + (1 + fw) * 8);
    assert (U64.v rem_obj + U64.v mword <= MH.chunk_end c)
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let object_member_header_at_or_after_start (c: MH.heap_chunk)
                                           (start: hp_addr)
                                           (obj: obj_addr)
  : Lemma (requires Seq.mem obj (MH.objects_in_chunk_from c start))
          (ensures U64.v start <= U64.v (hd_address obj))
  = MH.objects_in_chunk_from_addresses_gt_start c start obj;
    assert (U64.v start % U64.v mword == 0);
    assert (U64.v obj % U64.v mword == 0);
    MH.word_aligned_gt_at_least_mword (U64.v obj) (U64.v start);
    hd_address_spec obj;
    assert (U64.v obj >= U64.v start + U64.v mword);
    assert (U64.v (hd_address obj) == U64.v obj - U64.v mword)
#pop-options

#push-options "--z3rlimit 20 --split_queries always --fuel 3 --ifuel 1"
let rec objects_in_chunk_from_head_split_preserves_object
  (c: MH.heap_chunk) (start: hp_addr) (obj: obj_addr)
  (requested_wz block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t) (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires Seq.mem obj (MH.objects_in_chunk_from c start) /\
                requested_wz > 0 /\
                block_wz >= requested_wz /\
                block_wz < pow2 54 /\
                block_wz - requested_wz >= 2 /\
                U64.v rem_wz_u == block_wz - requested_wz - 1 /\
                U64.v rem_wz_u < pow2 54 /\
                MH.word_in_chunk c (hd_address obj) /\
                MH.word_in_chunk c rem_hd /\
                MH.word_in_chunk c rem_obj /\
                U64.v rem_hd == U64.v (hd_address obj) + (1 + requested_wz) * U64.v mword /\
                U64.v rem_obj == U64.v rem_hd + U64.v mword /\
                U64.v (hd_address obj) + (1 + block_wz) * U64.v mword <=
                  MH.chunk_end c)
       (ensures
         (let hd = hd_address obj in
          let alloc_hdr =
            Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
          let c1 = MH.write_word_in_chunk c hd alloc_hdr in
          let rem_hdr =
            Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
          let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
          let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
          Seq.mem obj (MH.objects_in_chunk_from c3 start)))
      (decreases MH.chunk_end c - U64.v start)
  =
  let hd = hd_address obj in
  let alloc_hdr =
    Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
  let c1 = MH.write_word_in_chunk c hd alloc_hdr in
  let rem_hdr =
    Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
  let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
  let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
  if U64.v start < MH.chunk_start c then
    assert False
  else if U64.v start + U64.v mword >= MH.chunk_end c then
    assert False
  else begin
    assert (MH.word_in_chunk c start);
    let header = MH.read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words = U64.v wz + 1 in
    let next_start_nat = U64.v start + obj_size_words * U64.v mword in
    if next_start_nat > MH.chunk_end c || next_start_nat >= pow2 64 then
      assert False
    else begin
      f_address_spec start;
      let first : obj_addr = f_address start in
      if first = obj then begin
        hd_f_roundtrip start;
        assert (hd == start);
        AllocHeader.make_header_getWosize
          (U64.uint_to_t requested_wz) Alloc.white_bits 0UL;
        assert (Obj.getWosize alloc_hdr == U64.uint_to_t requested_wz);
        assert (U64.v (Obj.getWosize alloc_hdr) == requested_wz);
        assert (U64.v start + (1 + requested_wz) * U64.v mword == U64.v rem_hd);
        assert (U64.v start + U64.v mword <= U64.v rem_hd);
        assert (U64.v start + U64.v mword <= U64.v rem_obj);
        MH.write_word_in_chunk_preserves_word c hd alloc_hdr rem_hd;
        MH.write_word_in_chunk_preserves_word c hd alloc_hdr rem_obj;
        MH.write_word_in_chunk_preserves_word c hd alloc_hdr start;
        MH.read_write_in_chunk_same c hd alloc_hdr;
        MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr start;
        MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr rem_obj;
        MH.read_write_in_chunk_different c1 rem_hd start rem_hdr;
        MH.write_word_in_chunk_preserves_word c2 rem_obj next_fp start;
        MH.read_write_in_chunk_different c2 rem_obj start next_fp;
        assert (MH.read_word_in_chunk c3 start == alloc_hdr);
        assert (U64.v rem_hd < MH.chunk_end c3);
        MH.objects_in_chunk_from_head_mem c3 start;
        assert (Seq.mem obj (MH.objects_in_chunk_from c3 start))
      end else begin
        let tail =
          if next_start_nat >= MH.chunk_end c then Seq.empty
          else begin
            assert (next_start_nat < heap_size);
            MH.next_object_start_aligned start obj_size_words;
            assert (next_start_nat % U64.v mword == 0);
            let next_start : hp_addr = U64.uint_to_t next_start_nat in
            MH.objects_in_chunk_from c next_start
          end
        in
        GC.Spec.Fields.mem_cons_lemma obj first tail;
        assert (Seq.mem obj tail);
        if next_start_nat >= MH.chunk_end c then
          assert False
        else begin
          assert (next_start_nat < heap_size);
          MH.next_object_start_aligned start obj_size_words;
          assert (next_start_nat % U64.v mword == 0);
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          assert (Seq.mem obj (MH.objects_in_chunk_from c next_start));
          object_member_header_at_or_after_start c next_start obj;
          assert (U64.v next_start <= U64.v hd);
          assert (U64.v start + U64.v mword <= U64.v next_start);
          assert (U64.v start + U64.v mword <= U64.v hd);
          assert (U64.v start + U64.v mword <= U64.v rem_hd);
          assert (U64.v start + U64.v mword <= U64.v rem_obj);
          MH.write_word_in_chunk_preserves_word c hd alloc_hdr start;
          MH.read_write_in_chunk_different c hd start alloc_hdr;
          MH.write_word_in_chunk_preserves_word c hd alloc_hdr rem_hd;
          MH.write_word_in_chunk_preserves_word c hd alloc_hdr rem_obj;
          MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr start;
          MH.read_write_in_chunk_different c1 rem_hd start rem_hdr;
          MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr rem_obj;
          MH.write_word_in_chunk_preserves_word c2 rem_obj next_fp start;
          MH.read_write_in_chunk_different c2 rem_obj start next_fp;
          assert (MH.read_word_in_chunk c3 start == header);
          objects_in_chunk_from_head_split_preserves_object
            c next_start obj requested_wz block_wz next_fp rem_wz_u rem_hd rem_obj;
          assert (Seq.mem obj (MH.objects_in_chunk_from c3 next_start));
          assert (MH.chunk_start c3 == MH.chunk_start c);
          assert (MH.chunk_end c3 == MH.chunk_end c);
          assert (U64.v start >= MH.chunk_start c3);
          assert (U64.v start + U64.v mword < MH.chunk_end c3);
          assert (MH.read_word_in_chunk c3 start == header);
          assert (Obj.getWosize (MH.read_word_in_chunk c3 start) == wz);
          assert (U64.v start +
                  (U64.v (Obj.getWosize (MH.read_word_in_chunk c3 start)) + 1) *
                    U64.v mword == next_start_nat);
          assert (next_start_nat < MH.chunk_end c3);
          assert (MH.objects_in_chunk_from c3 start ==
                  Seq.cons first (MH.objects_in_chunk_from c3 next_start));
          GC.Spec.Fields.mem_cons_lemma obj first (MH.objects_in_chunk_from c3 next_start);
          assert (Seq.mem obj (MH.objects_in_chunk_from c3 start))
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_head_split_preserves_head_wosize
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel remaining: nat)
  : Lemma
      (requires fuel > 0 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                remaining > 0 /\
                MH.well_formed_major_heap mh /\
                major_fl_valid mh fp fuel /\
                major_fl_above_zero mh fp fuel /\
                major_fl_blocks_fit mh fp fuel /\
                major_fl_head_wosize mh fp >= requested_wz + 1 + remaining)
      (ensures
        (let r = major_alloc_spec_with_fuel mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         major_alloc_result_fp_in_objects r /\
         major_fl_head_wosize r.major_alloc_out r.major_fp_out >= remaining))
  =
  major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  let obj : obj_addr = fp in
  let hd = hd_address obj in
  major_fl_head_wosize_current mh fp fuel;
  major_fl_head_block_fits_current mh fp fuel;
  major_fl_valid_link_lookup_index mh fp fuel;
  let idx = MH.lookup_chunk_index_value mh hd in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) hd);
  match MH.read_word_in_major mh hd with
  | None -> assert False
  | Some hdr ->
    let block_wz = U64.v (Obj.getWosize hdr) in
    assert (major_fl_head_wosize mh fp == block_wz);
    assert (block_wz < pow2 54);
    assert (block_wz >= requested_wz + 1 + remaining);
    assert (block_wz - requested_wz >= 2);
    match MH.read_word_in_major mh obj with
    | None -> assert False
    | Some next_fp ->
      let c = Seq.index mh idx in
      assert (U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c);
      assert (U64.v mword == 8);
      let rem_hd_nat = U64.v hd + (1 + requested_wz) * 8 in
      let rem_obj_nat = rem_hd_nat + U64.v mword in
      FStar.Math.Lemmas.distributivity_add_left (1 + requested_wz) 1 8;
      assert ((1 + requested_wz) * 8 + 8 == (requested_wz + 2) * 8);
      FStar.Math.Lemmas.paren_add_right (U64.v hd) ((1 + requested_wz) * 8) 8;
      assert (rem_obj_nat == U64.v hd + (requested_wz + 2) * 8);
      assert (requested_wz + 2 <= block_wz);
      assert (requested_wz + 3 <= 1 + block_wz);
      assert (rem_obj_nat + 8 == U64.v hd + (requested_wz + 3) * 8);
      assert (rem_obj_nat + 8 <= U64.v hd + (1 + block_wz) * 8);
      assert (rem_obj_nat + 8 <= MH.chunk_end c);
      assert (MH.chunk_end c <= heap_size);
      assert (rem_hd_nat < heap_size);
      assert (rem_obj_nat < heap_size);
      assert (heap_size < pow2 64);
      assert (rem_hd_nat < pow2 64);
      assert (rem_obj_nat < pow2 64);
      assert (rem_obj_nat >= U64.v mword);
      hd_address_spec obj;
      aligned_plus_word_product (U64.v hd) (1 + requested_wz);
      assert (rem_hd_nat % U64.v mword == 0);
      aligned_plus_word_product (U64.v hd) (requested_wz + 2);
      assert (rem_obj_nat % U64.v mword == 0);
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj : obj_addr = U64.uint_to_t rem_obj_nat in
      assert (U64.v rem_hd == rem_hd_nat);
      assert (U64.v rem_obj == rem_obj_nat);
      assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
      active_head_split_remainder_words_in_chunk
        c hd block_wz requested_wz rem_hd rem_obj;
      well_formed_no_prior_word_in_selected_chunk mh idx rem_hd;
      well_formed_no_prior_word_in_selected_chunk mh idx rem_obj;
      well_formed_no_prior_contains_selected_chunk mh idx rem_hd;
      major_alloc_head_split mh obj requested_wz fuel hdr next_fp rem_hd rem_obj;
      let alloc_hdr =
        Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
      let mh1 = major_write_word_or_same mh hd alloc_hdr in
      let c1 = MH.write_word_in_chunk c hd alloc_hdr in
      MH.write_word_in_major_at_lookup_index mh hd alloc_hdr idx;
      assert (mh1 == Seq.upd mh idx c1);
      indexed_chunk_write_preserves_word_no_prior
        mh idx idx hd rem_hd alloc_hdr;
      indexed_chunk_write_preserves_word_no_prior
        mh idx idx hd rem_obj alloc_hdr;
      indexed_chunk_write_preserves_contains_no_prior
        mh idx idx hd rem_hd alloc_hdr;
      let rem_wz = block_wz - requested_wz - 1 in
      assert (rem_wz >= 0);
      assert (rem_wz < pow2 54);
      let rem_hdr =
        Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
      let mh2 = major_write_word_or_same mh1 rem_hd rem_hdr in
      let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
      assert (Seq.index mh1 idx == c1);
      MH.write_word_in_major_at_index mh1 rem_hd rem_hdr idx;
      assert (mh2 == Seq.upd mh1 idx c2);
      indexed_chunk_write_preserves_word_no_prior
        mh1 idx idx rem_hd rem_hd rem_hdr;
      indexed_chunk_write_preserves_word_no_prior
        mh1 idx idx rem_hd rem_obj rem_hdr;
      indexed_chunk_write_preserves_contains_no_prior
        mh1 idx idx rem_hd rem_hd rem_hdr;
      let mh3 = major_write_word_or_same mh2 rem_obj next_fp in
      let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
      assert (Seq.index mh2 idx == c2);
      MH.write_word_in_major_at_index mh2 rem_obj next_fp idx;
      assert (mh3 == Seq.upd mh2 idx c3);
      indexed_chunk_write_preserves_word_no_prior
        mh2 idx idx rem_obj rem_hd next_fp;
      indexed_chunk_write_preserves_contains_no_prior
        mh2 idx idx rem_obj rem_hd next_fp;
      assert (Seq.index mh3 idx == c3);
      MH.read_write_in_chunk_same c1 rem_hd rem_hdr;
      assert (MH.read_word_in_chunk c2 rem_hd == rem_hdr);
      assert (rem_hd <> rem_obj);
      assert (U64.v rem_hd + U64.v mword <= U64.v rem_obj);
      MH.read_write_in_chunk_different c2 rem_obj rem_hd next_fp;
      assert (MH.read_word_in_chunk c3 rem_hd == rem_hdr);
      assert (U64.v hd + U64.v mword <= U64.v rem_hd);
      assert (U64.v hd + U64.v mword <= U64.v rem_obj);
      MH.write_word_in_chunk_preserves_word c hd alloc_hdr hd;
      MH.read_write_in_chunk_same c hd alloc_hdr;
      assert (MH.read_word_in_chunk c1 hd == alloc_hdr);
      MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr hd;
      MH.read_write_in_chunk_different c1 rem_hd hd rem_hdr;
      assert (MH.read_word_in_chunk c2 hd == alloc_hdr);
      MH.write_word_in_chunk_preserves_word c2 rem_obj next_fp hd;
      MH.read_write_in_chunk_different c2 rem_obj hd next_fp;
      assert (MH.read_word_in_chunk c3 hd == alloc_hdr);
      major_fl_valid_gives_mem mh fp fuel;
      assert (Seq.mem obj (MH.major_objects mh));
      MH.major_objects_member_in_lookup_chunk mh idx obj;
      assert (Seq.mem obj (MH.objects_in_chunk c));
      objects_in_chunk_from_head_split_preserves_object
        c c.base obj requested_wz block_wz next_fp
        (U64.uint_to_t rem_wz) rem_hd rem_obj;
      assert (Seq.mem obj (MH.objects_in_chunk_from c3 c3.base));
      AllocHeader.make_header_getWosize
        (U64.uint_to_t requested_wz) Alloc.white_bits 0UL;
      assert (Obj.getWosize alloc_hdr == U64.uint_to_t requested_wz);
      assert (U64.v (Obj.getWosize alloc_hdr) == requested_wz);
      assert (U64.v hd +
              (U64.v (Obj.getWosize alloc_hdr) + 1) * U64.v mword ==
              U64.v rem_hd);
      AllocHeader.make_header_getWosize
        (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL;
      assert (Obj.getWosize rem_hdr == U64.uint_to_t rem_wz);
      assert (U64.v (Obj.getWosize rem_hdr) == rem_wz);
      let diff = block_wz - requested_wz in
      assert (diff >= 2);
      assert (rem_wz == diff - 1);
      assert (rem_wz + 1 <= diff);
      assert (rem_wz + 1 <= block_wz - requested_wz);
      assert ((1 + requested_wz) + (rem_wz + 1) <= 1 + block_wz);
      assert (U64.v mword > 0);
      FStar.Math.Lemmas.lemma_mult_le_right
        (U64.v mword) ((1 + requested_wz) + (rem_wz + 1)) (1 + block_wz);
      assert (((1 + requested_wz) + (rem_wz + 1)) * U64.v mword <=
              (1 + block_wz) * U64.v mword);
      FStar.Math.Lemmas.distributivity_add_left
        (1 + requested_wz) (rem_wz + 1) (U64.v mword);
      assert (((1 + requested_wz) + (rem_wz + 1)) * U64.v mword ==
              (1 + requested_wz) * U64.v mword +
              (rem_wz + 1) * U64.v mword);
      assert ((1 + requested_wz) * U64.v mword +
              (rem_wz + 1) * U64.v mword <=
              (1 + block_wz) * U64.v mword);
      FStar.Math.Lemmas.paren_add_right
        (U64.v hd) ((1 + requested_wz) * U64.v mword)
        ((rem_wz + 1) * U64.v mword);
      assert (U64.v rem_hd +
              (U64.v (Obj.getWosize rem_hdr) + 1) * U64.v mword <=
              U64.v hd + (1 + block_wz) * U64.v mword);
      assert (U64.v rem_hd +
              (U64.v (Obj.getWosize rem_hdr) + 1) * U64.v mword <=
              MH.chunk_end c3);
      assert (U64.v rem_hd + U64.v mword < heap_size);
      f_address_spec rem_hd;
      assert (f_address rem_hd == rem_obj);
      MH.objects_in_chunk_from_head_mem c3 rem_hd;
      assert (Seq.mem rem_obj (MH.objects_in_chunk_from c3 rem_hd));
      f_hd_roundtrip obj;
      assert (f_address hd == obj);
      assert (U64.v hd >= MH.chunk_start c3);
      assert (U64.v hd + U64.v mword < MH.chunk_end c3);
      assert (MH.read_word_in_chunk c3 hd == alloc_hdr);
      assert (U64.v hd +
              (U64.v (Obj.getWosize (MH.read_word_in_chunk c3 hd)) + 1) *
                U64.v mword == U64.v rem_hd);
      assert (U64.v rem_hd < pow2 64);
      assert (U64.v rem_hd % U64.v mword == 0);
      assert (U64.uint_to_t (U64.v rem_hd) == rem_hd);
      assert (U64.v rem_hd < MH.chunk_end c3);
      MH.objects_in_chunk_from_tail_mem c3 hd rem_hd rem_obj;
      assert (Seq.mem rem_obj (MH.objects_in_chunk_from c3 hd));
      assert (U64.v c3.base <= U64.v hd);
      MH.objects_in_chunk_from_later_in_earlier c3 c3.base hd rem_obj;
      assert (Seq.mem rem_obj (MH.objects_in_chunk c3));
      MH.major_objects_member_at_index mh3 idx rem_obj;
      assert (Seq.mem rem_obj (MH.major_objects mh3));
      MH.read_word_in_major_at_index mh3 rem_hd idx;
      assert (MH.read_word_in_major mh3 rem_hd == Some rem_hdr);
      let r = major_alloc_spec_with_fuel mh fp requested_wz fuel in
      assert (r.major_alloc_out == mh3);
      assert (r.major_fp_out == rem_obj);
      assert (r.major_obj_out == fp);
      assert (U64.v rem_obj >= U64.v zero_addr + U64.v mword);
      assert (U64.v rem_hd + U64.v mword < heap_size);
      f_address_spec rem_hd;
      assert (f_address rem_hd == rem_obj);
      hd_f_roundtrip rem_hd;
      assert (hd_address rem_obj == rem_hd);
      AllocHeader.make_header_getWosize
        (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL;
      assert (Obj.getWosize rem_hdr == U64.uint_to_t rem_wz);
      assert (U64.v (Obj.getWosize rem_hdr) == rem_wz);
      FStar.Classical.exists_intro
        (fun (new_fp: obj_addr) ->
          new_fp == r.major_fp_out /\
          Seq.mem new_fp (MH.major_objects r.major_alloc_out))
        rem_obj;
      assert (major_alloc_result_fp_in_objects r);
      assert (diff >= remaining + 1);
      assert (diff - 1 >= remaining);
      assert (rem_wz == diff - 1);
      if rem_wz < remaining then assert False;
      assert (rem_wz >= remaining);
      assert (major_fl_head_wosize mh3 rem_obj == rem_wz);
      assert (major_fl_head_wosize r.major_alloc_out r.major_fp_out >= remaining)
#pop-options

#push-options "--z3rlimit 10"
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

let major_alloc_after_expand_exact (mh: MH.major_heap) (c: MH.heap_chunk)
                                   (next_fp: U64.t) (fuel: nat)
  : Lemma (requires U64.v c.base >= U64.v zero_addr)
          (ensures (let er = expand_major_heap mh c next_fp in
                    let init = (init_fresh_chunk c next_fp).chunk_out in
                    let alloc_hdr =
                      Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.white_bits 0UL in
                    let out =
                      Seq.upd er.major_out 0 (MH.write_word_in_chunk init c.base alloc_hdr) in
                    let r =
                      major_alloc_spec_with_fuel
                        er.major_out er.fp_out (fresh_chunk_wosize c) (fuel + 1) in
                    r.major_alloc_out == out /\
                    r.major_fp_out == next_fp /\
                    r.major_obj_out == er.fp_out))
  = let er = expand_major_heap mh c next_fp in
    let init = (init_fresh_chunk c next_fp).chunk_out in
    let fp = er.fp_out in
    let wz = fresh_chunk_wosize c in
    let wz_u = fresh_chunk_wosize_u64 c in
    let hdr = Alloc.make_header wz_u Alloc.blue_bits 0UL in
    let alloc_hdr = Alloc.make_header wz_u Alloc.white_bits 0UL in
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
    assert (Seq.length er.major_out > 0);
    assert (Seq.index er.major_out 0 == init);
    assert (MH.word_in_chunk init c.base);
    assert (MH.read_word_in_major er.major_out (hd_address fp) == Some hdr);
    assert (Obj.getWosize hdr == wz_u);
    assert (U64.v (Obj.getWosize hdr) == wz);
    assert (U64.v (Obj.getWosize hdr) - wz == 0);
    assert (U64.v (Obj.getWosize hdr) - wz < 2);
    assert (MH.read_word_in_major er.major_out fp == Some next_fp);
    major_spec_next_fp_some er.major_out fp next_fp;
    assert (major_spec_next_fp er.major_out fp == next_fp);
    MH.write_word_in_major_at_index er.major_out c.base alloc_hdr 0;
    major_write_word_or_same_some er.major_out
      (Seq.upd er.major_out 0 (MH.write_word_in_chunk init c.base alloc_hdr))
      c.base alloc_hdr;
    major_alloc_from_block_exact er.major_out fp wz next_fp hdr;
    major_alloc_search_found_head er.major_out fp 0UL fp wz (fuel + 1) hdr

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_after_expand_no_split (mh: MH.major_heap) (c: MH.heap_chunk)
                                      (next_fp: U64.t) (requested_wz fuel: nat)
  : Lemma (requires U64.v c.base >= U64.v zero_addr /\
                    requested_wz > 0 /\
                    fresh_chunk_wosize c >= requested_wz /\
                    fresh_chunk_wosize c - requested_wz < 2)
          (ensures (let er = expand_major_heap mh c next_fp in
                    let init = (init_fresh_chunk c next_fp).chunk_out in
                    let alloc_hdr =
                      Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.white_bits 0UL in
                    let out =
                      Seq.upd er.major_out 0 (MH.write_word_in_chunk init c.base alloc_hdr) in
                    let r =
                      major_alloc_spec_with_fuel
                        er.major_out er.fp_out requested_wz (fuel + 1) in
                    r.major_alloc_out == out /\
                    r.major_fp_out == next_fp /\
                    r.major_obj_out == er.fp_out))
  = let er = expand_major_heap mh c next_fp in
    let init = (init_fresh_chunk c next_fp).chunk_out in
    let fp = er.fp_out in
    let bwz = fresh_chunk_wosize c in
    let bwz_u = fresh_chunk_wosize_u64 c in
    let wz = requested_wz in
    let hdr = Alloc.make_header bwz_u Alloc.blue_bits 0UL in
    let alloc_hdr = Alloc.make_header bwz_u Alloc.white_bits 0UL in
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
    assert (Seq.length er.major_out > 0);
    assert (Seq.index er.major_out 0 == init);
    assert (MH.word_in_chunk init c.base);
    assert (MH.read_word_in_major er.major_out (hd_address fp) == Some hdr);
    assert (Obj.getWosize hdr == bwz_u);
    assert (U64.v (Obj.getWosize hdr) == bwz);
    assert (U64.v (Obj.getWosize hdr) >= wz);
    assert (U64.v (Obj.getWosize hdr) - wz < 2);
    assert (MH.read_word_in_major er.major_out fp == Some next_fp);
    major_spec_next_fp_some er.major_out fp next_fp;
    assert (major_spec_next_fp er.major_out fp == next_fp);
    MH.write_word_in_major_at_index er.major_out c.base alloc_hdr 0;
    major_write_word_or_same_some er.major_out
      (Seq.upd er.major_out 0 (MH.write_word_in_chunk init c.base alloc_hdr))
      c.base alloc_hdr;
    major_alloc_from_block_exact er.major_out fp wz next_fp hdr;
    major_alloc_search_found_head er.major_out fp 0UL fp wz (fuel + 1) hdr
#pop-options

let seq_upd_overwrite_head (#a: Type) (s: Seq.seq a{Seq.length s > 0}) (v1 v2: a)
  : Lemma (Seq.upd (Seq.upd s 0 v1) 0 v2 == Seq.upd s 0 v2)
  = assert (Seq.length (Seq.upd (Seq.upd s 0 v1) 0 v2) ==
            Seq.length (Seq.upd s 0 v2));
    let prove_i (i: nat{i < Seq.length (Seq.upd s 0 v2)})
      : Lemma (Seq.index (Seq.upd (Seq.upd s 0 v1) 0 v2) i ==
               Seq.index (Seq.upd s 0 v2) i)
      = if i = 0 then ()
        else begin
          assert (Seq.index (Seq.upd (Seq.upd s 0 v1) 0 v2) i ==
                  Seq.index (Seq.upd s 0 v1) i);
          assert (Seq.index (Seq.upd s 0 v1) i == Seq.index s i);
          assert (Seq.index (Seq.upd s 0 v2) i == Seq.index s i)
        end
    in
    FStar.Classical.forall_intro prove_i;
    Seq.lemma_eq_intro (Seq.upd (Seq.upd s 0 v1) 0 v2) (Seq.upd s 0 v2);
    Seq.lemma_eq_elim (Seq.upd (Seq.upd s 0 v1) 0 v2) (Seq.upd s 0 v2)

let seq_upd_overwrite_index (#a: Type) (s: Seq.seq a) (i: nat{i < Seq.length s})
                             (v1 v2: a)
  : Lemma (Seq.upd (Seq.upd s i v1) i v2 == Seq.upd s i v2)
  = assert (Seq.length (Seq.upd (Seq.upd s i v1) i v2) ==
            Seq.length (Seq.upd s i v2));
    let prove_k (k: nat{k < Seq.length (Seq.upd s i v2)})
      : Lemma (Seq.index (Seq.upd (Seq.upd s i v1) i v2) k ==
               Seq.index (Seq.upd s i v2) k)
      = if k = i then ()
        else begin
          assert (Seq.index (Seq.upd (Seq.upd s i v1) i v2) k ==
                  Seq.index (Seq.upd s i v1) k);
          assert (Seq.index (Seq.upd s i v1) k == Seq.index s k);
          assert (Seq.index (Seq.upd s i v2) k == Seq.index s k)
        end
    in
    FStar.Classical.forall_intro prove_k;
    Seq.lemma_eq_intro (Seq.upd (Seq.upd s i v1) i v2) (Seq.upd s i v2);
    Seq.lemma_eq_elim (Seq.upd (Seq.upd s i v1) i v2) (Seq.upd s i v2)

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let read_word_update_expanded_head_same_range_miss
  (mh: MH.major_heap) (fresh_head replacement: MH.heap_chunk) (addr: hp_addr)
  : Lemma (requires MH.chunk_start replacement == MH.chunk_start fresh_head /\
                    MH.chunk_end replacement == MH.chunk_end fresh_head /\
                    ~(MH.chunk_contains_addr fresh_head addr))
          (ensures MH.read_word_in_major
                    (Seq.upd (MH.add_chunk mh fresh_head) 0 replacement) addr ==
                  MH.read_word_in_major mh addr)
  = let out = Seq.upd (MH.add_chunk mh fresh_head) 0 replacement in
    assert (Seq.length out == Seq.length (MH.add_chunk mh fresh_head));
    assert (Seq.index out 0 == replacement);
    assert (Seq.length out == Seq.length (MH.add_chunk mh replacement));
    let same (i: nat{i < Seq.length out})
      : Lemma (Seq.index out i == Seq.index (MH.add_chunk mh replacement) i)
      = if i = 0 then ()
        else begin
          let im1 : n:nat{n < Seq.length mh} = i - 1 in
          assert (Seq.index out i == Seq.index (MH.add_chunk mh fresh_head) i);
          assert (Seq.index (MH.add_chunk mh fresh_head) i == Seq.index mh im1);
          assert (Seq.index (MH.add_chunk mh replacement) i == Seq.index mh im1)
        end
    in
    FStar.Classical.forall_intro same;
    Seq.lemma_eq_intro out (MH.add_chunk mh replacement);
    Seq.lemma_eq_elim out (MH.add_chunk mh replacement);
    assert (~(MH.chunk_contains_addr replacement addr));
    MH.read_word_add_chunk_miss mh replacement addr
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let fresh_chunk_split_remainder_fits (c: MH.heap_chunk) (next_fp: U64.t)
                                     (requested_wz: nat) (rem_hd rem_obj: hp_addr)
  : Lemma (requires requested_wz > 0 /\
                    fresh_chunk_wosize c - requested_wz >= 2 /\
                    U64.v rem_hd == U64.v c.base + (1 + requested_wz) * 8 /\
                    U64.v rem_obj == U64.v rem_hd + U64.v mword)
          (ensures (let init = (init_fresh_chunk c next_fp).chunk_out in
                    let alloc_hdr =
                      Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
                    let c1 = MH.write_word_in_chunk init c.base alloc_hdr in
                    let rem_wz = fresh_chunk_wosize c - requested_wz - 1 in
                    let rem_hdr =
                      Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
                    let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
                    MH.word_in_chunk init rem_hd /\
                    MH.word_in_chunk c1 rem_hd /\
                    MH.word_in_chunk c1 rem_obj /\
                    MH.word_in_chunk c2 rem_obj /\
                    rem_wz < pow2 54))
  = let init = (init_fresh_chunk c next_fp).chunk_out in
    let fw = fresh_chunk_wosize c in
    let wz = requested_wz in
    let alloc_hdr = Alloc.make_header (U64.uint_to_t wz) Alloc.white_bits 0UL in
    let c1 = MH.write_word_in_chunk init c.base alloc_hdr in
    init_fresh_chunk_preserves_range c next_fp;
    fresh_chunk_wosize_fits c;
    fresh_chunk_has_block c;
    assert (MH.word_in_chunk init c.base);
    let rem_hd_nat = U64.v c.base + (1 + wz) * 8 in
    aligned_plus_word_product (U64.v c.base) (1 + wz);
    assert (rem_hd_nat % 8 == 0);
    assert (U64.v mword == 8);
    assert (c.size % U64.v mword == 0);
    FStar.Math.Lemmas.lemma_div_exact c.size (U64.v mword);
    assert (c.size == (c.size / U64.v mword) * U64.v mword);
    assert (chunk_word_capacity c == c.size / U64.v mword);
    assert (c.size == chunk_word_capacity c * U64.v mword);
    assert (fw == chunk_word_capacity c - 1);
    assert (chunk_word_capacity c == fw + 1);
    assert (wz + 2 <= fw);
    FStar.Math.Lemmas.distributivity_add_left (1 + wz) 1 8;
    assert ((1 + wz) * 8 + 8 == (wz + 2) * 8);
    FStar.Math.Lemmas.paren_add_right (U64.v c.base) ((1 + wz) * 8) 8;
    assert (rem_hd_nat + 8 == U64.v c.base + ((1 + wz) * 8 + 8));
    assert (rem_hd_nat + 8 == U64.v c.base + (wz + 2) * 8);
    assert (U64.v c.base + (wz + 2) * 8 <= U64.v c.base + fw * 8);
    assert (U64.v c.base + fw * 8 < U64.v c.base + (fw + 1) * 8);
    assert (U64.v c.base + (fw + 1) * 8 == MH.chunk_end c);
    assert (rem_hd_nat + 8 < MH.chunk_end c);
    assert (U64.v rem_hd == rem_hd_nat);
    assert (MH.word_in_chunk init rem_hd);
    MH.write_word_in_chunk_preserves_word init c.base alloc_hdr rem_hd;
    assert (MH.word_in_chunk c1 rem_hd);
    let rem_wz = fw - wz - 1 in
    assert (rem_wz < fw);
    assert (rem_wz < pow2 54);
    let rem_hdr = Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
    let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
    let rem_obj_nat = rem_hd_nat + 8 in
    sum_of_aligned_is_aligned rem_hd mword;
    assert (rem_obj_nat == U64.v rem_hd + U64.v mword);
    assert (U64.v rem_obj == rem_obj_nat);
    assert (MH.word_in_chunk c1 rem_obj);
    MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr rem_obj;
    assert (MH.word_in_chunk c2 rem_obj)
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let fresh_chunk_split_remainder_addr_bounds (c: MH.heap_chunk)
                                            (requested_wz: nat)
  : Lemma (requires requested_wz > 0 /\
                    fresh_chunk_wosize c - requested_wz >= 2)
          (ensures (let rem_hd_nat = U64.v c.base + (1 + requested_wz) * 8 in
                    let rem_obj_nat = rem_hd_nat + U64.v mword in
                    rem_hd_nat < heap_size /\
                    rem_hd_nat % U64.v mword == 0 /\
                    rem_hd_nat < pow2 64 /\
                    rem_obj_nat < heap_size /\
                    rem_obj_nat % U64.v mword == 0 /\
                    rem_obj_nat < pow2 64))
  = let fw = fresh_chunk_wosize c in
    let wz = requested_wz in
    let rem_hd_nat = U64.v c.base + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + U64.v mword in
    fresh_chunk_has_block c;
    assert (U64.v mword == 8);
    assert (c.size % U64.v mword == 0);
    FStar.Math.Lemmas.lemma_div_exact c.size (U64.v mword);
    assert (c.size == (c.size / U64.v mword) * U64.v mword);
    assert (chunk_word_capacity c == c.size / U64.v mword);
    assert (c.size == chunk_word_capacity c * U64.v mword);
    assert (fw == chunk_word_capacity c - 1);
    assert (chunk_word_capacity c == fw + 1);
    assert (wz + 2 <= fw);
    aligned_plus_word_product (U64.v c.base) (1 + wz);
    assert (rem_hd_nat % U64.v mword == 0);
    FStar.Math.Lemmas.distributivity_add_left (1 + wz) 1 8;
    assert ((1 + wz) * 8 + 8 == (wz + 2) * 8);
    FStar.Math.Lemmas.paren_add_right (U64.v c.base) ((1 + wz) * 8) 8;
    assert (rem_obj_nat == U64.v c.base + (wz + 2) * 8);
    aligned_plus_word_product (U64.v c.base) (wz + 2);
    assert (rem_obj_nat % U64.v mword == 0);
    assert (U64.v c.base + (wz + 2) * 8 <= U64.v c.base + fw * 8);
    assert (U64.v c.base + fw * 8 < U64.v c.base + (fw + 1) * 8);
    assert (U64.v c.base + (fw + 1) * 8 == MH.chunk_end c);
    assert (rem_obj_nat < MH.chunk_end c);
    assert (MH.chunk_end c <= heap_size);
    assert (rem_hd_nat < rem_obj_nat);
    assert (rem_hd_nat < heap_size);
    assert (heap_size < pow2 64);
    assert (rem_hd_nat < pow2 64);
    assert (rem_obj_nat < pow2 64)
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_after_expand_split (mh: MH.major_heap) (c: MH.heap_chunk)
                                   (next_fp: U64.t) (requested_wz fuel: nat)
                                   (rem_hd rem_obj: hp_addr)
  : Lemma (requires U64.v c.base >= U64.v zero_addr /\
                    requested_wz > 0 /\
                    fresh_chunk_wosize c - requested_wz >= 2 /\
                    U64.v rem_hd == U64.v c.base + (1 + requested_wz) * 8 /\
                    U64.v rem_obj == U64.v rem_hd + U64.v mword)
          (ensures (let er = expand_major_heap mh c next_fp in
                    let init = (init_fresh_chunk c next_fp).chunk_out in
                    let alloc_hdr =
                      Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
                    let c1 = MH.write_word_in_chunk init c.base alloc_hdr in
                    let rem_wz = fresh_chunk_wosize c - requested_wz - 1 in
                    let rem_hdr =
                      Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
                    let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
                    let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
                    let out = Seq.upd er.major_out 0 c3 in
                    let r =
                      major_alloc_spec_with_fuel
                        er.major_out er.fp_out requested_wz (fuel + 1) in
                    r.major_alloc_out == out /\
                    r.major_fp_out == rem_obj /\
                    r.major_obj_out == er.fp_out))
  = let er = expand_major_heap mh c next_fp in
    let init = (init_fresh_chunk c next_fp).chunk_out in
    let fp = er.fp_out in
    let wz = requested_wz in
    let hdr = Alloc.make_header (fresh_chunk_wosize_u64 c) Alloc.blue_bits 0UL in
    let alloc_hdr = Alloc.make_header (U64.uint_to_t wz) Alloc.white_bits 0UL in
    let c1 = MH.write_word_in_chunk init c.base alloc_hdr in
    let rem_wz = fresh_chunk_wosize c - wz - 1 in
    let rem_hdr = Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
    let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
    let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
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
    assert (Seq.length er.major_out > 0);
    assert (Seq.index er.major_out 0 == init);
    assert (MH.word_in_chunk init c.base);
    assert (MH.read_word_in_major er.major_out (hd_address fp) == Some hdr);
    assert (Obj.getWosize hdr == fresh_chunk_wosize_u64 c);
    assert (U64.v (Obj.getWosize hdr) == fresh_chunk_wosize c);
    assert (U64.v (Obj.getWosize hdr) >= wz);
    assert (U64.v (Obj.getWosize hdr) - wz >= 2);
    assert (MH.read_word_in_major er.major_out fp == Some next_fp);
    major_spec_next_fp_some er.major_out fp next_fp;
    assert (major_spec_next_fp er.major_out fp == next_fp);
    fresh_chunk_split_remainder_fits c next_fp wz rem_hd rem_obj;
    assert (U64.v rem_hd == U64.v c.base + (1 + wz) * 8);
    assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
    assert (U64.v rem_hd < heap_size);
    assert (U64.v rem_hd % U64.v mword == 0);
    assert (U64.v rem_obj < heap_size);
    assert (U64.v rem_obj % U64.v mword == 0);
    assert (U64.v c.base + (1 + wz) * 8 < heap_size);
    assert (U64.v c.base + (1 + wz) * 8 + 8 < heap_size);
    assert ((U64.v c.base + (1 + wz) * 8) % 8 == 0);
    assert ((U64.v c.base + (1 + wz) * 8 + 8) % 8 == 0);
    MH.write_word_in_major_at_index er.major_out c.base alloc_hdr 0;
    assert (MH.write_word_in_major er.major_out c.base alloc_hdr == Some (Seq.upd er.major_out 0 c1));
    major_write_word_or_same_some er.major_out (Seq.upd er.major_out 0 c1) c.base alloc_hdr;
    assert (MH.word_in_chunk c1 rem_hd);
    MH.write_word_in_major_at_index (Seq.upd er.major_out 0 c1) rem_hd rem_hdr 0;
    assert (Seq.index (Seq.upd er.major_out 0 c1) 0 == c1);
    assert (MH.write_word_in_chunk (Seq.index (Seq.upd er.major_out 0 c1) 0) rem_hd rem_hdr == c2);
    seq_upd_overwrite_head er.major_out c1 c2;
    assert (Seq.upd (Seq.upd er.major_out 0 c1) 0 c2 == Seq.upd er.major_out 0 c2);
    assert (MH.write_word_in_major (Seq.upd er.major_out 0 c1) rem_hd rem_hdr ==
            Some (Seq.upd er.major_out 0 c2));
    major_write_word_or_same_some (Seq.upd er.major_out 0 c1) (Seq.upd er.major_out 0 c2)
      rem_hd rem_hdr;
    assert (MH.word_in_chunk c2 rem_obj);
    MH.write_word_in_major_at_index (Seq.upd er.major_out 0 c2) rem_obj next_fp 0;
    assert (Seq.index (Seq.upd er.major_out 0 c2) 0 == c2);
    assert (MH.write_word_in_chunk (Seq.index (Seq.upd er.major_out 0 c2) 0) rem_obj next_fp == c3);
    seq_upd_overwrite_head er.major_out c2 c3;
    assert (Seq.upd (Seq.upd er.major_out 0 c2) 0 c3 == Seq.upd er.major_out 0 c3);
    assert (MH.write_word_in_major (Seq.upd er.major_out 0 c2) rem_obj next_fp ==
            Some (Seq.upd er.major_out 0 c3));
    major_write_word_or_same_some (Seq.upd er.major_out 0 c2) (Seq.upd er.major_out 0 c3)
      rem_obj next_fp;
    major_alloc_from_block_split_normal er.major_out fp wz next_fp hdr;
    major_alloc_search_found_head er.major_out fp 0UL fp wz (fuel + 1) hdr
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_after_expand_split_preserves_head_wosize
  (mh: MH.major_heap) (c: MH.heap_chunk) (next_fp: U64.t)
  (requested_wz fuel: nat) (remaining: nat)
  : Lemma
      (requires U64.v c.base >= U64.v zero_addr /\
                requested_wz > 0 /\
                remaining > 0 /\
                fresh_chunk_wosize c >= requested_wz + 1 + remaining)
      (ensures
        (let er = expand_major_heap mh c next_fp in
         let r =
           major_alloc_spec_with_fuel
             er.major_out er.fp_out requested_wz (fuel + 1) in
         r.major_obj_out == er.fp_out /\
         r.major_fp_out <> 0UL /\
         major_fl_head_wosize r.major_alloc_out r.major_fp_out >= remaining))
  =
  let fw = fresh_chunk_wosize c in
  let wz = requested_wz in
  assert (fw - wz >= 1 + remaining);
  assert (fw - wz >= 2);
  fresh_chunk_split_remainder_addr_bounds c wz;
  let rem_hd_nat = U64.v c.base + (1 + wz) * 8 in
  let rem_obj_nat = rem_hd_nat + U64.v mword in
  let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
  let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
  assert (U64.v rem_hd == rem_hd_nat);
  assert (U64.v rem_obj == rem_obj_nat);
  assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
  major_alloc_after_expand_split mh c next_fp wz fuel rem_hd rem_obj;
  let er = expand_major_heap mh c next_fp in
  let init = (init_fresh_chunk c next_fp).chunk_out in
  let fp = er.fp_out in
  let alloc_hdr = Alloc.make_header (U64.uint_to_t wz) Alloc.white_bits 0UL in
  let c1 = MH.write_word_in_chunk init c.base alloc_hdr in
  let rem_wz = fw - wz - 1 in
  let rem_hdr = Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
  let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
  let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
  let out = Seq.upd er.major_out 0 c3 in
  let r = major_alloc_spec_with_fuel er.major_out fp wz (fuel + 1) in
  assert (r.major_alloc_out == out);
  assert (r.major_fp_out == rem_obj);
  assert (r.major_obj_out == fp);
  fresh_chunk_split_remainder_fits c next_fp wz rem_hd rem_obj;
  assert (MH.word_in_chunk c1 rem_hd);
  assert (MH.word_in_chunk c1 rem_obj);
  assert (MH.word_in_chunk c2 rem_obj);
  MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr rem_hd;
  assert (MH.word_in_chunk c2 rem_hd);
  MH.write_word_in_chunk_preserves_word c2 rem_obj next_fp rem_hd;
  assert (MH.word_in_chunk c3 rem_hd);
  MH.read_write_in_chunk_same c1 rem_hd rem_hdr;
  assert (MH.read_word_in_chunk c2 rem_hd == rem_hdr);
  assert (rem_hd <> rem_obj);
  assert (U64.v rem_hd + U64.v mword <= U64.v rem_obj);
  MH.read_write_in_chunk_different c2 rem_obj rem_hd next_fp;
  assert (MH.read_word_in_chunk c3 rem_hd == rem_hdr);
  assert (Seq.length out == Seq.length er.major_out);
  assert (Seq.length out > 0);
  assert (Seq.index out 0 == c3);
  MH.read_word_in_major_at_index out rem_hd 0;
  assert (MH.read_word_in_major out rem_hd == Some rem_hdr);
  assert (U64.v rem_obj >= U64.v zero_addr + U64.v mword);
  assert (U64.v rem_obj < heap_size);
  assert (U64.v rem_obj % U64.v mword == 0);
  assert (U64.v rem_hd + U64.v mword < heap_size);
  f_address_spec rem_hd;
  assert (f_address rem_hd == rem_obj);
  hd_f_roundtrip rem_hd;
  assert (hd_address rem_obj == rem_hd);
  AllocHeader.make_header_getWosize (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL;
  assert (Obj.getWosize rem_hdr == U64.uint_to_t rem_wz);
  assert (U64.v (Obj.getWosize rem_hdr) == rem_wz);
  assert (rem_wz >= remaining)
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_after_expand_fuel_irrelevant (mh: MH.major_heap) (c: MH.heap_chunk)
                                             (next_fp: U64.t)
                                             (requested_wz fuel: nat)
  : Lemma (requires U64.v c.base >= U64.v zero_addr /\
                    requested_wz > 0 /\
                    fresh_chunk_wosize c >= requested_wz)
          (ensures (let er = expand_major_heap mh c next_fp in
                    major_alloc_spec_with_fuel er.major_out er.fp_out requested_wz 1 ==
                    major_alloc_spec_with_fuel er.major_out er.fp_out requested_wz (fuel + 1)))
  = let er = expand_major_heap mh c next_fp in
    let r1 = major_alloc_spec_with_fuel er.major_out er.fp_out requested_wz 1 in
    let rf = major_alloc_spec_with_fuel er.major_out er.fp_out requested_wz (fuel + 1) in
    if fresh_chunk_wosize c - requested_wz >= 2 then begin
      fresh_chunk_split_remainder_addr_bounds c requested_wz;
      let rem_hd_nat = U64.v c.base + (1 + requested_wz) * 8 in
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj_nat = rem_hd_nat + U64.v mword in
      let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
      assert (U64.v rem_hd == U64.v c.base + (1 + requested_wz) * 8);
      assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
      major_alloc_after_expand_split mh c next_fp requested_wz 0 rem_hd rem_obj;
      major_alloc_after_expand_split mh c next_fp requested_wz fuel rem_hd rem_obj;
      assert (r1.major_alloc_out == rf.major_alloc_out);
      assert (r1.major_fp_out == rf.major_fp_out);
      assert (r1.major_obj_out == rf.major_obj_out)
    end else begin
      assert (fresh_chunk_wosize c - requested_wz < 2);
      major_alloc_after_expand_no_split mh c next_fp requested_wz 0;
      major_alloc_after_expand_no_split mh c next_fp requested_wz fuel;
      assert (r1.major_alloc_out == rf.major_alloc_out);
      assert (r1.major_fp_out == rf.major_fp_out);
      assert (r1.major_obj_out == rf.major_obj_out)
    end
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 0 --ifuel 0"
let major_alloc_expand_on_oom_preserves_old_read
  (mh: MH.major_heap) (fp: U64.t) (requested_wz fuel: nat)
  (fresh: MH.heap_chunk) (addr: hp_addr)
  : Lemma (requires (major_alloc_spec_with_fuel mh fp requested_wz fuel).major_obj_out == 0UL /\
                    U64.v fresh.base >= U64.v zero_addr /\
                    requested_wz > 0 /\
                    fresh_chunk_wosize fresh >= requested_wz /\
                    ~(MH.chunk_contains_addr fresh addr))
          (ensures MH.read_word_in_major
                    (major_alloc_spec_expand_on_oom
                      mh fp requested_wz fuel fresh).major_alloc_out addr ==
                  MH.read_word_in_major mh addr)
  = let er = expand_major_heap mh fresh fp in
    let init = (init_fresh_chunk fresh fp).chunk_out in
    assert (major_alloc_spec_expand_on_oom mh fp requested_wz fuel fresh ==
            major_alloc_spec_with_fuel er.major_out er.fp_out requested_wz (fuel + 1));
    init_fresh_chunk_preserves_range fresh fp;
    assert (~(MH.chunk_contains_addr init addr));
    if fresh_chunk_wosize fresh - requested_wz >= 2 then begin
      fresh_chunk_split_remainder_addr_bounds fresh requested_wz;
      let rem_hd_nat = U64.v fresh.base + (1 + requested_wz) * 8 in
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj_nat = rem_hd_nat + U64.v mword in
      let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
      assert (U64.v rem_hd == U64.v fresh.base + (1 + requested_wz) * 8);
      assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
      major_alloc_after_expand_split
        mh fresh fp requested_wz fuel rem_hd rem_obj;
      let alloc_hdr =
        Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
      let c1 = MH.write_word_in_chunk init fresh.base alloc_hdr in
      let rem_wz = fresh_chunk_wosize fresh - requested_wz - 1 in
      let rem_hdr =
        Alloc.make_header (U64.uint_to_t rem_wz) Alloc.blue_bits 0UL in
      let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
      let c3 = MH.write_word_in_chunk c2 rem_obj fp in
      MH.write_word_in_chunk_preserves_range init fresh.base alloc_hdr;
      MH.write_word_in_chunk_preserves_range c1 rem_hd rem_hdr;
      MH.write_word_in_chunk_preserves_range c2 rem_obj fp;
      assert (MH.chunk_start c3 == MH.chunk_start init);
      assert (MH.chunk_end c3 == MH.chunk_end init);
      read_word_update_expanded_head_same_range_miss mh init c3 addr;
      assert (MH.read_word_in_major
                (major_alloc_spec_expand_on_oom
                  mh fp requested_wz fuel fresh).major_alloc_out addr ==
              MH.read_word_in_major mh addr)
    end else begin
      assert (fresh_chunk_wosize fresh - requested_wz < 2);
      major_alloc_after_expand_no_split mh fresh fp requested_wz fuel;
      let alloc_hdr =
        Alloc.make_header (fresh_chunk_wosize_u64 fresh) Alloc.white_bits 0UL in
      let c1 = MH.write_word_in_chunk init fresh.base alloc_hdr in
      MH.write_word_in_chunk_preserves_range init fresh.base alloc_hdr;
      read_word_update_expanded_head_same_range_miss mh init c1 addr;
      assert (MH.read_word_in_major
                (major_alloc_spec_expand_on_oom
                  mh fp requested_wz fuel fresh).major_alloc_out addr ==
              MH.read_word_in_major mh addr)
    end
#pop-options
