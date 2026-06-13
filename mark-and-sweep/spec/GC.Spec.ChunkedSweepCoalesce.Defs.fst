/// ---------------------------------------------------------------------------
/// GC.Spec.ChunkedSweepCoalesce.Defs — Chunked sweep/coalesce definitions
/// ---------------------------------------------------------------------------
///
/// This is the first small, proof-local surface for porting major GC from the
/// legacy dense heap walk to `GC.Spec.MajorHeap`.  It keeps the dense
/// sweep/coalesce algorithm shape, but traverses one chunk's object list at a
/// time and flushes pending blue runs at chunk boundaries so coalescing never
/// merges adjacent chunks.

module GC.Spec.ChunkedSweepCoalesce.Defs

open FStar.Seq

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator

#set-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

/// ---------------------------------------------------------------------------
/// Chunked object header/color helpers
/// ---------------------------------------------------------------------------

let chunked_read_header (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option U64.t)
  = MH.read_word_in_major mh (hd_address obj)

let chunked_read_header_step (mh: MH.major_heap) (obj: obj_addr)
  : Lemma
      (chunked_read_header mh obj ==
       MH.read_word_in_major mh (hd_address obj))
  = ()

let chunked_color_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option Obj.color)
  = match chunked_read_header mh obj with
    | Some hdr -> Some (Obj.getColor hdr)
    | None -> None

let chunked_wosize_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot Obj.wosize
  = match chunked_read_header mh obj with
    | Some hdr -> Obj.getWosize hdr
    | None -> 0UL

let chunked_wosize_of_object_some
    (mh: MH.major_heap) (obj: obj_addr) (hdr: U64.t)
  : Lemma
      (requires chunked_read_header mh obj == Some hdr)
      (ensures chunked_wosize_of_object mh obj == Obj.getWosize hdr)
  = ()

let chunked_wosize_of_object_none
    (mh: MH.major_heap) (obj: obj_addr)
  : Lemma
      (requires chunked_read_header mh obj == None)
      (ensures chunked_wosize_of_object mh obj == 0UL)
  = ()

let chunked_tag_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot U64.t
  = match chunked_read_header mh obj with
    | Some hdr -> Obj.getTag hdr
    | None -> 0UL

let chunked_is_white (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_color_of_object mh obj with
    | Some Header.White -> true
    | _ -> false

let chunked_is_blue (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_color_of_object mh obj with
    | Some Header.Blue -> true
    | _ -> false

let chunked_is_black (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_color_of_object mh obj with
    | Some Header.Black -> true
    | _ -> false

let chunked_is_infix (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = chunked_tag_of_object mh obj = Obj.infix_tag

let chunked_set_object_color
    (mh: MH.major_heap) (obj: obj_addr) (color: Header.color_sem)
  : GTot MH.major_heap
  = match chunked_read_header mh obj with
    | None -> mh
    | Some hdr ->
      let hdr' = Obj.colorHeader hdr color in
      SpecMajorAlloc.major_write_word_or_same mh (hd_address obj) hdr'

let chunked_make_white (mh: MH.major_heap) (obj: obj_addr)
  : GTot MH.major_heap
  = chunked_set_object_color mh obj Header.White

let chunked_make_blue (mh: MH.major_heap) (obj: obj_addr)
  : GTot MH.major_heap
  = chunked_set_object_color mh obj Header.Blue

/// ---------------------------------------------------------------------------
/// Chunked sweep
/// ---------------------------------------------------------------------------

let chunked_sweep_object (mh: MH.major_heap) (obj: obj_addr) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)
  =
  if chunked_is_infix mh obj then (mh, fp)
  else if chunked_is_white mh obj then
    let ws = chunked_wosize_of_object mh obj in
    let hd = hd_address obj in
    let mh' =
      if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size then
        SpecMajorAlloc.major_write_word_or_same mh obj fp
      else
        mh
    in
    let mh'' = chunked_make_blue mh' obj in
    (mh'', obj)
  else if chunked_is_black mh obj then
    let mh' = chunked_make_white mh obj in
    (mh', fp)
  else
    (mh, fp)

let rec chunked_sweep_aux (mh: MH.major_heap) (objs: seq obj_addr) (fp: U64.t)
  : GTot (MH.major_heap & U64.t) (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then (mh, fp)
  else begin
    assert (Seq.length objs > 0);
    let obj = Seq.head objs in
    let (mh', fp') = chunked_sweep_object mh obj fp in
    chunked_sweep_aux mh' (Seq.tail objs) fp'
  end

let rec chunked_sweep_chunks
    (source_chunks: MH.major_heap) (work: MH.major_heap) (fp: U64.t)
  : GTot (MH.major_heap & U64.t) (decreases Seq.length source_chunks)
  =
  if Seq.length source_chunks = 0 then (work, fp)
  else begin
    assert (Seq.length source_chunks > 0);
    let c = Seq.head source_chunks in
    let (work', fp') = chunked_sweep_aux work (MH.objects_in_chunk c) fp in
    chunked_sweep_chunks (Seq.tail source_chunks) work' fp'
  end

let chunked_sweep (mh: MH.major_heap) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)
  = chunked_sweep_chunks mh mh fp

/// ---------------------------------------------------------------------------
/// Chunked fused sweep/coalesce
/// ---------------------------------------------------------------------------

let rec chunked_zero_fields (mh: MH.major_heap) (addr: U64.t) (n: nat)
  : GTot MH.major_heap (decreases n)
  =
  if n = 0 then mh
  else if U64.v addr + U64.v mword > heap_size then mh
  else if U64.v addr >= heap_size then mh
  else if U64.v addr % U64.v mword <> 0 then mh
  else
    let mh' = SpecMajorAlloc.major_write_word_or_same mh (addr <: hp_addr) 0UL in
    if U64.v addr + U64.v mword >= pow2 64 then
      mh'
    else
      chunked_zero_fields mh' (U64.uint_to_t (U64.v addr + U64.v mword)) (n - 1)

let chunked_flush_blue
    (mh: MH.major_heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (MH.major_heap & U64.t)
  =
  if run_words = 0 then (mh, fp)
  else if U64.v first_blue < U64.v mword ||
          U64.v first_blue >= heap_size ||
          U64.v first_blue % U64.v mword <> 0
  then (mh, fp)
  else
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    let wz : nat = run_words - 1 in
    if wz >= pow2 54 then (mh, fp)
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      let wz_u64 : Obj.wosize = U64.uint_to_t wz in
      let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
      let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then
        let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then
          let zero_start = U64.uint_to_t zero_start_nat in
          let mh3 = chunked_zero_fields mh2 zero_start (wz - 1) in
          (mh3, fb)
        else
          (mh2, fb)
      else
        (mh1, fp)
    end

let rec chunked_fused_aux
    (source: MH.major_heap) (work: MH.major_heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (MH.major_heap & U64.t) (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then
    chunked_flush_blue work first_blue run_words fp
  else begin
    assert (Seq.length objs > 0);
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    if chunked_is_black source obj then
      let (work', fp') = chunked_flush_blue work first_blue run_words fp in
      let work'' = chunked_make_white work' obj in
      chunked_fused_aux source work'' rest 0UL 0 fp'
    else
      let ws = U64.v (chunked_wosize_of_object source obj) in
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      chunked_fused_aux source work rest new_first (run_words + ws + 1) fp
  end

let rec chunked_fused_sweep_coalesce_chunks
    (source_chunks: MH.major_heap) (source: MH.major_heap)
    (work: MH.major_heap) (fp: U64.t)
  : GTot (MH.major_heap & U64.t) (decreases Seq.length source_chunks)
  =
  if Seq.length source_chunks = 0 then (work, fp)
  else begin
    assert (Seq.length source_chunks > 0);
    let c = Seq.head source_chunks in
    let (work', fp') =
      chunked_fused_aux source work (MH.objects_in_chunk c) 0UL 0 fp
    in
    chunked_fused_sweep_coalesce_chunks
      (Seq.tail source_chunks) source work' fp'
  end

let chunked_fused_sweep_coalesce (mh: MH.major_heap)
  : GTot (MH.major_heap & U64.t)
  = chunked_fused_sweep_coalesce_chunks mh mh mh 0UL

/// ---------------------------------------------------------------------------
/// Single-chunk compatibility
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always"
let chunked_read_header_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_read_header (MH.single_chunk_major_heap g) obj ==
       Some (read_word g (hd_address obj)))
  =
  hd_address_spec obj;
  assert (U64.v (hd_address obj) >= U64.v zero_addr);
  assert (U64.v (hd_address obj) + U64.v mword == U64.v obj);
  assert (U64.v (hd_address obj) + U64.v mword <= heap_size);
  MH.single_chunk_read_word_compat g (hd_address obj)

let chunked_color_of_object_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_color_of_object (MH.single_chunk_major_heap g) obj ==
       Some (Obj.color_of_object obj g))
  =
  chunked_read_header_single_chunk_compat g obj;
  Obj.color_of_object_spec obj g

let chunked_wosize_of_object_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_wosize_of_object (MH.single_chunk_major_heap g) obj ==
       Obj.wosize_of_object obj g)
  =
  chunked_read_header_single_chunk_compat g obj;
  Obj.wosize_of_object_spec obj g

let chunked_tag_of_object_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_tag_of_object (MH.single_chunk_major_heap g) obj ==
       Obj.tag_of_object obj g)
  =
  chunked_read_header_single_chunk_compat g obj;
  Obj.tag_of_object_spec obj g

let chunked_is_white_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_is_white (MH.single_chunk_major_heap g) obj ==
       Obj.is_white obj g)
  =
  chunked_color_of_object_single_chunk_compat g obj;
  Obj.is_white_iff obj g;
  match Obj.color_of_object obj g with
  | Header.White -> ()
  | Header.Gray -> ()
  | Header.Blue -> ()
  | Header.Black -> ()

let chunked_is_blue_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_is_blue (MH.single_chunk_major_heap g) obj ==
       Obj.is_blue obj g)
  =
  chunked_color_of_object_single_chunk_compat g obj;
  Obj.is_blue_iff obj g;
  match Obj.color_of_object obj g with
  | Header.White -> ()
  | Header.Gray -> ()
  | Header.Blue -> ()
  | Header.Black -> ()

let chunked_is_black_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_is_black (MH.single_chunk_major_heap g) obj ==
       Obj.is_black obj g)
  =
  chunked_color_of_object_single_chunk_compat g obj;
  Obj.is_black_iff obj g;
  match Obj.color_of_object obj g with
  | Header.White -> ()
  | Header.Gray -> ()
  | Header.Blue -> ()
  | Header.Black -> ()

let chunked_is_infix_single_chunk_compat
    (g: heap)
    (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (chunked_is_infix (MH.single_chunk_major_heap g) obj ==
       Obj.is_infix obj g)
  =
  chunked_tag_of_object_single_chunk_compat g obj;
  Obj.is_infix_spec obj g
#pop-options

/// ---------------------------------------------------------------------------
/// Unfolding lemmas
/// ---------------------------------------------------------------------------

let chunked_sweep_aux_empty (mh: MH.major_heap) (fp: U64.t)
  : Lemma (chunked_sweep_aux mh Seq.empty fp == (mh, fp))
  = ()

let chunked_sweep_aux_empty_length
    (mh: MH.major_heap) (objs: seq obj_addr) (fp: U64.t)
  : Lemma
      (requires Seq.length objs = 0)
      (ensures chunked_sweep_aux mh objs fp == (mh, fp))
  =
  ()

let chunked_sweep_step (mh: MH.major_heap) (fp: U64.t)
  : Lemma (chunked_sweep mh fp == chunked_sweep_chunks mh mh fp)
  = ()

let chunked_fused_sweep_coalesce_step (mh: MH.major_heap)
  : Lemma
      (chunked_fused_sweep_coalesce mh ==
       chunked_fused_sweep_coalesce_chunks mh mh mh 0UL)
  = ()

#push-options "--z3rlimit 1 --fuel 1 --ifuel 0 --split_queries always"
let chunked_zero_fields_zero (mh: MH.major_heap) (addr: U64.t)
  : Lemma (chunked_zero_fields mh addr 0 == mh)
  = ()

let chunked_zero_fields_no_room (mh: MH.major_heap) (addr: U64.t) (n: nat)
  : Lemma
      (requires n <> 0 /\ U64.v addr + U64.v mword > heap_size)
      (ensures chunked_zero_fields mh addr n == mh)
  = ()

let chunked_zero_fields_out_of_heap (mh: MH.major_heap) (addr: U64.t) (n: nat)
  : Lemma
      (requires n <> 0 /\
                ~(U64.v addr + U64.v mword > heap_size) /\
                U64.v addr >= heap_size)
      (ensures chunked_zero_fields mh addr n == mh)
  = ()

let chunked_zero_fields_unaligned (mh: MH.major_heap) (addr: U64.t) (n: nat)
  : Lemma
      (requires n <> 0 /\
                ~(U64.v addr + U64.v mword > heap_size) /\
                ~(U64.v addr >= heap_size) /\
                U64.v addr % U64.v mword <> 0)
      (ensures chunked_zero_fields mh addr n == mh)
  = ()

let chunked_zero_fields_step (mh: MH.major_heap) (addr: U64.t) (n: nat)
  : Lemma
      (requires n <> 0 /\
                ~(U64.v addr + U64.v mword > heap_size) /\
                ~(U64.v addr >= heap_size) /\
                ~(U64.v addr % U64.v mword <> 0))
      (ensures
        chunked_zero_fields mh addr n ==
        (let mh' =
          SpecMajorAlloc.major_write_word_or_same mh (addr <: hp_addr) 0UL in
         if U64.v addr + U64.v mword >= pow2 64 then mh'
         else
           chunked_zero_fields
             mh' (U64.uint_to_t (U64.v addr + U64.v mword)) (n - 1)))
  = ()

let chunked_flush_blue_empty
    (mh: MH.major_heap) (first_blue: U64.t) (fp: U64.t)
  : Lemma (chunked_flush_blue mh first_blue 0 fp == (mh, fp))
  = ()

let chunked_flush_blue_invalid
    (mh: MH.major_heap) (first_blue: U64.t)
    (run_words: nat{run_words > 0}) (fp: U64.t)
  : Lemma
      (requires (U64.v first_blue < U64.v mword \/
                 U64.v first_blue >= heap_size \/
                 U64.v first_blue % U64.v mword <> 0))
      (ensures chunked_flush_blue mh first_blue run_words fp == (mh, fp))
  = ()

let chunked_flush_blue_too_large
    (mh: MH.major_heap) (first_blue: U64.t)
    (run_words: nat{run_words > 0}) (fp: U64.t)
  : Lemma
      (requires ~(U64.v first_blue < U64.v mword) /\
                ~(U64.v first_blue >= heap_size) /\
                ~(U64.v first_blue % U64.v mword <> 0) /\
                run_words - 1 >= pow2 54)
      (ensures chunked_flush_blue mh first_blue run_words fp == (mh, fp))
  = ()

let chunked_flush_blue_step
    (mh: MH.major_heap) (first_blue: U64.t)
    (run_words: nat{run_words > 0}) (fp: U64.t)
  : Lemma
      (requires ~(U64.v first_blue < U64.v mword) /\
                ~(U64.v first_blue >= heap_size) /\
                ~(U64.v first_blue % U64.v mword <> 0) /\
                run_words - 1 < pow2 54 /\
                run_words - 1 < pow2 64)
      (ensures
        chunked_flush_blue mh first_blue run_words fp ==
        (let fb : obj_addr = first_blue in
         let hd = hd_address fb in
         let wz = run_words - 1 in
         let wz_u64 : Obj.wosize = U64.uint_to_t wz in
         let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
         let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
         if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then
           let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
           let zero_start_nat = U64.v fb + U64.v mword in
           if wz >= 2 && zero_start_nat < pow2 64 then
             let zero_start = U64.uint_to_t zero_start_nat in
             let mh3 = chunked_zero_fields mh2 zero_start (wz - 1) in
             (mh3, fb)
           else
             (mh2, fb)
         else
           (mh1, fp)))
  =   ()

let chunked_flush_blue_fst_zero_step
    (mh: MH.major_heap)
    (fb: obj_addr)
    (run_words: nat{run_words > 0})
    (fp: U64.t)
  : Lemma
      (requires ~(U64.v fb < U64.v mword) /\
                ~(U64.v fb >= heap_size) /\
                ~(U64.v fb % U64.v mword <> 0) /\
                run_words - 1 < pow2 54 /\
                run_words - 1 < pow2 64 /\
                run_words - 1 >= 2 /\
                U64.v (hd_address fb) + U64.v mword * 2 <= heap_size /\
                U64.v fb + U64.v mword < pow2 64)
      (ensures
        (let hd = hd_address fb in
         let wz : nat = run_words - 1 in
         let wz_u64 : Obj.wosize = U64.uint_to_t wz in
         let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
         let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
         let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
         let zero_start = U64.uint_to_t (U64.v fb + U64.v mword) in
         fst (chunked_flush_blue mh fb run_words fp) ==
         chunked_zero_fields mh2 zero_start (wz - 1)))
  =
  chunked_flush_blue_step mh fb run_words fp

let chunked_flush_blue_fst_link_step
    (mh: MH.major_heap)
    (fb: obj_addr)
    (run_words: nat{run_words > 0})
    (fp: U64.t)
  : Lemma
      (requires ~(U64.v fb < U64.v mword) /\
                ~(U64.v fb >= heap_size) /\
                ~(U64.v fb % U64.v mword <> 0) /\
                run_words - 1 < pow2 54 /\
                run_words - 1 < pow2 64 /\
                run_words - 1 >= 1 /\
                U64.v (hd_address fb) + U64.v mword * 2 <= heap_size /\
                ~(run_words - 1 >= 2 /\ U64.v fb + U64.v mword < pow2 64))
      (ensures
        (let hd = hd_address fb in
         let wz : nat = run_words - 1 in
         let wz_u64 : Obj.wosize = U64.uint_to_t wz in
         let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
         let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
         let mh2 = SpecMajorAlloc.major_write_word_or_same mh1 fb fp in
         fst (chunked_flush_blue mh fb run_words fp) == mh2))
  =
  chunked_flush_blue_step mh fb run_words fp

let chunked_flush_blue_fst_header_step
    (mh: MH.major_heap)
    (fb: obj_addr)
    (run_words: nat{run_words > 0})
    (fp: U64.t)
  : Lemma
      (requires ~(U64.v fb < U64.v mword) /\
                ~(U64.v fb >= heap_size) /\
                ~(U64.v fb % U64.v mword <> 0) /\
                run_words - 1 < pow2 54 /\
                run_words - 1 < pow2 64 /\
                ~(run_words - 1 >= 1 /\
                  U64.v (hd_address fb) + U64.v mword * 2 <= heap_size))
      (ensures
        (let hd = hd_address fb in
         let wz : nat = run_words - 1 in
         let wz_u64 : Obj.wosize = U64.uint_to_t wz in
         let hdr = Obj.makeHeader wz_u64 Header.Blue 0UL in
         let mh1 = SpecMajorAlloc.major_write_word_or_same mh hd hdr in
         fst (chunked_flush_blue mh fb run_words fp) == mh1))
  =
  chunked_flush_blue_step mh fb run_words fp

let chunked_set_object_color_some
    (mh: MH.major_heap) (obj: obj_addr) (color: Header.color_sem)
    (hdr: U64.t)
  : Lemma
      (requires chunked_read_header mh obj == Some hdr)
      (ensures
        chunked_set_object_color mh obj color ==
        SpecMajorAlloc.major_write_word_or_same
          mh (hd_address obj) (Obj.colorHeader hdr color))
  = ()

let chunked_set_object_color_none
    (mh: MH.major_heap) (obj: obj_addr) (color: Header.color_sem)
  : Lemma
      (requires chunked_read_header mh obj == None)
      (ensures chunked_set_object_color mh obj color == mh)
  = ()

let chunked_make_white_step (mh: MH.major_heap) (obj: obj_addr)
  : Lemma
      (chunked_make_white mh obj ==
       chunked_set_object_color mh obj Header.White)
  = ()

let chunked_make_blue_step (mh: MH.major_heap) (obj: obj_addr)
  : Lemma
      (chunked_make_blue mh obj ==
       chunked_set_object_color mh obj Header.Blue)
  = ()

let chunked_sweep_object_infix_step
    (mh: MH.major_heap) (obj: obj_addr) (fp: U64.t)
  : Lemma
      (requires chunked_is_infix mh obj)
      (ensures chunked_sweep_object mh obj fp == (mh, fp))
  = ()

let chunked_sweep_object_white_step
    (mh: MH.major_heap) (obj: obj_addr) (fp: U64.t)
  : Lemma
      (requires ~(chunked_is_infix mh obj) /\
                chunked_is_white mh obj)
      (ensures
        chunked_sweep_object mh obj fp ==
        (let ws = chunked_wosize_of_object mh obj in
         let hd = hd_address obj in
         let mh' =
           if U64.v ws > 0 && U64.v hd + U64.v mword * 2 <= heap_size
           then SpecMajorAlloc.major_write_word_or_same mh obj fp
           else mh
         in
         (chunked_make_blue mh' obj, obj)))
  = ()

let chunked_sweep_object_black_step
    (mh: MH.major_heap) (obj: obj_addr) (fp: U64.t)
  : Lemma
      (requires ~(chunked_is_infix mh obj) /\
                ~(chunked_is_white mh obj) /\
                chunked_is_black mh obj)
      (ensures
        chunked_sweep_object mh obj fp ==
        (chunked_make_white mh obj, fp))
  = ()

let chunked_sweep_object_other_step
    (mh: MH.major_heap) (obj: obj_addr) (fp: U64.t)
  : Lemma
      (requires ~(chunked_is_infix mh obj) /\
                ~(chunked_is_white mh obj) /\
                ~(chunked_is_black mh obj))
      (ensures chunked_sweep_object mh obj fp == (mh, fp))
  = ()
#pop-options

let chunked_sweep_aux_step
    (mh: MH.major_heap) (objs: seq obj_addr) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0)
      (ensures
        (let obj = Seq.head objs in
         let (mh', fp') = chunked_sweep_object mh obj fp in
         chunked_sweep_aux mh objs fp ==
         chunked_sweep_aux mh' (Seq.tail objs) fp'))
  = ()

let chunked_sweep_chunks_empty (work: MH.major_heap) (fp: U64.t)
  : Lemma (chunked_sweep_chunks Seq.empty work fp == (work, fp))
  = ()

let chunked_sweep_chunks_step
    (source_chunks work: MH.major_heap) (fp: U64.t)
  : Lemma
      (requires Seq.length source_chunks > 0)
      (ensures
        (let c = Seq.head source_chunks in
         let (work', fp') = chunked_sweep_aux work (MH.objects_in_chunk c) fp in
         chunked_sweep_chunks source_chunks work fp ==
         chunked_sweep_chunks (Seq.tail source_chunks) work' fp'))
  = ()

let chunked_fused_aux_empty
    (source work: MH.major_heap) (first_blue: U64.t) (run_words: nat)
    (fp: U64.t)
  : Lemma
      (chunked_fused_aux source work Seq.empty first_blue run_words fp ==
       chunked_flush_blue work first_blue run_words fp)
  = ()

let chunked_fused_aux_empty_length
    (source work: MH.major_heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
      (requires Seq.length objs = 0)
      (ensures
        chunked_fused_aux source work objs first_blue run_words fp ==
        chunked_flush_blue work first_blue run_words fp)
  =
  ()

let chunked_fused_aux_black_step
    (source work: MH.major_heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0 /\
                chunked_is_black source (Seq.head objs))
      (ensures
        (let obj = Seq.head objs in
         let rest = Seq.tail objs in
         let (work', fp') = chunked_flush_blue work first_blue run_words fp in
         let work'' = chunked_make_white work' obj in
         chunked_fused_aux source work objs first_blue run_words fp ==
         chunked_fused_aux source work'' rest 0UL 0 fp'))
  = ()

let chunked_fused_aux_nonblack_step
    (source work: MH.major_heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0 /\
                ~(chunked_is_black source (Seq.head objs)))
      (ensures
        (let obj = Seq.head objs in
         let rest = Seq.tail objs in
         let ws = U64.v (chunked_wosize_of_object source obj) in
         let new_first : U64.t = if run_words = 0 then obj else first_blue in
         chunked_fused_aux source work objs first_blue run_words fp ==
         chunked_fused_aux source work rest new_first (run_words + ws + 1) fp))
  = ()

let chunked_fused_sweep_coalesce_chunks_empty
    (source work: MH.major_heap) (fp: U64.t)
  : Lemma
      (chunked_fused_sweep_coalesce_chunks Seq.empty source work fp ==
       (work, fp))
  = ()

let chunked_fused_sweep_coalesce_chunks_step
    (source_chunks source work: MH.major_heap) (fp: U64.t)
  : Lemma
      (requires Seq.length source_chunks > 0)
      (ensures
        (let c = Seq.head source_chunks in
         let (work', fp') =
           chunked_fused_aux source work (MH.objects_in_chunk c) 0UL 0 fp
         in
         chunked_fused_sweep_coalesce_chunks source_chunks source work fp ==
         chunked_fused_sweep_coalesce_chunks
           (Seq.tail source_chunks) source work' fp'))
  = ()
