/// ---------------------------------------------------------------------------
/// GC.Gen.ChunkedCheney -- Chunked-major Cheney forwarding core
/// ---------------------------------------------------------------------------
///
/// This is the first chunked-major analogue of `GC.Gen.Cheney`: it mirrors the
/// one-step forwarding logic while replacing dense promotion with
/// `GC.Gen.ChunkedPromote`.

module GC.Gen.ChunkedCheney

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module GenInv = GC.Gen.HeapInvariant
module ChunkedPromote = GC.Gen.ChunkedPromote
module ChunkedUpdate = GC.Gen.ChunkedUpdate
module Dense = GC.Gen.Cheney

noeq
type chunked_cheney_state = {
  ccs_major : MH.major_heap;
  ccs_fp    : U64.t;
  ccs_fwd   : forwarding_map;
  ccs_queue : seq U64.t;
}

val single_chunk_cheney_state
  : cs:Dense.cheney_state -> GTot chunked_cheney_state

/// Forward a normal (non-infix) minor object using chunked-major promotion.
/// `fuel` is per-allocation search fuel, not a global allocation budget.
val chunked_cheney_forward_normal
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat -> GTot chunked_cheney_state

/// Try to forward `addr`, handling infix children through their parent.
val chunked_cheney_forward_one
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat -> GTot chunked_cheney_state

val chunked_cheney_forward_fields
  : minor:minor_state -> cs:chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    GTot chunked_cheney_state

val chunked_cheney_forward_roots
  : minor:minor_state -> cs:chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat ->
    GTot chunked_cheney_state

val chunked_cheney_scan
  : minor:minor_state -> cs:chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat ->
    GTot chunked_cheney_state

noeq
type chunked_promote_all_result = {
  major_final : MH.major_heap;
  fp_final    : U64.t;
  fwd_map     : forwarding_map;
}

noeq
type chunked_minor_collect_result = {
  cmc_major : MH.major_heap;
  cmc_fp    : U64.t;
  cmc_minor : minor_state;
  cmc_roots : seq U64.t;
  cmc_fwd   : forwarding_map;
}

val chunked_cheney_promote
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    GTot chunked_promote_all_result

/// Complete chunked minor collection = chunked Cheney promote + chunked pointer
/// update + root rewrite + minor reset.
val chunked_cheney_collect_spec
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    GTot chunked_minor_collect_result

val chunked_cheney_forward_normal_noop
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma (requires ~(Seq.mem addr (minor_objects minor)) \/
                    cs.ccs_fwd addr <> 0UL)
          (ensures chunked_cheney_forward_normal minor cs addr fuel == cs)

val chunked_cheney_forward_normal_noop_wz0
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma (requires Seq.mem addr (minor_objects minor) /\
                    cs.ccs_fwd addr = 0UL /\
                    minor_wosize minor addr = 0)
          (ensures chunked_cheney_forward_normal minor cs addr fuel == cs)

val chunked_cheney_forward_normal_noop_oom
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma
      (requires Seq.mem addr (minor_objects minor) /\
                cs.ccs_fwd addr = 0UL /\
                minor_wosize minor addr > 0 /\
                (ChunkedPromote.chunked_promote_object_with_fuel
                  minor cs.ccs_major addr cs.ccs_fp
                  (minor_wosize minor addr) fuel).new_addr = 0UL)
      (ensures chunked_cheney_forward_normal minor cs addr fuel == cs)

val chunked_cheney_forward_normal_success
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma
      (requires Seq.mem addr (minor_objects minor) /\
                cs.ccs_fwd addr = 0UL /\
                minor_wosize minor addr > 0 /\
                (ChunkedPromote.chunked_promote_object_with_fuel
                  minor cs.ccs_major addr cs.ccs_fp
                  (minor_wosize minor addr) fuel).new_addr <> 0UL)
      (ensures
        (let wz = minor_wosize minor addr in
         let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor cs.ccs_major addr cs.ccs_fp wz fuel in
         chunked_cheney_forward_normal minor cs addr fuel ==
         { ccs_major = res.major_out;
           ccs_fp    = res.fp_out;
           ccs_fwd   = extend_forwarding cs.ccs_fwd addr res.new_addr;
           ccs_queue = Seq.append cs.ccs_queue (Seq.create 1 addr) }))

val chunked_cheney_forward_normal_head_split_field_effect
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat -> j:nat -> field_addr:hp_addr ->
    Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        j < minor_wosize minor addr /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
         cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
        U64.v field_addr ==
         U64.v cs.ccs_fp + j * U64.v mword)
      (ensures
        (let cs' =
          chunked_cheney_forward_normal minor cs addr fuel in
         cs'.ccs_fwd addr == cs.ccs_fp /\
         MH.read_word_in_major cs'.ccs_major field_addr ==
          Some (minor_read_field minor addr j)))

val chunked_cheney_forward_normal_head_split_header_effect
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2)
      (ensures
        (let cs' =
           chunked_cheney_forward_normal minor cs addr fuel in
         cs'.ccs_fwd addr == cs.ccs_fp /\
         MH.well_formed_major_heap cs'.ccs_major /\
         Seq.mem (cs.ccs_fp <: obj_addr) (MH.major_objects cs'.ccs_major) /\
         (match MH.read_word_in_major cs'.ccs_major
            (hd_address (cs.ccs_fp <: obj_addr)) with
          | Some final_hdr ->
            U64.v (getWosize final_hdr) == minor_wosize minor addr /\
            getColor final_hdr == GC.Lib.Header.White /\
            U64.v (getTag final_hdr) == minor_tag minor addr
          | None -> False)))

val chunked_cheney_forward_normal_other_fwd
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    y:U64.t -> fuel:nat ->
    Lemma (requires y <> addr)
          (ensures
            (chunked_cheney_forward_normal minor cs addr fuel).ccs_fwd y ==
            cs.ccs_fwd y)

val chunked_cheney_forward_one_noop
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma (requires cs.ccs_fwd addr <> 0UL \/
                    (~(Seq.mem addr (minor_objects minor)) /\
                     ~(is_infix_in_minor minor addr)))
          (ensures chunked_cheney_forward_one minor cs addr fuel == cs)

val chunked_cheney_forward_one_normal
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma (requires cs.ccs_fwd addr = 0UL /\
                    ~(is_infix_in_minor minor addr))
          (ensures
            chunked_cheney_forward_one minor cs addr fuel ==
            chunked_cheney_forward_normal minor cs addr fuel)

val chunked_cheney_forward_one_normal_head_split_field_effect
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat -> j:nat -> field_addr:hp_addr ->
    Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        j < minor_wosize minor addr /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
        U64.v field_addr ==
          U64.v cs.ccs_fp + j * U64.v mword)
      (ensures
        (let cs' = chunked_cheney_forward_one minor cs addr fuel in
         cs'.ccs_fwd addr == cs.ccs_fp /\
         MH.read_word_in_major cs'.ccs_major field_addr ==
           Some (minor_read_field minor addr j)))

val chunked_cheney_forward_one_normal_head_split_header_effect
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2)
      (ensures
        (let cs' = chunked_cheney_forward_one minor cs addr fuel in
         cs'.ccs_fwd addr == cs.ccs_fp /\
         MH.well_formed_major_heap cs'.ccs_major /\
         Seq.mem (cs.ccs_fp <: obj_addr) (MH.major_objects cs'.ccs_major) /\
         (match MH.read_word_in_major cs'.ccs_major
           (hd_address (cs.ccs_fp <: obj_addr)) with
          | Some final_hdr ->
           U64.v (getWosize final_hdr) == minor_wosize minor addr /\
           getColor final_hdr == GC.Lib.Header.White /\
           U64.v (getTag final_hdr) == minor_tag minor addr
          | None -> False)))

val chunked_cheney_forward_one_infix
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma (requires cs.ccs_fwd addr = 0UL /\
                    is_infix_in_minor minor addr /\
                    U64.v addr >= U64.v (infix_parent minor addr))
          (ensures
            (let parent = infix_parent minor addr in
             let cs' = chunked_cheney_forward_normal minor cs parent fuel in
             let r = chunked_cheney_forward_one minor cs addr fuel in
             r.ccs_major == cs'.ccs_major /\
             r.ccs_fp == cs'.ccs_fp /\
             r.ccs_queue == cs'.ccs_queue))

val chunked_cheney_forward_one_infix_guard_pass
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma (requires cs.ccs_fwd addr = 0UL /\
                    is_infix_in_minor minor addr /\
                    (let parent = infix_parent minor addr in
                     let cs' =
                       chunked_cheney_forward_normal minor cs parent fuel in
                     cs'.ccs_fwd parent <> 0UL /\
                     U64.v addr >= U64.v parent /\
                     U64.v (cs'.ccs_fwd parent) +
                       (U64.v addr - U64.v parent) < heap_size))
          (ensures
            (let parent = infix_parent minor addr in
             let cs' = chunked_cheney_forward_normal minor cs parent fuel in
             let delta = U64.v addr - U64.v parent in
             let sum = U64.uint_to_t (U64.v (cs'.ccs_fwd parent) + delta) in
             let r = chunked_cheney_forward_one minor cs addr fuel in
             r.ccs_fwd == extend_forwarding cs'.ccs_fwd addr sum /\
             r.ccs_major == cs'.ccs_major /\
             r.ccs_fp == cs'.ccs_fp /\
             r.ccs_queue == cs'.ccs_queue))

val chunked_cheney_forward_one_infix_guard_fail
  : minor:minor_state -> cs:chunked_cheney_state -> addr:U64.t ->
    fuel:nat ->
    Lemma (requires cs.ccs_fwd addr = 0UL /\
                    is_infix_in_minor minor addr /\
                    (let parent = infix_parent minor addr in
                     let cs' =
                       chunked_cheney_forward_normal minor cs parent fuel in
                     ~(cs'.ccs_fwd parent <> 0UL &&
                       U64.v addr >= U64.v parent &&
                       U64.v (cs'.ccs_fwd parent) +
                         (U64.v addr - U64.v parent) < heap_size)))
          (ensures
            chunked_cheney_forward_one minor cs addr fuel ==
            chunked_cheney_forward_normal minor cs
              (infix_parent minor addr) fuel)

val chunked_cheney_forward_fields_base
  : minor:minor_state -> cs:chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    Lemma (requires idx >= wosize)
          (ensures
            chunked_cheney_forward_fields
              minor cs parent idx wosize alloc_fuel == cs)

val chunked_cheney_forward_fields_step
  : minor:minor_state -> cs:chunked_cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat -> alloc_fuel:nat ->
    Lemma (requires idx < wosize)
          (ensures
            chunked_cheney_forward_fields
              minor cs parent idx wosize alloc_fuel ==
            (let field_val = to_minor_offset (minor_read_field minor parent idx) in
             let cs' =
               chunked_cheney_forward_one minor cs field_val alloc_fuel in
             chunked_cheney_forward_fields
               minor cs' parent (idx + 1) wosize alloc_fuel))

val chunked_cheney_forward_roots_base
  : minor:minor_state -> cs:chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat ->
    Lemma (requires idx >= Seq.length roots)
          (ensures
            chunked_cheney_forward_roots
              minor cs roots idx alloc_fuel == cs)

val chunked_cheney_forward_roots_step
  : minor:minor_state -> cs:chunked_cheney_state ->
    roots:seq U64.t -> idx:nat -> alloc_fuel:nat ->
    Lemma (requires idx < Seq.length roots)
          (ensures
            chunked_cheney_forward_roots
              minor cs roots idx alloc_fuel ==
            (let r = Seq.index roots idx in
             let cs' = chunked_cheney_forward_one minor cs r alloc_fuel in
             chunked_cheney_forward_roots minor cs' roots (idx + 1) alloc_fuel))

val chunked_cheney_scan_base
  : minor:minor_state -> cs:chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat ->
    Lemma (requires scan_fuel = 0 \/ scan >= Seq.length cs.ccs_queue)
          (ensures chunked_cheney_scan minor cs scan scan_fuel alloc_fuel == cs)

val chunked_cheney_scan_step
  : minor:minor_state -> cs:chunked_cheney_state ->
    scan:nat -> scan_fuel:nat -> alloc_fuel:nat ->
    Lemma (requires scan_fuel > 0 /\ scan < Seq.length cs.ccs_queue)
          (ensures
            chunked_cheney_scan minor cs scan scan_fuel alloc_fuel ==
            (let obj = Seq.index cs.ccs_queue scan in
             let wz = minor_wosize minor obj in
             let cs' =
               chunked_cheney_forward_fields minor cs obj 0 wz alloc_fuel in
             chunked_cheney_scan minor cs' (scan + 1) (scan_fuel - 1)
               alloc_fuel))

val chunked_cheney_promote_equation
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
      (ensures
        (let cs0 : chunked_cheney_state =
           { ccs_major = major;
             ccs_fp = fp;
             ccs_fwd = empty_forwarding;
             ccs_queue = Seq.empty } in
         let cs1 =
           chunked_cheney_forward_roots minor cs0 roots 0 alloc_fuel in
         let cs2 =
           chunked_cheney_scan
             minor cs1 0 (Dense.cheney_fuel minor) alloc_fuel in
         chunked_cheney_promote minor major fp roots alloc_fuel ==
         { major_final = cs2.ccs_major;
           fp_final = cs2.ccs_fp;
           fwd_map = cs2.ccs_fwd }))

val chunked_cheney_collect_spec_equation
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat ->
    Lemma
      (ensures
        (let prom = chunked_cheney_promote minor major fp roots alloc_fuel in
         chunked_cheney_collect_spec minor major fp roots alloc_fuel ==
         { cmc_major =
             ChunkedUpdate.chunked_update_major_pointers
               prom.major_final prom.fwd_map;
           cmc_fp    = prom.fp_final;
           cmc_minor = minor_reset minor;
           cmc_roots = rewrite_roots roots prom.fwd_map;
           cmc_fwd   = prom.fwd_map }))

val chunked_cheney_forward_normal_default_single_chunk_compat
  : minor:minor_state -> cs:Dense.cheney_state -> addr:U64.t ->
    Lemma
      (ensures
        chunked_cheney_forward_normal
          minor (single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        single_chunk_cheney_state
          (Dense.cheney_forward_normal minor cs addr))

val chunked_cheney_forward_one_default_single_chunk_compat
  : minor:minor_state -> cs:Dense.cheney_state -> addr:U64.t ->
    Lemma
      (ensures
        chunked_cheney_forward_one
          minor (single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        single_chunk_cheney_state
          (Dense.cheney_forward_one minor cs addr))

val chunked_cheney_forward_fields_default_single_chunk_compat
  : minor:minor_state -> cs:Dense.cheney_state ->
    parent:U64.t -> idx:nat -> wosize:nat ->
    Lemma
      (ensures
        chunked_cheney_forward_fields
          minor (single_chunk_cheney_state cs) parent idx wosize
          SpecAlloc.alloc_search_fuel ==
        single_chunk_cheney_state
          (Dense.cheney_forward_fields minor cs parent idx wosize))

val chunked_cheney_forward_roots_default_single_chunk_compat
  : minor:minor_state -> cs:Dense.cheney_state ->
    roots:seq U64.t -> idx:nat ->
    Lemma
      (ensures
        chunked_cheney_forward_roots
          minor (single_chunk_cheney_state cs) roots idx
          SpecAlloc.alloc_search_fuel ==
        single_chunk_cheney_state
          (Dense.cheney_forward_roots minor cs roots idx))

val chunked_cheney_scan_default_single_chunk_compat
  : minor:minor_state -> cs:Dense.cheney_state ->
    scan:nat -> scan_fuel:nat ->
    Lemma
      (ensures
        chunked_cheney_scan
          minor (single_chunk_cheney_state cs) scan scan_fuel
          SpecAlloc.alloc_search_fuel ==
        single_chunk_cheney_state
          (Dense.cheney_scan minor cs scan scan_fuel))

val chunked_cheney_promote_default_single_chunk_compat
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
      (ensures
        (let chunked =
           chunked_cheney_promote
             minor (MH.single_chunk_major_heap major) fp roots
             SpecAlloc.alloc_search_fuel in
         let dense = Dense.cheney_promote minor major fp roots in
         chunked.major_final == MH.single_chunk_major_heap dense.major_final /\
         chunked.fp_final == dense.fp_final /\
         chunked.fwd_map == dense.fwd_map))

val chunked_cheney_collect_default_single_chunk_compat
  : minor:minor_state -> major:heap -> fp:U64.t -> roots:seq U64.t ->
    Lemma
      (ensures
        (let chunked =
           chunked_cheney_collect_spec
             minor (MH.single_chunk_major_heap major) fp roots
             SpecAlloc.alloc_search_fuel in
         let dense = Dense.cheney_collect_spec minor major fp roots in
         chunked.cmc_major == MH.single_chunk_major_heap dense.mc_major /\
         chunked.cmc_fp == dense.mc_fp /\
         chunked.cmc_minor == dense.mc_minor /\
         chunked.cmc_roots == dense.mc_roots /\
         chunked.cmc_fwd == dense.mc_fwd))
