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
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module ChunkedPromote = GC.Gen.ChunkedPromote
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
