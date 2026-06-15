module GC.Gen.ChunkedCheneyOrigin

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module GenInv = GC.Gen.HeapInvariant
module ChunkedCheney = GC.Gen.ChunkedCheney
module CP = GC.Gen.CheneyPreservation

/// Every non-blue object newly appearing in the current Cheney major heap is
/// the forwarding target of an ordinary positive-size minor object.
[@"opaque_to_smt"]
val chunked_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> Tot prop

val chunked_nonblue_origin_inv_elim
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> obj:obj_addr ->
    Lemma
      (requires
        chunked_nonblue_origin_inv minor major0 cs /\
        Seq.mem obj (MH.major_objects cs.ccs_major) /\
        ~(GenInv.chunked_is_blue cs.ccs_major obj) /\
        ~(Seq.mem obj (MH.major_objects major0) /\
          ~(GenInv.chunked_is_blue major0 obj)))
      (ensures
        exists (x: U64.t).
          cs.ccs_fwd x == obj /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0)

val chunked_nonblue_origin_inv_init
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    Lemma
      (ensures
        chunked_nonblue_origin_inv minor major
          { ChunkedCheney.ccs_major = major;
            ChunkedCheney.ccs_fp = fp;
            ChunkedCheney.ccs_fwd = empty_forwarding;
            ChunkedCheney.ccs_queue = Seq.empty })

val chunked_cheney_forward_normal_noop_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> addr:U64.t -> fuel:nat ->
    Lemma
      (requires
        chunked_nonblue_origin_inv minor major0 cs /\
        (~(Seq.mem addr (minor_objects minor)) \/ cs.ccs_fwd addr <> 0UL))
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))

val chunked_cheney_forward_normal_noop_wz0_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> addr:U64.t -> fuel:nat ->
    Lemma
      (requires
        chunked_nonblue_origin_inv minor major0 cs /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr = 0)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))

val chunked_cheney_forward_normal_noop_oom_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> addr:U64.t -> fuel:nat ->
    Lemma
      (requires
        chunked_nonblue_origin_inv minor major0 cs /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr > 0 /\
        (GC.Gen.ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp
          (minor_wosize minor addr) fuel).new_addr = 0UL)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))

val chunked_cheney_forward_normal_success_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> addr:U64.t -> fuel:nat ->
    Lemma
      (requires
        fuel > 1 /\
        chunked_nonblue_origin_inv minor major0 cs /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        Seq.mem addr (minor_objects minor) /\
        ~(is_infix_in_minor minor addr) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr > 0 /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
          minor_wosize minor addr + 2)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))

val chunked_cheney_forward_normal_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> addr:U64.t -> fuel:nat ->
    Lemma
      (requires
        fuel > 1 /\
        chunked_nonblue_origin_inv minor major0 cs /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
           ~(is_infix_in_minor minor addr) /\
           cs.ccs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2))
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))

val chunked_cheney_forward_one_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> addr:U64.t -> fuel:nat ->
    Lemma
      (requires
        fuel > 1 /\
        minor_wf minor /\
        minor_infix_wf minor /\
        chunked_nonblue_origin_inv minor major0 cs /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         ~(is_infix_in_minor minor addr) /\
         minor_wosize minor addr > 0 ==>
           cs.ccs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2) /\
        (cs.ccs_fwd addr = 0UL /\
         is_infix_in_minor minor addr ==>
           (let parent = infix_parent minor addr in
            Seq.mem parent (minor_objects minor) /\
            cs.ccs_fwd parent = 0UL /\
            minor_wosize minor parent > 0 ==>
              cs.ccs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= minor_wosize minor parent + 2)))
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel))

val chunked_cheney_forward_one_budget_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> addr:U64.t ->
    fuel:nat -> remaining:nat ->
    Lemma
      (requires
        fuel > 1 /\
        minor_wf minor /\
        minor_infix_wf minor /\
        chunked_nonblue_origin_inv minor major0 cs /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        CP.chunked_cheney_forward_one_budget_ready
          minor cs addr remaining)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel))

val chunked_cheney_forward_roots_budget_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> roots:seq U64.t ->
    idx:nat -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        minor_wf minor /\
        minor_infix_wf minor /\
        chunked_nonblue_origin_inv minor major0 cs /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CP.chunked_cheney_forward_roots_budget_ready
          minor cs roots idx alloc_fuel remaining)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots idx alloc_fuel))

val chunked_cheney_forward_fields_budget_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> parent:U64.t ->
    idx:nat -> wosize:nat -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        minor_wf minor /\
        minor_infix_wf minor /\
        chunked_nonblue_origin_inv minor major0 cs /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CP.chunked_cheney_forward_fields_budget_ready
          minor cs parent idx wosize alloc_fuel remaining)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel))

val chunked_cheney_scan_budget_preserves_nonblue_origin_inv
  : minor:minor_state -> major0:MH.major_heap ->
    cs:ChunkedCheney.chunked_cheney_state -> scan:nat ->
    scan_fuel:nat -> alloc_fuel:nat -> remaining:nat ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        minor_wf minor /\
        minor_infix_wf minor /\
        chunked_nonblue_origin_inv minor major0 cs /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CP.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel))

val chunked_cheney_promote_budget_nonblue_origin
  : minor:minor_state -> major:MH.major_heap -> fp:U64.t ->
    roots:seq U64.t -> alloc_fuel:nat -> remaining:nat -> src:obj_addr ->
    Lemma
      (requires
        alloc_fuel > 1 /\
        minor_wf minor /\
        minor_infix_wf minor /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         Seq.mem src (MH.major_objects res.major_final) /\
         ~(GenInv.chunked_is_blue res.major_final src) /\
         ~(Seq.mem src (MH.major_objects major) /\
           ~(GenInv.chunked_is_blue major src))))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         exists (x: U64.t).
           res.fwd_map x == src /\
           Seq.mem x (minor_objects minor) /\
           ~(is_infix_in_minor minor x) /\
           minor_wosize minor x > 0))
