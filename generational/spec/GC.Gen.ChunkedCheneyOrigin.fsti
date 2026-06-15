module GC.Gen.ChunkedCheneyOrigin

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module ChunkedCheney = GC.Gen.ChunkedCheney

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
