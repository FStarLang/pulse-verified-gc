module GC.Gen.ChunkedCheneyOrigin

open FStar.Seq
module U64 = FStar.UInt64
module Classical = FStar.Classical

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedPromote = GC.Gen.ChunkedPromote

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
[@"opaque_to_smt"]
let chunked_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (MH.major_objects cs.ccs_major) /\
    ~(GenInv.chunked_is_blue cs.ccs_major obj) /\
    ~(Seq.mem obj (MH.major_objects major0) /\
      ~(GenInv.chunked_is_blue major0 obj)) ==>
    exists (x: U64.t).
      cs.ccs_fwd x == obj /\
      Seq.mem x (minor_objects minor) /\
      ~(is_infix_in_minor minor x) /\
      minor_wosize minor x > 0

let chunked_nonblue_origin_inv_elim
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (obj: obj_addr)
  : Lemma
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
  =
  reveal_opaque (`%chunked_nonblue_origin_inv) chunked_nonblue_origin_inv

let chunked_nonblue_origin_inv_init
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  : Lemma
      (ensures
        chunked_nonblue_origin_inv minor major
          { ChunkedCheney.ccs_major = major;
            ChunkedCheney.ccs_fp = fp;
            ChunkedCheney.ccs_fwd = empty_forwarding;
            ChunkedCheney.ccs_queue = Seq.empty })
  =
  let cs0 =
    { ChunkedCheney.ccs_major = major;
      ChunkedCheney.ccs_fp = fp;
      ChunkedCheney.ccs_fwd = empty_forwarding;
      ChunkedCheney.ccs_queue = Seq.empty } in
  reveal_opaque (`%chunked_nonblue_origin_inv) chunked_nonblue_origin_inv;
  let aux (obj: obj_addr)
    : Lemma
        (ensures
          Seq.mem obj (MH.major_objects cs0.ccs_major) /\
          ~(GenInv.chunked_is_blue cs0.ccs_major obj) /\
          ~(Seq.mem obj (MH.major_objects major) /\
            ~(GenInv.chunked_is_blue major obj)) ==>
          exists (x: U64.t).
            cs0.ccs_fwd x == obj /\
            Seq.mem x (minor_objects minor) /\
            ~(is_infix_in_minor minor x) /\
            minor_wosize minor x > 0)
    =
    ()
  in
  Classical.forall_intro aux

let chunked_cheney_forward_normal_noop_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        chunked_nonblue_origin_inv minor major0 cs /\
        (~(Seq.mem addr (minor_objects minor)) \/ cs.ccs_fwd addr <> 0UL))
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))
  =
  ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel

let chunked_cheney_forward_normal_noop_wz0_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        chunked_nonblue_origin_inv minor major0 cs /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr = 0)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))
  =
  ChunkedCheney.chunked_cheney_forward_normal_noop_wz0 minor cs addr fuel

let chunked_cheney_forward_normal_noop_oom_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        chunked_nonblue_origin_inv minor major0 cs /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr > 0 /\
        (ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp
          (minor_wosize minor addr) fuel).new_addr = 0UL)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))
  =
  ChunkedCheney.chunked_cheney_forward_normal_noop_oom minor cs addr fuel
#pop-options
