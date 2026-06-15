module GC.Gen.ChunkedCheneyOrigin

open FStar.Seq
module U64 = FStar.UInt64
module Classical = FStar.Classical
module IndDesc = FStar.IndefiniteDescription

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocSplitOrigin = GC.Spec.MajorAllocator.SplitOrigin
module GenInv = GC.Gen.HeapInvariant
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedPromote = GC.Gen.ChunkedPromote
module CP = GC.Gen.CheneyPreservation

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

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 1"
let chunked_cheney_forward_normal_success_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (addr: U64.t) (fuel: nat)
  : Lemma
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
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2)
      (ensures
        chunked_nonblue_origin_inv minor major0
          (ChunkedCheney.chunked_cheney_forward_normal
            minor cs addr fuel))
  =
  let wz = minor_wosize minor addr in
  CP.chunked_promote_object_head_split_preserves_chunked_alloc_shape
    minor cs.ccs_major addr cs.ccs_fp wz fuel;
  GenInv.chunked_major_alloc_shape_elim cs.ccs_major cs.ccs_fp fuel;
  SpecMajorAllocSplitOrigin.major_alloc_head_split_nonblue_origin
    cs.ccs_major cs.ccs_fp wz fuel;
  ChunkedCheney.chunked_cheney_forward_normal_success minor cs addr fuel;
  let res =
    ChunkedPromote.chunked_promote_object_with_fuel
      minor cs.ccs_major addr cs.ccs_fp wz fuel in
  let alloc_res =
    SpecMajorAlloc.major_alloc_spec_with_fuel
      cs.ccs_major cs.ccs_fp wz fuel in
  let cs' = ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
  assert (res.new_addr == cs.ccs_fp);
  assert (cs'.ccs_major == res.major_out);
  assert (cs'.ccs_fwd == extend_forwarding cs.ccs_fwd addr res.new_addr);
  assert (GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel);
  GenInv.chunked_major_alloc_shape_elim res.major_out res.fp_out fuel;
  assert (MH.well_formed_major_heap cs'.ccs_major);
  SpecMajorAlloc.major_fl_above_zero_current cs.ccs_major cs.ccs_fp fuel;
  assert (U64.v cs.ccs_fp >= U64.v zero_addr + U64.v mword);
  assert (U64.v cs.ccs_fp >= U64.v mword);
  assert (U64.v cs.ccs_fp < heap_size);
  assert (U64.v cs.ccs_fp % U64.v mword == 0);
  let fp_obj : obj_addr = cs.ccs_fp in
  reveal_opaque (`%chunked_nonblue_origin_inv) chunked_nonblue_origin_inv;
  let aux (src: obj_addr)
    : Lemma
        (requires
          Seq.mem src (MH.major_objects cs'.ccs_major) /\
          ~(GenInv.chunked_is_blue cs'.ccs_major src) /\
          ~(Seq.mem src (MH.major_objects major0) /\
            ~(GenInv.chunked_is_blue major0 src)))
        (ensures
          exists (x: U64.t).
            cs'.ccs_fwd x == src /\
            Seq.mem x (minor_objects minor) /\
            ~(is_infix_in_minor minor x) /\
            minor_wosize minor x > 0)
    =
    MH.major_objects_member_header_read_some cs'.ccs_major src;
    match MH.read_word_in_major cs'.ccs_major (hd_address src) with
    | None -> assert False
    | Some hdr ->
      GenInv.chunked_is_blue_header cs'.ccs_major src hdr;
      assert (Obj.getColor hdr <> Header.Blue);
      assert (Seq.mem src (MH.major_objects res.major_out));
      assert (MH.major_objects res.major_out ==
              MH.major_objects alloc_res.major_alloc_out);
      assert (Seq.mem src (MH.major_objects alloc_res.major_alloc_out));
      if src = fp_obj then begin
        assert (cs'.ccs_fwd addr == src);
        Classical.exists_intro
          (fun (x: U64.t) ->
            cs'.ccs_fwd x == src /\
            Seq.mem x (minor_objects minor) /\
            ~(is_infix_in_minor minor x) /\
            minor_wosize minor x > 0)
          addr
      end else begin
        assert (src <> fp_obj);
        assert (MH.read_word_in_major res.major_out (hd_address src) ==
                MH.read_word_in_major alloc_res.major_alloc_out
                  (hd_address src));
        assert (MH.read_word_in_major
                  alloc_res.major_alloc_out (hd_address src) == Some hdr);
        assert (src == fp_obj \/
                (Seq.mem src (MH.major_objects cs.ccs_major) /\
                 (exists (old_hdr:U64.t).
                    MH.read_word_in_major cs.ccs_major (hd_address src) ==
                      Some old_hdr /\
                    Obj.getColor old_hdr <> Header.Blue)));
        assert (Seq.mem src (MH.major_objects cs.ccs_major));
        match MH.read_word_in_major cs.ccs_major (hd_address src) with
        | None -> assert False
        | Some old_hdr ->
          assert (Obj.getColor old_hdr <> Header.Blue);
          GenInv.chunked_is_blue_header cs.ccs_major src old_hdr;
          assert (~(GenInv.chunked_is_blue cs.ccs_major src));
          chunked_nonblue_origin_inv_elim minor major0 cs src;
          let goal =
            exists (x: U64.t).
              cs'.ccs_fwd x == src /\
              Seq.mem x (minor_objects minor) /\
              ~(is_infix_in_minor minor x) /\
              minor_wosize minor x > 0 in
          assert (exists (x: U64.t).
            cs.ccs_fwd x == src /\
            Seq.mem x (minor_objects minor) /\
            ~(is_infix_in_minor minor x) /\
            minor_wosize minor x > 0);
          let x = IndDesc.indefinite_description_ghost U64.t
           (fun x ->
             cs.ccs_fwd x == src /\
             Seq.mem x (minor_objects minor) /\
             ~(is_infix_in_minor minor x) /\
             minor_wosize minor x > 0) in
          assert (cs.ccs_fwd x == src /\
                 Seq.mem x (minor_objects minor) /\
                 ~(is_infix_in_minor minor x) /\
                 minor_wosize minor x > 0);
          assert (cs.ccs_fwd x == src);
          assert (Seq.mem x (minor_objects minor));
          assert (~(is_infix_in_minor minor x));
          assert (minor_wosize minor x > 0);
          if x = addr then begin
            assert (cs.ccs_fwd addr == 0UL);
            assert (src == 0UL);
            assert (U64.v src == 0);
            assert_norm (U64.v mword == 8);
            assert (U64.v mword > 0);
            assert (U64.v src >= U64.v mword);
            assert False
          end else begin
            ChunkedCheney.chunked_cheney_forward_normal_other_fwd
              minor cs addr x fuel;
            assert (cs'.ccs_fwd x == src);
            Classical.exists_intro
              (fun (y: U64.t) ->
                cs'.ccs_fwd y == src /\
                Seq.mem y (minor_objects minor) /\
                ~(is_infix_in_minor minor y) /\
                minor_wosize minor y > 0)
              x
          end
      end
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options
