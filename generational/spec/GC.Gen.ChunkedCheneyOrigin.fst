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
module DenseCheney = GC.Gen.Cheney
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

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
let chunked_cheney_forward_normal_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (addr: U64.t) (fuel: nat)
  : Lemma
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
  =
  if ~(Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    chunked_cheney_forward_normal_noop_preserves_nonblue_origin_inv
      minor major0 cs addr fuel
  else if minor_wosize minor addr = 0 then
    chunked_cheney_forward_normal_noop_wz0_preserves_nonblue_origin_inv
      minor major0 cs addr fuel
  else begin
    assert (Seq.mem addr (minor_objects minor));
    assert (cs.ccs_fwd addr = 0UL);
    assert (minor_wosize minor addr > 0);
    assert (~(is_infix_in_minor minor addr));
    assert (cs.ccs_fp <> 0UL);
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2);
    chunked_cheney_forward_normal_success_preserves_nonblue_origin_inv
      minor major0 cs addr fuel
  end
#pop-options


#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 1"
let chunked_cheney_forward_one_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (addr: U64.t) (fuel: nat)
  : Lemma
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
  =
  if cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr fuel
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    infix_parent_value minor addr;
    infix_parent_in_minor_objects minor addr;
    let parent = infix_parent minor addr in
    minor_objects_not_infix minor parent;
    assert (~(is_infix_in_minor minor parent));
    assert (Seq.mem parent (minor_objects minor));
    assert (Seq.mem parent (minor_objects minor) /\
            cs.ccs_fwd parent = 0UL /\
            minor_wosize minor parent > 0 ==>
              ~(is_infix_in_minor minor parent) /\
              cs.ccs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= minor_wosize minor parent + 2);
    chunked_cheney_forward_normal_preserves_nonblue_origin_inv
      minor major0 cs parent fuel;
    let cs' = ChunkedCheney.chunked_cheney_forward_normal minor cs parent fuel in
    let r = ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
    if not (cs'.ccs_fwd parent <> 0UL &&
            U64.v addr >= U64.v parent &&
            U64.v (cs'.ccs_fwd parent) +
              (U64.v addr - U64.v parent) < heap_size) then begin
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr fuel;
      assert (r == cs')
    end else begin
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr fuel;
      reveal_opaque (`%chunked_nonblue_origin_inv) chunked_nonblue_origin_inv;
      let aux (src: obj_addr)
        : Lemma
            (requires
              Seq.mem src (MH.major_objects r.ccs_major) /\
              ~(GenInv.chunked_is_blue r.ccs_major src) /\
              ~(Seq.mem src (MH.major_objects major0) /\
                ~(GenInv.chunked_is_blue major0 src)))
            (ensures
              exists (x: U64.t).
                r.ccs_fwd x == src /\
                Seq.mem x (minor_objects minor) /\
                ~(is_infix_in_minor minor x) /\
                minor_wosize minor x > 0)
        =
        assert (r.ccs_major == cs'.ccs_major);
        assert (Seq.mem src (MH.major_objects cs'.ccs_major));
        assert (~(GenInv.chunked_is_blue cs'.ccs_major src));
        assert (chunked_nonblue_origin_inv minor major0 cs');
        chunked_nonblue_origin_inv_elim minor major0 cs' src;
        assert (exists (x: U64.t).
          cs'.ccs_fwd x == src /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0);
        let x = IndDesc.indefinite_description_ghost U64.t
          (fun x ->
            cs'.ccs_fwd x == src /\
            Seq.mem x (minor_objects minor) /\
            ~(is_infix_in_minor minor x) /\
            minor_wosize minor x > 0) in
        assert (cs'.ccs_fwd x == src);
        assert (Seq.mem x (minor_objects minor));
        assert (~(is_infix_in_minor minor x));
        assert (minor_wosize minor x > 0);
        if x = addr then begin
          assert (is_infix_in_minor minor x);
          assert False
        end;
        assert (x <> addr);
        ChunkedCheney.chunked_cheney_forward_one_infix_fwd
          minor cs addr x fuel;
        assert (r.ccs_fwd x == src);
        Classical.exists_intro
          (fun (y: U64.t) ->
            r.ccs_fwd y == src /\
            Seq.mem y (minor_objects minor) /\
            ~(is_infix_in_minor minor y) /\
            minor_wosize minor y > 0)
          x
      in
      Classical.forall_intro (Classical.move_requires aux)
    end
  end else begin
    assert (cs.ccs_fwd addr = 0UL);
    assert (~(is_infix_in_minor minor addr));
    ChunkedCheney.chunked_cheney_forward_one_normal minor cs addr fuel;
    assert (Seq.mem addr (minor_objects minor) /\
            cs.ccs_fwd addr = 0UL /\
            minor_wosize minor addr > 0 ==>
              ~(is_infix_in_minor minor addr) /\
              cs.ccs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2);
    chunked_cheney_forward_normal_preserves_nonblue_origin_inv
      minor major0 cs addr fuel
  end
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 1"
let chunked_cheney_forward_one_budget_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (addr: U64.t)
  (fuel remaining: nat)
  : Lemma
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
  =
  CP.chunked_cheney_forward_one_budget_ready_elim
    minor cs addr remaining;
  assert (remaining > 0);
  assert (Seq.mem addr (minor_objects minor) /\
          cs.ccs_fwd addr = 0UL /\
          ~(is_infix_in_minor minor addr) /\
          minor_wosize minor addr > 0 ==>
            cs.ccs_fp <> 0UL /\
            SpecMajorAlloc.major_fl_head_wosize
              cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2);
  assert (cs.ccs_fwd addr = 0UL /\
          is_infix_in_minor minor addr ==>
            (let parent = infix_parent minor addr in
             Seq.mem parent (minor_objects minor) /\
             cs.ccs_fwd parent = 0UL /\
             minor_wosize minor parent > 0 ==>
               cs.ccs_fp <> 0UL /\
               SpecMajorAlloc.major_fl_head_wosize
                 cs.ccs_major cs.ccs_fp >= minor_wosize minor parent + 2));
  chunked_cheney_forward_one_preserves_nonblue_origin_inv
    minor major0 cs addr fuel
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let rec chunked_cheney_forward_roots_budget_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (roots: seq U64.t)
  (idx alloc_fuel remaining: nat)
  : Lemma
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
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    CP.chunked_cheney_forward_roots_budget_ready_step
      minor cs roots idx alloc_fuel remaining;
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs r alloc_fuel in
    assert (CP.chunked_cheney_forward_one_budget_ready
              minor cs r remaining);
    assert (CP.chunked_cheney_forward_roots_budget_ready
              minor cs' roots (idx + 1) alloc_fuel remaining);
    chunked_cheney_forward_one_budget_preserves_nonblue_origin_inv
      minor major0 cs r alloc_fuel remaining;
    CP.chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
      minor cs r alloc_fuel remaining;
    chunked_cheney_forward_roots_budget_preserves_nonblue_origin_inv
      minor major0 cs' roots (idx + 1) alloc_fuel remaining
  end

let rec chunked_cheney_forward_fields_budget_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (parent: U64.t)
  (idx wosize alloc_fuel remaining: nat)
  : Lemma
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
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    CP.chunked_cheney_forward_fields_budget_ready_step
      minor cs parent idx wosize alloc_fuel remaining;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one
        minor cs field_val alloc_fuel in
    assert (CP.chunked_cheney_forward_one_budget_ready
              minor cs field_val remaining);
    assert (CP.chunked_cheney_forward_fields_budget_ready
              minor cs' parent (idx + 1) wosize alloc_fuel remaining);
    chunked_cheney_forward_one_budget_preserves_nonblue_origin_inv
      minor major0 cs field_val alloc_fuel remaining;
    CP.chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
      minor cs field_val alloc_fuel remaining;
    chunked_cheney_forward_fields_budget_preserves_nonblue_origin_inv
      minor major0 cs' parent (idx + 1) wosize alloc_fuel remaining
  end

let rec chunked_cheney_scan_budget_preserves_nonblue_origin_inv
  (minor: minor_state) (major0: MH.major_heap)
  (cs: ChunkedCheney.chunked_cheney_state) (scan scan_fuel alloc_fuel remaining: nat)
  : Lemma
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
      (decreases scan_fuel)
  =
  if scan_fuel = 0 || scan >= Seq.length cs.ccs_queue then
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel
  else begin
    ChunkedCheney.chunked_cheney_scan_step
      minor cs scan scan_fuel alloc_fuel;
    CP.chunked_cheney_scan_budget_ready_step
      minor cs scan scan_fuel alloc_fuel remaining;
    assert (scan_fuel > 0);
    let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
    let obj = Seq.index cs.ccs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_fields
        minor cs obj 0 wz alloc_fuel in
    assert (CP.chunked_cheney_forward_fields_budget_ready
              minor cs obj 0 wz alloc_fuel remaining);
    assert (CP.chunked_cheney_scan_budget_ready
              minor cs' (scan + 1) fuel' alloc_fuel remaining);
    chunked_cheney_forward_fields_budget_preserves_nonblue_origin_inv
      minor major0 cs obj 0 wz alloc_fuel remaining;
    CP.chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
      minor cs obj 0 wz alloc_fuel remaining;
    chunked_cheney_scan_budget_preserves_nonblue_origin_inv
      minor major0 cs' (scan + 1) fuel' alloc_fuel remaining
  end
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_cheney_promote_budget_nonblue_origin
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat) (src: obj_addr)
  : Lemma
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
  =
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  CP.chunked_cheney_promote_budget_ready_elim
    minor major fp roots alloc_fuel remaining;
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ChunkedCheney.ccs_major = major;
      ChunkedCheney.ccs_fp = fp;
      ChunkedCheney.ccs_fwd = empty_forwarding;
      ChunkedCheney.ccs_queue = Seq.empty } in
  chunked_nonblue_origin_inv_init minor major fp;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  assert (CP.chunked_cheney_forward_roots_budget_ready
            minor cs0 roots 0 alloc_fuel remaining);
  chunked_cheney_forward_roots_budget_preserves_nonblue_origin_inv
    minor major cs0 roots 0 alloc_fuel remaining;
  CP.chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
    minor cs0 roots 0 alloc_fuel remaining;
  assert (CP.chunked_cheney_scan_budget_ready
            minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel remaining);
  let cs2 =
    ChunkedCheney.chunked_cheney_scan
      minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel in
  chunked_cheney_scan_budget_preserves_nonblue_origin_inv
    minor major cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel remaining;
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  assert (res.major_final == cs2.ccs_major);
  assert (res.fwd_map == cs2.ccs_fwd);
  chunked_nonblue_origin_inv_elim minor major cs2 src
#pop-options
