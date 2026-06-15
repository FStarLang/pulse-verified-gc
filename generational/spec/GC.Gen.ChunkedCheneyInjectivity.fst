module GC.Gen.ChunkedCheneyInjectivity

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Lib.Header

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module GenInv = GC.Gen.HeapInvariant
module DenseCheney = GC.Gen.Cheney
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedPromote = GC.Gen.ChunkedPromote
module CP = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module MarkDefs = GC.Spec.ChunkedMark.Defs
module GenMajorGCBridge = GC.Gen.ChunkedMajorGCBridge

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
private let nat_nonzero_gt_zero (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

private let nat_lt_pow2_54_size64 (n: nat)
  : Lemma (requires n < pow2 54) (ensures FStar.UInt.size n 64)
  =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  assert (n < pow2 64)
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
[@"opaque_to_smt"]
let chunked_fwd_normal_injective
  (minor: minor_state) (fwd: forwarding_map) : prop =
  forall (x: U64.t) (y: U64.t).
    fwd x <> 0UL /\
    fwd y <> 0UL /\
    Seq.mem x (minor_objects minor) /\
    Seq.mem y (minor_objects minor) /\
    ~(is_infix_in_minor minor x) /\
    ~(is_infix_in_minor minor y) /\
    minor_wosize minor x > 0 /\
    minor_wosize minor y > 0 /\
    fwd x == fwd y ==>
    x == y

let chunked_fwd_normal_injective_elim
  (minor: minor_state) (fwd: forwarding_map) (x: U64.t) (y: U64.t)
  : Lemma
      (requires
        chunked_fwd_normal_injective minor fwd /\
        fwd x <> 0UL /\
        fwd y <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        Seq.mem y (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        ~(is_infix_in_minor minor y) /\
        minor_wosize minor x > 0 /\
        minor_wosize minor y > 0 /\
        fwd x == fwd y)
      (ensures x == y)
  =
  reveal_opaque (`%chunked_fwd_normal_injective)
    (chunked_fwd_normal_injective minor fwd)

private let chunked_fwd_normal_injective_empty (minor: minor_state)
  : Lemma (ensures chunked_fwd_normal_injective minor empty_forwarding)
  =
  reveal_opaque (`%chunked_fwd_normal_injective)
    (chunked_fwd_normal_injective minor empty_forwarding);
  let aux (x: U64.t) (y: U64.t)
    : Lemma
        (requires
          empty_forwarding x <> 0UL /\
          empty_forwarding y <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          Seq.mem y (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          ~(is_infix_in_minor minor y) /\
          minor_wosize minor x > 0 /\
          minor_wosize minor y > 0 /\
          empty_forwarding x == empty_forwarding y)
        (ensures x == y)
    =
    assert (empty_forwarding x == 0UL);
    assert False
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 aux)

private let chunked_fwd_normal_injective_extend_excluded
  (minor: minor_state) (fwd: forwarding_map) (addr target: U64.t)
  : Lemma
      (requires
        chunked_fwd_normal_injective minor fwd /\
        is_infix_in_minor minor addr)
      (ensures
        chunked_fwd_normal_injective minor
          (extend_forwarding fwd addr target))
  =
  let fwd' = extend_forwarding fwd addr target in
  reveal_opaque (`%chunked_fwd_normal_injective)
    (chunked_fwd_normal_injective minor fwd');
  let aux (x: U64.t) (y: U64.t)
    : Lemma
        (requires
          fwd' x <> 0UL /\
          fwd' y <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          Seq.mem y (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          ~(is_infix_in_minor minor y) /\
          minor_wosize minor x > 0 /\
          minor_wosize minor y > 0 /\
          fwd' x == fwd' y)
        (ensures x == y)
    =
    if x = addr then begin
      assert (is_infix_in_minor minor x);
      assert False
    end else if y = addr then begin
      assert (is_infix_in_minor minor y);
      assert False
    end else begin
      assert (fwd' x == fwd x);
      assert (fwd' y == fwd y);
      chunked_fwd_normal_injective_elim minor fwd x y
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 aux)

private let chunked_fwd_normal_injective_extend_fresh
  (minor: minor_state) (fwd: forwarding_map) (addr target: U64.t)
  : Lemma
      (requires
        chunked_fwd_normal_injective minor fwd /\
        fwd addr = 0UL /\
        target <> 0UL /\
        Seq.mem addr (minor_objects minor) /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        (forall (y: U64.t).
          fwd y <> 0UL /\
          Seq.mem y (minor_objects minor) /\
          ~(is_infix_in_minor minor y) /\
          minor_wosize minor y > 0 ==>
          fwd y <> target))
      (ensures
        chunked_fwd_normal_injective minor
          (extend_forwarding fwd addr target))
  =
  let fwd' = extend_forwarding fwd addr target in
  reveal_opaque (`%chunked_fwd_normal_injective)
    (chunked_fwd_normal_injective minor fwd');
  let aux (x: U64.t) (y: U64.t)
    : Lemma
        (requires
          fwd' x <> 0UL /\
          fwd' y <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          Seq.mem y (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          ~(is_infix_in_minor minor y) /\
          minor_wosize minor x > 0 /\
          minor_wosize minor y > 0 /\
          fwd' x == fwd' y)
        (ensures x == y)
    =
    if x = addr then begin
      assert (fwd' x == target);
      if y = addr then ()
      else begin
        assert (fwd' y == fwd y);
        assert (fwd y <> target);
        assert False
      end
    end else if y = addr then begin
      assert (fwd' y == target);
      assert (fwd' x == fwd x);
      assert (fwd x <> target);
      assert False
    end else begin
      assert (fwd' x == fwd x);
      assert (fwd' y == fwd y);
      chunked_fwd_normal_injective_elim minor fwd x y
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 aux)
#pop-options

#restart-solver

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
[@"opaque_to_smt"]
let chunked_fwd_normal_targets_not_blue
  (minor: minor_state) (fwd: forwarding_map) (mh: MH.major_heap) : prop =
  forall (x: U64.t).
    fwd x <> 0UL /\
    Seq.mem x (minor_objects minor) /\
    ~(is_infix_in_minor minor x) /\
    minor_wosize minor x > 0 ==>
    is_val_addr (fwd x) /\
    (let target : obj_addr = fwd x in
     Seq.mem target (MH.major_objects mh) /\
     (match MH.read_word_in_major mh (hd_address target) with
      | Some hdr -> getColor hdr <> Blue /\ U64.v (getWosize hdr) >= 1
      | None -> False))

let chunked_fwd_normal_targets_not_blue_elim
  (minor: minor_state) (fwd: forwarding_map) (mh: MH.major_heap)
  (x: U64.t)
  : Lemma
      (requires
        chunked_fwd_normal_targets_not_blue minor fwd mh /\
        fwd x <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        minor_wosize minor x > 0)
      (ensures
        is_val_addr (fwd x) /\
        (let target : obj_addr = fwd x in
         Seq.mem target (MH.major_objects mh) /\
         (match MH.read_word_in_major mh (hd_address target) with
          | Some hdr -> getColor hdr <> Blue /\ U64.v (getWosize hdr) >= 1
          | None -> False)))
  =
  reveal_opaque (`%chunked_fwd_normal_targets_not_blue)
    (chunked_fwd_normal_targets_not_blue minor fwd mh)

private let chunked_fwd_normal_targets_not_blue_empty
  (minor: minor_state) (mh: MH.major_heap)
  : Lemma
      (ensures
        chunked_fwd_normal_targets_not_blue minor empty_forwarding mh)
  =
  reveal_opaque (`%chunked_fwd_normal_targets_not_blue)
    (chunked_fwd_normal_targets_not_blue minor empty_forwarding mh);
  let aux (x: U64.t)
    : Lemma
        (requires
          empty_forwarding x <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0)
        (ensures
          is_val_addr (empty_forwarding x) /\
          (let target : obj_addr = empty_forwarding x in
           Seq.mem target (MH.major_objects mh) /\
           (match MH.read_word_in_major mh (hd_address target) with
            | Some hdr -> getColor hdr <> Blue /\ U64.v (getWosize hdr) >= 1
            | None -> False)))
    =
    assert (empty_forwarding x == 0UL);
    assert False
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)

private let chunked_fwd_normal_targets_not_blue_extend_excluded
  (minor: minor_state) (fwd: forwarding_map) (mh: MH.major_heap)
  (addr target: U64.t)
  : Lemma
      (requires
        chunked_fwd_normal_targets_not_blue minor fwd mh /\
        is_infix_in_minor minor addr)
      (ensures
        chunked_fwd_normal_targets_not_blue minor
          (extend_forwarding fwd addr target) mh)
  =
  let fwd' = extend_forwarding fwd addr target in
  reveal_opaque (`%chunked_fwd_normal_targets_not_blue)
    (chunked_fwd_normal_targets_not_blue minor fwd' mh);
  let aux (x: U64.t)
    : Lemma
        (requires
          fwd' x <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0)
        (ensures
          is_val_addr (fwd' x) /\
          (let target : obj_addr = fwd' x in
           Seq.mem target (MH.major_objects mh) /\
           (match MH.read_word_in_major mh (hd_address target) with
            | Some hdr -> getColor hdr <> Blue /\ U64.v (getWosize hdr) >= 1
            | None -> False)))
    =
    if x = addr then begin
      assert (is_infix_in_minor minor x);
      assert False
    end else begin
      assert (fwd' x == fwd x);
      chunked_fwd_normal_targets_not_blue_elim minor fwd mh x
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)

private let current_free_head_ne_normal_target
  (minor: minor_state) (fwd: forwarding_map) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (x: U64.t)
  : Lemma
      (requires
        fuel > 0 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        chunked_fwd_normal_targets_not_blue minor fwd mh /\
        fwd x <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        minor_wosize minor x > 0)
      (ensures fp <> fwd x)
  =
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.major_fl_above_zero_current mh fp fuel;
  chunked_fwd_normal_targets_not_blue_elim minor fwd mh x;
  let target : obj_addr = fwd x in
  match MH.read_word_in_major mh (hd_address target) with
  | Some hdr ->
    GenInv.chunked_is_blue_header mh target hdr;
    assert (~(GenInv.chunked_is_blue mh target));
    GenInv.chunked_chain_objects_blue_elim mh fp fuel target;
    SpecMajorAlloc.major_fl_chain_avoids_head_ne mh fp target fuel
  | None ->
    assert False

private let chunked_cheney_forward_normal_preserves_old_major_objects
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        remaining > 0 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 1 + remaining))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         forall (src: obj_addr).
           Seq.mem src (MH.major_objects cs.ccs_major) ==>
           Seq.mem src (MH.major_objects cs'.ccs_major)))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0 minor cs addr fuel
    else begin
      nat_nonzero_gt_zero wz;
      assert (wz > 0);
      assert (remaining >= 1);
      assert (wz + 2 <= wz + 1 + remaining);
      assert (cs.ccs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= wz + 2);
      CP.chunked_promote_object_head_split_preserves_chunked_alloc_shape
        minor cs.ccs_major addr cs.ccs_fp wz fuel;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      assert (res.new_addr == cs.ccs_fp);
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr fuel
    end
  end

private let chunked_cheney_forward_normal_preserves_old_non_blue_header
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel remaining: nat) (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        fuel > 1 /\
        remaining > 0 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 1 + remaining) /\
        Seq.mem src (MH.major_objects cs.ccs_major) /\
        MH.read_word_in_major cs.ccs_major (hd_address src) == Some hdr /\
        getColor hdr <> Blue /\
        U64.v (getWosize hdr) >= 1)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0 minor cs addr fuel
    else begin
      nat_nonzero_gt_zero wz;
      assert (wz > 0);
      assert (remaining >= 1);
      assert (wz + 2 <= wz + 1 + remaining);
      assert (cs.ccs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= wz + 2);
      CP.chunked_promote_object_head_split_preserves_old_non_blue_header
        minor cs.ccs_major addr cs.ccs_fp wz fuel src hdr;
      CP.chunked_promote_object_head_split_preserves_chunked_alloc_shape
        minor cs.ccs_major addr cs.ccs_fp wz fuel;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      assert (res.new_addr == cs.ccs_fp);
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr fuel
    end
  end
#pop-options

#restart-solver

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
private let chunked_cheney_forward_normal_preserves_fwd_targets_not_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        remaining > 0 /\
        chunked_fwd_normal_targets_not_blue
          minor cs.ccs_fwd cs.ccs_major /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 1 + remaining))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         chunked_fwd_normal_targets_not_blue
          minor cs'.ccs_fwd cs'.ccs_major))
  =
  let cs' =
    ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
  reveal_opaque (`%chunked_fwd_normal_targets_not_blue)
    (chunked_fwd_normal_targets_not_blue minor cs'.ccs_fwd cs'.ccs_major);
  let aux (x: U64.t)
    : Lemma
        (requires
          cs'.ccs_fwd x <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0)
        (ensures
          is_val_addr (cs'.ccs_fwd x) /\
          (let target : obj_addr = cs'.ccs_fwd x in
           Seq.mem target (MH.major_objects cs'.ccs_major) /\
           (match MH.read_word_in_major cs'.ccs_major (hd_address target) with
            | Some hdr -> getColor hdr <> Blue /\ U64.v (getWosize hdr) >= 1
            | None -> False)))
    =
    if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then begin
      ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel;
      assert (cs' == cs);
      chunked_fwd_normal_targets_not_blue_elim
        minor cs.ccs_fwd cs.ccs_major x
    end else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then begin
        ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
          minor cs addr fuel;
        assert (cs' == cs);
        chunked_fwd_normal_targets_not_blue_elim
          minor cs.ccs_fwd cs.ccs_major x
      end else begin
        nat_nonzero_gt_zero wz;
        assert (wz > 0);
        assert (remaining >= 1);
        assert (wz + 2 <= wz + 1 + remaining);
        assert (cs.ccs_fp <> 0UL);
        assert (SpecMajorAlloc.major_fl_head_wosize
                  cs.ccs_major cs.ccs_fp >= wz + 2);
        if x = addr then begin
          if is_infix_in_minor minor addr then begin
            assert (is_infix_in_minor minor x);
            assert False
          end else begin
            GenInv.chunked_major_alloc_shape_elim
              cs.ccs_major cs.ccs_fp fuel;
            SpecMajorAlloc.major_fl_above_zero_current
              cs.ccs_major cs.ccs_fp fuel;
            SpecMajorAlloc.major_fl_head_wosize_current
              cs.ccs_major cs.ccs_fp fuel;
            match MH.read_word_in_major
                    cs.ccs_major (hd_address (cs.ccs_fp <: obj_addr)) with
            | None -> assert False
            | Some old_hdr ->
              assert (SpecMajorAlloc.major_fl_head_wosize
                        cs.ccs_major cs.ccs_fp ==
                      U64.v (getWosize old_hdr));
              assert (U64.v (getWosize old_hdr) < pow2 54);
              assert (wz + 2 <= U64.v (getWosize old_hdr));
              assert (wz < pow2 54);
            nat_lt_pow2_54_size64 wz;
            ChunkedCheney.chunked_cheney_forward_normal_head_split_header_effect
              minor cs addr fuel;
            assert (cs'.ccs_fwd addr == cs.ccs_fp);
            is_val_addr_spec (cs'.ccs_fwd x);
            let target : obj_addr = cs'.ccs_fwd x in
            let head : obj_addr = cs.ccs_fp in
            assert (target == head);
            assert (Seq.mem target (MH.major_objects cs'.ccs_major));
            assert (hd_address target == hd_address head);
            match MH.read_word_in_major cs'.ccs_major (hd_address head) with
            | Some final_hdr ->
              assert (getColor final_hdr == White);
              assert (getColor final_hdr <> Blue);
              assert (U64.v (getWosize final_hdr) == wz);
              assert (U64.v (getWosize final_hdr) >= 1)
            | None ->
              assert False
          end
        end else begin
          ChunkedCheney.chunked_cheney_forward_normal_other_fwd
            minor cs addr x fuel;
          assert (cs'.ccs_fwd x == cs.ccs_fwd x);
          chunked_fwd_normal_targets_not_blue_elim
            minor cs.ccs_fwd cs.ccs_major x;
          let old_target : obj_addr = cs.ccs_fwd x in
          match MH.read_word_in_major cs.ccs_major (hd_address old_target) with
          | Some hdr ->
            chunked_cheney_forward_normal_preserves_old_major_objects
              minor cs addr fuel remaining;
            chunked_cheney_forward_normal_preserves_old_non_blue_header
              minor cs addr fuel remaining old_target hdr;
            is_val_addr_spec (cs'.ccs_fwd x);
            let target : obj_addr = cs'.ccs_fwd x in
            assert (target == old_target);
            assert (hd_address target == hd_address old_target);
            assert (Seq.mem target (MH.major_objects cs'.ccs_major));
            assert (MH.read_word_in_major cs'.ccs_major (hd_address target) ==
                    Some hdr)
          | None ->
            assert False
        end
      end
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)

private let chunked_cheney_forward_normal_preserves_inj_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        remaining > 0 /\
        chunked_fwd_normal_injective minor cs.ccs_fwd /\
        chunked_fwd_normal_targets_not_blue
          minor cs.ccs_fwd cs.ccs_major /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 1 + remaining))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         chunked_fwd_normal_injective minor cs'.ccs_fwd /\
         chunked_fwd_normal_targets_not_blue
          minor cs'.ccs_fwd cs'.ccs_major /\
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp fuel = true /\
         GenInv.chunked_chain_objects_blue
          cs'.ccs_major cs'.ccs_fp fuel))
  =
  let cs' =
    ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then begin
    ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel;
    assert (cs' == cs)
  end else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then begin
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
        minor cs addr fuel;
      assert (cs' == cs)
    end else begin
      nat_nonzero_gt_zero wz;
      assert (wz > 0);
      assert (remaining >= 1);
      assert (wz + 2 <= wz + 1 + remaining);
      assert (cs.ccs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= wz + 2);
      CP.chunked_promote_object_head_split_preserves_chunked_alloc_shape
        minor cs.ccs_major addr cs.ccs_fp wz fuel;
      CP.chunked_promote_object_head_split_preserves_chain_objects_blue
        minor cs.ccs_major addr cs.ccs_fp wz fuel;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      assert (res.new_addr == cs.ccs_fp);
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr fuel;
      assert (cs'.ccs_fwd ==
              extend_forwarding cs.ccs_fwd addr cs.ccs_fp);
      if is_infix_in_minor minor addr then begin
        assert (chunked_fwd_normal_injective minor cs.ccs_fwd);
        assert (is_infix_in_minor minor addr);
        chunked_fwd_normal_injective_extend_excluded
          minor cs.ccs_fwd addr cs.ccs_fp
      end
      else begin
        assert (~(is_infix_in_minor minor addr));
        assert (Seq.mem addr (minor_objects minor));
        assert (cs.ccs_fwd addr == 0UL);
        assert (minor_wosize minor addr > 0);
        let sep (y: U64.t)
          : Lemma
              (requires
                cs.ccs_fwd y <> 0UL /\
                Seq.mem y (minor_objects minor) /\
                ~(is_infix_in_minor minor y) /\
                minor_wosize minor y > 0)
              (ensures cs.ccs_fwd y <> cs.ccs_fp)
          =
          current_free_head_ne_normal_target
            minor cs.ccs_fwd cs.ccs_major cs.ccs_fp fuel y
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires sep);
        assert (forall (y: U64.t).
          cs.ccs_fwd y <> 0UL /\
          Seq.mem y (minor_objects minor) /\
          ~(is_infix_in_minor minor y) /\
          minor_wosize minor y > 0 ==>
          cs.ccs_fwd y <> cs.ccs_fp);
        assert (chunked_fwd_normal_injective minor cs.ccs_fwd);
        assert (cs.ccs_fp <> 0UL);
        chunked_fwd_normal_injective_extend_fresh
          minor cs.ccs_fwd addr cs.ccs_fp
      end
    end
  end;
  chunked_cheney_forward_normal_preserves_fwd_targets_not_blue
    minor cs addr fuel remaining
#pop-options

#restart-solver

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
private let chunked_cheney_forward_one_preserves_inj_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        chunked_fwd_normal_injective minor cs.ccs_fwd /\
        chunked_fwd_normal_targets_not_blue
          minor cs.ccs_fwd cs.ccs_major /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        CP.chunked_cheney_forward_one_budget_ready minor cs addr remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         chunked_fwd_normal_injective minor cs'.ccs_fwd /\
         chunked_fwd_normal_targets_not_blue
          minor cs'.ccs_fwd cs'.ccs_major /\
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp fuel = true /\
         GenInv.chunked_chain_objects_blue
          cs'.ccs_major cs'.ccs_fp fuel))
  =
  CP.chunked_cheney_forward_one_budget_ready_elim
    minor cs addr remaining;
  assert (remaining > 0);
  let r = ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
  if cs.ccs_fwd addr <> 0UL then begin
    ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr fuel;
    assert (r == cs)
  end else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    assert (
      Seq.mem parent (minor_objects minor) /\
      cs.ccs_fwd parent = 0UL /\
      minor_wosize minor parent > 0 ==>
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        minor_wosize minor parent + 1 + remaining);
    chunked_cheney_forward_normal_preserves_inj_inv
      minor cs parent fuel remaining;
    let csn =
      ChunkedCheney.chunked_cheney_forward_normal minor cs parent fuel in
    assert (chunked_fwd_normal_injective minor csn.ccs_fwd);
    assert (chunked_fwd_normal_targets_not_blue
              minor csn.ccs_fwd csn.ccs_major);
    if csn.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (csn.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then begin
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr fuel;
      let sum =
        U64.uint_to_t
          (U64.v (csn.ccs_fwd parent) + (U64.v addr - U64.v parent)) in
      assert (r.ccs_fwd == extend_forwarding csn.ccs_fwd addr sum);
      assert (r.ccs_major == csn.ccs_major);
      chunked_fwd_normal_injective_extend_excluded
        minor csn.ccs_fwd addr sum;
      chunked_fwd_normal_targets_not_blue_extend_excluded
        minor csn.ccs_fwd csn.ccs_major addr sum
    end else begin
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr fuel;
      assert (r == csn)
    end
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal minor cs addr fuel;
    assert (r == ChunkedCheney.chunked_cheney_forward_normal
                 minor cs addr fuel);
    assert (
      Seq.mem addr (minor_objects minor) /\
      cs.ccs_fwd addr = 0UL /\
      minor_wosize minor addr > 0 ==>
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >=
        minor_wosize minor addr + 1 + remaining);
    chunked_cheney_forward_normal_preserves_inj_inv
      minor cs addr fuel remaining
  end
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
private let chunked_cheney_forward_one_budget_ready_implies_head_split_pre
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (remaining: nat)
  : Lemma
      (requires
        CP.chunked_cheney_forward_one_budget_ready minor cs addr remaining)
      (ensures
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
                cs.ccs_major cs.ccs_fp >=
              minor_wosize minor parent + 2)))
  =
  CP.chunked_cheney_forward_one_budget_ready_elim
    minor cs addr remaining;
  assert (remaining > 0);
  if Seq.mem addr (minor_objects minor) &&
     cs.ccs_fwd addr = 0UL &&
     ~(is_infix_in_minor minor addr) &&
     minor_wosize minor addr > 0
  then begin
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs.ccs_major cs.ccs_fp >=
            minor_wosize minor addr + 1 + remaining);
    assert (SpecMajorAlloc.major_fl_head_wosize
              cs.ccs_major cs.ccs_fp >=
            minor_wosize minor addr + 2)
  end;
  if cs.ccs_fwd addr = 0UL &&
     is_infix_in_minor minor addr
  then begin
    let parent = infix_parent minor addr in
    if Seq.mem parent (minor_objects minor) &&
       cs.ccs_fwd parent = 0UL &&
       minor_wosize minor parent > 0
    then begin
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >=
              minor_wosize minor parent + 1 + remaining);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >=
              minor_wosize minor parent + 2)
    end
  end
#pop-options

#restart-solver

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
private let rec chunked_cheney_forward_roots_preserves_inj_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        chunked_fwd_normal_injective minor cs.ccs_fwd /\
        chunked_fwd_normal_targets_not_blue
          minor cs.ccs_fwd cs.ccs_major /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CP.chunked_cheney_forward_roots_budget_ready
          minor cs roots idx alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         chunked_fwd_normal_injective minor cs'.ccs_fwd /\
         chunked_fwd_normal_targets_not_blue
          minor cs'.ccs_fwd cs'.ccs_major /\
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
          cs'.ccs_major cs'.ccs_fp alloc_fuel))
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then begin
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel
  end else begin
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
    chunked_cheney_forward_one_preserves_inj_inv
      minor cs r alloc_fuel remaining;
    CP.chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
      minor cs r alloc_fuel remaining;
    chunked_cheney_forward_one_budget_ready_implies_head_split_pre
      minor cs r remaining;
    CP.chunked_cheney_forward_one_head_split_preserves_chain_objects_blue
      minor cs r alloc_fuel;
    assert (chunked_fwd_normal_injective minor cs'.ccs_fwd);
    assert (chunked_fwd_normal_targets_not_blue
              minor cs'.ccs_fwd cs'.ccs_major);
    assert (GenInv.chunked_major_alloc_shape
              cs'.ccs_major cs'.ccs_fp alloc_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              cs'.ccs_major cs'.ccs_fp alloc_fuel = true);
    assert (GenInv.chunked_chain_objects_blue
              cs'.ccs_major cs'.ccs_fp alloc_fuel);
    chunked_cheney_forward_roots_preserves_inj_inv
      minor cs' roots (idx + 1) alloc_fuel remaining
  end

private let rec chunked_cheney_forward_fields_preserves_inj_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        chunked_fwd_normal_injective minor cs.ccs_fwd /\
        chunked_fwd_normal_targets_not_blue
          minor cs.ccs_fwd cs.ccs_major /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CP.chunked_cheney_forward_fields_budget_ready
          minor cs parent idx wosize alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         chunked_fwd_normal_injective minor cs'.ccs_fwd /\
         chunked_fwd_normal_targets_not_blue
          minor cs'.ccs_fwd cs'.ccs_major /\
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
          cs'.ccs_major cs'.ccs_fp alloc_fuel))
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then begin
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    CP.chunked_cheney_forward_fields_budget_ready_step
      minor cs parent idx wosize alloc_fuel remaining;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs field_val alloc_fuel in
    assert (CP.chunked_cheney_forward_one_budget_ready
              minor cs field_val remaining);
    assert (CP.chunked_cheney_forward_fields_budget_ready
              minor cs' parent (idx + 1) wosize alloc_fuel remaining);
    chunked_cheney_forward_one_preserves_inj_inv
      minor cs field_val alloc_fuel remaining;
    CP.chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
      minor cs field_val alloc_fuel remaining;
    chunked_cheney_forward_one_budget_ready_implies_head_split_pre
      minor cs field_val remaining;
    CP.chunked_cheney_forward_one_head_split_preserves_chain_objects_blue
      minor cs field_val alloc_fuel;
    assert (chunked_fwd_normal_injective minor cs'.ccs_fwd);
    assert (chunked_fwd_normal_targets_not_blue
              minor cs'.ccs_fwd cs'.ccs_major);
    assert (GenInv.chunked_major_alloc_shape
              cs'.ccs_major cs'.ccs_fp alloc_fuel);
    assert (SpecMajorAlloc.major_fl_chain_terminates
              cs'.ccs_major cs'.ccs_fp alloc_fuel = true);
    assert (GenInv.chunked_chain_objects_blue
              cs'.ccs_major cs'.ccs_fp alloc_fuel);
    chunked_cheney_forward_fields_preserves_inj_inv
      minor cs' parent (idx + 1) wosize alloc_fuel remaining
  end

private let rec chunked_cheney_scan_preserves_inj_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        chunked_fwd_normal_injective minor cs.ccs_fwd /\
        chunked_fwd_normal_targets_not_blue
          minor cs.ccs_fwd cs.ccs_major /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CP.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         chunked_fwd_normal_injective minor cs'.ccs_fwd /\
         chunked_fwd_normal_targets_not_blue
          minor cs'.ccs_fwd cs'.ccs_major /\
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
          cs'.ccs_major cs'.ccs_fp alloc_fuel))
      (decreases scan_fuel)
  =
  if scan_fuel > 0 then
    if scan >= Seq.length cs.ccs_queue then
      ChunkedCheney.chunked_cheney_scan_base
        minor cs scan scan_fuel alloc_fuel
    else begin
      let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
      ChunkedCheney.chunked_cheney_scan_step
        minor cs scan scan_fuel alloc_fuel;
      CP.chunked_cheney_scan_budget_ready_step
        minor cs scan scan_fuel alloc_fuel remaining;
      let obj = Seq.index cs.ccs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' =
        ChunkedCheney.chunked_cheney_forward_fields
          minor cs obj 0 wz alloc_fuel in
      assert (CP.chunked_cheney_forward_fields_budget_ready
                minor cs obj 0 wz alloc_fuel remaining);
      assert (CP.chunked_cheney_scan_budget_ready
                minor cs' (scan + 1) fuel' alloc_fuel remaining);
      chunked_cheney_forward_fields_preserves_inj_inv
        minor cs obj 0 wz alloc_fuel remaining;
      assert (chunked_fwd_normal_injective minor cs'.ccs_fwd);
      assert (chunked_fwd_normal_targets_not_blue
                minor cs'.ccs_fwd cs'.ccs_major);
      assert (GenInv.chunked_major_alloc_shape
                cs'.ccs_major cs'.ccs_fp alloc_fuel);
      assert (SpecMajorAlloc.major_fl_chain_terminates
                cs'.ccs_major cs'.ccs_fp alloc_fuel = true);
      assert (GenInv.chunked_chain_objects_blue
                cs'.ccs_major cs'.ccs_fp alloc_fuel);
      chunked_cheney_scan_preserves_inj_inv
        minor cs' (scan + 1) fuel' alloc_fuel remaining
    end
  else
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel

private let chunked_cheney_promote_fwd_normal_inj_inv
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        chunked_fwd_normal_injective minor
          (ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel).fwd_map /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         chunked_fwd_normal_targets_not_blue minor res.fwd_map res.major_final))
  =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  CP.chunked_cheney_promote_budget_ready_elim
    minor major fp roots alloc_fuel remaining;
  chunked_fwd_normal_injective_empty minor;
  chunked_fwd_normal_targets_not_blue_empty minor major;
  assert (CP.chunked_cheney_forward_roots_budget_ready
            minor cs0 roots 0 alloc_fuel remaining);
  chunked_cheney_forward_roots_preserves_inj_inv
    minor cs0 roots 0 alloc_fuel remaining;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  assert (chunked_fwd_normal_injective minor cs1.ccs_fwd);
  assert (chunked_fwd_normal_targets_not_blue
            minor cs1.ccs_fwd cs1.ccs_major);
  assert (GenInv.chunked_major_alloc_shape
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
  assert (GenInv.chunked_chain_objects_blue
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (CP.chunked_cheney_scan_budget_ready
            minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel remaining);
  chunked_cheney_scan_preserves_inj_inv
    minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel remaining;
  let cs2 =
    ChunkedCheney.chunked_cheney_scan
      minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel in
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  assert (res.fwd_map == cs2.ccs_fwd);
  assert (res.major_final == cs2.ccs_major);
  assert (chunked_fwd_normal_targets_not_blue minor res.fwd_map res.major_final)

let chunked_cheney_promote_fwd_normal_injective
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        chunked_fwd_normal_injective minor
          (ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel).fwd_map)
  =
  chunked_cheney_promote_fwd_normal_inj_inv
    minor major fp roots alloc_fuel remaining

let chunked_cheney_promote_fwd_normal_targets_not_blue
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         chunked_fwd_normal_targets_not_blue minor res.fwd_map res.major_final))
  =
  chunked_cheney_promote_fwd_normal_inj_inv
    minor major fp roots alloc_fuel remaining

let chunked_cheney_promote_fwd_target_minor_field_no_infix
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  (x: U64.t) (j: nat) (field_addr: hp_addr) (raw: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        GenInv.minor_fields_no_infix_targets minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         res.fwd_map x <> 0UL /\
         Seq.mem x (minor_objects minor) /\
         ~(is_infix_in_minor minor x) /\
         j < minor_wosize minor x /\
         U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword /\
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         is_minor_pointer (to_minor_offset raw)))
      (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))
  =
  CP.chunked_cheney_promote_fwd_target_fields_match
    minor major fp roots alloc_fuel remaining x j field_addr;
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  assert (MH.read_word_in_major res.major_final field_addr ==
          Some (minor_read_field minor x j));
  assert (raw == minor_read_field minor x j);
  assert (to_minor_offset raw ==
          to_minor_offset (minor_read_field minor x j));
  GenInv.minor_fields_no_infix_targets_elim minor x j

let chunked_cheney_promote_old_nonblue_field_no_infix
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  (src: obj_addr) (hdr: U64.t) (j: nat) (field_addr: hp_addr)
  (old raw: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        GenInv.chunked_major_minor_fields_no_infix_targets minor major /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> Blue /\
        U64.v (getTag hdr) < U64.v no_scan_tag /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         is_minor_pointer (to_minor_offset raw)))
      (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))
  =
  CG.chunked_major_field_slot_elim src j field_addr;
  CP.chunked_cheney_promote_head_split_preserves_old_non_blue_field
    minor major fp roots alloc_fuel src hdr j field_addr old;
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  assert (MH.read_word_in_major res.major_final field_addr == Some old);
  assert (raw == old);
  GenInv.chunked_is_blue_header major src hdr;
  assert (~(GenInv.chunked_is_blue major src));
  CG.chunked_is_no_scan_header major src hdr;
  assert (~(CG.chunked_is_no_scan major src));
  CG.chunked_wosize_nat_header major src hdr;
  assert (j < CG.chunked_wosize_nat_of_object major src);
  GenInv.chunked_major_minor_fields_no_infix_targets_elim
    minor major src j field_addr old

let chunked_cheney_promote_fwd_target_minor_major_field_raw_target
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  (x: U64.t) (j: nat) (field_addr: hp_addr) (raw: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        GenInv.chunked_minor_major_fields_no_blue minor major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         res.fwd_map x <> 0UL /\
         Seq.mem x (minor_objects minor) /\
         ~(is_infix_in_minor minor x) /\
         j < minor_wosize minor x /\
         U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword /\
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         is_pointer_field raw /\
         MarkDefs.chunked_is_pointer_field res.major_final raw))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr
                    res.major_final raw)
           (MH.major_objects res.major_final)))
  =
  CP.chunked_cheney_promote_fwd_target_fields_match
    minor major fp roots alloc_fuel remaining x j field_addr;
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  assert (MH.read_word_in_major res.major_final field_addr ==
          Some (minor_read_field minor x j));
  assert (raw == minor_read_field minor x j);
  assert (is_pointer_field (minor_read_field minor x j));
  GenInv.chunked_minor_major_fields_no_blue_elim minor major x j;
  assert (Seq.mem ((raw) <: obj_addr) (MH.major_objects major));
  CP.chunked_cheney_promote_head_split_preserves_old_major_objects
    minor major fp roots alloc_fuel;
  assert (Seq.mem ((raw) <: obj_addr) (MH.major_objects res.major_final));
  MarkDefs.chunked_pointer_field_as_obj_addr_step res.major_final raw;
  assert (MarkDefs.chunked_pointer_field_as_obj_addr res.major_final raw ==
          ((raw) <: obj_addr))

let chunked_cheney_promote_old_nonblue_field_raw_target
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  (src: obj_addr) (hdr: U64.t) (j: nat) (field_addr: hp_addr)
  (old raw: U64.t)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old /\
        MarkDefs.chunked_is_pointer_field major old /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         MarkDefs.chunked_is_pointer_field res.major_final raw))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr
                    res.major_final raw)
           (MH.major_objects res.major_final)))
  =
  CP.chunked_cheney_promote_head_split_preserves_old_non_blue_field
    minor major fp roots alloc_fuel src hdr j field_addr old;
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  assert (MH.read_word_in_major res.major_final field_addr == Some old);
  assert (raw == old);
  CG.chunked_wosize_nat_header major src hdr;
  assert (j < CG.chunked_wosize_nat_of_object major src);
  GenMajorGCBridge.chunked_major_raw_field_targets_in_major_elim
    major src j field_addr old;
  assert (Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr major old)
            (MH.major_objects major));
  CP.chunked_cheney_promote_head_split_preserves_old_major_objects
    minor major fp roots alloc_fuel;
  assert (Seq.mem (MarkDefs.chunked_pointer_field_as_obj_addr major old)
            (MH.major_objects res.major_final));
  MarkDefs.chunked_pointer_field_as_obj_addr_step major old;
  MarkDefs.chunked_pointer_field_as_obj_addr_step res.major_final raw;
  assert (MarkDefs.chunked_pointer_field_as_obj_addr major old ==
          ((old) <: obj_addr));
  assert (MarkDefs.chunked_pointer_field_as_obj_addr res.major_final raw ==
          ((raw) <: obj_addr));
  assert (((old) <: obj_addr) == ((raw) <: obj_addr))
#pop-options
