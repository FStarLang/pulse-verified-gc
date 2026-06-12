module GC.Gen.ChunkedCheneyDisjointness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Lib.Header

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocSplitShape = GC.Spec.MajorAllocator.SplitShape
module DenseCheney = GC.Gen.Cheney
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedPromote = GC.Gen.ChunkedPromote
module GenInv = GC.Gen.HeapInvariant
module CP = GC.Gen.CheneyPreservation

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0"
private let nat_nonzero_gt_zero (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
[@"opaque_to_smt"]
let chunked_fwd_normal_disjoint_from_old_major
  (minor: minor_state) (fwd: forwarding_map) (old: U64.t) : prop =
  forall (x: U64.t).
    fwd x <> 0UL /\
    Seq.mem x (minor_objects minor) /\
    ~(is_infix_in_minor minor x) /\
    minor_wosize minor x > 0 ==>
    fwd x <> old

let chunked_fwd_normal_disjoint_from_old_major_elim
  (minor: minor_state) (fwd: forwarding_map) (old x: U64.t)
  : Lemma
      (requires
        chunked_fwd_normal_disjoint_from_old_major minor fwd old /\
        fwd x <> 0UL /\
        Seq.mem x (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        minor_wosize minor x > 0)
      (ensures fwd x <> old)
  =
  reveal_opaque (`%chunked_fwd_normal_disjoint_from_old_major)
    (chunked_fwd_normal_disjoint_from_old_major minor fwd old)

private let chunked_fwd_normal_disjoint_from_old_major_empty
  (minor: minor_state) (old: U64.t)
  : Lemma
      (ensures
        chunked_fwd_normal_disjoint_from_old_major
          minor empty_forwarding old)
  =
  reveal_opaque (`%chunked_fwd_normal_disjoint_from_old_major)
    (chunked_fwd_normal_disjoint_from_old_major
      minor empty_forwarding old);
  let aux (x: U64.t)
    : Lemma
        (requires
          empty_forwarding x <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0)
        (ensures empty_forwarding x <> old)
    =
    assert (empty_forwarding x == 0UL);
    assert False
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)

private let chunked_fwd_normal_disjoint_from_old_major_extend_excluded
  (minor: minor_state) (fwd: forwarding_map) (old addr target: U64.t)
  : Lemma
      (requires
        chunked_fwd_normal_disjoint_from_old_major minor fwd old /\
        is_infix_in_minor minor addr)
      (ensures
        chunked_fwd_normal_disjoint_from_old_major minor
          (extend_forwarding fwd addr target) old)
  =
  let fwd' = extend_forwarding fwd addr target in
  reveal_opaque (`%chunked_fwd_normal_disjoint_from_old_major)
    (chunked_fwd_normal_disjoint_from_old_major minor fwd' old);
  let aux (x: U64.t)
    : Lemma
        (requires
          fwd' x <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0)
        (ensures fwd' x <> old)
    =
    if x = addr then begin
      assert (is_infix_in_minor minor x);
      assert False
    end else begin
      assert (fwd' x == fwd x);
      chunked_fwd_normal_disjoint_from_old_major_elim
        minor fwd old x
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)

private let chunked_fwd_normal_disjoint_from_old_major_extend_fresh
  (minor: minor_state) (fwd: forwarding_map) (old addr target: U64.t)
  : Lemma
      (requires
        chunked_fwd_normal_disjoint_from_old_major minor fwd old /\
        target <> old)
      (ensures
        chunked_fwd_normal_disjoint_from_old_major minor
          (extend_forwarding fwd addr target) old)
  =
  let fwd' = extend_forwarding fwd addr target in
  reveal_opaque (`%chunked_fwd_normal_disjoint_from_old_major)
    (chunked_fwd_normal_disjoint_from_old_major minor fwd' old);
  let aux (x: U64.t)
    : Lemma
        (requires
          fwd' x <> 0UL /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0)
        (ensures fwd' x <> old)
    =
    if x = addr then begin
      assert (fwd' x == target)
    end else begin
      assert (fwd' x == fwd x);
      chunked_fwd_normal_disjoint_from_old_major_elim
        minor fwd old x
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)
#pop-options

#restart-solver

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
private let current_free_head_ne_old_major
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (old: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_avoids mh fp old fuel = true)
      (ensures fp <> old)
  =
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.major_fl_above_zero_current mh fp fuel;
  SpecMajorAlloc.major_fl_chain_avoids_head_ne mh fp old fuel

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
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
        minor cs addr fuel
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

private let rec chunked_fl_chain_avoids_transfer_on_chain
  (mh0 mh1: MH.major_heap) (excl cur: U64.t) (fuel: nat)
  : Lemma
      (requires
        SpecMajorAlloc.major_fl_valid mh0 cur fuel /\
        SpecMajorAlloc.major_fl_above_zero mh0 cur fuel /\
        SpecMajorAlloc.major_fl_chain_avoids mh0 cur excl fuel = true /\
        (forall (src: obj_addr).
          Seq.mem src (MH.major_objects mh0) /\
          src <> excl /\
          (match MH.read_word_in_major mh0 (hd_address src) with
           | Some hdr -> U64.v (getWosize hdr) >= 1
           | None -> False) /\
          SpecMajorAlloc.major_fl_chain_avoids mh0 cur src fuel = false ==>
          MH.read_word_in_major mh1 src ==
          MH.read_word_in_major mh0 src))
      (ensures
        SpecMajorAlloc.major_fl_chain_avoids mh1 cur excl fuel = true)
      (decreases fuel)
  =
  if fuel = 0 then ()
  else if cur = 0UL then ()
  else begin
    assert (fuel > 0);
    let fuel' : f:nat{f < fuel} = fuel - 1 in
    SpecMajorAlloc.major_fl_above_zero_current mh0 cur fuel;
    assert (U64.v cur >= U64.v zero_addr + U64.v mword);
    assert (U64.v cur >= U64.v mword);
    assert (U64.v cur < heap_size);
    assert (U64.v cur % U64.v mword == 0);
    SpecMajorAlloc.major_fl_chain_avoids_head_ne mh0 cur excl fuel;
    assert (cur <> excl);
    let x : obj_addr = cur in
    SpecMajorAlloc.major_fl_valid_gives_mem mh0 cur fuel;
    SpecMajorAlloc.major_fl_valid_gives_wosize mh0 cur fuel;
    SpecMajorAlloc.major_fl_valid_next mh0 cur fuel;
    SpecMajorAlloc.major_fl_chain_avoids_tail mh0 cur excl fuel;
    assert (SpecMajorAlloc.major_fl_chain_avoids mh0 cur cur fuel = false);
    match MH.read_word_in_major mh0 (hd_address x) with
    | None -> assert False
    | Some hdr ->
      assert (U64.v (getWosize hdr) >= 1);
      match MH.read_word_in_major mh0 x with
      | None -> assert False
      | Some next ->
        SpecMajorAlloc.major_fl_above_zero_next mh0 x fuel next;
        assert (MH.read_word_in_major mh1 x == Some next);
        assert (SpecMajorAlloc.major_fl_valid mh0 next fuel');
        assert (SpecMajorAlloc.major_fl_above_zero mh0 next fuel');
        assert (SpecMajorAlloc.major_fl_chain_avoids
                  mh0 next excl fuel' = true);
        let tail_frame (src: obj_addr)
          : Lemma
              (requires
                Seq.mem src (MH.major_objects mh0) /\
                src <> excl /\
                (match MH.read_word_in_major mh0 (hd_address src) with
                 | Some hdr -> U64.v (getWosize hdr) >= 1
                 | None -> False) /\
                SpecMajorAlloc.major_fl_chain_avoids
                  mh0 next src fuel' = false)
              (ensures
                MH.read_word_in_major mh1 src ==
                MH.read_word_in_major mh0 src)
          =
          if src = x then
            assert (SpecMajorAlloc.major_fl_chain_avoids
                      mh0 cur src fuel = false)
          else begin
            assert (cur <> src);
            assert (SpecMajorAlloc.major_fl_chain_avoids
                      mh0 cur src fuel = false)
          end
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires tail_frame);
        chunked_fl_chain_avoids_transfer_on_chain mh0 mh1 excl next fuel';
        assert
          (match MH.read_word_in_major mh1 (cur <: obj_addr) with
           | Some next' ->
             SpecMajorAlloc.major_fl_chain_avoids mh1 next' excl fuel' = true
           | None -> True);
        SpecMajorAlloc.major_fl_chain_avoids_step mh1 cur excl fuel
  end

private let chunked_promote_object_head_split_preserves_chain_avoids
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (old: obj_addr)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        SpecMajorAlloc.major_fl_chain_avoids mh fp old fuel = true /\
        Seq.mem old (MH.major_objects mh) /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_out res.fp_out fuel = true /\
         SpecMajorAlloc.major_fl_chain_avoids
           res.major_out res.fp_out old fuel = true))
  =
  CP.chunked_promote_object_head_split_preserves_chunked_alloc_shape
    minor mh obj fp wosize fuel;
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.major_alloc_head_split_remainder_not_old_object
    mh fp old wosize fuel;
  let alloc_res =
    SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
  SpecMajorAllocSplitShape.major_alloc_head_split_preserves_alloc_shape
    mh fp wosize fuel;
  SpecMajorAllocSplitShape.major_alloc_head_split_remainder_avoids_other
    mh fp old wosize fuel;
  let res =
    ChunkedPromote.chunked_promote_object_with_fuel
      minor mh obj fp wosize fuel in
  assert (res.fp_out == alloc_res.major_fp_out);
  assert (SpecMajorAlloc.major_fl_valid
            alloc_res.major_alloc_out alloc_res.major_fp_out fuel);
  assert (SpecMajorAlloc.major_fl_above_zero
            alloc_res.major_alloc_out alloc_res.major_fp_out fuel);
  assert (SpecMajorAlloc.major_fl_chain_avoids
            alloc_res.major_alloc_out alloc_res.major_fp_out old fuel = true);
  let promote_frame (src: obj_addr)
    : Lemma
        (requires
          Seq.mem src (MH.major_objects alloc_res.major_alloc_out) /\
          src <> old /\
          (match MH.read_word_in_major
             alloc_res.major_alloc_out (hd_address src)
           with
           | Some hdr -> U64.v (getWosize hdr) >= 1
           | None -> False) /\
          SpecMajorAlloc.major_fl_chain_avoids
            alloc_res.major_alloc_out alloc_res.major_fp_out src fuel = false)
        (ensures
          MH.read_word_in_major res.major_out src ==
          MH.read_word_in_major alloc_res.major_alloc_out src)
    =
    SpecMajorAllocSplitShape.major_alloc_head_split_remainder_avoids_allocated_head
      mh fp wosize fuel;
    if src = fp then begin
      assert (SpecMajorAlloc.major_fl_chain_avoids
                alloc_res.major_alloc_out alloc_res.major_fp_out fp fuel = true);
      assert False
    end else begin
      assert (MH.read_word_in_major res.major_out src ==
              MH.read_word_in_major alloc_res.major_alloc_out src)
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires promote_frame);
  chunked_fl_chain_avoids_transfer_on_chain
    alloc_res.major_alloc_out res.major_out old alloc_res.major_fp_out fuel;
  assert (SpecMajorAlloc.major_fl_chain_avoids
            res.major_out res.fp_out old fuel = true)
#pop-options

#restart-solver

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
private let chunked_cheney_forward_normal_preserves_disjoint_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel remaining: nat) (old: obj_addr)
  : Lemma
      (requires
        fuel > 1 /\
        remaining > 0 /\
        chunked_fwd_normal_disjoint_from_old_major
          minor cs.ccs_fwd old /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        SpecMajorAlloc.major_fl_chain_avoids
          cs.ccs_major cs.ccs_fp old fuel = true /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 1 + remaining) /\
        Seq.mem old (MH.major_objects cs.ccs_major))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         chunked_fwd_normal_disjoint_from_old_major
           minor cs'.ccs_fwd old /\
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         SpecMajorAlloc.major_fl_chain_avoids
           cs'.ccs_major cs'.ccs_fp old fuel = true /\
         Seq.mem old (MH.major_objects cs'.ccs_major)))
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
      current_free_head_ne_old_major
        cs.ccs_major cs.ccs_fp fuel old;
      chunked_promote_object_head_split_preserves_chain_avoids
        minor cs.ccs_major addr cs.ccs_fp wz fuel old;
      chunked_cheney_forward_normal_preserves_old_major_objects
        minor cs addr fuel remaining;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      assert (res.new_addr == cs.ccs_fp);
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success
        minor cs addr fuel;
      assert (cs'.ccs_fwd ==
              extend_forwarding cs.ccs_fwd addr cs.ccs_fp);
      if is_infix_in_minor minor addr then
        chunked_fwd_normal_disjoint_from_old_major_extend_excluded
          minor cs.ccs_fwd old addr cs.ccs_fp
      else begin
        assert (cs.ccs_fp <> old);
        chunked_fwd_normal_disjoint_from_old_major_extend_fresh
          minor cs.ccs_fwd old addr cs.ccs_fp
      end
    end
  end

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

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
private let chunked_cheney_forward_one_preserves_disjoint_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel remaining: nat) (old: obj_addr)
  : Lemma
      (requires
        fuel > 1 /\
        chunked_fwd_normal_disjoint_from_old_major
          minor cs.ccs_fwd old /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        SpecMajorAlloc.major_fl_chain_avoids
          cs.ccs_major cs.ccs_fp old fuel = true /\
        CP.chunked_cheney_forward_one_budget_ready minor cs addr remaining /\
        Seq.mem old (MH.major_objects cs.ccs_major))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         chunked_fwd_normal_disjoint_from_old_major
           minor cs'.ccs_fwd old /\
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         SpecMajorAlloc.major_fl_chain_avoids
           cs'.ccs_major cs'.ccs_fp old fuel = true /\
         Seq.mem old (MH.major_objects cs'.ccs_major)))
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
    chunked_cheney_forward_normal_preserves_disjoint_inv
      minor cs parent fuel remaining old;
    let csn =
      ChunkedCheney.chunked_cheney_forward_normal minor cs parent fuel in
    assert (chunked_fwd_normal_disjoint_from_old_major
              minor csn.ccs_fwd old);
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
      chunked_fwd_normal_disjoint_from_old_major_extend_excluded
        minor csn.ccs_fwd old addr sum
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
    chunked_cheney_forward_normal_preserves_disjoint_inv
      minor cs addr fuel remaining old
  end

private let rec chunked_cheney_forward_roots_preserves_disjoint_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel remaining: nat)
  (old: obj_addr)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        chunked_fwd_normal_disjoint_from_old_major
          minor cs.ccs_fwd old /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_chain_avoids
          cs.ccs_major cs.ccs_fp old alloc_fuel = true /\
        CP.chunked_cheney_forward_roots_budget_ready
          minor cs roots idx alloc_fuel remaining /\
        Seq.mem old (MH.major_objects cs.ccs_major))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         chunked_fwd_normal_disjoint_from_old_major
           minor cs'.ccs_fwd old /\
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_chain_avoids
          cs'.ccs_major cs'.ccs_fp old alloc_fuel = true /\
         Seq.mem old (MH.major_objects cs'.ccs_major)))
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
    chunked_cheney_forward_one_preserves_disjoint_inv
      minor cs r alloc_fuel remaining old;
    CP.chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
      minor cs r alloc_fuel remaining;
    chunked_cheney_forward_one_budget_ready_implies_head_split_pre
      minor cs r remaining;
    chunked_cheney_forward_roots_preserves_disjoint_inv
      minor cs' roots (idx + 1) alloc_fuel remaining old
  end

private let rec chunked_cheney_forward_fields_preserves_disjoint_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel remaining: nat)
  (old: obj_addr)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        chunked_fwd_normal_disjoint_from_old_major
          minor cs.ccs_fwd old /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_chain_avoids
          cs.ccs_major cs.ccs_fp old alloc_fuel = true /\
        CP.chunked_cheney_forward_fields_budget_ready
          minor cs parent idx wosize alloc_fuel remaining /\
        Seq.mem old (MH.major_objects cs.ccs_major))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         chunked_fwd_normal_disjoint_from_old_major
           minor cs'.ccs_fwd old /\
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_chain_avoids
          cs'.ccs_major cs'.ccs_fp old alloc_fuel = true /\
         Seq.mem old (MH.major_objects cs'.ccs_major)))
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
    chunked_cheney_forward_one_preserves_disjoint_inv
      minor cs field_val alloc_fuel remaining old;
    CP.chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
      minor cs field_val alloc_fuel remaining;
    chunked_cheney_forward_one_budget_ready_implies_head_split_pre
      minor cs field_val remaining;
    chunked_cheney_forward_fields_preserves_disjoint_inv
      minor cs' parent (idx + 1) wosize alloc_fuel remaining old
  end

private let rec chunked_cheney_scan_preserves_disjoint_inv
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel remaining: nat)
  (old: obj_addr)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        chunked_fwd_normal_disjoint_from_old_major
          minor cs.ccs_fwd old /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_chain_avoids
          cs.ccs_major cs.ccs_fp old alloc_fuel = true /\
        CP.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining /\
        Seq.mem old (MH.major_objects cs.ccs_major))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         chunked_fwd_normal_disjoint_from_old_major
           minor cs'.ccs_fwd old /\
         GenInv.chunked_major_alloc_shape
          cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
          cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_chain_avoids
          cs'.ccs_major cs'.ccs_fp old alloc_fuel = true /\
         Seq.mem old (MH.major_objects cs'.ccs_major)))
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
      chunked_cheney_forward_fields_preserves_disjoint_inv
        minor cs obj 0 wz alloc_fuel remaining old;
      chunked_cheney_scan_preserves_disjoint_inv
        minor cs' (scan + 1) fuel' alloc_fuel remaining old
    end
  else
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel

let chunked_cheney_promote_fwd_normal_disjoint_from_old_major
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  (old: obj_addr)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        Seq.mem old (MH.major_objects major) /\
        SpecMajorAlloc.major_fl_chain_avoids
          major fp old alloc_fuel = true)
      (ensures
        chunked_fwd_normal_disjoint_from_old_major minor
          (ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel).fwd_map old)
  =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  CP.chunked_cheney_promote_budget_ready_elim
    minor major fp roots alloc_fuel remaining;
  chunked_fwd_normal_disjoint_from_old_major_empty minor old;
  assert (CP.chunked_cheney_forward_roots_budget_ready
            minor cs0 roots 0 alloc_fuel remaining);
  chunked_cheney_forward_roots_preserves_disjoint_inv
    minor cs0 roots 0 alloc_fuel remaining old;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  assert (chunked_fwd_normal_disjoint_from_old_major
            minor cs1.ccs_fwd old);
  assert (GenInv.chunked_major_alloc_shape
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
  assert (SpecMajorAlloc.major_fl_chain_avoids
            cs1.ccs_major cs1.ccs_fp old alloc_fuel = true);
  assert (Seq.mem old (MH.major_objects cs1.ccs_major));
  assert (CP.chunked_cheney_scan_budget_ready
            minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel remaining);
  chunked_cheney_scan_preserves_disjoint_inv
    minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel remaining old;
  let cs2 =
    ChunkedCheney.chunked_cheney_scan
      minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel in
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  assert (res.fwd_map == cs2.ccs_fwd)
#pop-options
