module GC.Gen.ChunkedCheneyInjectivity

open FStar.Seq
module U64 = FStar.UInt64
module Classical = FStar.Classical
module IndDesc = FStar.IndefiniteDescription

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Lib.Header

module MH = GC.Spec.MajorHeap
module MHFieldRead = GC.Spec.MajorHeap.FieldRead
module SpecMajorAlloc = GC.Spec.MajorAllocator
module GenInv = GC.Gen.HeapInvariant
module DenseCheney = GC.Gen.Cheney
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedCheneyOrigin = GC.Gen.ChunkedCheneyOrigin
module ChunkedPromote = GC.Gen.ChunkedPromote
module CP = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module MarkDefs = GC.Spec.ChunkedMark.Defs
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedMarkTargetMembership =
  GC.Spec.ChunkedMarkBounded.TargetMembership
module GenMajorGCBridge = GC.Gen.ChunkedMajorGCBridge
module ChunkedUpdate = GC.Gen.ChunkedUpdate
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation

private let rec seq_mem_to_index (#a:eqtype) (x:a) (s:seq a)
  : Ghost nat
    (requires Seq.mem x s)
    (ensures fun i -> i < Seq.length s /\ Seq.index s i == x)
    (decreases Seq.length s)
  =
  if Seq.index s 0 == x then 0
  else begin
    let tl = Seq.slice s 1 (Seq.length s) in
    Seq.lemma_count_slice s 1;
    1 + seq_mem_to_index x tl
  end

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
private let sweep_chunked_is_infix_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        SweepDefs.chunked_is_infix
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        SweepDefs.chunked_is_infix mh obj)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  SpecMajorAlloc.expand_major_heap_old_read mh fresh fp (hd_address obj);
  SweepDefs.chunked_read_header_step mh obj;
  SweepDefs.chunked_read_header_step expanded obj;
  SweepDefs.chunked_is_infix_step mh obj;
  SweepDefs.chunked_is_infix_step expanded obj;
  match MH.read_word_in_major mh (hd_address obj) with
  | Some hdr ->
    SweepDefs.chunked_tag_of_object_some mh obj hdr;
    SweepDefs.chunked_tag_of_object_some expanded obj hdr
  | None ->
    SweepDefs.chunked_tag_of_object_none mh obj;
    SweepDefs.chunked_tag_of_object_none expanded obj
#pop-options

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

#push-options "--split_queries always --z3rlimit 3 --fuel 0 --ifuel 0"
[@"opaque_to_smt"]
let chunked_fwd_noninfix_sources_valid
  (minor: minor_state) (fwd: forwarding_map) : prop =
  forall (x: U64.t).
    fwd x <> 0UL /\
    ~(is_infix_in_minor minor x) ==>
    Seq.mem x (minor_objects minor) /\
    minor_wosize minor x > 0

let chunked_fwd_noninfix_sources_valid_elim
  (minor: minor_state) (fwd: forwarding_map) (x: U64.t)
  : Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor fwd /\
        fwd x <> 0UL /\
        ~(is_infix_in_minor minor x))
      (ensures
        Seq.mem x (minor_objects minor) /\
        minor_wosize minor x > 0)
  =
  reveal_opaque (`%chunked_fwd_noninfix_sources_valid)
    (chunked_fwd_noninfix_sources_valid minor fwd)

private let chunked_fwd_noninfix_sources_valid_empty
  (minor: minor_state)
  : Lemma
      (ensures
        chunked_fwd_noninfix_sources_valid minor empty_forwarding)
  =
  reveal_opaque (`%chunked_fwd_noninfix_sources_valid)
    (chunked_fwd_noninfix_sources_valid minor empty_forwarding);
  let aux (x: U64.t)
    : Lemma
        (requires
          empty_forwarding x <> 0UL /\
          ~(is_infix_in_minor minor x))
        (ensures
          Seq.mem x (minor_objects minor) /\
          minor_wosize minor x > 0)
    =
    assert (empty_forwarding x == 0UL);
    assert False
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)

private let chunked_fwd_noninfix_sources_valid_extend_excluded
  (minor: minor_state) (fwd: forwarding_map) (addr target: U64.t)
  : Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor fwd /\
        is_infix_in_minor minor addr)
      (ensures
        chunked_fwd_noninfix_sources_valid minor
          (extend_forwarding fwd addr target))
  =
  let fwd' = extend_forwarding fwd addr target in
  reveal_opaque (`%chunked_fwd_noninfix_sources_valid)
    (chunked_fwd_noninfix_sources_valid minor fwd');
  let aux (x: U64.t)
    : Lemma
        (requires
          fwd' x <> 0UL /\
          ~(is_infix_in_minor minor x))
        (ensures
          Seq.mem x (minor_objects minor) /\
          minor_wosize minor x > 0)
    =
    if x = addr then begin
      assert (is_infix_in_minor minor x);
      assert False
    end else begin
      assert (fwd' x == fwd x);
      chunked_fwd_noninfix_sources_valid_elim minor fwd x
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)

private let chunked_fwd_noninfix_sources_valid_extend_fresh
  (minor: minor_state) (fwd: forwarding_map) (addr target: U64.t)
  : Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor fwd /\
        Seq.mem addr (minor_objects minor) /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0)
      (ensures
        chunked_fwd_noninfix_sources_valid minor
          (extend_forwarding fwd addr target))
  =
  let fwd' = extend_forwarding fwd addr target in
  reveal_opaque (`%chunked_fwd_noninfix_sources_valid)
    (chunked_fwd_noninfix_sources_valid minor fwd');
  let aux (x: U64.t)
    : Lemma
        (requires
          fwd' x <> 0UL /\
          ~(is_infix_in_minor minor x))
        (ensures
          Seq.mem x (minor_objects minor) /\
          minor_wosize minor x > 0)
    =
    if x = addr then begin
      assert (Seq.mem x (minor_objects minor));
      assert (minor_wosize minor x > 0)
    end else begin
      assert (fwd' x == fwd x);
      chunked_fwd_noninfix_sources_valid_elim minor fwd x
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)
#pop-options

#restart-solver

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
private let chunked_cheney_forward_normal_preserves_fwd_sources_valid
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor cs.ccs_fwd)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         chunked_fwd_noninfix_sources_valid minor cs'.ccs_fwd))
  =
  let cs' =
    ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
  reveal_opaque (`%chunked_fwd_noninfix_sources_valid)
    (chunked_fwd_noninfix_sources_valid minor cs'.ccs_fwd);
  let aux (x: U64.t)
    : Lemma
        (requires
          cs'.ccs_fwd x <> 0UL /\
          ~(is_infix_in_minor minor x))
        (ensures
          Seq.mem x (minor_objects minor) /\
          minor_wosize minor x > 0)
    =
    if not (Seq.mem addr (minor_objects minor)) ||
       cs.ccs_fwd addr <> 0UL
    then begin
      ChunkedCheney.chunked_cheney_forward_normal_noop
        minor cs addr fuel;
      assert (cs' == cs);
      chunked_fwd_noninfix_sources_valid_elim minor cs.ccs_fwd x
    end else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then begin
        ChunkedCheney.chunked_cheney_forward_normal_noop_wz0
          minor cs addr fuel;
        assert (cs' == cs);
        chunked_fwd_noninfix_sources_valid_elim minor cs.ccs_fwd x
      end else begin
        assert (wz > 0);
        let pres =
          ChunkedPromote.chunked_promote_object_with_fuel
            minor cs.ccs_major addr cs.ccs_fp wz fuel in
        if pres.new_addr = 0UL then begin
          ChunkedCheney.chunked_cheney_forward_normal_noop_oom
            minor cs addr fuel;
          assert (cs' == cs);
          chunked_fwd_noninfix_sources_valid_elim minor cs.ccs_fwd x
        end else begin
          ChunkedCheney.chunked_cheney_forward_normal_success
            minor cs addr fuel;
          assert (cs'.ccs_fwd ==
                  extend_forwarding cs.ccs_fwd addr pres.new_addr);
          if x = addr then begin
            if is_infix_in_minor minor addr then begin
              assert (is_infix_in_minor minor x);
              assert False
            end else begin
              assert (Seq.mem x (minor_objects minor));
              assert (minor_wosize minor x > 0)
            end
          end else begin
            ChunkedCheney.chunked_cheney_forward_normal_other_fwd
              minor cs addr x fuel;
            assert (cs'.ccs_fwd x == cs.ccs_fwd x);
            chunked_fwd_noninfix_sources_valid_elim minor cs.ccs_fwd x
          end
        end
      end
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires aux)

private let chunked_cheney_forward_one_preserves_fwd_sources_valid
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor cs.ccs_fwd)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         chunked_fwd_noninfix_sources_valid minor cs'.ccs_fwd))
  =
  let r = ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
  if cs.ccs_fwd addr <> 0UL then begin
    ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr fuel;
    assert (r == cs)
  end else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_preserves_fwd_sources_valid
      minor cs parent fuel;
    let csn = ChunkedCheney.chunked_cheney_forward_normal minor cs parent fuel in
    assert (chunked_fwd_noninfix_sources_valid minor csn.ccs_fwd);
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
      chunked_fwd_noninfix_sources_valid_extend_excluded
        minor csn.ccs_fwd addr sum
    end else begin
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr fuel;
      assert (r == csn)
    end
  end else begin
    if Seq.mem addr (minor_objects minor) then begin
      ChunkedCheney.chunked_cheney_forward_one_normal minor cs addr fuel;
      assert (r ==
        ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel);
      chunked_cheney_forward_normal_preserves_fwd_sources_valid
        minor cs addr fuel
    end else begin
      ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr fuel;
      assert (r == cs)
    end
  end

private let rec chunked_cheney_forward_roots_preserves_fwd_sources_valid
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx alloc_fuel: nat)
  : Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor cs.ccs_fwd)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         chunked_fwd_noninfix_sources_valid minor cs'.ccs_fwd))
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then begin
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs r alloc_fuel in
    chunked_cheney_forward_one_preserves_fwd_sources_valid
      minor cs r alloc_fuel;
    chunked_cheney_forward_roots_preserves_fwd_sources_valid
      minor cs' roots (idx + 1) alloc_fuel
  end

private let rec chunked_cheney_forward_fields_preserves_fwd_sources_valid
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat)
  : Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor cs.ccs_fwd)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         chunked_fwd_noninfix_sources_valid minor cs'.ccs_fwd))
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then begin
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs field_val alloc_fuel in
    chunked_cheney_forward_one_preserves_fwd_sources_valid
      minor cs field_val alloc_fuel;
    chunked_cheney_forward_fields_preserves_fwd_sources_valid
      minor cs' parent (idx + 1) wosize alloc_fuel
  end

private let rec chunked_cheney_scan_preserves_fwd_sources_valid
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (requires
        chunked_fwd_noninfix_sources_valid minor cs.ccs_fwd)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         chunked_fwd_noninfix_sources_valid minor cs'.ccs_fwd))
      (decreases scan_fuel)
  =
  if scan_fuel = 0 || scan >= Seq.length cs.ccs_queue then begin
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel
  end else begin
    assert (scan_fuel > 0);
    ChunkedCheney.chunked_cheney_scan_step
      minor cs scan scan_fuel alloc_fuel;
    let obj = Seq.index cs.ccs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_fields
        minor cs obj 0 wz alloc_fuel in
    chunked_cheney_forward_fields_preserves_fwd_sources_valid
      minor cs obj 0 wz alloc_fuel;
    let fuel' : f:nat{f < scan_fuel} = scan_fuel - 1 in
    chunked_cheney_scan_preserves_fwd_sources_valid
      minor cs' (scan + 1) fuel' alloc_fuel
  end

let chunked_cheney_promote_fwd_noninfix_sources_valid
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  : Lemma
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         chunked_fwd_noninfix_sources_valid minor res.fwd_map))
  =
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ChunkedCheney.ccs_major = major;
      ChunkedCheney.ccs_fp = fp;
      ChunkedCheney.ccs_fwd = empty_forwarding;
      ChunkedCheney.ccs_queue = Seq.empty } in
  chunked_fwd_noninfix_sources_valid_empty minor;
  chunked_cheney_forward_roots_preserves_fwd_sources_valid
    minor cs0 roots 0 alloc_fuel;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  chunked_cheney_scan_preserves_fwd_sources_valid
    minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel
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
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
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

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
private let promoted_target_header_tag_not_infix
  (minor: minor_state) (mh: MH.major_heap)
  (x: U64.t) (target: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        Seq.mem x (minor_objects minor) /\
        U64.v (getTag hdr) == minor_tag minor x /\
        SweepDefs.chunked_read_header mh target == Some hdr)
      (ensures ~(SweepDefs.chunked_is_infix mh target))
  =
  minor_objects_not_infix minor x;
  infix_tag_val ();
  assert (U64.v infix_tag == 249);
  assert (minor_tag minor x <> U64.v infix_tag);
  assert (getTag hdr <> infix_tag);
  SweepDefs.chunked_tag_of_object_some mh target hdr;
  SweepDefs.chunked_is_infix_step mh target;
  assert (SweepDefs.chunked_tag_of_object mh target <> infix_tag);
  assert (~(SweepDefs.chunked_is_infix mh target))
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_cheney_promote_fwd_noninfix_targets_not_infix
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
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
         GenMajorGCBridge.chunked_fwd_noninfix_targets_not_infix
           minor res.fwd_map res.major_final))
  =
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  chunked_cheney_promote_fwd_noninfix_sources_valid
    minor major fp roots alloc_fuel;
  let one (x: U64.t) (target: obj_addr)
    : Lemma
        (requires
          res.fwd_map x == target /\
          res.fwd_map x <> 0UL /\
          ~(is_infix_in_minor minor x))
        (ensures ~(SweepDefs.chunked_is_infix res.major_final target))
    =
    chunked_fwd_noninfix_sources_valid_elim minor res.fwd_map x;
    assert (Seq.mem x (minor_objects minor));
    assert (minor_wosize minor x > 0);
    let field0 : hp_addr = target in
    assert (0 < minor_wosize minor x);
    assert (U64.v field0 == U64.v target);
    assert (U64.v target == U64.v (res.fwd_map x));
    assert (U64.v field0 ==
            U64.v (res.fwd_map x) + 0 * U64.v mword);
    CP.chunked_cheney_promote_fwd_target_fields_match
      minor major fp roots alloc_fuel remaining x 0 field0;
    assert (Seq.mem target (MH.major_objects res.major_final));
    match MH.read_word_in_major res.major_final (hd_address target) with
    | None ->
      assert False
    | Some hdr ->
      assert (U64.v (getTag hdr) == minor_tag minor x);
      SweepDefs.chunked_read_header_step res.major_final target;
      assert (SweepDefs.chunked_read_header res.major_final target == Some hdr);
      promoted_target_header_tag_not_infix
        minor res.major_final x target hdr
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one);
  GenMajorGCBridge.chunked_fwd_noninfix_targets_not_infix_intro
    minor res.fwd_map res.major_final

let chunked_cheney_promote_updated_fwd_noninfix_targets_not_infix
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
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
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final alloc_fuel))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         GenMajorGCBridge.chunked_fwd_noninfix_targets_not_infix
           minor res.fwd_map
           (ChunkedUpdate.chunked_update_major_pointers
             res.major_final res.fwd_map)))
  =
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  let post =
    ChunkedUpdate.chunked_update_major_pointers
      res.major_final res.fwd_map in
  chunked_cheney_promote_fwd_noninfix_sources_valid
    minor major fp roots alloc_fuel;
  GenInv.chunked_major_alloc_shape_elim
    res.major_final res.fp_final alloc_fuel;
  let one (x: U64.t) (target: obj_addr)
    : Lemma
        (requires
          res.fwd_map x == target /\
          res.fwd_map x <> 0UL /\
          ~(is_infix_in_minor minor x))
        (ensures ~(SweepDefs.chunked_is_infix post target))
    =
    chunked_fwd_noninfix_sources_valid_elim minor res.fwd_map x;
    assert (Seq.mem x (minor_objects minor));
    assert (minor_wosize minor x > 0);
    let field0 : hp_addr = target in
    assert (0 < minor_wosize minor x);
    assert (U64.v field0 == U64.v target);
    assert (U64.v target == U64.v (res.fwd_map x));
    assert (U64.v field0 ==
            U64.v (res.fwd_map x) + 0 * U64.v mword);
    CP.chunked_cheney_promote_fwd_target_fields_match
      minor major fp roots alloc_fuel remaining x 0 field0;
    assert (Seq.mem target (MH.major_objects res.major_final));
    match MH.read_word_in_major res.major_final (hd_address target) with
    | None ->
      assert False
    | Some hdr ->
      assert (U64.v (getTag hdr) == minor_tag minor x);
      ChunkedUpdate.chunked_update_major_pointers_preserves_header
        res.major_final res.fwd_map target hdr;
      SweepDefs.chunked_read_header_step post target;
      assert (SweepDefs.chunked_read_header post target == Some hdr);
      promoted_target_header_tag_not_infix
        minor post x target hdr
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one);
  GenMajorGCBridge.chunked_fwd_noninfix_targets_not_infix_intro
    minor res.fwd_map post
#pop-options

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
  GenInv.chunked_major_alloc_shape_elim major fp alloc_fuel;
  CG.chunked_major_field_slot_elim src j field_addr;
  assert (U64.v field_addr == U64.v src + j * U64.v mword);
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

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
private let chunked_cheney_forward_normal_preserves_ranges
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         RangePres.same_chunk_ranges cs.ccs_major cs'.ccs_major))
  =
  if ~(Seq.mem addr (minor_objects minor)) ||
     cs.ccs_fwd addr <> 0UL then begin
    ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel;
    RangePres.same_chunk_ranges_refl cs.ccs_major
  end else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then begin
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0 minor cs addr fuel;
      RangePres.same_chunk_ranges_refl cs.ccs_major
    end else begin
      nat_nonzero_gt_zero wz;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      ChunkedPromote.chunked_promote_object_with_fuel_preserves_ranges
        minor cs.ccs_major addr cs.ccs_fp wz fuel;
      if res.new_addr = 0UL then begin
        ChunkedCheney.chunked_cheney_forward_normal_noop_oom minor cs addr fuel;
        RangePres.same_chunk_ranges_refl cs.ccs_major
      end else
        ChunkedCheney.chunked_cheney_forward_normal_success minor cs addr fuel
    end
  end

private let chunked_cheney_forward_one_preserves_ranges
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         RangePres.same_chunk_ranges cs.ccs_major cs'.ccs_major))
  =
  if cs.ccs_fwd addr <> 0UL then begin
    ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr fuel;
    RangePres.same_chunk_ranges_refl cs.ccs_major
  end else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    ChunkedCheney.chunked_cheney_forward_one_infix minor cs addr fuel;
    chunked_cheney_forward_normal_preserves_ranges minor cs parent fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal minor cs addr fuel;
    chunked_cheney_forward_normal_preserves_ranges minor cs addr fuel
  end

private let rec chunked_cheney_forward_roots_preserves_ranges
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx alloc_fuel: nat)
  : Lemma
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots idx alloc_fuel in
         RangePres.same_chunk_ranges cs.ccs_major cs'.ccs_major))
      (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then begin
    ChunkedCheney.chunked_cheney_forward_roots_base
      minor cs roots idx alloc_fuel;
    RangePres.same_chunk_ranges_refl cs.ccs_major
  end else begin
    ChunkedCheney.chunked_cheney_forward_roots_step
      minor cs roots idx alloc_fuel;
    let r = Seq.index roots idx in
    let cs' = ChunkedCheney.chunked_cheney_forward_one minor cs r alloc_fuel in
    chunked_cheney_forward_one_preserves_ranges minor cs r alloc_fuel;
    chunked_cheney_forward_roots_preserves_ranges
      minor cs' roots (idx + 1) alloc_fuel;
    RangePres.same_chunk_ranges_trans
      cs.ccs_major cs'.ccs_major
      (ChunkedCheney.chunked_cheney_forward_roots
        minor cs' roots (idx + 1) alloc_fuel).ccs_major
  end

private let rec chunked_cheney_forward_fields_preserves_ranges
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat)
  : Lemma
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel in
         RangePres.same_chunk_ranges cs.ccs_major cs'.ccs_major))
      (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then begin
    ChunkedCheney.chunked_cheney_forward_fields_base
      minor cs parent idx wosize alloc_fuel;
    RangePres.same_chunk_ranges_refl cs.ccs_major
  end else begin
    ChunkedCheney.chunked_cheney_forward_fields_step
      minor cs parent idx wosize alloc_fuel;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_one minor cs field_val alloc_fuel in
    chunked_cheney_forward_one_preserves_ranges minor cs field_val alloc_fuel;
    chunked_cheney_forward_fields_preserves_ranges
      minor cs' parent (idx + 1) wosize alloc_fuel;
    RangePres.same_chunk_ranges_trans
      cs.ccs_major cs'.ccs_major
      (ChunkedCheney.chunked_cheney_forward_fields
        minor cs' parent (idx + 1) wosize alloc_fuel).ccs_major
  end

private let rec chunked_cheney_scan_preserves_ranges
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         RangePres.same_chunk_ranges cs.ccs_major cs'.ccs_major))
      (decreases scan_fuel)
  =
  if scan_fuel = 0 || scan >= Seq.length cs.ccs_queue then begin
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel;
    RangePres.same_chunk_ranges_refl cs.ccs_major
  end else begin
    assert (scan_fuel > 0);
    let next_fuel : nat = scan_fuel - 1 in
    ChunkedCheney.chunked_cheney_scan_step
      minor cs scan scan_fuel alloc_fuel;
    let obj = Seq.index cs.ccs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' =
      ChunkedCheney.chunked_cheney_forward_fields
        minor cs obj 0 wz alloc_fuel in
    chunked_cheney_forward_fields_preserves_ranges
      minor cs obj 0 wz alloc_fuel;
    chunked_cheney_scan_preserves_ranges
      minor cs' (scan + 1) next_fuel alloc_fuel;
    RangePres.same_chunk_ranges_trans
      cs.ccs_major cs'.ccs_major
      (ChunkedCheney.chunked_cheney_scan
        minor cs' (scan + 1) next_fuel alloc_fuel).ccs_major
  end

let chunked_cheney_promote_preserves_ranges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  : Lemma
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         RangePres.same_chunk_ranges major res.major_final))
  =
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  chunked_cheney_forward_roots_preserves_ranges
    minor cs0 roots 0 alloc_fuel;
  chunked_cheney_scan_preserves_ranges
    minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel;
  RangePres.same_chunk_ranges_trans
    major cs1.ccs_major
    (ChunkedCheney.chunked_cheney_scan
      minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel).ccs_major
#pop-options

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
  CG.chunked_major_field_slot_elim src j field_addr;
  CP.chunked_cheney_promote_head_split_preserves_old_non_blue_field
    minor major fp roots alloc_fuel src hdr j field_addr old;
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  assert (MH.read_word_in_major res.major_final field_addr == Some old);
  assert (raw == old);
  chunked_cheney_promote_preserves_ranges
    minor major fp roots alloc_fuel;
  MarkDefs.chunked_is_pointer_field_step res.major_final raw;
  assert (MH.is_major_pointer res.major_final raw);
  RangePres.same_chunk_ranges_preserves_is_major_pointer
    major res.major_final old;
  assert (MH.is_major_pointer major old);
  MarkDefs.chunked_is_pointer_field_step major old;
  assert (MarkDefs.chunked_is_pointer_field major old);
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

let chunked_cheney_promote_old_field_source_case
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
  : Tot prop =
  exists (hdr: U64.t). exists (old: U64.t).
    Seq.mem src (MH.major_objects major) /\
    MH.read_word_in_major major (hd_address src) == Some hdr /\
    getColor hdr <> GC.Lib.Header.Blue /\
    U64.v (getTag hdr) < U64.v no_scan_tag /\
    j < U64.v (getWosize hdr) /\
    CG.chunked_major_field_slot src j == Some field_addr /\
    MH.read_word_in_major major field_addr == Some old /\
    (let res =
      ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
     MH.read_word_in_major res.major_final field_addr == Some raw)

let chunked_cheney_promote_fwd_field_source_case
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
  : Tot prop =
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  exists (x: U64.t).
    res.fwd_map x == src /\
    Seq.mem x (minor_objects minor) /\
    ~(is_infix_in_minor minor x) /\
    j < minor_wosize minor x /\
    U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword

let chunked_cheney_promote_field_source_cases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  : Tot prop =
  forall (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t).
    (let res =
      ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
     Seq.mem src (MH.major_objects res.major_final) /\
     ~(GenInv.chunked_is_blue res.major_final src) /\
     ~(CG.chunked_is_no_scan res.major_final src) /\
     j < CG.chunked_wosize_nat_of_object res.major_final src /\
     CG.chunked_major_field_slot src j == Some field_addr /\
     MH.read_word_in_major res.major_final field_addr == Some raw ==>
     chunked_cheney_promote_old_field_source_case
       minor major fp roots alloc_fuel src j field_addr raw \/
     chunked_cheney_promote_fwd_field_source_case
       minor major fp roots alloc_fuel src j field_addr raw)

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
private let selected_head_split_header_read_region
  (mh: MH.major_heap) (idx: nat) (obj x: obj_addr) (old_hdr: U64.t)
  (requested_wz block_wz: nat) (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        Seq.mem x (MH.major_objects mh) /\
        x <> obj /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        MH.read_word_in_major mh (hd_address x) == Some old_hdr /\
        MH.object_wosize_in_chunk (Seq.index mh idx) obj == block_wz /\
        requested_wz > 0 /\
        block_wz - requested_wz >= 2 /\
        U64.v rem_hd ==
          U64.v (hd_address obj) + (1 + requested_wz) * U64.v mword /\
        U64.v rem_obj == U64.v rem_hd + U64.v mword)
      (ensures
        (let c = Seq.index mh idx in
         let hd = hd_address obj in
         let xhd = hd_address x in
         ((MH.word_in_chunk c xhd /\
           (xhd = hd \/
            U64.v xhd + U64.v mword <= U64.v hd \/
            (U64.v hd + U64.v mword <= U64.v xhd /\
             U64.v xhd + U64.v mword <= U64.v rem_hd) \/
            U64.v rem_obj + U64.v mword <= U64.v xhd)) \/
          ~(MH.chunk_contains_addr c xhd))))
  =
  let c = Seq.index mh idx in
  let hd = hd_address obj in
  let xhd = hd_address x in
  MH.read_word_in_major_lookup_index mh xhd old_hdr;
  let xidx = MH.lookup_chunk_index_value mh xhd in
  assert (MH.lookup_chunk_index mh xhd == Some xidx);
  assert (xidx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh xidx) xhd);
  if xidx = idx then begin
    assert (Seq.index mh xidx == c);
    assert (MH.word_in_chunk c xhd);
    MH.major_objects_member_in_lookup_chunk mh idx x;
    assert (Seq.mem x (MH.objects_in_chunk c));
    hd_address_spec obj;
    hd_address_spec x;
    if U64.v x < U64.v obj then begin
      MH.word_aligned_gt_at_least_mword (U64.v obj) (U64.v x);
      assert (U64.v x + U64.v mword <= U64.v obj);
      assert (U64.v hd + U64.v mword == U64.v obj);
      assert (U64.v x <= U64.v hd);
      assert (U64.v xhd + U64.v mword == U64.v x);
      assert (U64.v xhd + U64.v mword <= U64.v hd)
    end else begin
      assert (U64.v obj < U64.v x);
      MH.objects_in_chunk_separated c obj x;
      assert (U64.v x >
              U64.v obj + MH.object_wosize_in_chunk c obj * U64.v mword);
      assert (MH.object_wosize_in_chunk c obj == block_wz);
      let old_end = U64.v hd + (1 + block_wz) * U64.v mword in
      assert (old_end == U64.v obj + block_wz * U64.v mword);
      assert (U64.v x > old_end);
      SpecMajorAlloc.aligned_plus_word_product (U64.v hd) (1 + block_wz);
      assert (old_end % U64.v mword == 0);
      MH.word_aligned_gt_at_least_mword (U64.v x) old_end;
      assert (U64.v x >= old_end + U64.v mword);
      assert (U64.v xhd + U64.v mword == U64.v x);
      assert (U64.v xhd >= old_end);
      assert (requested_wz + 2 <= block_wz);
      FStar.Math.Lemmas.distributivity_add_left (requested_wz + 2) 1 8;
      assert (U64.v mword == 8);
      assert (U64.v rem_obj + U64.v mword ==
              U64.v hd + (requested_wz + 3) * U64.v mword);
      assert (requested_wz + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.lemma_mult_le_right
        (U64.v mword) (requested_wz + 3) (1 + block_wz);
      assert (U64.v rem_obj + U64.v mword <= old_end);
      assert (U64.v rem_obj + U64.v mword <= U64.v xhd)
    end
  end else begin
    if MH.chunk_contains_addr c xhd then begin
      assert (MH.chunk_contains_addr (Seq.index mh xidx) xhd);
      MH.chunks_pairwise_disjoint_index mh idx xidx;
      assert (MH.chunks_disjoint c (Seq.index mh xidx));
      MH.chunks_disjoint_no_shared_addr c (Seq.index mh xidx) xhd;
      assert False
    end
  end

#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 0 --ifuel 0"
private let chunked_promote_object_head_split_preserves_old_header_no_wosize
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2 /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue)
      (ensures
        (let res =
          ChunkedPromote.chunked_promote_object_with_fuel
            minor mh obj fp wosize fuel in
         res.new_addr == fp /\
         GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_out res.fp_out fuel = true /\
         GenInv.chunked_chain_objects_blue res.major_out res.fp_out fuel /\
         Seq.mem src (MH.major_objects res.major_out) /\
         MH.read_word_in_major res.major_out (hd_address src) == Some hdr))
  =
  CP.chunked_promote_object_head_split_preserves_chunked_alloc_shape
    minor mh obj fp wosize fuel;
  CP.chunked_promote_object_head_split_preserves_chain_objects_blue
    minor mh obj fp wosize fuel;
  GenInv.chunked_major_alloc_shape_elim mh fp fuel;
  SpecMajorAlloc.major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  assert (U64.v fp >= U64.v mword);
  assert (U64.v fp < heap_size);
  assert (U64.v fp % U64.v mword == 0);
  let dst : obj_addr = fp in
  if src = dst then begin
    GenInv.chunked_is_blue_header mh src hdr;
    assert (~(GenInv.chunked_is_blue mh src));
    GenInv.chunked_chain_objects_blue_elim mh fp fuel src;
    SpecMajorAlloc.major_fl_chain_avoids_head_ne mh fp src fuel;
    assert False
  end else begin
    assert (src <> fp);
    let hd = hd_address dst in
    let src_hd = hd_address src in
    SpecMajorAlloc.major_fl_head_wosize_current mh fp fuel;
    SpecMajorAlloc.major_fl_head_block_fits_current mh fp fuel;
    SpecMajorAlloc.major_fl_valid_link_lookup_index mh fp fuel;
    let idx = MH.lookup_chunk_index_value mh hd in
    assert (MH.lookup_chunk_index mh hd == Some idx);
    assert (idx < Seq.length mh);
    assert (MH.word_in_chunk (Seq.index mh idx) hd);
    match MH.read_word_in_major mh hd with
    | None -> assert False
    | Some old_head_hdr ->
      let block_wz = U64.v (getWosize old_head_hdr) in
      assert (SpecMajorAlloc.major_fl_head_wosize mh fp == block_wz);
      assert (block_wz < pow2 54);
      assert (block_wz >= wosize + 2);
      assert (block_wz - wosize >= 2);
      assert (wosize < pow2 54);
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (wosize < pow2 64);
      assert (FStar.UInt.size wosize 64);
      match MH.read_word_in_major mh dst with
      | None -> assert False
      | Some next_fp ->
        let c = Seq.index mh idx in
        MH.read_word_in_major_at_lookup_index mh hd idx;
        assert (MH.read_word_in_chunk c hd == old_head_hdr);
        SpecMajorAlloc.major_fl_valid_gives_mem mh fp fuel;
        assert (Seq.mem dst (MH.major_objects mh));
        MH.major_objects_member_in_lookup_chunk mh idx dst;
        assert (Seq.mem dst (MH.objects_in_chunk c));
        assert (MH.object_wosize_in_chunk c dst == block_wz);
        assert (U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c);
        assert (U64.v mword == 8);
        let rem_hd_nat = U64.v hd + (1 + wosize) * 8 in
        let rem_obj_nat = rem_hd_nat + U64.v mword in
        FStar.Math.Lemmas.distributivity_add_left (1 + wosize) 1 8;
        assert ((1 + wosize) * 8 + 8 == (wosize + 2) * 8);
        FStar.Math.Lemmas.paren_add_right (U64.v hd) ((1 + wosize) * 8) 8;
        assert (rem_obj_nat == U64.v hd + (wosize + 2) * 8);
        assert (wosize + 3 <= 1 + block_wz);
        FStar.Math.Lemmas.distributivity_add_left (wosize + 2) 1 8;
        assert ((wosize + 2) * 8 + 8 == (wosize + 3) * 8);
        FStar.Math.Lemmas.paren_add_right (U64.v hd) ((wosize + 2) * 8) 8;
        assert (rem_obj_nat + 8 == U64.v hd + (wosize + 3) * 8);
        assert (rem_obj_nat + 8 <= U64.v hd + (1 + block_wz) * 8);
        assert (rem_obj_nat + 8 <= MH.chunk_end c);
        assert (MH.chunk_end c <= heap_size);
        assert (rem_hd_nat < heap_size);
        assert (rem_obj_nat < heap_size);
        assert (heap_size < pow2 64);
        assert (rem_hd_nat < pow2 64);
        assert (rem_obj_nat < pow2 64);
        assert (rem_obj_nat >= U64.v mword);
        hd_address_spec dst;
        SpecMajorAlloc.aligned_plus_word_product (U64.v hd) (1 + wosize);
        assert (rem_hd_nat % U64.v mword == 0);
        SpecMajorAlloc.aligned_plus_word_product (U64.v hd) (wosize + 2);
        assert (rem_obj_nat % U64.v mword == 0);
        let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
        let rem_obj : obj_addr = U64.uint_to_t rem_obj_nat in
        assert (U64.v rem_hd == rem_hd_nat);
        assert (U64.v rem_obj == rem_obj_nat);
        assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
        SpecMajorAlloc.active_head_split_remainder_words_in_chunk
          c hd block_wz wosize rem_hd rem_obj;
        let rem_wz = block_wz - wosize - 1 in
        assert (rem_wz >= 1);
        assert (rem_wz < pow2 54);
        assert (rem_wz < pow2 64);
        assert (FStar.UInt.size rem_wz 64);
        let rem_wz_u : w:U64.t{U64.v w == rem_wz /\ U64.v w < pow2 54} =
          U64.uint_to_t rem_wz in
        assert (U64.v rem_wz_u == block_wz - wosize - 1);
        SpecMajorAlloc.major_alloc_head_split
          mh dst wosize fuel old_head_hdr next_fp rem_hd rem_obj;
        let alloc_res =
          SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
        selected_head_split_header_read_region
          mh idx dst src hdr wosize block_wz rem_hd rem_obj;
        SpecMajorAlloc.head_split_major_preserves_read_at
          mh idx dst src_hd hdr wosize block_wz next_fp
          rem_wz_u rem_hd rem_obj;
        hd_address_injective src dst;
        assert (src_hd <> hd);
        assert (MH.read_word_in_major
                  alloc_res.major_alloc_out src_hd == Some hdr);
        let res =
          ChunkedPromote.chunked_promote_object_with_fuel
            minor mh obj fp wosize fuel in
        assert (MH.major_objects res.major_out ==
                MH.major_objects alloc_res.major_alloc_out);
        assert (Seq.mem src (MH.major_objects res.major_out));
        assert (Seq.mem src (MH.major_objects alloc_res.major_alloc_out));
        assert (MH.read_word_in_major res.major_out src_hd ==
                MH.read_word_in_major alloc_res.major_alloc_out src_hd)
  end

#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
private let old_source_field_read_exists
  (major: MH.major_heap) (fp: U64.t) (alloc_fuel: nat)
  (src: obj_addr) (hdr: U64.t) (j: nat) (field_addr: hp_addr)
  : Lemma
     (requires
       GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (hd_address src) == Some hdr /\
       j < U64.v (getWosize hdr) /\
       CG.chunked_major_field_slot src j == Some field_addr)
     (ensures
       exists (old: U64.t).
         MH.read_word_in_major major field_addr == Some old)
  =
  GenInv.chunked_major_alloc_shape_elim major fp alloc_fuel;
  CG.chunked_major_field_slot_elim src j field_addr;
  assert (U64.v field_addr == U64.v src + j * U64.v mword);
  assert (U64.v src <= U64.v field_addr);
  assert (j + 1 <= U64.v (getWosize hdr));
  assert (U64.v field_addr + U64.v mword ==
         U64.v src + (j + 1) * U64.v mword);
  FStar.Math.Lemmas.lemma_mult_le_right
    (U64.v mword) (j + 1) (U64.v (getWosize hdr));
  assert (U64.v field_addr + U64.v mword <=
         U64.v src + U64.v (getWosize hdr) * U64.v mword);
  MHFieldRead.major_objects_member_payload_read_some
    major src hdr field_addr;
  match MH.read_word_in_major major field_addr with
  | None -> assert False
  | Some old ->
    FStar.Classical.exists_intro
     (fun old' -> MH.read_word_in_major major field_addr == Some old')
     old
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
let chunked_cheney_promote_old_field_source_case_intro
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  (src: obj_addr) (hdr: U64.t) (j: nat) (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
     (requires
       GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (hd_address src) == Some hdr /\
       getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (getTag hdr) < U64.v no_scan_tag /\
       j < U64.v (getWosize hdr) /\
       CG.chunked_major_field_slot src j == Some field_addr /\
       (let res =
         ChunkedCheney.chunked_cheney_promote
           minor major fp roots alloc_fuel in
        MH.read_word_in_major res.major_final field_addr == Some raw))
     (ensures
       chunked_cheney_promote_old_field_source_case
         minor major fp roots alloc_fuel src j field_addr raw)
  =
  old_source_field_read_exists major fp alloc_fuel src hdr j field_addr;
  match MH.read_word_in_major major field_addr with
  | None -> assert False
  | Some old ->
    FStar.Classical.exists_intro
     (fun hdr' -> exists (old': U64.t).
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (hd_address src) == Some hdr' /\
       getColor hdr' <> GC.Lib.Header.Blue /\
       U64.v (getTag hdr') < U64.v no_scan_tag /\
       j < U64.v (getWosize hdr') /\
       CG.chunked_major_field_slot src j == Some field_addr /\
       MH.read_word_in_major major field_addr == Some old' /\
       (let res =
         ChunkedCheney.chunked_cheney_promote
           minor major fp roots alloc_fuel in
        MH.read_word_in_major res.major_final field_addr == Some raw))
     hdr;
    FStar.Classical.exists_intro
     (fun old' ->
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (hd_address src) == Some hdr /\
       getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (getTag hdr) < U64.v no_scan_tag /\
       j < U64.v (getWosize hdr) /\
       CG.chunked_major_field_slot src j == Some field_addr /\
       MH.read_word_in_major major field_addr == Some old' /\
       (let res =
         ChunkedCheney.chunked_cheney_promote
           minor major fp roots alloc_fuel in
        MH.read_word_in_major res.major_final field_addr == Some raw))
     old
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_cheney_promote_fwd_field_source_case_intro
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  (x: U64.t) (src: obj_addr) (j: nat) (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
     (requires
       (let res =
         ChunkedCheney.chunked_cheney_promote
           minor major fp roots alloc_fuel in
        res.fwd_map x == src /\
        Seq.mem x (minor_objects minor) /\
        ~(is_infix_in_minor minor x) /\
        j < minor_wosize minor x /\
        U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword))
     (ensures
       chunked_cheney_promote_fwd_field_source_case
         minor major fp roots alloc_fuel src j field_addr raw)
  =
  FStar.Classical.exists_intro
    (fun x' ->
     (let res =
       ChunkedCheney.chunked_cheney_promote
         minor major fp roots alloc_fuel in
      res.fwd_map x' == src /\
      Seq.mem x' (minor_objects minor) /\
      ~(is_infix_in_minor minor x') /\
      j < minor_wosize minor x' /\
      U64.v field_addr == U64.v (res.fwd_map x') + j * U64.v mword))
    x
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
private let chunked_cheney_forward_normal_preserves_old_header_no_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2) /\
        Seq.mem src (MH.major_objects cs.ccs_major) /\
        MH.read_word_in_major cs.ccs_major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         GenInv.chunked_chain_objects_blue cs'.ccs_major cs'.ccs_fp fuel /\
         Seq.mem src (MH.major_objects cs'.ccs_major) /\
         MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_normal_noop minor cs addr fuel
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      ChunkedCheney.chunked_cheney_forward_normal_noop_wz0 minor cs addr fuel
    else begin
      assert (wz > 0);
      assert (cs.ccs_fp <> 0UL);
      assert (SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= wz + 2);
      chunked_promote_object_head_split_preserves_old_header_no_wosize
        minor cs.ccs_major addr cs.ccs_fp wz fuel src hdr;
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      assert (res.new_addr == cs.ccs_fp);
      assert (res.new_addr <> 0UL);
      ChunkedCheney.chunked_cheney_forward_normal_success minor cs addr fuel
    end
  end

private let chunked_cheney_forward_one_preserves_old_header_no_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel remaining: nat) (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        CP.chunked_cheney_forward_one_budget_ready
          minor cs addr remaining /\
        Seq.mem src (MH.major_objects cs.ccs_major) /\
        MH.read_word_in_major cs.ccs_major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         GenInv.chunked_chain_objects_blue cs'.ccs_major cs'.ccs_fp fuel /\
         Seq.mem src (MH.major_objects cs'.ccs_major) /\
         MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr))
  =
  CP.chunked_cheney_forward_one_budget_ready_elim minor cs addr remaining;
  if cs.ccs_fwd addr <> 0UL then
    ChunkedCheney.chunked_cheney_forward_one_noop minor cs addr fuel
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_preserves_old_header_no_wosize
      minor cs parent fuel src hdr;
    let cs' = ChunkedCheney.chunked_cheney_forward_normal minor cs parent fuel in
    if cs'.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_pass
        minor cs addr fuel
    else
      ChunkedCheney.chunked_cheney_forward_one_infix_guard_fail
        minor cs addr fuel
  end else begin
    ChunkedCheney.chunked_cheney_forward_one_normal minor cs addr fuel;
    chunked_cheney_forward_normal_preserves_old_header_no_wosize
      minor cs addr fuel src hdr
  end

private let rec chunked_cheney_forward_roots_preserves_old_header_no_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: seq U64.t) (idx: nat) (alloc_fuel remaining: nat)
  (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CP.chunked_cheney_forward_roots_budget_ready
          minor cs roots idx alloc_fuel remaining /\
        Seq.mem src (MH.major_objects cs.ccs_major) /\
        MH.read_word_in_major cs.ccs_major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots idx alloc_fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         Seq.mem src (MH.major_objects cs'.ccs_major) /\
         MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr))
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
    chunked_cheney_forward_one_preserves_old_header_no_wosize
      minor cs r alloc_fuel remaining src hdr;
    assert (Seq.mem src (MH.major_objects cs'.ccs_major));
    assert (MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr);
    chunked_cheney_forward_roots_preserves_old_header_no_wosize
      minor cs' roots (idx + 1) alloc_fuel remaining src hdr
  end

private let rec chunked_cheney_forward_fields_preserves_old_header_no_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel remaining: nat)
  (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CP.chunked_cheney_forward_fields_budget_ready
          minor cs parent idx wosize alloc_fuel remaining /\
        Seq.mem src (MH.major_objects cs.ccs_major) /\
        MH.read_word_in_major cs.ccs_major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         Seq.mem src (MH.major_objects cs'.ccs_major) /\
         MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr))
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
    chunked_cheney_forward_one_preserves_old_header_no_wosize
      minor cs field_val alloc_fuel remaining src hdr;
    assert (Seq.mem src (MH.major_objects cs'.ccs_major));
    assert (MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr);
    chunked_cheney_forward_fields_preserves_old_header_no_wosize
      minor cs' parent (idx + 1) wosize alloc_fuel remaining src hdr
  end

private let rec chunked_cheney_scan_preserves_old_header_no_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel remaining: nat) (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CP.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining /\
        Seq.mem src (MH.major_objects cs.ccs_major) /\
        MH.read_word_in_major cs.ccs_major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         Seq.mem src (MH.major_objects cs'.ccs_major) /\
         MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr))
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
      chunked_cheney_forward_fields_preserves_old_header_no_wosize
        minor cs obj 0 wz alloc_fuel remaining src hdr;
      assert (Seq.mem src (MH.major_objects cs'.ccs_major));
      assert (MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr);
      chunked_cheney_scan_preserves_old_header_no_wosize
        minor cs' (scan + 1) fuel' alloc_fuel remaining src hdr
    end
  else
    ChunkedCheney.chunked_cheney_scan_base
      minor cs scan scan_fuel alloc_fuel

private let chunked_cheney_promote_preserves_old_header_no_wosize
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape res.major_final res.fp_final alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           res.major_final res.fp_final alloc_fuel /\
         Seq.mem src (MH.major_objects res.major_final) /\
         MH.read_word_in_major res.major_final (hd_address src) == Some hdr))
  =
  let cs0 : ChunkedCheney.chunked_cheney_state =
    { ccs_major = major; ccs_fp = fp;
      ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
  CP.chunked_cheney_promote_budget_ready_elim
    minor major fp roots alloc_fuel remaining;
  let cs1 =
    ChunkedCheney.chunked_cheney_forward_roots
      minor cs0 roots 0 alloc_fuel in
  chunked_cheney_forward_roots_preserves_old_header_no_wosize
    minor cs0 roots 0 alloc_fuel remaining src hdr;
  assert (GenInv.chunked_major_alloc_shape cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
  assert (GenInv.chunked_chain_objects_blue
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (CP.chunked_cheney_scan_budget_ready
            minor cs1 0 (DenseCheney.cheney_fuel minor) alloc_fuel remaining);
  assert (Seq.mem src (MH.major_objects cs1.ccs_major));
  assert (MH.read_word_in_major cs1.ccs_major (hd_address src) == Some hdr);
  assert (getColor hdr <> GC.Lib.Header.Blue);
  let scan_fuel = DenseCheney.cheney_fuel minor in
  assert (alloc_fuel > 1);
  assert (GenInv.chunked_major_alloc_shape cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs1.ccs_major cs1.ccs_fp alloc_fuel = true);
  assert (GenInv.chunked_chain_objects_blue
            cs1.ccs_major cs1.ccs_fp alloc_fuel);
  assert (CP.chunked_cheney_scan_budget_ready
            minor cs1 0 scan_fuel alloc_fuel remaining);
  assert (Seq.mem src (MH.major_objects cs1.ccs_major));
  assert (MH.read_word_in_major cs1.ccs_major (hd_address src) == Some hdr);
  assert (getColor hdr <> GC.Lib.Header.Blue);
  chunked_cheney_scan_preserves_old_header_no_wosize
    minor cs1 0 scan_fuel alloc_fuel remaining src hdr;
  assert (
    (let cs' =
      ChunkedCheney.chunked_cheney_scan
        minor cs1 0 scan_fuel alloc_fuel in
     GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp alloc_fuel /\
     SpecMajorAlloc.major_fl_chain_terminates
       cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
     GenInv.chunked_chain_objects_blue
       cs'.ccs_major cs'.ccs_fp alloc_fuel /\
     Seq.mem src (MH.major_objects cs'.ccs_major) /\
     MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr));
  let cs2 =
    ChunkedCheney.chunked_cheney_scan
      minor cs1 0 scan_fuel alloc_fuel in
  assert (GenInv.chunked_major_alloc_shape cs2.ccs_major cs2.ccs_fp alloc_fuel);
  assert (SpecMajorAlloc.major_fl_chain_terminates
            cs2.ccs_major cs2.ccs_fp alloc_fuel = true);
  assert (GenInv.chunked_chain_objects_blue
            cs2.ccs_major cs2.ccs_fp alloc_fuel);
  assert (Seq.mem src (MH.major_objects cs2.ccs_major));
  assert (
    (let cs' =
      ChunkedCheney.chunked_cheney_scan
        minor cs1 0 scan_fuel alloc_fuel in
     MH.read_word_in_major cs'.ccs_major (hd_address src) == Some hdr));
  let res =
    ChunkedCheney.chunked_cheney_promote
      minor major fp roots alloc_fuel in
  let expected : ChunkedCheney.chunked_promote_all_result =
    { major_final = cs2.ccs_major;
      fp_final = cs2.ccs_fp;
      fwd_map = cs2.ccs_fwd } in
  assert (scan_fuel == DenseCheney.cheney_fuel minor);
  ChunkedCheney.chunked_cheney_promote_equation
    minor major fp roots alloc_fuel;
  assert (res == expected);
  assert (res.major_final == cs2.ccs_major)
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_cheney_promote_field_source_cases_from_nonblue_origin
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        minor_infix_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        chunked_cheney_promote_field_source_cases
          minor major fp roots alloc_fuel)
  =
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  CP.chunked_cheney_promote_head_split_preserves_remaining_head_wosize
    minor major fp roots alloc_fuel remaining;
  GenInv.chunked_major_alloc_shape_elim
    res.major_final res.fp_final alloc_fuel;
  let aux (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
        (requires
          Seq.mem src (MH.major_objects res.major_final) /\
          ~(GenInv.chunked_is_blue res.major_final src) /\
          ~(CG.chunked_is_no_scan res.major_final src) /\
          j < CG.chunked_wosize_nat_of_object res.major_final src /\
          CG.chunked_major_field_slot src j == Some field_addr /\
          MH.read_word_in_major res.major_final field_addr == Some raw)
        (ensures
          chunked_cheney_promote_old_field_source_case
            minor major fp roots alloc_fuel src j field_addr raw \/
          chunked_cheney_promote_fwd_field_source_case
            minor major fp roots alloc_fuel src j field_addr raw)
    =
    MH.major_objects_member_header_read_some res.major_final src;
    match MH.read_word_in_major res.major_final (hd_address src) with
    | None -> assert False
    | Some final_hdr ->
      GenInv.chunked_is_blue_header res.major_final src final_hdr;
      CG.chunked_is_no_scan_header res.major_final src final_hdr;
      CG.chunked_wosize_nat_header res.major_final src final_hdr;
      assert (getColor final_hdr <> GC.Lib.Header.Blue);
      assert (U64.v (getTag final_hdr) < U64.v no_scan_tag);
      assert (j < U64.v (getWosize final_hdr));
      if Seq.mem src (MH.major_objects major) &&
         ~(GenInv.chunked_is_blue major src) then begin
        GenInv.chunked_major_alloc_shape_elim major fp alloc_fuel;
        MH.major_objects_member_header_read_some major src;
        match MH.read_word_in_major major (hd_address src) with
        | None -> assert False
        | Some old_hdr ->
          GenInv.chunked_is_blue_header major src old_hdr;
          assert (getColor old_hdr <> GC.Lib.Header.Blue);
          chunked_cheney_promote_preserves_old_header_no_wosize
            minor major fp roots alloc_fuel remaining src old_hdr;
          assert (MH.read_word_in_major res.major_final (hd_address src) ==
                  Some old_hdr);
          assert (old_hdr == final_hdr);
          assert (U64.v (getTag old_hdr) < U64.v no_scan_tag);
          assert (j < U64.v (getWosize old_hdr));
          chunked_cheney_promote_old_field_source_case_intro
            minor major fp roots alloc_fuel
            src old_hdr j field_addr raw;
          assert (chunked_cheney_promote_old_field_source_case
            minor major fp roots alloc_fuel src j field_addr raw)
      end else begin
        ChunkedCheneyOrigin.chunked_cheney_promote_budget_nonblue_origin
          minor major fp roots alloc_fuel remaining src;
        assert (exists (x: U64.t).
          res.fwd_map x == src /\
          Seq.mem x (minor_objects minor) /\
          ~(is_infix_in_minor minor x) /\
          minor_wosize minor x > 0);
        let x = IndDesc.indefinite_description_ghost U64.t
          (fun x ->
            res.fwd_map x == src /\
            Seq.mem x (minor_objects minor) /\
            ~(is_infix_in_minor minor x) /\
            minor_wosize minor x > 0) in
        assert (res.fwd_map x == src);
        assert (Seq.mem x (minor_objects minor));
        assert (~(is_infix_in_minor minor x));
        assert (minor_wosize minor x > 0);
        assert (res.fwd_map x <> 0UL);
        CP.chunked_cheney_promote_fwd_target_header_matches_minor
          minor major fp roots alloc_fuel remaining x;
        let target : obj_addr = res.fwd_map x in
        assert (target == src);
        assert (MH.read_word_in_major res.major_final (hd_address target) ==
                Some final_hdr);
        assert (U64.v (getWosize final_hdr) == minor_wosize minor x);
        assert (j < minor_wosize minor x);
        CG.chunked_major_field_slot_elim src j field_addr;
        assert (U64.v field_addr ==
                U64.v src + j * U64.v mword);
        assert (U64.v field_addr ==
                U64.v (res.fwd_map x) + j * U64.v mword);
        chunked_cheney_promote_fwd_field_source_case_intro
          minor major fp roots alloc_fuel x src j field_addr raw;
        assert (chunked_cheney_promote_fwd_field_source_case
          minor major fp roots alloc_fuel src j field_addr raw)
      end
  in
  let aux_imp (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
        (ensures
          (let res =
            ChunkedCheney.chunked_cheney_promote
              minor major fp roots alloc_fuel in
           Seq.mem src (MH.major_objects res.major_final) /\
           ~(GenInv.chunked_is_blue res.major_final src) /\
           ~(CG.chunked_is_no_scan res.major_final src) /\
           j < CG.chunked_wosize_nat_of_object res.major_final src /\
           CG.chunked_major_field_slot src j == Some field_addr /\
           MH.read_word_in_major res.major_final field_addr == Some raw ==>
           chunked_cheney_promote_old_field_source_case
             minor major fp roots alloc_fuel src j field_addr raw \/
           chunked_cheney_promote_fwd_field_source_case
             minor major fp roots alloc_fuel src j field_addr raw))
    =
    Classical.move_requires_4 aux src j field_addr raw
  in
  Classical.forall_intro_4 aux_imp
#pop-options

private let old_field_source_case_no_infix
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat)
  (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
  : Lemma
      (requires
        GenInv.chunked_major_minor_fields_no_infix_targets minor major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        chunked_cheney_promote_old_field_source_case
          minor major fp roots alloc_fuel src j field_addr raw /\
        is_minor_pointer (to_minor_offset raw))
      (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))
  =
  let goal = ~(is_infix_in_minor minor (to_minor_offset raw)) in
  let old_case =
    chunked_cheney_promote_old_field_source_case
      minor major fp roots alloc_fuel src j field_addr raw in
  let use_hdr (hdr: U64.t) : Lemma
    (requires exists (old: U64.t).
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (hd_address src) == Some hdr /\
       getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (getTag hdr) < U64.v no_scan_tag /\
       j < U64.v (getWosize hdr) /\
       CG.chunked_major_field_slot src j == Some field_addr /\
       MH.read_word_in_major major field_addr == Some old /\
       (let res =
        ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
        MH.read_word_in_major res.major_final field_addr == Some raw))
    (ensures goal)
  =
    let use_old (old: U64.t) : Lemma
      (requires
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (getTag hdr) < U64.v no_scan_tag /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old /\
        (let res =
          ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw))
      (ensures goal)
    =
      chunked_cheney_promote_old_nonblue_field_no_infix
        minor major fp roots alloc_fuel src hdr j field_addr old raw
    in
    Classical.exists_elim goal #U64.t
      #(fun old ->
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (getTag hdr) < U64.v no_scan_tag /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw))
      ()
      (fun old -> Classical.move_requires use_old old)
  in
  Classical.exists_elim goal #U64.t
    #(fun hdr -> exists (old: U64.t).
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (hd_address src) == Some hdr /\
       getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (getTag hdr) < U64.v no_scan_tag /\
       j < U64.v (getWosize hdr) /\
       CG.chunked_major_field_slot src j == Some field_addr /\
       MH.read_word_in_major major field_addr == Some old /\
       (let res =
        ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
        MH.read_word_in_major res.major_final field_addr == Some raw))
    ()
    (fun hdr -> Classical.move_requires use_hdr hdr)

private let fwd_field_source_case_no_infix
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
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
        chunked_cheney_promote_fwd_field_source_case
          minor major fp roots alloc_fuel src j field_addr raw /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw) /\
        is_minor_pointer (to_minor_offset raw))
      (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))
  =
  let goal = ~(is_infix_in_minor minor (to_minor_offset raw)) in
  let use_x (x: U64.t) : Lemma
    (requires
      (let res =
        ChunkedCheney.chunked_cheney_promote
          minor major fp roots alloc_fuel in
       res.fwd_map x == src /\
       Seq.mem x (minor_objects minor) /\
       ~(is_infix_in_minor minor x) /\
       j < minor_wosize minor x /\
       U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword))
    (ensures goal)
  =
    let res =
      ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
    assert (res.fwd_map x <> 0UL);
    assert (U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword);
    chunked_cheney_promote_fwd_target_minor_field_no_infix
      minor major fp roots alloc_fuel remaining x j field_addr raw
  in
  Classical.exists_elim goal #U64.t
    #(fun x ->
      (let res =
        ChunkedCheney.chunked_cheney_promote
          minor major fp roots alloc_fuel in
       res.fwd_map x == src /\
       Seq.mem x (minor_objects minor) /\
       ~(is_infix_in_minor minor x) /\
       j < minor_wosize minor x /\
       U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword))
    ()
    (fun x -> Classical.move_requires use_x x)

let chunked_cheney_promote_major_minor_fields_no_infix_targets
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        minor_infix_wf minor /\
        GenInv.minor_fields_no_infix_targets minor /\
        GenInv.chunked_major_minor_fields_no_infix_targets minor major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         GenInv.chunked_major_minor_fields_no_infix_targets
           minor res.major_final))
  =
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  chunked_cheney_promote_field_source_cases_from_nonblue_origin
    minor major fp roots alloc_fuel remaining;
  let aux (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
        (requires
          Seq.mem src (MH.major_objects res.major_final) /\
          ~(GenInv.chunked_is_blue res.major_final src) /\
          ~(CG.chunked_is_no_scan res.major_final src) /\
          j < CG.chunked_wosize_nat_of_object res.major_final src /\
          CG.chunked_major_field_slot src j == Some field_addr /\
          MH.read_word_in_major res.major_final field_addr == Some raw /\
          is_minor_pointer (to_minor_offset raw))
        (ensures ~(is_infix_in_minor minor (to_minor_offset raw)))
    =
    assert
      (chunked_cheney_promote_old_field_source_case
        minor major fp roots alloc_fuel src j field_addr raw \/
       chunked_cheney_promote_fwd_field_source_case
        minor major fp roots alloc_fuel src j field_addr raw);
    let old_case =
      chunked_cheney_promote_old_field_source_case
        minor major fp roots alloc_fuel src j field_addr raw in
    let fwd_case =
      chunked_cheney_promote_fwd_field_source_case
        minor major fp roots alloc_fuel src j field_addr raw in
    let goal (_: (old_case \/ fwd_case)) =
      ~(is_infix_in_minor minor (to_minor_offset raw)) in
    let old_branch (_: old_case) : Lemma (goal ()) =
      old_field_source_case_no_infix
        minor major fp roots alloc_fuel src j field_addr raw in
    let fwd_branch (_: fwd_case) : Lemma (goal ()) =
      fwd_field_source_case_no_infix
        minor major fp roots alloc_fuel remaining src j field_addr raw in
    Classical.or_elim #old_case #fwd_case #goal old_branch fwd_branch
  in
  let aux_imp (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
        (ensures
          Seq.mem src (MH.major_objects res.major_final) /\
          ~(GenInv.chunked_is_blue res.major_final src) /\
          ~(CG.chunked_is_no_scan res.major_final src) /\
          j < CG.chunked_wosize_nat_of_object res.major_final src /\
          CG.chunked_major_field_slot src j == Some field_addr /\
          MH.read_word_in_major res.major_final field_addr == Some raw /\
          is_minor_pointer (to_minor_offset raw) ==>
          ~(is_infix_in_minor minor (to_minor_offset raw)))
    =
    Classical.move_requires_4 aux src j field_addr raw
  in
  Classical.forall_intro_4 aux_imp;
  GenInv.chunked_major_minor_fields_no_infix_targets_intro
    minor res.major_final
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
[@"opaque_to_smt"]
let chunked_minor_major_fields_nonblue_non_infix_targets
  (minor: minor_state) (mh: MH.major_heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj /\
    MarkDefs.chunked_is_pointer_field mh (minor_read_field minor obj j) ==>
    (let raw = minor_read_field minor obj j in
     let target = MarkDefs.chunked_pointer_field_as_obj_addr mh raw in
     Seq.mem target (MH.major_objects mh) /\
     ~(GenInv.chunked_is_blue mh target) /\
     ~(SweepDefs.chunked_is_infix mh target))

let chunked_minor_major_fields_nonblue_non_infix_targets_elim
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t) (j: nat)
  : Lemma
      (requires
        chunked_minor_major_fields_nonblue_non_infix_targets minor mh /\
        Seq.mem obj (minor_objects minor) /\
        j < minor_wosize minor obj /\
        MarkDefs.chunked_is_pointer_field mh
          (minor_read_field minor obj j))
      (ensures
        (let raw = minor_read_field minor obj j in
         let target = MarkDefs.chunked_pointer_field_as_obj_addr mh raw in
         Seq.mem target (MH.major_objects mh) /\
         ~(GenInv.chunked_is_blue mh target) /\
         ~(SweepDefs.chunked_is_infix mh target)))
  =
  reveal_opaque
    (`%chunked_minor_major_fields_nonblue_non_infix_targets)
    (chunked_minor_major_fields_nonblue_non_infix_targets minor mh)

[@"opaque_to_smt"]
let chunked_minor_fields_miss_chunk
  (minor: minor_state) (fresh: MH.heap_chunk) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    j < minor_wosize minor obj ==>
    ~(MH.pointer_in_chunk fresh (minor_read_field minor obj j))

let chunked_minor_fields_miss_chunk_elim
  (minor: minor_state) (fresh: MH.heap_chunk) (obj: U64.t) (j: nat)
  : Lemma
      (requires
        chunked_minor_fields_miss_chunk minor fresh /\
        Seq.mem obj (minor_objects minor) /\
        j < minor_wosize minor obj)
      (ensures ~(MH.pointer_in_chunk fresh (minor_read_field minor obj j)))
  =
  reveal_opaque
    (`%chunked_minor_fields_miss_chunk)
    (chunked_minor_fields_miss_chunk minor fresh)

private let init_fresh_chunk_pointer_in_chunk
  (fresh: MH.heap_chunk) (fp: U64.t) (v: U64.t)
  : Lemma
      (ensures
        MH.pointer_in_chunk
          (SpecMajorAlloc.init_fresh_chunk fresh fp).chunk_out v ==
        MH.pointer_in_chunk fresh v)
  =
  SpecMajorAlloc.init_fresh_chunk_preserves_range fresh fp

private let expand_major_heap_pointer_field_miss
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (v: U64.t)
  : Lemma
      (requires ~(MH.pointer_in_chunk fresh v))
      (ensures
        MarkDefs.chunked_is_pointer_field
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        MarkDefs.chunked_is_pointer_field mh v)
  =
  let init = SpecMajorAlloc.init_fresh_chunk fresh fp in
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  init_fresh_chunk_pointer_in_chunk fresh fp v;
  assert (~(MH.pointer_in_chunk init.chunk_out v));
  MarkDefs.chunked_is_pointer_field_step expanded v;
  MarkDefs.chunked_is_pointer_field_step mh v;
  MH.major_pointer_add_chunk_miss mh init.chunk_out v

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
let chunked_minor_major_fields_nonblue_non_infix_targets_preserved_by_expansion
  (minor: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires
        chunked_minor_major_fields_nonblue_non_infix_targets minor mh /\
        chunked_minor_fields_miss_chunk minor fresh /\
        MH.chunk_disjoint_from_all fresh mh)
      (ensures
        chunked_minor_major_fields_nonblue_non_infix_targets
          minor (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  let aux_obj (obj: U64.t)
    : Lemma
        (ensures
          forall (j:nat).
            Seq.mem obj (minor_objects minor) /\
            j < minor_wosize minor obj /\
            MarkDefs.chunked_is_pointer_field
              expanded (minor_read_field minor obj j) ==>
            (let raw = minor_read_field minor obj j in
             let target =
               MarkDefs.chunked_pointer_field_as_obj_addr expanded raw in
             Seq.mem target (MH.major_objects expanded) /\
             ~(GenInv.chunked_is_blue expanded target) /\
             ~(SweepDefs.chunked_is_infix expanded target)))
    =
    let aux_j (j: nat)
      : Lemma
          (ensures
            Seq.mem obj (minor_objects minor) /\
            j < minor_wosize minor obj /\
            MarkDefs.chunked_is_pointer_field
              expanded (minor_read_field minor obj j) ==>
            (let raw = minor_read_field minor obj j in
             let target =
               MarkDefs.chunked_pointer_field_as_obj_addr expanded raw in
             Seq.mem target (MH.major_objects expanded) /\
             ~(GenInv.chunked_is_blue expanded target) /\
             ~(SweepDefs.chunked_is_infix expanded target)))
      =
      if Seq.mem obj (minor_objects minor) &&
         j < minor_wosize minor obj &&
         MarkDefs.chunked_is_pointer_field
           expanded (minor_read_field minor obj j)
      then begin
        let raw = minor_read_field minor obj j in
        chunked_minor_fields_miss_chunk_elim minor fresh obj j;
        expand_major_heap_pointer_field_miss mh fresh fp raw;
        assert (MarkDefs.chunked_is_pointer_field mh raw);
        chunked_minor_major_fields_nonblue_non_infix_targets_elim
          minor mh obj j;
        MarkDefs.chunked_pointer_field_as_obj_addr_step mh raw;
        MarkDefs.chunked_pointer_field_as_obj_addr_step expanded raw;
        let target = MarkDefs.chunked_pointer_field_as_obj_addr expanded raw in
        assert (target == (raw <: obj_addr));
        assert (Seq.mem target (MH.major_objects mh));
        SpecMajorAlloc.expand_major_heap_old_object mh fresh fp target;
        GenInv.chunked_is_blue_preserved_by_expansion mh fresh fp target;
        MH.major_object_header_disjoint_from_chunk mh fresh target;
        sweep_chunked_is_infix_preserved_by_expansion mh fresh fp target;
        assert (~(SweepDefs.chunked_is_infix expanded target))
      end
    in
    FStar.Classical.forall_intro aux_j
  in
  FStar.Classical.forall_intro aux_obj;
  reveal_opaque
    (`%chunked_minor_major_fields_nonblue_non_infix_targets)
    (chunked_minor_major_fields_nonblue_non_infix_targets minor expanded)

let chunked_minor_major_fields_nonblue_non_infix_targets_ensure_head_capacity
  (minor: minor_state) (mh: MH.major_heap) (fp: U64.t)
  (fuel: nat) (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        chunked_minor_major_fields_nonblue_non_infix_targets minor mh /\
        (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
         chunked_minor_fields_miss_chunk minor fresh /\
         MH.chunk_disjoint_from_all fresh mh))
      (ensures
        chunked_minor_major_fields_nonblue_non_infix_targets
          minor
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize mh fp < needed then
    chunked_minor_major_fields_nonblue_non_infix_targets_preserved_by_expansion
      minor mh fresh fp
  else
    ()
#pop-options

[@"opaque_to_smt"]
let chunked_nonblue_scanned_raw_targets_in_major
  (mh: MH.major_heap) : prop =
  forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
    Seq.mem obj (MH.major_objects mh) /\
    ~(GenInv.chunked_is_blue mh obj) /\
    ~(MarkDefs.chunked_is_no_scan mh obj) /\
    U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) ==>
    (let v = MarkDefs.chunked_get_field mh obj i in
     if MarkDefs.chunked_is_pointer_field mh v then
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      Seq.mem child_raw (MH.major_objects mh) /\
      ~(SweepDefs.chunked_is_infix mh child_raw)
     else
      True)

private let chunked_nonblue_scanned_raw_targets_in_major_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
          Seq.mem obj (MH.major_objects mh) /\
          ~(GenInv.chunked_is_blue mh obj) /\
          ~(MarkDefs.chunked_is_no_scan mh obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj) ==>
          (let v = MarkDefs.chunked_get_field mh obj i in
           if MarkDefs.chunked_is_pointer_field mh v then
            let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
            Seq.mem child_raw (MH.major_objects mh) /\
            ~(SweepDefs.chunked_is_infix mh child_raw)
           else
            True))
      (ensures chunked_nonblue_scanned_raw_targets_in_major mh)
  =
  reveal_opaque
    (`%chunked_nonblue_scanned_raw_targets_in_major)
    (chunked_nonblue_scanned_raw_targets_in_major mh)

let chunked_nonblue_scanned_raw_targets_in_major_elim
  (mh: MH.major_heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        chunked_nonblue_scanned_raw_targets_in_major mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(GenInv.chunked_is_blue mh obj) /\
        ~(MarkDefs.chunked_is_no_scan mh obj) /\
        U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj))
      (ensures
        (let v = MarkDefs.chunked_get_field mh obj i in
         if MarkDefs.chunked_is_pointer_field mh v then
          let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          Seq.mem child_raw (MH.major_objects mh) /\
          ~(SweepDefs.chunked_is_infix mh child_raw)
         else
          True))
  =
  reveal_opaque
    (`%chunked_nonblue_scanned_raw_targets_in_major)
    (chunked_nonblue_scanned_raw_targets_in_major mh)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_wosize_nat_agrees_with_sweep
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        CG.chunked_wosize_nat_of_object mh obj ==
        U64.v (SweepDefs.chunked_wosize_of_object mh obj))
  =
  MH.major_objects_member_header_read_some mh obj;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  CG.chunked_wosize_nat_header mh obj hdr;
  SweepDefs.chunked_read_header_step mh obj;
  assert (SweepDefs.chunked_read_header mh obj == Some hdr);
  SweepDefs.chunked_wosize_of_object_some mh obj hdr
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_field_slot_mark_index_facts
  (mh: MH.major_heap)
  (src: obj_addr)
  (idx: nat)
  (field_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr)
      (ensures
        idx + 1 < pow2 64 /\
        U64.v field_addr ==
          U64.v (hd_address src) + U64.v mword * (idx + 1) /\
        idx + 1 <= U64.v (SweepDefs.chunked_wosize_of_object mh src))
  =
  chunked_wosize_nat_agrees_with_sweep mh src;
  CG.chunked_major_field_slot_elim src idx field_addr;
  assert (U64.v field_addr == U64.v src + idx * U64.v mword);
  assert (idx + 1 <= U64.v (SweepDefs.chunked_wosize_of_object mh src));
  assert (U64.v (SweepDefs.chunked_wosize_of_object mh src) < pow2 64);
  assert (idx + 1 < pow2 64);
  hd_address_spec src;
  assert_norm (U64.v mword == 8);
  FStar.Math.Lemmas.distributivity_add_left idx 1 (U64.v mword);
  assert (idx * U64.v mword + U64.v mword ==
          (idx + 1) * U64.v mword);
  assert (U64.v (hd_address src) + U64.v mword == U64.v src);
  assert (U64.v field_addr ==
          U64.v (hd_address src) + U64.v mword + idx * U64.v mword);
  assert (U64.v mword + idx * U64.v mword ==
          idx * U64.v mword + U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v (hd_address src)) (U64.v mword)
    (idx * U64.v mword);
  assert (U64.v field_addr ==
          U64.v (hd_address src) +
          (idx * U64.v mword + U64.v mword));
  assert ((idx + 1) * U64.v mword ==
          U64.v mword * (idx + 1));
  assert (U64.v field_addr ==
          U64.v (hd_address src) + U64.v mword * (idx + 1))
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_get_field_from_major_field_slot
  (mh: MH.major_heap)
  (src: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (idx: nat)
  (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx + 1 == U64.v i /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw)
      (ensures MarkDefs.chunked_get_field mh src i == raw)
  =
  chunked_field_slot_mark_index_facts mh src idx field_addr;
  CG.chunked_major_field_slot_elim src idx field_addr;
  assert (U64.v field_addr ==
          U64.v (hd_address src) + U64.v mword * U64.v i);
  assert (U64.v field_addr + U64.v mword <= heap_size);
  let get_field_addr = U64.add (hd_address src) (U64.mul mword i) in
  assert (U64.v (U64.mul mword i) == U64.v mword * U64.v i);
  assert (U64.v get_field_addr ==
          U64.v (hd_address src) + U64.v mword * U64.v i);
  U64.v_inj get_field_addr field_addr;
  assert (get_field_addr == field_addr);
  MarkDefs.chunked_get_field_read_some mh src i raw
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_nonblue_scanned_raw_targets_in_major_from_major_raw_field_targets
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major mh /\
        (forall (target: obj_addr).
          Seq.mem target (MH.major_objects mh) ==> is_pointer_field target) /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh)
      (ensures chunked_nonblue_scanned_raw_targets_in_major mh)
  =
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects mh) /\
          ~(GenInv.chunked_is_blue mh obj) /\
          ~(MarkDefs.chunked_is_no_scan mh obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj))
        (ensures
          (let v = MarkDefs.chunked_get_field mh obj i in
           if MarkDefs.chunked_is_pointer_field mh v then
            let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
            Seq.mem child_raw (MH.major_objects mh) /\
            ~(SweepDefs.chunked_is_infix mh child_raw)
           else
            True))
    =
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      MH.major_objects_member_header_read_some mh obj;
      let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
      assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
      CG.chunked_wosize_nat_header mh obj hdr;
      chunked_wosize_nat_agrees_with_sweep mh obj;
      let idx = U64.v i - 1 in
      assert (idx + 1 == U64.v i);
      assert (idx < CG.chunked_wosize_nat_of_object mh obj);
      assert (CG.chunked_wosize_nat_of_object mh obj ==
              U64.v (getWosize hdr));
      assert (idx < U64.v (getWosize hdr));
      CG.chunked_major_field_slot_of_object_header mh obj hdr idx;
      match CG.chunked_major_field_slot obj idx with
      | None -> assert False
      | Some field_addr ->
        CG.chunked_major_field_slot_elim obj idx field_addr;
        chunked_field_slot_mark_index_facts mh obj idx field_addr;
        MH.read_word_in_major_lookup_index mh (hd_address obj) hdr;
        let hidx = MH.lookup_chunk_index_value mh (hd_address obj) in
        assert (MH.lookup_chunk_index mh (hd_address obj) == Some hidx);
        assert (hidx < Seq.length mh);
        MH.major_objects_member_in_lookup_chunk mh hidx obj;
        MH.objects_in_chunk_member_header_fits (Seq.index mh hidx) obj;
        assert (MH.object_wosize_in_chunk (Seq.index mh hidx) obj ==
                U64.v (getWosize hdr));
        assert (U64.v obj <= U64.v field_addr);
        assert (idx < U64.v (getWosize hdr));
        assert (U64.v field_addr + U64.v mword <=
                U64.v obj + U64.v (getWosize hdr) * U64.v mword);
        MH.major_object_payload_word_in_lookup_chunk mh hidx obj field_addr;
        let raw_v = MH.read_word_in_chunk (Seq.index mh hidx) field_addr in
        MH.read_word_in_major_at_lookup_index mh field_addr hidx;
        assert (MH.read_word_in_major mh field_addr == Some raw_v);
        chunked_get_field_from_major_field_slot mh obj i idx field_addr raw_v;
        assert (v == raw_v);
        assert (MarkDefs.chunked_is_pointer_field mh raw_v);
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major_elim
          mh obj idx field_addr raw_v;
        MarkDefs.chunked_pointer_field_as_obj_addr_step mh raw_v;
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        assert (child_raw ==
                MarkDefs.chunked_pointer_field_as_obj_addr mh raw_v);
        assert (Seq.mem child_raw (MH.major_objects mh));
        assert (is_pointer_field child_raw);
        assert (raw_v == child_raw);
        assert (is_pointer_to raw_v child_raw);
        GenMajorGCBridge.chunked_major_field_targets_non_infix_elim
          mh obj child_raw idx field_addr raw_v
    end
  in
  Classical.forall_intro_2 (Classical.move_requires_2 one);
  chunked_nonblue_scanned_raw_targets_in_major_intro mh
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
private let chunked_major_field_read_some_from_slot
  (mh: MH.major_heap)
  (src: obj_addr)
  (hdr: U64.t)
  (idx: nat)
  (field_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        idx < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src idx == Some field_addr)
      (ensures
        (match MH.read_word_in_major mh field_addr with
         | Some _ -> True
         | None -> False))
  =
  ChunkedUpdate.chunked_wosize_nat_header mh src hdr;
  assert (idx < ChunkedUpdate.chunked_wosize_nat_of_object mh src);
  ChunkedUpdate.chunked_update_field_slot_from_major_field_slot
    src idx field_addr;
  ChunkedUpdate.chunked_update_field_slot_in_object_chunk
    mh src idx field_addr;
  let cidx = MH.lookup_chunk_index_value mh (hd_address src) in
  assert (MH.lookup_chunk_index mh field_addr == Some cidx);
  assert (cidx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh cidx) field_addr);
  MH.read_word_in_major_at_lookup_index mh field_addr cidx
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
private let expand_major_heap_fresh_object_is_blue
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (ensures
        GenInv.chunked_is_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out
          (SpecMajorAlloc.fresh_chunk_object fresh))
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  SpecMajorAlloc.expand_major_heap_header mh fresh fp;
  hd_f_roundtrip fresh.base;
  assert (hd_address fresh_obj == fresh.base);
  let hdr = Some?.v (MH.read_word_in_major expanded (hd_address fresh_obj)) in
  assert (MH.read_word_in_major expanded (hd_address fresh_obj) == Some hdr);
  assert (MH.read_word_in_major expanded fresh.base == Some hdr);
  SpecMajorAlloc.expand_major_heap_header_fields mh fresh fp;
  assert (getColor hdr == GC.Lib.Header.Blue);
  GenInv.chunked_is_blue_header expanded fresh_obj hdr
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
private let chunked_nonblue_scanned_raw_target_preserved_by_expansion_old_case
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_nonblue_scanned_raw_targets_in_major mh /\
        MH.chunk_disjoint_from_all fresh mh /\
        CG.chunked_all_major_object_expansion_safe
          mh fresh (MH.major_objects mh) 0 /\
        Seq.mem obj (MH.major_objects mh) /\
        (let expanded =
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
         ~(GenInv.chunked_is_blue expanded obj) /\
         ~(MarkDefs.chunked_is_no_scan expanded obj) /\
         U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object
                             expanded obj) /\
         MarkDefs.chunked_is_pointer_field
           expanded (MarkDefs.chunked_get_field expanded obj i)))
      (ensures
        (let expanded =
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
         let v = MarkDefs.chunked_get_field expanded obj i in
         let child_raw =
           MarkDefs.chunked_pointer_field_as_obj_addr expanded v in
         Seq.mem child_raw (MH.major_objects expanded) /\
         ~(SweepDefs.chunked_is_infix expanded child_raw)))
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  SpecMajorAlloc.expand_major_heap_wf mh fresh fp;
  let k = seq_mem_to_index obj (MH.major_objects mh) in
  CG.chunked_all_major_object_expansion_safe_at
    mh fresh (MH.major_objects mh) 0 k;
  CG.chunked_major_object_expansion_safe_header mh fresh obj;
  CG.chunked_major_object_expansion_safe_fields mh fresh obj;
  SpecMajorAlloc.expand_major_heap_old_object mh fresh fp obj;
  CG.chunked_wosize_nat_of_object_preserved_by_expansion
    mh fresh fp obj;
  CG.chunked_is_no_scan_preserved_by_expansion mh fresh fp obj;
  MH.major_objects_member_header_read_some mh obj;
  let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
  assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
  SweepDefs.chunked_read_header_step mh obj;
  assert (SweepDefs.chunked_read_header mh obj == Some hdr);
  CG.chunked_wosize_nat_header mh obj hdr;
  SweepDefs.chunked_wosize_of_object_some mh obj hdr;
  chunked_wosize_nat_agrees_with_sweep expanded obj;
  assert (CG.chunked_wosize_nat_of_object mh obj ==
          U64.v (SweepDefs.chunked_wosize_of_object mh obj));
  assert (CG.chunked_wosize_nat_of_object expanded obj ==
          U64.v (SweepDefs.chunked_wosize_of_object expanded obj));
  assert (U64.v i <=
          U64.v (SweepDefs.chunked_wosize_of_object mh obj));
  let idx = U64.v i - 1 in
  assert (idx + 1 == U64.v i);
  assert (idx < CG.chunked_wosize_nat_of_object mh obj);
  CG.chunked_major_field_slot_of_object_header mh obj hdr idx;
  match CG.chunked_major_field_slot obj idx with
  | None -> assert False
  | Some field_addr ->
    CG.chunked_major_field_slot_elim obj idx field_addr;
    CG.chunked_major_field_expansion_safe_at
      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj)
      0 idx field_addr 0UL;
    SpecMajorAlloc.expand_major_heap_old_read mh fresh fp field_addr;
    chunked_major_field_read_some_from_slot
      mh obj hdr idx field_addr;
    let old = Some?.v (MH.read_word_in_major mh field_addr) in
    assert (MH.read_word_in_major mh field_addr == Some old);
    CG.chunked_major_field_expansion_safe_at
      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj)
      0 idx field_addr old;
    assert (~(MH.pointer_in_chunk fresh old));
    assert (MH.read_word_in_major expanded field_addr == Some old);
    chunked_get_field_from_major_field_slot
      expanded obj i idx field_addr old;
    let v = MarkDefs.chunked_get_field expanded obj i in
    assert (v == old);
    expand_major_heap_pointer_field_miss mh fresh fp old;
    assert (MarkDefs.chunked_is_pointer_field mh old);
    chunked_get_field_from_major_field_slot
      mh obj i idx field_addr old;
    assert (MarkDefs.chunked_get_field mh obj i == old);
    GenInv.chunked_is_blue_preserved_by_expansion
      mh fresh fp obj;
    assert (~(GenInv.chunked_is_blue mh obj));
    SweepDefs.chunked_read_header_step mh obj;
    assert (SweepDefs.chunked_read_header mh obj == Some hdr);
    SpecMajorAlloc.expand_major_heap_old_read mh fresh fp (hd_address obj);
    assert (MH.read_word_in_major expanded (hd_address obj) == Some hdr);
    SweepDefs.chunked_read_header_step expanded obj;
    assert (SweepDefs.chunked_read_header expanded obj == Some hdr);
    SweepDefs.chunked_tag_of_object_some mh obj hdr;
    SweepDefs.chunked_tag_of_object_some expanded obj hdr;
    MarkDefs.chunked_is_no_scan_step expanded obj;
    MarkDefs.chunked_is_no_scan_step mh obj;
    assert (MarkDefs.chunked_is_no_scan expanded obj ==
            MarkDefs.chunked_is_no_scan mh obj);
    assert (~(MarkDefs.chunked_is_no_scan mh obj));
    chunked_nonblue_scanned_raw_targets_in_major_elim mh obj i;
    let target0 = MarkDefs.chunked_pointer_field_as_obj_addr mh old in
    assert (Seq.mem target0 (MH.major_objects mh));
    MarkDefs.chunked_pointer_field_as_obj_addr_step mh old;
    MarkDefs.chunked_pointer_field_as_obj_addr_step expanded v;
    assert (target0 == MarkDefs.chunked_pointer_field_as_obj_addr expanded v);
    SpecMajorAlloc.expand_major_heap_old_object mh fresh fp target0;
    MH.major_object_header_disjoint_from_chunk mh fresh target0;
    sweep_chunked_is_infix_preserved_by_expansion mh fresh fp target0;
    assert (Seq.mem
              (MarkDefs.chunked_pointer_field_as_obj_addr expanded v)
              (MH.major_objects expanded));
    assert (~(SweepDefs.chunked_is_infix expanded
              (MarkDefs.chunked_pointer_field_as_obj_addr expanded v)))
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 0"
let chunked_nonblue_scanned_raw_targets_in_major_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_nonblue_scanned_raw_targets_in_major mh /\
        MH.chunk_disjoint_from_all fresh mh /\
        CG.chunked_all_major_object_expansion_safe
          mh fresh (MH.major_objects mh) 0)
      (ensures
        chunked_nonblue_scanned_raw_targets_in_major
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  SpecMajorAlloc.expand_major_heap_wf mh fresh fp;
  SpecMajorAlloc.expand_major_heap_objects mh fresh fp;
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects expanded) /\
          ~(GenInv.chunked_is_blue expanded obj) /\
          ~(MarkDefs.chunked_is_no_scan expanded obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object
                              expanded obj))
        (ensures
          (let v = MarkDefs.chunked_get_field expanded obj i in
           if MarkDefs.chunked_is_pointer_field expanded v then
            let child_raw =
              MarkDefs.chunked_pointer_field_as_obj_addr expanded v in
            Seq.mem child_raw (MH.major_objects expanded) /\
            ~(SweepDefs.chunked_is_infix expanded child_raw)
           else
            True))
    =
    let v = MarkDefs.chunked_get_field expanded obj i in
    if MarkDefs.chunked_is_pointer_field expanded v then begin
      if obj = fresh_obj then begin
        expand_major_heap_fresh_object_is_blue mh fresh fp;
        assert (GenInv.chunked_is_blue expanded obj);
        assert False
      end else begin
        if ~(Seq.mem obj (MH.major_objects mh)) then begin
          GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
            fresh_obj obj (MH.major_objects mh);
          assert False
        end;
        assert (Seq.mem obj (MH.major_objects mh));
        chunked_nonblue_scanned_raw_target_preserved_by_expansion_old_case
          mh fresh fp obj i
      end
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one);
  chunked_nonblue_scanned_raw_targets_in_major_intro expanded

let chunked_nonblue_scanned_raw_targets_in_major_ensure_head_capacity
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_nonblue_scanned_raw_targets_in_major mh /\
        (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
          MH.chunk_disjoint_from_all fresh mh /\
          CG.chunked_all_major_object_expansion_safe
            mh fresh (MH.major_objects mh) 0))
      (ensures
        chunked_nonblue_scanned_raw_targets_in_major
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize mh fp < needed then
    chunked_nonblue_scanned_raw_targets_in_major_preserved_by_expansion
      mh fresh fp
  else
    ()
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
private let chunked_cheney_promote_preserves_old_nonblue_non_infix
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  (target: obj_addr)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        Seq.mem target (MH.major_objects major) /\
        ~(GenInv.chunked_is_blue major target) /\
        ~(SweepDefs.chunked_is_infix major target))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         ~(SweepDefs.chunked_is_infix res.major_final target)))
  =
  GenInv.chunked_major_alloc_shape_elim major fp alloc_fuel;
  MH.major_objects_member_header_read_some major target;
  match MH.read_word_in_major major (hd_address target) with
  | None -> assert False
  | Some hdr ->
    GenInv.chunked_is_blue_header major target hdr;
    assert (getColor hdr <> GC.Lib.Header.Blue);
    SweepDefs.chunked_read_header_step major target;
    assert (SweepDefs.chunked_read_header major target == Some hdr);
    SweepDefs.chunked_tag_of_object_some major target hdr;
    SweepDefs.chunked_is_infix_step major target;
    assert (SweepDefs.chunked_tag_of_object major target == getTag hdr);
    assert (getTag hdr <> infix_tag);
    chunked_cheney_promote_preserves_old_header_no_wosize
      minor major fp roots alloc_fuel remaining target hdr;
    let res =
      ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
    assert (MH.read_word_in_major res.major_final (hd_address target) ==
            Some hdr);
    SweepDefs.chunked_read_header_step res.major_final target;
    assert (SweepDefs.chunked_read_header res.major_final target == Some hdr);
    SweepDefs.chunked_tag_of_object_some res.major_final target hdr;
    SweepDefs.chunked_is_infix_step res.major_final target;
    assert (SweepDefs.chunked_tag_of_object res.major_final target == getTag hdr);
    assert (~(SweepDefs.chunked_is_infix res.major_final target))

private let old_field_source_case_scanned_raw_target
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
  : Lemma
      (requires
        GenInv.chunked_no_pointer_to_blue major /\
        chunked_nonblue_scanned_raw_targets_in_major major /\
        (forall (target: obj_addr).
          Seq.mem target (MH.major_objects major) ==> is_pointer_field target) /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        chunked_cheney_promote_old_field_source_case
          minor major fp roots alloc_fuel src j field_addr raw /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MarkDefs.chunked_is_pointer_field res.major_final raw))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         let target =
          MarkDefs.chunked_pointer_field_as_obj_addr res.major_final raw in
         Seq.mem target (MH.major_objects res.major_final) /\
         ~(SweepDefs.chunked_is_infix res.major_final target)))
  =
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  let goal =
    let target =
      MarkDefs.chunked_pointer_field_as_obj_addr res.major_final raw in
    Seq.mem target (MH.major_objects res.major_final) /\
    ~(SweepDefs.chunked_is_infix res.major_final target) in
  let use_hdr (hdr: U64.t) : Lemma
    (requires exists (old: U64.t).
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (hd_address src) == Some hdr /\
       getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (getTag hdr) < U64.v no_scan_tag /\
       j < U64.v (getWosize hdr) /\
       CG.chunked_major_field_slot src j == Some field_addr /\
       MH.read_word_in_major major field_addr == Some old /\
       MH.read_word_in_major res.major_final field_addr == Some raw)
    (ensures goal)
  =
    let use_old (old: U64.t) : Lemma
      (requires
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (getTag hdr) < U64.v no_scan_tag /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old /\
        MH.read_word_in_major res.major_final field_addr == Some raw)
      (ensures goal)
    =
      GenInv.chunked_major_alloc_shape_elim major fp alloc_fuel;
      assert (MH.well_formed_major_heap major);
      CG.chunked_major_field_slot_elim src j field_addr;
      assert (U64.v field_addr == U64.v src + j * U64.v mword);
      CP.chunked_cheney_promote_head_split_preserves_old_non_blue_field
        minor major fp roots alloc_fuel src hdr j field_addr old;
      assert (MH.read_word_in_major res.major_final field_addr == Some old);
      assert (raw == old);
      chunked_cheney_promote_preserves_ranges
        minor major fp roots alloc_fuel;
      MarkDefs.chunked_is_pointer_field_step res.major_final raw;
      assert (MH.is_major_pointer res.major_final raw);
      RangePres.same_chunk_ranges_preserves_is_major_pointer
        major res.major_final old;
      assert (MH.is_major_pointer major old);
      MarkDefs.chunked_is_pointer_field_step major old;
      assert (MarkDefs.chunked_is_pointer_field major old);
      CG.chunked_wosize_nat_header major src hdr;
      assert (j < CG.chunked_wosize_nat_of_object major src);
      let field_i: (i: U64.t{U64.v i >= 1}) =
        U64.uint_to_t (j + 1) in
      U64.vu_inv (j + 1);
      assert (U64.v field_i == j + 1);
      assert (j + 1 <= U64.v (getWosize hdr));
      chunked_get_field_from_major_field_slot
        major src field_i j field_addr old;
      assert (MarkDefs.chunked_get_field major src field_i == old);
      SweepDefs.chunked_read_header_step major src;
      assert (SweepDefs.chunked_read_header major src == Some hdr);
      SweepDefs.chunked_wosize_of_object_some major src hdr;
      SweepDefs.chunked_tag_of_object_some major src hdr;
      MarkDefs.chunked_is_no_scan_step major src;
      assert (~(MarkDefs.chunked_is_no_scan major src));
      GenInv.chunked_is_blue_header major src hdr;
      assert (~(GenInv.chunked_is_blue major src));
      assert (U64.v (SweepDefs.chunked_wosize_of_object major src) ==
              U64.v (getWosize hdr));
      assert (U64.v field_i <=
              U64.v (SweepDefs.chunked_wosize_of_object major src));
      chunked_nonblue_scanned_raw_targets_in_major_elim
        major src field_i;
      let target0 = MarkDefs.chunked_pointer_field_as_obj_addr major old in
      assert (Seq.mem target0 (MH.major_objects major));
      MarkDefs.chunked_pointer_field_as_obj_addr_step major old;
      assert (target0 == old);
      assert (is_pointer_field target0);
      assert (is_pointer_to old target0);
      GenInv.chunked_no_pointer_to_blue_elim
        major src target0 j field_addr old;
      assert (~(GenInv.chunked_is_blue major target0));
      assert (~(SweepDefs.chunked_is_infix major target0));
      CP.chunked_cheney_promote_head_split_preserves_old_major_objects
        minor major fp roots alloc_fuel;
      assert (Seq.mem target0 (MH.major_objects res.major_final));
      chunked_cheney_promote_preserves_old_nonblue_non_infix
        minor major fp roots alloc_fuel remaining target0;
      MarkDefs.chunked_pointer_field_as_obj_addr_step res.major_final raw;
      assert (MarkDefs.chunked_pointer_field_as_obj_addr res.major_final raw ==
              raw);
      assert (target0 == MarkDefs.chunked_pointer_field_as_obj_addr
                         res.major_final raw);
      assert (goal)
    in
    Classical.exists_elim goal #U64.t
      #(fun old ->
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (getTag hdr) < U64.v no_scan_tag /\
        j < U64.v (getWosize hdr) /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old /\
        MH.read_word_in_major res.major_final field_addr == Some raw)
      ()
      (fun old -> Classical.move_requires use_old old)
  in
  Classical.exists_elim goal #U64.t
    #(fun hdr -> exists (old: U64.t).
       Seq.mem src (MH.major_objects major) /\
       MH.read_word_in_major major (hd_address src) == Some hdr /\
       getColor hdr <> GC.Lib.Header.Blue /\
       U64.v (getTag hdr) < U64.v no_scan_tag /\
       j < U64.v (getWosize hdr) /\
       CG.chunked_major_field_slot src j == Some field_addr /\
       MH.read_word_in_major major field_addr == Some old /\
       MH.read_word_in_major res.major_final field_addr == Some raw)
    ()
    (fun hdr -> Classical.move_requires use_hdr hdr)

private let fwd_field_source_case_scanned_raw_target
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  (src: obj_addr) (j: nat) (field_addr: hp_addr) (raw: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        chunked_minor_major_fields_nonblue_non_infix_targets minor major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        chunked_cheney_promote_fwd_field_source_case
          minor major fp roots alloc_fuel src j field_addr raw /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some raw /\
         MarkDefs.chunked_is_pointer_field res.major_final raw))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         let target =
          MarkDefs.chunked_pointer_field_as_obj_addr res.major_final raw in
         Seq.mem target (MH.major_objects res.major_final) /\
         ~(SweepDefs.chunked_is_infix res.major_final target)))
  =
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  let goal =
    let target =
      MarkDefs.chunked_pointer_field_as_obj_addr res.major_final raw in
    Seq.mem target (MH.major_objects res.major_final) /\
    ~(SweepDefs.chunked_is_infix res.major_final target) in
  let use_x (x: U64.t) : Lemma
    (requires
      res.fwd_map x == src /\
      Seq.mem x (minor_objects minor) /\
      ~(is_infix_in_minor minor x) /\
      j < minor_wosize minor x /\
      U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword)
    (ensures goal)
  =
    assert (res.fwd_map x <> 0UL);
    CP.chunked_cheney_promote_fwd_target_fields_match
      minor major fp roots alloc_fuel remaining x j field_addr;
    assert (MH.read_word_in_major res.major_final field_addr ==
            Some (minor_read_field minor x j));
    assert (raw == minor_read_field minor x j);
    chunked_cheney_promote_preserves_ranges
      minor major fp roots alloc_fuel;
    MarkDefs.chunked_is_pointer_field_step res.major_final raw;
    assert (MH.is_major_pointer res.major_final raw);
    RangePres.same_chunk_ranges_preserves_is_major_pointer
      major res.major_final raw;
    assert (MH.is_major_pointer major raw);
    MarkDefs.chunked_is_pointer_field_step major raw;
    assert (MarkDefs.chunked_is_pointer_field major (minor_read_field minor x j));
    chunked_minor_major_fields_nonblue_non_infix_targets_elim
      minor major x j;
    let target0 = MarkDefs.chunked_pointer_field_as_obj_addr major raw in
    assert (Seq.mem target0 (MH.major_objects major));
    assert (~(GenInv.chunked_is_blue major target0));
    assert (~(SweepDefs.chunked_is_infix major target0));
    CP.chunked_cheney_promote_head_split_preserves_old_major_objects
      minor major fp roots alloc_fuel;
    assert (Seq.mem target0 (MH.major_objects res.major_final));
    chunked_cheney_promote_preserves_old_nonblue_non_infix
      minor major fp roots alloc_fuel remaining target0;
    MarkDefs.chunked_pointer_field_as_obj_addr_step major raw;
    MarkDefs.chunked_pointer_field_as_obj_addr_step res.major_final raw;
    assert (target0 == MarkDefs.chunked_pointer_field_as_obj_addr
                       res.major_final raw);
    assert (goal)
  in
  Classical.exists_elim goal #U64.t
    #(fun x ->
      res.fwd_map x == src /\
      Seq.mem x (minor_objects minor) /\
      ~(is_infix_in_minor minor x) /\
      j < minor_wosize minor x /\
      U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword)
    ()
    (fun x -> Classical.move_requires use_x x)

let chunked_cheney_promote_nonblue_scanned_raw_targets_in_major
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        minor_infix_wf minor /\
        GenInv.chunked_no_pointer_to_blue major /\
        chunked_nonblue_scanned_raw_targets_in_major major /\
        (forall (target: obj_addr).
          Seq.mem target (MH.major_objects major) ==> is_pointer_field target) /\
        chunked_minor_major_fields_nonblue_non_infix_targets minor major /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CP.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        CP.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         chunked_nonblue_scanned_raw_targets_in_major res.major_final))
  =
  let res =
    ChunkedCheney.chunked_cheney_promote minor major fp roots alloc_fuel in
  chunked_cheney_promote_field_source_cases_from_nonblue_origin
    minor major fp roots alloc_fuel remaining;
  CP.chunked_cheney_promote_head_split_preserves_remaining_head_wosize
    minor major fp roots alloc_fuel remaining;
  GenInv.chunked_major_alloc_shape_elim
    res.major_final res.fp_final alloc_fuel;
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects res.major_final) /\
          ~(GenInv.chunked_is_blue res.major_final obj) /\
          ~(MarkDefs.chunked_is_no_scan res.major_final obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object
                              res.major_final obj))
        (ensures
          (let v = MarkDefs.chunked_get_field res.major_final obj i in
           if MarkDefs.chunked_is_pointer_field res.major_final v then
            let child_raw =
              MarkDefs.chunked_pointer_field_as_obj_addr res.major_final v in
            Seq.mem child_raw (MH.major_objects res.major_final) /\
            ~(SweepDefs.chunked_is_infix res.major_final child_raw)
           else
            True))
    =
    let v = MarkDefs.chunked_get_field res.major_final obj i in
    if MarkDefs.chunked_is_pointer_field res.major_final v then begin
      MH.major_objects_member_header_read_some res.major_final obj;
      let hdr =
        Some?.v
          (MH.read_word_in_major res.major_final (hd_address obj)) in
      assert (MH.read_word_in_major res.major_final (hd_address obj) ==
              Some hdr);
      GenInv.chunked_is_blue_header res.major_final obj hdr;
      assert (getColor hdr <> GC.Lib.Header.Blue);
      SweepDefs.chunked_read_header_step res.major_final obj;
      assert (SweepDefs.chunked_read_header res.major_final obj == Some hdr);
      SweepDefs.chunked_tag_of_object_some res.major_final obj hdr;
      MarkDefs.chunked_is_no_scan_step res.major_final obj;
      assert (U64.v (getTag hdr) < U64.v no_scan_tag);
      CG.chunked_is_no_scan_header res.major_final obj hdr;
      assert (~(CG.chunked_is_no_scan res.major_final obj));
      CG.chunked_wosize_nat_header res.major_final obj hdr;
      SweepDefs.chunked_wosize_of_object_some res.major_final obj hdr;
      assert (CG.chunked_wosize_nat_of_object res.major_final obj ==
              U64.v (SweepDefs.chunked_wosize_of_object
                      res.major_final obj));
      let idx = U64.v i - 1 in
      assert (idx + 1 == U64.v i);
      assert (idx < CG.chunked_wosize_nat_of_object res.major_final obj);
      CG.chunked_major_field_slot_of_object_header
        res.major_final obj hdr idx;
      match CG.chunked_major_field_slot obj idx with
      | None -> assert False
      | Some field_addr ->
        CG.chunked_major_field_slot_elim obj idx field_addr;
        chunked_field_slot_mark_index_facts
          res.major_final obj idx field_addr;
        MH.read_word_in_major_lookup_index
          res.major_final (hd_address obj) hdr;
        let hidx = MH.lookup_chunk_index_value
          res.major_final (hd_address obj) in
        assert (MH.lookup_chunk_index res.major_final (hd_address obj) ==
                Some hidx);
        assert (hidx < Seq.length res.major_final);
        MH.major_objects_member_in_lookup_chunk res.major_final hidx obj;
        MH.objects_in_chunk_member_header_fits
          (Seq.index res.major_final hidx) obj;
        assert (MH.object_wosize_in_chunk
                  (Seq.index res.major_final hidx) obj ==
                U64.v (getWosize hdr));
        assert (U64.v field_addr == U64.v obj + idx * U64.v mword);
        assert (idx + 1 <= U64.v (getWosize hdr));
        FStar.Math.Lemmas.lemma_mult_le_right
          (U64.v mword) (idx + 1) (U64.v (getWosize hdr));
        FStar.Math.Lemmas.distributivity_add_left idx 1 (U64.v mword);
        assert (idx * U64.v mword + U64.v mword ==
                (idx + 1) * U64.v mword);
        FStar.Math.Lemmas.paren_add_right
          (U64.v obj) (idx * U64.v mword) (U64.v mword);
        FStar.Math.Lemmas.lemma_mult_le_left idx 0 (U64.v mword);
        assert (idx * 0 == 0);
        assert (idx * U64.v mword >= 0);
        assert (U64.v obj <= U64.v obj + idx * U64.v mword);
        assert (U64.v obj <= U64.v field_addr);
        assert (U64.v field_addr + U64.v mword <=
                U64.v obj + U64.v (getWosize hdr) * U64.v mword);
        MH.major_object_payload_word_in_lookup_chunk
          res.major_final hidx obj field_addr;
        let raw_v =
          MH.read_word_in_chunk (Seq.index res.major_final hidx) field_addr in
        MH.read_word_in_major_at_lookup_index
          res.major_final field_addr hidx;
        assert (MH.read_word_in_major res.major_final field_addr ==
                Some raw_v);
        chunked_get_field_from_major_field_slot
          res.major_final obj i idx field_addr raw_v;
        assert (v == raw_v);
        assert
          (chunked_cheney_promote_old_field_source_case
            minor major fp roots alloc_fuel obj idx field_addr raw_v \/
           chunked_cheney_promote_fwd_field_source_case
            minor major fp roots alloc_fuel obj idx field_addr raw_v);
        let old_case =
          chunked_cheney_promote_old_field_source_case
            minor major fp roots alloc_fuel obj idx field_addr raw_v in
        let fwd_case =
          chunked_cheney_promote_fwd_field_source_case
            minor major fp roots alloc_fuel obj idx field_addr raw_v in
        let goal2 (_: (old_case \/ fwd_case)) =
          let child_raw =
            MarkDefs.chunked_pointer_field_as_obj_addr
              res.major_final raw_v in
          Seq.mem child_raw (MH.major_objects res.major_final) /\
          ~(SweepDefs.chunked_is_infix res.major_final child_raw) in
        let old_branch (_: old_case) : Lemma (goal2 ()) =
          old_field_source_case_scanned_raw_target
            minor major fp roots alloc_fuel remaining
            obj idx field_addr raw_v in
        let fwd_branch (_: fwd_case) : Lemma (goal2 ()) =
          fwd_field_source_case_scanned_raw_target
            minor major fp roots alloc_fuel remaining
            obj idx field_addr raw_v in
        Classical.or_elim #old_case #fwd_case #goal2
          old_branch fwd_branch
    end
  in
  let one_imp (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (ensures
          Seq.mem obj (MH.major_objects res.major_final) /\
          ~(GenInv.chunked_is_blue res.major_final obj) /\
          ~(MarkDefs.chunked_is_no_scan res.major_final obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object
                              res.major_final obj) ==>
          (let v = MarkDefs.chunked_get_field res.major_final obj i in
           if MarkDefs.chunked_is_pointer_field res.major_final v then
            let child_raw =
              MarkDefs.chunked_pointer_field_as_obj_addr res.major_final v in
            Seq.mem child_raw (MH.major_objects res.major_final) /\
            ~(SweepDefs.chunked_is_infix res.major_final child_raw)
           else
            True))
    =
    Classical.move_requires_2 one obj i
  in
  Classical.forall_intro_2 one_imp;
  chunked_nonblue_scanned_raw_targets_in_major_intro
    res.major_final
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_nonblue_scanned_raw_targets_in_major_to_bounded
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_nonblue_scanned_raw_targets_in_major mh)
      (ensures
        ChunkedMarkTargetMembership.chunked_nonblue_scanned_raw_targets_in_major
          mh)
  =
  let one (obj: obj_addr) (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          Seq.mem obj (MH.major_objects mh) /\
          ~(SweepDefs.chunked_is_blue mh obj) /\
          ~(MarkDefs.chunked_is_no_scan mh obj) /\
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh obj))
        (ensures
          (let v = MarkDefs.chunked_get_field mh obj i in
           if MarkDefs.chunked_is_pointer_field mh v then
             let child_raw =
               MarkDefs.chunked_pointer_field_as_obj_addr mh v in
             Seq.mem child_raw (MH.major_objects mh) /\
             ~(SweepDefs.chunked_is_infix mh child_raw)
           else
             True))
    =
    MH.major_objects_member_header_read_some mh obj;
    let hdr = Some?.v (MH.read_word_in_major mh (hd_address obj)) in
    assert (MH.read_word_in_major mh (hd_address obj) == Some hdr);
    GenInv.chunked_is_blue_header mh obj hdr;
    SweepDefs.chunked_read_header_step mh obj;
    assert (SweepDefs.chunked_read_header mh obj == Some hdr);
    SweepDefs.chunked_is_blue_header mh obj hdr;
    assert (GenInv.chunked_is_blue mh obj ==
            SweepDefs.chunked_is_blue mh obj);
    assert (~(GenInv.chunked_is_blue mh obj));
    chunked_nonblue_scanned_raw_targets_in_major_elim mh obj i
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one);
  ChunkedMarkTargetMembership.chunked_nonblue_scanned_raw_targets_in_major_intro
    mh
#pop-options
