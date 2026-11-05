/// ---------------------------------------------------------------------------
/// GC.SPOT.CycleHeap - a concrete heap for the incremental cycle's theorems
/// ---------------------------------------------------------------------------
///
/// The four-object heap of `GC.SPOT.MarkPhaseHeap`, all white, then one free
/// block running to the end of the heap, with an empty nursery:
///
///     A (1) -> B (2)      B (2): no pointer      U (3) -> A      C (4): no pointer
///
/// The roots are `[A; C]`, so `A`, `B` and `C` are reachable and `U` is not
/// (`u_unreachable`): nothing points at `U`, though `U` points at a reachable
/// object.
///
/// This module proves what the run (`GC.SPOT.IncrementalCycleTheorems`)
/// needs: the heap is in the idle collector's state
/// (`collection_heap_shape`, as `GC.SPOT.InfixMajor` does for its heap), the
/// minor collection's precondition holds with no remembered slot, the minor
/// collection of the empty nursery changes nothing (`collect_empty`), and
/// the reachability facts.

module GC.SPOT.CycleHeap

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Phase

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module MPH = GC.SPOT.MarkPhaseHeap
module InfixPre = GC.SPOT.InfixPre
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module SweepInv = GC.Spec.SweepInv
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
module FreeListShape = GC.Gen.FreeListShape
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Mark = GC.Spec.Mark
module CheneySpec = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module RBridge = GC.Gen.ReachabilityBridge
module MinorFwd = GC.Gen.MinorCollectForwarding
module RT = GC.Gen.RefTable
module MP = GC.Spec.MarkPhase
module MPC = GC.Spec.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor
module MBP = GC.Impl.MarkBoundedPrecondition
module FA = GC.Gen.ForwardingArray

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The heap
/// ---------------------------------------------------------------------------

let col0 (i: MPH.idx) : MPH.ccol = Header.White

let tg0 (i: MPH.idx) : MPH.tgt = if i = 1 then 2 else if i = 3 then 1 else 0

let h0 (r: unit{MPH.room}) : heap = MPH.heap4 r col0 tg0

let fp0 (r: unit{MPH.room}) : U64.t = MPH.free_obj r

let obj_a (r: unit{MPH.room}) : obj_addr = MPH.obj r 1
let obj_b (r: unit{MPH.room}) : obj_addr = MPH.obj r 2
let obj_u (r: unit{MPH.room}) : obj_addr = MPH.obj r 3
let obj_c (r: unit{MPH.room}) : obj_addr = MPH.obj r 4

/// The roots: `A` and `C`.
let roots0 (r: unit{MPH.room}) : seq U64.t =
  Seq.cons (obj_a r <: U64.t) (Seq.cons (obj_c r <: U64.t) Seq.empty)

/// The empty nursery.
let minor0 : minor_state = InfixPre.spot_infix_minor

/// The objects are distinct, and their facts.
let layout (r: unit{MPH.room})
  : Lemma (U64.v (obj_a r) == U64.v zero_addr + 8 /\ U64.v (obj_b r) == U64.v zero_addr + 24 /\
           U64.v (obj_u r) == U64.v zero_addr + 40 /\ U64.v (obj_c r) == U64.v zero_addr + 56 /\
           U64.v (MPH.free_obj r) == U64.v zero_addr + 72)
  = ()

let facts (r: unit{MPH.room})
  : Lemma (let h = h0 r in
           (forall (i: MPH.idx). let o = MPH.obj r i in
              Seq.mem o (objects zero_addr h) /\ is_white o h /\ ~(is_blue o h) /\
              ~(is_black o h) /\ ~(is_gray o h) /\
              wosize_of_object o h == 1UL /\ ~(is_no_scan o h) /\ ~(is_infix o h) /\
              ~(is_closure o h) /\ resolve_object o h == o /\
              read_word h o == MPH.fv r (tg0 i)) /\
           Seq.mem (MPH.free_obj r) (objects zero_addr h) /\ is_blue (MPH.free_obj r) h /\
           ~(is_black (MPH.free_obj r) h) /\ ~(is_gray (MPH.free_obj r) h) /\
           ~(is_white (MPH.free_obj r) h))
  = let f (i: MPH.idx)
      : Lemma (let h = h0 r in let o = MPH.obj r i in
               Seq.mem o (objects zero_addr h) /\ is_white o h /\ ~(is_blue o h) /\
               ~(is_black o h) /\ ~(is_gray o h) /\
               wosize_of_object o h == 1UL /\ ~(is_no_scan o h) /\ ~(is_infix o h) /\
               ~(is_closure o h) /\ resolve_object o h == o /\
               read_word h o == MPH.fv r (tg0 i))
      = MPH.obj_facts r col0 tg0 i;
        Mark.colors_exclusive (MPH.obj r i) (h0 r)
    in
    FStar.Classical.forall_intro f;
    MPH.free_facts r col0 tg0

/// Every block is one of the five.
let cases (r: unit{MPH.room}) (x: obj_addr)
  : Lemma (Seq.mem x (objects zero_addr (h0 r)) <==>
           (x == obj_a r \/ x == obj_b r \/ x == obj_u r \/ x == obj_c r \/ x == MPH.free_obj r))
  = MPH.object_cases r col0 tg0 x

/// ---------------------------------------------------------------------------
/// The shape
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 0"
let fl_valid (r: unit{MPH.room})
  : Lemma (AllocLemmas.fl_valid (h0 r) (fp0 r) heap_words)
  = let g = h0 r in
    let fp = fp0 r in
    let fuel = heap_words in
    MPH.free_block r col0 tg0;
    facts r;
    hd_address_spec (MPH.free_obj r);
    assert (fuel > 1);
    AllocLemmas.fl_valid_null g (fuel - 1);
    AllocLemmas.fl_valid_step g fp fuel

let fl_chain_terminates (r: unit{MPH.room})
  : Lemma (AllocLemmas.fl_chain_terminates (h0 r) (fp0 r) heap_words)
  = let g = h0 r in
    let fp = fp0 r in
    let fuel = heap_words in
    MPH.free_block r col0 tg0;
    hd_address_spec (MPH.free_obj r);
    assert (fuel > 1);
    AllocLemmas.fl_chain_terminates_terminal g 0UL (fuel - 1);
    AllocLemmas.fl_chain_terminates_step g fp fuel
#pop-options

let fp_pointer_or_zero (r: unit{MPH.room})
  : Lemma (FreeListShape.fp_pointer_or_zero (fp0 r))
  = zero_addr_above_2048 ();
    assert (HeapGraph.is_pointer_field (fp0 r))

let blue_link_fields_valid (r: unit{MPH.room})
  : Lemma (FreeListShape.blue_link_fields_valid (h0 r))
  = let g = h0 r in
    let proof (src: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr g) /\ is_blue src g /\
                        U64.v (wosize_of_object src g) >= 1 /\
                        U64.v (hd_address src) + 16 <= heap_size)
              (ensures (let v = read_word g src in v = 0UL \/ HeapGraph.is_pointer_field v))
      = cases r src; facts r; MPH.free_block r col0 tg0
    in
    FreeListShape.blue_link_fields_valid_intro g proof

let fp_valid (r: unit{MPH.room})
  : Lemma (SweepInv.fp_valid (fp0 r) (h0 r) /\ GC.Spec.FreeList.fp_in_heap (fp0 r) (h0 r))
  = fp_pointer_or_zero r;
    fl_valid r;
    FreeListShape.fp_pointer_or_zero_fl_valid_implies_fp_valid (fp0 r) (h0 r) heap_words;
    FreeListShape.fp_pointer_or_zero_implies_fp_in_heap (fp0 r) (h0 r)

let heap_objects_dense_intro_by_proof (g: heap)
  (proof: (start: hp_addr{U64.v start + 8 < heap_size} -> Lemma
    (ensures
      Seq.mem (f_address start) (objects zero_addr g) ==>
      Seq.length (objects start g) > 0 ==>
      (let wz = getWosize (read_word g start) in
       let next = U64.v start + ((U64.v wz + 1) * 8) in
       next + 8 < heap_size ==>
       Seq.length (objects (U64.uint_to_t next) g) > 0 /\
       Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g)))))
  : Lemma (ensures heap_objects_dense g)
  = let aux (start: hp_addr)
      : Lemma (ensures
                U64.v start + 8 < heap_size ==>
                Seq.mem (f_address start) (objects zero_addr g) ==>
                Seq.length (objects start g) > 0 ==>
                (let wz = getWosize (read_word g start) in
                 let next = U64.v start + ((U64.v wz + 1) * 8) in
                 next + 8 < heap_size ==>
                 Seq.length (objects (U64.uint_to_t next) g) > 0 /\
                 Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g)))
      = if U64.v start + 8 < heap_size then proof start
    in
    FStar.Classical.forall_intro aux;
    reveal_opaque (`%heap_objects_dense) heap_objects_dense

/// The block at header position `k` (even, at most 8) is followed by the one
/// at `k + 2`, a block of the walk (or the end of the heap after the free
/// block).
#push-options "--z3rlimit 20"
let dense_at (r: unit{MPH.room}) (k: nat{k <= 8 /\ k % 2 == 0})
  : Lemma (let g = h0 r in
           let start = MPH.at r k in
           Seq.length (objects start g) > 0 /\
           (let wz = getWosize (read_word g start) in
            let next = U64.v start + ((U64.v wz + 1) * 8) in
            next + 8 < heap_size ==>
            Seq.length (objects (U64.uint_to_t next) g) > 0 /\
            Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g)))
  = MPH.objects_from r col0 tg0 k;
    if k < 8 then begin
      MPH.objects_from r col0 tg0 (k + 2);
      assert (U64.uint_to_t (U64.v (MPH.at r (k + 2))) == MPH.at r (k + 2));
      cases r (MPH.at r (k + 3))
    end
#pop-options

#push-options "--z3rlimit 20"
let dense (r: unit{MPH.room})
  : Lemma (heap_objects_dense (h0 r))
  = let g = h0 r in
    let proof (start: hp_addr{U64.v start + 8 < heap_size})
      : Lemma (ensures
                Seq.mem (f_address start) (objects zero_addr g) ==>
                Seq.length (objects start g) > 0 ==>
                (let wz = getWosize (read_word g start) in
                 let next = U64.v start + ((U64.v wz + 1) * 8) in
                 next + 8 < heap_size ==>
                 Seq.length (objects (U64.uint_to_t next) g) > 0 /\
                 Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g)))
      = if Seq.mem (f_address start) (objects zero_addr g) then begin
          cases r (f_address start);
          f_address_spec start;
          layout r;
          if U64.v start = U64.v zero_addr then dense_at r 0
          else if U64.v start = U64.v zero_addr + 16 then dense_at r 2
          else if U64.v start = U64.v zero_addr + 32 then dense_at r 4
          else if U64.v start = U64.v zero_addr + 48 then dense_at r 6
          else dense_at r 8
        end
    in
    heap_objects_dense_intro_by_proof g proof
#pop-options

#push-options "--fuel 1 --ifuel 0"
let chain_avoids (r: unit{MPH.room}) (obj: obj_addr)
  : Lemma (requires obj <> MPH.free_obj r)
          (ensures AllocLemmas.chain_avoids (h0 r) (fp0 r) obj heap_words = true)
  = let g = h0 r in
    let fp = fp0 r in
    let fuel = heap_words in
    MPH.free_block r col0 tg0;
    assert (fuel > 0);
    hd_address_spec (MPH.free_obj r);
    AllocChain.chain_avoids_null g obj (fuel - 1);
    AllocChain.chain_avoids_unfold_step g fp obj fuel
#pop-options

let chain_objects_blue (r: unit{MPH.room})
  : Lemma (Promote.chain_objects_blue (h0 r) (fp0 r))
  = let g = h0 r in
    let proof (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g))
              (ensures AllocLemmas.chain_avoids g (fp0 r) obj heap_words = true)
      = cases r obj; facts r; chain_avoids r obj
    in
    reveal_opaque (`%Promote.chain_objects_blue) Promote.chain_objects_blue;
    FStar.Classical.forall_intro (FStar.Classical.move_requires proof)

let colours (r: unit{MPH.room})
  : Lemma (Mark.no_black_objects (h0 r) /\ SweepInv.no_gray_objects (h0 r))
  = let g = h0 r in
    let proof (obj: obj_addr)
      : Lemma (Seq.mem obj (objects zero_addr g) ==> ~(is_black obj g) /\ ~(is_gray obj g))
      = if Seq.mem obj (objects zero_addr g) then begin cases r obj; facts r end
    in
    FStar.Classical.forall_intro proof;
    SweepInv.no_gray_intro g

#push-options "--fuel 1 --ifuel 0"
let fl_complete (r: unit{MPH.room})
  : Lemma (FL.fl_complete (h0 r) (fp0 r))
  = let g = h0 r in
    let proof (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr g) /\ is_blue obj g /\
                        U64.v (wosize_of_object obj g) >= 1)
              (ensures FL.reachable_on_fl g (fp0 r) obj)
      = cases r obj; facts r; MPH.free_block r col0 tg0;
        hd_address_spec (MPH.free_obj r);
        FL.reachable_head g (fp0 r)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires proof)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let fl_ascending (r: unit{MPH.room})
  : Lemma (FLA.fl_ascending (h0 r) (fp0 r))
  = let g = h0 r in
    let only (x: U64.t)
      : Lemma (requires FL.fl_cell g x) (ensures x == fp0 r)
      = cases r x; facts r
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only);
    MPH.free_block r col0 tg0; facts r;
    hd_address_spec (MPH.free_obj r);
    fl_valid r;
    AllocLemmas.fl_valid_gives_mem g (fp0 r) heap_words;
    FLA.fl_ascending_single g (fp0 r)
#pop-options

let major_heap_shape (r: unit{MPH.room})
  : Lemma (GenInv.major_heap_shape (h0 r) (fp0 r))
  = let g = h0 r in
    let fp = fp0 r in
    facts r;
    MPH.objects_from r col0 tg0 0;
    assert (MPH.at r 0 == zero_addr);
    MPH.wf r col0 tg0;
    fl_valid r;
    fl_chain_terminates r;
    fp_pointer_or_zero r;
    blue_link_fields_valid r;
    dense r;
    chain_objects_blue r;
    fp_valid r;
    colours r;
    fl_complete r;
    fl_ascending r;
    GC.Gen.AllocExact.fl_valid_cob_gives_sound g fp;
    GenInv.free_list_exact_iff g fp;
    GenInv.major_heap_shape_intro g fp

/// **The idle collector's state.**
let shape (r: unit{MPH.room})
  : Lemma (GenInv.collection_heap_shape minor0 (h0 r) (fp0 r))
  = major_heap_shape r;
    let ms0 = minor_init (Seq.create minor_heap_size 0uy) in
    GenInv.collection_heap_shape_after_minor_reset ms0 (h0 r) (fp0 r);
    InfixPre.spot_infix_minor_is_reset ms0

/// ---------------------------------------------------------------------------
/// The roots
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let roots_facts (r: unit{MPH.room})
  : Lemma (Seq.length (roots0 r) == 2 /\
           Seq.index (roots0 r) 0 == (obj_a r <: U64.t) /\ Seq.index (roots0 r) 1 == (obj_c r <: U64.t) /\
           (forall (q: U64.t). Seq.mem q (roots0 r) <==> q == (obj_a r <: U64.t) \/ q == (obj_c r <: U64.t)))
  = let tl = Seq.cons (obj_c r <: U64.t) Seq.empty in
    let mm (q: U64.t)
      : Lemma (Seq.mem q (roots0 r) <==> q == (obj_a r <: U64.t) \/ q == (obj_c r <: U64.t))
      = FStar.Seq.Properties.mem_cons (obj_a r <: U64.t) tl;
        FStar.Seq.Properties.mem_cons (obj_c r <: U64.t) (Seq.empty #U64.t);
        assert_norm (~(Seq.mem q (Seq.empty #U64.t)))
    in
    FStar.Classical.forall_intro mm;
    FStar.Seq.Properties.head_cons (obj_a r <: U64.t) tl;
    FStar.Seq.Properties.lemma_tl (obj_a r <: U64.t) tl;
    FStar.Seq.Properties.head_cons (obj_c r <: U64.t) (Seq.empty #U64.t)
#pop-options

/// The roots are the objects `A` and `C`: major blocks, white, not free.
let roots_valid_darkening (r: unit{MPH.room})
  : Lemma (forall (i: nat). i < Seq.length (roots0 r) ==> MBP.root_valid_for_darkening (h0 r) (Seq.index (roots0 r) i))
  = roots_facts r; facts r; layout r

/// What the roots hold (resolved): `A` and `C`.
let roots_held_iff (r: unit{MPH.room}) (w: obj_addr)
  : Lemma (GMM.roots_held (h0 r) (roots0 r) w <==> w == obj_a r \/ w == obj_c r)
  = roots_facts r; facts r; layout r; zero_addr_above_2048 ();
    if w = obj_a r then assert (Seq.mem (obj_a r <: U64.t) (roots0 r))
    else if w = obj_c r then assert (Seq.mem (obj_c r <: U64.t) (roots0 r))

/// ---------------------------------------------------------------------------
/// The minor collection's precondition, with no remembered slot
/// ---------------------------------------------------------------------------

let slots0 : seq U64.t = Seq.empty

#push-options "--z3rlimit 20"
let minor_pre (r: unit{MPH.room}) (farr sl: seq U64.t)
  : Lemma (requires Seq.length farr == FA.fwd_array_size /\
                    (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL))
          (ensures GC.Gen.Impl.minor_collect_pre_idle minor0 (h0 r) (fp0 r) (roots0 r) farr sl 0)
  = let g = h0 r in
    shape r;
    assert_norm (Seq.length (Seq.empty #U64.t) == 0);
    // no field holds a nursery pointer
    let cov (obj: obj_addr) (j: nat)
      : Lemma ((Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false /\
                is_no_scan obj g = false /\ j < U64.v (wosize_of_object obj g) /\
                U64.v obj + j * 8 + 8 <= heap_size) ==>
               ~(Promote.is_minor_pointer (to_minor_offset (read_word g (U64.uint_to_t (U64.v obj + j * 8))))))
      = if Seq.mem obj (objects zero_addr g) && not (is_blue obj g) && not (is_no_scan obj g) &&
           j < U64.v (wosize_of_object obj g) && U64.v obj + j * 8 + 8 <= heap_size
        then begin
          cases r obj; facts r; layout r;
          assert (j == 0);
          assert (U64.uint_to_t (U64.v obj + j * 8) == obj);
          zero_addr_above_minor ();
          zero_addr_above_2048 ();
          let v = read_word g obj in
          if v = 0UL then assert_norm (Promote.is_minor_pointer 0UL == false)
          else begin
            assert (U64.v v >= minor_heap_size);
            to_minor_offset_stable_above_minor v
          end
        end
    in
    FStar.Classical.forall_intro_2 cov;
    GC.Gen.MinorCollectForwarding.Helpers.remembered_targets_in_roots_intro_by_slots g (roots0 r) sl 0;
    let rv (q: U64.t)
      : Lemma (requires Seq.mem q (roots0 r))
              (ensures (Promote.is_minor_pointer q ==>
                          Seq.mem (resolve_minor minor0 q) (minor_objects minor0) /\
                          minor_wosize minor0 (resolve_minor minor0 q) > 0) /\
                       (~(Promote.is_minor_pointer q) ==>
                          is_val_addr q /\ Seq.mem (q <: obj_addr) (objects zero_addr g) /\
                          ~(is_blue (q <: obj_addr) g)))
      = roots_facts r; facts r; layout r;
        if q = (obj_a r <: U64.t) then RBridge.major_object_not_minor_pointer g (obj_a r)
        else RBridge.major_object_not_minor_pointer g (obj_c r)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires rv)
#pop-options

/// ---------------------------------------------------------------------------
/// The collection of the empty nursery changes nothing
/// ---------------------------------------------------------------------------

let reset_facts (addr: U64.t)
  : Lemma (~(Seq.mem addr (minor_objects minor0)) /\ ~(is_infix_in_minor minor0 addr))
  = let ms0 = minor_init (Seq.create minor_heap_size 0uy) in
    InfixPre.spot_infix_minor_is_reset ms0;
    minor_reset_objects_not_mem ms0 addr;
    minor_reset_no_infix ms0 addr

let rec forward_roots_noop (cs: CheneySpec.cheney_state) (rs: seq U64.t) (idx: nat)
  : Lemma (ensures CheneySpec.cheney_forward_roots minor0 cs rs idx == cs)
          (decreases (Seq.length rs - idx))
  = if idx >= Seq.length rs then CheneySpec.cheney_forward_roots_base minor0 cs rs idx
    else begin
      CheneySpec.cheney_forward_roots_step minor0 cs rs idx;
      reset_facts (Seq.index rs idx);
      CheneySpec.cheney_forward_one_noop minor0 cs (Seq.index rs idx);
      forward_roots_noop cs rs (idx + 1)
    end

let empty_fwd (x: U64.t) : Lemma (Promote.empty_forwarding x == 0UL) =
  assert_norm (Promote.empty_forwarding x == 0UL)

#push-options "--fuel 1"
let rec update_object_noop (major: heap) (obj: U64.t) (wz: nat) (i: nat)
  : Lemma (ensures Promote.update_object_pointers major obj wz Promote.empty_forwarding i == major)
          (decreases (wz - i))
  = if i >= wz then ()
    else begin
      let fo = U64.v obj + i * 8 in
      if fo + 8 > heap_size || fo % 8 <> 0 then ()
      else begin
        empty_fwd (to_minor_offset (read_word major (U64.uint_to_t fo)));
        update_object_noop major obj wz (i + 1)
      end
    end

let rec update_walk_noop (major: heap) (objs: seq obj_addr) (upd: obj_addr -> GTot bool) (idx: nat)
  : Lemma (ensures Promote.update_walk_aux major objs upd Promote.empty_forwarding idx == major)
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      (if upd obj && not (is_no_scan obj major) then
         update_object_noop major obj (U64.v (wosize_of_object obj major)) 0);
      update_walk_noop major objs upd (idx + 1)
    end

let rec rewrite_noop (rs: seq U64.t)
  : Lemma (ensures Promote.rewrite_roots rs Promote.empty_forwarding == rs)
          (decreases (Seq.length rs))
  = if Seq.length rs = 0 then assert (Seq.equal (Seq.empty #U64.t) rs)
    else begin
      let tl = Seq.slice rs 1 (Seq.length rs) in
      rewrite_noop tl;
      empty_fwd (Seq.index rs 0);
      FStar.Seq.Properties.cons_head_tail rs
    end
#pop-options

/// **The collection of the empty nursery changes nothing**: the heap, the
/// free-list head and the roots are as they were.
#push-options "--z3rlimit 20"
let collect_empty (g: heap) (fp: U64.t) (rs: seq U64.t)
  : Lemma (let prom = CheneySpec.cheney_promote Idle minor0 g fp rs in
           let res = CheneySpec.cheney_collect_spec minor0 g fp rs in
           res.Promote.mc_major == g /\ prom.Promote.fp_final == fp /\
           Promote.rewrite_roots rs prom.Promote.fwd_map == rs)
  = let cs0 : CheneySpec.cheney_state =
      { CheneySpec.cs_major = g; CheneySpec.cs_fp = fp;
        CheneySpec.cs_fwd = Promote.empty_forwarding; CheneySpec.cs_queue = Seq.empty;
        CheneySpec.cs_phase = Idle } in
    forward_roots_noop cs0 rs 0;
    CheneySpec.cheney_fuel_eq minor0;
    InfixPre.spot_infix_minor_objects_empty ();
    assert_norm (Seq.length (Seq.empty #U64.t) == 0);
    CheneySpec.cheney_scan_base minor0 cs0 0 (CheneySpec.cheney_fuel minor0);
    update_walk_noop g (objects zero_addr g) (in_use free_stw g) 0;
    rewrite_noop rs
#pop-options

/// No promotion can fail: there is nothing to promote.
#push-options "--ifuel 1"
let no_oom (r: unit{MPH.room})
  : Lemma (~(CheneyBFS.cheney_oom Idle minor0 (h0 r) (fp0 r) (roots0 r)))
  = let ms0 = minor_init (Seq.create minor_heap_size 0uy) in
    InfixPre.spot_infix_minor_is_reset ms0;
    minor_reset_objects_empty ms0;
    assert_norm (Seq.length (Seq.empty #U64.t) == 0);
    let no_fail (cs: CheneySpec.cheney_state) (addr: U64.t)
      : Lemma (ensures ~(CheneyBFS.promote_fails_for minor0 cs addr))
      = minor_reset_objects_not_mem ms0 addr;
        minor_reset_no_infix ms0 addr
    in
    FStar.Classical.forall_intro_2 no_fail;
    reveal_opaque (`%CheneyBFS.cheney_oom_reaching) CheneyBFS.cheney_oom_reaching
#pop-options

/// ---------------------------------------------------------------------------
/// Reachable when the cycle starts
/// ---------------------------------------------------------------------------

/// The roots' objects `A` and `C` are reachable ...
let roots_reachable (r: unit{MPH.room})
  : Lemma (MPC.reachable (h0 r) (GMM.roots_held (h0 r) (roots0 r)) (obj_a r) /\
           MPC.reachable (h0 r) (GMM.roots_held (h0 r) (roots0 r)) (obj_c r))
  = roots_held_iff r (obj_a r);
    roots_held_iff r (obj_c r);
    MPC.reachable_held (h0 r) (GMM.roots_held (h0 r) (roots0 r)) (obj_a r);
    MPC.reachable_held (h0 r) (GMM.roots_held (h0 r) (roots0 r)) (obj_c r)

/// ... and `U` is not: `A`, `B` and `C` contain the roots and are closed
/// under the edges.
let u_unreachable (r: unit{MPH.room})
  : Lemma (~(MPC.reachable (h0 r) (GMM.roots_held (h0 r) (roots0 r)) (obj_u r)))
  = let g = h0 r in
    let c (x: obj_addr) : prop = x == obj_a r \/ x == obj_b r \/ x == obj_c r in
    FStar.Classical.forall_intro (roots_held_iff r);
    let closed (u v: obj_addr) : Lemma (requires c u /\ MP.field_edge g u v) (ensures c v) =
      if u = obj_a r then MPH.field_edge_iff r col0 tg0 1 v
      else if u = obj_b r then MPH.field_edge_iff r col0 tg0 2 v
      else MPH.field_edge_iff r col0 tg0 4 v
    in
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (closed u));
    layout r;
    FStar.Classical.move_requires (MPC.reachable_closed g (GMM.roots_held g (roots0 r)) c) (obj_u r)
