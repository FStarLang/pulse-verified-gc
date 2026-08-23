module GC.Impl.MarkBoundedPrecondition

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecMark = GC.Spec.Mark
module SpecObject = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecSweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module SpecMarkBounded = GC.Spec.MarkBounded
module MB = GC.Impl.MarkBounded
module RL = GC.Impl.MarkBoundedRootLemmas
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module HeapModel = GC.Spec.HeapModel
module MajorGC = GC.Impl
module SpecHeap = GC.Spec.Heap

open GC.Spec.Base

let root_valid_for_darkening_points_to_object g r
  = SpecHeap.hd_address_spec (r <: obj_addr);
    SpecHeap.f_hd_roundtrip (r <: obj_addr)

/// ---------------------------------------------------------------------------
/// Lifting the single-root lemmas over the prefix recursion
/// ---------------------------------------------------------------------------

let rec prefix_preserves_not_blue
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat) (x: obj_addr)
  : Lemma
      (requires ~(SpecObject.is_blue x g))
      (ensures
        ~(SpecObject.is_blue x
            (fst (MB.darken_roots_bounded_prefix_spec g st roots idx cap))))
      (decreases idx)
  = if idx = 0 then ()
    else begin
      prefix_preserves_not_blue g st roots (idx - 1) cap x;
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
      RL.check_and_darken_bounded_spec_preserves_not_blue
        g0 st0 (Seq.index roots (idx - 1)) cap x
    end

let rec prefix_preserves_not_black
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat) (x: obj_addr)
  : Lemma
      (requires ~(SpecObject.is_black x g))
      (ensures
        ~(SpecObject.is_black x
            (fst (MB.darken_roots_bounded_prefix_spec g st roots idx cap))))
      (decreases idx)
  = if idx = 0 then ()
    else begin
      prefix_preserves_not_black g st roots (idx - 1) cap x;
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
      RL.check_and_darken_bounded_spec_preserves_not_black
        g0 st0 (Seq.index roots (idx - 1)) cap x
    end

let rec prefix_preserves_stack_mem
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat) (x: obj_addr)
  : Lemma
      (requires Seq.mem x st)
      (ensures
        Seq.mem x (snd (MB.darken_roots_bounded_prefix_spec g st roots idx cap)))
      (decreases idx)
  = if idx = 0 then ()
    else begin
      prefix_preserves_stack_mem g st roots (idx - 1) cap x;
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
      RL.check_and_darken_bounded_spec_preserves_stack_mem
        g0 st0 (Seq.index roots (idx - 1)) cap x
    end

/// Darkening only ever pushes elements of `roots`, so the stack stays a subset.
let rec prefix_preserves_stack_roots
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (requires forall (x: obj_addr). Seq.mem x st ==> Seq.mem (x <: U64.t) roots)
      (ensures
        (forall (x: obj_addr).
          Seq.mem x (snd (MB.darken_roots_bounded_prefix_spec g st roots idx cap)) ==>
          Seq.mem (x <: U64.t) roots))
      (decreases idx)
  = if idx = 0 then ()
    else begin
      prefix_preserves_stack_roots g st roots (idx - 1) cap;
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
      Seq.contains_intro roots (idx - 1) (Seq.index roots (idx - 1));
      RL.check_and_darken_bounded_spec_preserves_stack_roots
        g0 st0 roots (Seq.index roots (idx - 1)) cap
    end

/// The root-set facts of `darken_precondition` transported to the state
/// reached after darkening the first `idx` roots.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let prefix_root_facts
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat) (i: nat{i < Seq.length roots})
  : Lemma
      (requires
        MarkBoundedInv.bounded_mark_inv g st cap /\
        SpecMark.no_black_objects g /\
        (forall (j: nat). j < Seq.length roots ==>
           root_valid_for_darkening g (Seq.index roots j)))
      (ensures
        (let g0 = fst (MB.darken_roots_bounded_prefix_spec g st roots idx cap) in
         let r = Seq.index roots i in
         MB.root_points_to_object g0 r /\
         ~(SpecObject.is_black (r <: obj_addr) g0) /\
         ~(SpecObject.is_blue (r <: obj_addr) g0)))
  = let r = Seq.index roots i in
    root_valid_for_darkening_points_to_object g r;
    MB.darken_roots_bounded_prefix_preserves_objects g st roots idx cap;
    prefix_preserves_not_blue g st roots idx cap (r <: obj_addr);
    // `no_black_objects` plus membership in `objects` gives the pre-state fact.
    assert (Seq.mem (r <: obj_addr) (SpecFields.objects zero_addr g));
    prefix_preserves_not_black g st roots idx cap (r <: obj_addr)
#pop-options

/// Shared hypotheses of the two darkening step lemmas below.
let pushes_roots_pre
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (cap: nat) : prop =
  MarkBoundedInv.bounded_mark_inv g st cap /\
  SpecMark.no_black_objects g /\
  SpecMark.gray_objects_on_stack g st /\
  Seq.length st + Seq.length roots <= cap /\
  (forall (j: nat). j < Seq.length roots ==>
     root_valid_for_darkening g (Seq.index roots j))

/// One darkening step puts its own root on the stack.  Proved on its own so
/// that the recursion below never has to carry these hypotheses into Z3.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let prefix_step_pushes_last
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{0 < idx /\ idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (requires pushes_roots_pre g st roots cap)
      (ensures
        (let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
         let v = Seq.index roots (idx - 1) in
         Seq.mem (v <: obj_addr) (snd (MB.check_and_darken_bounded_spec g0 st0 v cap))))
  = let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
    let v = Seq.index roots (idx - 1) in
    // `st0` cannot have outgrown the capacity: it started at `Seq.length st`
    // and gained at most one element per darkened root.
    RL.darken_roots_bounded_prefix_length_increases_at_most g st roots (idx - 1) cap;
    RL.darken_roots_bounded_prefix_preserves_gray_objects_on_stack g st roots (idx - 1) cap;
    prefix_root_facts g st roots (idx - 1) cap (idx - 1);
    RL.check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root g0 st0 v cap
#pop-options

/// Roots pushed by earlier steps are still on the stack after one more step.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let prefix_step_keeps_earlier
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{0 < idx /\ idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (requires
        pushes_roots_pre g st roots cap /\
        (forall (i: nat). i < idx - 1 ==>
           Seq.mem ((Seq.index roots i) <: obj_addr)
                   (snd (MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap))))
      (ensures
        (let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
         let v = Seq.index roots (idx - 1) in
         forall (i: nat). i < idx - 1 ==>
           Seq.mem ((Seq.index roots i) <: obj_addr)
                   (snd (MB.check_and_darken_bounded_spec g0 st0 v cap))))
  = let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st roots (idx - 1) cap in
    let v = Seq.index roots (idx - 1) in
    introduce forall (i: nat). i < idx - 1 ==>
      Seq.mem ((Seq.index roots i) <: obj_addr)
              (snd (MB.check_and_darken_bounded_spec g0 st0 v cap))
    with introduce _ ==> _
    with RL.check_and_darken_bounded_spec_preserves_stack_mem
           g0 st0 v cap ((Seq.index roots i) <: obj_addr)
#pop-options

/// Every root darkened so far is on the stack.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec prefix_pushes_roots
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (requires pushes_roots_pre g st roots cap)
      (ensures
        (forall (i: nat). i < idx ==>
           Seq.mem ((Seq.index roots i) <: obj_addr)
                   (snd (MB.darken_roots_bounded_prefix_spec g st roots idx cap))))
      (decreases idx)
  = if idx = 0 then ()
    else begin
      prefix_pushes_roots g st roots (idx - 1) cap;
      prefix_step_pushes_last g st roots idx cap;
      prefix_step_keeps_earlier g st roots idx cap
    end
#pop-options

/// ---------------------------------------------------------------------------
/// `stack_no_dups` is exactly `is_vertex_set` on the coerced list
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec stack_no_dups_is_vertex_set (st: Seq.seq obj_addr)
  : Lemma
      (requires SpecMark.stack_no_dups st)
      (ensures Graph.is_vertex_set (HeapGraph.coerce_to_vertex_list st))
      (decreases Seq.length st)
  = if Seq.length st = 0 then ()
    else begin
      stack_no_dups_is_vertex_set (Seq.tail st);
      HeapGraph.coerce_mem_lemma (Seq.tail st) (Seq.head st);
      Graph.is_vertex_set_cons (Seq.head st) (HeapGraph.coerce_to_vertex_list (Seq.tail st));
      assert (Seq.equal (HeapGraph.coerce_to_vertex_list st)
                        (Seq.cons (Seq.head st) (HeapGraph.coerce_to_vertex_list (Seq.tail st))))
    end
#pop-options

/// `bounded_stack_props` is `root_props` in structural clothing: the recursive
/// `stack_elements_valid` gives membership, `stack_points_to_gray` the colour.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let bsp_root_props (g: heap) (st: Seq.seq obj_addr)
  : Lemma
      (requires SpecMarkBounded.bounded_stack_props g st)
      (ensures SpecMark.root_props g st)
  = introduce forall (r: obj_addr). Seq.mem r st ==>
      (Seq.mem r (SpecFields.objects zero_addr g) /\
       (SpecObject.is_gray r g \/ SpecObject.is_black r g))
    with introduce _ ==> _
    with SpecMark.sev_mem_objects g st r
#pop-options

/// ---------------------------------------------------------------------------
/// Main results
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let darken_roots_match_stack g st roots fp cap
  = let n = Seq.length roots in
    prefix_pushes_roots g st roots n cap;
    prefix_preserves_stack_roots g st roots n cap;
    let st' = snd (MB.darken_roots_bounded_spec g st roots cap) in
    introduce forall (r: U64.t). Seq.mem r roots ==> is_val_addr r
    with introduce _ ==> _
    with Seq.mem_index r roots;
    introduce forall (r: obj_addr). Seq.mem (r <: U64.t) roots ==> Seq.mem r st'
    with introduce _ ==> _
    with (
      // `Seq.mem` gives an index, and every indexed root is pushed.
      Seq.mem_index (r <: U64.t) roots;
      eliminate exists (i: nat{i < n}). Seq.index roots i == (r <: U64.t)
      with ()
    )
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let darken_establishes_precondition g st roots fp cap
  = let n = Seq.length roots in
    let g' = fst (MB.darken_roots_bounded_spec g st roots cap) in
    let st' = snd (MB.darken_roots_bounded_spec g st roots cap) in
    MarkBoundedInv.bounded_mark_inv_elim_wfh g st cap;
    introduce forall (i: nat). i < Seq.length roots ==>
      MB.root_points_to_object g (Seq.index roots i)
    with introduce _ ==> _
    with root_valid_for_darkening_points_to_object g (Seq.index roots i);
    // 1. bounded_mark_inv (which also supplies well_formed_heap g')
    MB.darken_roots_bounded_spec_preserves_bounded_mark_inv g st roots cap;
    MarkBoundedInv.bounded_mark_inv_elim_wfh g' st' cap;
    MarkBoundedInv.bounded_mark_inv_elim_bsp g' st' cap;
    bsp_root_props g' st';
    // 2, 4. free-list facts survive because `objects` is unchanged
    MB.darken_roots_bounded_spec_preserves_fp_valid g st roots cap fp;
    MB.darken_roots_bounded_spec_preserves_fp_in_heap g st roots cap fp;
    // 5, 6, 7. colour and shape invariants
    MB.darken_roots_bounded_spec_preserves_no_black g st roots cap;
    MB.darken_roots_bounded_spec_preserves_no_pointer_to_blue g st roots cap;
    MB.darken_roots_bounded_spec_preserves_no_scan_invariant g st roots cap;
    // 8. every gray-or-black object is on the stack: there are no black objects,
    //    and darkening keeps all gray objects on the stack.
    RL.darken_roots_bounded_spec_preserves_gray_objects_on_stack g st roots cap;
    // 9. graph facts
    SpecMark.create_graph_wf_from_heap g';
    stack_no_dups_is_vertex_set st';
    SpecMark.root_props_subset_create_graph g' st'
#pop-options
