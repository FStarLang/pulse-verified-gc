/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Darken - a collection starts by greying its roots
/// ---------------------------------------------------------------------------
///
/// In the allocator's `Idle` invariant every live object is white
/// (`MarkPhase.live_white`).  The mark needs its roots grey and on its stack
/// (`GcCorrect.mark_pre`, from `GC.Spec.Correctness.mark_satisfies_mark_post`).
/// So a collection starts, as OCaml's `caml_darken_all_roots` does, by
/// greying each root (`darken`), with the roots as the mark stack.
///
/// `darken_ok`: from `Idle` and roots that are live objects (`roots_ok`), the
/// darkened heap meets everything the mark needs (`mark_pre`, with the roots
/// as the stack) and the allocator's marking invariant, and it differs from
/// the first heap only in the roots' colours: the same walk, the same graph,
/// the same sizes and fields.  The allocator ignores the colours of live
/// objects, so greying keeps its invariant (`MarkPhase.mark_inv_recolour`).

module GC.Spec.Pages.Darken

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module MP = GC.Spec.Pages.MarkPhase
module GP = GC.Spec.Pages.GcPillars
module CF = GC.Spec.Pages.ColourFacts
module R = GC.Spec.Pages.Replace
module WE = GC.Spec.WalkEnd
module SI = GC.Spec.SweepInv
module Mark = GC.Spec.Mark
module MarkInv = GC.Spec.MarkInv
module Graph = GC.Spec.Graph
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The step
/// ---------------------------------------------------------------------------

/// Grey each root, in order.
#push-options "--fuel 1"
let rec darken (h: heap) (roots: Seq.seq obj_addr) : GTot heap (decreases Seq.length roots) =
  if Seq.length roots = 0 then h
  else darken (makeGray (Seq.head roots) h) (Seq.tail roots)
#pop-options

/// The roots are live objects of the heap, and the graph facts that guard
/// pillar 2 hold (`GP.graph_pre`; with them, the roots are distinct).
let roots_ok (h: heap) (roots: Seq.seq obj_addr) : prop =
  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r (objects zero_addr h) /\ ~(is_blue r h)) /\
  GP.graph_pre h roots

/// What a collection needs: the allocator's `Idle` invariant and live roots.
let start_pre (h: heap) (st: pstate) (roots: Seq.seq obj_addr) : prop =
  PA.inv I.Idle h st /\ roots_ok h roots

/// ---------------------------------------------------------------------------
/// What one recolouring keeps
/// ---------------------------------------------------------------------------

/// What `darken` keeps of `h`, in `h'`: everything but colours.
let same (h h': heap) : prop =
  well_formed_heap h' /\
  objects zero_addr h' == objects zero_addr h /\
  HeapModel.create_graph h' == HeapModel.create_graph h /\
  (forall (y: obj_addr). is_blue y h' <==> is_blue y h) /\
  (forall (x: obj_addr). wosize_of_object x h' == wosize_of_object x h) /\
  (forall (x: obj_addr) (i: U64.t{U64.v i >= 1}).
     Seq.mem x (objects zero_addr h) /\ U64.v i <= U64.v (wosize_of_object x h) ==>
     HeapGraph.get_field h' x i == HeapGraph.get_field h x i)

/// ... and how it sets the colours.
let kept (h h': heap) (roots: Seq.seq obj_addr) : prop =
  same h h' /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr h) ==>
     (Seq.mem x roots ==> is_gray x h') /\
     (~(Seq.mem x roots) ==> color_of_object x h' == color_of_object x h))

/// One recolouring keeps `no_pointer_to_blue`: the fields, how pointers
/// resolve and which blocks are free are unchanged.
let npb_step (h: heap) (r: obj_addr) (c: color)
  : Lemma (requires well_formed_heap h /\ Seq.mem r (objects zero_addr h) /\ ~(is_blue r h) /\ c <> Blue /\
                    Mark.no_pointer_to_blue h)
          (ensures Mark.no_pointer_to_blue (set_object_color r h c))
  = let h' = set_object_color r h c in
    CF.step_facts h r c;
    let one (src dst: obj_addr)
      : Lemma (Seq.mem src (objects zero_addr h') /\ ~(is_blue src h') /\
               fields_constrained h' src /\ points_to h' src dst ==>
               ~(is_blue (resolve_object dst h') h'))
      = if Seq.mem src (objects zero_addr h') then begin
          if src = r then begin
            color_change_preserves_points_to_self h r c dst;
            color_preserves_is_no_scan r h c
          end else begin
            color_change_preserves_points_to_other h r c src dst;
            color_change_preserves_other_is_no_scan r src h c
          end;
          color_change_preserves_resolve r dst h c
        end
    in
    FStar.Classical.forall_intro_2 one

/// One recolouring, grey, of a live object.
let gray_step (h: heap) (r: obj_addr)
  : Lemma (requires well_formed_heap h /\ Seq.mem r (objects zero_addr h) /\ ~(is_blue r h))
          (ensures (let h' = makeGray r h in
                    same h h' /\ is_gray r h' /\
                    (forall (x: obj_addr). x <> r ==> color_of_object x h' == color_of_object x h) /\
                    (Mark.no_pointer_to_blue h ==> Mark.no_pointer_to_blue h') /\
                    (forall (st: pstate). MP.mark_inv h st ==> MP.mark_inv h' st)))
  = let h' = makeGray r h in
    makeGray_eq r h;
    CF.step_facts h r Gray;
    Mark.color_preserves_create_graph r h Gray;
    FStar.Classical.forall_intro (fun x -> color_change_preserves_wosize_any r x h Gray);
    let fld (x: obj_addr) (i: U64.t{U64.v i >= 1})
      : Lemma (Seq.mem x (objects zero_addr h) /\ U64.v i <= U64.v (wosize_of_object x h) ==>
               HeapGraph.get_field h' x i == HeapGraph.get_field h x i)
      = if Seq.mem x (objects zero_addr h) && U64.v i <= U64.v (wosize_of_object x h) then
          Mark.color_preserves_get_field r x h Gray i
    in
    FStar.Classical.forall_intro_2 fld;
    makeGray_is_gray r h;
    let col (x: obj_addr) : Lemma (x <> r ==> color_of_object x h' == color_of_object x h)
      = if x <> r then color_change_preserves_other_color r x h Gray
    in
    FStar.Classical.forall_intro col;
    FStar.Classical.move_requires (npb_step h r) Gray;
    let mi (st: pstate) : Lemma (MP.mark_inv h st ==> MP.mark_inv h' st)
      = FStar.Classical.move_requires (MP.mark_inv_recolour h st r) Gray
    in
    FStar.Classical.forall_intro mi

/// ---------------------------------------------------------------------------
/// All the roots
/// ---------------------------------------------------------------------------

let live_roots (h: heap) (roots: Seq.seq obj_addr) : prop =
  forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r (objects zero_addr h) /\ ~(is_blue r h)

#push-options "--fuel 1 --z3rlimit 40"
let rec darken_kept (h: heap) (roots: Seq.seq obj_addr)
  : Lemma (requires well_formed_heap h /\ live_roots h roots)
          (ensures kept h (darken h roots) roots /\
                   (Mark.no_pointer_to_blue h ==> Mark.no_pointer_to_blue (darken h roots)) /\
                   (forall (st: pstate). MP.mark_inv h st ==> MP.mark_inv (darken h roots) st))
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then begin
      Seq.lemma_empty roots;
      let col (x: obj_addr) : Lemma (~(Seq.mem x roots)) = () in
      FStar.Classical.forall_intro col
    end else begin
      let r = Seq.head roots in
      let tl = Seq.tail roots in
      let h1 = makeGray r h in
      gray_step h r;
      let mem_tl (x: obj_addr) : Lemma (Seq.mem x roots <==> x == r \/ Seq.mem x tl)
        = Seq.cons_head_tail roots;
          Seq.mem_cons r tl
      in
      FStar.Classical.forall_intro mem_tl;
      assert (live_roots h1 tl);
      darken_kept h1 tl;
      let h2 = darken h1 tl in
      assert (h2 == darken h roots);
      let col (x: obj_addr)
        : Lemma (Seq.mem x (objects zero_addr h) ==>
                 (Seq.mem x roots ==> is_gray x h2) /\
                 (~(Seq.mem x roots) ==> color_of_object x h2 == color_of_object x h))
        = if Seq.mem x (objects zero_addr h) then begin
            if x = r && not (Seq.mem x tl) then begin
              is_gray_iff x h1;
              is_gray_iff x h2
            end
          end
      in
      FStar.Classical.forall_intro col
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The stack
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec sev_of_mem (g: heap) (st: Seq.seq obj_addr)
  : Lemma (requires forall (x: obj_addr). Seq.mem x st ==> Seq.mem x (objects zero_addr g))
          (ensures Mark.stack_elements_valid g st)
          (decreases Seq.length st)
  = if Seq.length st = 0 then ()
    else begin
      Seq.cons_head_tail st;
      Seq.mem_cons (Seq.head st) (Seq.tail st);
      sev_of_mem g (Seq.tail st)
    end

let rec no_dups_of_vertex_set (st: Seq.seq obj_addr)
  : Lemma (requires Graph.is_vertex_set (HeapGraph.coerce_to_vertex_list st))
          (ensures Mark.stack_no_dups st)
          (decreases Seq.length st)
  = if Seq.length st = 0 then ()
    else begin
      HeapGraph.coerce_tail_lemma st;
      Seq.lemma_eq_elim (Seq.tail (HeapGraph.coerce_to_vertex_list st))
                        (HeapGraph.coerce_to_vertex_list (Seq.tail st));
      HeapGraph.coerce_mem_lemma (Seq.tail st) (Seq.head st);
      no_dups_of_vertex_set (Seq.tail st)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// From `Idle`
/// ---------------------------------------------------------------------------

/// In `Idle`, every live object is white.
let idle_white (h: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires PA.inv I.Idle h st /\ Seq.mem x (objects zero_addr h) /\ ~(is_blue x h))
          (ensures is_white x h)
  = MP.live_white h st x;
    hd_address_spec x;
    color_of_object_spec x h;
    is_white_iff x h

/// In `Idle`, the walk is not empty and is dense.
let idle_dense (h: heap) (st: pstate)
  : Lemma (requires PA.inv I.Idle h st)
          (ensures Seq.length (objects zero_addr h) > 0 /\ heap_objects_dense h)
  = GC.Spec.Pages.Step.pages_ok_elim h st;
    heap_tiled h st.pm;
    pages_end_bound ();
    WE.walk_nonempty_of_walk_end h zero_addr;
    WE.dense_from_walk_end h

/// Density carries over a run of recolourings.
#push-options "--fuel 1"
let rec darken_dense (h: heap) (roots: Seq.seq obj_addr)
  : Lemma (requires heap_objects_dense h)
          (ensures heap_objects_dense (darken h roots))
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      makeGray_eq (Seq.head roots) h;
      SI.color_change_preserves_density (Seq.head roots) h Gray;
      darken_dense (makeGray (Seq.head roots) h) (Seq.tail roots)
    end
#pop-options

/// What the mark needs, as `GcCorrect.mark_pre` states it, with the roots as
/// the stack.
let mark_ready (h: heap) (gs roots: Seq.seq obj_addr) : prop =
  MarkInv.mark_inv h gs /\ Mark.root_props h roots /\
  Mark.no_black_objects h /\ Mark.no_pointer_to_blue h /\
  (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r gs) /\
  GP.graph_pre h roots

/// **Darkening the roots takes `Idle` to what the mark needs.**  The
/// darkened heap is the first one up to the roots' colours, and it is in the
/// allocator's marking invariant.
let darken_ok (h: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires start_pre h st roots)
          (ensures (let hd = darken h roots in
                    mark_ready hd roots roots /\ MP.mark_inv hd st /\ PA.inv I.Marking hd st /\
                    kept h hd roots /\ Mark.no_black_objects h /\ Mark.no_pointer_to_blue h /\
                    well_formed_heap h))
  = let hd = darken h roots in
    GC.Spec.Pages.Step.pages_ok_elim h st;
    MP.mark_inv_of_ok h st;
    darken_kept h roots;
    idle_dense h st;
    darken_dense h roots;
    let white (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr h) /\ ~(is_blue x h) ==> is_white x h)
      = if Seq.mem x (objects zero_addr h) && not (is_blue x h) then idle_white h st x
    in
    FStar.Classical.forall_intro white;
    let col (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr hd) ==>
               ~(is_black x hd) /\ ~(is_black x h) /\ (is_gray x hd ==> Seq.mem x roots))
      = if Seq.mem x (objects zero_addr hd) then begin
          colors_exhaustive_and_exclusive x h;
          colors_exhaustive_and_exclusive x hd;
          is_white_iff x h;
          is_blue_iff x h;
          is_blue_iff x hd;
          is_gray_iff x hd;
          is_black_iff x h;
          is_black_iff x hd
        end
    in
    FStar.Classical.forall_intro col;
    sev_of_mem hd roots;
    no_dups_of_vertex_set roots;
    assert (Mark.stack_props hd roots);
    MarkInv.mark_inv_intro hd roots;
    assert (GP.graph_pre hd roots)
