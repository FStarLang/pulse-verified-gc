/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.End — what holds when marking has ended
///
/// In a quiescent state that meets the marking invariant, nothing is
/// pending, no worker is part-way through an object and every work list is
/// empty.  So no object is grey, every root object is black, and no black
/// object points to a white one.  `GC.Spec.Mark.black_reach_is_black` then
/// makes every reachable object black, and `sound` makes every black object
/// reachable.  Every other object keeps g's colour.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.End

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Lib.Header
open GC.Spec.MarkPar.Model
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar.Inv

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module F = GC.Spec.MarkPar.Field
module Own = GC.Spec.MarkPar.Own
module R = GC.Spec.MarkPar.Roots

/// ---------------------------------------------------------------------------
/// A quiescent state
/// ---------------------------------------------------------------------------

let rec for_all_nth (ws: list worker) (i: nat) (w: worker)
  : Lemma (requires L.for_all idle ws /\ nth ws i == Some w) (ensures idle w) (decreases ws)
  = match ws with
    | [] -> ()
    | _ :: r -> if i = 0 then () else for_all_nth r (i - 1) w

let quiet (s: state) (i: nat)
  : Lemma (requires quiescent s)
          (ensures work_at s i == [] /\ inbox_at s i == [] /\ scan_at s i == None /\ s.net == [])
  = match nth s.workers i with
    | Some w -> for_all_nth s.workers i w
    | None -> ()

let nothing_pending (cs: list nat) (s: state) (c: obj_addr)
  : Lemma (requires quiescent s) (ensures ~(pending cs s c))
  = quiet s (owner cs c)

let nothing_unscanned (cs: list nat) (s: state) (x: obj_addr) (j: nat)
  : Lemma (requires quiescent s) (ensures ~(unscanned cs s x j))
  = quiet s (owner cs x)

/// ---------------------------------------------------------------------------
/// Colours at the end
/// ---------------------------------------------------------------------------

let end_pre (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) : prop =
  ctx cs g roots /\ inv_mark cs g roots s /\ quiescent s

let end_recoloured (cs: list nat) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires end_pre cs g roots s) (ensures recoloured g s.heap)
  = reveal_opaque (`%own) (own cs g s)

let end_ctx (cs: list nat) (g: heap) (roots: list obj_addr)
  : Lemma (requires ctx cs g roots) (ensures mark_pre g roots /\ graph_pre g roots)
  = reveal_opaque (`%ctx) (ctx cs g roots)

let end_no_grey (cs: list nat) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires end_pre cs g roots s) (ensures Mark.noGreyObjects s.heap)
  = reveal_opaque (`%grey_ok) (grey_ok cs g s);
    end_recoloured cs g roots s;
    let aux (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr s.heap)) (ensures not (is_gray x s.heap)) =
      quiet s (owner cs x) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let end_roots_black (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (r: obj_addr)
  : Lemma (requires end_pre cs g roots s /\ L.memP r (root_objs g roots))
          (ensures is_black r s.heap)
  = reveal_opaque (`%roots_ok) (roots_ok cs g roots s);
    end_ctx cs g roots;
    end_recoloured cs g roots s;
    end_no_grey cs g roots s;
    nothing_pending cs s r;
    R.root_obj_facts g roots r;
    colors r g;
    colors r s.heap;
    recoloured_blue g s.heap r

/// No black object points to a white one.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let end_tri_color (cs: list nat) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires end_pre cs g roots s) (ensures Mark.tri_color_invariant s.heap)
  = let h = s.heap in
    end_recoloured cs g roots s;
    let aux (x child: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr h) /\ is_black x h /\ ~(is_no_scan x h) /\
                        points_to h x child)
              (ensures ~(is_white (resolve_object child h) h))
      = wosize_of_object_bound x h;
        let j = F.efp_witness h x (wosize_of_object x h) child in
        recoloured_wosize g h x;
        recoloured_no_scan g h x;
        colors x h;
        recoloured_blue g h x;
        assert (HeapGraph.get_field h x j == HeapGraph.get_field g x j);
        assert (is_field g x j);
        black_ok_at cs g s x j;
        nothing_pending cs s (field_target g x j);
        nothing_unscanned cs s x (U64.v j)
    in
    FStar.Classical.forall_intro_2 (fun x c -> FStar.Classical.move_requires (aux x) c)
#pop-options

/// Every reachable object is black.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let end_reachable_black (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (x: obj_addr)
  : Lemma (requires end_pre cs g roots s /\ Seq.mem x (objects zero_addr g) /\ reachable g roots x)
          (ensures is_black x s.heap)
  = let h = s.heap in
    end_ctx cs g roots;
    end_recoloured cs g roots s;
    end_no_grey cs g roots s;
    end_tri_color cs g roots s;
    let graph = create_graph g in
    let rs' = HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (root_objs g roots)) in
    reachable_set_correct graph rs';
    graph_vertices_mem g x;
    let r = FStar.IndefiniteDescription.indefinite_description_ghost (r: vertex_id{mem_graph_vertex graph r})
              (fun r -> Seq.mem r rs' /\ GC.Spec.Graph.reachable graph r x) in
    R.coerce_vertex (Seq.seq_of_list (root_objs g roots)) r;
    let ro = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
               (fun (y: obj_addr) -> U64.v y == U64.v r /\ Seq.mem y (Seq.seq_of_list (root_objs g roots))) in
    U64.v_inj r ro;
    R.mem_seq_of_list (root_objs g roots) ro;
    end_roots_black cs g roots s ro;
    let p = FStar.IndefiniteDescription.indefinite_description_ghost (reach graph ro x) (fun _ -> True) in
    Mark.black_reach_is_black graph h ro x p
#pop-options

/// Objects not reachable keep g's colour.
let end_unreachable (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (x: obj_addr)
  : Lemma (requires end_pre cs g roots s /\ Seq.mem x (objects zero_addr g) /\ ~(reachable g roots x))
          (ensures color_of_object x s.heap == color_of_object x g /\ ~(is_black x s.heap))
  = reveal_opaque (`%sound) (sound cs g roots s);
    end_ctx cs g roots;
    end_recoloured cs g roots s;
    end_no_grey cs g roots s;
    recoloured_blue g s.heap x;
    colors x g; colors x s.heap;
    is_white_iff x g; is_blue_iff x g; is_white_iff x s.heap; is_blue_iff x s.heap;
    is_gray_iff x g; is_black_iff x g

/// The run's heap, characterized.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let end_marked (cs: list nat) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires end_pre cs g roots s)
          (ensures (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      (is_black x s.heap <==> reachable g roots x)) /\
                   marked_as g s.heap (reachable g roots))
  = end_recoloured cs g roots s;
    reveal_opaque (`%sound) (sound cs g roots s);
    let col (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g))
              (ensures (reachable g roots x ==> is_black x s.heap) /\
                       (~(reachable g roots x) ==> color_of_object x s.heap == color_of_object x g) /\
                       (is_black x s.heap <==> reachable g roots x))
      = FStar.Classical.move_requires (end_reachable_black cs g roots s) x;
        FStar.Classical.move_requires (end_unreachable cs g roots s) x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires col);
    recoloured_marked_as g s.heap (reachable g roots)
#pop-options

/// The run, from mark_pre and the graph hypotheses to the end.
let run_end (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots /\ graph_pre g roots /\ quiescent (run cs g roots sched))
          (ensures (let h = (run cs g roots sched).heap in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       (is_black x h <==> reachable g roots x)) /\
                    marked_as g h (reachable g roots)))
  = reveal_opaque (`%ctx) (ctx cs g roots);
    run_mark cs g roots sched;
    end_marked cs g roots (run cs g roots sched)
