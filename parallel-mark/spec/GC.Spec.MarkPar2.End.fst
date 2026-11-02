/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.End — every run keeps the invariant; a finished run
/// leaves the sequential mark's heap
///
/// `run_inv`: setup establishes `inv` (`GC.Spec.MarkPar2.Init`), and every
/// step keeps it (`.Step` for workers, `.Main` for the main thread).
///
/// When marking is done, `fin_ok` says no flag is set, every worker has
/// stopped and the counter is 0; so every stack and inbox is empty and no
/// worker holds or scans anything.  Then grey_ok leaves no grey object,
/// black_ok leaves no black object pointing to a white one, and roots_ok
/// makes every root object black.  So exactly the reachable objects are
/// black (`GC.Spec.Mark.black_reach_is_black` one way, `sound` the other),
/// and every other object keeps g's colour: the heap has the shape
/// `marked_as g h (reachable g roots)`, as the sequential mark's does
/// (`GC.Spec.MarkPar.Seq`).
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.End

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
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar2.Model
open GC.Spec.MarkPar2.Inv

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module M1 = GC.Spec.MarkPar.Model
module I1 = GC.Spec.MarkPar.Inv
module F = GC.Spec.MarkPar.Field
module R = GC.Spec.MarkPar.Roots
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module St = GC.Spec.MarkPar2.Step
module Mn = GC.Spec.MarkPar2.Main
module In = GC.Spec.MarkPar2.Init

/// ---------------------------------------------------------------------------
/// Runs
/// ---------------------------------------------------------------------------

let step_inv (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (e: event)
  : Lemma (requires ctx k g roots /\ inv k g roots s) (ensures inv k g roots (step k s e))
  = if s.finished then ()
    else match e with
      | W i -> St.wstep_inv k g roots s i
      | Main -> if all_stopped s.wks then Mn.main_inv k g roots s

let rec run_from_inv (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (sched: list event)
  : Lemma (requires ctx k g roots /\ inv k g roots s)
          (ensures inv k g roots (run_from k s sched))
          (decreases sched)
  = match sched with
    | [] -> ()
    | e :: rest -> step_inv k g roots s e; run_from_inv k g roots (step k s e) rest

let run_inv (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires ctx k g roots) (ensures inv k g roots (run k g roots sched))
  = In.init_inv k g roots;
    run_from_inv k g roots (init k g roots) sched

/// ---------------------------------------------------------------------------
/// When marking is done
/// ---------------------------------------------------------------------------

let end_pre (k: cfg) (g: heap) (roots: list obj_addr) (s: state) : prop =
  ctx k g roots /\ inv k g roots s /\ s.finished

let quiet (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires end_pre k g roots s)
          (ensures ~(flagged s) /\ recoloured g s.heap /\
                   (forall (i: nat) (v: obj_addr). ~(holds s i v)) /\
                   (forall (x: obj_addr) (j: nat). ~(unscanned k s x j)) /\
                   (forall (i: nat). stack_of s i == []))
  = reveal_opaque (`%fin_ok) (fin_ok s);
    U.own_heap k g s;
    Mn.stopped_empty k g s;
    let st (i: nat) : Lemma (stack_of s i == [] /\ (forall (v: obj_addr). ~(holds s i v)) /\
                             ~(Scan? (pc_of s i))) =
      match wk_of s i with Some w -> () | None -> () in
    FStar.Classical.forall_intro st

let end_no_grey (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires end_pre k g roots s) (ensures Mark.noGreyObjects s.heap)
  = quiet k g roots s;
    reveal_opaque (`%grey_ok) (grey_ok k g s);
    let aux (x: obj_addr) : Lemma (requires Seq.mem x (objects zero_addr s.heap)) (ensures not (is_gray x s.heap)) =
      assert (stack_of s (own k x) == []) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let end_roots_black (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (r: obj_addr)
  : Lemma (requires end_pre k g roots s /\ L.memP r (M1.root_objs g roots))
          (ensures is_black r s.heap)
  = reveal_opaque (`%roots_ok) (roots_ok g roots s);
    ctx_elim k g roots;
    quiet k g roots s;
    end_no_grey k g roots s;
    R.root_obj_facts g roots r;
    colors r g;
    colors r s.heap;
    recoloured_blue g s.heap r

/// No black object points to a white one.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let end_tri_color (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires end_pre k g roots s) (ensures Mark.tri_color_invariant s.heap)
  = let h = s.heap in
    quiet k g roots s;
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
        assert (I1.is_field g x j);
        black_ok_at k g s None x j;
        assert (~(pending g s (I1.field_target g x j)));
        assert (~(unscanned k s x (U64.v j)))
    in
    FStar.Classical.forall_intro_2 (fun x c -> FStar.Classical.move_requires (aux x) c)
#pop-options

/// Every reachable object is black.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let end_reachable_black (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (x: obj_addr)
  : Lemma (requires end_pre k g roots s /\ Seq.mem x (objects zero_addr g) /\ M1.reachable g roots x)
          (ensures is_black x s.heap)
  = let h = s.heap in
    ctx_elim k g roots;
    quiet k g roots s;
    end_no_grey k g roots s;
    end_tri_color k g roots s;
    let graph = create_graph g in
    let rs' = HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (M1.root_objs g roots)) in
    reachable_set_correct graph rs';
    graph_vertices_mem g x;
    let r = FStar.IndefiniteDescription.indefinite_description_ghost (r: vertex_id{mem_graph_vertex graph r})
              (fun r -> Seq.mem r rs' /\ GC.Spec.Graph.reachable graph r x) in
    R.coerce_vertex (Seq.seq_of_list (M1.root_objs g roots)) r;
    let ro = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
               (fun (y: obj_addr) -> U64.v y == U64.v r /\ Seq.mem y (Seq.seq_of_list (M1.root_objs g roots))) in
    U64.v_inj r ro;
    R.mem_seq_of_list (M1.root_objs g roots) ro;
    end_roots_black k g roots s ro;
    let p = FStar.IndefiniteDescription.indefinite_description_ghost (reach graph ro x) (fun _ -> True) in
    Mark.black_reach_is_black graph h ro x p
#pop-options

/// Objects not reachable keep g's colour.
let end_unreachable (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (x: obj_addr)
  : Lemma (requires end_pre k g roots s /\ Seq.mem x (objects zero_addr g) /\ ~(M1.reachable g roots x))
          (ensures color_of_object x s.heap == color_of_object x g /\ ~(is_black x s.heap))
  = reveal_opaque (`%sound) (sound g roots s);
    ctx_elim k g roots;
    quiet k g roots s;
    end_no_grey k g roots s;
    recoloured_blue g s.heap x;
    colors x g; colors x s.heap;
    is_white_iff x g; is_blue_iff x g; is_white_iff x s.heap; is_blue_iff x s.heap;
    is_gray_iff x g; is_black_iff x g

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let end_marked (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires end_pre k g roots s)
          (ensures (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      (is_black x s.heap <==> M1.reachable g roots x)) /\
                   marked_as g s.heap (M1.reachable g roots))
  = quiet k g roots s;
    let col (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g))
              (ensures (M1.reachable g roots x ==> is_black x s.heap) /\
                       (~(M1.reachable g roots x) ==> color_of_object x s.heap == color_of_object x g) /\
                       (is_black x s.heap <==> M1.reachable g roots x))
      = FStar.Classical.move_requires (end_reachable_black k g roots s) x;
        FStar.Classical.move_requires (end_unreachable k g roots s) x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires col);
    recoloured_marked_as g s.heap (M1.reachable g roots)
#pop-options

/// A finished run's heap, characterized.
let run_end (k: cfg) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires M1.mark_pre g roots /\ valid_cfg k /\ (run k g roots sched).finished)
          (ensures (let h = (run k g roots sched).heap in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       (is_black x h <==> M1.reachable g roots x)) /\
                    marked_as g h (M1.reachable g roots)))
  = R.graph_pre_holds g roots;
    reveal_opaque (`%ctx) (ctx k g roots);
    run_inv k g roots sched;
    end_marked k g roots (run k g roots sched)
