module GC.Gen.SweepPhase.Safety

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Graph = GC.Spec.Graph
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module CA = GC.Gen.CheneyAt
module Cheney = GC.Gen.Cheney
module CE = GC.Gen.CheneyExcept
module Paint = GC.Gen.Paint
module Promote = GC.Gen.Promote
module SPM = GC.Gen.SweepPhase.Minor
module Ph = GC.Spec.Phase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// A vertex of the heap graph is an object.
#push-options "--fuel 1"
let rec coerce_mem_obj (s: seq obj_addr) (v: Graph.vertex_id)
  : Lemma (ensures Seq.mem v (HeapGraph.coerce_to_vertex_list s) ==>
                   U64.v v >= U64.v mword /\ Seq.mem (v <: obj_addr) s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      Seq.Properties.mem_cons (Seq.head s) (HeapGraph.coerce_to_vertex_list (Seq.tail s));
      coerce_mem_obj (Seq.tail s) v;
      if Seq.mem v (HeapGraph.coerce_to_vertex_list (Seq.tail s)) then
        Seq.Properties.mem_cons (Seq.head s) (Seq.tail s);
      Seq.Properties.cons_head_tail s
    end
#pop-options

let vertex_obj (g: heap) (st: sweep_state) (v: Graph.vertex_id)
  : Lemma (requires Graph.mem_graph_vertex (sweep_graph g st) v)
          (ensures U64.v v >= U64.v mword /\ Seq.mem (v <: obj_addr) (objects zero_addr g))
  = HeapModel.create_graph_except_vertices g (pending g st);
    HeapModel.objects_is_vertex_set g;
    coerce_mem_obj (objects zero_addr g) v

#push-options "--z3rlimit 20"
let rec reach_aux (g: heap) (fp: U64.t) (st: sweep_state)
                  (r: Graph.vertex_id{Graph.mem_graph_vertex (sweep_graph g st) r})
                  (x: Graph.vertex_id{Graph.mem_graph_vertex (sweep_graph g st) x})
                  (w: Graph.reach (sweep_graph g st) r x)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v r >= U64.v mword /\
                    not_freed g (pending g st) (r <: obj_addr))
          (ensures U64.v x >= U64.v mword /\ not_freed g (pending g st) (x <: obj_addr))
          (decreases w)
  = vertex_obj g st x;
    match w with
    | Graph.ReachRefl _ -> ()
    | Graph.ReachTrans _ y _ w' ->
      reach_aux g fp st r y w';
      sweep_phase_inv_iff g fp st;
      MCFH.heap_graph_edge_to_field_read g (pending g st) (y <: obj_addr) (x <: obj_addr)
#pop-options

let reachable_not_pending g fp st r x =
  let gr = sweep_graph g st in
  eliminate exists (w: Graph.reach gr r x). True
  with reach_aux g fp st r x w

let reachable_not_pending_combined minor g fp st roots v =
  sweep_phase_inv_iff g fp st;
  RBridge.reachable_never_pending minor g (pending g st) roots

let step_keeps_reachable g fp st r x =
  reachable_not_pending g fp st r x;
  sweep_phase_step g fp st

let steps_keep_reachable g fp st k r x =
  reachable_not_pending g fp st r x;
  sweep_phase_steps g fp st k

#push-options "--z3rlimit 20"
let minor_keeps_not_freed minor g fp st roots x =
  let pf = pending g st in
  SPM.minor_keeps_sweep_phase minor g fp st roots;
  SPM.sweep_collection_shape minor g fp st;
  GenInv.collection_shape_except_elim minor g fp pf;
  GenInv.major_shape_except_elim g fp pf;
  GenInv.minor_heap_shape_elim minor;
  CE.cheney_promote_keeps_not_freed minor g fp roots pf x;
  let prom = Cheney.cheney_promote minor g fp roots in
  let res = Cheney.cheney_collect_spec_except minor g fp roots pf in
  GC.Spec.SweepPhase.Util.part1_holds prom.Promote.major_final;
  CE.update_walk_not_freed prom.Promote.major_final (not_freed prom.Promote.major_final pf) pf
    prom.Promote.fwd_map x;
  Paint.paint_ph_recoloured (Ph.Sweeping st) g res.Promote.mc_major;
  Paint.recoloured_facts res.Promote.mc_major (Paint.paint_ph (Ph.Sweeping st) g res.Promote.mc_major)
#pop-options
