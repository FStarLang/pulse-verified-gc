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
module Cheney = GC.Gen.Cheney
module CV = GC.Gen.CheneyGeneric
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
  = HeapModel.create_graph_with_vertices (free_incremental st) g;
    HeapModel.objects_is_vertex_set g;
    coerce_mem_obj (objects zero_addr g) v

#push-options "--z3rlimit 20"
let rec reach_aux (g: heap) (fp: U64.t) (st: sweep_state)
                  (r: Graph.vertex_id{Graph.mem_graph_vertex (sweep_graph g st) r})
                  (x: Graph.vertex_id{Graph.mem_graph_vertex (sweep_graph g st) x})
                  (w: Graph.reach (sweep_graph g st) r x)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v r >= U64.v mword /\
                    in_use (free_incremental st) g (r <: obj_addr))
          (ensures U64.v x >= U64.v mword /\ in_use (free_incremental st) g (x <: obj_addr))
          (decreases w)
  = vertex_obj g st x;
    match w with
    | Graph.ReachRefl _ -> ()
    | Graph.ReachTrans _ y _ w' ->
      reach_aux g fp st r y w';
      sweep_phase_inv_iff g fp st;
      free_incremental_ok st;
      MCFH.heap_graph_edge_to_field_read g (free_incremental st) (y <: obj_addr) (x <: obj_addr)
#pop-options

let reachable_not_free g fp st r x =
  let gr = sweep_graph g st in
  eliminate exists (w: Graph.reach gr r x). True
  with reach_aux g fp st r x w

let reachable_not_free_combined minor g fp st roots a =
  sweep_phase_inv_iff g fp st;
  RBridge.reachable_not_free (free_incremental st) minor g roots

let step_keeps_reachable g fp st r x =
  reachable_not_free g fp st r x;
  sweep_phase_step g fp st

let steps_keep_reachable g fp st k r x =
  reachable_not_free g fp st r x;
  sweep_phase_steps g fp st k

let minor_keeps_not_free minor g fp st roots x =
  SPM.minor_keeps_blocks minor g fp st roots x
