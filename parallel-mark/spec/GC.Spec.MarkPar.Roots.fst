/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Roots — the root objects, and reachability from them
///
/// `root_objs g roots` resolves each root and removes repeats.  These lemmas
/// give its members, show that `mark_pre` already supplies the graph
/// hypotheses (`graph_pre_holds`), and that the reachable objects contain the
/// root objects and are closed under the graph's edges.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Roots

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Spec.MarkPar.Model

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Lists and sequences
/// ---------------------------------------------------------------------------

let rec mem_seq_of_list (l: list obj_addr) (x: obj_addr)
  : Lemma (ensures Seq.mem x (Seq.seq_of_list l) <==> L.memP x l) (decreases l)
  = SP.lemma_seq_of_list_induction l;
    match l with
    | [] -> ()
    | h :: t -> Seq.mem_cons h (Seq.seq_of_list t); mem_seq_of_list t x

let rec dedup_mem (l: list obj_addr) (x: obj_addr)
  : Lemma (ensures L.memP x (dedup l) <==> L.memP x l) (decreases l)
  = match l with
    | [] -> ()
    | h :: t -> L.mem_memP h t; dedup_mem t x; dedup_mem t h

let rec dedup_norepeats (l: list obj_addr)
  : Lemma (ensures L.noRepeats (dedup l)) (decreases l)
  = match l with
    | [] -> ()
    | h :: t -> dedup_norepeats t; L.mem_memP h t; dedup_mem t h

let rec resolve_all_mem (g: heap) (l: list obj_addr) (c: obj_addr)
  : Lemma (ensures L.memP c (resolve_all g l) <==>
                   (exists (r: obj_addr). L.memP r l /\ c == resolve_object r g))
          (decreases l)
  = match l with
    | [] -> ()
    | h :: t -> resolve_all_mem g t c

let root_objs_mem (g: heap) (roots: list obj_addr) (c: obj_addr)
  : Lemma (L.memP c (root_objs g roots) <==>
           (exists (r: obj_addr). L.memP r roots /\ c == resolve_object r g))
  = dedup_mem (resolve_all g roots) c;
    resolve_all_mem g roots c

/// No repeats in a list: the coerced sequence is a vertex set.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec vertex_set_of_list (l: list obj_addr)
  : Lemma (requires L.noRepeats l)
          (ensures is_vertex_set (HeapGraph.coerce_to_vertex_list (Seq.seq_of_list l)))
          (decreases l)
  = SP.lemma_seq_of_list_induction l;
    match l with
    | [] -> ()
    | h :: t ->
      vertex_set_of_list t;
      HeapGraph.coerce_cons_lemma h (Seq.seq_of_list t);
      let ct = HeapGraph.coerce_to_vertex_list (Seq.seq_of_list t) in
      HeapGraph.coerce_mem_lemma (Seq.seq_of_list t) h;
      mem_seq_of_list t h;
      L.mem_memP h t;
      assert (Seq.head (Seq.cons h ct) == h);
      assert (Seq.equal (Seq.tail (Seq.cons h ct)) ct)
#pop-options

/// Membership in the coerced root sequence.
let roots'_mem (g: heap) (roots: list obj_addr) (x: obj_addr)
  : Lemma (Seq.mem x (HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (root_objs g roots))) <==>
           L.memP x (root_objs g roots))
  = HeapGraph.coerce_mem_lemma (Seq.seq_of_list (root_objs g roots)) x;
    mem_seq_of_list (root_objs g roots) x

/// ---------------------------------------------------------------------------
/// The graph hypotheses follow from mark_pre
/// ---------------------------------------------------------------------------

/// Each root object is enumerated and white.
let root_obj_facts (g: heap) (roots: list obj_addr) (c: obj_addr)
  : Lemma (requires mark_pre g roots /\ L.memP c (root_objs g roots))
          (ensures Seq.mem c (objects zero_addr g) /\ is_white c g)
  = root_objs_mem g roots c

/// A vertex of a coerced sequence is one of its objects.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec coerce_vertex (s: seq obj_addr) (x: vertex_id)
  : Lemma (requires Seq.mem x (HeapGraph.coerce_to_vertex_list s))
          (ensures exists (y: obj_addr). U64.v y == U64.v x /\ Seq.mem y s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let t = HeapGraph.coerce_to_vertex_list (Seq.tail s) in
      Seq.mem_cons (Seq.head s) t;
      Seq.cons_head_tail s;
      Seq.mem_cons (Seq.head s) (Seq.tail s);
      if x = Seq.head s then () else coerce_vertex (Seq.tail s) x
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let graph_pre_holds (g: heap) (roots: list obj_addr)
  : Lemma (requires mark_pre g roots) (ensures graph_pre g roots)
  = Mark.create_graph_wf_from_heap g;
    dedup_norepeats (resolve_all g roots);
    vertex_set_of_list (root_objs g roots);
    let sub (x: vertex_id)
      : Lemma (requires Seq.mem x (HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (root_objs g roots))))
              (ensures Seq.mem x (create_graph g).vertices)
      = coerce_vertex (Seq.seq_of_list (root_objs g roots)) x;
        let y = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                  (fun (y: obj_addr) -> U64.v y == U64.v x /\ Seq.mem y (Seq.seq_of_list (root_objs g roots))) in
        U64.v_inj x y;
        mem_seq_of_list (root_objs g roots) y;
        root_obj_facts g roots y;
        graph_vertices_mem g y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sub)
#pop-options

/// ---------------------------------------------------------------------------
/// Reachability
/// ---------------------------------------------------------------------------

let root_reachable (g: heap) (roots: list obj_addr) (r: obj_addr)
  : Lemma (requires mark_pre g roots /\ graph_pre g roots /\ L.memP r (root_objs g roots))
          (ensures reachable g roots r)
  = let graph = create_graph g in
    let roots' = HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (root_objs g roots)) in
    root_obj_facts g roots r;
    graph_vertices_mem g r;
    roots'_mem g roots r;
    reach_refl graph r;
    reachable_set_correct graph roots'

let edge_reachable (g: heap) (roots: list obj_addr) (x c: obj_addr)
  : Lemma (requires graph_pre g roots /\ reachable g roots x /\
                    Seq.mem c (objects zero_addr g) /\ mem_graph_edge (create_graph g) x c)
          (ensures reachable g roots c)
  = let graph = create_graph g in
    let roots' = HeapGraph.coerce_to_vertex_list (Seq.seq_of_list (root_objs g roots)) in
    graph_vertices_mem g c;
    reachable_successor_closed graph roots' x c
