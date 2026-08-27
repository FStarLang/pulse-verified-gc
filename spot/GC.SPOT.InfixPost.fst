module GC.SPOT.InfixPost

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecFields = GC.Spec.Fields
module SpecCorrectness = GC.Spec.Correctness
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module SpecGraph = GC.Spec.Graph
module SpecDFS = GC.Spec.DFS
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module Promote = GC.Gen.Promote
module GenImpl = GC.Gen.Impl
module MajorPre = GC.Gen.MajorPrecondition
module GenInv = GC.Gen.HeapInvariant
module MinorFwd = GC.Gen.MinorCollectForwarding
module MajorGC = GC.Impl
module Postconditions = GC.SPOT.Postconditions
module InfixMajor = GC.SPOT.InfixMajor
module InfixPre = GC.SPOT.InfixPre

#set-options "--z3rlimit 30 --fuel 1 --ifuel 1"

let spot_infix_ok (r: unit{InfixMajor.spot_infix_room}) (ok: bool)
  =
  InfixPre.spot_infix_no_oom r

/// `Q` is still a root after the minor collection: it is not a minor pointer,
/// so root rewriting leaves it alone.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let post_roots_mem_q
  (r: unit{InfixMajor.spot_infix_room})
  (roots_out: seq U64.t) (st: seq obj_addr) (cap: nat)
  : Lemma
      (requires
        GenImpl.gen_gc_roots_post
          InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
          (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r)
          roots_out true st cap)
      (ensures
        Seq.mem (InfixMajor.spot_q r <: U64.t) roots_out /\
        Seq.mem (InfixMajor.spot_q r)
          (GenImpl.gen_gc_prepared_roots
            InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
            (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r) st cap))
  =
  let q = InfixMajor.spot_q r in
  let roots = InfixPre.spot_infix_roots r in
  let prom = Cheney.cheney_promote
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
    (InfixMajor.spot_infix_fp r) roots in
  let res = Cheney.cheney_collect_spec
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
    (InfixMajor.spot_infix_fp r) roots in
  assert (roots_out == res.mc_roots);
  InfixPre.spot_infix_roots_len r;
  Promote.rewrite_roots_length roots prom.fwd_map;
  Promote.rewrite_roots_index roots prom.fwd_map 0;
  InfixMajor.spot_infix_layout_facts r;
  zero_addr_above_minor ();
  assert (~(Promote.is_minor_pointer (q <: U64.t)));
  assert (Promote.rewrite_root (q <: U64.t) prom.fwd_map == (q <: U64.t));
  assert (Seq.length roots_out > 0);
  assert (Seq.index roots_out 0 == (q <: U64.t));
  FStar.Seq.Properties.seq_mem_k roots_out 0;
  let prepared_roots = GenImpl.gen_gc_prepared_roots
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
    (InfixMajor.spot_infix_fp r) roots st cap in
  GC.Spec.Base.is_val_addr_spec (q <: U64.t);
  // `q` is a major root, so it survives rewriting untouched and still names
  // itself in the post-minor heap; the darkened stack therefore holds it
  // literally, not merely up to resolution.
  InfixPre.spot_infix_collection_heap_shape r;
  InfixPre.spot_infix_roots_valid r;
  MajorPre.post_minor_major_root_valid
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
    (InfixMajor.spot_infix_fp r) roots (q <: U64.t);
  GenImpl.gen_gc_named_root_in_stack
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
    (InfixMajor.spot_infix_fp r) roots roots_out st cap ((q <: U64.t) <: obj_addr);
  assert (Seq.mem ((q <: U64.t) <: obj_addr) prepared_roots)
#pop-options

/// Any prepared root is reachable in the prepared (post-minor) heap, which is
/// what the major-collection survival theorem is stated against.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let prepared_root_heap_reachable
  (r: unit{InfixMajor.spot_infix_room})
  (st: seq obj_addr) (cap: nat) (v: obj_addr)
  : Lemma
      (requires
        GenImpl.gen_gc_stack_budget (InfixPre.spot_infix_roots r) st cap /\
        Seq.mem v (GenImpl.gen_gc_prepared_roots
          InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
          (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r) st cap))
      (ensures
        SpecCorrectness.heap_reachable
          (GenImpl.gen_gc_prepared_major
            InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
            (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r) st cap)
          (GenImpl.gen_gc_prepared_roots
            InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
            (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r) st cap)
          v)
  =
  let minor = InfixPre.spot_infix_minor in
  let major = InfixMajor.spot_infix_heap r in
  let fp = InfixMajor.spot_infix_fp r in
  let roots = InfixPre.spot_infix_roots r in
  InfixPre.spot_infix_collection_heap_shape r;
  InfixPre.spot_infix_roots_valid r;
  InfixPre.spot_infix_cheney_no_oom r;
  let prepared_major = GenImpl.gen_gc_prepared_major minor major fp roots st cap in
  let prepared_roots = GenImpl.gen_gc_prepared_roots minor major fp roots st cap in
  let graph = HeapModel.create_graph prepared_major in
  let roots' = HeapGraph.coerce_to_vertex_list prepared_roots in
  GenImpl.gen_gc_major_precondition_elim minor major fp roots st cap;
  assert (MajorGC.gc_precondition_with_roots
    prepared_major prepared_roots prepared_roots
    (Cheney.cheney_collect_spec minor major fp roots).mc_fp cap);
  HeapGraph.coerce_mem_lemma prepared_roots v;
  assert (Seq.mem v roots');
  assert (SpecGraph.mem_graph_vertex graph v);
  assert (Seq.mem v (SpecDFS.reachable_set graph roots'));
  assert (SpecCorrectness.heap_reachable prepared_major prepared_roots v)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let spot_infix_q_survives
  (r: unit{InfixMajor.spot_infix_room})
  (roots_out: seq U64.t) (final_major: heap) (st: seq obj_addr) (cap: nat)
  =
  post_roots_mem_q r roots_out st cap;
  prepared_root_heap_reachable r st cap (InfixMajor.spot_q r);
  Postconditions.final_major_survives_from_gen_gc_post
    InfixPre.spot_infix_minor (InfixMajor.spot_infix_heap r)
    (InfixMajor.spot_infix_fp r) (InfixPre.spot_infix_roots r)
    roots_out true final_major st cap (InfixMajor.spot_q r)
#pop-options
