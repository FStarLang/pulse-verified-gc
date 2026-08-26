module GC.SPOT.MinorInfix

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecObj = GC.Spec.Object
module SpecMark = GC.Spec.Mark
module SpecHeap = GC.Spec.Heap
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module GenInv = GC.Gen.HeapInvariant
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CG = GC.Gen.CombinedGraph
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs

/// ---------------------------------------------------------------------------
/// SPOT: an *interior* pointer into the nursery
/// ---------------------------------------------------------------------------
///
/// `GC.SPOT.InfixMajor` audits an interior pointer between two *major* objects.
/// This module audits the nursery case: a major object `c` whose field `i`
/// holds an interior pointer into a minor-heap closure.
///
/// Stock OCaml produces exactly this shape.  `CLOSUREREC`
/// (`runtime/interp.c:575`) allocates a mutually recursive closure group in the
/// minor heap whenever it fits in `Max_young_wosize` (256 words,
/// `runtime/caml/config.h:204`), and pushes the *infix* entry points of the
/// group as values (`runtime/interp.c:601`).  `caml_modify`
/// (`runtime/memory.c:617`) has no infix special case, so storing such a value
/// into a major field yields a major-to-minor interior pointer, recorded in the
/// remembered set like any other.  `caml_oldify_one`
/// (`runtime/minor_gc.c:231`) handles it by forwarding the parent and re-adding
/// the offset --- which is precisely what the theorem below states our
/// collector does.
///
/// The point of the SPOT is that this heap satisfies the *unmodified*
/// `collection_heap_shape` precondition: nothing in the invariant forbids the
/// interior pointer, and the conclusions below are proved from the ordinary
/// minor-collection theorems.

/// The address of field `i` of major object `c`.
let field_slot (c: obj_addr) (i: nat{U64.v c + i * 8 + 8 <= heap_size}) : U64.t =
  U64.uint_to_t (U64.v c + i * 8)

/// The interior pointer as stored in that field, in nursery-offset form.
let stored_target
  (major: heap) (c: obj_addr) (i: nat{U64.v c + i * 8 + 8 <= heap_size}) : GTot U64.t =
  to_minor_offset (SpecHeap.read_word major (field_slot c i))

/// The scenario.  Everything above the horizontal rule is what any client of
/// `cheney_collect_spec` already has to supply; only the last three conjuncts
/// are specific to this SPOT.
let minor_infix_scenario
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  (c: obj_addr) (i: nat) : prop =
  U64.v c + i * 8 + 8 <= heap_size /\
  (U64.v c + i * 8) % 8 == 0 /\
  // ---- the standard minor-collection context ------------------------------
  GenInv.collection_heap_shape minor major fp /\
  RBridge.major_field_zero_covered minor major roots /\
  UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
  MinorFwd.remembered_targets_in_roots major roots slots n /\
  SpecMark.no_pointer_to_blue major /\
  RBridge.minor_no_pointer_to_blue minor major /\
  RBridge.roots_valid_nonblue roots major /\
  CheneyBFS.cheney_no_oom minor major fp roots /\
  ~(SpecObj.is_no_scan c major) /\
  i < U64.v (SpecObj.wosize_of_object c major) /\
  (let cg = CG.build_combined_graph minor major in
   let combined_roots = CG.classify_roots minor roots in
   CG.combined_reachable cg combined_roots (CG.MajorV c) /\
   CG.combined_reachable cg combined_roots
     (CG.MinorV (infix_parent minor (stored_target major c i)))) /\
  // ---- what makes this the interior-pointer scenario -----------------------
  is_infix_in_minor minor (stored_target major c i) /\
  minor_wosize minor (infix_parent minor (stored_target major c i)) > 0 /\
  HeapGraph.is_pointer_field
    ((Cheney.cheney_promote minor major fp roots).fwd_map
      (infix_parent minor (stored_target major c i)))

/// The nursery interior pointer is admissible: the scenario really does satisfy
/// the collector's entry invariant, with the interior pointer in place.  (This
/// is the conjunct that used to be impossible: `collection_heap_shape` carried
/// `major_minor_fields_no_infix_targets`, which contradicts the last group of
/// clauses above.)
val spot_minor_infix_admissible
  : minor:minor_state -> major:heap -> fp:U64.t ->
    roots:seq U64.t -> slots:seq U64.t -> n:nat ->
    c:obj_addr -> i:nat ->
    Lemma
      (requires minor_infix_scenario minor major fp roots slots n c i)
      (ensures
        GenInv.collection_heap_shape minor major fp /\
        is_infix_in_minor minor (stored_target major c i) /\
        // the enclosing closure is a genuine nursery object carrying
        // `Closure_tag`, and the interior pointer lies strictly inside it
        (let ov = stored_target major c i in
         let par = infix_parent minor ov in
         Seq.mem par (minor_objects minor) /\
         minor_tag minor par == 247 /\
         minor_wosize minor ov >= 2 /\
         U64.v ov - U64.v par < minor_wosize minor par * 8))

/// The audit.  After the minor collection:
///
///   * the enclosing closure is promoted (`fwd par <> 0`);
///   * the *interior* address is forwarded too, and its image is again an
///     interior pointer of the post-collection major heap, resolving to the
///     promoted closure --- i.e. the offset is preserved, exactly as
///     `caml_oldify_one` does with `*p += offset`;
///   * the major field is rewritten to that interior image, not to the closure;
///   * and the post-collection heap graph nevertheless carries the edge
///     `c -> promoted closure`, because the graph resolves interior pointers.
val spot_minor_infix_promoted
  : minor:minor_state -> major:heap -> fp:U64.t ->
    roots:seq U64.t -> slots:seq U64.t -> n:nat ->
    c:obj_addr -> i:nat ->
    Lemma
      (requires minor_infix_scenario minor major fp roots slots n c i)
      (ensures (
        let prom = Cheney.cheney_promote minor major fp roots in
        let post = (Cheney.cheney_collect_spec minor major fp roots).mc_major in
        let ov = stored_target major c i in
        let par = infix_parent minor ov in
        prom.fwd_map par <> 0UL /\
        prom.fwd_map ov <> 0UL /\
        is_val_addr (prom.fwd_map ov) /\
        SpecObj.is_infix ((prom.fwd_map ov) <: obj_addr) post /\
        SpecObj.resolve_object ((prom.fwd_map ov) <: obj_addr) post ==
          prom.fwd_map par /\
        SpecHeap.read_word post (field_slot c i) == prom.fwd_map ov /\
        MinorFwd.mem_graph_edge_at (HeapModel.create_graph post)
          c (prom.fwd_map par)))

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------
///
/// A lemma whose precondition is unsatisfiable proves nothing, and *this*
/// precondition used to be unsatisfiable: `collection_heap_shape` carried a
/// clause forbidding exactly the shape above.  The clause is reproduced here
/// verbatim (it is no longer part of any invariant) so that the SPOT can state
/// what changed --- the scenario is precisely, and only, what the deleted
/// restriction ruled out.
///
/// This does not by itself exhibit a witness.  Doing that needs a *concrete*
/// nursery containing a closure with an infix header, which in turn needs a
/// nursery body-write primitive: `GC.Gen.MinorHeap` currently only ever
/// produces minor states through `minor_init` and `minor_alloc_spec`, whose
/// object bodies are all zero.  See `docs/minor-infix-support-plan.md`.
let deleted_major_minor_fields_no_infix_targets
  (minor: minor_state) (major: heap) : prop =
  forall (obj: obj_addr) (j: nat).
    Seq.mem obj (GC.Spec.Fields.objects zero_addr major) /\
    ~(SpecObj.is_blue obj major) /\
    ~(SpecObj.is_no_scan obj major) /\
    j < U64.v (SpecObj.wosize_of_object obj major) /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (U64.v obj + j * 8) % 8 == 0 ==>
    ~(is_infix_in_minor minor
        (to_minor_offset (SpecHeap.read_word major (U64.uint_to_t (U64.v obj + j * 8)))))

/// The scenario is exactly what the deleted clause forbade.
val spot_minor_infix_was_forbidden
  : minor:minor_state -> major:heap -> fp:U64.t ->
    roots:seq U64.t -> slots:seq U64.t -> n:nat ->
    c:obj_addr -> i:nat ->
    Lemma
      (requires minor_infix_scenario minor major fp roots slots n c i /\
                deleted_major_minor_fields_no_infix_targets minor major)
      (ensures False)
