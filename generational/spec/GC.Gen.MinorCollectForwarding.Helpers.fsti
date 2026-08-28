/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding -- Minor-collection forwarding kernel
/// ---------------------------------------------------------------------------
///
/// This module captures the reusable forwarding kernel of the upstream
/// minor-collection isomorphism proof, specialized to the current
/// `minor_collect_full` path.
///
/// The property is intentionally stated over `cheney_collect_spec`, since the
/// Pulse implementation proves its concrete two-pass update equals that spec.
/// The source roots are the program roots plus the remembered-set slot targets;
/// when those remembered targets are represented in the root array and the
/// collector returns `ok`, the forwarding map is an injective morphism for
/// reachable minor objects and all images are valid post-minor addresses
/// (ordinary objects or infix interior pointers).  This is NOT, by itself, a
/// graph isomorphism: the full reachable-subgraph isomorphism additionally
/// proves surjectivity onto the post-minor reachable subgraph and edge
/// preservation/reflection.  The result-indexed wrapper states that theorem
/// directly over the heap and roots returned by `minor_collect_full`.

module GC.Gen.MinorCollectForwarding.Helpers

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered
open GC.Gen.Reachability
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromUpdate = GC.Gen.PromoteUpdate
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel

/// Read the remembered-set slot targets from the pre-collection major heap.
/// Only valid slots containing minor pointers contribute roots.
val remembered_slot_targets_from
  (major: heap) (slots: seq U64.t) (n idx: nat) : GTot (seq U64.t)

let remembered_slot_targets (major: heap) (slots: seq U64.t) (n: nat)
  : GTot (seq U64.t) =
  remembered_slot_targets_from major slots n 0

let remembered_targets_in_roots
  (major: heap) (roots slots: seq U64.t) (n: nat) : prop =
  forall (r: U64.t).
    Seq.mem r (remembered_slot_targets major slots n) ==> Seq.mem r roots

val remembered_targets_in_roots_intro_by_slots:
  major:heap ->
  roots:seq U64.t ->
  slots:seq U64.t ->
  n:nat ->
  Lemma
    (requires n <= Seq.length slots /\
      (forall (i:nat). i < n ==>
        U64.v (Seq.index slots i) < heap_size /\
        U64.v (Seq.index slots i) % U64.v mword == 0 /\
        (let slot = (Seq.index slots i <: hp_addr) in
         let v = to_minor_offset (read_word major slot) in
         is_minor_pointer v ==> Seq.mem v roots)))
    (ensures remembered_targets_in_roots major roots slots n)

#push-options "--z3rlimit 10"
/// Root validity needed to make the target be all concrete post-reachable
/// vertices: a minor-shaped root must *resolve* to a real live minor object,
/// while a non-minor root must be an allocated major object.
///
/// The minor branch is stated on `resolve_minor minor r` rather than on `r`
/// itself so that an **interior** nursery root is admissible: OCaml pushes the
/// entry point of a non-first function of a mutually recursive group directly
/// (`runtime/interp.c:601`) and the byte-code root scanner walks such stack
/// slots verbatim (`runtime/roots_byt.c:39`).  For a non-interior root
/// `resolve_minor` is the identity, so this is a genuine weakening.
let roots_valid_for_minor_collection
  (minor: minor_state) (major: heap) (roots: seq U64.t) : prop =
  forall (r: U64.t).
    Seq.mem r roots ==>
    ((is_minor_pointer r ==>
      Seq.mem (resolve_minor minor r) (minor_objects minor) /\
      minor_wosize minor (resolve_minor minor r) > 0) /\
     (~(is_minor_pointer r) ==>
     is_val_addr r /\ Seq.mem (r <: obj_addr) (objects zero_addr major) /\
     ~(is_blue (r <: obj_addr) major)))
#pop-options

/// `roots_valid_for_minor_collection` subsumes `RBridge.roots_valid_nonblue`:
/// the non-minor branch of the former already establishes exactly the
/// non-blueness that the latter asserts, under strictly weaker hypotheses
/// (the latter additionally guards on `is_val_addr` and object membership,
/// both of which the former supplies outright).  Callers that already have
/// the former therefore need not carry the latter as a separate assumption.
val roots_valid_for_minor_collection_nonblue
  (minor: minor_state) (major: heap) (roots: seq U64.t)
  : Lemma
    (requires roots_valid_for_minor_collection minor major roots)
    (ensures RBridge.roots_valid_nonblue roots major)

/// The slot table already covers field 0.
///
/// `ref_table_covers_minor_ptrs` quantifies over `j < wosize` at address
/// `obj + j*8`, so `j = 0` -- the word at `obj + 0` -- is included; the write
/// barrier records that field like any other.  Combined with
/// `remembered_targets_in_roots`, which puts every recorded slot's minor target
/// into the Cheney root sequence, the two preconditions that
/// `minor_collect_full` already demands are together enough to discharge
/// `RBridge.major_field_zero_covered` outright.
///
/// Callers therefore do not need to supply a separate field-0 hypothesis at
/// all: it is discharged inside `minor_collect_full` from preconditions the
/// caller was already required to establish.
val major_field_zero_covered_from_slots
  (minor: minor_state) (major: heap) (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n)
    (ensures RBridge.major_field_zero_covered minor major roots)

/// Raw-address view of graph-edge membership, useful when the endpoint is a
/// forwarding-map image whose `hp_addr` refinement is proved by preconditions.
let mem_graph_edge_at (g: graph_state) (src dst: U64.t) : prop =
  exists (s: hp_addr) (d: hp_addr).
    s == src /\ d == dst /\ mem_graph_edge g s d

let mem_graph_vertex_at (g: graph_state) (w: U64.t) : prop =
  exists (x: vertex_id{mem_graph_vertex g x}). x == w

/// The objects a post-collection root sequence names.
///
/// A rewritten root may be an *interior* pointer: `rewrite_root` is
/// deliberately raw --- an interior root must keep its offset at run time ---
/// so it maps an interior nursery root `r` to `fwd r`, which by
/// `fwd_infix_targets_wf` is an interior pointer into the promoted copy of the
/// closure `r` points into.  Such an address is not a graph vertex, so the
/// post-collection reachable set has to be rooted at the objects the roots
/// *name*, exactly as the collector's own marking does.
///
/// Resolving *once, into a concrete sequence* rather than putting the
/// resolution step inside the reachability predicate is what makes this
/// tractable.  `result_post_reachable` stays a statement about a fixed root
/// set, so the major collection can be crossed
/// (`GC.Gen.MajorReachabilityTransfer`) with no obligation to show that the
/// roots resolve the same way on both sides of a sweep --- an obligation that
/// bottoms out in an `infix_addr_wf` bound nothing supplies for a root.
let rec resolve_roots (h: heap) (rts: seq U64.t)
  : GTot (seq U64.t) (decreases Seq.length rts) =
  if Seq.length rts = 0 then Seq.empty
  else Seq.cons (HeapGraph.resolve_field h (Seq.head rts))
                (resolve_roots h (Seq.tail rts))

val resolve_roots_length (h: heap) (rts: seq U64.t)
  : Lemma (ensures Seq.length (resolve_roots h rts) == Seq.length rts)
          (decreases Seq.length rts)
          [SMTPat (Seq.length (resolve_roots h rts))]

/// Every root's resolution is in the resolved sequence.
val resolve_roots_mem (h: heap) (rts: seq U64.t) (rr: U64.t)
  : Lemma (requires Seq.mem rr rts)
          (ensures Seq.mem (HeapGraph.resolve_field h rr) (resolve_roots h rts))
          (decreases Seq.length rts)

/// ... and nothing else is.
val resolve_roots_mem_inv (h: heap) (rts: seq U64.t) (e: U64.t)
  : Lemma (requires Seq.mem e (resolve_roots h rts))
          (ensures exists (rr: U64.t).
                     Seq.mem rr rts /\ HeapGraph.resolve_field h rr == e)
          (decreases Seq.length rts)

/// Two heaps that resolve every root alike produce the same resolved sequence.
/// Root darkening is such a pair, which is how the post-minor statement is
/// carried to the heap the major collection actually starts from.
val resolve_roots_congr (h1 h2: heap) (rts: seq U64.t)
  : Lemma
    (requires forall (v: U64.t).
                HeapGraph.resolve_field h1 v == HeapGraph.resolve_field h2 v)
    (ensures resolve_roots h1 rts == resolve_roots h2 rts)
    (decreases Seq.length rts)

/// Result-indexed post-minor reachability: this names the concrete heap and
/// (already resolved) roots exposed by an implementation postcondition.
let result_post_reachable
  (post_major: heap) (post_roots: seq U64.t) (w: U64.t) : prop =
  let post_g = HeapModel.create_graph post_major in
  exists (rr: U64.t)
         (r: vertex_id{mem_graph_vertex post_g r})
         (x: vertex_id{mem_graph_vertex post_g x}).
    Seq.mem rr post_roots /\
    r == rr /\ x == w /\ reachable post_g r x

/// The same predicate at the collector's own heap and resolved rewritten roots.
///
/// It is *defined* as `result_post_reachable` rather than restated, so the two
/// are interchangeable by unfolding alone.  Restating it duplicates a
/// three-binder existential whose binders are refined by a graph built from the
/// heap, and transporting a witness between two such copies across a
/// propositional heap equality is not something the solver manages.
let post_minor_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (w: U64.t) : prop =
  let prom = cheney_promote minor major fp roots in
  let res = cheney_collect_spec minor major fp roots in
  result_post_reachable res.mc_major
    (resolve_roots res.mc_major (rewrite_roots roots prom.fwd_map)) w

let post_minor_edge
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x y: U64.t) : prop =
  let res = cheney_collect_spec minor major fp roots in
  mem_graph_edge_at (HeapModel.create_graph res.mc_major) x y

let result_post_edge (post_major: heap) (x y: U64.t) : prop =
  mem_graph_edge_at (HeapModel.create_graph post_major) x y

/// Reflexive entry at an *abstract* heap: a rewritten root that is itself a
/// graph vertex is post-reachable.
///
/// Stated abstractly on purpose.  Performed in place --- where the heap is the
/// applied term `(cheney_collect_spec minor major fp roots).mc_major` --- the
/// solver does not find the three witnesses.
val result_post_reachable_refl_direct
  (post_major: heap) (post_roots: seq U64.t) (w: U64.t)
  : Lemma
    (requires Seq.mem w post_roots /\
              mem_graph_vertex_at (HeapModel.create_graph post_major) w)
    (ensures result_post_reachable post_major post_roots w)

/// The same for a root whose *resolution* is the vertex.
val result_post_reachable_refl_resolved
  (post_major: heap) (rts: seq U64.t) (rr w: U64.t)
  : Lemma
    (requires Seq.mem rr rts /\
              HeapGraph.resolve_field post_major rr == w /\
              mem_graph_vertex_at (HeapModel.create_graph post_major) w)
    (ensures result_post_reachable post_major (resolve_roots post_major rts) w)

/// A rewritten root that names `w` --- either directly, or, when the root is an
/// interior pointer, by resolving to it --- makes `w` post-reachable.
val post_minor_reachable_refl_from_root
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: seq U64.t) (rr: U64.t) (w: U64.t)
  : Lemma
    (requires (
      let prom = cheney_promote minor major fp roots in
      let res = cheney_collect_spec minor major fp roots in
      Seq.mem rr (rewrite_roots roots prom.fwd_map) /\
      HeapGraph.resolve_field res.mc_major rr == w /\
      mem_graph_vertex_at (HeapModel.create_graph res.mc_major) w))
    (ensures post_minor_reachable minor major fp roots w)

/// Bridge the implementation-facing ref-table coverage predicate to the
/// scan-root coverage predicate used by the combined-graph reachability bridge.
val remembered_roots_in_roots_from_slots
  (major: heap) (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n)
    (ensures RBridge.remembered_roots_in_roots major roots)

/// A major-to-major field is not affected by `update_major_pointers`: existing
/// major object addresses are outside the nursery range.
val update_preserves_major_target_field
  (major: heap) (fwd: forwarding_map) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem src (objects zero_addr major) /\
      Seq.mem dst (objects zero_addr major) /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      is_blue src major = false /\
      is_no_scan src major = false /\
      read_word major (U64.uint_to_t (U64.v src + j * 8)) == dst)
    (ensures
      read_word (update_major_pointers major fwd)
        (U64.uint_to_t (U64.v src + j * 8)) == dst)

/// Turn a concrete field value in a heap object into a graph edge in
/// `HeapModel.create_graph`.
val heap_field_points_to_graph_edge
  (g: heap) (src: obj_addr) (dst: U64.t) (j: nat)
  : Lemma
    (requires
      well_formed_heap g /\
      Seq.mem src (objects zero_addr g) /\
      ~(is_no_scan src g) /\
      j < U64.v (wosize_of_object src g) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      read_word g (U64.uint_to_t (U64.v src + j * 8)) == dst /\
      HeapGraph.is_pointer_field dst)
    (ensures mem_graph_edge (HeapModel.create_graph g) src
               (HeapGraph.resolve_field g dst))

val heap_graph_edge_to_pointer_field
  (g: heap) (src dst: obj_addr)
  : Lemma
    (requires mem_graph_edge (HeapModel.create_graph g) src dst /\
              well_formed_heap g)
    (ensures
      Seq.mem src (objects zero_addr g) /\
      HeapGraph.object_fits_in_heap src g /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      (exists (j: U64.t{U64.v j >= 1}).
        U64.v j <= U64.v (wosize_of_object src g) /\
        HeapGraph.is_pointer_field (HeapGraph.get_field g src j) /\
        HeapGraph.resolve_field g (HeapGraph.get_field g src j) == dst))

val heap_graph_edge_to_field_read
  (g: heap) (src dst: obj_addr)
  : Lemma
    (requires mem_graph_edge (HeapModel.create_graph g) src dst /\
              well_formed_heap g)
    (ensures
      Seq.mem src (objects zero_addr g) /\
      is_no_scan src g = false /\
      HeapGraph.is_pointer_field dst /\
      (exists (j: nat).
        j < U64.v (wosize_of_object src g) /\
        U64.v src + j * 8 + 8 <= heap_size /\
        (U64.v src + j * 8) % 8 == 0 /\
        HeapGraph.is_pointer_field
          (read_word g (U64.uint_to_t (U64.v src + j * 8))) /\
        HeapGraph.resolve_field g
          (read_word g (U64.uint_to_t (U64.v src + j * 8))) == dst))

/// Internal helper exposed to later forwarding proof slices.
val mem_graph_vertex_at_is_obj_addr
  (g: heap) (w: U64.t)
  : Lemma
    (requires mem_graph_vertex_at (HeapModel.create_graph g) w)
    (ensures is_val_addr w /\ Seq.mem (w <: obj_addr) (objects zero_addr g))

/// A graph vertex resolves to itself: vertices are enumerated objects, and
/// well-formedness forbids an enumerated object from carrying an infix header.
val vertex_resolves_to_itself (h: heap) (w: U64.t)
  : Lemma
    (requires well_formed_heap h /\
              mem_graph_vertex_at (HeapModel.create_graph h) w)
    (ensures HeapGraph.resolve_field h w == w)

/// Cheney promotion preserves the header-derived facts and body field of a
/// pre-existing non-blue major object.
val cheney_promote_preserves_old_major_field_context
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Seq.mem src (objects zero_addr major) /\
      is_blue src major = false /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      Seq.mem src (objects zero_addr prom.major_final) /\
      is_blue src prom.major_final = false /\
      is_no_scan src prom.major_final == is_no_scan src major /\
      wosize_of_object src prom.major_final == wosize_of_object src major /\
      read_word prom.major_final (U64.uint_to_t (U64.v src + j * 8)) ==
      read_word major (U64.uint_to_t (U64.v src + j * 8))))


/// Internal helper exposed to later forwarding proof slices.
val header_eq_preserves_wosize_no_scan
  (g1 g2: heap) (src: obj_addr)
  : Lemma
    (requires read_word g1 (hd_address src) == read_word g2 (hd_address src))
    (ensures wosize_of_object src g1 == wosize_of_object src g2 /\
             is_no_scan src g1 == is_no_scan src g2)

/// ---------------------------------------------------------------------------
/// Resolution of forwarding images
/// ---------------------------------------------------------------------------

/// The forwarding map is keyed by the address *as stored*, so an interior
/// nursery pointer has its own entry, distinct from its enclosing closure's.
/// This lemma is the bridge that makes that entry usable: whatever the source
/// address is, its image resolves --- in the post-collection major heap --- to
/// the image of the source's *resolution* in the nursery.
///
/// For a non-interior source both sides are the plain image.  For an interior
/// source the image is an interior major pointer whose copied infix header
/// still encodes the offset back to the promoted closure
/// (`GC.Gen.CheneyPreservation.Forwarding.fwd_infix_targets_wf`), and
/// `update_major_pointers` cannot disturb that header because an infix header
/// word is congruent to 1 mod 8 and so never looks like a minor pointer.
///
/// Stated over `cheney_collect_spec`'s final heap, this is exactly what turns a
/// rewritten interior field into the combined-graph edge
/// `MinorV (resolve_minor minor x)`.
val fwd_image_resolves
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) (x: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (cheney_promote minor major fp roots).fwd_map x <> 0UL)
    (ensures (
      let prom = cheney_promote minor major fp roots in
      let updated = (cheney_collect_spec minor major fp roots).mc_major in
      let rv = resolve_minor minor x in
      Seq.mem rv (minor_objects minor) /\
      is_minor_addr rv /\
      minor_wosize minor rv > 0 /\
      prom.fwd_map rv <> 0UL /\
      is_val_addr (prom.fwd_map rv) /\
      Seq.mem ((prom.fwd_map rv) <: obj_addr) (objects zero_addr prom.major_final) /\
      is_infix (prom.fwd_map rv) prom.major_final = false /\
      is_val_addr (prom.fwd_map x) /\
      HeapGraph.is_pointer_field (prom.fwd_map x) /\
      (let t : obj_addr = prom.fwd_map x in
       resolve_object t prom.major_final == prom.fwd_map rv /\
       resolve_object t updated == prom.fwd_map rv /\
       // an interior nursery pointer is promoted to an interior pointer into
       // the promoted copy of its enclosing closure
       (is_infix_in_minor minor x ==> is_infix t updated) /\
       (~(is_infix_in_minor minor x) ==> t == prom.fwd_map rv))))

/// ---------------------------------------------------------------------------
/// Interior nursery targets are forwarded
/// ---------------------------------------------------------------------------

/// Generalisation of `field_zero_target_in_roots` to an arbitrary field index:
/// the write barrier records *every* field of a scannable non-blue major object
/// that holds a nursery pointer, and the recorded target is the word as stored,
/// interior or not.
val major_field_target_in_roots
  (major: heap) (roots slots: seq U64.t) (n: nat) (src: obj_addr) (j: nat)
  : Lemma
    (requires
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Seq.mem src (objects zero_addr major) /\
      is_blue src major = false /\
      is_no_scan src major = false /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      is_minor_pointer (to_minor_offset
        (read_word major (U64.uint_to_t (U64.v src + j * 8)))))
    (ensures
      Seq.mem (to_minor_offset (read_word major (U64.uint_to_t (U64.v src + j * 8))))
        roots)

/// An interior nursery pointer stored in a *nursery* field has its own entry in
/// the forwarding map.  This is `fwd_covers_infix_fields`, which the scan loop
/// establishes for every queued object.
val minor_field_infix_target_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: U64.t) (j: nat)
  : Lemma
    (requires
      CheneyBFS.cheney_no_oom minor major fp roots /\
      Seq.mem src (minor_objects minor) /\
      (cheney_promote minor major fp roots).fwd_map src <> 0UL /\
      j < minor_wosize minor src /\
      is_infix_in_minor minor (to_minor_offset (minor_read_field minor src j)))
    (ensures
      (cheney_promote minor major fp roots).fwd_map
        (to_minor_offset (minor_read_field minor src j)) <> 0UL)

/// The same for an interior nursery pointer stored in a *major* field: the
/// remembered set files it as a Cheney root, and `fwd_covers_infix_roots`
/// forwards every interior root.
val major_field_infix_target_forwarded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots slots: seq U64.t) (n: nat)
  (src: obj_addr) (j: nat)
  : Lemma
    (requires
      CheneyBFS.cheney_no_oom minor major fp roots /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Seq.mem src (objects zero_addr major) /\
      is_blue src major = false /\
      is_no_scan src major = false /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      is_infix_in_minor minor (to_minor_offset
        (read_word major (U64.uint_to_t (U64.v src + j * 8)))))
    (ensures
      (cheney_promote minor major fp roots).fwd_map
        (to_minor_offset (read_word major (U64.uint_to_t (U64.v src + j * 8)))) <> 0UL)
