/// ---------------------------------------------------------------------------
/// GC.Gen.MarkPhase.Minor - a minor collection in the middle of marking
/// ---------------------------------------------------------------------------
///
/// While marking, the minor collection runs at `Marking` (its promoted copies
/// are black) with `free_stw` (marking frees nothing), so the generic theorem
/// (`GC.Gen.CheneyGeneric.cheney_collect_with_preserves_shape`) gives its
/// shape.  What it must also keep is the marking invariant
/// (`GC.Spec.MarkPhase.marking_inv`) with what is referenced from outside the
/// major heap: before the collection, the program's roots and the nursery's
/// major pointers (`outside_refs_of`); after it, with the nursery empty, the
/// rewritten roots (`root_refs`).
///
/// It is an instance of `marking_inv_change`, at the scan position it keeps:
///   * every non-free block stays, with its header (`old_block`), and its
///     pointer fields: the pointer update rewrites only nursery pointers,
///     which never look like major pointers (`old_pointer_field`), and their
///     targets keep their resolution -- so no edge between grey or white
///     blocks is cut (field by field: the partly scanned object keeps its
///     unscanned edges), and no colour changes;
///   * every other non-free block afterwards is a promoted copy, black
///     (`new_block_black`): so nothing new is white;
///   * a scanned edge's white target (out of a black object, or the grey
///     partly scanned one) is one the marker would already reach.
///     That is the trick of `GC.Spec.MarkPhase.unreached g sp`: the invariant
///     makes `g` well formed for "free = blue, or white and not reached"; the
///     generic theorem keeps well-formedness for *any* admissible definition
///     of free whose allocations are not free (black copies are not), and
///     the pointer update at `free_stw` agrees with the one at `unreached g sp`
///     on every block non-free for the latter; so the heap after is well
///     formed for `unreached g sp`, which says exactly that
///     (`unreached_wf_after`).  This covers the promoted copies' fields (old
///     targets the nursery points at, or copies) and the remembered slots
///     (rewritten to copies) without looking at them;
///   * a rewritten root is the old one (an outside reference before) or a forwarded copy
///     (black).

module GC.Gen.MarkPhase.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module Ph = GC.Spec.Phase
module Cheney = GC.Gen.Cheney
module Promote = GC.Gen.Promote
module MP = GC.Spec.MarkPhase
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator

/// What the nursery holds in the major heap `g`: a major pointer in the scan
/// window of a nursery object names `w` (resolved in `g`: the field may be an
/// interior pointer into a major closure, `minor_major_fields_not_free`).
let nursery_refs (minor: minor_state) (g: heap) (w: obj_addr) : prop =
  exists (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) /\
    resolve_object ((minor_read_field minor obj j) <: obj_addr) g == w

/// The nursery's major pointers name the same blocks in `g'` as in `g` when
/// each of them resolves the same way in both.
val nursery_refs_transfer (minor: minor_state) (g g': heap)
  : Lemma (requires forall (obj: U64.t) (j: nat).
                      Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
                      is_pointer_field (minor_read_field minor obj j) ==>
                      resolve_object ((minor_read_field minor obj j) <: obj_addr) g' ==
                      resolve_object ((minor_read_field minor obj j) <: obj_addr) g)
          (ensures forall (w: obj_addr). nursery_refs minor g' w <==> nursery_refs minor g w)

/// ... which a change keeps that keeps the non-free blocks, their headers
/// and the blocks of the non-free closures (`SPI.storable_transfer`).
val nursery_refs_transfer_storable (free free': free_def) (minor: minor_state) (g g': heap)
  : Lemma (requires GenInv.minor_major_fields_not_free free minor g /\
                    no_infix_block g /\ no_infix_block g' /\ free_def_ok free' /\
                    SPI.heads_kept free g g' /\
                    (forall (y: obj_addr). in_use free g y ==> in_use free' g' y))
          (ensures forall (w: obj_addr). nursery_refs minor g' w <==> nursery_refs minor g w)

/// ... or that may recolour them (`SPI.storable_transfer_blocks`).
val nursery_refs_transfer_blocks (free free': free_def) (minor: minor_state) (g g': heap)
  : Lemma (requires GenInv.minor_major_fields_not_free free minor g /\
                    no_infix_block g /\ no_infix_block g' /\
                    (forall (y: obj_addr). in_use free g y ==>
                       in_use free' g' y /\ SPI.same_block g g' (hd_address y)))
          (ensures forall (w: obj_addr). nursery_refs minor g' w <==> nursery_refs minor g w)

/// ... and so does recolouring one object.
val nursery_refs_colour (minor: minor_state) (x: obj_addr) (g: heap) (c: color)
  : Lemma (forall (w: obj_addr). nursery_refs minor (set_object_color x g c) w <==> nursery_refs minor g w)

/// ... and so does a program write: into the body of a block on the walk,
/// not blue and not a closure, so every non-free block keeps its header, and
/// every non-free closure its block.
val write_keeps_nursery (free: free_def) (minor: minor_state) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires free_def_ok free /\ no_infix_block g /\
                    GenInv.minor_major_fields_not_free free minor g /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ ~(is_closure x g) /\
                    SPM.in_body g x a)
          (ensures GenInv.minor_major_fields_not_free free minor (write_word g a v) /\
                   (forall (w: obj_addr). nursery_refs minor (write_word g a v) w <==> nursery_refs minor g w))

/// Every block the nursery names is not free, when the cross-generation
/// condition holds.
val nursery_refs_in_use (free: free_def) (minor: minor_state) (g: heap) (w: obj_addr)
  : Lemma (requires GenInv.minor_major_fields_not_free free minor g /\ nursery_refs minor g w)
          (ensures in_use free g w)

/// What the program's roots hold in the major heap: a root that is a major
/// pointer points (resolved) at `w`.
let root_refs (g: heap) (roots: seq U64.t) (w: obj_addr) : prop =
  exists (r: U64.t). Seq.mem r roots /\ is_pointer r /\ resolve_object (r <: obj_addr) g == w

/// What is referenced from outside the major heap, with a nursery: the roots and
/// the nursery's major pointers.
let outside_refs_of (minor: minor_state) (g: heap) (roots: seq U64.t) (w: obj_addr) : prop =
  root_refs g roots w \/ nursery_refs minor g w

/// The reset nursery holds nothing.
val nursery_refs_reset (minor: minor_state) (g: heap) (w: obj_addr)
  : Lemma (~(nursery_refs (minor_reset minor) g w))

/// The collection at `Marking`.
let collect_marking (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot Promote.minor_collect_result
  = Cheney.cheney_collect_spec_with Ph.Marking free_stw minor g fp roots

/// **A minor collection while marking keeps the marking invariant**, at the
/// same scan position, with the rewritten roots as the outside references
/// (the nursery is empty afterwards), and its shape.
val minor_keeps_marking_inv (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (sp: MP.scan_pos)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\
                    MCFH.roots_valid_for_minor_collection minor g roots /\
                    MP.marking_inv g (outside_refs_of minor g roots) sp)
          (ensures (let res = collect_marking minor g fp roots in
                    res.Promote.mc_minor == minor_reset minor /\
                    GenInv.collection_shape_with Ph.Marking free_stw
                      res.Promote.mc_minor res.Promote.mc_major res.Promote.mc_fp /\
                    MP.marking_inv res.Promote.mc_major (root_refs res.Promote.mc_major res.Promote.mc_roots) sp))

/// **... and with more outside references**: a fixed set of addresses
/// `extra` that are outside references before (besides the roots and the
/// nursery's fields) still are after (besides the rewritten roots).  The
/// completeness of the cycle uses it with `extra` the objects reachable when
/// the cycle started (`GC.Gen.Run.Invariant`).
val minor_keeps_marking_inv_with (extra: obj_addr -> prop)
    (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (sp: MP.scan_pos)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\
                    MCFH.roots_valid_for_minor_collection minor g roots /\
                    MP.marking_inv g (fun w -> outside_refs_of minor g roots w \/ extra w) sp)
          (ensures (let res = collect_marking minor g fp roots in
                    MP.marking_inv res.Promote.mc_major
                      (fun w -> root_refs res.Promote.mc_major res.Promote.mc_roots w \/ extra w) sp))

/// **The collection keeps the grey objects**: a block of the heap after it
/// is a grey object exactly when it was one before.  An old non-free block
/// keeps its header, and a block that was not one is a promoted copy, black.
/// The mark stack (`GC.Gen.MarkState`) is a cache of the grey objects, so
/// this is what keeps it across a minor collection while marking.
val minor_keeps_greys (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (y: obj_addr)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp)
          (ensures (let g' = (collect_marking minor g fp roots).Promote.mc_major in
                    (Seq.mem y (objects zero_addr g') /\ is_gray y g') <==>
                    (Seq.mem y (objects zero_addr g) /\ is_gray y g)))

/// **The collection keeps every block that was not free**, on the walk and
/// with its header (so its colour).
val minor_keeps_block (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (y: obj_addr)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\ in_use free_stw g y)
          (ensures (let g' = (collect_marking minor g fp roots).Promote.mc_major in
                    Seq.mem y (objects zero_addr g') /\
                    read_word g' (hd_address y) == read_word g (hd_address y)))

/// **The collection keeps well-formedness for any admissible definition of
/// free** whose allocations while marking are not free (a promoted copy is
/// black), given that the nursery's major pointers are not free for it.
/// (`GC.Gen.MarkPhase.Completeness` uses it for the cycle's account.)
val minor_keeps_wf_with (un: free_def) (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\ free_def_ok un /\
                    Promote.allocations_not_free Ph.Marking un /\
                    well_formed_heap_with un g /\ GenInv.minor_major_fields_not_free un minor g)
          (ensures well_formed_heap_with un (collect_marking minor g fp roots).Promote.mc_major)

/// **Every block the collection makes non-free is a promoted copy, black.**
val minor_new_block_black (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (y: obj_addr)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\
                    in_use free_stw (collect_marking minor g fp roots).Promote.mc_major y /\
                    ~(in_use free_stw g y))
          (ensures is_black y (collect_marking minor g fp roots).Promote.mc_major)

/// **... and its fields that point into the major heap** (a nursery pointer
/// never looks like one); the other pointer fields are rewritten to the
/// promoted copies (the forwarding map, `GC.Gen.Promote`).
val minor_keeps_major_field (minor: minor_state) (g: heap) (fp: U64.t) (roots: seq U64.t) (y: obj_addr) (j: nat)
  : Lemma (requires GenInv.collection_shape_with Ph.Marking free_stw minor g fp /\ in_use free_stw g y /\
                    j < U64.v (wosize_of_object y g) /\ U64.v y + j * 8 + 8 <= heap_size /\
                    is_pointer (read_word g (U64.uint_to_t (U64.v y + j * 8))))
          (ensures (let g' = (collect_marking minor g fp roots).Promote.mc_major in
                    read_word g' (U64.uint_to_t (U64.v y + j * 8)) ==
                    read_word g (U64.uint_to_t (U64.v y + j * 8))))
