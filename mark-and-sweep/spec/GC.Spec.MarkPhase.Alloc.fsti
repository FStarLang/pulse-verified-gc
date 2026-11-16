/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPhase.Alloc - allocation while marking, and fresh objects
/// ---------------------------------------------------------------------------
///
/// While marking, a new major object is black (`GC.Spec.Phase.allocation_color
/// Marking`, 4.14's `Phase_mark`): the marker never needs to scan it.  Its
/// fields are what the free block held until the runtime initialises them, so
/// they must not count against the marking invariant until then -- the
/// analogue of the sweep's `fresh_ok` (`GC.Spec.SweepPhase.Mutator`):
///
///   * **Fresh** (`marking_fresh g outside_refs sp obj`): the invariant with
///     `obj` black and its fields exempt: well-formedness counts `obj` as free
///     (`free_or_new obj`, so nothing points at it and its fields are
///     unconstrained) and the weak tri-colour clause skips it as a source
///     (`fresh_tri_color`).  Being black, `obj` lies on no path the marker
///     follows, so what the marker will reach is unaffected by its fields;
///     and it is not the partly scanned object, which is grey.
///   * **Allocation** (`marking_alloc`): first-fit at `Marking` from an
///     ascending free list keeps the invariant with the new object fresh; it
///     frees nothing (every non-free block keeps its header and fields,
///     `keeps_blocks`), keeps the list ascending, and the new object was not
///     a non-free block before.
///   * **Initialising** (`marking_fresh_write`): writes into the fresh
///     object's body keep it fresh.
///   * **Closing** (`marking_fresh_close`): once every field is storable and
///     its target is not white, or an outside reference, or one the marker will reach
///     (`fields_ok`), the invariant holds.  A field the program initialises
///     with a value it holds meets this.
///
/// The frame lemmas (`keeps_blocks_*`) are about any change that keeps every
/// non-free block (for any admissible definition of free): its edges (field
/// by field), the resolution of what it stores, and what the marker will
/// reach.

module GC.Spec.MarkPhase.Alloc

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.MarkPhase

module U64 = FStar.UInt64
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module MM = GC.Spec.MarkPhase.Mutator
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module FLA = GC.Spec.FreeList.Ascending
module Ph = GC.Spec.Phase

/// ---------------------------------------------------------------------------
/// Changes that keep every non-free block
/// ---------------------------------------------------------------------------

/// `g'` keeps every block non-free under `free` in `g`: on the walk, with its
/// header and its fields.
let keeps_blocks (free: free_def) (g g': heap) : prop =
  forall (y: obj_addr). in_use free g y ==>
    Seq.mem y (objects zero_addr g') /\
    read_word g' (hd_address y) == read_word g (hd_address y) /\
    SPI.same_block g g' (hd_address y)

/// What a non-free block stores keeps its resolution.
val keeps_blocks_resolve (free: free_def) (g g': heap) (w: U64.t)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ keeps_blocks free g g' /\
                    is_pointer w /\ SPI.storable free g w)
          (ensures resolve_object (w <: obj_addr) g' == resolve_object (w <: obj_addr) g)

/// A non-free block keeps its edges ...
val keeps_blocks_edges (free: free_def) (g g': heap) (u t: obj_addr)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ blocks_fit g' /\
                    keeps_blocks free g g' /\ in_use free g u)
          (ensures field_edge g' u t <==> field_edge g u t)

/// ... field by field.
val keeps_blocks_field_edge_at (free: free_def) (g g': heap) (u: obj_addr) (k: nat) (t: obj_addr)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ blocks_fit g' /\
                    keeps_blocks free g g' /\ in_use free g u)
          (ensures field_edge_at g' u k t <==> field_edge_at g u k t)

/// When every grey or white block is non-free, the marker will still reach
/// what it would.
val keeps_blocks_reach (free: free_def) (g g': heap) (sp: scan_pos) (w: obj_addr)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ blocks_fit g' /\
                    keeps_blocks free g g' /\
                    (forall (y: obj_addr). grey_or_white g y ==> in_use free g y) /\
                    marker_will_reach g sp w)
          (ensures marker_will_reach g' sp w)

/// ---------------------------------------------------------------------------
/// Fresh objects
/// ---------------------------------------------------------------------------

/// What counts as free while the new object `obj` is uninitialised: blue
/// blocks, and `obj`.
let free_or_new (obj: obj_addr) : free_def = fun g x -> is_blue x g || x = obj

val free_or_new_ok (obj: obj_addr) : Lemma (free_def_ok (free_or_new obj))

/// The weak tri-colour clause for every scanned edge but `obj`'s.
let fresh_tri_color (g: heap) (sp: scan_pos) (obj: obj_addr) : prop =
  forall (b w: obj_addr).
    scanned_edge g sp b w /\ b <> obj /\ is_white w g ==> marker_will_reach g sp w

/// **The marking invariant with `obj` fresh**: black, a block, its fields
/// not yet bound by well-formedness or the weak tri-colour clause.
let marking_fresh (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (obj: obj_addr) : prop =
  well_formed_heap_with (free_or_new obj) g /\
  Seq.mem obj (objects zero_addr g) /\ is_black obj g /\ scan_pos_ok g sp /\
  fresh_tri_color g sp obj /\ outside_refs_reached g sp outside_refs

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// After an allocation while marking, the non-free blocks with the new object
/// counted free are exactly the non-free blocks before (so, for instance, a
/// grey object after was a grey object before).
val alloc_in_use (g: heap) (fp: U64.t) (wz: nat) (tag: SPM.tag_t) (obj x: obj_addr)
  : Lemma (requires well_formed_heap g /\ FLA.fl_ascending g fp /\ wz >= 1 /\
                    (AC.alloc_phase g fp Ph.Marking wz tag).SA.obj_out == obj)
          (ensures (let r = AC.alloc_phase g fp Ph.Marking wz tag in
                    in_use (free_or_new obj) r.SA.heap_out x == in_use free_stw g x))

/// **Allocation while marking**: first-fit at `Marking` from an ascending
/// free list.  If nothing fits, nothing changes; otherwise the new object is
/// black, of the requested size and tag, was not a non-free block before,
/// and is fresh; every non-free block is kept (allocation frees nothing),
/// and the list stays ascending.
val marking_alloc (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (fp: U64.t) (wz: nat) (tag: SPM.tag_t)
  : Lemma (requires marking_inv g outside_refs sp /\ FLA.fl_ascending g fp /\ wz >= 1 /\ tag <> infix_tag)
          (ensures (let r = AC.alloc_phase g fp Ph.Marking wz tag in
                    (r.SA.obj_out == 0UL ==> r.SA.heap_out == g /\ r.SA.fp_out == fp) /\
                    (r.SA.obj_out <> 0UL ==>
                       GC.Spec.FusedSweep.is_obj r.SA.obj_out /\
                       (let obj : obj_addr = r.SA.obj_out in
                        ~(Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g)) /\
                        U64.v (wosize_of_object obj r.SA.heap_out) == wz /\
                        tag_of_object obj r.SA.heap_out == tag /\
                        keeps_blocks free_stw g r.SA.heap_out /\
                        FLA.fl_ascending r.SA.heap_out r.SA.fp_out /\
                        marking_fresh r.SA.heap_out outside_refs sp obj))))

/// ---------------------------------------------------------------------------
/// Initialising a fresh object
/// ---------------------------------------------------------------------------

/// A write into the body of a fresh object keeps it fresh.
val marking_fresh_write (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (obj: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires marking_fresh g outside_refs sp obj /\ SPM.in_body g obj a)
          (ensures marking_fresh (write_word g a v) outside_refs sp obj /\
                   SPI.same_heads g (write_word g a v))

/// Every field of `obj`, if it is scannable, points at nothing white unless
/// that is an outside reference or one the marker will reach.
let fields_ok (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (obj: obj_addr) : prop =
  not (is_no_scan obj g) ==>
  (forall (i: nat). i < U64.v (wosize_of_object obj g) /\ U64.v obj + i * 8 + 8 <= heap_size ==>
     MM.target_ok g outside_refs sp (SPM.field_val g obj i))

/// **Closing a fresh object**: once its fields are storable and fine for a
/// black object to point at, the invariant holds.
val marking_fresh_close (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (obj: obj_addr)
  : Lemma (requires marking_fresh g outside_refs sp obj /\ SPM.fields_storable free_stw g obj /\
                    fields_ok g outside_refs sp obj)
          (ensures marking_inv g outside_refs sp)
