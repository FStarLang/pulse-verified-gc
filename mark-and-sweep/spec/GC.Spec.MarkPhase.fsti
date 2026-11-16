/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPhase - incremental marking: the step and the invariant
/// ---------------------------------------------------------------------------
///
/// Incremental marking (incremental-mark-plan.md, section 3) runs the mark
/// step a few objects at a time, with the program running in between.  The
/// mark stack is an implementation cache: the spec state is the heap's
/// colours, and the *scan position* (`scan_pos`): the object a slice stopped
/// in the middle of, if any, and its next field.
///
///   * **The partly scanned object** (`sp.cur`, 0 for none): a slice that
///     runs out of budget inside an object leaves it grey with its fields
///     before `sp.fld` scanned (fields are numbered from 1, as the slice and
///     `GC.Spec.HeapGraph.get_field` number them).  The invariant treats it
///     field by field: its scanned fields like a black object's, the others
///     like a grey object's.
///
///   * **Edges** (`field_edge_at g x k y`: field `k` of `x` points, resolved
///     through infix headers, at `y`; `field_edge g x y`: some field does).
///     An edge is *scanned* (`scanned_edge`) when the marker is done with it
///     -- it leaves a black object, or a scanned field of the partly scanned
///     object -- and *unscanned* (`unscanned_edge`) when the marker will still
///     process it once it gets to its source -- any other field.
///
///   * **What the marker will reach** (`marker_will_reach g sp w`): `w` is
///     reachable from a grey object along unscanned edges, through grey or
///     white blocks.  The marker follows each such path.  A path through a
///     black object, or through a scanned field of the partly scanned object,
///     does not count: the marker never looks at it again.
///
///   * **The invariant** (`marking_inv g outside_refs sp`), where
///     `outside_refs w` says that something outside the major heap points at
///     `w` (the program's roots, and later the nursery's fields: the
///     generational layer chooses):
///       1. every white object a scanned edge points at is one the marker
///          will reach (the weak tri-colour invariant, `weak_tri_color`);
///       2. every white object referenced from outside is one the marker will
///          reach (`outside_refs_reached`);
///       3. the heap is well formed with free meaning blue: marking frees
///          nothing; and the partly scanned object, if any, is a grey block
///          (`scan_pos_ok`).
///     With no partly scanned object (`scan_none`) the edges are today's
///     black and non-black edges (`scan_none_edges`).
///
/// Start: after the roots are darkened, with no black object, it holds
/// (`marking_inv_start`).  Step: the stop-the-world mark step at any grey
/// object keeps it (`marking_inv_step`); so do the slice's moves, one field
/// at a time (`marking_inv_begin`, `marking_inv_advance`,
/// `marking_inv_blacken`; `GC.Spec.MarkPhase.Slice`).  End: with no grey
/// object left, nothing is one the marker will reach, so clause 1 is the
/// strong tri-colour invariant and clause 2 says every outside reference is
/// marked -- the heap is `marked`, where the sweep starts (`marking_done`,
/// `marking_done_sweep_start`).
///
/// The program's events are changes to the heap that keep grey objects grey
/// and every grey or white block one, add no white object, and grey the
/// target of every unscanned edge between non-black blocks they cut
/// (`marking_inv_change`); greying a white object (the write barrier's
/// darkening) is one (`marking_inv_grey`).  A write into a scanned field of
/// the partly scanned object is a write into a "black" field: the barrier
/// greys the old value and the new one must be one the marker will reach
/// (or not white), as for a black object -- there is no restart.

module GC.Spec.MarkPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within

module U64 = FStar.UInt64
module HG = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module FSE = GC.Spec.FusedSweep.End
module FSI = GC.Spec.FusedSweep.Inv
module FLA = GC.Spec.FreeList.Ascending
module SPI = GC.Spec.SweepPhase.Intrinsic

/// ---------------------------------------------------------------------------
/// Edges, field by field
/// ---------------------------------------------------------------------------

/// The edges of the heap graph: `y` is the object a pointer field of the
/// scannable object `x` points at, resolved through infix headers -- read
/// off the heap directly, so a colour change visibly keeps it.  Every edge of
/// `GC.Spec.HeapModel.create_graph` is one (`Mark.edge_implies_points_to`).
let field_edge (g: heap) (x y: obj_addr) : prop =
  ~(is_no_scan x g) /\ (exists (c: obj_addr). points_to g x c /\ resolve_object c g == y)

/// The field `k` of the scannable object `x` points, resolved through infix
/// headers, at `y`.  Fields are numbered from 1 (`HG.get_field`, as the mark
/// slice numbers them: field `k` is the word `x + (k - 1) * 8`).
let field_edge_at (g: heap) (x: obj_addr) (k: nat) (y: obj_addr) : prop =
  ~(is_no_scan x g) /\ 1 <= k /\ k <= U64.v (wosize_of_object x g) /\
  (let v = HG.get_field g x (U64.uint_to_t k) in is_pointer v /\ resolve_object v g == y)

/// The field `k` of a block whose fields fit is the word `x + (k - 1) * 8`.
val get_field_word (g: heap) (x: obj_addr) (k: nat)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\
                    1 <= k /\ k <= U64.v (wosize_of_object x g))
          (ensures U64.v x + (k - 1) * 8 + 8 <= heap_size /\
                   HG.get_field g x (U64.uint_to_t k) ==
                   read_word g (U64.uint_to_t (U64.v x + (k - 1) * 8)))

/// An edge is an edge of some field, for a block of a heap whose blocks fit.
val field_edge_fields (g: heap) (x y: obj_addr)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g))
          (ensures field_edge g x y <==> (exists (k: nat). field_edge_at g x k y))

/// A field's edge depends on the block's header (whether it is scannable,
/// its size), the field's word, and where that word resolves.
val field_edge_at_kept (g g': heap) (x: obj_addr) (k: nat) (y: obj_addr)
  : Lemma (requires is_no_scan x g' == is_no_scan x g /\
                    wosize_of_object x g' == wosize_of_object x g /\
                    (1 <= k /\ k <= U64.v (wosize_of_object x g) ==>
                       (let v = HG.get_field g x (U64.uint_to_t k) in
                        HG.get_field g' x (U64.uint_to_t k) == v /\
                        (is_pointer v ==> resolve_object v g' == resolve_object v g))))
          (ensures field_edge_at g' x k y <==> field_edge_at g x k y)

/// ---------------------------------------------------------------------------
/// The scan position
/// ---------------------------------------------------------------------------

/// The partly scanned object (`cur`, 0 for none) and its next field (`fld`):
/// its fields before `fld` are scanned.
type scan_pos = { cur: U64.t; fld: nat }

/// No partly scanned object.
let scan_none : scan_pos = { cur = 0UL; fld = 1 }

/// The partly scanned object, if any, is a grey block.
let scan_pos_ok (g: heap) (sp: scan_pos) : prop =
  sp.cur <> 0UL ==>
  (is_val_addr sp.cur /\ Seq.mem (sp.cur <: obj_addr) (objects zero_addr g) /\ is_gray sp.cur g)

/// **A scanned edge**: the marker is done with it -- an edge of a black
/// object, or of a scanned field of the partly scanned object.
let scanned_edge (g: heap) (sp: scan_pos) (x y: obj_addr) : prop =
  (Seq.mem x (objects zero_addr g) /\ is_black x g /\ field_edge g x y) \/
  (x == sp.cur /\ (exists (k: nat). k < sp.fld /\ field_edge_at g x k y))

/// **An unscanned edge**: the marker will still process it once it gets to
/// its source -- an edge of any object but the partly scanned one, or of an
/// unscanned field of it.  (For a block whose fields fit, that is: some field
/// `k` points at `y`, and `x` is not the partly scanned object or `k` is not
/// before its next field -- `unscanned_edge_fields`.)
let unscanned_edge (g: heap) (sp: scan_pos) (x y: obj_addr) : prop =
  field_edge g x y /\ (x <> sp.cur \/ (exists (k: nat). sp.fld <= k /\ field_edge_at g x k y))

val unscanned_edge_fields (g: heap) (sp: scan_pos) (x y: obj_addr)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g))
          (ensures unscanned_edge g sp x y <==>
                   (exists (k: nat). field_edge_at g x k y /\ (x <> sp.cur \/ sp.fld <= k)))

/// **With no partly scanned object** the scanned edges are the black
/// objects' edges and every edge is unscanned: the definitions are those of
/// stop-the-world marking.
val scan_none_edges (g: heap) (x y: obj_addr)
  : Lemma ((scanned_edge g scan_none x y <==>
              (Seq.mem x (objects zero_addr g) /\ is_black x g /\ field_edge g x y)) /\
           (unscanned_edge g scan_none x y <==> field_edge g x y))

/// A scanned edge is an edge.
val scanned_edge_field_edge (g: heap) (sp: scan_pos) (x y: obj_addr)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\ scanned_edge g sp x y)
          (ensures field_edge g x y)

/// ---------------------------------------------------------------------------
/// What the marker will reach
/// ---------------------------------------------------------------------------

/// A block the marker has not finished: grey or white (not black, not free).
let grey_or_white (g: heap) (v: obj_addr) : prop =
  Seq.mem v (objects zero_addr g) /\ (is_gray v g \/ is_white v g)

/// `w` is reachable from a grey object along unscanned edges, through grey
/// or white blocks.
let marker_will_reach (g: heap) (sp: scan_pos) (w: obj_addr) : prop =
  exists (x: obj_addr). is_gray x g /\ reach_within (unscanned_edge g sp) (grey_or_white g) x w

/// It is a grey or white block, from a grey block.
val marker_will_reach_elim (g: heap) (sp: scan_pos) (w: obj_addr)
  : Lemma (requires marker_will_reach g sp w)
          (ensures grey_or_white g w /\
                   (exists (x: obj_addr). Seq.mem x (objects zero_addr g) /\ is_gray x g))

/// With no partly scanned object, it is reachability from a grey object
/// along every edge, through grey or white blocks.
val marker_will_reach_none (g: heap) (w: obj_addr)
  : Lemma (marker_will_reach g scan_none w <==>
           (exists (x: obj_addr). is_gray x g /\ reach_within (field_edge g) (grey_or_white g) x w))

/// ---------------------------------------------------------------------------
/// The mark step at any grey object
/// ---------------------------------------------------------------------------

/// Blacken `x` and grey its white children (`Mark.push_children` resolves
/// each pointer field through infix headers and greys the target if white).
let mark_step_at (g: heap) (x: obj_addr) : GTot heap =
  let g' = makeBlack x g in
  if is_no_scan x g then g'
  else fst (Mark.push_children g' Seq.empty x 1UL (wosize_of_object x g))

/// The stop-the-world step is the step at the top of the stack.
val mark_step_heap (g: heap) (st: seq obj_addr)
  : Lemma (requires Seq.length st > 0)
          (ensures fst (Mark.mark_step g st) == mark_step_at g (Seq.head st))

/// The step only recolours: the walk, well-formedness and density are kept.
val mark_step_at_objects (g: heap) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures objects zero_addr (mark_step_at g x) == objects zero_addr g)

val mark_step_at_wf (g: heap) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures well_formed_heap (mark_step_at g x))

val mark_step_at_dense (g: heap) (x: obj_addr)
  : Lemma (requires heap_objects_dense g)
          (ensures heap_objects_dense (mark_step_at g x))

/// `x` is black afterwards; free blocks stay free and nothing else becomes free.
val mark_step_at_black (g: heap) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures is_black x (mark_step_at g x))

val mark_step_at_blue (g: heap) (x y: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ is_gray x g /\
                    Seq.mem y (objects zero_addr g))
          (ensures is_blue y (mark_step_at g x) <==> is_blue y g)

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// Clause 1, the weak tri-colour invariant: every white object a scanned
/// edge points at is one the marker will reach.
let weak_tri_color (g: heap) (sp: scan_pos) : prop =
  forall (b w: obj_addr). scanned_edge g sp b w /\ is_white w g ==> marker_will_reach g sp w

/// Clause 2: every white object referenced from outside the major heap is
/// one the marker will reach.
let outside_refs_reached (g: heap) (sp: scan_pos) (outside_refs: obj_addr -> prop) : prop =
  forall (w: obj_addr).
    outside_refs w /\ Seq.mem w (objects zero_addr g) /\ is_white w g ==> marker_will_reach g sp w

/// The marking invariant.  `outside_refs w`: something outside the major
/// heap points at `w` (resolved); `sp`: the scan position.
let marking_inv (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) : prop =
  well_formed_heap g /\ scan_pos_ok g sp /\ weak_tri_color g sp /\ outside_refs_reached g sp outside_refs

/// ---------------------------------------------------------------------------
/// Start, step, end
/// ---------------------------------------------------------------------------

/// **Start.**  No black object points at a white one (in particular, there is
/// no black object), and every outside reference has been darkened.
val marking_inv_start (g: heap) (outside_refs: obj_addr -> prop)
  : Lemma (requires well_formed_heap g /\ Mark.tri_color_invariant g /\
                    (forall (w: obj_addr). outside_refs w /\ Seq.mem w (objects zero_addr g) ==> ~(is_white w g)))
          (ensures marking_inv g outside_refs scan_none)

/// With no black object, no black object points at a white one.
val no_black_tri_color (g: heap)
  : Lemma (requires Mark.no_black_objects g)
          (ensures Mark.tri_color_invariant g)

/// **Step.**  The stop-the-world mark step at any grey object keeps the
/// invariant, with no partly scanned object.
val marking_inv_step (g: heap) (outside_refs: obj_addr -> prop) (x: obj_addr)
  : Lemma (requires marking_inv g outside_refs scan_none /\ Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures marking_inv (mark_step_at g x) outside_refs scan_none)

/// **End.**  With no grey object left, the heap is `marked` -- no grey, and no
/// black object points at a white one -- and no outside reference is white.
val marking_done (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos)
  : Lemma (requires marking_inv g outside_refs sp /\ Mark.noGreyObjects g)
          (ensures FSE.marked g /\
                   (forall (w: obj_addr). outside_refs w /\ Seq.mem w (objects zero_addr g) ==> ~(is_white w g)))

/// The hand-over to the sweep: from a heap where marking is done, with the
/// walk facts and the free list the allocator keeps, the sweep starts
/// (`SPI.sweep_inv_incremental_start`).
val marking_done_sweep_start (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (fp: U64.t)
  : Lemma (requires marking_inv g outside_refs sp /\ Mark.noGreyObjects g /\
                    FSI.sweep_g0 g /\ FLA.fl_ascending g fp)
          (ensures FSI.sweep_pre g fp /\ FSE.marked g /\
                   SPI.sweep_inv_incremental g fp GC.Spec.FusedSweep.sweep_start.cursor /\
                   SPI.pending_free_within g GC.Spec.FusedSweep.sweep_start.cursor (SPI.white_after_mark g))

/// ---------------------------------------------------------------------------
/// The partly scanned object
/// ---------------------------------------------------------------------------

/// **Starting to scan** a grey object, with none partly scanned: no field of
/// it is scanned yet, so nothing changes.
val marking_inv_begin (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (x: obj_addr)
  : Lemma (requires marking_inv g outside_refs sp /\ sp.cur == 0UL /\
                    Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures marking_inv g outside_refs ({ cur = x; fld = 1 }))

/// **Moving past a field** of the partly scanned object whose target, if
/// any, is not white (the slice has just darkened it): the edge becomes
/// scanned, and a path that used it now has a grey object there.
val marking_inv_advance (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (x: obj_addr)
  : Lemma (requires marking_inv g outside_refs sp /\ x == sp.cur /\
                    (forall (t: obj_addr). field_edge_at g x sp.fld t ==> ~(is_white t g)))
          (ensures marking_inv g outside_refs ({ sp with fld = sp.fld + 1 }))

/// Every field of `x` is scanned: it has none to scan, or it is the partly
/// scanned object and its next field is past the last one.
let all_scanned (g: heap) (sp: scan_pos) (x: obj_addr) : prop =
  is_no_scan x g \/ U64.v (wosize_of_object x g) < (if x = sp.cur then sp.fld else 1)

/// The position after blackening `x`: none partly scanned if it was `x`.
let blackened_pos (sp: scan_pos) (x: obj_addr) : scan_pos =
  if x = sp.cur then scan_none else sp

/// **Blackening** a grey object whose fields are all scanned: its edges were
/// scanned already.
val marking_inv_blacken (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (x: obj_addr)
  : Lemma (requires marking_inv g outside_refs sp /\ Seq.mem x (objects zero_addr g) /\ is_gray x g /\
                    all_scanned g sp x)
          (ensures marking_inv (makeBlack x g) outside_refs (blackened_pos sp x))

/// ---------------------------------------------------------------------------
/// Other changes to the heap
/// ---------------------------------------------------------------------------

/// A change that keeps the invariant, at a scan position it keeps: it keeps
/// grey objects grey and grey or white blocks grey or white, makes no object
/// white, and every unscanned edge between grey or white blocks it cuts ends
/// at a grey object; a scanned edge to a white object is an old scanned
/// edge, or its target is one the marker would already reach; and every
/// white outside reference afterwards was one before, or is one the marker
/// would already reach.
val marking_inv_change (g g': heap) (outside_refs outside_refs': obj_addr -> prop) (sp: scan_pos)
  : Lemma (requires
            marking_inv g outside_refs sp /\ well_formed_heap g' /\
            (forall (y: obj_addr). grey_or_white g y ==> grey_or_white g' y) /\
            (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_gray y g ==> is_gray y g') /\
            (forall (y: obj_addr). Seq.mem y (objects zero_addr g') /\ is_white y g' ==>
                              Seq.mem y (objects zero_addr g) /\ is_white y g) /\
            (forall (s t: obj_addr). grey_or_white g s /\ grey_or_white g t /\ unscanned_edge g sp s t ==>
                                unscanned_edge g' sp s t \/ is_gray t g') /\
            (forall (b t: obj_addr).
               scanned_edge g' sp b t /\ is_white t g' ==>
               scanned_edge g sp b t \/ marker_will_reach g sp t) /\
            (forall (w: obj_addr). outside_refs' w /\ Seq.mem w (objects zero_addr g') /\ is_white w g' ==>
                              outside_refs w \/ marker_will_reach g sp w))
          (ensures marking_inv g' outside_refs' sp)

/// Greying a white object -- the write barrier's darkening -- keeps it.
val marking_inv_grey (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos) (w: obj_addr)
  : Lemma (requires marking_inv g outside_refs sp /\ Seq.mem w (objects zero_addr g) /\ is_white w g)
          (ensures marking_inv (makeGray w g) outside_refs sp)

/// Greying a white object keeps every object the marker would reach.
val marker_will_reach_grey (g: heap) (sp: scan_pos) (w u: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem w (objects zero_addr g) /\ is_white w g /\
                    marker_will_reach g sp u)
          (ensures marker_will_reach (makeGray w g) sp u)

/// ---------------------------------------------------------------------------
/// The invariant as well-formedness
/// ---------------------------------------------------------------------------

/// What the marker leaves free, as of the heap `g0` at the scan position
/// `sp`: blue blocks, and white blocks it will not reach.  A function of the
/// header alone (the set it reads off `g0` is fixed), so an admissible
/// definition of free.
let unreached (g0: heap) (sp: scan_pos) : free_def =
  fun g x -> is_blue x g ||
          (is_white x g && not (FStar.IndefiniteDescription.strong_excluded_middle (marker_will_reach g0 sp x)))

val unreached_ok (g0: heap) (sp: scan_pos) : Lemma (free_def_ok (unreached g0 sp))

/// **The invariant makes the heap well formed for `unreached g sp`**: no
/// grey or black block, and no white one the marker will reach, points at a
/// white block the marker will not reach.  So whatever keeps
/// well-formedness for every admissible definition of free -- the minor
/// collection's generic theorem -- keeps that too.
val marking_inv_unreached (g: heap) (outside_refs: obj_addr -> prop) (sp: scan_pos)
  : Lemma (requires marking_inv g outside_refs sp)
          (ensures well_formed_heap_with (unreached g sp) g)

/// And back: in a heap well formed for `unreached g0 sp`, a grey or black
/// object's white target is one the marker would reach in `g0`.
val unreached_dark_edge (g0: heap) (sp: scan_pos) (g: heap) (b t: obj_addr)
  : Lemma (requires well_formed_heap_with (unreached g0 sp) g /\ Seq.mem b (objects zero_addr g) /\
                    (is_black b g \/ is_gray b g) /\ field_edge g b t /\ is_white t g)
          (ensures marker_will_reach g0 sp t)
