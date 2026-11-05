/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPhase - incremental marking: the step and the invariant
/// ---------------------------------------------------------------------------
///
/// Incremental marking (incremental-mark-plan.md, section 3) runs the mark
/// step a few objects at a time, with the program running in between.  The
/// mark stack is an implementation cache: the spec state is the heap's
/// colours alone.
///
///   * **The step** (`mark_step_at g x`, for any grey `x`): blacken `x`, and
///     grey its white children, resolved through infix pointers; a no-scan
///     object has none.  The stop-the-world step `GC.Spec.Mark.mark_step`,
///     which pops the stack, is the instance at the top of the stack
///     (`mark_step_heap`).
///
///   * **What the marker will reach** (`marker_will_reach g w`): `w` is
///     reachable from a grey object along a path of grey or white blocks.
///     The marker scans each object on such a path in turn.  A path through a
///     black object does not count, because the marker never scans a black
///     object again; grey objects in the middle are fine (the part from the
///     last one on is itself such a path).
///
///   * **The invariant** (`marking_inv g held`), where `held w` says that
///     something outside the major heap points at `w` (the program's roots,
///     and later the nursery's fields: the generational layer chooses):
///       1. every white object a black object points at is one the marker
///          will reach (the weak tri-colour invariant, `weak_tri_color`);
///       2. every white object held from outside is one the marker will
///          reach (`held_reached`);
///       3. the heap is well formed with free meaning blue: marking frees
///          nothing.
///
/// Start: after the roots are darkened, with no black object, it holds
/// (`marking_inv_start`).  Step: any mark step keeps it
/// (`marking_inv_step`).  End: with no grey object left, nothing is one the
/// marker will reach, so clause 1 is the strong tri-colour invariant and
/// clause 2 says every held object is marked -- the heap is `marked`, where
/// the sweep starts (`marking_done`, `marking_done_sweep_start`).
///
/// The program's events are changes to the heap that keep grey objects grey
/// and every grey or white block one, add no white object, and grey the
/// target of every edge between non-black blocks they cut
/// (`marking_inv_change`); greying a white object (the write barrier's
/// darkening) is one (`marking_inv_grey`).  The barrier's field write and
/// black allocation are instances too; proving their hypotheses needs the
/// field-write and allocation lemmas, which is M2.

module GC.Spec.MarkPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module FSE = GC.Spec.FusedSweep.End
module FSI = GC.Spec.FusedSweep.Inv
module FLA = GC.Spec.FreeList.Ascending
module SPI = GC.Spec.SweepPhase.Intrinsic

/// ---------------------------------------------------------------------------
/// What the marker will reach
/// ---------------------------------------------------------------------------

/// The edges of the heap graph: `y` is the object a pointer field of the
/// scannable object `x` points at, resolved through infix headers -- read
/// off the heap directly, so a colour change visibly keeps it.  Every edge of
/// `GC.Spec.HeapModel.create_graph` is one (`Mark.edge_implies_points_to`).
let field_edge (g: heap) (x y: obj_addr) : prop =
  ~(is_no_scan x g) /\ (exists (c: obj_addr). points_to g x c /\ resolve_object c g == y)

/// A block the marker has not finished: grey or white (not black, not free).
let grey_or_white (g: heap) (v: obj_addr) : prop =
  Seq.mem v (objects zero_addr g) /\ (is_gray v g \/ is_white v g)

/// `w` is reachable from a grey object along a path of grey or white blocks.
let marker_will_reach (g: heap) (w: obj_addr) : prop =
  exists (x: obj_addr). is_gray x g /\ reach_within (field_edge g) (grey_or_white g) x w

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

/// It is a grey or white block, from a grey block.
val marker_will_reach_elim (g: heap) (w: obj_addr)
  : Lemma (requires marker_will_reach g w)
          (ensures grey_or_white g w /\
                   (exists (x: obj_addr). Seq.mem x (objects zero_addr g) /\ is_gray x g))

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// Clause 1, the weak tri-colour invariant: every white object a black
/// object points at is one the marker will reach.
let weak_tri_color (g: heap) : prop =
  forall (b w: obj_addr).
    Seq.mem b (objects zero_addr g) /\ is_black b g /\ field_edge g b w /\ is_white w g ==>
    marker_will_reach g w

/// Clause 2: every white object held from outside the major heap is one
/// the marker will reach.
let held_reached (g: heap) (held: obj_addr -> prop) : prop =
  forall (w: obj_addr).
    held w /\ Seq.mem w (objects zero_addr g) /\ is_white w g ==> marker_will_reach g w

/// The marking invariant.  `held w`: something outside the major heap points
/// at `w` (resolved).
let marking_inv (g: heap) (held: obj_addr -> prop) : prop =
  well_formed_heap g /\ weak_tri_color g /\ held_reached g held

/// ---------------------------------------------------------------------------
/// Start, step, end
/// ---------------------------------------------------------------------------

/// **Start.**  No black object points at a white one (in particular, there is
/// no black object), and every held object has been darkened.
val marking_inv_start (g: heap) (held: obj_addr -> prop)
  : Lemma (requires well_formed_heap g /\ Mark.tri_color_invariant g /\
                    (forall (w: obj_addr). held w /\ Seq.mem w (objects zero_addr g) ==> ~(is_white w g)))
          (ensures marking_inv g held)

/// With no black object, no black object points at a white one.
val no_black_tri_color (g: heap)
  : Lemma (requires Mark.no_black_objects g)
          (ensures Mark.tri_color_invariant g)

/// **Step.**  A mark step at any grey object keeps the invariant.
val marking_inv_step (g: heap) (held: obj_addr -> prop) (x: obj_addr)
  : Lemma (requires marking_inv g held /\ Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures marking_inv (mark_step_at g x) held)

/// **End.**  With no grey object left, the heap is `marked` -- no grey, and no
/// black object points at a white one -- and no held object is white.
val marking_done (g: heap) (held: obj_addr -> prop)
  : Lemma (requires marking_inv g held /\ Mark.noGreyObjects g)
          (ensures FSE.marked g /\
                   (forall (w: obj_addr). held w /\ Seq.mem w (objects zero_addr g) ==> ~(is_white w g)))

/// The hand-over to the sweep: from a heap where marking is done, with the
/// walk facts and the free list the allocator keeps, the sweep starts
/// (`SPI.sweep_inv_incremental_start`).
val marking_done_sweep_start (g: heap) (held: obj_addr -> prop) (fp: U64.t)
  : Lemma (requires marking_inv g held /\ Mark.noGreyObjects g /\
                    FSI.sweep_g0 g /\ FLA.fl_ascending g fp)
          (ensures FSI.sweep_pre g fp /\ FSE.marked g /\
                   SPI.sweep_inv_incremental g fp GC.Spec.FusedSweep.sweep_start.cursor /\
                   SPI.pending_free_within g GC.Spec.FusedSweep.sweep_start.cursor (SPI.white_after_mark g))

/// ---------------------------------------------------------------------------
/// Other changes to the heap
/// ---------------------------------------------------------------------------

/// A change that keeps the invariant: it keeps grey objects grey and grey or
/// white blocks grey or white, makes no object white, and every edge between
/// grey or white blocks it cuts ends at a grey object; a black object's edge
/// to a white one is an old black edge, or its target is one the marker would
/// already reach; and every white object held afterwards was held before, or
/// is one the marker would already reach.
val marking_inv_change (g g': heap) (held held': obj_addr -> prop)
  : Lemma (requires
            marking_inv g held /\ well_formed_heap g' /\
            (forall (y: obj_addr). grey_or_white g y ==> grey_or_white g' y) /\
            (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_gray y g ==> is_gray y g') /\
            (forall (y: obj_addr). Seq.mem y (objects zero_addr g') /\ is_white y g' ==>
                              Seq.mem y (objects zero_addr g) /\ is_white y g) /\
            (forall (s t: obj_addr). grey_or_white g s /\ grey_or_white g t /\ field_edge g s t ==>
                                field_edge g' s t \/ is_gray t g') /\
            (forall (b t: obj_addr).
               Seq.mem b (objects zero_addr g') /\ is_black b g' /\ field_edge g' b t /\ is_white t g' ==>
               (Seq.mem b (objects zero_addr g) /\ is_black b g /\ field_edge g b t) \/
               marker_will_reach g t) /\
            (forall (w: obj_addr). held' w /\ Seq.mem w (objects zero_addr g') /\ is_white w g' ==>
                              held w \/ marker_will_reach g w))
          (ensures marking_inv g' held')

/// Greying a white object -- the write barrier's darkening -- keeps it.
val marking_inv_grey (g: heap) (held: obj_addr -> prop) (w: obj_addr)
  : Lemma (requires marking_inv g held /\ Seq.mem w (objects zero_addr g) /\ is_white w g)
          (ensures marking_inv (makeGray w g) held)

/// Greying a white object keeps every object the marker would reach.
val marker_will_reach_grey (g: heap) (w u: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem w (objects zero_addr g) /\ is_white w g /\
                    marker_will_reach g u)
          (ensures marker_will_reach (makeGray w g) u)

/// ---------------------------------------------------------------------------
/// The invariant as well-formedness
/// ---------------------------------------------------------------------------

/// What the marker leaves free, as of the heap `g0`: blue blocks, and white
/// blocks it will not reach.  A function of the header alone (the set it
/// reads off `g0` is fixed), so an admissible definition of free.
let unreached (g0: heap) : free_def =
  fun g x -> is_blue x g ||
          (is_white x g && not (FStar.IndefiniteDescription.strong_excluded_middle (marker_will_reach g0 x)))

val unreached_ok (g0: heap) : Lemma (free_def_ok (unreached g0))

/// **The invariant makes the heap well formed for `unreached g`**: no grey or
/// black block, and no white one the marker will reach, points at a white
/// block the marker will not reach.  So whatever keeps well-formedness for
/// every admissible definition of free -- the minor collection's generic
/// theorem -- keeps that too.
val marking_inv_unreached (g: heap) (held: obj_addr -> prop)
  : Lemma (requires marking_inv g held)
          (ensures well_formed_heap_with (unreached g) g)

/// And back: in a heap well formed for `unreached g0`, a black object's
/// white target is one the marker would reach in `g0`.
val unreached_black_edge (g0 g: heap) (b t: obj_addr)
  : Lemma (requires well_formed_heap_with (unreached g0) g /\ Seq.mem b (objects zero_addr g) /\
                    is_black b g /\ field_edge g b t /\ is_white t g)
          (ensures marker_will_reach g0 t)
