/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPhase.Slice - what a mark slice does to the heap
/// ---------------------------------------------------------------------------
///
/// A mark slice (incremental-mark-plan.md, M4) scans a budget of words and
/// stops.  An object larger than what is left of the budget is scanned in
/// parts: it stays grey while some of its fields are scanned, and is
/// blackened only once the last one is (OCaml 4.14 keeps `(object, next
/// field)` entries for the same purpose).  The scan position
/// (`GC.Spec.MarkPhase.scan_pos`: the partly scanned object and its next
/// field) is part of the state, so a slice is a sequence of three kinds of
/// moves on the heap's colours and the position:
///
///   * **starting to scan** (`begin_move`): with no partly scanned object, a
///     grey object with fields becomes it, at its first field;
///   * **scanning a field** (`grey_move`): the target of the partly scanned
///     object's next field is greyed if it is white (`MM.darken`, 4.14's
///     `mark_slice_darken`), and the position moves one field on; the object
///     stays grey;
///   * **blackening** (`black_move`): a grey object all of whose fields are
///     scanned (`MP.all_scanned`: the partly scanned object past its last
///     field, or an object with no fields to scan) becomes black, and is no
///     longer the partly scanned object.
///
/// The marking invariant survives each move on its own
/// (`MP.marking_inv_begin`, `MP.marking_inv_advance` after the darkening,
/// `MP.marking_inv_blacken`).  Blackening asks nothing of the fields' current
/// values: a field scanned in an earlier slice and overwritten since by the
/// program is an edge the invariant already treats as scanned (the barrier
/// made sure its new target is one the marker will reach, or not white).  So
/// the program's writes never restart a scan, and a slice with an unbounded
/// budget finishes marking whatever the program did in between.
///
/// `mark_steps g sp g' sp'` is any number of moves.  What they keep: the
/// marking invariant for every set of outside references (`mark_steps_inv`);
/// everything but colours, with colours only getting darker (`darker`,
/// `mark_steps_darker`).  And what they decrease: `mark_weight` (two per
/// white block, one per grey), strictly at every move that changes the heap
/// (`weight_grey`, `weight_black`), the measure behind the termination of an
/// unbounded slice.  The stop-the-world step `GC.Spec.MarkPhase.mark_step_at`
/// is the composition (scan every field, then blacken): blackening an object
/// whose fields are dark is that step (`black_move_is_step`), which a full
/// collection (`GC.Spec.MarkPhase.Stw`) uses with the fields the partly
/// scanned object has been scanned up to kept dark (`fields_dark`, no program
/// running).

module GC.Spec.MarkPhase.Slice

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module HG = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator

/// ---------------------------------------------------------------------------
/// Dark fields
/// ---------------------------------------------------------------------------

/// The field `k` of `x` is dark: not a pointer, or a pointer to a block that
/// is not white (resolved through infix headers, as the marker resolves it).
let field_dark (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1}) : prop =
  is_pointer (HG.get_field g x k) ==>
  ~(is_white (resolve_object (HG.get_field g x k) g) g)

/// The fields `lo .. hi` of `x` are dark (none when `hi < lo`).
let fields_dark (g: heap) (x: obj_addr) (lo hi: nat) : prop =
  forall (k: U64.t{U64.v k >= 1}). {:pattern (field_dark g x k)}
    lo <= U64.v k /\ U64.v k <= hi ==> field_dark g x k

/// A block the marker may scan: a grey block with fields to scan.
let scan_target (g: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\ is_gray x g /\ ~(is_no_scan x g)

/// ---------------------------------------------------------------------------
/// The moves
/// ---------------------------------------------------------------------------

/// Scanning the field `k` of `x`: its target greyed if white.
let scan_field (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1}) : GTot heap =
  MM.darken g (HG.get_field g x k)

/// **Scanning the next field** of the partly scanned object, and moving past
/// it.
let grey_move (g: heap) (sp: MP.scan_pos) (g': heap) (sp': MP.scan_pos) : prop =
  exists (x: obj_addr).
    x == sp.MP.cur /\ scan_target g x /\ 1 <= sp.MP.fld /\ sp.MP.fld <= U64.v (wosize_of_object x g) /\
    g' == scan_field g x (U64.uint_to_t sp.MP.fld) /\ sp' == { sp with MP.fld = sp.MP.fld + 1 }

/// **Blackening** a grey object whose fields are all scanned; it is no longer
/// the partly scanned object.
let black_move (g: heap) (sp: MP.scan_pos) (g': heap) (sp': MP.scan_pos) : prop =
  exists (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ is_gray x g /\ MP.all_scanned g sp x /\
    g' == makeBlack x g /\ sp' == MP.blackened_pos sp x

/// **Starting to scan** a grey object with fields, when none is partly
/// scanned.
let begin_move (g: heap) (sp: MP.scan_pos) (g': heap) (sp': MP.scan_pos) : prop =
  exists (x: obj_addr).
    sp.MP.cur == 0UL /\ scan_target g x /\ g' == g /\ sp' == { MP.cur = x; MP.fld = 1 }

let mark_move (g: heap) (sp: MP.scan_pos) (g': heap) (sp': MP.scan_pos) : prop =
  grey_move g sp g' sp' \/ black_move g sp g' sp' \/ begin_move g sp g' sp'

/// The moves through the states of `l`, from `(g, sp)` to `(g', sp')`.
let rec moves (g: heap) (sp: MP.scan_pos) (l: list (heap & MP.scan_pos)) (g': heap) (sp': MP.scan_pos)
  : Tot prop (decreases l) =
  match l with
  | [] -> g == g' /\ sp == sp'
  | (h, q) :: t -> mark_move g sp h q /\ moves h q t g' sp'

/// **Any number of moves.**
let mark_steps (g: heap) (sp: MP.scan_pos) (g': heap) (sp': MP.scan_pos) : prop =
  exists (l: list (heap & MP.scan_pos)). moves g sp l g' sp'

val mark_steps_refl (g: heap) (sp: MP.scan_pos) : Lemma (mark_steps g sp g sp)

val mark_steps_trans (g1 g2 g3: heap) (sp1 sp2 sp3: MP.scan_pos)
  : Lemma (requires mark_steps g1 sp1 g2 sp2 /\ mark_steps g2 sp2 g3 sp3) (ensures mark_steps g1 sp1 g3 sp3)

val mark_steps_move (g g': heap) (sp sp': MP.scan_pos)
  : Lemma (requires mark_move g sp g' sp') (ensures mark_steps g sp g' sp')

/// One more move.
val mark_steps_snoc (g1 g2 g3: heap) (sp1 sp2 sp3: MP.scan_pos)
  : Lemma (requires mark_steps g1 sp1 g2 sp2 /\ mark_move g2 sp2 g3 sp3) (ensures mark_steps g1 sp1 g3 sp3)

/// What every move keeps, any number of moves keep.
val mark_steps_ind (p: heap -> MP.scan_pos -> prop)
  (step: (g: heap) -> (sp: MP.scan_pos) -> (g': heap) -> (sp': MP.scan_pos) ->
         Lemma (requires p g sp /\ mark_move g sp g' sp') (ensures p g' sp'))
  (g: heap) (sp: MP.scan_pos) (g': heap) (sp': MP.scan_pos)
  : Lemma (requires p g sp /\ mark_steps g sp g' sp') (ensures p g' sp')

/// ---------------------------------------------------------------------------
/// The moves as the stop-the-world step
/// ---------------------------------------------------------------------------

/// Scanning a field is greying its target, if white.
val scan_field_is_grey (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g))
          (ensures (let v = HG.get_field g x k in
                    if is_pointer v && is_white (resolve_object v g) g
                    then Seq.mem (resolve_object v g) (objects zero_addr g) /\
                         scan_field g x k == makeGray (resolve_object v g) g
                    else scan_field g x k == g))

/// It leaves the field dark.
val scan_field_dark (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g))
          (ensures field_dark (scan_field g x k) x k)

/// **Blackening a grey object whose fields are dark is the stop-the-world
/// step at it.**  (Not a condition of `black_move`; a full collection, with
/// no program running, keeps the fields dark and uses it.)
val black_move_is_step (g: heap) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ is_gray x g /\
                    (is_no_scan x g \/ fields_dark g x 1 (U64.v (wosize_of_object x g))))
          (ensures makeBlack x g == MP.mark_step_at g x)

/// ---------------------------------------------------------------------------
/// What the moves keep
/// ---------------------------------------------------------------------------

/// **The marking invariant**, for any `outside_refs`.
val mark_move_inv (g g': heap) (sp sp': MP.scan_pos) (outside_refs: obj_addr -> prop)
  : Lemma (requires MP.marking_inv g outside_refs sp /\ mark_move g sp g' sp')
          (ensures MP.marking_inv g' outside_refs sp')

val mark_steps_inv (g g': heap) (sp sp': MP.scan_pos) (outside_refs: obj_addr -> prop)
  : Lemma (requires MP.marking_inv g outside_refs sp /\ mark_steps g sp g' sp')
          (ensures MP.marking_inv g' outside_refs sp')

/// `g'` is `g` with some blocks darker: the same walk, headers but for their
/// colours, fields and resolutions; free blocks stay free and nothing else
/// becomes free; nothing becomes white, grey blocks stay grey or turn black,
/// and black ones stay black.
let darker (g g': heap) : prop =
  well_formed_heap g' /\
  objects zero_addr g' == objects zero_addr g /\
  (heap_objects_dense g ==> heap_objects_dense g') /\
  (forall (y: obj_addr). {:pattern (wosize_of_object y g')}
     Seq.mem y (objects zero_addr g) ==> wosize_of_object y g' == wosize_of_object y g) /\
  (forall (y: obj_addr). {:pattern (is_no_scan y g')}
     Seq.mem y (objects zero_addr g) ==> is_no_scan y g' == is_no_scan y g) /\
  (forall (y: obj_addr). {:pattern (is_blue y g')}
     Seq.mem y (objects zero_addr g) ==> (is_blue y g' <==> is_blue y g)) /\
  (forall (y: obj_addr). {:pattern (is_white y g')}
     Seq.mem y (objects zero_addr g) ==> (is_white y g' ==> is_white y g)) /\
  (forall (y: obj_addr). {:pattern (is_gray y g')}
     Seq.mem y (objects zero_addr g) /\ is_gray y g ==> is_gray y g' \/ is_black y g') /\
  (forall (y: obj_addr). {:pattern (is_black y g')}
     Seq.mem y (objects zero_addr g) /\ is_black y g ==> is_black y g') /\
  (forall (y: obj_addr) (k: U64.t{U64.v k >= 1}). {:pattern (HG.get_field g' y k)}
     Seq.mem y (objects zero_addr g) /\ U64.v k <= U64.v (wosize_of_object y g) ==>
     HG.get_field g' y k == HG.get_field g y k) /\
  (forall (v: obj_addr). {:pattern (resolve_object v g')} resolve_object v g' == resolve_object v g)

val darker_refl (g: heap) : Lemma (requires well_formed_heap g) (ensures darker g g)

val darker_trans (g1 g2 g3: heap)
  : Lemma (requires darker g1 g2 /\ darker g2 g3) (ensures darker g1 g3)

val mark_move_darker (g g': heap) (sp sp': MP.scan_pos)
  : Lemma (requires well_formed_heap g /\ mark_move g sp g' sp') (ensures darker g g')

val mark_steps_darker (g g': heap) (sp sp': MP.scan_pos)
  : Lemma (requires well_formed_heap g /\ mark_steps g sp g' sp') (ensures darker g g')

/// Dark fields of a scannable block that is not free stay dark.
val darker_fields_dark (g g': heap) (x: obj_addr) (lo hi: nat)
  : Lemma (requires darker g g' /\ Seq.mem x (objects zero_addr g) /\
                    ~(is_blue x g) /\ ~(is_no_scan x g) /\
                    hi <= U64.v (wosize_of_object x g) /\ fields_dark g x lo hi)
          (ensures fields_dark g' x lo hi)

/// ---------------------------------------------------------------------------
/// The measure
/// ---------------------------------------------------------------------------

/// Two for each white block, one for each grey block.
val mark_weight (g: heap) : GTot nat

/// Greying a white block, or blackening a grey one, takes one off.
val weight_grey (g: heap) (t: obj_addr)
  : Lemma (requires Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures mark_weight (makeGray t g) + 1 == mark_weight g)

val weight_black (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures mark_weight (makeBlack x g) + 1 == mark_weight g)

/// A scanned field: one less if its target was white, else the same heap.
val scan_field_weight (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g))
          (ensures (scan_field g x k == g) \/ (mark_weight (scan_field g x k) + 1 == mark_weight g))
