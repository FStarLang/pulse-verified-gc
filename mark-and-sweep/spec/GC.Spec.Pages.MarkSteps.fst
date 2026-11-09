/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.MarkSteps - the mark keeps the allocator's marking invariant
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Mark.mark` changes the heap only by recolouring objects that
/// are not free: `makeBlack` of the grey object it takes off the stack, and
/// `makeGray` of each white child it pushes.  Item 0's
/// `GC.Spec.Pages.MarkPhase.mark_inv_recolour` (the `phase_ok` clause of
/// `GC.Spec.AllocIface`) keeps the invariant at each of these, so it holds
/// of the marked heap (`mark_keeps_inv`).
///
/// The proof follows `GC.Spec.Mark`'s own `push_children_preserves_wf` and
/// `mark_step_preserves_wf`, step for step.

module GC.Spec.Pages.MarkSteps

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module Header = GC.Lib.Header
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module MP = GC.Spec.Pages.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// One field of `obj`, then the rest.
#push-options "--fuel 1 --ifuel 1"
let rec push_inv (g: heap) (pst: pstate) (st: Seq.seq obj_addr) (obj: obj_addr)
                 (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires MP.mark_inv g pst /\ well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\
                    fields_constrained g obj /\
                    U64.v ws <= U64.v (wosize_of_object obj g) /\
                    U64.v (wosize_of_object obj g) < pow2 54)
          (ensures MP.mark_inv (fst (Mark.push_children g st obj i ws)) pst)
          (decreases (U64.v ws - U64.v i))
  = if U64.v i > U64.v ws then ()
    else begin
      let v = HeapGraph.get_field g obj i in
      if HeapGraph.is_pointer_field v then begin
        HeapGraph.is_pointer_field_is_obj_addr v;
        let child_raw : obj_addr = v in
        let child = resolve_object child_raw g in
        if is_white child g then begin
          let g' = makeGray child g in
          makeGray_eq child g;
          Mark.check_and_darken_field_preserves_wf g obj i ws;
          colors_exhaustive_and_exclusive child g;
          MP.mark_inv_recolour g pst child Header.Gray;
          set_color_preserves_not_blue child obj g Header.Gray;
          if child = obj then color_preserves_is_no_scan obj g Header.Gray
          else color_change_preserves_other_is_no_scan child obj g Header.Gray;
          if U64.v i < U64.v ws then
            push_inv g' pst (Seq.cons child st) obj (U64.add i 1UL) ws
        end
        else if U64.v i < U64.v ws then push_inv g pst st obj (U64.add i 1UL) ws
      end
      else if U64.v i < U64.v ws then push_inv g pst st obj (U64.add i 1UL) ws
    end
#pop-options

/// One step of the mark.
let step_inv (g: heap) (pst: pstate) (st: Seq.seq obj_addr{Seq.length st > 0})
  : Lemma (requires MP.mark_inv g pst /\ well_formed_heap g /\ Mark.stack_props g st)
          (ensures MP.mark_inv (fst (Mark.mark_step g st)) pst)
  = let obj = Seq.head st in
    Mark.stack_head_is_gray g st;
    colors_exhaustive_and_exclusive obj g;
    makeBlack_eq obj g;
    MP.mark_inv_recolour g pst obj Header.Black;
    let g' = makeBlack obj g in
    Mark.color_change_preserves_wf g obj Header.Black;
    color_change_preserves_objects_mem g obj Header.Black obj;
    let ws = wosize_of_object obj g in
    wosize_of_object_bound obj g;
    set_object_color_preserves_getWosize_at_hd obj g Header.Black;
    wosize_of_object_spec obj g;
    wosize_of_object_spec obj g';
    color_preserves_is_no_scan obj g Header.Black;
    set_color_preserves_not_blue obj obj g Header.Black;
    if is_no_scan obj g then ()
    else push_inv g' pst (Seq.tail st) obj 1UL ws

#push-options "--fuel 1 --ifuel 1"
let rec aux_inv (g: heap) (pst: pstate) (st: Seq.seq obj_addr) (fuel: nat)
  : Lemma (requires MP.mark_inv g pst /\ well_formed_heap g /\ Mark.stack_props g st)
          (ensures MP.mark_inv (Mark.mark_aux g st fuel) pst)
          (decreases fuel)
  = if Seq.length st = 0 || fuel = 0 then ()
    else begin
      let (g', st') = Mark.mark_step g st in
      step_inv g pst st;
      Mark.mark_step_preserves_stack_props g st;
      Mark.mark_step_preserves_wf g st;
      aux_inv g' pst st' (fuel - 1)
    end
#pop-options

/// **The mark keeps the marking invariant.**
let mark_keeps_inv (g: heap) (pst: pstate) (st: Seq.seq obj_addr)
  : Lemma (requires MP.mark_inv g pst /\ well_formed_heap g /\ Mark.stack_props g st)
          (ensures MP.mark_inv (Mark.mark g st) pst)
  = aux_inv g pst st heap_words

/// Vacuity: the hypotheses are not refutable.
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
[@@expect_failure [19]]
let mark_keeps_inv_hyps_not_false (g: heap) (pst: pstate) (st: Seq.seq obj_addr)
  : Lemma (requires MP.mark_inv g pst /\ well_formed_heap g /\ Mark.stack_props g st)
          (ensures False)
  = ()
#pop-options
