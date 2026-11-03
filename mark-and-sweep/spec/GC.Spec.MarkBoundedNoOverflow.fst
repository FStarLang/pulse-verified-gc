/// ---------------------------------------------------------------------------
/// GC.Spec.MarkBoundedNoOverflow — proofs
/// ---------------------------------------------------------------------------

module GC.Spec.MarkBoundedNoOverflow

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Mark
open GC.Spec.MarkBounded

module U64 = FStar.UInt64
module SweepInv = GC.Spec.SweepInv
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header
module SeqP = FStar.Seq.Properties

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// Recolouring one object leaves every other object's grayness alone.
let set_color_other_gray (obj x: obj_addr) (g: heap) (c: color)
  : Lemma (requires x <> obj)
          (ensures is_gray x (set_object_color obj g c) == is_gray x g)
  = hd_address_injective obj x;
    color_change_locality obj x g c;
    is_gray_iff x g;
    is_gray_iff x (set_object_color obj g c)

let rec push_children_bounded_length_mono g st obj i ws cap =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    let (g', st') =
      if HeapGraph.is_pointer_field v then begin
        HeapGraph.is_pointer_field_is_obj_addr v;
        let child_raw : obj_addr = v in
        let child = resolve_object child_raw g in
        if is_white child g then
          let g' = makeGray child g in
          if Seq.length st < cap then (g', Seq.cons child st) else (g', st)
        else (g, st)
      end else (g, st)
    in
    if U64.v i < U64.v ws then
      push_children_bounded_length_mono g' st' obj (U64.add i 1UL) ws cap
    else ()
  end

/// Graying a white `child` and consing it keeps every gray object on the stack.
let gray_on_stack_after_push (g: heap) (st: seq obj_addr) (child: obj_addr)
  : Lemma (requires gray_objects_on_stack g st)
          (ensures gray_objects_on_stack (makeGray child g) (Seq.cons child st))
  = let g1 = makeGray child g in
    makeGray_eq child g;
    color_change_preserves_objects g child Header.Gray;
    SeqP.mem_cons child st;
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g1) /\ is_gray x g1)
              (ensures Seq.mem x (Seq.cons child st))
      = if x = child then () else set_color_other_gray child x g Header.Gray
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#push-options "--z3rlimit 40"
let rec push_children_bounded_gray_on_stack g st obj i ws cap =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child_raw : obj_addr = v in
      let child = resolve_object child_raw g in
      if is_white child g then begin
        let g1 = makeGray child g in
        if Seq.length st < cap then begin
          gray_on_stack_after_push g st child;
          if U64.v i < U64.v ws then
            push_children_bounded_gray_on_stack g1 (Seq.cons child st) obj (U64.add i 1UL) ws cap
          else ()
        end else begin
          // The child is dropped here.  The stack is full and can only grow,
          // so it is still full at the end, contradicting the hypothesis.
          if U64.v i < U64.v ws then
            push_children_bounded_length_mono g1 st obj (U64.add i 1UL) ws cap
          else ()
        end
      end else begin
        if U64.v i < U64.v ws then
          push_children_bounded_gray_on_stack g st obj (U64.add i 1UL) ws cap
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_bounded_gray_on_stack g st obj (U64.add i 1UL) ws cap
      else ()
    end
  end
#pop-options

/// Popping the gray head and blackening it keeps every gray object on the tail.
let gray_on_stack_after_pop (g: heap) (st: seq obj_addr{Seq.length st > 0})
  : Lemma (requires gray_objects_on_stack g st)
          (ensures gray_objects_on_stack (makeBlack (Seq.head st) g) (Seq.tail st))
  = let obj = Seq.head st in
    let g1 = makeBlack obj g in
    makeBlack_eq obj g;
    color_change_preserves_objects g obj Header.Black;
    makeBlack_is_black obj g;
    SeqP.cons_head_tail st;
    SeqP.mem_cons obj (Seq.tail st);
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g1) /\ is_gray x g1)
              (ensures Seq.mem x (Seq.tail st))
      = gray_black_disjoint x obj g1;
        set_color_other_gray obj x g Header.Black
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let mark_step_bounded_gray_on_stack g st cap =
  let obj = Seq.head st in
  gray_on_stack_after_pop g st;
  if is_no_scan obj g then ()
  else
    push_children_bounded_gray_on_stack (makeBlack obj g) (Seq.tail st) obj 1UL
      (wosize_of_object obj g) cap

let no_gray_of_gray_on_empty_stack g st =
  Seq.lemma_empty st;
  SweepInv.no_gray_intro g

let gray_on_stack_of_roots_eq_stack g st = ()

/// ---------------------------------------------------------------------------
/// Vacuity checks
/// ---------------------------------------------------------------------------
///
/// Checked on every build.  `expect_failure` makes the build fail if the inner
/// proof ever *succeeds* (mark-and-sweep/NOTES.md, "Vacuity checking").

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// The hypotheses of the step lemma are satisfiable.
[@@expect_failure [19]]
let mark_step_bounded_gray_on_stack_hyps_not_false
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires gray_objects_on_stack g st /\
                    Seq.length (snd (mark_step_bounded g st cap)) < cap)
          (ensures False)
  = ()

[@@expect_failure [19]]
let push_children_bounded_gray_on_stack_hyps_not_false
  (g: heap) (st: seq obj_addr) (obj: obj_addr)
  (i: U64.t{U64.v i >= 1}) (ws: U64.t) (cap: nat)
  : Lemma (requires gray_objects_on_stack g st /\
                    Seq.length (snd (push_children_bounded g st obj i ws cap)) < cap)
          (ensures False)
  = ()

[@@expect_failure [19]]
let no_gray_of_gray_on_empty_stack_hyps_not_false (g: heap) (st: seq obj_addr)
  : Lemma (requires gray_objects_on_stack g st /\ Seq.length st == 0)
          (ensures False)
  = ()

/// The `< cap` hypothesis is what carries the step lemma: a full stack may
/// have dropped a child, and then the conclusion does not follow.
[@@expect_failure [19]]
let mark_step_bounded_gray_on_stack_needs_not_full
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires gray_objects_on_stack g st)
          (ensures (let (g', st') = mark_step_bounded g st cap in
                    gray_objects_on_stack g' st'))
  = gray_on_stack_after_pop g st
#pop-options
