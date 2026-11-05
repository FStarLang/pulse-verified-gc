module GC.Spec.MarkPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv
module FSE = GC.Spec.FusedSweep.End
module FSI = GC.Spec.FusedSweep.Inv
module FLA = GC.Spec.FreeList.Ascending
module SPI = GC.Spec.SweepPhase.Intrinsic

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// The stop-the-world step is the step at the top of the stack
/// ---------------------------------------------------------------------------

/// `push_children`'s heap does not depend on the stack.
#push-options "--fuel 1"
let rec push_children_heap (g: heap) (st st': seq obj_addr) (obj: obj_addr)
    (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (ensures fst (Mark.push_children g st obj i ws) == fst (Mark.push_children g st' obj i ws))
          (decreases (U64.v ws - U64.v i))
  = if U64.v i > U64.v ws then ()
    else begin
      let v = HeapGraph.get_field g obj i in
      if HeapGraph.is_pointer_field v then begin
        HeapGraph.is_pointer_field_is_obj_addr v;
        let child = resolve_object (v <: obj_addr) g in
        if is_white child g then begin
          if U64.v i < U64.v ws then
            push_children_heap (makeGray child g) (Seq.cons child st) (Seq.cons child st') obj (U64.add i 1UL) ws
        end else if U64.v i < U64.v ws then
          push_children_heap g st st' obj (U64.add i 1UL) ws
      end else if U64.v i < U64.v ws then
        push_children_heap g st st' obj (U64.add i 1UL) ws
    end
#pop-options

let mark_step_heap g st =
  let x = Seq.head st in
  if is_no_scan x g then ()
  else push_children_heap (makeBlack x g) (Seq.tail st) Seq.empty x 1UL (wosize_of_object x g)

/// ---------------------------------------------------------------------------
/// One colour change
/// ---------------------------------------------------------------------------

let cc_colours (o y: obj_addr) (g: heap) (c: color)
  : Lemma (requires o <> y)
          (ensures (let g' = set_object_color o g c in
                    (is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                    (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))
  = let g' = set_object_color o g c in
    color_change_preserves_other_color o y g c;
    is_black_iff y g; is_black_iff y g';
    is_white_iff y g; is_white_iff y g';
    is_gray_iff y g; is_gray_iff y g';
    is_blue_iff y g; is_blue_iff y g'

/// A colour change keeps every edge.
let cc_field_edge (g: heap) (o: obj_addr) (c: color) (u v: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem o (objects zero_addr g) /\ Seq.mem u (objects zero_addr g))
          (ensures field_edge (set_object_color o g c) u v <==> field_edge g u v)
  = let g' = set_object_color o g c in
    let pt (d: obj_addr) : Lemma (points_to g' u d == points_to g u d) =
      if u = o then color_change_preserves_points_to_self g o c d
      else color_change_preserves_points_to_other g o c u d
    in
    FStar.Classical.forall_intro pt;
    let rs (d: obj_addr) : Lemma (resolve_object d g' == resolve_object d g) =
      color_change_preserves_resolve o d g c
    in
    FStar.Classical.forall_intro rs;
    if u = o then color_preserves_is_no_scan o g c
    else color_change_preserves_other_is_no_scan o u g c

/// The target of an edge out of a block that is not free is a block that is
/// not free.
let edge_target (g: heap) (b w: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem b (objects zero_addr g) /\ ~(is_blue b g) /\
                    field_edge g b w)
          (ensures Seq.mem w (objects zero_addr g) /\ ~(is_blue w g))
  = eliminate exists (c: obj_addr). points_to g b c /\ resolve_object c g == w
    with points_to_target_not_blue g b c

/// ---------------------------------------------------------------------------
/// The step's effect
/// ---------------------------------------------------------------------------

let pre (g: heap) (x: obj_addr) : prop =
  well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ is_gray x g

let pc_pre (g1: heap) (x: obj_addr) (ws: U64.t) : prop =
  well_formed_heap g1 /\ Seq.mem x (objects zero_addr g1) /\ in_use free_stw g1 x /\
  U64.v ws <= U64.v (wosize_of_object x g1) /\
  ~(is_no_scan x g1) /\ ~(is_blue x g1) /\ U64.v (wosize_of_object x g1) < pow2 54

let black_setup (g: heap) (x: obj_addr)
  : Lemma (requires pre g x)
          (ensures (let g1 = makeBlack x g in
                    g1 == set_object_color x g Header.Black /\
                    well_formed_heap g1 /\ objects zero_addr g1 == objects zero_addr g /\
                    wosize_of_object x g1 == wosize_of_object x g /\
                    is_no_scan x g1 == is_no_scan x g /\
                    is_black x g1 /\ ~(is_blue x g1) /\ ~(is_blue x g) /\ ~(is_white x g1) /\
                    U64.v (wosize_of_object x g) < pow2 54 /\
                    (~(is_no_scan x g) ==>
                       pc_pre g1 x (wosize_of_object x g) /\
                       mark_step_at g x == fst (Mark.push_children g1 Seq.empty x 1UL (wosize_of_object x g)))))
  = let g1 = makeBlack x g in
    makeBlack_eq x g; makeBlack_is_black x g;
    Mark.colors_exclusive x g;
    Mark.colors_exclusive x g1;
    Mark.color_change_preserves_wf g x Header.Black;
    color_change_preserves_objects g x Header.Black;
    color_preserves_wosize x g Header.Black;
    wosize_of_object_bound x g;
    color_preserves_is_no_scan x g Header.Black

let mark_step_at_objects g x =
  black_setup g x;
  if is_no_scan x g then ()
  else Mark.push_children_preserves_objects (makeBlack x g) Seq.empty x 1UL (wosize_of_object x g)

let mark_step_at_wf g x =
  black_setup g x;
  if is_no_scan x g then ()
  else Mark.push_children_preserves_wf (makeBlack x g) Seq.empty x 1UL (wosize_of_object x g)

/// Density is kept by every colour change, so by `push_children`.
#push-options "--fuel 1"
let rec push_children_dense (g: heap) (st: seq obj_addr) (obj: obj_addr)
    (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires heap_objects_dense g)
          (ensures heap_objects_dense (fst (Mark.push_children g st obj i ws)))
          (decreases (U64.v ws - U64.v i))
  = if U64.v i > U64.v ws then ()
    else begin
      let v = HeapGraph.get_field g obj i in
      if HeapGraph.is_pointer_field v then begin
        HeapGraph.is_pointer_field_is_obj_addr v;
        let child = resolve_object (v <: obj_addr) g in
        if is_white child g then begin
          makeGray_eq child g;
          SweepInv.color_change_preserves_density child g Header.Gray;
          if U64.v i < U64.v ws then
            push_children_dense (makeGray child g) (Seq.cons child st) obj (U64.add i 1UL) ws
        end else if U64.v i < U64.v ws then
          push_children_dense g st obj (U64.add i 1UL) ws
      end else if U64.v i < U64.v ws then
        push_children_dense g st obj (U64.add i 1UL) ws
    end
#pop-options

let mark_step_at_dense g x =
  makeBlack_eq x g;
  SweepInv.color_change_preserves_density x g Header.Black;
  if is_no_scan x g then ()
  else push_children_dense (makeBlack x g) Seq.empty x 1UL (wosize_of_object x g)

let mark_step_at_black g x =
  black_setup g x;
  if is_no_scan x g then ()
  else Mark.push_children_preserves_parent_black (makeBlack x g) Seq.empty x 1UL (wosize_of_object x g)

let mark_step_at_blue g x y =
  black_setup g x;
  let g1 = makeBlack x g in
  let ws = wosize_of_object x g in
  if y <> x then cc_colours x y g Header.Black;
  if is_no_scan x g then ()
  else if is_blue y g1 then Mark.push_children_preserves_blue g1 Seq.empty x 1UL ws y
  else Mark.push_children_no_new_blue g1 Seq.empty x 1UL ws y

/// Edges are kept.
let step_edge (g: heap) (x u v: obj_addr)
  : Lemma (requires pre g x /\ Seq.mem u (objects zero_addr g))
          (ensures field_edge (mark_step_at g x) u v <==> field_edge g u v)
  = black_setup g x;
    let g1 = makeBlack x g in
    let ws = wosize_of_object x g in
    cc_field_edge g x Header.Black u v;
    if is_no_scan x g then ()
    else begin
      let g2 = mark_step_at g x in
      let pt (d: obj_addr) : Lemma (points_to g2 u d == points_to g1 u d) =
        Mark.push_children_preserves_points_to g1 Seq.empty x 1UL ws u d
      in
      FStar.Classical.forall_intro pt;
      let rs (d: obj_addr) : Lemma (resolve_object d g2 == resolve_object d g1) =
        Mark.push_children_preserves_resolve g1 Seq.empty x 1UL ws d
      in
      FStar.Classical.forall_intro rs;
      Mark.push_children_preserves_is_no_scan g1 Seq.empty x 1UL ws u
    end

/// Blackness changes at `x` only.
let step_black_other (g: heap) (x y: obj_addr)
  : Lemma (requires pre g x /\ Seq.mem y (objects zero_addr g) /\ y <> x)
          (ensures is_black y (mark_step_at g x) <==> is_black y g)
  = black_setup g x;
    let g1 = makeBlack x g in
    let ws = wosize_of_object x g in
    cc_colours x y g Header.Black;
    if is_no_scan x g then ()
    else begin
      if is_black y g1 then Mark.push_children_preserves_other_black g1 Seq.empty x 1UL ws y;
      if is_black y (mark_step_at g x) then Mark.push_children_black_backward g1 Seq.empty x 1UL ws y
    end

/// Nothing becomes white.
let step_white (g: heap) (x y: obj_addr)
  : Lemma (requires pre g x /\ Seq.mem y (objects zero_addr g) /\ is_white y (mark_step_at g x))
          (ensures is_white y g /\ y <> x)
  = black_setup g x;
    let g1 = makeBlack x g in
    let ws = wosize_of_object x g in
    if y <> x then cc_colours x y g Header.Black;
    if is_no_scan x g then ()
    else if not (is_white y g1) then Mark.push_children_no_new_white g1 Seq.empty x 1UL ws y

/// `x`'s children are not white afterwards.
let step_child (g: heap) (x y: obj_addr)
  : Lemma (requires pre g x /\ field_edge g x y)
          (ensures ~(is_white y (mark_step_at g x)))
  = black_setup g x;
    let g1 = makeBlack x g in
    eliminate exists (c: obj_addr). points_to g x c /\ resolve_object c g == y
    with begin
      color_change_preserves_points_to_self g x Header.Black c;
      color_change_preserves_resolve x c g Header.Black;
      Mark.push_children_obj_children_non_white g1 Seq.empty x c
    end

/// A grey or white block other than `x` stays one; a grey one stays grey.
let step_grey_or_white (g: heap) (x y: obj_addr)
  : Lemma (requires pre g x /\ grey_or_white g y /\ y <> x)
          (ensures grey_or_white (mark_step_at g x) y /\
                   (is_gray y g ==> is_gray y (mark_step_at g x)))
  = let g2 = mark_step_at g x in
    mark_step_at_objects g x;
    step_black_other g x y;
    mark_step_at_blue g x y;
    Mark.colors_exclusive y g;
    Mark.color_exhaustive y g2;
    Mark.colors_exclusive y g2;
    if is_white y g2 then step_white g x y

/// A child of `x` that was grey or white is grey afterwards.
let step_child_grey (g: heap) (x y: obj_addr)
  : Lemma (requires pre g x /\ grey_or_white g y /\ y <> x /\ field_edge g x y)
          (ensures is_gray y (mark_step_at g x))
  = let g2 = mark_step_at g x in
    step_grey_or_white g x y;
    step_child g x y;
    Mark.colors_exclusive y g2

/// ---------------------------------------------------------------------------
/// What the marker will reach, across the step
/// ---------------------------------------------------------------------------

let marker_will_reach_elim g w =
  eliminate exists (x: obj_addr). is_gray x g /\ reach_within (field_edge g) (grey_or_white g) x w
  with reach_within_ends (field_edge g) (grey_or_white g) x w

let mwr_intro (g: heap) (x w: obj_addr)
  : Lemma (requires is_gray x g /\ reach_within (field_edge g) (grey_or_white g) x w)
          (ensures marker_will_reach g w)
  = ()

/// The mark step maps paths avoiding `x` to paths.
let step_mono (g: heap) (x a w: obj_addr)
  : Lemma (requires pre g x /\ reach_within (field_edge g) (without (grey_or_white g) x) a w)
          (ensures reach_within (field_edge (mark_step_at g x)) (grey_or_white (mark_step_at g x)) a w)
  = let g2 = mark_step_at g x in
    let p = without (grey_or_white g) x in
    let pm (v: obj_addr) : Lemma (requires p v) (ensures grey_or_white g2 v) =
      step_grey_or_white g x v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires pm);
    let em (u v: obj_addr) : Lemma (requires p u) (ensures field_edge g2 u v <==> field_edge g u v) =
      step_edge g x u v
    in
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (em u));
    reach_within_mono (field_edge g) (field_edge g2) p (grey_or_white g2) a w

let reach_step_avoid (g: heap) (x a w: obj_addr)
  : Lemma (requires pre g x /\ is_gray a g /\ reach_within (field_edge g) (without (grey_or_white g) x) a w)
          (ensures marker_will_reach (mark_step_at g x) w)
  = reach_within_ends (field_edge g) (without (grey_or_white g) x) a w;
    step_grey_or_white g x a;
    step_mono g x a w;
    mwr_intro (mark_step_at g x) a w

let reach_step_restart (g: heap) (x w: obj_addr)
  : Lemma (requires pre g x /\
                    (exists (s: obj_addr). field_edge g x s /\
                                      reach_within (field_edge g) (without (grey_or_white g) x) s w))
          (ensures marker_will_reach (mark_step_at g x) w)
  = eliminate exists (s: obj_addr). field_edge g x s /\
                                reach_within (field_edge g) (without (grey_or_white g) x) s w
    with begin
      reach_within_ends (field_edge g) (without (grey_or_white g) x) s w;
      step_child_grey g x s;
      step_mono g x s w;
      mwr_intro (mark_step_at g x) s w
    end

/// A white object the marker would reach, it still will after the step.
let reach_step (g: heap) (x w: obj_addr)
  : Lemma (requires pre g x /\ marker_will_reach g w /\ is_white w (mark_step_at g x))
          (ensures marker_will_reach (mark_step_at g x) w)
  = eliminate exists (a: obj_addr). is_gray a g /\ reach_within (field_edge g) (grey_or_white g) a w
    with begin
      reach_within_without (field_edge g) (grey_or_white g) x a w;
      mark_step_at_black g x;
      Mark.colors_exclusive x (mark_step_at g x);
      FStar.Classical.move_requires (reach_step_avoid g x a) w;
      FStar.Classical.move_requires (reach_step_restart g x) w
    end

/// ---------------------------------------------------------------------------
/// Start, step, end
/// ---------------------------------------------------------------------------

let marking_inv_start g held =
  let c1 (b w: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g) /\ is_black b g /\ field_edge g b w /\ is_white w g)
            (ensures marker_will_reach g w)
    = eliminate exists (c: obj_addr). points_to g b c /\ resolve_object c g == w
      with ()
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (c1 b))

let no_black_tri_color g = ()

let marking_inv_step g held x =
  let g2 = mark_step_at g x in
  mark_step_at_wf g x;
  mark_step_at_objects g x;
  let c1 (b w: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g2) /\ is_black b g2 /\ field_edge g2 b w /\ is_white w g2)
            (ensures marker_will_reach g2 w)
    = Mark.colors_exclusive b g2;
      edge_target g2 b w;
      step_white g x w;
      step_edge g x b w;
      if b = x then step_child g x w
      else begin
        step_black_other g x b;
        reach_step g x w
      end
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (c1 b));
  let c2 (w: obj_addr)
    : Lemma (requires held w /\ Seq.mem w (objects zero_addr g2) /\ is_white w g2)
            (ensures marker_will_reach g2 w)
    = step_white g x w;
      reach_step g x w
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires c2)

/// With nothing grey, the marker will reach nothing.
let nothing_to_reach (g: heap) (w: obj_addr)
  : Lemma (requires Mark.noGreyObjects g)
          (ensures ~(marker_will_reach g w))
  = FStar.Classical.move_requires (marker_will_reach_elim g) w

let marking_done g held =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (nothing_to_reach g));
  let tc (b c: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g) /\ is_black b g /\ ~(is_no_scan b g) /\ points_to g b c)
            (ensures ~(is_white (resolve_object c g) g))
    = assert (field_edge g b (resolve_object c g))
  in
  let tc' (b c: obj_addr)
    : Lemma (Seq.mem b (objects zero_addr g) ==> is_black b g ==> ~(is_no_scan b g) ==> points_to g b c ==>
             ~(is_white (resolve_object c g) g))
    = FStar.Classical.move_requires (tc b) c
  in
  FStar.Classical.forall_intro_2 tc';
  assert (Mark.tri_color_invariant g)

let marking_done_sweep_start g held fp =
  marking_done g held;
  SPI.sweep_inv_incremental_start g fp

/// ---------------------------------------------------------------------------
/// Other changes
/// ---------------------------------------------------------------------------

let change_hyps (g g': heap) : prop =
  (forall (y: obj_addr). grey_or_white g y ==> grey_or_white g' y) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_gray y g ==> is_gray y g') /\
  (forall (s t: obj_addr). grey_or_white g s /\ grey_or_white g t /\ field_edge g s t ==>
                      field_edge g' s t \/ is_gray t g')

let reach_change (g g': heap) (w: obj_addr)
  : Lemma (requires change_hyps g g' /\ marker_will_reach g w)
          (ensures marker_will_reach g' w)
  = eliminate exists (a: obj_addr). is_gray a g /\ reach_within (field_edge g) (grey_or_white g) a w
    with begin
      reach_within_ends (field_edge g) (grey_or_white g) a w;
      reach_within_restart (field_edge g) (field_edge g') (grey_or_white g) (grey_or_white g')
        (fun t -> is_gray t g') a w
    end

let marking_inv_change g g' held held' =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (reach_change g g'));
  let c1 (b w: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g') /\ is_black b g' /\ field_edge g' b w /\ is_white w g')
            (ensures marker_will_reach g' w)
    = Mark.colors_exclusive b g';
      edge_target g' b w
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (c1 b))

let marking_inv_grey g held w =
  let g' = makeGray w g in
  makeGray_eq w g;
  makeGray_is_gray w g;
  Mark.colors_exclusive w g;
  Mark.colors_exclusive w g';
  Mark.color_change_preserves_wf g w Header.Gray;
  color_change_preserves_objects g w Header.Gray;
  let col (y: obj_addr)
    : Lemma (y <> w ==> ((is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                         (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))
    = if y <> w then cc_colours w y g Header.Gray
  in
  FStar.Classical.forall_intro col;
  let edge (u v: obj_addr)
    : Lemma (Seq.mem u (objects zero_addr g) ==> (field_edge g' u v <==> field_edge g u v))
    = if Seq.mem u (objects zero_addr g) then cc_field_edge g w Header.Gray u v
  in
  FStar.Classical.forall_intro_2 edge;
  marking_inv_change g g' held held
