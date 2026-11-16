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
module FT = GC.Spec.FieldTarget

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

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
/// Edges, field by field
/// ---------------------------------------------------------------------------

let get_field_word g x k =
  hd_address_spec x;
    wosize_of_object_bound x g

/// A field that points at `c` witnesses `points_to`.
let field_edge_at_points_to (g: heap) (x: obj_addr) (k: nat) (y: obj_addr)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\ field_edge_at g x k y)
          (ensures field_edge g x y)
  = get_field_word g x k;
    let v : obj_addr = HeapGraph.get_field g x (U64.uint_to_t k) in
    hd_address_spec v;
    FT.field_pointer_points_to_nat g x v (k - 1)

let field_edge_fields g x y =
  let to_fields () : Lemma (requires field_edge g x y) (ensures exists (k: nat). field_edge_at g x k y)
    = eliminate exists (c: obj_addr). points_to g x c /\ resolve_object c g == y
      with begin
        let q (d: obj_addr) : prop = resolve_object d g == y ==> (exists (k: nat). field_edge_at g x k y) in
        let field (j: nat)
          : Lemma (requires j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size)
                  (ensures (let w = read_word g (U64.uint_to_t (U64.v x + j * 8)) in
                            is_pointer w ==> q (w <: obj_addr)))
          = get_field_word g x (j + 1);
            let w = read_word g (U64.uint_to_t (U64.v x + j * 8)) in
            if is_pointer w then assert (field_edge_at g x (j + 1) (resolve_object (w <: obj_addr) g))
        in
        pointer_from_field g x c q field
      end
  in
  FStar.Classical.move_requires to_fields ();
  let from_fields (k: nat) : Lemma (requires field_edge_at g x k y) (ensures field_edge g x y)
    = field_edge_at_points_to g x k y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires from_fields)

let field_edge_at_kept g g' x k y = ()

/// A colour change keeps every field's edge.
let cc_field_edge_at (g: heap) (o: obj_addr) (c: color) (u: obj_addr) (k: nat) (v: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem o (objects zero_addr g) /\ Seq.mem u (objects zero_addr g))
          (ensures field_edge_at (set_object_color o g c) u k v <==> field_edge_at g u k v)
  = let g' = set_object_color o g c in
    color_change_preserves_wosize_any o u g c;
    (if u = o then color_preserves_is_no_scan o g c
     else color_change_preserves_other_is_no_scan o u g c);
    if 1 <= k && k <= U64.v (wosize_of_object u g) then begin
      Mark.color_preserves_get_field o u g c (U64.uint_to_t k);
      let w = HeapGraph.get_field g u (U64.uint_to_t k) in
      if is_pointer w then color_change_preserves_resolve o (w <: obj_addr) g c
    end;
    field_edge_at_kept g g' u k v

let unscanned_edge_fields g sp x y = field_edge_fields g x y

let scan_none_edges g x y = ()

let scanned_edge_field_edge g sp x y =
  if FStar.IndefiniteDescription.strong_excluded_middle
       (Seq.mem x (objects zero_addr g) /\ is_black x g /\ field_edge g x y) then ()
  else eliminate exists (k: nat). k < sp.fld /\ field_edge_at g x k y
       with field_edge_at_points_to g x k y

/// A colour change keeps every scanned and unscanned edge out of a block,
/// but for the blackness of the block itself.
let cc_edges (g: heap) (o: obj_addr) (c: color) (sp: scan_pos) (u v: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem o (objects zero_addr g) /\ Seq.mem u (objects zero_addr g))
          (ensures (let g' = set_object_color o g c in
                    (unscanned_edge g' sp u v <==> unscanned_edge g sp u v) /\
                    ((u == sp.cur /\ (exists (k: nat). k < sp.fld /\ field_edge_at g' u k v)) <==>
                     (u == sp.cur /\ (exists (k: nat). k < sp.fld /\ field_edge_at g u k v))) /\
                    (field_edge g' u v <==> field_edge g u v)))
  = cc_field_edge g o c u v;
    let f (k: nat) : Lemma (field_edge_at (set_object_color o g c) u k v <==> field_edge_at g u k v) = cc_field_edge_at g o c u k v in
    FStar.Classical.forall_intro f

let marker_will_reach_elim g sp w =
  eliminate exists (x: obj_addr). is_gray x g /\ reach_within (unscanned_edge g sp) (grey_or_white g) x w
  with reach_within_ends (unscanned_edge g sp) (grey_or_white g) x w

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

/// With no partly scanned object every edge is unscanned: what the marker
/// will reach is then reachability along every edge (`mwr0`), the form the
/// stop-the-world step is proved with.
let mwr0 (g: heap) (w: obj_addr) : prop =
  exists (x: obj_addr). is_gray x g /\ reach_within (field_edge g) (grey_or_white g) x w

let mwr_intro (g: heap) (x w: obj_addr)
  : Lemma (requires is_gray x g /\ reach_within (field_edge g) (grey_or_white g) x w)
          (ensures mwr0 g w)
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
          (ensures mwr0 (mark_step_at g x) w)
  = reach_within_ends (field_edge g) (without (grey_or_white g) x) a w;
    step_grey_or_white g x a;
    step_mono g x a w;
    mwr_intro (mark_step_at g x) a w

let reach_step_restart (g: heap) (x w: obj_addr)
  : Lemma (requires pre g x /\
                    (exists (s: obj_addr). field_edge g x s /\
                                      reach_within (field_edge g) (without (grey_or_white g) x) s w))
          (ensures mwr0 (mark_step_at g x) w)
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
  : Lemma (requires pre g x /\ mwr0 g w /\ is_white w (mark_step_at g x))
          (ensures mwr0 (mark_step_at g x) w)
  = eliminate exists (a: obj_addr). is_gray a g /\ reach_within (field_edge g) (grey_or_white g) a w
    with begin
      reach_within_without (field_edge g) (grey_or_white g) x a w;
      mark_step_at_black g x;
      Mark.colors_exclusive x (mark_step_at g x);
      FStar.Classical.move_requires (reach_step_avoid g x a) w;
      FStar.Classical.move_requires (reach_step_restart g x) w
    end

/// ---------------------------------------------------------------------------
/// What the marker will reach, at a scan position
/// ---------------------------------------------------------------------------

/// With no partly scanned object it is `mwr0`.
let mwr_none (g: heap) (w: obj_addr)
  : Lemma (marker_will_reach g scan_none w <==> mwr0 g w)
  = let p = grey_or_white g in
    let e1 = unscanned_edge g scan_none in
    let e0 = field_edge g in
    let to0 (x: obj_addr) : Lemma (requires is_gray x g /\ reach_within e1 p x w) (ensures mwr0 g w)
      = reach_within_mono e1 e0 p p x w
    in
    let from0 (x: obj_addr) : Lemma (requires is_gray x g /\ reach_within e0 p x w)
                                    (ensures marker_will_reach g scan_none w)
      = reach_within_mono e0 e1 p p x w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires to0);
    FStar.Classical.forall_intro (FStar.Classical.move_requires from0)

/// **What the marker will reach, across a change**: when every grey or
/// white block stays one, grey objects stay grey, and every unscanned edge
/// between grey or white blocks stays unscanned (at the new position) or
/// ends at an object grey afterwards.
let change_hyps (g g': heap) (sp sp': scan_pos) : prop =
  (forall (y: obj_addr). grey_or_white g y ==> grey_or_white g' y) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_gray y g ==> is_gray y g') /\
  (forall (s t: obj_addr). grey_or_white g s /\ grey_or_white g t /\ unscanned_edge g sp s t ==>
                      unscanned_edge g' sp' s t \/ is_gray t g')

let reach_change (g g': heap) (sp sp': scan_pos) (w: obj_addr)
  : Lemma (requires change_hyps g g' sp sp' /\ marker_will_reach g sp w)
          (ensures marker_will_reach g' sp' w)
  = eliminate exists (a: obj_addr). is_gray a g /\ reach_within (unscanned_edge g sp) (grey_or_white g) a w
    with begin
      reach_within_ends (unscanned_edge g sp) (grey_or_white g) a w;
      reach_within_restart (unscanned_edge g sp) (unscanned_edge g' sp') (grey_or_white g) (grey_or_white g')
        (fun t -> is_gray t g') a w
    end

/// **The invariant, across a change** from `g` at `sp` to `g'` at `sp'`:
/// well formed with the partly scanned object a grey block, no new white
/// object, what the marker would reach (if still white) it still will, a
/// scanned edge to a white object is an old one or ends where the marker
/// would reach, and so does every new outside reference.
let inv_transfer (g g': heap) (outside_refs outside_refs': obj_addr -> prop) (sp sp': scan_pos)
  : Lemma (requires
            marking_inv g outside_refs sp /\ well_formed_heap g' /\ scan_pos_ok g' sp' /\
            (forall (y: obj_addr). Seq.mem y (objects zero_addr g') /\ is_white y g' ==>
                              Seq.mem y (objects zero_addr g) /\ is_white y g) /\
            (forall (w: obj_addr). marker_will_reach g sp w /\ Seq.mem w (objects zero_addr g') /\ is_white w g' ==>
                              marker_will_reach g' sp' w) /\
            (forall (b t: obj_addr). scanned_edge g' sp' b t /\ is_white t g' ==>
                                scanned_edge g sp b t \/ marker_will_reach g sp t) /\
            (forall (w: obj_addr). outside_refs' w /\ Seq.mem w (objects zero_addr g') /\ is_white w g' ==>
                              outside_refs w \/ marker_will_reach g sp w))
          (ensures marking_inv g' outside_refs' sp')
  = let c1 (b w: obj_addr)
      : Lemma (requires scanned_edge g' sp' b w /\ is_white w g')
              (ensures marker_will_reach g' sp' w)
      = wf_parts ();
        Mark.colors_exclusive b g';
        assert (Seq.mem b (objects zero_addr g') /\ ~(is_blue b g'));
        scanned_edge_field_edge g' sp' b w;
        edge_target g' b w;
        assert (Seq.mem w (objects zero_addr g) /\ is_white w g);
        assert (scanned_edge g sp b w \/ marker_will_reach g sp w);
        assert (marker_will_reach g sp w)
    in
    FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (c1 b));
    let c2 (w: obj_addr)
      : Lemma (requires outside_refs' w /\ Seq.mem w (objects zero_addr g') /\ is_white w g')
              (ensures marker_will_reach g' sp' w)
      = assert (Seq.mem w (objects zero_addr g) /\ is_white w g);
        assert (outside_refs w \/ marker_will_reach g sp w);
        assert (marker_will_reach g sp w)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires c2)

/// ---------------------------------------------------------------------------
/// Start, step, end
/// ---------------------------------------------------------------------------

let marking_inv_start g outside_refs =
  let c1 (b w: obj_addr)
    : Lemma (requires scanned_edge g scan_none b w /\ is_white w g)
            (ensures marker_will_reach g scan_none w)
    = eliminate exists (c: obj_addr). points_to g b c /\ resolve_object c g == w
      with ()
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (c1 b))

let no_black_tri_color g = ()

/// The invariant with no partly scanned object, in the stop-the-world form.
let inv0 (g: heap) (outside_refs: obj_addr -> prop) : prop =
  well_formed_heap g /\
  (forall (b w: obj_addr).
     Seq.mem b (objects zero_addr g) /\ is_black b g /\ field_edge g b w /\ is_white w g ==> mwr0 g w) /\
  (forall (w: obj_addr). outside_refs w /\ Seq.mem w (objects zero_addr g) /\ is_white w g ==> mwr0 g w)

let inv_none (g: heap) (outside_refs: obj_addr -> prop)
  : Lemma (marking_inv g outside_refs scan_none <==> inv0 g outside_refs)
  = FStar.Classical.forall_intro (mwr_none g);
    FStar.Classical.forall_intro_2 (scan_none_edges g)

let marking_inv_step g outside_refs x =
  let g2 = mark_step_at g x in
  inv_none g outside_refs;
  inv_none g2 outside_refs;
  mark_step_at_wf g x;
  mark_step_at_objects g x;
  let c1 (b w: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g2) /\ is_black b g2 /\ field_edge g2 b w /\ is_white w g2)
            (ensures mwr0 g2 w)
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
    : Lemma (requires outside_refs w /\ Seq.mem w (objects zero_addr g2) /\ is_white w g2)
            (ensures mwr0 g2 w)
    = step_white g x w;
      reach_step g x w
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires c2)

/// With nothing grey, the marker will reach nothing.
let nothing_to_reach (g: heap) (sp: scan_pos) (w: obj_addr)
  : Lemma (requires Mark.noGreyObjects g)
          (ensures ~(marker_will_reach g sp w))
  = FStar.Classical.move_requires (marker_will_reach_elim g sp) w

let marking_done g outside_refs sp =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (nothing_to_reach g sp));
  let tc (b c: obj_addr)
    : Lemma (requires Seq.mem b (objects zero_addr g) /\ is_black b g /\ ~(is_no_scan b g) /\ points_to g b c)
            (ensures ~(is_white (resolve_object c g) g))
    = assert (field_edge g b (resolve_object c g));
      assert (scanned_edge g sp b (resolve_object c g))
  in
  let tc' (b c: obj_addr)
    : Lemma (Seq.mem b (objects zero_addr g) ==> is_black b g ==> ~(is_no_scan b g) ==> points_to g b c ==>
             ~(is_white (resolve_object c g) g))
    = FStar.Classical.move_requires (tc b) c
  in
  FStar.Classical.forall_intro_2 tc';
  assert (Mark.tri_color_invariant g)

let marking_done_sweep_start g outside_refs sp fp =
  marking_done g outside_refs sp;
  SPI.sweep_inv_incremental_start g fp

/// ---------------------------------------------------------------------------
/// The partly scanned object
/// ---------------------------------------------------------------------------

let obj_val (x: obj_addr) : Lemma (is_val_addr x) = ()

let marking_inv_begin g outside_refs sp x =
  let sp' : scan_pos = { cur = x; fld = 1 } in
  wf_parts ();
  obj_val x;
  let hyp (s t: obj_addr)
    : Lemma (requires grey_or_white g s /\ grey_or_white g t /\ unscanned_edge g sp s t)
            (ensures unscanned_edge g sp' s t)
    = if s = x then field_edge_fields g s t
  in
  FStar.Classical.forall_intro_2 (fun s -> FStar.Classical.move_requires (hyp s));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (reach_change g g sp sp'));
  inv_transfer g g outside_refs outside_refs sp sp'

let marking_inv_advance g outside_refs sp x =
  let sp' = { sp with fld = sp.fld + 1 } in
  let hyp (s t: obj_addr)
    : Lemma (requires grey_or_white g s /\ grey_or_white g t /\ unscanned_edge g sp s t)
            (ensures unscanned_edge g sp' s t \/ is_gray t g)
    = if s = x then begin
        eliminate exists (k: nat). sp.fld <= k /\ field_edge_at g x k t
        with if k = sp.fld then Mark.colors_exclusive t g
      end
  in
  FStar.Classical.forall_intro_2 (fun s -> FStar.Classical.move_requires (hyp s));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (reach_change g g sp sp'));
  let sc (b t: obj_addr)
    : Lemma (requires scanned_edge g sp' b t /\ is_white t g) (ensures scanned_edge g sp b t)
    = if FStar.IndefiniteDescription.strong_excluded_middle
           (Seq.mem b (objects zero_addr g) /\ is_black b g /\ field_edge g b t) then ()
      else eliminate exists (k: nat). k < sp'.fld /\ field_edge_at g b k t
           with assert (k <> sp.fld)
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (sc b));
  inv_transfer g g outside_refs outside_refs sp sp'

/// A block whose fields are all scanned has no unscanned edge.
let all_scanned_no_edge (g: heap) (sp: scan_pos) (x y: obj_addr)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\ all_scanned g sp x)
          (ensures ~(unscanned_edge g sp x y) /\
                   (field_edge g x y ==> x == sp.cur /\ (exists (k: nat). k < sp.fld /\ field_edge_at g x k y)))
  = field_edge_fields g x y

/// What blackening `x` keeps: the walk, well-formedness, every other block's
/// colours, every edge.
let black_setup_any (g: heap) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ is_gray x g)
          (ensures (let g' = makeBlack x g in
                    well_formed_heap g' /\ objects zero_addr g' == objects zero_addr g /\
                    is_black x g' /\ ~(is_white x g') /\ ~(is_gray x g') /\ ~(is_blue x g') /\
                    (forall (y: obj_addr). y <> x ==>
                       ((is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                        (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))))
  = let g' = makeBlack x g in
    makeBlack_eq x g; makeBlack_is_black x g;
    Mark.colors_exclusive x g';
    Mark.color_change_preserves_wf g x Header.Black;
    color_change_preserves_objects g x Header.Black;
    let col (y: obj_addr)
      : Lemma (y <> x ==> ((is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                           (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))
      = if y <> x then cc_colours x y g Header.Black
    in
    FStar.Classical.forall_intro col

#push-options "--z3rlimit 20"
let marking_inv_blacken g outside_refs sp x =
  let g' = makeBlack x g in
  let sp' = blackened_pos sp x in
  black_setup_any g x;
  makeBlack_eq x g;
  wf_parts ();
  let edges (u v: obj_addr)
    : Lemma (requires Seq.mem u (objects zero_addr g))
            (ensures (unscanned_edge g' sp u v <==> unscanned_edge g sp u v) /\
                     ((u == sp.cur /\ (exists (k: nat). k < sp.fld /\ field_edge_at g' u k v)) <==>
                      (u == sp.cur /\ (exists (k: nat). k < sp.fld /\ field_edge_at g u k v))) /\
                     (field_edge g' u v <==> field_edge g u v))
    = cc_edges g x Header.Black sp u v
  in
  // what the marker would reach (if still white) it still will: a path
  // cannot go through `x`, which has no unscanned edge
  let reach (w: obj_addr)
    : Lemma (requires marker_will_reach g sp w /\ is_white w g')
            (ensures marker_will_reach g' sp' w)
    = eliminate exists (a: obj_addr). is_gray a g /\ reach_within (unscanned_edge g sp) (grey_or_white g) a w
      with begin
        reach_within_without (unscanned_edge g sp) (grey_or_white g) x a w;
        FStar.Classical.forall_intro (FStar.Classical.move_requires (all_scanned_no_edge g sp x));
        let p = without (grey_or_white g) x in
        reach_within_ends (unscanned_edge g sp) p a w;
        let pm (v: obj_addr) : Lemma (requires p v) (ensures grey_or_white g' v) = () in
        FStar.Classical.forall_intro (FStar.Classical.move_requires pm);
        let em (u v: obj_addr)
          : Lemma (requires p u /\ p v /\ unscanned_edge g sp u v) (ensures unscanned_edge g' sp' u v)
          = edges u v
        in
        FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (em u));
        reach_within_mono (unscanned_edge g sp) (unscanned_edge g' sp') p (grey_or_white g') a w
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires reach);
  let sc (b t: obj_addr)
    : Lemma (requires scanned_edge g' sp' b t /\ is_white t g') (ensures scanned_edge g sp b t)
    = if b = x then begin
        edges x t;
        all_scanned_no_edge g sp x t
      end else if FStar.IndefiniteDescription.strong_excluded_middle
                (Seq.mem b (objects zero_addr g') /\ is_black b g' /\ field_edge g' b t) then
        edges b t
      else begin
        assert (b == sp.cur);
        edges b t
      end
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (sc b));
  inv_transfer g g' outside_refs outside_refs sp sp'
#pop-options

/// ---------------------------------------------------------------------------
/// Other changes
/// ---------------------------------------------------------------------------

let marking_inv_change g g' outside_refs outside_refs' sp =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (reach_change g g' sp sp));
  inv_transfer g g' outside_refs outside_refs' sp sp

/// What greying a white object keeps: the walk, well-formedness, every edge
/// out of a block, and every other block's colours.
let grey_setup (g: heap) (w: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem w (objects zero_addr g) /\ is_white w g)
          (ensures (let g' = makeGray w g in
                    well_formed_heap g' /\ objects zero_addr g' == objects zero_addr g /\
                    is_gray w g' /\ ~(is_white w g') /\ ~(is_black w g') /\ ~(is_blue w g') /\
                    ~(is_black w g) /\ ~(is_blue w g) /\ ~(is_gray w g) /\
                    (forall (y: obj_addr). y <> w ==>
                       ((is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                        (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))))
  = let g' = makeGray w g in
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
    FStar.Classical.forall_intro col

/// Greying keeps every scanned and unscanned edge out of a block.
let grey_edges (g: heap) (w: obj_addr) (sp: scan_pos) (u v: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem w (objects zero_addr g) /\ is_white w g /\
                    Seq.mem u (objects zero_addr g))
          (ensures (unscanned_edge (makeGray w g) sp u v <==> unscanned_edge g sp u v) /\
                   (scanned_edge (makeGray w g) sp u v <==> scanned_edge g sp u v))
  = grey_setup g w;
    makeGray_eq w g;
    cc_edges g w Header.Gray sp u v

let grey_reach (g: heap) (w: obj_addr) (sp: scan_pos)
  : Lemma (requires well_formed_heap g /\ Seq.mem w (objects zero_addr g) /\ is_white w g)
          (ensures change_hyps g (makeGray w g) sp sp)
  = grey_setup g w;
    let e (s t: obj_addr)
      : Lemma (requires grey_or_white g s /\ unscanned_edge g sp s t)
              (ensures unscanned_edge (makeGray w g) sp s t)
      = grey_edges g w sp s t
    in
    FStar.Classical.forall_intro_2 (fun s -> FStar.Classical.move_requires (e s))

let marking_inv_grey g outside_refs sp w =
  let g' = makeGray w g in
  grey_setup g w;
  grey_reach g w sp;
  let sc (b t: obj_addr)
    : Lemma (requires scanned_edge g' sp b t) (ensures scanned_edge g sp b t)
    = if FStar.IndefiniteDescription.strong_excluded_middle (Seq.mem b (objects zero_addr g)) then
        grey_edges g w sp b t
  in
  FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (sc b));
  marking_inv_change g g' outside_refs outside_refs sp

let marker_will_reach_grey g sp w u =
  grey_reach g w sp;
  reach_change g (makeGray w g) sp sp u

/// ---------------------------------------------------------------------------
/// The invariant as well-formedness
/// ---------------------------------------------------------------------------

let header_colours (g g': heap) (x: obj_addr)
  : Lemma (requires read_word g (hd_address x) == read_word g' (hd_address x))
          (ensures is_blue x g == is_blue x g' /\ is_white x g == is_white x g')
  = color_of_object_spec x g; color_of_object_spec x g';
    is_blue_iff x g; is_blue_iff x g'; is_white_iff x g; is_white_iff x g'

let unreached_ok g0 sp =
  reveal_opaque (`%free_def_ok) free_def_ok;
  let det (g g': heap) (x: obj_addr)
    : Lemma ((is_block g x <==> is_block g' x) /\ read_word g (hd_address x) == read_word g' (hd_address x) ==>
             unreached g0 sp g x == unreached g0 sp g' x)
    = if read_word g (hd_address x) = read_word g' (hd_address x) then header_colours g g' x
  in
  FStar.Classical.forall_intro_3 det

#push-options "--z3rlimit 20"
let marking_inv_unreached g outside_refs sp =
  let un = unreached g sp in
  wf_with_parts ();
  let tgt (src dst: obj_addr)
    : Lemma (requires in_use un g src /\ scannable g src /\ points_to g src dst)
            (ensures in_use un g (resolve_object dst g) /\
                     infix_addr_wf g (objects zero_addr g) dst)
    = points_to_target_not_free free_stw g src dst;
      let t = resolve_object dst g in
      assert (field_edge g src t);
      Mark.colors_exclusive src g;
      Mark.color_exhaustive src g;
      if is_white t g then begin
        Mark.colors_exclusive t g;
        field_edge_fields g src t;
        if is_black src g then assert (scanned_edge g sp src t)
        else if FStar.IndefiniteDescription.strong_excluded_middle (scanned_edge g sp src t) then ()
        else begin
          assert (unscanned_edge g sp src t);
          if is_gray src g then reach_within_edge (unscanned_edge g sp) (grey_or_white g) src t
          else begin
            eliminate exists (x: obj_addr). is_gray x g /\ reach_within (unscanned_edge g sp) (grey_or_white g) x src
            with begin
              reach_within_edge (unscanned_edge g sp) (grey_or_white g) src t;
              reach_within_trans (unscanned_edge g sp) (grey_or_white g) x src t
            end
          end
        end
      end
  in
  pointers_lead_to_non_free_intro un g tgt;
  interior_pointers_valid_intro un g tgt
#pop-options

let unreached_dark_edge g0 sp g b t =
  Mark.colors_exclusive b g;
  eliminate exists (c: obj_addr). points_to g b c /\ resolve_object c g == t
  with points_to_target_not_free (unreached g0 sp) g b c
