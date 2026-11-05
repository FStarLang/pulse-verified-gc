/// ---------------------------------------------------------------------------
/// GC.SPOT.MarkPhase - incremental marking's invariant on small concrete heaps
/// ---------------------------------------------------------------------------
///
/// Two four-object heaps built by `GC.SPOT.MarkPhaseHeap` (one field each,
/// then a free block to the end of the heap).
///
/// **1. A mid-mark heap where the invariant holds with a black-to-white
/// edge** (`mid_mark_inv`, `mid_mark_step`).  Objects B (black), G (grey),
/// W1 (white), W (white); B -> W, G -> W1, W1 -> W, and W1 is held from
/// outside the major heap (`held_w1`).  The black object B points at the
/// white object W, so the heap is not strongly tri-coloured, but the marker
/// will reach W: from the grey object G through the white object W1.  So
/// `marking_inv` holds, and the clause about black objects is used, not
/// vacuous.  One mark step at G keeps it (`marking_inv_step`); concretely the
/// step blackens G and greys W1 and leaves W white (`mid_mark_step_colours`).
///
/// **2. Why a path through a black object does not count**
/// (`through_black_*`).  Objects G (grey), B (black), W1 (white), W (white);
/// G -> B and B -> W.  The weaker property "every white object a black one
/// points at is reachable from some grey object, through any objects"
/// (`reachable_from_grey_inv`) holds: G -> B -> W.  But the marker never
/// scans B again, so it will not reach W: `marker_will_reach` fails for W and
/// `marking_inv` fails (`through_black_not_inv`).  And indeed the next mark
/// step at G (its only child B is not white) leaves no grey object and the
/// edge B -> W to a white object: the weaker property no longer holds and
/// marking would stop with W white although B points at it
/// (`through_black_step_breaks`).

module GC.SPOT.MarkPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within
open GC.Spec.MarkPhase

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module H = GC.SPOT.MarkPhaseHeap

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// All the facts of a `heap4` heap.
let heap_facts (r: unit{H.room}) (col: H.idx -> H.ccol) (tg: H.idx -> H.tgt)
  : Lemma (let h = H.heap4 r col tg in
           well_formed_heap h /\ Seq.mem (H.free_obj r) (objects zero_addr h) /\
           is_blue (H.free_obj r) h /\ ~(is_black (H.free_obj r) h) /\
           ~(is_gray (H.free_obj r) h) /\ ~(is_white (H.free_obj r) h) /\
           (forall (i: H.idx).
              Seq.mem (H.obj r i) (objects zero_addr h) /\
              (is_black (H.obj r i) h <==> col i == Header.Black) /\
              (is_gray (H.obj r i) h <==> col i == Header.Gray) /\
              (is_white (H.obj r i) h <==> col i == Header.White) /\
              ~(is_blue (H.obj r i) h) /\ ~(is_no_scan (H.obj r i) h) /\ ~(is_infix (H.obj r i) h) /\
              resolve_object (H.obj r i) h == H.obj r i /\
              wosize_of_object (H.obj r i) h == 1UL /\
              read_word h (H.obj r i) == H.fv r (tg i)) /\
           (forall (i: H.idx) (y: obj_addr). field_edge h (H.obj r i) y <==> (tg i <> 0 /\ y == H.obj r (tg i))) /\
           (forall (i: H.idx) (c: obj_addr). points_to h (H.obj r i) c <==> (tg i <> 0 /\ c == H.obj r (tg i))) /\
           (forall (x: obj_addr). Seq.mem x (objects zero_addr h) <==>
              (x == H.obj r 1 \/ x == H.obj r 2 \/ x == H.obj r 3 \/ x == H.obj r 4 \/ x == H.free_obj r)))
  = H.wf r col tg;
    H.free_facts r col tg;
    FStar.Classical.forall_intro (H.obj_facts r col tg);
    FStar.Classical.forall_intro_2 (H.field_edge_iff r col tg);
    FStar.Classical.forall_intro_2 (H.points_to_iff r col tg);
    FStar.Classical.forall_intro (H.object_cases r col tg)

/// ---------------------------------------------------------------------------
/// 1. A mid-mark heap with a black-to-white edge
/// ---------------------------------------------------------------------------

/// B = 1 (black), G = 2 (grey), W1 = 3 (white), W = 4 (white).
let mid_col (i: H.idx) : H.ccol =
  if i = 1 then Header.Black else if i = 2 then Header.Gray else Header.White

/// B -> W, G -> W1, W1 -> W, W -> nothing.
let mid_tg (i: H.idx) : H.tgt = if i = 1 then 4 else if i = 2 then 3 else if i = 3 then 4 else 0

let mid (r: unit{H.room}) : heap = H.heap4 r mid_col mid_tg

/// W1 is held from outside the major heap.
let held_w1 (r: unit{H.room}) : obj_addr -> prop = fun w -> w == H.obj r 3

/// The black object B points at the white object W: not strongly tri-coloured.
let mid_black_to_white (r: unit{H.room})
  : Lemma (let h = mid r in
           is_black (H.obj r 1) h /\ field_edge h (H.obj r 1) (H.obj r 4) /\ is_white (H.obj r 4) h /\
           ~(Mark.tri_color_invariant h))
  = heap_facts r mid_col mid_tg

/// The marker will reach W1 (from G) and W (from G, through W1).
let mid_reach (r: unit{H.room})
  : Lemma (marker_will_reach (mid r) (H.obj r 3) /\ marker_will_reach (mid r) (H.obj r 4))
  = let h = mid r in
    heap_facts r mid_col mid_tg;
    let e = field_edge h in
    let p = grey_or_white h in
    reach_within_edge e p (H.obj r 3) (H.obj r 4);
    reach_within_cons e p (H.obj r 2) (H.obj r 3) (H.obj r 4);
    reach_within_edge e p (H.obj r 2) (H.obj r 3)

#push-options "--z3rlimit 20"
let mid_mark_inv (r: unit{H.room})
  : Lemma (marking_inv (mid r) (held_w1 r))
  = let h = mid r in
    heap_facts r mid_col mid_tg;
    mid_reach r
#pop-options

/// One mark step at G keeps the invariant.
let mid_mark_step (r: unit{H.room})
  : Lemma (marking_inv (mark_step_at (mid r) (H.obj r 2)) (held_w1 r))
  = heap_facts r mid_col mid_tg;
    mid_mark_inv r;
    marking_inv_step (mid r) (held_w1 r) (H.obj r 2)

/// ---------------------------------------------------------------------------
/// Blackening an object whose only field points at `child`
/// ---------------------------------------------------------------------------

/// After `makeBlack o h`, the field of `o` and the target it resolves to are
/// those of `h`.
let black_field (h: heap) (o child: obj_addr)
  : Lemma (requires U64.v o + 8 <= heap_size /\ read_word h o == child /\
                    resolve_object child h == child)
          (ensures (let g1 = makeBlack o h in
                    HeapGraph.get_field g1 o 1UL == child /\ resolve_object child g1 == child))
  = let g1 = makeBlack o h in
    makeBlack_spec o h;
    hd_address_spec o;
    read_write_different h (hd_address o) o (colorHeader (read_word h (hd_address o)) Header.Black);
    makeBlack_eq o h;
    color_change_preserves_resolve o child h Header.Black

/// A colour change elsewhere keeps the four colour predicates.
let other_colours (o y: obj_addr) (h: heap) (c: color)
  : Lemma (requires o <> y)
          (ensures (let h' = set_object_color o h c in
                    (is_black y h' <==> is_black y h) /\ (is_white y h' <==> is_white y h) /\
                    (is_gray y h' <==> is_gray y h) /\ (is_blue y h' <==> is_blue y h)))
  = let h' = set_object_color o h c in
    color_change_preserves_other_color o y h c;
    is_black_iff y h; is_black_iff y h';
    is_white_iff y h; is_white_iff y h';
    is_gray_iff y h; is_gray_iff y h';
    is_blue_iff y h; is_blue_iff y h'

/// The step at G in the mid-mark heap: G black, W1 grey, B black, W white.
#push-options "--fuel 1 --z3rlimit 20"
let mid_mark_step_colours (r: unit{H.room})
  : Lemma (let h' = mark_step_at (mid r) (H.obj r 2) in
           is_black (H.obj r 1) h' /\ is_black (H.obj r 2) h' /\
           is_gray (H.obj r 3) h' /\ is_white (H.obj r 4) h')
  = let h = mid r in
    heap_facts r mid_col mid_tg;
    let g = H.obj r 2 in
    let w1 = H.obj r 3 in
    let g1 = makeBlack g h in
    black_field h g w1;
    makeBlack_eq g h; makeBlack_is_black g h;
    other_colours g w1 h Header.Black;
    other_colours g (H.obj r 1) h Header.Black;
    other_colours g (H.obj r 4) h Header.Black;
    assert (HeapGraph.is_pointer_field w1);
    assert (mark_step_at h g == makeGray w1 g1);
    makeGray_eq w1 g1; makeGray_is_gray w1 g1;
    other_colours w1 g g1 Header.Gray;
    other_colours w1 (H.obj r 1) g1 Header.Gray;
    other_colours w1 (H.obj r 4) g1 Header.Gray
#pop-options

/// ---------------------------------------------------------------------------
/// 2. A path through a black object does not count
/// ---------------------------------------------------------------------------

/// G = 1 (grey), B = 2 (black), W1 = 3 (white), W = 4 (white).
let thr_col (i: H.idx) : H.ccol =
  if i = 1 then Header.Gray else if i = 2 then Header.Black else Header.White

/// G -> B, B -> W.
let thr_tg (i: H.idx) : H.tgt = if i = 1 then 2 else if i = 2 then 4 else 0

let thr (r: unit{H.room}) : heap = H.heap4 r thr_col thr_tg

/// The weaker property: every white object a black one points at is
/// reachable from a grey object, through any blocks.
let reachable_from_grey_inv (g: heap) : prop =
  forall (b w: obj_addr).
    Seq.mem b (objects zero_addr g) /\ is_black b g /\ field_edge g b w /\ is_white w g ==>
    (exists (x: obj_addr). is_gray x g /\
       reach_within (field_edge g) (fun v -> Seq.mem v (objects zero_addr g)) x w)

/// It holds: G -> B -> W.
#push-options "--z3rlimit 20"
let through_black_reachable (r: unit{H.room})
  : Lemma (reachable_from_grey_inv (thr r))
  = let h = thr r in
    heap_facts r thr_col thr_tg;
    let e = field_edge h in
    let p : obj_addr -> prop = fun (v: obj_addr) -> Seq.mem v (objects zero_addr h) in
    reach_within_edge e p (H.obj r 2) (H.obj r 4);
    reach_within_cons e p (H.obj r 1) (H.obj r 2) (H.obj r 4)
#pop-options

/// No path of grey or white blocks leaves G: its only successor is B.
#push-options "--fuel 2"
let no_path (r: unit{H.room}) (l: list obj_addr)
  : Lemma (~(path_within (field_edge (thr r)) (grey_or_white (thr r)) (H.obj r 1) (H.obj r 4) l))
  = heap_facts r thr_col thr_tg
#pop-options

/// The marker will not reach W, so the invariant fails, whatever is held.
let through_black_not_reached (r: unit{H.room})
  : Lemma (~(marker_will_reach (thr r) (H.obj r 4)))
  = let h = thr r in
    heap_facts r thr_col thr_tg;
    let aux (x: obj_addr)
      : Lemma (requires is_gray x h /\ reach_within (field_edge h) (grey_or_white h) x (H.obj r 4))
              (ensures False)
      = reach_within_ends (field_edge h) (grey_or_white h) x (H.obj r 4);
        assert (x == H.obj r 1);
        eliminate exists (l: list obj_addr).
          path_within (field_edge h) (grey_or_white h) (H.obj r 1) (H.obj r 4) l
        with no_path r l
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let through_black_not_inv (r: unit{H.room}) (held: obj_addr -> prop)
  : Lemma (~(marking_inv (thr r) held))
  = let h = thr r in
    heap_facts r thr_col thr_tg;
    through_black_not_reached r;
    assert (Seq.mem (H.obj r 2) (objects zero_addr h) /\ is_black (H.obj r 2) h /\
            field_edge h (H.obj r 2) (H.obj r 4) /\ is_white (H.obj r 4) h);
    assert (weak_tri_color h ==> marker_will_reach h (H.obj r 4))

/// The step at G is just blackening G: its only child B is not white.  It
/// leaves no grey object, and B -> W to a white object.
#push-options "--fuel 1 --z3rlimit 20"
let through_black_step (r: unit{H.room})
  : Lemma (let h = thr r in
           let h' = mark_step_at h (H.obj r 1) in
           h' == makeBlack (H.obj r 1) h /\
           Mark.noGreyObjects h' /\
           Seq.mem (H.obj r 2) (objects zero_addr h') /\
           is_black (H.obj r 2) h' /\ ~(is_no_scan (H.obj r 2) h') /\
           points_to h' (H.obj r 2) (H.obj r 4) /\
           resolve_object (H.obj r 4) h' == H.obj r 4 /\
           field_edge h' (H.obj r 2) (H.obj r 4) /\ is_white (H.obj r 4) h')
  = let h = thr r in
    heap_facts r thr_col thr_tg;
    let g = H.obj r 1 in
    let b = H.obj r 2 in
    let w = H.obj r 4 in
    let g1 = makeBlack g h in
    black_field h g b;
    makeBlack_eq g h; makeBlack_is_black g h;
    other_colours g b h Header.Black;
    other_colours g (H.obj r 3) h Header.Black;
    other_colours g w h Header.Black;
    other_colours g (H.free_obj r) h Header.Black;
    assert (HeapGraph.is_pointer_field b);
    assert (mark_step_at h g == g1);
    color_change_preserves_objects h g Header.Black;
    color_change_preserves_points_to_other h g Header.Black b w;
    color_change_preserves_resolve g w h Header.Black;
    color_change_preserves_other_is_no_scan g b h Header.Black;
    Mark.colors_exclusive g g1;
    assert (field_edge g1 b w)
#pop-options

let through_black_step_breaks (r: unit{H.room})
  : Lemma (let h' = mark_step_at (thr r) (H.obj r 1) in
           Mark.noGreyObjects h' /\
           ~(reachable_from_grey_inv h') /\ ~(Mark.tri_color_invariant h'))
  = let h' = mark_step_at (thr r) (H.obj r 1) in
    through_black_step r;
    let no (x: obj_addr)
      : Lemma (requires is_gray x h' /\
                        reach_within (field_edge h') (fun v -> Seq.mem v (objects zero_addr h')) x (H.obj r 4))
              (ensures False)
      = reach_within_ends (field_edge h') (fun v -> Seq.mem v (objects zero_addr h')) x (H.obj r 4)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires no)
