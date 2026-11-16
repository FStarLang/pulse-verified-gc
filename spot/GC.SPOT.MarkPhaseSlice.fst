/// ---------------------------------------------------------------------------
/// GC.SPOT.MarkPhaseSlice - the moves of a mark slice on small concrete heaps
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.MarkPhase.Slice` splits the stop-the-world mark step into the
/// moves an incremental mark slice makes, on the heap and the scan position
/// (`GC.Spec.MarkPhase.scan_pos`: the partly scanned object and its next
/// field): starting to scan a grey object (`begin_move`), scanning its next
/// field (`grey_move`), and blackening an object all of whose fields are
/// scanned (`black_move`).  Three four-object heaps of
/// `GC.SPOT.MarkPhaseHeap` (one field each, then a free block):
///
/// **1. The three moves, one at a time** (`mid_*`).  The mid-mark heap of
/// `GC.SPOT.MarkPhase` (B black, G grey, W1 white, W white; B -> W, G -> W1,
/// W1 -> W; W1 referenced from outside).  Starting to scan G changes only the
/// position; scanning its field greys W1 and moves the position past it;
/// blackening G (its only field scanned) leaves no partly scanned object.
/// Each keeps the marking invariant (`mark_move_inv`), and together they are
/// mark steps ending with G black and W1 grey, the colours the
/// stop-the-world step at G leaves (`GC.SPOT.MarkPhase.mid_mark_step_colours`).
///
/// **2. Blackening asks for every field scanned** (`par_*`).  G grey, W
/// white, G -> W, and nothing else points at W.  With G's field not scanned
/// the invariant holds (`par_inv`) and no blackening is a mark move
/// (`par_no_black_move`); blackening G anyway breaks the invariant at any
/// position, whatever the outside references (`par_blacken_breaks`).  With
/// G's field counted as scanned -- the heap the program would leave by
/// writing W into a field the slice had scanned -- the invariant fails
/// (`par_scanned_not_inv`): this is the write the barrier's contract rules
/// out (`MM.target_ok`: W is not one the marker will reach).
///
/// **3. A write into a scanned field needs no restart** (`fork_*`).  G grey,
/// X grey, W white; G -> W and X -> W, G's field scanned (the position is G
/// past its only field): the program wrote W into G's scanned field, and W
/// is one the marker will reach, from X.  The invariant holds at that
/// position (`fork_inv`), and blackening G is a mark move that keeps it
/// (`fork_black_move`): the slice finishes G without scanning it again.
/// This is why the write barrier no longer restarts a partly scanned
/// object's scan, and why a program that keeps writing into it cannot keep
/// marking from finishing.

module GC.SPOT.MarkPhaseSlice

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
module S = GC.Spec.MarkPhase.Slice
module H = GC.SPOT.MarkPhaseHeap
module MPS = GC.SPOT.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// The field of object `i` of a `heap4` heap, as the marker reads it.
let field_of (r: unit{H.room}) (col: H.idx -> H.ccol) (tg: H.idx -> H.tgt) (i: H.idx)
  : Lemma (HeapGraph.get_field (H.heap4 r col tg) (H.obj r i) 1UL == H.fv r (tg i))
  = H.obj_facts r col tg i;
    hd_address_spec (H.obj r i)

/// A pointer to an object of the heap is a pointer.
let obj_is_pointer (r: unit{H.room}) (i: H.idx) : Lemma (is_pointer (H.obj r i))
  = ()

/// A field's edge on a `heap4` heap: field 1, the object's target.
let field_edge_at_iff (r: unit{H.room}) (col: H.idx -> H.ccol) (tg: H.idx -> H.tgt) (i: H.idx)
  (k: nat) (y: obj_addr)
  : Lemma (field_edge_at (H.heap4 r col tg) (H.obj r i) k y <==> (k == 1 /\ tg i <> 0 /\ y == H.obj r (tg i)))
  = MPS.heap_facts r col tg;
    field_of r col tg i;
    U64.v_inj (U64.uint_to_t 1) 1UL;
    if tg i <> 0 then obj_is_pointer r (tg i)

/// ---------------------------------------------------------------------------
/// 1. The three moves, one at a time
/// ---------------------------------------------------------------------------

/// G and W1 of the mid-mark heap.
let g_obj (r: unit{H.room}) : obj_addr = H.obj r 2
let w1_obj (r: unit{H.room}) : obj_addr = H.obj r 3

/// G partly scanned, at its first field, then past it.
let at_first (r: unit{H.room}) : scan_pos = { cur = g_obj r; fld = 1 }
let past_first (r: unit{H.room}) : scan_pos = { cur = g_obj r; fld = 2 }

/// The heap after scanning the field of G.
let mid_scanned (r: unit{H.room}) : GTot heap = S.scan_field (MPS.mid r) (g_obj r) 1UL

/// **Starting to scan G is a `begin_move`.**
let mid_begin_move (r: unit{H.room})
  : Lemma (S.begin_move (MPS.mid r) scan_none (MPS.mid r) (at_first r) /\
           S.mark_move (MPS.mid r) scan_none (MPS.mid r) (at_first r))
  = MPS.heap_facts r MPS.mid_col MPS.mid_tg;
    assert (S.scan_target (MPS.mid r) (g_obj r))

/// **Scanning the field of G is a `grey_move`**: it greys W1 (white, so
/// darkened), G stays grey, and the position moves past the field.
let mid_scan_move (r: unit{H.room})
  : Lemma (let h0 = MPS.mid r in
           let h1 = mid_scanned r in
           S.grey_move h0 (at_first r) h1 (past_first r) /\ S.mark_move h0 (at_first r) h1 (past_first r) /\
           h1 == makeGray (w1_obj r) h0 /\
           is_gray (g_obj r) h1 /\ is_gray (w1_obj r) h1)
  = let h0 = MPS.mid r in
    let g = g_obj r in
    let w1 = w1_obj r in
    MPS.heap_facts r MPS.mid_col MPS.mid_tg;
    field_of r MPS.mid_col MPS.mid_tg 2;
    obj_is_pointer r 3;
    assert (S.scan_target h0 g);
    S.scan_field_is_grey h0 g 1UL;
    assert (mid_scanned r == makeGray w1 h0);
    makeGray_eq w1 h0;
    makeGray_is_gray w1 h0;
    MPS.other_colours w1 g h0 Header.Gray;
    U64.v_inj (U64.uint_to_t 1) 1UL;
    assert (S.scan_field h0 g (U64.uint_to_t (at_first r).fld) == mid_scanned r)

/// The heap after blackening G.
let mid_blackened (r: unit{H.room}) : GTot heap = makeBlack (g_obj r) (mid_scanned r)

/// **Then blackening G is a `black_move`**: its only field is scanned.  It
/// leaves G black, W1 grey, and no partly scanned object.
let mid_blacken_move (r: unit{H.room})
  : Lemma (let h1 = mid_scanned r in
           let h2 = mid_blackened r in
           S.black_move h1 (past_first r) h2 scan_none /\ S.mark_move h1 (past_first r) h2 scan_none /\
           is_black (g_obj r) h2 /\ is_gray (w1_obj r) h2)
  = let h0 = MPS.mid r in
    let h1 = mid_scanned r in
    let g = g_obj r in
    let w1 = w1_obj r in
    MPS.heap_facts r MPS.mid_col MPS.mid_tg;
    mid_scan_move r;
    S.mark_move_darker h0 h1 (at_first r) (past_first r);
    assert (Seq.mem g (objects zero_addr h1));
    assert (wosize_of_object g h1 == 1UL);
    assert (all_scanned h1 (past_first r) g);
    assert (blackened_pos (past_first r) g == scan_none);
    makeBlack_eq g h1;
    makeBlack_is_black g h1;
    MPS.other_colours g w1 h1 Header.Black

/// **Each move keeps the marking invariant**, and the three are mark steps
/// from the mid-mark heap with nothing partly scanned to the same.
let mid_moves_inv (r: unit{H.room})
  : Lemma (marking_inv (MPS.mid r) (MPS.outside_refs_w1 r) (at_first r) /\
           marking_inv (mid_scanned r) (MPS.outside_refs_w1 r) (past_first r) /\
           marking_inv (mid_blackened r) (MPS.outside_refs_w1 r) scan_none /\
           S.mark_steps (MPS.mid r) scan_none (mid_blackened r) scan_none)
  = let h0 = MPS.mid r in
    mid_begin_move r;
    mid_scan_move r;
    mid_blacken_move r;
    MPS.mid_mark_inv r;
    S.mark_move_inv h0 h0 scan_none (at_first r) (MPS.outside_refs_w1 r);
    S.mark_move_inv h0 (mid_scanned r) (at_first r) (past_first r) (MPS.outside_refs_w1 r);
    S.mark_move_inv (mid_scanned r) (mid_blackened r) (past_first r) scan_none (MPS.outside_refs_w1 r);
    S.mark_steps_move h0 h0 scan_none (at_first r);
    S.mark_steps_snoc h0 h0 (mid_scanned r) scan_none (at_first r) (past_first r);
    S.mark_steps_snoc h0 (mid_scanned r) (mid_blackened r) scan_none (past_first r) scan_none

/// ---------------------------------------------------------------------------
/// 2. Blackening asks for every field scanned
/// ---------------------------------------------------------------------------

/// G = 1 (grey), W = 2 (white), 3 and 4 white.
let par_col (i: H.idx) : H.ccol = if i = 1 then Header.Gray else Header.White

/// G -> W, nothing else.
let par_tg (i: H.idx) : H.tgt = if i = 1 then 2 else 0

let par (r: unit{H.room}) : heap = H.heap4 r par_col par_tg

/// Nothing is referenced from outside the major heap.
let no_outside_refs : obj_addr -> prop = fun _ -> False

/// **With G's field not scanned the marking invariant holds**: there is no
/// black object.
let par_inv (r: unit{H.room}) : Lemma (marking_inv (par r) no_outside_refs scan_none)
  = MPS.heap_facts r par_col par_tg;
    FStar.Classical.forall_intro_2 (scan_none_edges (par r))

/// **No blackening is a mark move**: G is the only grey object, and its
/// field is not scanned.
let par_no_black_move (r: unit{H.room}) (h': heap) (sp': scan_pos)
  : Lemma (~(S.black_move (par r) scan_none h' sp'))
  = MPS.heap_facts r par_col par_tg

/// With G past its only field.
let par_past (r: unit{H.room}) : scan_pos = { cur = H.obj r 1; fld = 2 }

/// **With G's field counted as scanned the invariant fails**: the scanned
/// edge G -> W ends at a white object, and no unscanned edge is left for the
/// marker to reach it by.
#push-options "--fuel 1 --z3rlimit 20"
let par_scanned_not_inv (r: unit{H.room}) (outside_refs: obj_addr -> prop)
  : Lemma (~(marking_inv (par r) outside_refs (par_past r)))
  = let h = par r in
    let sp = par_past r in
    let w = H.obj r 2 in
    MPS.heap_facts r par_col par_tg;
    field_edge_at_iff r par_col par_tg 1 1 w;
    assert (scanned_edge h sp (H.obj r 1) w);
    let no_edge (x y: obj_addr) : Lemma (requires grey_or_white h x /\ unscanned_edge h sp x y) (ensures False)
      = FStar.Classical.forall_intro (fun (k: nat) -> field_edge_at_iff r par_col par_tg 1 k y)
    in
    let no (x: obj_addr)
      : Lemma (requires is_gray x h /\ reach_within (unscanned_edge h sp) (grey_or_white h) x w)
              (ensures False)
      = reach_within_ends (unscanned_edge h sp) (grey_or_white h) x w;
        assert (x == H.obj r 1);
        eliminate exists (l: list obj_addr). path_within (unscanned_edge h sp) (grey_or_white h) x w l
        with (match l with
              | [] -> ()
              | z :: _ -> no_edge x z)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires no);
    assert (~(marker_will_reach h sp w))
#pop-options

/// **Blackening G anyway breaks the invariant**, at any position and
/// whatever the outside references: the black G points at the white W, and
/// no grey object is left to reach it.
#push-options "--fuel 1"
let par_blacken_breaks (r: unit{H.room}) (outside_refs: obj_addr -> prop) (sp: scan_pos)
  : Lemma (let h' = makeBlack (H.obj r 1) (par r) in
           is_black (H.obj r 1) h' /\ is_white (H.obj r 2) h' /\
           field_edge h' (H.obj r 1) (H.obj r 2) /\ Mark.noGreyObjects h' /\
           ~(marking_inv h' outside_refs sp))
  = let h = par r in
    let g = H.obj r 1 in
    let w = H.obj r 2 in
    let h' = makeBlack g h in
    MPS.heap_facts r par_col par_tg;
    MPS.black_field h g w;
    makeBlack_eq g h;
    makeBlack_is_black g h;
    MPS.other_colours g w h Header.Black;
    MPS.other_colours g (H.obj r 3) h Header.Black;
    MPS.other_colours g (H.obj r 4) h Header.Black;
    MPS.other_colours g (H.free_obj r) h Header.Black;
    color_change_preserves_objects h g Header.Black;
    color_change_preserves_points_to_self h g Header.Black w;
    color_change_preserves_resolve g w h Header.Black;
    color_preserves_is_no_scan g h Header.Black;
    Mark.colors_exclusive g h';
    assert (points_to h' g w);
    assert (field_edge h' g w);
    assert (scanned_edge h' sp g w);
    let no (x: obj_addr)
      : Lemma (requires is_gray x h' /\ reach_within (unscanned_edge h' sp) (grey_or_white h') x w)
              (ensures False)
      = reach_within_ends (unscanned_edge h' sp) (grey_or_white h') x w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires no);
    assert (~(marker_will_reach h' sp w))
#pop-options

/// ---------------------------------------------------------------------------
/// 3. A write into a scanned field needs no restart
/// ---------------------------------------------------------------------------

/// G = 1 (grey), X = 2 (grey), W = 3 (white), 4 white.
let fork_col (i: H.idx) : H.ccol = if i = 1 || i = 2 then Header.Gray else Header.White

/// G -> W, X -> W.
let fork_tg (i: H.idx) : H.tgt = if i = 1 || i = 2 then 3 else 0

let fork (r: unit{H.room}) : heap = H.heap4 r fork_col fork_tg

/// G past its only field.
let fork_past (r: unit{H.room}) : scan_pos = { cur = H.obj r 1; fld = 2 }

/// **The invariant holds with G's scanned field pointing at the white W**:
/// the marker will reach W from X.
#push-options "--z3rlimit 20"
let fork_inv (r: unit{H.room}) : Lemma (marking_inv (fork r) no_outside_refs (fork_past r))
  = let h = fork r in
    let sp = fork_past r in
    let w = H.obj r 3 in
    MPS.heap_facts r fork_col fork_tg;
    assert (unscanned_edge h sp (H.obj r 2) w);
    reach_within_edge (unscanned_edge h sp) (grey_or_white h) (H.obj r 2) w;
    assert (marker_will_reach h sp w);
    let sc (b t: obj_addr) : Lemma (requires scanned_edge h sp b t) (ensures t == w)
      = FStar.Classical.forall_intro (fun (k: nat) -> field_edge_at_iff r fork_col fork_tg 1 k t)
    in
    FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (sc b))
#pop-options

/// **Blackening G is a mark move, and keeps the invariant**: no rescan of G.
let fork_black_move (r: unit{H.room})
  : Lemma (let h' = makeBlack (H.obj r 1) (fork r) in
           S.black_move (fork r) (fork_past r) h' scan_none /\
           marking_inv h' no_outside_refs scan_none)
  = let h = fork r in
    MPS.heap_facts r fork_col fork_tg;
    assert (all_scanned h (fork_past r) (H.obj r 1));
    assert (blackened_pos (fork_past r) (H.obj r 1) == scan_none);
    fork_inv r;
    S.mark_move_inv h (makeBlack (H.obj r 1) h) (fork_past r) scan_none no_outside_refs
