/// ---------------------------------------------------------------------------
/// GC.SPOT.MarkPhaseSlice - the moves of a mark slice on small concrete heaps
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.MarkPhase.Slice` splits the stop-the-world mark step into the two
/// moves an incremental mark slice makes: scanning one field of a grey
/// object (`grey_move`), and blackening a grey object once all its fields are
/// dark (`black_move`).  Two four-object heaps of `GC.SPOT.MarkPhaseHeap`
/// (one field each, then a free block):
///
/// **1. The two moves, one at a time** (`mid_scan_*`, `mid_blacken_*`).  The
/// mid-mark heap of `GC.SPOT.MarkPhase` (B black, G grey, W1 white, W white;
/// B -> W, G -> W1, W1 -> W; W1 held).  Scanning the field of G is a
/// `grey_move`: it greys W1 and leaves G grey with its field dark.  Then
/// blackening G is a `black_move` (its only field is dark).  Each keeps the
/// marking invariant (`mark_move_inv`), and the two together are mark steps
/// ending with G black and W1 grey, the colours the stop-the-world step at G
/// leaves (`GC.SPOT.MarkPhase.mid_mark_step_colours`).
///
/// **2. Why blackening asks for *every* field dark** (`par_*`).  G grey,
/// W white, G -> W, and nothing else points at W or holds it: the heap of an
/// object whose field was scanned in an earlier slice (when it held a dark
/// value) and then overwritten by the program with W.  The marking
/// invariant holds -- W is reached from G -- but G's field is not dark, so
/// no blackening is a mark move here (`par_no_black_move`).  And indeed
/// blackening G anyway breaks the invariant, whatever is held: the black G
/// points at the white W and no grey object is left to reach it
/// (`par_blacken_breaks`).  This is the counterexample `black_move`'s
/// `fields_dark` requirement rules out, and why the implementation restarts
/// the scan of a partly scanned object when the program writes into its
/// scanned prefix (`GC.Gen.MarkState`).

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

/// The only dark-field range of a one-field object: field 1.
let fields_dark_one (g: heap) (x: obj_addr)
  : Lemma (requires S.field_dark g x 1UL) (ensures S.fields_dark g x 1 1)
  = let aux (k: U64.t{U64.v k >= 1})
      : Lemma (1 <= U64.v k /\ U64.v k <= 1 ==> S.field_dark g x k)
      = if U64.v k = 1 then U64.v_inj k 1UL
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// 1. The two moves, one at a time
/// ---------------------------------------------------------------------------

/// G and W1 of the mid-mark heap.
let g_obj (r: unit{H.room}) : obj_addr = H.obj r 2
let w1_obj (r: unit{H.room}) : obj_addr = H.obj r 3

/// The heap after scanning the field of G.
let mid_scanned (r: unit{H.room}) : GTot heap = S.scan_field (MPS.mid r) (g_obj r) 1UL

/// **Scanning the field of G is a `grey_move`**: it greys W1 (white, so
/// darkened), G stays grey, and G's field is dark.
let mid_scan_move (r: unit{H.room})
  : Lemma (let h0 = MPS.mid r in
           let h1 = mid_scanned r in
           S.grey_move h0 h1 /\ S.mark_move h0 h1 /\
           h1 == makeGray (w1_obj r) h0 /\
           is_gray (g_obj r) h1 /\ is_gray (w1_obj r) h1 /\ S.field_dark h1 (g_obj r) 1UL)
  = let h0 = MPS.mid r in
    let g = g_obj r in
    let w1 = w1_obj r in
    MPS.heap_facts r MPS.mid_col MPS.mid_tg;
    field_of r MPS.mid_col MPS.mid_tg 2;
    obj_is_pointer r 3;
    assert (S.scan_target h0 g);
    S.scan_field_is_grey h0 g 1UL;
    S.scan_field_dark h0 g 1UL;
    assert (mid_scanned r == makeGray w1 h0);
    makeGray_eq w1 h0;
    makeGray_is_gray w1 h0;
    MPS.other_colours w1 g h0 Header.Gray;
    introduce exists (x: obj_addr) (k: U64.t{U64.v k >= 1}).
        S.scan_target h0 x /\ U64.v k <= U64.v (wosize_of_object x h0) /\ mid_scanned r == S.scan_field h0 x k
      with g 1UL and ()

/// The heap after blackening G.
let mid_blackened (r: unit{H.room}) : GTot heap = makeBlack (g_obj r) (mid_scanned r)

/// **Then blackening G is a `black_move`**: its only field is dark.  It
/// leaves G black and W1 grey.
let mid_blacken_move (r: unit{H.room})
  : Lemma (let h1 = mid_scanned r in
           let h2 = mid_blackened r in
           S.black_move h1 h2 /\ S.mark_move h1 h2 /\
           is_black (g_obj r) h2 /\ is_gray (w1_obj r) h2)
  = let h0 = MPS.mid r in
    let h1 = mid_scanned r in
    let g = g_obj r in
    let w1 = w1_obj r in
    MPS.heap_facts r MPS.mid_col MPS.mid_tg;
    mid_scan_move r;
    S.mark_move_darker h0 h1;
    assert (Seq.mem g (objects zero_addr h1));
    assert (wosize_of_object g h1 == 1UL);
    assert (~(is_no_scan g h1));
    fields_dark_one h1 g;
    makeBlack_eq g h1;
    makeBlack_is_black g h1;
    MPS.other_colours g w1 h1 Header.Black

/// **Each move keeps the marking invariant**, and the two are mark steps
/// from the mid-mark heap.
let mid_moves_inv (r: unit{H.room})
  : Lemma (marking_inv (mid_scanned r) (MPS.held_w1 r) /\
           marking_inv (mid_blackened r) (MPS.held_w1 r) /\
           S.mark_steps (MPS.mid r) (mid_blackened r))
  = mid_scan_move r;
    mid_blacken_move r;
    MPS.mid_mark_inv r;
    S.mark_move_inv (MPS.mid r) (mid_scanned r) (MPS.held_w1 r);
    S.mark_move_inv (mid_scanned r) (mid_blackened r) (MPS.held_w1 r);
    S.mark_steps_move (MPS.mid r) (mid_scanned r);
    S.mark_steps_snoc (MPS.mid r) (mid_scanned r) (mid_blackened r)

/// ---------------------------------------------------------------------------
/// 2. Blackening with a white field
/// ---------------------------------------------------------------------------

/// G = 1 (grey), W = 2 (white), 3 and 4 white.
let par_col (i: H.idx) : H.ccol = if i = 1 then Header.Gray else Header.White

/// G -> W, nothing else.
let par_tg (i: H.idx) : H.tgt = if i = 1 then 2 else 0

let par (r: unit{H.room}) : heap = H.heap4 r par_col par_tg

/// Nothing is held from outside the major heap.
let held_none : obj_addr -> prop = fun _ -> False

/// **The marking invariant holds**: there is no black object.
let par_inv (r: unit{H.room}) : Lemma (marking_inv (par r) held_none)
  = MPS.heap_facts r par_col par_tg

/// G's field is not dark: it points at the white W.
let par_not_dark (r: unit{H.room}) : Lemma (~(S.field_dark (par r) (H.obj r 1) 1UL))
  = MPS.heap_facts r par_col par_tg;
    field_of r par_col par_tg 1;
    obj_is_pointer r 2

/// **No blackening is a mark move**: G is the only grey object, and its
/// field is not dark.
let par_no_black_move (r: unit{H.room}) (h': heap) : Lemma (~(S.black_move (par r) h'))
  = let h = par r in
    MPS.heap_facts r par_col par_tg;
    par_not_dark r;
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr h) /\ is_gray x h /\
                        (is_no_scan x h \/ S.fields_dark h x 1 (U64.v (wosize_of_object x h))))
              (ensures False)
      = assert (x == H.obj r 1);
        assert (S.field_dark h x 1UL)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// **Blackening G anyway breaks the invariant**, whatever is held: the black
/// G points at the white W, and no grey object is left to reach it.
#push-options "--fuel 1"
let par_blacken_breaks (r: unit{H.room}) (held: obj_addr -> prop)
  : Lemma (let h' = makeBlack (H.obj r 1) (par r) in
           is_black (H.obj r 1) h' /\ is_white (H.obj r 2) h' /\
           field_edge h' (H.obj r 1) (H.obj r 2) /\ Mark.noGreyObjects h' /\
           ~(marking_inv h' held))
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
    let no (x: obj_addr)
      : Lemma (requires is_gray x h' /\ reach_within (field_edge h') (grey_or_white h') x w)
              (ensures False)
      = reach_within_ends (field_edge h') (grey_or_white h') x w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires no);
    assert (~(marker_will_reach h' w))
#pop-options
