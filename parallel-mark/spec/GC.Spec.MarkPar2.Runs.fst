/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Runs — concrete runs of the Stage 3 model on g5
///
/// For the vacuity checks (`GC.Spec.MarkPar2.Vacuity`).  Each state is the
/// previous one stepped, so the invariant holds of it by `init_inv` and
/// `step_inv`; this module works out its shape.
///
/// Run R1: one range, S = 1, Q = 0, roots [A; B].
///     setup: A pushed; B greyed, the stack full: overflow_main
///     W0 pop A; W0 scan B (grey: nothing); W0 scan 0; W0 finish; W0 idle; W0 stop
///     Main: overflow_main set; the fix-up pushes B (grey); a new round
///     W0 pop B; W0 scan A (black: nothing); W0 finish; W0 idle; W0 stop
///     Main: no flag: done
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Runs

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar.Witness
open GC.Spec.MarkPar2.Witness
open GC.Spec.MarkPar2.Model

module HeapGraph = GC.Spec.HeapGraph
module M1 = GC.Spec.MarkPar.Model
module Own = GC.Spec.MarkPar.Own

/// ---------------------------------------------------------------------------
/// g5's objects
/// ---------------------------------------------------------------------------

let p40 (_: squash big) : hp_addr = U64.uint_to_t (za + 40)

let tl (_: squash big) : list obj_addr = Seq.seq_to_list (objects_x (p40 ()) (g5 ()))

let objs_g5 (_: squash big)
  : Lemma (objs_list (g5 ()) == vA :: obj_B () :: tl () /\
           (forall (z: obj_addr). L.memP z (tl ()) ==> z <> vA /\ z <> obj_B () /\
                                   Seq.mem z (objects zero_addr (g5 ()))))
  = objects_g5 ();
    let g = g5 () in
    Seq.lemma_seq_to_list_cons vA (Seq.cons (obj_B ()) (objects (p40 ()) g));
    Seq.lemma_seq_to_list_cons (obj_B ()) (objects (p40 ()) g);
    let aux (z: obj_addr) : Lemma (requires L.memP z (tl ()))
        (ensures z <> vA /\ z <> obj_B () /\ Seq.mem z (objects zero_addr g)) =
      GC.Spec.MarkPar2.Lists.objs_list_mem g z;
      Seq.lemma_seq_to_list_permutation (objects (p40 ()) g);
      L.mem_memP z (tl ());
      L.mem_count (tl ()) z;
      hd_address_spec z; hd_address_spec vA; hd_address_spec (obj_B ());
      Seq.mem_cons (obj_B ()) (objects (p40 ()) g);
      Seq.mem_cons vA (Seq.cons (obj_B ()) (objects (p40 ()) g))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Colours along a run
/// ---------------------------------------------------------------------------

/// h is g5 with only A's and B's colours changed, never to or from blue.
let ab (_: squash big) (h: heap) : prop =
  recoloured (g5 ()) h /\
  (forall (z: obj_addr). z <> vA /\ z <> obj_B () ==> color_of_object z h == color_of_object z (g5 ()))

let ab_g5 (_: squash big) : Lemma (ab () (g5 ()))
  = g5_pre_roots () []; recoloured_refl (g5 ())

let paint (_: squash big) (h: heap) (x: obj_addr) (c: color)
  : Lemma (requires ab () h /\ (x == vA \/ x == obj_B ()) /\ (c == Gray \/ c == Black))
          (ensures ab () (set_object_color x h c) /\ color_of_object x (set_object_color x h c) == c /\
                   (forall (y: obj_addr). y <> x ==>
                      color_of_object y (set_object_color x h c) == color_of_object y h))
  = objects_g5 ();
    facts_g5 () x;
    recoloured_blue (g5 ()) h x;
    recoloured_set (g5 ()) h x c;
    color_of_object_spec x (set_object_color x h c);
    if c = Gray then begin makeGray_eq x h; makeGray_spec x h end
    else begin makeBlack_eq x h; makeBlack_spec x h end;
    read_write_same h (hd_address x) (colorHeader (read_word h (hd_address x)) c);
    colorHeader_getColor (read_word h (hd_address x)) c;
    let oth (y: obj_addr) : Lemma (requires y <> x)
        (ensures color_of_object y (set_object_color x h c) == color_of_object y h) =
      color_change_preserves_other_color x y h c in
    FStar.Classical.forall_intro (FStar.Classical.move_requires oth)


/// ---------------------------------------------------------------------------
/// Reading a heap that is g5 recoloured at A and B
/// ---------------------------------------------------------------------------

let view (_: squash big) (h: heap)
  : Lemma (requires ab () h)
          (ensures (let b = obj_B () in
                    resolve_x vA h == vA /\ resolve_x b h == b /\
                    wosize_x vA h == 2UL /\ wosize_x b h == 1UL /\
                    is_no_scan_x vA h == false /\ is_no_scan_x b h == false /\
                    get_field_x h vA 1UL == vB /\ get_field_x h vA 2UL == 0UL /\
                    get_field_x h b 1UL == vA /\
                    HeapGraph.is_pointer_field vB /\ HeapGraph.is_pointer_field vA /\
                    ~(HeapGraph.is_pointer_field 0UL) /\
                    objs_list h == vA :: b :: tl ()))
  = let g = g5 () in
    let b = obj_B () in
    objects_g5 ();
    facts_g5 () vA; facts_g5 () b;
    resolve_non_infix vA g; resolve_non_infix b g;
    recoloured_wosize g h vA; recoloured_wosize g h b;
    recoloured_no_scan g h vA; recoloured_no_scan g h b;
    fields_g5 ();
    objs_g5 ()

/// The colours a predicate reads, from color_of_object.
let colors_of (h: heap) (x: obj_addr) (c: color)
  : Lemma (requires color_of_object x h == c)
          (ensures is_white_x x h == (c = White) /\ is_gray_x x h == (c = Gray) /\
                   is_black_x x h == (c = Black))
  = is_white_iff x h; is_gray_iff x h; is_black_iff x h

/// An object of the tail is white in every such heap.
let tl_white (_: squash big) (h: heap) (z: obj_addr)
  : Lemma (requires ab () h /\ L.memP z (tl ()))
          (ensures ~(is_gray z h) /\ ~(is_black z h))
  = objs_g5 ();
    facts_g5 () z;
    color_of_object_spec z (g5 ());
    is_gray_iff z h; is_black_iff z h;
    is_white_iff z (g5 ())

/// The walk passes over the tail without change.
let rec walk_tl (k: cfg) (f: fx) (l: list obj_addr)
  : Lemma (requires forall (z: obj_addr). L.memP z l ==> ~(is_gray z f.fh) /\ ~(is_black z f.fh))
          (ensures fix_walk k f l == f) (decreases l)
  = match l with [] -> () | _ :: r -> walk_tl k f r

let walk_tl_ab (_: squash big) (k: cfg) (f: fx)
  : Lemma (requires ab () f.fh) (ensures fix_walk k f (tl ()) == f)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (tl_white () f.fh));
    walk_tl k f (tl ())
