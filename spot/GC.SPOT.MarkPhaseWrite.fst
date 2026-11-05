/// ---------------------------------------------------------------------------
/// GC.SPOT.MarkPhaseWrite - the deletion barrier on a concrete mid-mark heap
/// ---------------------------------------------------------------------------
///
/// The mid-mark heap of `GC.SPOT.MarkPhase`: B (black), G (grey), W1 (white),
/// W (white); B -> W, G -> W1, W1 -> W; W1 held from outside.  The program
/// overwrites G's only field with an immediate, cutting G -> W1.
///
///   * **Without the barrier the invariant breaks** (`unbarriered_write_breaks`):
///     G was the only grey object and loses its only edge, so the marker
///     will reach nothing, yet W1 is white and held.
///   * **With the barrier it holds** (`barrier_write_inv`): the barrier greys
///     W1 first (`darken` of the old value is `makeGray W1`,
///     `barrier_greys_w1`), and `marking_write_barrier` applies.  So the
///     barrier's hypotheses are met and its conclusion is not vacuous: the
///     only reason the invariant survives is that W1 was greyed.

module GC.SPOT.MarkPhaseWrite

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within
open GC.Spec.MarkPhase

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module H = GC.SPOT.MarkPhaseHeap
module S = GC.SPOT.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module SPM = GC.Spec.SweepPhase.Mutator

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// G's field: the word at G.
let slot (r: unit{H.room}) : hp_addr = H.obj r 2

/// The write is a program write: G is a non-free, scannable, non-closure
/// block, the slot is its only field, and an immediate is storable.
#push-options "--z3rlimit 20"
let write_ok_mid (r: unit{H.room})
  : Lemma (SPM.program_write free_stw (S.mid r) (H.obj r 2) (slot r) 0UL /\
           ~(is_no_scan (H.obj r 2) (S.mid r)))
  = S.heap_facts r S.mid_col S.mid_tg;
    let g = S.mid r in
    H.obj_facts r S.mid_col S.mid_tg 2;
    assert (~(is_closure (H.obj r 2) g));
    assert (SPM.in_body g (H.obj r 2) (slot r))

let write_ok (r: unit{H.room}) (h: heap)
  : Lemma (requires h == S.mid r \/ h == makeGray (H.obj r 3) (S.mid r))
          (ensures SPM.program_write free_stw h (H.obj r 2) (slot r) 0UL /\
                   ~(is_no_scan (H.obj r 2) h))
  = write_ok_mid r;
    S.heap_facts r S.mid_col S.mid_tg;
    let g = S.mid r in
    let w1 = H.obj r 3 in
    makeGray_eq w1 g;
    color_change_preserves_objects g w1 Header.Gray;
    color_change_preserves_wosize_any w1 (H.obj r 2) g Header.Gray;
    color_change_preserves_is_closure w1 (H.obj r 2) g Header.Gray;
    color_change_preserves_other_is_no_scan w1 (H.obj r 2) g Header.Gray;
    S.other_colours w1 (H.obj r 2) g Header.Gray
#pop-options

/// The barrier greys W1: the old value is W1, a white block.
let barrier_greys_w1 (r: unit{H.room})
  : Lemma (MM.darken (S.mid r) (read_word (S.mid r) (slot r)) == makeGray (H.obj r 3) (S.mid r))
  = S.heap_facts r S.mid_col S.mid_tg

/// **With the barrier the invariant holds.**
let barrier_write_inv (r: unit{H.room})
  : Lemma (marking_inv (write_word (makeGray (H.obj r 3) (S.mid r)) (slot r) 0UL) (S.held_w1 r))
  = S.mid_mark_inv r;
    write_ok r (S.mid r);
    barrier_greys_w1 r;
    MM.marking_write_barrier (S.mid r) (S.held_w1 r) (H.obj r 2) (slot r) 0UL

/// After the unbarriered write, G has no edge: its only field is 0.
#push-options "--z3rlimit 20"
let g_no_edge (r: unit{H.room}) (t: obj_addr)
  : Lemma (~(field_edge (write_word (S.mid r) (slot r) 0UL) (H.obj r 2) t))
  = let g = S.mid r in
    let h' = write_word g (slot r) 0UL in
    S.heap_facts r S.mid_col S.mid_tg;
    write_ok r g;
    MM.write_heads g (H.obj r 2) (slot r) 0UL;
    GC.Spec.SweepPhase.Util.part1_holds h';
    let no (c: obj_addr)
      : Lemma (requires points_to h' (H.obj r 2) c) (ensures False)
      = let field (j: nat)
          : Lemma (requires j < U64.v (wosize_of_object (H.obj r 2) h') /\ U64.v (H.obj r 2) + j * 8 + 8 <= heap_size)
                  (ensures (let w = read_word h' (U64.uint_to_t (U64.v (H.obj r 2) + j * 8)) in
                            is_pointer w ==> False))
          = wosize_of_object_spec (H.obj r 2) g;
            wosize_of_object_spec (H.obj r 2) h';
            assert (j == 0);
            assert (U64.uint_to_t (U64.v (H.obj r 2) + j * 8) == slot r);
            read_write_same g (slot r) 0UL
        in
        pointer_from_field h' (H.obj r 2) c (fun _ -> False) field
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires no)
#pop-options

/// A path out of G, through grey or white blocks, to W1 needs an edge out of G.
#push-options "--fuel 1"
let no_path (r: unit{H.room}) (l: list obj_addr)
  : Lemma (let h' = write_word (S.mid r) (slot r) 0UL in
           ~(path_within (field_edge h') (grey_or_white h') (H.obj r 2) (H.obj r 3) l))
  = match l with
    | [] -> ()
    | z :: _ -> g_no_edge r z
#pop-options

/// **Without the barrier the invariant breaks**: W1 is white and held, and
/// the marker will not reach it.
#push-options "--z3rlimit 20"
let unbarriered_write_breaks (r: unit{H.room})
  : Lemma (~(marking_inv (write_word (S.mid r) (slot r) 0UL) (S.held_w1 r)))
  = let g = S.mid r in
    let h' = write_word g (slot r) 0UL in
    S.heap_facts r S.mid_col S.mid_tg;
    write_ok r g;
    MM.write_heads g (H.obj r 2) (slot r) 0UL;
    let w1 = H.obj r 3 in
    let aux (x: obj_addr)
      : Lemma (requires is_gray x h' /\ reach_within (field_edge h') (grey_or_white h') x w1)
              (ensures False)
      = reach_within_ends (field_edge h') (grey_or_white h') x w1;
        assert (x == H.obj r 2);
        eliminate exists (l: list obj_addr). path_within (field_edge h') (grey_or_white h') (H.obj r 2) w1 l
        with no_path r l
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    assert (~(marker_will_reach h' w1));
    assert (Seq.mem w1 (objects zero_addr h') /\ is_white w1 h' /\ S.held_w1 r w1)
#pop-options
