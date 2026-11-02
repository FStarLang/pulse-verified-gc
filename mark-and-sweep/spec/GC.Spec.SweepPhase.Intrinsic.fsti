/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Intrinsic - the sweep phase, stated on the current heap
/// ---------------------------------------------------------------------------
///
/// An experiment (incremental-sweep-plan.md, "Open: is the ghost reference heap
/// the right sweep-phase invariant?").  `GC.Spec.FusedSweep.Phase.sweeping`
/// states the sweep phase against a ghost *reference heap* `g1`, which every
/// program action has to update.  Here the invariant is about the current heap
/// `g` and the sweep state alone:
///
///   * *pending free* (`pending g st`): the white blocks in front of the
///     cursor -- read off the heap and the cursor, no ghost heap;
///   * the heap is well formed except the pending objects
///     (`well_formed_heap_except g (pending g st)`), its walk covers the heap,
///     and the free list is exact and ascending;
///   * behind the cursor every block is white or free, no two free blocks are
///     adjacent, and `swept_tail` / `last_fragment` are as in
///     `GC.Spec.FusedSweep.Inv` (`tail_ok`, `frag_ok`, `ends_free`);
///   * in front of the cursor no block is grey.
///
/// The one ghost datum is a *set*, `pf0` (the white objects when marking
/// ended), with `pending g st ⊆ pf0` (`pending_within`); it only shrinks.
///
/// Stop-the-world, the end facts relate the result to the marked heap `g0`;
/// for those the sweep carries `stw_rel g0 g c`: the walk of `g0` reaches the
/// cursor, `g` is `g0` from the cursor on (`front_same`), every block black
/// in `g0` is still a block of `g` with the same size, tag and fields
/// (`survivors_unchanged`), and every non-free block behind the cursor was
/// black in `g0` (`behind_survivors`).

module GC.Spec.SweepPhase.Intrinsic

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Blocks and colours
/// ---------------------------------------------------------------------------

/// A block of `g`: a position of its walk that can step.
let pos (g: heap) (p: hp_addr) : bool =
  W.reaches g zero_addr (U64.v p) && W.can_step g p

let white_at (g: heap) (p: hp_addr) : bool = getColor (read_word g p) = Header.White

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// Pending free: a white object in front of the cursor.
let pending (g: heap) (st: sweep_state) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g) /\ is_white x g /\ U64.v x > U64.v st.cursor

/// Behind the cursor every block is white or free.
[@@"opaque_to_smt"]
let behind_swept (g: heap) (c: nat) : prop =
  forall (p: hp_addr). W.reaches g zero_addr (U64.v p) /\ U64.v p < c ==>
    W.can_step g p /\ (white_at g p \/ blue_at g p)

/// In front of the cursor no block is grey.
[@@"opaque_to_smt"]
let front_unswept (g: heap) (c: nat) : prop =
  forall (p: hp_addr). pos g p /\ U64.v p >= c ==>
    black_at g p \/ white_at g p \/ blue_at g p

/// **The sweep phase**, about the current heap only.
[@@"opaque_to_smt"]
let sweep_phase_inv (g: heap) (fp: U64.t) (st: sweep_state) : prop =
  let c = U64.v st.cursor in
  c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  well_formed_heap_except g (pending g st) /\
  behind_swept g c /\ front_unswept g c /\
  no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
  tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
  FLA.fl_ascending g fp

val sweep_phase_inv_elim (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st)
          (ensures (let c = U64.v st.cursor in
                    c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    well_formed_heap_except g (pending g st) /\
                    behind_swept g c /\ front_unswept g c /\
                    no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
                    tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                    FLA.fl_ascending g fp))

val behind_swept_elim (g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires behind_swept g c /\ W.reaches g zero_addr (U64.v p) /\ U64.v p < c)
          (ensures W.can_step g p /\ (white_at g p \/ blue_at g p))

/// The pending set is admissible.
val pending_ok_lemma (g: heap) (st: sweep_state) : Lemma (pending_ok g (pending g st))

/// The ghost set: every pending object is in `pf0`.
let pending_within (g: heap) (st: sweep_state) (pf0: obj_addr -> prop) : prop =
  forall (x: obj_addr). pending g st x ==> pf0 x

/// The white objects when marking ended.
let white_after_mark (g0: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g0) /\ is_white x g0

/// ---------------------------------------------------------------------------
/// Stop-the-world: the relation to the marked heap
/// ---------------------------------------------------------------------------

/// Every block black in `g0` is still a block, not free, with the same size,
/// tag and fields; only its colour may differ.
[@@"opaque_to_smt"]
let survivors_unchanged (g0 g: heap) : prop =
  forall (p: hp_addr). pos g0 p /\ black_at g0 p ==>
    pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
    getTag (read_word g p) == getTag (read_word g0 p) /\
    (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
       read_word g a == read_word g0 a)

/// Every block behind the cursor that is not free was black in `g0`.
[@@"opaque_to_smt"]
let behind_survivors (g0 g: heap) (c: nat) : prop =
  forall (p: hp_addr). pos g p /\ U64.v p < c /\ not (blue_at g p) ==> pos g0 p /\ black_at g0 p

let stw_rel (g0 g: heap) (c: nat) : prop =
  W.reaches g0 zero_addr c /\ front_same g0 g c /\
  survivors_unchanged g0 g /\ behind_survivors g0 g c

val survivors_unchanged_elim (g0 g: heap) (p: hp_addr)
  : Lemma (requires survivors_unchanged g0 g /\ pos g0 p /\ black_at g0 p)
          (ensures pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
                   getTag (read_word g p) == getTag (read_word g0 p) /\
                   (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                      read_word g a == read_word g0 a))

val behind_survivors_elim (g0 g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires behind_survivors g0 g c /\ pos g p /\ U64.v p < c /\ not (blue_at g p))
          (ensures pos g0 p /\ black_at g0 p)

/// ---------------------------------------------------------------------------
/// Objects and positions
/// ---------------------------------------------------------------------------

/// The colour predicates of an object are those of its header.
val colour_of (g: heap) (x: obj_addr)
  : Lemma (let q = hd_address x in
           (is_black x g <==> black_at g q) /\ (is_blue x g <==> blue_at g q) /\
           (is_white x g <==> white_at g q) /\
           U64.v (wosize_of_object x g) == wz_at g q /\
           tag_of_object x g == getTag (read_word g q))

/// An object of the walk is a block at its header.
val obj_pos (g: heap) (x: obj_addr)
  : Lemma (U64.v (hd_address x) == U64.v x - 8 /\
           (Seq.mem x (objects zero_addr g) <==> pos g (hd_address x)))

/// The object of a block.
let obj_of (q: hp_addr{U64.v q + 8 < heap_size}) : obj_addr = f_address q

val obj_of_facts (q: hp_addr{U64.v q + 8 < heap_size})
  : Lemma (U64.v (obj_of q) == U64.v q + 8 /\ hd_address (obj_of q) == q)

/// Two blocks at `q` with the same size, tag and fields.
let same_block (g g': heap) (q: hp_addr) : prop =
  wz_at g' q == wz_at g q /\ getTag (read_word g' q) == getTag (read_word g q) /\
  (forall (a: hp_addr). U64.v q < U64.v a /\ U64.v a < W.bnext g q ==> read_word g' a == read_word g a)

/// **Well-formedness except the pending objects, transported**: a change
/// that keeps the same not-freed objects, with the same size, tag and
/// fields, keeps the field closure.
val wf_transport (g g': heap) (pf pf': obj_addr -> prop)
  : Lemma (requires well_formed_heap_except g pf /\ well_formed_heap_part4 g' /\
                    (forall (x: obj_addr). not_freed g' pf' x <==> not_freed g pf x) /\
                    (forall (x: obj_addr). not_freed g pf x ==> same_block g g' (hd_address x)))
          (ensures well_formed_heap_except g' pf')

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

/// From the heap marking left: everything white is pending, and the
/// stop-the-world relation holds trivially.
val sweep_phase_start (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0)
          (ensures sweep_phase_inv g0 fp sweep_start /\
                   pending_within g0 sweep_start (white_after_mark g0) /\
                   stw_rel g0 g0 (U64.v sweep_start.cursor))

/// ---------------------------------------------------------------------------
/// Step
/// ---------------------------------------------------------------------------

/// **One step keeps the sweep phase**, and the pending set shrinks.  The
/// step frees only pending objects: the objects neither free nor pending are
/// the same before and after (with the same size, tag and fields).
val sweep_phase_step (g: heap) (fp: U64.t) (st: sweep_state) (pf0: obj_addr -> prop)
  : Lemma (requires sweep_phase_inv g fp st /\ pending_within g st pf0 /\
                    U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    sweep_phase_inv g' fp' st' /\
                    (forall (x: obj_addr). not_freed g' (pending g' st') x <==> not_freed g (pending g st) x) /\
                    (forall (x: obj_addr). not_freed g (pending g st) x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending g' st' x ==> pending g st x) /\
                    pending_within g' st' pf0 /\
                    U64.v st'.cursor > U64.v st.cursor /\ U64.v st'.cursor <= heap_size))

/// Stop-the-world, one step keeps the relation to the marked heap.
val sweep_phase_step_stw (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    stw_rel g0 g' (U64.v st'.cursor)))
