/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Intrinsic - the sweep phase, stated on the current heap
/// ---------------------------------------------------------------------------
///
/// The sweep phase (incremental-sweep-plan.md): the major collector has
/// finished marking and sweeps the heap a few blocks at a time while the
/// program runs.  The invariant is about the current heap `g` and the sweep
/// state alone -- no ghost heap:
///
///   * *pending free* (`pending_free st g`): the white blocks in front of the
///     cursor, dead but not yet freed -- read off the heap and the cursor;
///   * the heap is well formed when free means blue or pending free
///     (`well_formed_heap_with (free_incremental st) g`), so the fields of a
///     block pending free may point anywhere; its walk covers the heap, and
///     the free list is exact and ascending;
///   * behind the cursor every block is white or free, no two free blocks are
///     adjacent, and `swept_tail` / `last_fragment` are as in
///     `GC.Spec.FusedSweep.Inv` (`tail_ok`, `frag_ok`, `ends_free`);
///   * in front of the cursor no block is grey.
///
/// Everything but well-formedness is `sweep_shape`: facts about the walk,
/// the headers and the free list, which any change that keeps the walk and
/// the headers keeps (`shape_transport`).  The program's events are in
/// `GC.Gen.SweepPhase`, a minor collection mid-sweep in
/// `GC.Gen.SweepPhase.Minor`, and safety in `GC.Gen.SweepPhase.Safety`.
///
/// A sweep step frees only blocks pending free and the pending-free set only
/// shrinks (`sweep_phase_step`, `sweep_phase_steps` for a slice of `k`
/// steps).  That the blocks pending free are among the white objects marking
/// left (`pending_free_within`, `white_after_mark`) is a lemma, never carried.
///
/// Stop-the-world, the end facts relate the result to the marked heap `g0`;
/// for those the sweep carries `stw_rel g0 g c`: the walk of `g0` reaches the
/// cursor, `g` is `g0` from the cursor on (`front_same`), every block black
/// in `g0` is still a block of `g` with the same size, tag and fields
/// (`marked_unchanged`), and every non-free block behind the cursor was
/// black in `g0` (`behind_marked`).

module GC.Spec.SweepPhase.Intrinsic

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module W = GC.Spec.Walk
module FLA = GC.Spec.FreeList.Ascending
module Mark = GC.Spec.Mark
module FreeList = GC.Spec.FreeList

/// ---------------------------------------------------------------------------
/// Blocks and colours
/// ---------------------------------------------------------------------------

let white_at (g: heap) (p: hp_addr) : bool = getColor (read_word g p) = Header.White

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// Pending free: a white block in front of the cursor (its header at or above
/// it).  It is dead, and this sweep will free it when the cursor gets there.
let pending_free (st: sweep_state) (g: heap) (x: obj_addr) : GTot bool =
  is_block g x && is_white x g && U64.v x > U64.v st.cursor

/// **What counts as free during the sweep**: the blue blocks, and the blocks
/// pending free.  A block pending free is garbage left in place; nothing reads
/// its fields before the sweep frees it.
let free_incremental (st: sweep_state) : free_def =
  fun g x -> is_blue x g || pending_free st g x

/// The same, with what is pending free read at a fixed heap `g0`: across a
/// change that frees nothing and makes nothing newly pending free (a minor
/// collection), a block is free when it is blue now or was pending free in
/// `g0`; so every block allocated since is not free.
let free_incremental_from (st: sweep_state) (g0: heap) : free_def =
  fun g x -> is_blue x g || pending_free st g0 x

/// Both are definitions of free a generic theorem may take.
val free_incremental_ok (st: sweep_state) : Lemma (free_def_ok (free_incremental st))

val free_incremental_from_ok (st: sweep_state) (g0: heap) : Lemma (free_def_ok (free_incremental_from st g0))

/// A block allocated by a change from `g0` was not pending free in `g0`.
val free_incremental_from_fresh (st: sweep_state) (g0 g: heap)
  : Lemma (fresh_not_free (free_incremental_from st g0) g0 g)

/// Definitions of free that agree on the non-free blocks of a heap give the
/// same well-formedness of it.
val well_formed_heap_with_congr (free free': free_def) (g: heap)
  : Lemma (requires forall (x: obj_addr). in_use free' g x == in_use free g x)
          (ensures well_formed_heap_with free' g <==> well_formed_heap_with free g)

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
  well_formed_heap_with (free_incremental st) g /\
  behind_swept g c /\ front_unswept g c /\
  no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
  tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
  FLA.fl_ascending g fp

val sweep_phase_inv_elim (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st)
          (ensures (let c = U64.v st.cursor in
                    c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    well_formed_heap_with (free_incremental st) g /\
                    behind_swept g c /\ front_unswept g c /\
                    no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
                    tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                    FLA.fl_ascending g fp))

/// The sweep phase without well-formedness: the walk, the headers, the
/// free list and the sweep state.  These are about the walk and the headers
/// only (and the free list's links), so a change that keeps the walk and
/// every header on it keeps them (`shape_transport`).
[@@"opaque_to_smt"]
let sweep_shape (g: heap) (fp: U64.t) (st: sweep_state) : prop =
  let c = U64.v st.cursor in
  c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  behind_swept g c /\ front_unswept g c /\
  no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
  tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
  FLA.fl_ascending g fp

/// The sweep phase is its shape and well-formedness for `free_incremental`.
val sweep_phase_inv_iff (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (sweep_phase_inv g fp st <==>
           sweep_shape g fp st /\ well_formed_heap_with (free_incremental st) g)

val sweep_shape_elim (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_shape g fp st)
          (ensures (let c = U64.v st.cursor in
                    c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    behind_swept g c /\ front_unswept g c /\
                    no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
                    tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                    FLA.fl_ascending g fp))

val sweep_shape_intro (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires (let c = U64.v st.cursor in
                     c % 8 == 0 /\ c <= heap_size /\ W.reaches g zero_addr c /\
                     heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                     behind_swept g c /\ front_unswept g c /\
                     no_adjacent_free g c /\ ends_free g c (prev_free g st) /\
                     tail_ok g c st.swept_tail /\ frag_ok g c st.last_fragment /\
                     FLA.fl_ascending g fp))
          (ensures sweep_shape g fp st)

val behind_swept_intro (g: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires W.reaches g zero_addr (U64.v p) /\ U64.v p < c)
                           (ensures W.can_step g p /\ (white_at g p \/ blue_at g p))))
  : Lemma (behind_swept g c)

val front_unswept_elim (g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires front_unswept g c /\ pos g p /\ U64.v p >= c)
          (ensures black_at g p \/ white_at g p \/ blue_at g p)

val front_unswept_intro (g: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires pos g p /\ U64.v p >= c)
                           (ensures black_at g p \/ white_at g p \/ blue_at g p)))
  : Lemma (front_unswept g c)

val behind_swept_elim (g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires behind_swept g c /\ W.reaches g zero_addr (U64.v p) /\ U64.v p < c)
          (ensures W.can_step g p /\ (white_at g p \/ blue_at g p))

/// The ghost set: every object pending free is in `dead`.
let pending_free_within (g: heap) (st: sweep_state) (dead: obj_addr -> prop) : prop =
  forall (x: obj_addr). pending_free st g x ==> dead x

/// The white objects when marking ended.
let white_after_mark (g0: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g0) /\ is_white x g0

/// ---------------------------------------------------------------------------
/// Stop-the-world: the relation to the marked heap
/// ---------------------------------------------------------------------------

/// Every block black in `g0` is still a block, not free, with the same size,
/// tag and fields; only its colour may differ.
[@@"opaque_to_smt"]
let marked_unchanged (g0 g: heap) : prop =
  forall (p: hp_addr). pos g0 p /\ black_at g0 p ==>
    pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
    getTag (read_word g p) == getTag (read_word g0 p) /\
    (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
       read_word g a == read_word g0 a)

/// Every block behind the cursor that is not free was black in `g0`.
[@@"opaque_to_smt"]
let behind_marked (g0 g: heap) (c: nat) : prop =
  forall (p: hp_addr). pos g p /\ U64.v p < c /\ not (blue_at g p) ==> pos g0 p /\ black_at g0 p

let stw_rel (g0 g: heap) (c: nat) : prop =
  W.reaches g0 zero_addr c /\ front_same g0 g c /\
  marked_unchanged g0 g /\ behind_marked g0 g c

val marked_unchanged_elim (g0 g: heap) (p: hp_addr)
  : Lemma (requires marked_unchanged g0 g /\ pos g0 p /\ black_at g0 p)
          (ensures pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
                   getTag (read_word g p) == getTag (read_word g0 p) /\
                   (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                      read_word g a == read_word g0 a))

val behind_marked_elim (g0 g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires behind_marked g0 g c /\ pos g p /\ U64.v p < c /\ not (blue_at g p))
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

/// **Well-formedness, transported**: a change after which the non-free blocks
/// under `free'` are those non-free under `free` before, with the same size,
/// tag and fields, keeps the pointer clauses.
val wf_transport (g g': heap) (free free': free_def)
  : Lemma (requires well_formed_heap_with free g /\ no_infix_block g' /\ free_def_ok free' /\
                    (forall (x: obj_addr). in_use free' g' x == in_use free g x) /\
                    (forall (x: obj_addr). in_use free g x ==> same_block g g' (hd_address x)))
          (ensures well_formed_heap_with free' g')

/// ---------------------------------------------------------------------------
/// Changes that keep the walk and the headers
/// ---------------------------------------------------------------------------

/// `g'` has the walk of `g`, with the same header at every position of it.
let same_heads (g g': heap) : prop =
  (forall (b: nat). W.reaches g' zero_addr b == W.reaches g zero_addr b) /\
  (forall (q: hp_addr). W.reaches g zero_addr (U64.v q) ==> read_word g' q == read_word g q)

/// With the walk and the headers, the objects, their colours, sizes and tags,
/// the free-list cells, the pending free and allocated objects, and the blocks
/// of any admissible definition of free are the same.
val same_heads_facts (g g': heap)
  : Lemma (requires same_heads g g')
          (ensures objects zero_addr g' == objects zero_addr g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      read_word g' (hd_address x) == read_word g (hd_address x)) /\
                   (forall (x: obj_addr) (st: sweep_state). pending_free st g' x == pending_free st g x) /\
                   (forall (x: obj_addr). in_use free_stw g' x == in_use free_stw g x) /\
                   (forall (x: obj_addr) (free: free_def). free_def_ok free ==> in_use free g' x == in_use free g x) /\
                   (forall (x: U64.t). FreeList.fl_cell g' x <==> FreeList.fl_cell g x))

/// **The shape depends only on the walk, the headers and the free list.**
val shape_transport (g g': heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_shape g fp st /\ same_heads g g' /\ FLA.fl_ascending g' fp)
          (ensures sweep_shape g' fp st)

/// A word in the body of a block that is not free is not a position of the
/// walk, and not the link word of a free-list cell.
val body_word (g: heap) (p: hp_addr) (a: hp_addr)
  : Lemma (requires pos g p /\ not (blue_at g p) /\ U64.v p < U64.v a /\ U64.v a < W.bnext g p)
          (ensures (forall (x: nat). W.reaches g zero_addr x ==> x <> U64.v a) /\
                   ~(FreeList.fl_cell g a))

/// A write into the body of a block that is not free keeps the walk, the
/// headers and the free list.
val body_write (g: heap) (fp: U64.t) (p: hp_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires pos g p /\ not (blue_at g p) /\ U64.v p < U64.v a /\ U64.v a < W.bnext g p)
          (ensures same_heads g (write_word g a v) /\
                   (FLA.fl_ascending g fp ==> FLA.fl_ascending (write_word g a v) fp))

/// ---------------------------------------------------------------------------
/// Pointer targets across a change
/// ---------------------------------------------------------------------------

/// A field value that may be stored in a non-free block: not a pointer, or a
/// pointer whose target (resolved) is a non-free block and, if interior, well
/// formed.  This is what the pointer clauses of `well_formed_heap_with free`
/// ask of every field of a non-free block.
let storable (free: free_def) (g: heap) (w: U64.t) : prop =
  is_pointer w ==>
  in_use free g (resolve_object (w <: obj_addr) g) /\
  infix_addr_wf g (objects zero_addr g) (w <: obj_addr)

/// Every non-free block keeps its header, and a non-free closure (the only
/// kind of object an interior pointer can point into) its whole block.
let heads_kept (free: free_def) (g g': heap) : prop =
  forall (y: obj_addr). in_use free g y ==>
    read_word g' (hd_address y) == read_word g (hd_address y) /\
    (is_closure y g ==> same_block g g' (hd_address y))

/// **A storable value stays storable** across a change that keeps every block
/// non-free under `free` non-free under `free'`, with its header, and the
/// blocks of the non-free closures.
val storable_transfer (g g': heap) (free free': free_def) (w: U64.t)
  : Lemma (requires storable free g w /\ no_infix_block g /\ no_infix_block g' /\ free_def_ok free' /\
                    heads_kept free g g' /\
                    (forall (y: obj_addr). in_use free g y ==> in_use free' g' y))
          (ensures storable free' g' w)

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

/// From the heap marking left: everything white is pending free, and the
/// stop-the-world relation holds trivially.
val sweep_phase_start (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0)
          (ensures sweep_phase_inv g0 fp sweep_start /\
                   pending_free_within g0 sweep_start (white_after_mark g0) /\
                   stw_rel g0 g0 (U64.v sweep_start.cursor))

/// ---------------------------------------------------------------------------
/// Step
/// ---------------------------------------------------------------------------

/// **One step keeps the sweep phase**, and the pending-free set shrinks.  The
/// step frees only objects pending free: the non-free objects are the same
/// before and after (with the same size, tag and fields).
val sweep_phase_step (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    sweep_phase_inv g' fp' st' /\
                    (forall (x: obj_addr). in_use (free_incremental st') g' x == in_use (free_incremental st) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental st) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free st' g' x ==> pending_free st g x) /\
                    U64.v st'.cursor > U64.v st.cursor /\ U64.v st'.cursor <= heap_size))

/// The ghost set is never carried: that the objects pending free stay among the
/// white objects marking left follows from the shrinking, step by step.
val pending_free_within_step (g: heap) (fp: U64.t) (st: sweep_state) (dead: obj_addr -> prop)
  : Lemma (requires sweep_phase_inv g fp st /\ pending_free_within g st dead /\
                    U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in pending_free_within g' st' dead))

/// ---------------------------------------------------------------------------
/// Up to `k` steps
/// ---------------------------------------------------------------------------

/// The sweep is finished: the cursor is at the end of the heap.
let sweep_done (st: sweep_state) : bool = U64.v st.cursor + 8 >= heap_size

/// At most `k` steps, stopping when the sweep is finished (or, defensively,
/// when it cannot step).  A slice of the incremental sweep is this, for a
/// budget of steps.
let rec sweep_steps (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Tot (heap & U64.t & sweep_state) (decreases k)
  = if k = 0 || sweep_done st || not (can_sweep g st) then (g, fp, st)
    else begin
      let (g', fp', st') = sweep_step g fp st in
      sweep_steps g' fp' st' (k - 1)
    end

/// One unfolding of `sweep_steps`.
val sweep_steps_unfold (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (sweep_steps g fp st k ==
           (if k = 0 || sweep_done st || not (can_sweep g st) then (g, fp, st)
            else (let (g', fp', st') = sweep_step g fp st in sweep_steps g' fp' st' (k - 1))))

/// **`k` steps keep the sweep phase**: the pending-free set shrinks, the
/// non-free objects are the same before and after, the cursor does
/// not move back, and fewer than `k` steps were taken only if the sweep is
/// finished.
val sweep_phase_steps (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (requires sweep_phase_inv g fp st)
          (ensures (let (g', fp', st') = sweep_steps g fp st k in
                    sweep_phase_inv g' fp' st' /\
                    (forall (x: obj_addr). in_use (free_incremental st') g' x == in_use (free_incremental st) g x) /\
                    (forall (x: obj_addr). in_use (free_incremental st) g x ==> same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). pending_free st' g' x ==> pending_free st g x) /\
                    U64.v st'.cursor >= U64.v st.cursor /\
                    (st' == st ==> k = 0 \/ sweep_done st)))

/// Stop-the-world, one step keeps the relation to the marked heap.
val sweep_phase_step_stw (g0 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ stw_rel g0 g (U64.v st.cursor) /\
                    U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    stw_rel g0 g' (U64.v st'.cursor)))

/// Stop-the-world, `k` steps keep the relation to the marked heap.
val sweep_phase_steps_stw (g0 g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (requires sweep_phase_inv g fp st /\ stw_rel g0 g (U64.v st.cursor))
          (ensures (let (g', fp', st') = sweep_steps g fp st k in
                    stw_rel g0 g' (U64.v st'.cursor)))

/// A budget of one step per word of the heap finishes the sweep.
val sweep_steps_done (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (requires sweep_phase_inv g fp st /\ k * 8 >= heap_size - U64.v st.cursor)
          (ensures (let (g', fp', st') = sweep_steps g fp st k in sweep_done st'))

/// What a step needs to be safe to run on the heap itself (the Pulse step
/// reads the header at the cursor, `swept_tail`'s and `last_fragment`'s
/// blocks, and writes a merged header): the facts the stop-the-world
/// invariant gives (`GC.Spec.FusedSweep.Inv.sweep_inv_facts`), from the sweep
/// phase.
val sweep_phase_ready (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_phase_inv g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (st.swept_tail == 0UL \/ is_obj st.swept_tail) /\
                   (st.last_fragment == 0UL \/ is_obj st.last_fragment) /\
                   (prev_free g st ==>
                     (let p = if st.last_fragment <> 0UL then st.last_fragment else st.swept_tail in
                      is_obj p /\
                      wosize_at g p + U64.v (getWosize (read_word g (st.cursor <: hp_addr))) + 1
                        < pow2 54)))
