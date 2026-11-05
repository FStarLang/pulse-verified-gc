/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Intrinsic - the sweep invariant, on the current heap
/// ---------------------------------------------------------------------------
///
/// The sweep (incremental-sweep-plan.md): the major collector has finished
/// marking and sweeps the heap block by block -- all at once (stop-the-world,
/// `GC.Spec.FusedSweep.fused_sweep_coalesce`) or a few blocks at a time while
/// the program runs.  The invariant, `sweep_inv_incremental g fp c`, holds in
/// both modes and is about the current heap `g` and the cursor `c` alone:
///
///   * *pending free* (`pending_free c g`): the white blocks in front of the
///     cursor, dead but not yet freed -- read off the heap and the cursor;
///   * the heap is well formed when free means blue or pending free
///     (`well_formed_heap_with (free_incremental c) g`), so the fields of a
///     block pending free may point anywhere; its walk covers the heap and
///     reaches the cursor, and the free list is exact and ascending;
///   * behind the cursor every block is white or free, and no two free
///     blocks are adjacent;
///   * in front of the cursor no block is grey.
///
/// The rest of the sweep's state, `swept_tail` and `last_fragment`, is a
/// function of the heap and the cursor (`state_at`), so the invariant does
/// not carry it: the clauses `GC.Spec.FusedSweep.Inv` states of it
/// (`tail_ok`, `frag_ok`, `ends_free`) hold of the derived state at any
/// position of the walk (`tail_ok_iff`, `frag_at_ok`, `ends_free_derived`).
/// A sweep step is the one `fused_sweep_coalesce` runs, from `state_at g c`,
/// and the state it leaves is again the derived one
/// (`GC.Spec.FusedSweep.Step.sweep_inv_incremental_step`).
///
/// Everything but well-formedness is `sweep_shape`: facts about the walk,
/// the headers and the free list, which any change that keeps the walk and
/// the headers keeps (`shape_transport`).  The program's events are in
/// `GC.Gen.SweepPhase`, a minor collection mid-sweep in
/// `GC.Gen.SweepPhase.Minor`, and safety in `GC.Gen.SweepPhase.Safety`.
///
/// A sweep step frees only blocks pending free and the pending-free set only
/// shrinks.  That the blocks pending free are among the white objects marking
/// left (`pending_free_within`, `white_after_mark`) is a lemma, never carried.
///
/// Stop-the-world, the end facts relate the result to the marked heap `g0`;
/// for those the sweep keeps `sweep_inv_stw g0 g fp c`: the invariant, the
/// walk of `g0` reaches the cursor, `g` is `g0` from the cursor on
/// (`front_unchanged`), every block black in `g0` is still a block of `g`
/// with the same size, tag and fields (`marked_survive`), and every non-free
/// block behind the cursor was black in `g0` (`survivors_were_marked`).

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
/// The sweep's caches, derived
/// ---------------------------------------------------------------------------
///
/// `swept_tail` and `last_fragment` are caches: both are functions of the
/// heap and the cursor.  The implementation stores them in the phase record
/// and updates them in place (the sweep step, and the allocator's
/// `caml_fl_merge` update); its phase predicate says the stored values are
/// the derived ones (`GC.Impl.Allocator.is_phase`).

/// The last cell at or below `x` (0 when there is none).
let rec max_cell_below (g: heap) (x: nat) : GTot U64.t (decreases x) =
  if x = 0 then 0UL
  else if x < heap_size && FStar.IndefiniteDescription.strong_excluded_middle (FreeList.fl_cell g (U64.uint_to_t x))
  then U64.uint_to_t x
  else max_cell_below g (x - 1)

val max_cell_below_spec (g: heap) (x: nat)
  : Lemma (let m = max_cell_below g x in
           (m == 0UL \/ (FreeList.fl_cell g m /\ U64.v m <= x)) /\
           (forall (y: U64.t). FreeList.fl_cell g y /\ U64.v y <= x ==> m <> 0UL /\ U64.v y <= U64.v m))

/// Heaps with the same cells have the same last cells.
val max_cell_below_congr (g g': heap) (x: nat)
  : Lemma (requires forall (y: U64.t). FreeList.fl_cell g' y <==> FreeList.fl_cell g y)
          (ensures max_cell_below g' x == max_cell_below g x)

/// **`swept_tail`, derived**: the last free-list cell behind the cursor `c`
/// (its block ends at or before `c`), or 0, the list-head sentinel.
let last_cell_behind (g: heap) (c: nat) : GTot U64.t =
  if c = 0 then 0UL else max_cell_below g (c - 1)

/// **`last_fragment`, derived**: `c` when the block ending at the cursor `c`
/// is a free block with no field (a one-word fragment, too small for a link),
/// otherwise 0.
let frag_at (g: heap) (c: nat) : GTot U64.t =
  if c >= U64.v zero_addr + 8 && c < heap_size && c % 8 = 0 &&
     W.reaches g zero_addr (c - 8) && W.can_step g (mk_hp_addr (c - 8)) &&
     blue_at g (mk_hp_addr (c - 8)) && wz_at g (mk_hp_addr (c - 8)) = 0
  then U64.uint_to_t c
  else 0UL

/// The sweep state at cursor `c` on `g`: the caches derived.
let state_at (g: heap) (c: U64.t) : GTot sweep_state =
  { cursor = c; swept_tail = last_cell_behind g (U64.v c); last_fragment = frag_at g (U64.v c) }

/// `tail_ok` (`GC.Spec.FusedSweep.Inv`) pins `swept_tail` down: at a walk
/// position it says exactly that it is the derived one.
val tail_ok_iff (g: heap) (c: nat) (t: U64.t)
  : Lemma (requires W.reaches g zero_addr c)
          (ensures tail_ok g c t <==> t == last_cell_behind g c)

/// So does `frag_ok`, given `swept_tail` and that the block before the cursor
/// is free exactly when one of the two says so (`ends_free`).
val frag_ok_derived (g: heap) (st: sweep_state)
  : Lemma (requires W.reaches g zero_addr (U64.v st.cursor) /\
                    tail_ok g (U64.v st.cursor) st.swept_tail /\
                    ends_free g (U64.v st.cursor) (prev_free g st) /\
                    frag_ok g (U64.v st.cursor) st.last_fragment)
          (ensures st.last_fragment == frag_at g (U64.v st.cursor))

/// The derived fragment is a fragment.
val frag_at_ok (g: heap) (c: nat) : Lemma (frag_ok g c (frag_at g c))

/// **The derived caches say whether the block before the cursor is free**:
/// at any position `c` of the walk, the block ending at `c` is free exactly
/// when `prev_free` of the derived state says so.  A free block ending at
/// `c` is a fragment (`frag_at`) or a cell, and then the last cell behind
/// `c` (`last_cell_behind`), whose block ends at `c`; conversely, both caches
/// name a free block ending at `c`, and only one block of the walk ends there.
val ends_free_derived (g: heap) (c: U64.t)
  : Lemma (requires W.reaches g zero_addr (U64.v c))
          (ensures ends_free g (U64.v c) (prev_free g (state_at g c)))

/// At the start of the walk the derived state is the sweep's start.
val state_at_start (g: heap) : Lemma (state_at g sweep_start.cursor == sweep_start)

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// Pending free: a white block in front of the cursor (its header at or above
/// it).  It is dead, and this sweep will free it when the cursor gets there.
let pending_free (c: U64.t) (g: heap) (x: obj_addr) : GTot bool =
  is_block g x && is_white x g && U64.v x > U64.v c

/// **What counts as free during the sweep**: the blue blocks, and the blocks
/// pending free.  A block pending free is garbage left in place; nothing reads
/// its fields before the sweep frees it.
let free_incremental (c: U64.t) : free_def =
  fun g x -> is_blue x g || pending_free c g x

/// It is a definition of free a generic theorem may take.
val free_incremental_ok (c: U64.t) : Lemma (free_def_ok (free_incremental c))

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

/// **The sweep invariant at cursor `c`**, about the current heap only.
[@@"opaque_to_smt"]
let sweep_inv_incremental (g: heap) (fp: U64.t) (c: U64.t) : prop =
  let n = U64.v c in
  n % 8 == 0 /\ n <= heap_size /\ W.reaches g zero_addr n /\
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  well_formed_heap_with (free_incremental c) g /\
  behind_swept g n /\ front_unswept g n /\
  no_adjacent_free g n /\
  FLA.fl_ascending g fp

/// Its clauses, and those of the derived sweep state (`state_at`).
val sweep_inv_incremental_elim (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c)
          (ensures (let n = U64.v c in
                    let st = state_at g c in
                    n % 8 == 0 /\ n <= heap_size /\ W.reaches g zero_addr n /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    well_formed_heap_with (free_incremental c) g /\
                    behind_swept g n /\ front_unswept g n /\
                    no_adjacent_free g n /\ ends_free g n (prev_free g st) /\
                    tail_ok g n st.swept_tail /\ frag_ok g n st.last_fragment /\
                    FLA.fl_ascending g fp))

/// Closing it at a sweep state whose caches satisfy `tail_ok`, `frag_ok` and
/// `ends_free`: they are the derived ones.
val sweep_inv_incremental_intro (g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires (let n = U64.v st.cursor in
                     n % 8 == 0 /\ n <= heap_size /\ W.reaches g zero_addr n /\
                     heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                     well_formed_heap_with (free_incremental st.cursor) g /\
                     behind_swept g n /\ front_unswept g n /\
                     no_adjacent_free g n /\ ends_free g n (prev_free g st) /\
                     tail_ok g n st.swept_tail /\ frag_ok g n st.last_fragment /\
                     FLA.fl_ascending g fp))
          (ensures sweep_inv_incremental g fp st.cursor /\ st == state_at g st.cursor)

/// The sweep invariant without well-formedness: the walk, the headers and the
/// free list.  These are about the walk and the headers only (and the free
/// list's links), so a change that keeps the walk and every header on it
/// keeps them (`shape_transport`).
[@@"opaque_to_smt"]
let sweep_shape (g: heap) (fp: U64.t) (c: U64.t) : prop =
  let n = U64.v c in
  n % 8 == 0 /\ n <= heap_size /\ W.reaches g zero_addr n /\
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  behind_swept g n /\ front_unswept g n /\
  no_adjacent_free g n /\
  FLA.fl_ascending g fp

/// The sweep invariant is its shape and well-formedness for `free_incremental`.
val sweep_inv_incremental_iff (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (sweep_inv_incremental g fp c <==>
           sweep_shape g fp c /\ well_formed_heap_with (free_incremental c) g)

val sweep_shape_elim (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_shape g fp c)
          (ensures (let n = U64.v c in
                    let st = state_at g c in
                    n % 8 == 0 /\ n <= heap_size /\ W.reaches g zero_addr n /\
                    heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                    behind_swept g n /\ front_unswept g n /\
                    no_adjacent_free g n /\ ends_free g n (prev_free g st) /\
                    tail_ok g n st.swept_tail /\ frag_ok g n st.last_fragment /\
                    FLA.fl_ascending g fp))

val sweep_shape_intro (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires (let n = U64.v c in
                     n % 8 == 0 /\ n <= heap_size /\ W.reaches g zero_addr n /\
                     heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
                     behind_swept g n /\ front_unswept g n /\
                     no_adjacent_free g n /\
                     FLA.fl_ascending g fp))
          (ensures sweep_shape g fp c)

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
let pending_free_within (g: heap) (c: U64.t) (dead: obj_addr -> prop) : prop =
  forall (x: obj_addr). pending_free c g x ==> dead x

/// The white objects when marking ended.
let white_after_mark (g0: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g0) /\ is_white x g0

/// ---------------------------------------------------------------------------
/// Stop-the-world: the relation to the marked heap
/// ---------------------------------------------------------------------------

/// From the cursor on, `g` is word for word `g0`.
[@@"opaque_to_smt"]
let front_unchanged (g0 g: heap) (c: nat) : prop =
  forall (a: hp_addr). U64.v a >= c ==> read_word g a == read_word g0 a

/// Every block black in `g0` is still a block, not free, with the same size,
/// tag and fields; only its colour may differ.
[@@"opaque_to_smt"]
let marked_survive (g0 g: heap) : prop =
  forall (p: hp_addr). pos g0 p /\ black_at g0 p ==>
    pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
    getTag (read_word g p) == getTag (read_word g0 p) /\
    (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
       read_word g a == read_word g0 a)

/// Every block behind the cursor that is not free was black in `g0`.
[@@"opaque_to_smt"]
let survivors_were_marked (g0 g: heap) (c: nat) : prop =
  forall (p: hp_addr). pos g p /\ U64.v p < c /\ not (blue_at g p) ==> pos g0 p /\ black_at g0 p

/// **The stop-the-world sweep at cursor `c`** of the marked heap `g0`: the
/// sweep invariant, and the relation to `g0`.
let sweep_inv_stw (g0 g: heap) (fp: U64.t) (c: U64.t) : prop =
  sweep_inv_incremental g fp c /\ W.reaches g0 zero_addr (U64.v c) /\
  front_unchanged g0 g (U64.v c) /\ marked_survive g0 g /\ survivors_were_marked g0 g (U64.v c)

val front_unchanged_elim (g0 g: heap) (c: nat) (a: hp_addr)
  : Lemma (requires front_unchanged g0 g c /\ U64.v a >= c)
          (ensures read_word g a == read_word g0 a)

val front_unchanged_intro (g0 g: heap) (c: nat)
  (pf: (a: hp_addr -> Lemma (requires U64.v a >= c) (ensures read_word g a == read_word g0 a)))
  : Lemma (front_unchanged g0 g c)

val marked_survive_elim (g0 g: heap) (p: hp_addr)
  : Lemma (requires marked_survive g0 g /\ pos g0 p /\ black_at g0 p)
          (ensures pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
                   getTag (read_word g p) == getTag (read_word g0 p) /\
                   (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                      read_word g a == read_word g0 a))

val marked_survive_intro (g0 g: heap)
  (pf: (p: hp_addr -> Lemma (requires pos g0 p /\ black_at g0 p)
         (ensures pos g p /\ not (blue_at g p) /\ wz_at g p == wz_at g0 p /\
                  getTag (read_word g p) == getTag (read_word g0 p) /\
                  (forall (a: hp_addr). U64.v p < U64.v a /\ U64.v a < W.bnext g0 p ==>
                     read_word g a == read_word g0 a))))
  : Lemma (marked_survive g0 g)

val survivors_were_marked_elim (g0 g: heap) (c: nat) (p: hp_addr)
  : Lemma (requires survivors_were_marked g0 g c /\ pos g p /\ U64.v p < c /\ not (blue_at g p))
          (ensures pos g0 p /\ black_at g0 p)

val survivors_were_marked_intro (g0 g: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires pos g p /\ U64.v p < c /\ not (blue_at g p))
                           (ensures pos g0 p /\ black_at g0 p)))
  : Lemma (survivors_were_marked g0 g c)

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

/// A block that is not free during the sweep, at its header: on the walk,
/// not blue, and not pending free.
let live_pos (g: heap) (c: nat) (q: hp_addr) : bool =
  pos g q && not (blue_at g q) && not (white_at g q && U64.v q >= c)

/// An object is not free during the sweep exactly when its block is.
val live_obj (g: heap) (c: U64.t) (x: obj_addr)
  : Lemma (requires U64.v c % 8 == 0)
          (ensures in_use (free_incremental c) g x == live_pos g (U64.v c) (hd_address x))

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
                   (forall (x: obj_addr) (c: U64.t). pending_free c g' x == pending_free c g x) /\
                   (forall (x: obj_addr). in_use free_stw g' x == in_use free_stw g x) /\
                   (forall (x: obj_addr) (free: free_def). free_def_ok free ==> in_use free g' x == in_use free g x) /\
                   (forall (x: U64.t). FreeList.fl_cell g' x <==> FreeList.fl_cell g x))

/// **The shape depends only on the walk, the headers and the free list.**
val shape_transport (g g': heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_shape g fp c /\ same_heads g g' /\ FLA.fl_ascending g' fp)
          (ensures sweep_shape g' fp c)

/// So is the derived sweep state.
val state_at_heads (g g': heap) (c: U64.t)
  : Lemma (requires same_heads g g')
          (ensures state_at g' c == state_at g c)

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

/// From the heap marking left: everything white is pending free.
val sweep_inv_incremental_start (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0)
          (ensures sweep_inv_incremental g0 fp sweep_start.cursor /\
                   pending_free_within g0 sweep_start.cursor (white_after_mark g0))

/// Stop-the-world, the relation to the marked heap holds trivially.
val sweep_inv_stw_start (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0)
          (ensures sweep_inv_stw g0 g0 fp sweep_start.cursor)

/// ---------------------------------------------------------------------------
/// Up to `k` steps
/// ---------------------------------------------------------------------------

/// The sweep is finished: the cursor is at the end of the heap.
let sweep_done (c: U64.t) : bool = U64.v c + 8 >= heap_size

/// At most `k` steps, stopping when the sweep is finished (or, defensively,
/// when it cannot step).  A slice of the incremental sweep is this, for a
/// budget of steps, from the derived state.  `GC.Spec.FusedSweep.Step` proves
/// what the steps keep.
let rec sweep_steps (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Tot (heap & U64.t & sweep_state) (decreases k)
  = if k = 0 || sweep_done st.cursor || not (can_sweep g st) then (g, fp, st)
    else begin
      let (g', fp', st') = sweep_step g fp st in
      sweep_steps g' fp' st' (k - 1)
    end

/// One unfolding of `sweep_steps`.
val sweep_steps_unfold (g: heap) (fp: U64.t) (st: sweep_state) (k: nat)
  : Lemma (sweep_steps g fp st k ==
           (if k = 0 || sweep_done st.cursor || not (can_sweep g st) then (g, fp, st)
            else (let (g', fp', st') = sweep_step g fp st in sweep_steps g' fp' st' (k - 1))))
