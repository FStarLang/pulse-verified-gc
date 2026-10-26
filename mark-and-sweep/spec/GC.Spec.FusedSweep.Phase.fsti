/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.Phase - the sweep, with the program running between steps
/// ---------------------------------------------------------------------------
///
/// The stop-the-world sweep's invariant `sweep_inv g0 g fp st`
/// (`GC.Spec.FusedSweep.Inv`) says that in front of the cursor the current
/// heap `g` is the heap marking left, `g0`, word for word (`front_same`).  An
/// incremental sweep runs the program between slices, and the program changes
/// the heap in front of the cursor too:
///
///   * it allocates there, carving a new black object, a smaller free block and
///     possibly a header-only fragment out of a free cell;
///   * it writes the fields of live objects.
///
/// So in front of the cursor the heap is no longer `g0`, but it is still
/// *related* to `g0` (the plan's `front_ok`): every block there is an
/// unchanged block of `g0` (a survivor's fields may differ), a new black object
/// carved out of a free block of `g0`, or a free block carved out of one; and
/// every white block there is a white block of `g0` with its header unchanged
/// -- garbage is never created or revived.
///
/// **The reference heap.**  Rather than restate the sweep's invariant and its
/// step lemmas against a relation, the sweep phase keeps a ghost *reference
/// heap* `g1`: `g0` as the program has changed it since marking, with every
/// new object black.  The sweep's invariant holds of the current heap against
/// the reference heap, `sweep_inv g1 g fp st`, so the step, start and end
/// lemmas apply unchanged; the program's actions update `g1` alongside `g`
/// (`GC.Gen.SweepPhase`); and `ref_ok g0 g1 c` relates the reference heap to
/// the heap marking left:
///
///   * `keeps_live`     every block live (black) after marking is still a
///                      block of `g1`, with the header marking gave it;
///   * `no_new_garbage` every block of `g1` that is neither black nor free is a
///                      block of `g0`, with its header unchanged;
///   * `front_carved`   in front of the cursor every block of `g1` is a block of
///                      `g0` with its header unchanged, or a black or free
///                      block carved out of a free block of `g0`;
///   * the walk of `g1` covers the heap, and no block of it is infix.
///
/// The stop-the-world sweep is the case `g1 = g0` (`sweeping_stw`), and
/// `sweeping_front_ok` reads the plan's `front_ok` back off the invariant.

module GC.Spec.FusedSweep.Phase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv

module U64 = FStar.UInt64
module W = GC.Spec.Walk

/// ---------------------------------------------------------------------------
/// Blocks
/// ---------------------------------------------------------------------------

/// A block of `g`: a position of its walk from the heap's start, that can step.
let pos (g: heap) (p: hp_addr) : bool =
  W.reaches g zero_addr (U64.v p) && W.can_step g p

/// The block at `p` of `g` lies inside a free block of `g0`.
let carved (g0 g: heap) (p: hp_addr) : prop =
  exists (q: hp_addr). pos g0 q /\ blue_at g0 q /\
                       U64.v q <= U64.v p /\ W.bnext g p <= W.bnext g0 q

/// ---------------------------------------------------------------------------
/// The reference heap
/// ---------------------------------------------------------------------------

/// Every block live after marking is still a block, with its header.
[@@"opaque_to_smt"]
let keeps_live (g0 g1: heap) : prop =
  forall (p: hp_addr). pos g0 p /\ black_at g0 p ==> pos g1 p /\ read_word g1 p == read_word g0 p

/// Every block that is neither live nor free was a block of `g0`, with the
/// same header: garbage is never created or revived.
[@@"opaque_to_smt"]
let no_new_garbage (g0 g1: heap) : prop =
  forall (p: hp_addr). pos g1 p /\ not (black_at g1 p) /\ not (blue_at g1 p) ==>
    pos g0 p /\ read_word g1 p == read_word g0 p

/// In front of `c`, a block is one of `g0`'s with its header, or a black or
/// free block carved out of a free block of `g0`.
[@@"opaque_to_smt"]
let front_carved (g0 g1: heap) (c: nat) : prop =
  forall (p: hp_addr). pos g1 p /\ U64.v p >= c ==>
    (pos g0 p /\ read_word g1 p == read_word g0 p) \/
    ((black_at g1 p \/ blue_at g1 p) /\ carved g0 g1 p)

/// The reference heap `g1`, against the heap `g0` marking left, at cursor `c`.
let ref_ok (g0 g1: heap) (c: nat) : prop =
  sweep_g0 g1 /\ well_formed_heap_part4 g1 /\
  keeps_live g0 g1 /\ no_new_garbage g0 g1 /\ front_carved g0 g1 c

/// The sweep phase: the current heap `g`, with free-list head `fp` and sweep
/// state `st`, against the reference heap `g1`, against the heap `g0`
/// marking left.
let sweeping (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) : prop =
  ref_ok g0 g1 (U64.v st.cursor) /\ sweep_inv g1 g fp st

/// ---------------------------------------------------------------------------
/// Opening and closing the clauses
/// ---------------------------------------------------------------------------

val keeps_live_elim (g0 g1: heap) (p: hp_addr)
  : Lemma (requires keeps_live g0 g1 /\ pos g0 p /\ black_at g0 p)
          (ensures pos g1 p /\ read_word g1 p == read_word g0 p)

val keeps_live_intro (g0 g1: heap)
  (pf: (p: hp_addr -> Lemma (requires pos g0 p /\ black_at g0 p)
                           (ensures pos g1 p /\ read_word g1 p == read_word g0 p)))
  : Lemma (keeps_live g0 g1)

val no_new_garbage_elim (g0 g1: heap) (p: hp_addr)
  : Lemma (requires no_new_garbage g0 g1 /\ pos g1 p /\
                    not (black_at g1 p) /\ not (blue_at g1 p))
          (ensures pos g0 p /\ read_word g1 p == read_word g0 p)

val no_new_garbage_intro (g0 g1: heap)
  (pf: (p: hp_addr -> Lemma (requires pos g1 p /\ not (black_at g1 p) /\ not (blue_at g1 p))
                           (ensures pos g0 p /\ read_word g1 p == read_word g0 p)))
  : Lemma (no_new_garbage g0 g1)

val front_carved_elim (g0 g1: heap) (c: nat) (p: hp_addr)
  : Lemma (requires front_carved g0 g1 c /\ pos g1 p /\ U64.v p >= c)
          (ensures (pos g0 p /\ read_word g1 p == read_word g0 p) \/
                   ((black_at g1 p \/ blue_at g1 p) /\ carved g0 g1 p))

val front_carved_intro (g0 g1: heap) (c: nat)
  (pf: (p: hp_addr -> Lemma (requires pos g1 p /\ U64.v p >= c)
                           (ensures (pos g0 p /\ read_word g1 p == read_word g0 p) \/
                                    ((black_at g1 p \/ blue_at g1 p) /\ carved g0 g1 p))))
  : Lemma (front_carved g0 g1 c)

/// The front shrinks as the cursor advances.
val front_carved_mono (g0 g1: heap) (c c': nat)
  : Lemma (requires front_carved g0 g1 c /\ c <= c') (ensures front_carved g0 g1 c')

/// ---------------------------------------------------------------------------
/// Start, step, and the stop-the-world case
/// ---------------------------------------------------------------------------

/// The sweep phase starts from the heap marking left, which is also the
/// reference heap.
val sweeping_start (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp)
          (ensures sweeping g0 g0 g0 fp sweep_start)

/// A sweep step keeps it, with the reference heap unchanged.
val sweeping_step (g0 g1 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweeping g0 g1 g fp st /\ U64.v st.cursor + 8 < heap_size)
          (ensures can_sweep g st /\
                   (let (g', fp', st') = sweep_step g fp st in
                    sweeping g0 g1 g' fp' st' /\
                    U64.v st'.cursor > U64.v st.cursor /\ U64.v st'.cursor <= heap_size))

/// Stop-the-world: no program runs between steps, so the reference heap is the
/// heap marking left and the stop-the-world invariant is the sweep phase's.
val sweeping_stw (g0 g: heap) (fp0 fp: U64.t) (st: sweep_state)
  : Lemma (requires sweep_pre g0 fp0 /\ sweep_inv g0 g fp st)
          (ensures sweeping g0 g0 g fp st)

/// ---------------------------------------------------------------------------
/// In front of the cursor
/// ---------------------------------------------------------------------------

/// The plan's `front_ok`, of the current heap: in front of the cursor every
/// block is a block of `g0` with its header unchanged, or a black or free
/// block carved out of a free block of `g0`; and every block there that is
/// neither black nor free is a block of `g0` with its header unchanged.
let front_ok (g0 g: heap) (c: nat) : prop =
  (forall (p: hp_addr). pos g p /\ U64.v p >= c ==>
     (pos g0 p /\ read_word g p == read_word g0 p) \/
     ((black_at g p \/ blue_at g p) /\ carved g0 g p)) /\
  (forall (p: hp_addr). pos g p /\ U64.v p >= c /\ not (black_at g p) /\ not (blue_at g p) ==>
     pos g0 p /\ read_word g p == read_word g0 p)

/// Stop-the-world, `front_same` gives `front_ok`.
val front_same_front_ok (g0 g: heap) (c: nat)
  : Lemma (requires front_same g0 g c /\ W.reaches g0 zero_addr c /\ W.reaches g zero_addr c)
          (ensures front_ok g0 g c)

/// The sweep phase gives `front_ok`.
val sweeping_front_ok (g0 g1 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweeping g0 g1 g fp st)
          (ensures front_ok g0 g (U64.v st.cursor))
