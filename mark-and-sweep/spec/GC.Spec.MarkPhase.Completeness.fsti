/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPhase.Completeness - an incremental cycle frees what was dead when it started
/// ---------------------------------------------------------------------------
///
/// Completeness across a whole incremental cycle (incremental-mark-plan.md,
/// M6): **an object that is unreachable from the roots when the cycle starts
/// is freed by the end of the sweep, unless its address was handed out again
/// since** (by an allocation, or a minor collection's promotion).
///
/// The marking invariant (`GC.Spec.MarkPhase.marking_inv`) is intrinsic: it
/// says nothing about the heap marking started from.  Completeness does, so
/// it is carried separately, as an *account* indexed by a ghost set `s` of
/// addresses -- those reachable when the cycle started (`reachable g0
/// held`), and those allocated or promoted since.  The account
/// (`mark_account s g`) has two halves:
///
///   * **what is dark is accounted for** (`dark_accounted`): every grey or
///     black object is in `s`;
///   * **the accounted objects are closed under the heap's edges**: the heap
///     is well formed for the definition of free `unaccounted s` -- blue, or
///     white and not in `s` -- so a non-free block that is dark or in `s`
///     points only at blocks that are dark or in `s`.
///
/// So an object outside `s` is never greyed: marking greys only targets of
/// fields of grey objects (dark, so accounted, so their targets are), and the
/// barrier greys only the old value of a field of an object the program
/// writes, which the program can reach (accounted, so its targets are).
/// When marking ends nothing is grey, so every block black in the marked
/// heap is in `s` (`account_marked`), and the sweep's completeness
/// (`GC.Spec.SweepPhase.Completeness`) frees every non-free block that is
/// not a survivor of marking or new.
///
/// Every event of the marking phase keeps the account (a per-event family,
/// as the sweep's `survivor_or_new_*`):
///
///   * the start, after root darkening (`account_start`, with `s` the
///     objects reachable from the roots);
///   * mark moves (`account_move`, `account_steps`);
///   * the barrier write (`account_barrier`), under the trusted obligation
///     `cycle_write s` -- the program writes into an object it can reach a
///     value it holds (both accounted for);
///   * allocation, with the new object added to `s` (`account_alloc`,
///     `account_fresh_write`, `account_fresh_close`);
///   * a minor collection, with its promoted copies added to `s`
///     (`GC.Gen.MarkPhase.Completeness.account_minor`).
///
/// The trusted obligation is the same kind as the marking invariant's roots
/// clause (option (a) of the plan): OCaml's type safety -- the program
/// obtains pointers only from its roots, by loading fields of objects it
/// holds, and by allocating.  `account_load` says that loading keeps it: a
/// field of an accounted object is accounted.
///
/// `cycle_account` packages the account at the collector's phase: the mark
/// account while marking; mid-sweep, every block that is not free (for
/// `free_incremental c`) is in `s` -- the sweep's account
/// (`SPC.survivor_or_new`) with the survivors of marking folded into `s`.
/// The hand-over (`cycle_handover`), sweep slices (`cycle_sweep_slice`) and
/// the program's events mid-sweep (`cycle_sweep_alloc`, `cycle_sweep_write`)
/// keep it, and idle again the cycle is complete (`cycle_complete`): every
/// non-free block is in `s`, so every address outside `s` is freed.

module GC.Spec.MarkPhase.Completeness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph.Within

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module MPA = GC.Spec.MarkPhase.Alloc
module S = GC.Spec.MarkPhase.Slice
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module SPC = GC.Spec.SweepPhase.Completeness
module SL = GC.Spec.SweepPhase.Slice
module FLA = GC.Spec.FreeList.Ascending
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Ph = GC.Spec.Phase

/// ---------------------------------------------------------------------------
/// Reachable when the cycle starts
/// ---------------------------------------------------------------------------

/// `x` is reachable in `g` from an object `held` names (the roots), along
/// the heap's edges (`MP.field_edge`: pointer fields of scannable objects,
/// resolved through infix headers).
let reachable (g: heap) (held: obj_addr -> prop) (x: obj_addr) : prop =
  exists (r: obj_addr). held r /\ reach_within (MP.field_edge g) (fun _ -> True) r x

/// The roots are reachable ...
val reachable_held (g: heap) (held: obj_addr -> prop) (x: obj_addr)
  : Lemma (requires held x) (ensures reachable g held x)

/// ... and reachability is the least set containing them and closed under
/// the edges: a set that contains the roots and is closed contains every
/// reachable object.  (How a concrete heap shows an object unreachable.)
val reachable_closed (g: heap) (held: obj_addr -> prop) (c: obj_addr -> prop) (x: obj_addr)
  : Lemma (requires (forall (r: obj_addr). held r ==> c r) /\
                    (forall (u v: obj_addr). c u /\ MP.field_edge g u v ==> c v) /\
                    reachable g held x)
          (ensures c x)

/// ---------------------------------------------------------------------------
/// The account
/// ---------------------------------------------------------------------------

/// What is free for the account: blue blocks, and white blocks outside `s`.
/// A function of the header (the set is fixed), so an admissible definition
/// of free.
let unaccounted (s: obj_addr -> prop) : free_def =
  fun g x -> is_blue x g || (is_white x g && not (FStar.IndefiniteDescription.strong_excluded_middle (s x)))

val unaccounted_ok (s: obj_addr -> prop) : Lemma (free_def_ok (unaccounted s))

/// Not free for it: a block that is not blue, and that is in `s` if white.
val in_use_unaccounted (s: obj_addr -> prop) (g: heap) (x: obj_addr)
  : Lemma (in_use (unaccounted s) g x <==>
           (Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ (is_white x g ==> s x)))

/// Every grey or black object is accounted for.
let dark_accounted (s: obj_addr -> prop) (g: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ (is_gray x g \/ is_black x g) ==> s x

/// **The account**: what is dark is in `s`, and a block that is dark or in
/// `s` points only at blocks that are dark or in `s`.
let mark_account (s: obj_addr -> prop) (g: heap) : prop =
  dark_accounted s g /\ well_formed_heap_with (unaccounted s) g

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

/// **The start**: when every dark object is a root (after root darkening,
/// before any mark step), the account holds with `s` the objects reachable
/// from the roots.
val account_start (g: heap) (held: obj_addr -> prop)
  : Lemma (requires well_formed_heap g /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ (is_gray x g \/ is_black x g) ==>
                       held x))
          (ensures mark_account (reachable g held) g)

/// ---------------------------------------------------------------------------
/// Marking
/// ---------------------------------------------------------------------------

/// **Greying an accounted white object** keeps the account, and the heap's
/// blocks, fields, resolutions and non-free blocks for the account.
val account_grey (s: obj_addr -> prop) (g: heap) (t: obj_addr)
  : Lemma (requires mark_account s g /\ well_formed_heap g /\
                    Seq.mem t (objects zero_addr g) /\ is_white t g /\ s t)
          (ensures mark_account s (makeGray t g) /\ well_formed_heap (makeGray t g) /\
                   objects zero_addr (makeGray t g) == objects zero_addr g /\
                   (forall (y: obj_addr). in_use (unaccounted s) (makeGray t g) y == in_use (unaccounted s) g y))

/// The barrier's darkening (`MM.darken`) of a value an accounted object
/// stores, or of no pointer at all.
val account_darken (s: obj_addr -> prop) (g: heap) (w: U64.t)
  : Lemma (requires mark_account s g /\ well_formed_heap g /\
                    (is_pointer w ==> in_use (unaccounted s) g (resolve_object (w <: obj_addr) g)))
          (ensures mark_account s (MM.darken g w) /\ well_formed_heap (MM.darken g w))

/// **A mark move keeps it**: a scanned field's target is a field of a grey
/// object, so accounted; blackening changes no block's status.
val account_move (s: obj_addr -> prop) (g g': heap)
  : Lemma (requires mark_account s g /\ well_formed_heap g /\ S.mark_move g g')
          (ensures mark_account s g')

/// ... and so do any number of moves (a mark slice).
val account_steps (s: obj_addr -> prop) (g g': heap)
  : Lemma (requires mark_account s g /\ well_formed_heap g /\ S.mark_steps g g')
          (ensures mark_account s g')

/// **What marking keeps (safety)**: a mark move only recolours, so every
/// block keeps its size, tag and fields (`SPI.same_block`), and which blocks
/// are blue; so do any number of moves.
val mark_move_keeps_blocks (g g': heap)
  : Lemma (requires well_formed_heap g /\ S.mark_move g g')
          (ensures objects zero_addr g' == objects zero_addr g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      SPI.same_block g g' (hd_address x) /\ (is_blue x g' <==> is_blue x g)))

val mark_steps_keep_blocks (g g': heap)
  : Lemma (requires well_formed_heap g /\ S.mark_steps g g')
          (ensures objects zero_addr g' == objects zero_addr g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      SPI.same_block g g' (hd_address x) /\ (is_blue x g' <==> is_blue x g)))

/// ---------------------------------------------------------------------------
/// The program
/// ---------------------------------------------------------------------------

/// **The trusted obligation for completeness**: the program writes a body
/// word of a scannable object `x` it can reach, and stores a value it holds
/// -- `x` and `v`'s target are accounted for (in `s`, or dark).  This is
/// `SPM.program_write` at the account's definition of free, as the sweep
/// phase states the program's writes at `free_incremental c`.
let cycle_write (s: obj_addr -> prop) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t) : prop =
  SPM.program_write (unaccounted s) g x a v /\ scannable g x

/// **Loading keeps the obligation maintainable**: a field of an accounted
/// object, loaded, is accounted for (the account is closed under the edges).
val account_load (s: obj_addr -> prop) (g: heap) (u t: obj_addr)
  : Lemma (requires mark_account s g /\ in_use (unaccounted s) g u /\ MP.field_edge g u t)
          (ensures in_use (unaccounted s) g t)

/// **A program write keeps it** (no barrier: idle, or into a fresh black
/// object's initialised fields).
val account_write (s: obj_addr -> prop) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires mark_account s g /\ SPM.program_write (unaccounted s) g x a v)
          (ensures mark_account s (write_word g a v))

/// **The barrier write keeps it**: 4.14's `caml_modify` while marking --
/// darken the old value, then write.  The old value is a field of `x`,
/// which is accounted for, so it is too.
val account_barrier (s: obj_addr -> prop) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires mark_account s g /\ well_formed_heap g /\ cycle_write s g x a v)
          (ensures mark_account s (write_word (MM.darken g (read_word g a)) a v))

/// What is free while the new object `obj` is uninitialised.
let unaccounted_or_new (s: obj_addr -> prop) (obj: obj_addr) : free_def =
  fun g x -> unaccounted s g x || x = obj

val unaccounted_or_new_ok (s: obj_addr -> prop) (obj: obj_addr)
  : Lemma (free_def_ok (unaccounted_or_new s obj))

/// **The account with `obj` fresh**: black, accounted for, its fields not
/// yet bound by the closure clause.
let account_fresh (s: obj_addr -> prop) (g: heap) (obj: obj_addr) : prop =
  dark_accounted s g /\ s obj /\
  Seq.mem obj (objects zero_addr g) /\ is_black obj g /\
  well_formed_heap_with (unaccounted_or_new s obj) g

/// **Allocation while marking**: the new object is added to `s`
/// (`SPC.with_new`); it is fresh.
val account_alloc (s: obj_addr -> prop) (held: obj_addr -> prop) (g: heap) (fp: U64.t)
                  (wz: nat) (tag: SPM.tag_t)
  : Lemma (requires mark_account s g /\ MP.marking_inv g held /\ FLA.fl_ascending g fp /\
                    wz >= 1 /\ tag <> infix_tag)
          (ensures (let r = AC.alloc_phase g fp Ph.Marking wz tag in
                    (r.SA.obj_out == 0UL ==> r.SA.heap_out == g) /\
                    (r.SA.obj_out <> 0UL ==>
                       GC.Spec.FusedSweep.is_obj r.SA.obj_out /\
                       account_fresh (SPC.with_new s r.SA.obj_out) r.SA.heap_out r.SA.obj_out)))

/// Writes into the fresh object's body keep it fresh.
val account_fresh_write (s: obj_addr -> prop) (g: heap) (obj: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires account_fresh s g obj /\ SPM.in_body g obj a)
          (ensures account_fresh s (write_word g a v) obj)

/// Once its fields are accounted for (values the program holds), the
/// account holds.
val account_fresh_close (s: obj_addr -> prop) (g: heap) (obj: obj_addr)
  : Lemma (requires account_fresh s g obj /\ SPM.fields_storable (unaccounted s) g obj)
          (ensures mark_account s g)

/// ---------------------------------------------------------------------------
/// The end of marking, and the cycle
/// ---------------------------------------------------------------------------

/// **When marking ends** every block black in the marked heap is accounted
/// for.
val account_marked (s: obj_addr -> prop) (g: heap)
  : Lemma (requires mark_account s g)
          (ensures forall (x: obj_addr). SPC.survived_mark g x ==> s x)

/// Mid-sweep, every block that is not free (not blue, not pending free) is
/// accounted for.  (This is `SPC.survivor_or_new` with the survivors of
/// marking folded into `s`.)
let sweep_accounted (s: obj_addr -> prop) (g: heap) (c: U64.t) : prop =
  forall (x: obj_addr). in_use (SPI.free_incremental c) g x ==> s x

/// **The account at the collector's phase.**  While marking, the mark
/// account; mid-sweep, every non-free block accounted for; idle again
/// (the sweep over), every block that is not blue accounted for.
let cycle_account (s: obj_addr -> prop) (g: heap) (ph: Ph.gc_phase) : prop =
  match ph with
  | Ph.Marking -> mark_account s g
  | Ph.Sweeping c -> sweep_accounted s g c
  | Ph.Idle -> forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==> s x

/// **The hand-over**: when nothing is grey, the sweep starts accounted for
/// (a block that is not free at the start of the sweep is black).
val cycle_handover (s: obj_addr -> prop) (g: heap)
  : Lemma (requires mark_account s g /\ Mark.noGreyObjects g)
          (ensures cycle_account s g (Ph.Sweeping zero_addr))

/// **A sweep slice keeps it**, at whatever phase it leaves.
val cycle_sweep_slice (s: obj_addr -> prop) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
  : Lemma (requires cycle_account s g ph /\ ~(Ph.Marking? ph) /\
                    (Ph.Sweeping? ph ==> SPI.sweep_inv_incremental g fp (Ph.Sweeping?._0 ph)))
          (ensures (let (g', fp', ph') = SL.phase_slice g fp ph budget in
                    cycle_account s g' ph'))

/// **An allocation mid-sweep keeps it**, with the new object added to `s`.
val cycle_sweep_alloc (s: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t) (wz: nat) (tag: SPM.tag_t)
  : Lemma (requires sweep_accounted s g c /\ SPI.sweep_shape g fp c)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
                    sweep_accounted (SPC.with_new s r.SA.obj_out) r.SA.heap_out c))

/// **A write into the body of a block that is not blue keeps it** mid-sweep
/// (a program write, or a fresh object's initialisation).
val cycle_sweep_write (s: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t)
                      (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires sweep_accounted s g c /\ SPI.sweep_shape g fp c /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a)
          (ensures sweep_accounted s (write_word g a v) c)

/// A larger set accounts for as much, past marking.
val cycle_weaken (s s': obj_addr -> prop) (g: heap) (ph: Ph.gc_phase)
  : Lemma (requires cycle_account s g ph /\ ~(Ph.Marking? ph) /\ (forall (x: obj_addr). s x ==> s' x))
          (ensures cycle_account s' g ph)

/// **The cycle is complete**: idle again, every block that is not free is
/// accounted for -- reachable when the cycle started, or allocated or
/// promoted since -- so every other address is freed.
val cycle_complete (s: obj_addr -> prop) (g: heap)
  : Lemma (requires cycle_account s g Ph.Idle)
          (ensures forall (x: obj_addr). ~(s x) ==> SPC.freed g x)
