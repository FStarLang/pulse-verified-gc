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
/// it is carried separately, as an *account* against the cycle's **snapshot**:
/// the ghost set `snapshot` of the addresses the cycle must keep, in the
/// sense of snapshot-at-the-beginning (SATB) marking -- those reachable from
/// the roots when the cycle started (`reachable g0 outside_refs`), and those
/// allocated or promoted during the cycle.  The account (`within_snapshot
/// snapshot g`) has two halves:
///
///   * **what is dark is in the snapshot** (`dark_in_snapshot`): every grey
///     or black object is in `snapshot`;
///   * **the snapshot is closed under the heap's edges**: the heap is well
///     formed for the definition of free `outside_snapshot snapshot` -- blue,
///     or white and not in `snapshot` -- so a non-free block that is dark or
///     in `snapshot` points only at blocks that are dark or in `snapshot`.
///
/// So an object outside `snapshot` is never greyed: marking greys only targets of
/// fields of grey objects (dark, so in the snapshot, so their targets are),
/// and the barrier greys only the old value of a field of an object the
/// program writes, which the program can reach (in the snapshot, so its
/// targets are).
/// When marking ends nothing is grey, so every block black in the marked
/// heap is in `snapshot` (`account_marked`), and the sweep's completeness
/// (`GC.Spec.SweepPhase.Completeness`) frees every non-free block that is
/// not a survivor of marking or new.
///
/// Every event of the marking phase keeps the account (a per-event family,
/// as the sweep's `survivor_or_new_*`):
///
///   * the start, after root darkening (`account_start`, with `snapshot` the
///     objects reachable from the roots);
///   * mark moves (`account_move`, `account_steps`);
///   * the barrier write (`account_barrier`), under the trusted obligation
///     `cycle_write snapshot` -- the program writes into an object it can reach a
///     value it holds (both in the snapshot);
///   * allocation, with the new object added to `snapshot` (`account_alloc`,
///     `account_fresh_write`, `account_fresh_close`);
///   * a minor collection, with its promoted copies added to `snapshot`
///     (`GC.Gen.MarkPhase.Completeness.account_minor`).
///
/// The trusted obligation is the same kind as the marking invariant's roots
/// clause (option (a) of the plan): OCaml's type safety -- the program
/// obtains pointers only from its roots, by loading fields of objects it
/// holds, and by allocating.  `account_load` says that loading keeps it: a
/// field of an object in the snapshot is in the snapshot.
///
/// `cycle_account` packages the account at the collector's phase:
/// `within_snapshot` while marking; mid-sweep, every block that is not free (for
/// `free_incremental c`) is in `snapshot` -- the sweep's account
/// (`SPC.survivor_or_new`) with the survivors of marking folded into `snapshot`.
/// The hand-over (`cycle_handover`), sweep slices (`cycle_sweep_slice`) and
/// the program's events mid-sweep (`cycle_sweep_alloc`, `cycle_sweep_write`)
/// keep it, and idle again the cycle is complete (`cycle_complete`): every
/// non-free block is in `snapshot`, so every address outside `snapshot` is freed.
///
/// These lemmas take the snapshot as an argument, and the set of every
/// address satisfies them.  A run of the cycle fixes it
/// (`GC.Gen.Run.Invariant`: the cycle's snapshot, snapshot-at-the-beginning
/// while marking, and that the cycle is lossless, `cycle_lossless`).

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

/// `x` is reachable in `g` from an object `outside_refs` names (the roots), along
/// the heap's edges (`MP.field_edge`: pointer fields of scannable objects,
/// resolved through infix headers).
let reachable (g: heap) (outside_refs: obj_addr -> prop) (x: obj_addr) : prop =
  exists (r: obj_addr). outside_refs r /\ reach_within (MP.field_edge g) (fun _ -> True) r x

/// The roots are reachable ...
val reachable_outside_refs (g: heap) (outside_refs: obj_addr -> prop) (x: obj_addr)
  : Lemma (requires outside_refs x) (ensures reachable g outside_refs x)

/// ... and reachability is the least set containing them and closed under
/// the edges: a set that contains the roots and is closed contains every
/// reachable object.  (How a concrete heap shows an object unreachable.)
val reachable_closed (g: heap) (outside_refs: obj_addr -> prop) (c: obj_addr -> prop) (x: obj_addr)
  : Lemma (requires (forall (r: obj_addr). outside_refs r ==> c r) /\
                    (forall (u v: obj_addr). c u /\ MP.field_edge g u v ==> c v) /\
                    reachable g outside_refs x)
          (ensures c x)

/// ---------------------------------------------------------------------------
/// The account
/// ---------------------------------------------------------------------------

/// What is free for the account: blue blocks, and white blocks outside `snapshot`.
/// A function of the header (the set is fixed), so an admissible definition
/// of free.
let outside_snapshot (snapshot: obj_addr -> prop) : free_def =
  fun g x -> is_blue x g || (is_white x g && not (FStar.IndefiniteDescription.strong_excluded_middle (snapshot x)))

val outside_snapshot_ok (snapshot: obj_addr -> prop) : Lemma (free_def_ok (outside_snapshot snapshot))

/// Not free for it: a block that is not blue, and that is in `snapshot` if white.
val in_use_outside_snapshot (snapshot: obj_addr -> prop) (g: heap) (x: obj_addr)
  : Lemma (in_use (outside_snapshot snapshot) g x <==>
           (Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ (is_white x g ==> snapshot x)))

/// Every grey or black object is in the snapshot.
let dark_in_snapshot (snapshot: obj_addr -> prop) (g: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ (is_gray x g \/ is_black x g) ==> snapshot x

/// **The account**: what is dark is in `snapshot`, and a block that is dark or in
/// `snapshot` points only at blocks that are dark or in `snapshot`.
let within_snapshot (snapshot: obj_addr -> prop) (g: heap) : prop =
  dark_in_snapshot snapshot g /\ well_formed_heap_with (outside_snapshot snapshot) g

/// The account depends on the snapshot only through which addresses are in
/// it.
val within_snapshot_ext (snapshot snapshot': obj_addr -> prop) (g: heap)
  : Lemma (requires within_snapshot snapshot g /\ (forall (x: obj_addr). snapshot x <==> snapshot' x))
          (ensures within_snapshot snapshot' g)

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

/// **The start**: when every dark object is a root (after root darkening,
/// before any mark step), the account holds with `snapshot` the objects reachable
/// from the roots.
val account_start (g: heap) (outside_refs: obj_addr -> prop)
  : Lemma (requires well_formed_heap g /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ (is_gray x g \/ is_black x g) ==>
                       outside_refs x))
          (ensures within_snapshot (reachable g outside_refs) g)

/// ---------------------------------------------------------------------------
/// Marking
/// ---------------------------------------------------------------------------

/// **Greying a white object in the snapshot** keeps the account, and the heap's
/// blocks, fields, resolutions and non-free blocks for the account.
val account_grey (snapshot: obj_addr -> prop) (g: heap) (t: obj_addr)
  : Lemma (requires within_snapshot snapshot g /\ well_formed_heap g /\
                    Seq.mem t (objects zero_addr g) /\ is_white t g /\ snapshot t)
          (ensures within_snapshot snapshot (makeGray t g) /\ well_formed_heap (makeGray t g) /\
                   objects zero_addr (makeGray t g) == objects zero_addr g /\
                   (forall (y: obj_addr). in_use (outside_snapshot snapshot) (makeGray t g) y == in_use (outside_snapshot snapshot) g y))

/// The barrier's darkening (`MM.darken`) of a value an object in the snapshot
/// stores, or of no pointer at all.
val account_darken (snapshot: obj_addr -> prop) (g: heap) (w: U64.t)
  : Lemma (requires within_snapshot snapshot g /\ well_formed_heap g /\
                    (is_pointer w ==> in_use (outside_snapshot snapshot) g (resolve_object (w <: obj_addr) g)))
          (ensures within_snapshot snapshot (MM.darken g w) /\ well_formed_heap (MM.darken g w))

/// **A mark move keeps it**: a scanned field's target is a field of a grey
/// object, so in the snapshot; blackening changes no block's status; starting to
/// scan an object changes nothing.
val account_move (snapshot: obj_addr -> prop) (g g': heap) (sp sp': MP.scan_pos)
  : Lemma (requires within_snapshot snapshot g /\ well_formed_heap g /\ S.mark_move g sp g' sp')
          (ensures within_snapshot snapshot g')

/// ... and so do any number of moves (a mark slice).
val account_steps (snapshot: obj_addr -> prop) (g g': heap) (sp sp': MP.scan_pos)
  : Lemma (requires within_snapshot snapshot g /\ well_formed_heap g /\ S.mark_steps g sp g' sp')
          (ensures within_snapshot snapshot g')

/// **What marking keeps (safety)**: a mark move only recolours, so every
/// block keeps its size, tag and fields (`SPI.same_block`), and which blocks
/// are blue; so do any number of moves.
val mark_move_keeps_blocks (g g': heap) (sp sp': MP.scan_pos)
  : Lemma (requires well_formed_heap g /\ S.mark_move g sp g' sp')
          (ensures objects zero_addr g' == objects zero_addr g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      SPI.same_block g g' (hd_address x) /\ (is_blue x g' <==> is_blue x g)))

/// Greying a block that is not blue keeps every block (size, tag, fields),
/// which blocks are blue, and every other header.
val grey_keeps_blocks (g: heap) (t: obj_addr)
  : Lemma (requires Seq.mem t (objects zero_addr g) /\ ~(is_blue t g))
          (ensures objects zero_addr (makeGray t g) == objects zero_addr g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      SPI.same_block g (makeGray t g) (hd_address x) /\ (is_blue x (makeGray t g) <==> is_blue x g)) /\
                   (forall (y: obj_addr). y <> t ==> read_word (makeGray t g) (hd_address y) == read_word g (hd_address y)))

val mark_steps_keep_blocks (g g': heap) (sp sp': MP.scan_pos)
  : Lemma (requires well_formed_heap g /\ S.mark_steps g sp g' sp')
          (ensures objects zero_addr g' == objects zero_addr g /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      SPI.same_block g g' (hd_address x) /\ (is_blue x g' <==> is_blue x g)))

/// ---------------------------------------------------------------------------
/// The program
/// ---------------------------------------------------------------------------

/// **The trusted obligation for completeness**: the program writes a body
/// word of a scannable object `x` it can reach, and stores a value it holds
/// -- `x` and `v`'s target are covered by the snapshot (in `snapshot`, or dark).  This is
/// `SPM.program_write` at the account's definition of free, as the sweep
/// phase states the program's writes at `free_incremental c`.
let cycle_write (snapshot: obj_addr -> prop) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t) : prop =
  SPM.program_write (outside_snapshot snapshot) g x a v /\ scannable g x

/// **Loading keeps the obligation maintainable**: a field of an object
/// in the snapshot, loaded, is in the snapshot (the account is closed under the edges).
val account_load (snapshot: obj_addr -> prop) (g: heap) (u t: obj_addr)
  : Lemma (requires within_snapshot snapshot g /\ in_use (outside_snapshot snapshot) g u /\ MP.field_edge g u t)
          (ensures in_use (outside_snapshot snapshot) g t)

/// **A program write keeps it** (no barrier: idle, or into a fresh black
/// object's initialised fields).
val account_write (snapshot: obj_addr -> prop) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires within_snapshot snapshot g /\ SPM.program_write (outside_snapshot snapshot) g x a v)
          (ensures within_snapshot snapshot (write_word g a v))

/// **The barrier write keeps it**: 4.14's `caml_modify` while marking --
/// darken the old value, then write.  The old value is a field of `x`,
/// which is in the snapshot, so it is too.
val account_barrier (snapshot: obj_addr -> prop) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires within_snapshot snapshot g /\ well_formed_heap g /\ cycle_write snapshot g x a v)
          (ensures within_snapshot snapshot (write_word (MM.darken g (read_word g a)) a v))

/// What is free while the new object `obj` is uninitialised.
let outside_snapshot_or_new (snapshot: obj_addr -> prop) (obj: obj_addr) : free_def =
  fun g x -> outside_snapshot snapshot g x || x = obj

val outside_snapshot_or_new_ok (snapshot: obj_addr -> prop) (obj: obj_addr)
  : Lemma (free_def_ok (outside_snapshot_or_new snapshot obj))

/// **The account with `obj` fresh**: black, in the snapshot, its fields not
/// yet bound by the closure clause.
let within_snapshot_fresh (snapshot: obj_addr -> prop) (g: heap) (obj: obj_addr) : prop =
  dark_in_snapshot snapshot g /\ snapshot obj /\
  Seq.mem obj (objects zero_addr g) /\ is_black obj g /\
  well_formed_heap_with (outside_snapshot_or_new snapshot obj) g

/// **Allocation while marking**: the new object is added to `snapshot`
/// (`SPC.with_new`); it is fresh.
val account_alloc (snapshot: obj_addr -> prop) (outside_refs: obj_addr -> prop) (sp: MP.scan_pos) (g: heap) (fp: U64.t)
                  (wz: nat) (tag: SPM.tag_t)
  : Lemma (requires within_snapshot snapshot g /\ MP.marking_inv g outside_refs sp /\ FLA.fl_ascending g fp /\
                    wz >= 1 /\ tag <> infix_tag)
          (ensures (let r = AC.alloc_phase g fp Ph.Marking wz tag in
                    (r.SA.obj_out == 0UL ==> r.SA.heap_out == g) /\
                    (r.SA.obj_out <> 0UL ==>
                       GC.Spec.FusedSweep.is_obj r.SA.obj_out /\
                       within_snapshot_fresh (SPC.with_new snapshot r.SA.obj_out) r.SA.heap_out r.SA.obj_out)))

/// Writes into the fresh object's body keep it fresh.
val account_fresh_write (snapshot: obj_addr -> prop) (g: heap) (obj: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires within_snapshot_fresh snapshot g obj /\ SPM.in_body g obj a)
          (ensures within_snapshot_fresh snapshot (write_word g a v) obj)

/// Once its fields are in the snapshot (values the program holds), the
/// account holds.
val account_fresh_close (snapshot: obj_addr -> prop) (g: heap) (obj: obj_addr)
  : Lemma (requires within_snapshot_fresh snapshot g obj /\ SPM.fields_storable (outside_snapshot snapshot) g obj)
          (ensures within_snapshot snapshot g)

/// ---------------------------------------------------------------------------
/// The end of marking, and the cycle
/// ---------------------------------------------------------------------------

/// **When marking ends** every block black in the marked heap is in the snapshot
/// for.
val account_marked (snapshot: obj_addr -> prop) (g: heap)
  : Lemma (requires within_snapshot snapshot g)
          (ensures forall (x: obj_addr). SPC.survived_mark g x ==> snapshot x)

/// Mid-sweep, every block that is not free (not blue, not pending free) is
/// in the snapshot.  (This is `SPC.survivor_or_new` with the survivors of
/// marking folded into `snapshot`.)
let sweep_in_snapshot (snapshot: obj_addr -> prop) (g: heap) (c: U64.t) : prop =
  forall (x: obj_addr). in_use (SPI.free_incremental c) g x ==> snapshot x

/// **The account at the collector's phase.**  While marking, the mark
/// account; mid-sweep, every non-free block in the snapshot; idle again
/// (the sweep over), every block that is not blue in the snapshot.
let cycle_account (snapshot: obj_addr -> prop) (g: heap) (ph: Ph.gc_phase) : prop =
  match ph with
  | Ph.Marking -> within_snapshot snapshot g
  | Ph.Sweeping c -> sweep_in_snapshot snapshot g c
  | Ph.Idle -> forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==> snapshot x

/// **The hand-over**: when nothing is grey, the sweep starts with every
/// non-free block in the snapshot
/// (a block that is not free at the start of the sweep is black).
val cycle_handover (snapshot: obj_addr -> prop) (g: heap)
  : Lemma (requires within_snapshot snapshot g /\ Mark.noGreyObjects g)
          (ensures cycle_account snapshot g (Ph.Sweeping zero_addr))

/// **A sweep slice keeps it**, at whatever phase it leaves.
val cycle_sweep_slice (snapshot: obj_addr -> prop) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) (budget: nat)
  : Lemma (requires cycle_account snapshot g ph /\ ~(Ph.Marking? ph) /\
                    (Ph.Sweeping? ph ==> SPI.sweep_inv_incremental g fp (Ph.Sweeping?._0 ph)))
          (ensures (let (g', fp', ph') = SL.phase_slice g fp ph budget in
                    cycle_account snapshot g' ph'))

/// **An allocation mid-sweep keeps it**, with the new object added to `snapshot`.
val cycle_sweep_alloc (snapshot: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t) (wz: nat) (tag: SPM.tag_t)
  : Lemma (requires sweep_in_snapshot snapshot g c /\ SPI.sweep_shape g fp c)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
                    sweep_in_snapshot (SPC.with_new snapshot r.SA.obj_out) r.SA.heap_out c))

/// **A write into the body of a block that is not blue keeps it** mid-sweep
/// (a program write, or a fresh object's initialisation).
val cycle_sweep_write (snapshot: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t)
                      (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires sweep_in_snapshot snapshot g c /\ SPI.sweep_shape g fp c /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ SPM.in_body g x a)
          (ensures sweep_in_snapshot snapshot (write_word g a v) c)

/// A larger set accounts for as much, past marking.
val cycle_weaken (snapshot snapshot': obj_addr -> prop) (g: heap) (ph: Ph.gc_phase)
  : Lemma (requires cycle_account snapshot g ph /\ ~(Ph.Marking? ph) /\ (forall (x: obj_addr). snapshot x ==> snapshot' x))
          (ensures cycle_account snapshot' g ph)

/// **The cycle is complete**: idle again, every block that is not free is
/// in the snapshot -- reachable when the cycle started, or allocated or
/// promoted since -- so every other address is freed.
val cycle_complete (snapshot: obj_addr -> prop) (g: heap)
  : Lemma (requires cycle_account snapshot g Ph.Idle)
          (ensures forall (x: obj_addr). ~(snapshot x) ==> SPC.freed g x)
