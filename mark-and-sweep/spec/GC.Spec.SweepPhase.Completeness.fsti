/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Completeness - the sweep phase frees what marking left dead
/// ---------------------------------------------------------------------------
///
/// Stop-the-world, every object unreachable from the roots at mark time ends
/// up free (`GC.Spec.Correctness.major_gc_unreachable_final_blue`).  This is
/// the same for the incremental sweep: **when the sweep ends, every block that
/// was dead when marking ended has been freed** -- it is no longer a non-free
/// block (it was merged into a free block, or is a free block itself) -- unless
/// its address was handed out again by an allocation since, and then the
/// block there is a new object.  Objects that die during the sweep are
/// floating garbage, left for the next cycle; nothing is said about them.
///
/// The statement is carried as an account of the non-free blocks
/// (`survivor_or_new g0 since g c`): every block not free during the sweep
/// (`free_incremental c`) is a survivor of marking -- black in the marked
/// heap `g0` -- or was allocated since marking ended (`since`, a ghost set of
/// addresses that only an allocation grows).  It holds from the marked heap
/// with nothing allocated (`survivor_or_new_start`), and every event keeps
/// it:
///
///   * sweep steps, `k` of them, or a slice (`survivor_or_new_steps`,
///     `survivor_or_new_slice`): a step frees, never makes a block non-free;
///   * an allocation (`survivor_or_new_alloc`), with the new object added to
///     `since` (`with_new`);
///   * a write into the body of a non-free block -- a program write, or the
///     initialisation of a fresh object (`survivor_or_new_body_write`);
///   * a minor collection, with its promoted copies added to `since`
///     (`GC.Gen.SweepPhase.Completeness`).
///
/// At the end of the sweep nothing is pending free, so the account is about
/// the blocks that are not blue (`freed_by_end`): each is a survivor or new,
/// and so a block dead at mark -- white in the marked heap, which marking
/// leaves exactly for the unreachable objects (`dead_at_mark_white`) -- is
/// freed by then, or its address holds a new object
/// (`unreachable_freed_by_end`).
///
/// Survivors are named by address only; that a survivor is still the same
/// block (never freed while reachable) is safety
/// (`GC.Gen.SweepPhase.Safety`).

module GC.Spec.SweepPhase.Completeness

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Intrinsic

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module Mut = GC.Spec.SweepPhase.Mutator
module SL = GC.Spec.SweepPhase.Slice
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Corr = GC.Spec.Correctness
module HeapModel = GC.Spec.HeapModel
module HeapGraph = GC.Spec.HeapGraph
module Graph = GC.Spec.Graph
module Ph = GC.Spec.Phase

/// ---------------------------------------------------------------------------
/// The account
/// ---------------------------------------------------------------------------

/// The objects marking left black: they survive this cycle.
let survived_mark (g0: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g0) /\ is_black x g0

/// No address: nothing is allocated yet when the sweep starts.
let nothing_new : obj_addr -> prop = fun _ -> False

/// `since`, and the object `obj` an allocation just handed out.
let with_new (since: obj_addr -> prop) (obj: U64.t) : obj_addr -> prop =
  fun x -> since x \/ x == obj

/// **Every non-free block is a survivor or new**: at cursor `c`, every block
/// of `g` not free during the sweep was black in the marked heap `g0`, or its
/// address was allocated since marking ended (`since`).
let survivor_or_new (g0: heap) (since: obj_addr -> prop) (g: heap) (c: U64.t) : prop =
  forall (x: obj_addr). in_use (free_incremental c) g x ==> survived_mark g0 x \/ since x

/// A larger set of new addresses accounts for as much.
val survivor_or_new_weaken (g0: heap) (since since': obj_addr -> prop) (g: heap) (c: U64.t)
  : Lemma (requires survivor_or_new g0 since g c /\ (forall (x: obj_addr). since x ==> since' x))
          (ensures survivor_or_new g0 since' g c)

/// ---------------------------------------------------------------------------
/// Start
/// ---------------------------------------------------------------------------

/// **From the marked heap**: with nothing grey, every block that is not free
/// at the start of the sweep (not blue, and not white: everything white is
/// pending free) is black.
val survivor_or_new_start (g0: heap)
  : Lemma (requires Mark.noGreyObjects g0)
          (ensures survivor_or_new g0 nothing_new g0 sweep_start.cursor)

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

/// **Sweep steps keep it**: the non-free blocks before and after are the same.
val survivor_or_new_steps (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t) (k: nat)
  : Lemma (requires sweep_inv_incremental g fp c /\ survivor_or_new g0 since g c)
          (ensures (let (g', fp', st') = sweep_steps g fp (state_at g c) k in
                    survivor_or_new g0 since g' st'.cursor))

/// So does a slice.
val survivor_or_new_slice (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t) (budget: nat)
  : Lemma (requires sweep_inv_incremental g fp c /\ survivor_or_new g0 since g c)
          (ensures (let (g', fp', st') = SL.sweep_slice g fp (state_at g c) budget in
                    survivor_or_new g0 since g' st'.cursor))

/// ---------------------------------------------------------------------------
/// The program
/// ---------------------------------------------------------------------------

/// **An allocation keeps it**, with the new object among the new addresses:
/// it makes no other block non-free (`Mut.alloc_in_use`).
val survivor_or_new_alloc (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t)
                          (wz: nat) (tag: Mut.tag_t)
  : Lemma (requires sweep_shape g fp c /\ survivor_or_new g0 since g c)
          (ensures (let r = AC.alloc_phase g fp (SA.Sweeping c) wz tag in
                    survivor_or_new g0 (with_new since r.SA.obj_out) r.SA.heap_out c))

/// **A write into the body of a block that is not blue keeps it**: it keeps
/// the walk and every header.  This covers the program's writes
/// (`Mut.program_write`) and the initialisation of a fresh object
/// (`Mut.fresh_ok`).
val survivor_or_new_body_write (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t)
                               (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires sweep_shape g fp c /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    Mut.in_body g x a /\ survivor_or_new g0 since g c)
          (ensures survivor_or_new g0 since (write_word g a v) c)

/// ---------------------------------------------------------------------------
/// The end
/// ---------------------------------------------------------------------------

/// Freed: not a non-free block -- not a block of the walk (merged into a free
/// block), or a free (blue) block.
let freed (g: heap) (x: obj_addr) : prop =
  ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))

/// **The end of the sweep: everything dead at mark is freed.**  When the
/// cursor reaches the end of the heap, every block that is not free is a
/// survivor of marking or new, and every object white in the marked heap is
/// freed, or its address was allocated since.
val freed_by_end (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\ sweep_done c /\ survivor_or_new g0 since g c)
          (ensures (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
                      survived_mark g0 x \/ since x) /\
                   (forall (x: obj_addr). white_after_mark g0 x ==> freed g x \/ since x))

/// ---------------------------------------------------------------------------
/// Dead at mark: unreachable
/// ---------------------------------------------------------------------------

/// The roots reach the heap's graph (the hypotheses of the reachability
/// clause of `Corr.mark_post`).
let roots_in_graph (h: heap) (roots: seq obj_addr) : prop =
  let g = HeapModel.create_graph h in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  Graph.graph_wf g /\ Graph.is_vertex_set roots' /\ Graph.subset_vertices roots' g.vertices

/// **Dead at mark**: a block of the marked heap `h_mark`, not free, and not
/// reachable from the roots in the heap `h_init` marking started from.
let dead_at_mark (h_init h_mark: heap) (roots: seq obj_addr) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr h_mark) /\ ~(is_blue x h_mark) /\ ~(Corr.heap_reachable h_init roots x)

/// Marking leaves the dead blocks white, and only them.
val dead_at_mark_white (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t) (x: obj_addr)
  : Lemma (requires Corr.mark_post h_init h_mark roots fp /\ roots_in_graph h_init roots)
          (ensures dead_at_mark h_init h_mark roots x <==> white_after_mark h_mark x)

/// **Completeness of the sweep phase**: at its end, every block dead at mark
/// -- unreachable from the roots when marking ended -- is freed, or its
/// address was allocated since.
val unreachable_freed_by_end (h_init h_mark: heap) (roots: seq obj_addr) (fp0: U64.t)
                             (since: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires Corr.mark_post h_init h_mark roots fp0 /\ roots_in_graph h_init roots /\
                    sweep_inv_incremental g fp c /\ sweep_done c /\
                    survivor_or_new h_mark since g c)
          (ensures forall (x: obj_addr). dead_at_mark h_init h_mark roots x ==> freed g x \/ since x)

/// ---------------------------------------------------------------------------
/// At the collector's phase
/// ---------------------------------------------------------------------------

/// The account at the collector's phase: mid-sweep, the sweep phase and the
/// account at its cursor; idle (the sweep has ended), every block that is not
/// free is a survivor of marking or new.  It is an account of one sweep, from
/// its marked heap `g0`: there is none while marking.
let phase_account (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) : prop =
  match ph with
  | Ph.Sweeping c -> sweep_inv_incremental g fp c /\ survivor_or_new g0 since g c
  | Ph.Marking -> False
  | Ph.Idle ->
      forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
        survived_mark g0 x \/ since x

/// From the marked heap, at the start of the sweep.
val phase_account_start (g0: heap) (fp: U64.t)
  : Lemma (requires sweep_pre g0 fp /\ Mark.noGreyObjects g0 /\ Mark.tri_color_invariant g0)
          (ensures phase_account g0 nothing_new g0 fp (Ph.Sweeping sweep_start.cursor))

/// **A slice at the collector's phase keeps it**, and so does finishing the
/// sweep (a slice with an unbounded budget).
val phase_account_slice (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t)
                        (ph: Ph.gc_phase) (budget: nat)
  : Lemma (requires phase_account g0 since g fp ph)
          (ensures (let (g', fp', ph') = SL.phase_slice g fp ph budget in
                    phase_account g0 since g' fp' ph'))

/// **Idle again, everything dead at mark is freed**, or its address was
/// allocated since.
val phase_account_idle (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t)
  : Lemma (requires phase_account g0 since g fp Ph.Idle)
          (ensures forall (x: obj_addr). white_after_mark g0 x ==> freed g x \/ since x)
