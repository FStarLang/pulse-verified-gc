/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPhase.Completeness - the sweep phase frees what marking left dead
/// ---------------------------------------------------------------------------
///
/// Stop-the-world, every object unreachable from the roots at mark time ends
/// up free (`GC.Spec.Correctness.major_gc_unreachable_final_blue`), and the
/// sweep loses no free space (`GC.Spec.FusedSweep.Lossless`).  This is the
/// same for the incremental sweep: **when the sweep ends, every word of a
/// block that was dead when marking ended lies in a free block** -- unless an
/// allocation since handed out a block over it, and then it lies in that new
/// object.  Objects that die during the sweep are floating garbage, left for
/// the next cycle; nothing is said about them.
///
/// The statement is carried as an account of the non-free blocks
/// (`survivor_or_new g0 since g c`): the walk of `g` ends where the walk of
/// the marked heap `g0` ended, and every block not free during the sweep
/// (`free_incremental c`) is a survivor of marking -- black in `g0`, with
/// the size it had there (`survivor`), so over the same words -- or was
/// allocated since marking ended (`since`, a ghost set of addresses that only
/// an allocation or a promotion grows).  It holds from the marked heap with
/// nothing allocated (`survivor_or_new_start`), and every event keeps it:
///
///   * sweep steps, `k` of them, or a slice (`survivor_or_new_steps`,
///     `survivor_or_new_slice`): a step frees, never makes a block non-free,
///     and keeps the size of every non-free block;
///   * an allocation (`survivor_or_new_alloc`), with the new object added to
///     `since` (`with_new`);
///   * a write into the body of a non-free block -- a program write, or the
///     initialisation of a fresh object (`survivor_or_new_body_write`);
///   * a minor collection, with its promoted copies added to `since`
///     (`GC.Gen.SweepPhase.Completeness`).
///
/// At the end of the sweep nothing is pending free, so the account is about
/// the blocks that are not blue (`idle_account`).  The end theorem is by
/// coverage (`covered_by_end`, `covered_at_idle`): every word of a block
/// white in the marked heap lies in a blue block, or in a block in `since`.
/// The walk of the end heap covers the words of the marked heap's walk, a
/// block over such a word that is neither blue nor new is a survivor with
/// its old extent, and two blocks of the marked heap do not overlap.
/// Marking leaves white exactly the unreachable objects
/// (`dead_at_mark_white`), which gives the reachability form
/// (`unreachable_covered_at_idle`).  The older, address-based form -- no
/// non-free block starts at a dead block's address (`freed_by_end`,
/// `unreachable_freed_by_end`) -- is kept.
///
/// `since` is an argument here, and any larger set accounts for as much
/// (`survivor_or_new_weaken`); a run of the sweep phase fixes it
/// (`GC.Gen.SweepPhase.Cycle`).

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
module W = GC.Spec.Walk
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
module LL = GC.Spec.FusedSweep.Lossless

/// ---------------------------------------------------------------------------
/// The account
/// ---------------------------------------------------------------------------

/// The objects marking left black: they survive this cycle.
let survived_mark (g0: heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g0) /\ is_black x g0

/// A survivor of marking, with the size it had in the marked heap `g0`: its
/// block in `g` is over the same words as in `g0`.
let survivor (g0 g: heap) (x: obj_addr) : prop =
  survived_mark g0 x /\ wosize_of_object x g == wosize_of_object x g0

/// No address: nothing is allocated yet when the sweep starts.
let nothing_new : obj_addr -> prop = fun _ -> False

/// `since`, and the object `obj` an allocation just handed out.
let with_new (since: obj_addr -> prop) (obj: U64.t) : obj_addr -> prop =
  fun x -> since x \/ x == obj

/// **Every non-free block is a survivor or new**: at cursor `c`, the walk of
/// `g` ends where the walk of the marked heap `g0` ended, and every block of
/// `g` not free during the sweep was black in `g0` and has the size it had
/// there, or its address was allocated since marking ended (`since`).
let survivor_or_new (g0: heap) (since: obj_addr -> prop) (g: heap) (c: U64.t) : prop =
  W.walk_end g zero_addr == W.walk_end g0 zero_addr /\
  (forall (x: obj_addr). in_use (free_incremental c) g x ==> survivor g0 g x \/ since x)

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

/// **Sweep steps keep it**: the non-free blocks before and after are the
/// same, with the same sizes, and the walk ends where it did.
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
/// it makes no other block non-free (`Mut.alloc_in_use`), keeps the header
/// of every non-free block (`Mut.alloc_keeps`), and keeps where the walk
/// ends (`Mut.alloc_walk_end`).
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

/// **The account once the sweep has ended**: the heap is dense, its walk
/// ends where the marked heap's did, and every block that is not blue is a
/// survivor of marking with its size, or new.
let idle_account (g0: heap) (since: obj_addr -> prop) (g: heap) : prop =
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  W.walk_end g zero_addr == W.walk_end g0 zero_addr /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
     survivor g0 g x \/ since x)

/// The word `p` lies in a free (blue) block of `g`, or in a block of `g`
/// allocated since marking ended.
let free_or_new_at (g: heap) (since: obj_addr -> prop) (p: nat) : prop =
  LL.blue_covered g p \/
  (exists (y: obj_addr). Seq.mem y (objects zero_addr g) /\ since y /\ LL.in_extent g y p)

/// **Coverage once the sweep has ended**: every word of a block white in the
/// marked heap `g0` lies in a free block, or in a block allocated since.
val covered_at_idle (g0: heap) (since: obj_addr -> prop) (g: heap)
  : Lemma (requires idle_account g0 since g)
          (ensures forall (x: obj_addr) (p: nat).
                     white_after_mark g0 x /\ LL.in_extent g0 x p ==> free_or_new_at g since p)

/// Freed: not a non-free block -- not a block of the walk (merged into a free
/// block), or a free (blue) block.
let freed (g: heap) (x: obj_addr) : prop =
  ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))

/// **The end of the sweep: everything dead at mark is freed.**  When the
/// cursor reaches the end of the heap, nothing is pending free, so the
/// account is the idle one, and every object white in the marked heap is
/// freed, or its address was allocated since.
val freed_by_end (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\ sweep_done c /\ survivor_or_new g0 since g c)
          (ensures idle_account g0 since g /\
                   (forall (x: obj_addr). white_after_mark g0 x ==> freed g x \/ since x))

/// **The end of the sweep, by coverage**: every word of a block white in
/// the marked heap lies in a free block, or in a block allocated since.
val covered_by_end (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (c: U64.t)
  : Lemma (requires sweep_inv_incremental g fp c /\ sweep_done c /\ survivor_or_new g0 since g c)
          (ensures forall (x: obj_addr) (p: nat).
                     white_after_mark g0 x /\ LL.in_extent g0 x p ==> free_or_new_at g since p)

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

/// **Completeness of the sweep phase, by coverage**: once the sweep has
/// ended, every word of a block dead at mark lies in a free block, or in a
/// block allocated since.
val unreachable_covered_at_idle (h_init h_mark: heap) (roots: seq obj_addr) (fp0: U64.t)
                                (since: obj_addr -> prop) (g: heap)
  : Lemma (requires Corr.mark_post h_init h_mark roots fp0 /\ roots_in_graph h_init roots /\
                    idle_account h_mark since g)
          (ensures forall (x: obj_addr) (p: nat).
                     dead_at_mark h_init h_mark roots x /\ LL.in_extent h_mark x p ==>
                     free_or_new_at g since p)

/// ---------------------------------------------------------------------------
/// At the collector's phase
/// ---------------------------------------------------------------------------

/// The account at the collector's phase: mid-sweep, the sweep phase and the
/// account at its cursor; idle (the sweep has ended), the idle account.
let phase_account (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t) (ph: Ph.gc_phase) : prop =
  match ph with
  | Ph.Sweeping c -> sweep_inv_incremental g fp c /\ survivor_or_new g0 since g c
  | Ph.Idle -> idle_account g0 since g

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
/// allocated since; and every word of it lies in a free block, or in a block
/// allocated since.
val phase_account_idle (g0: heap) (since: obj_addr -> prop) (g: heap) (fp: U64.t)
  : Lemma (requires phase_account g0 since g fp Ph.Idle)
          (ensures (forall (x: obj_addr). white_after_mark g0 x ==> freed g x \/ since x) /\
                   (forall (x: obj_addr) (p: nat).
                      white_after_mark g0 x /\ LL.in_extent g0 x p ==> free_or_new_at g since p))
