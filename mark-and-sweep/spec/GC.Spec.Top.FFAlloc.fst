/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFAlloc - akhil's first-fit allocator, as a component of the
/// top-level specification
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  akhil's first-fit allocator (`GC.Spec.Allocator.Phase.alloc_at`,
/// `GC.Spec.Allocator.Cursor.alloc_phase`) and fused sweep
/// (`GC.Spec.FusedSweep.sweep_step`), on the byte heap, through the byte
/// representation (GC.Spec.Top.ByteRep):
///   - the state is the free list's head and the bytes below `zero_addr`
///     (which the representation does not read, GC.Spec.Top.Low);
///   - the sweep's progress is akhil's cursor; a model block is unswept when
///     its header is at or above it.  The sweep's caches (`swept_tail`,
///     `last_fragment`) are derived from the heap and the cursor
///     (`SweepPhase.Intrinsic.state_at`), so they are not state;
///   - allocation is first-fit at the phase (`alloc_at`), whose colour is
///     `Phase.allocation_color`: the model's `colour_at`;
///   - free means blue, read from the header;
///   - the invariant per phase:
///       * mid-sweep at `c`, akhil's sweep invariant
///         (`sweep_inv_incremental g fp c`: blue or white in front counts as
///         free) and the walk to the end of the heap;
///       * idle, the same at some cursor where the sweep is done;
///       * marking, the colour-blind shape: well formed (blue is free),
///         dense, the walk to the end, the free list exact and ascending.
///
/// This module: the definitions.

module GC.Spec.Top.FFAlloc

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module Ph = GC.Spec.Phase
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AC = GC.Spec.Allocator.Cursor
module FLA = GC.Spec.FreeList.Ascending
module SPI = GC.Spec.SweepPhase.Intrinsic

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The sweep's progress
/// ---------------------------------------------------------------------------

/// The progress is the cursor: the header address of the next block to visit.
/// A model block is unswept when its header is at or above it.
let ffunswept (c: U64.t) (o: nat) : bool = pos o >= U64.v c

let ffk : T.sweep_kind = { T.progress = U64.t; T.unswept = ffunswept }

/// The collector's phase, as akhil's.
let gph (ph: T.phase U64.t) : Ph.gc_phase =
  match ph with
  | T.Idle -> Ph.Idle
  | T.Marking -> Ph.Marking
  | T.Sweeping c -> Ph.Sweeping c

/// ---------------------------------------------------------------------------
/// The state and the invariant
/// ---------------------------------------------------------------------------

/// The free list's head, and the bytes below the heap.
noeq type ffst = { fp: U64.t; lo: low_t }

/// The heap the first-fit functions run on.
let gl (g: heap) (s: ffst) : heap = set_low g s.lo

/// Every block in use has a field (design doc §13, G40: akhil's sweep
/// steps only at a cursor with a word after the header, so a header-only
/// block at the end of the heap would never be swept; no allocation or
/// promotion makes one).
let nz (g: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==> U64.v (wosize_of_object x g) >= 1

/// The shape while marking: well formed with blue free, dense, the walk to
/// the end, the free list exact and ascending.
[@@"opaque_to_smt"]
let mshape (g: heap) (fp: U64.t) : prop =
  well_formed_heap g /\ heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  W.reaches g zero_addr heap_size /\ FLA.fl_ascending g fp /\ nz g

/// Idle: the sweep's invariant at a cursor where the sweep is done.
let idle_at (g: heap) (fp: U64.t) (c: U64.t) : prop =
  SPI.sweep_done c /\ SPI.sweep_inv_incremental g fp c

[@@"opaque_to_smt"]
let ishape (g: heap) (fp: U64.t) : prop =
  W.reaches g zero_addr heap_size /\ nz g /\ (exists (c: U64.t). idle_at g fp c)

/// Mid-sweep at `c`: the sweep's invariant.
[@@"opaque_to_smt"]
let sshape (g: heap) (fp: U64.t) (c: U64.t) : prop =
  W.reaches g zero_addr heap_size /\ nz g /\ SPI.sweep_inv_incremental g fp c

let ffinv (ph: T.phase U64.t) (g: heap) (s: ffst) : prop =
  match ph with
  | T.Idle -> ishape (gl g s) s.fp
  | T.Marking -> mshape (gl g s) s.fp
  | T.Sweeping c -> sshape (gl g s) s.fp c

/// ---------------------------------------------------------------------------
/// Free, room, allocation
/// ---------------------------------------------------------------------------

/// Free: a blue block.
let fffree (s: ffst) (g: heap) (o: nat) : GTot bool =
  match abs_hd g o with Some h -> h.M.col = M.Blue | None -> false

/// A model tag, as a header's tag.
let tg (tag: M.tag_t) : AP.tag_t = assert_norm (256 < pow2 64); U64.uint_to_t tag

let tg_v (tag: M.tag_t) : Lemma (U64.v (tg tag) == tag) = assert_norm (256 < pow2 64)

/// First-fit at the phase.
let ffres (ph: T.phase U64.t) (g: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t) : GTot SA.alloc_result =
  AP.alloc_at (gph ph) (gl g s) s.fp sz (tg tag)

let ffalloc (ph: T.phase U64.t) (g: heap) (s: ffst) (sz: M.size_t) (tag: M.tag_t) : GTot (heap & ffst & T.result) =
  let r = ffres ph g s sz tag in
  if r.SA.obj_out = 0UL then (g, s, T.NoRoom)
  else (r.SA.heap_out, { fp = r.SA.fp_out; lo = low r.SA.heap_out }, T.Ok (maddr r.SA.obj_out))

/// Room: the allocation succeeds (the tag and the phase play no part).
let ffroom (ph: T.phase U64.t) (s: ffst) (g: heap) (sz: M.size_t) : GTot bool =
  (ffres ph g s sz 0).SA.obj_out <> 0UL

/// ---------------------------------------------------------------------------
/// The initial heap: one free block from `zero_addr` to the end
/// ---------------------------------------------------------------------------

let zero_heap : heap = Seq.create heap_size 0uy

/// The words of the heap past `zero_addr`, but the header.
let init_wz : nat = (heap_size - base) / 8 - 1

let init_facts (_: unit)
  : Lemma (heap_size - base >= 16 /\ (heap_size - base) % 8 == 0 /\ init_wz >= 1 /\ init_wz < pow2 54 /\
           base + 8 * (init_wz + 1) == heap_size /\ base % 8 == 0 /\ base + 8 < heap_size)
  = base_facts ();
    assert (U64.v zero_addr % 8 == 0 /\ heap_size % 8 == 0);
    FStar.Math.Lemmas.pow2_plus 54 3;
    assert_norm (pow2 3 == 8)

let init_heap : heap =
  init_facts ();
  let g1 = write_word zero_heap zero_addr (GC.Spec.FusedSweep.free_header init_wz) in
  let a1 : hp_addr = U64.uint_to_t (base + 8) in
  write_word g1 a1 0UL

let init_fp : U64.t = init_facts (); U64.uint_to_t (base + 8)

let ffinit (n: nat) : GTot (heap & ffst) = (init_heap, { fp = init_fp; lo = low init_heap })

let ffa : T.allocator heap ffk = {
  T.state = ffst;
  T.init = ffinit;
  T.inv = ffinv;
  T.free = fffree;
  T.room = ffroom;
  T.alloc = ffalloc;
}
