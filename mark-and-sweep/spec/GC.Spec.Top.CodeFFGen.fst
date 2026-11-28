/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeFFGen - the first-fit run in akhil's generational terms
/// ---------------------------------------------------------------------------
///
/// Design doc §18, plan step 1 (first-fit mark and barrier).  What the
/// glue `GC.Impl.FFGen` shares with the modules beside this one:
///   - `spof`: the model's scan (`T.scan`, a block and its next field,
///     0-based) as akhil's scan position (`MP.scan_pos`, the block's first
///     field address and its next field, 1-based);
///   - L13 for the major heap: the model's per-phase shape of the first-fit
///     allocator (`FFAlloc.ishape`, `mshape`, `sshape`) gives the shape
///     akhil's Pulse calls ask, idle the stop-the-world shape
///     (`GenInv.major_heap_shape`), and at every phase the minor
///     collection's major half (`GenInv.major_shape_with` at the phase's
///     definition of free, `FFAllocOk.ffree_of`), while marking what the
///     mark slice asks (`heap_ok`).

module GC.Spec.Top.CodeFFGen

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Base
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MS = GC.Gen.MarkState
module GI = GC.Gen.Incremental
module GenInv = GC.Gen.HeapInvariant
module PCS = GC.Gen.PostCollectionShape
module GP = GC.Gen.Promote
module SPMi = GC.Gen.SweepPhase.Minor
module SPI = GC.Spec.SweepPhase.Intrinsic
module FLA = GC.Spec.FreeList.Ascending
module FAl = GC.Spec.Top.FFAlloc
module FAO = GC.Spec.Top.FFAllocOk
module CF = GC.Spec.Top.CodeFF
module Abs = GC.Spec.Top.Abs

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The scan
/// ---------------------------------------------------------------------------

/// The model's scan as akhil's scan position: none is `scan_none`; the block
/// `o` (its header at `o`) with next field `i` is its first field address and
/// field `i + 1` (a block inside the heap; under the run invariant the
/// scanned address is one).
let spof (sc: T.scan) : MP.scan_pos =
  match sc with
  | Some (o, i) -> if Abs.pos o + 8 < heap_size then { MP.cur = Abs.obj_of o; MP.fld = i + 1 } else MP.scan_none
  | None -> MP.scan_none

/// ---------------------------------------------------------------------------
/// L13: the major heap's shape
/// ---------------------------------------------------------------------------

/// An empty nursery (any reset one): its shape, and nothing of its fields.
let reset_facts (m: minor_state) (free: free_def) (g: heap)
  : Lemma (GenInv.minor_heap_shape (minor_reset m) /\ GenInv.minor_major_fields_not_free free (minor_reset m) g)
  = GenInv.minor_reset_heap_shape m;
    let h (obj: U64.t) (j: nat)
      : Lemma (requires Seq.mem obj (minor_objects (minor_reset m)) /\
                        j < minor_scan_wosize (minor_reset m) obj /\
                        is_pointer_field (minor_read_field (minor_reset m) obj j))
              (ensures in_use free g (resolve_object ((minor_read_field (minor_reset m) obj j) <: obj_addr) g) /\
                       infix_addr_wf g (objects zero_addr g) ((minor_read_field (minor_reset m) obj j) <: obj_addr))
      = minor_reset_objects_not_mem m obj
    in
    GenInv.minor_major_fields_not_free_intro free (minor_reset m) g h

/// A nursery to reset (the shape lemmas below are about any).
let m0 : minor_state = minor_reset (minor_init (Seq.create minor_heap_size 0uy))

/// Mid-sweep at `c`: the minor collection's major half.
let sweep_major (g: heap) (fp c: U64.t)
  : Lemma (requires SPI.sweep_inv_incremental g fp c)
          (ensures GenInv.major_shape_with (Ph.Sweeping c) (SPI.free_incremental c) g fp)
  = reset_facts m0 (SPI.free_incremental c) g;
    GI.phase_shape_sweeping m0 g fp c MP.scan_none;
    GI.phase_shape_collection m0 g fp (Ph.Sweeping c) MP.scan_none;
    GI.phase_free_sweeping c;
    GenInv.collection_shape_with_elim (Ph.Sweeping c) (SPI.free_incremental c) m0 g fp

/// Idle: the stop-the-world shape.
let idle_major (g: heap) (fp: U64.t)
  : Lemma (requires FAl.ishape g fp) (ensures GenInv.major_heap_shape g fp)
  = reveal_opaque (`%FAl.ishape) (FAl.ishape g fp);
    eliminate exists (c: U64.t). FAl.idle_at g fp c
    with begin
      reset_facts m0 (SPI.free_incremental c) g;
      GI.phase_shape_sweeping m0 g fp c MP.scan_none;
      GI.sweep_end_shape m0 g fp c MP.scan_none;
      GenInv.collection_heap_shape_elim m0 g fp
    end

/// Idle, at `free_stw`.
let idle_with (g: heap) (fp: U64.t)
  : Lemma (requires FAl.ishape g fp) (ensures GenInv.major_shape_with Ph.Idle free_stw g fp)
  = idle_major g fp;
    GenInv.major_heap_shape_as_free_stw g fp

/// While marking: what the mark slice asks ...
let mark_heap_ok (g: heap) (fp: U64.t)
  : Lemma (requires FAl.mshape g fp)
          (ensures well_formed_heap g /\ heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0)
  = reveal_opaque (`%FAl.mshape) (FAl.mshape g fp)

/// ... and the minor collection's major half, at `free_stw`.
let mark_major (g: heap) (fp: U64.t)
  : Lemma (requires FAl.mshape g fp) (ensures GenInv.major_shape_with Ph.Marking free_stw g fp)
  = reveal_opaque (`%FAl.mshape) (FAl.mshape g fp);
    free_stw_ok ();
    GP.free_stw_allocations_not_free Ph.Marking;
    PCS.free_list_shape_of_ascending g fp;
    GenInv.major_shape_with_intro Ph.Marking free_stw g fp

/// **At every phase**, the minor collection's major half at the phase's
/// definition of free.
let major_with (ph: T.phase U64.t) (g: heap) (fp: U64.t)
  : Lemma (requires CF.shape_of ph g fp)
          (ensures GenInv.major_shape_with (FAl.gph ph) (FAO.ffree_of ph) g fp)
  = match ph with
    | T.Idle -> idle_with g fp
    | T.Marking -> mark_major g fp
    | T.Sweeping c ->
      reveal_opaque (`%FAl.sshape) (FAl.sshape g fp c);
      sweep_major g fp c
