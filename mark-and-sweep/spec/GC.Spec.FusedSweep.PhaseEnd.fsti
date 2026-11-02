/// ---------------------------------------------------------------------------
/// GC.Spec.FusedSweep.PhaseEnd - what an incremental sweep leaves behind
/// ---------------------------------------------------------------------------
///
/// When the sweep phase (`GC.Spec.FusedSweep.Phase.sweeping`) reaches the end
/// of the heap, the end lemma of the sweep (`GC.Spec.FusedSweep.End`) applies
/// against the reference heap, and the reference heap's relation to the heap
/// marking left turns it into facts about the result that mention no
/// reference heap:
///
///   * `swept_clean`: the walk covers the heap; the free list is exact and
///     ascending; every object is white or free (no black or grey object);
///     no object is infix;
///   * `live_survive` -- **safety**: every object that was live when marking
///     finished is still an object, white, with its size and tag.  Its fields
///     may have changed since, by the program's writes; nothing the sweep did
///     freed it.
///
/// And while the sweep is running, the free list is exact, so an allocation
/// fails only when no free block anywhere is big enough
/// (`sweeping_oom_no_fit`, #29 mid-sweep).

module GC.Spec.FusedSweep.PhaseEnd

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.FusedSweep.Phase

module U64 = FStar.UInt64
module FLA = GC.Spec.FreeList.Ascending
module FSE = GC.Spec.FusedSweep.End
module AC = GC.Spec.Allocator.Cursor

/// The heap a sweep leaves: dense, with an exact ascending free list, every
/// object white or free, none infix.
let swept_clean (g: heap) (fp: U64.t) : prop =
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
  FLA.fl_ascending g fp /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> is_white x g \/ is_blue x g) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_infix x g))

/// Every object live when marking finished is still an object, white, with
/// its size and tag.
let live_survive (g0 g: heap) : prop =
  forall (x: obj_addr). Seq.mem x (objects zero_addr g0) /\ is_black x g0 ==>
    Seq.mem x (objects zero_addr g) /\ is_white x g /\
    wosize_of_object x g == wosize_of_object x g0 /\
    tag_of_object x g == tag_of_object x g0

/// **The end of the sweep phase.**
val sweeping_end (g0 g1 g: heap) (fp: U64.t) (st: sweep_state)
  : Lemma (requires sweeping g0 g1 g fp st /\ U64.v st.cursor + 8 >= heap_size)
          (ensures FSE.sweep_post g1 g fp /\ swept_clean g fp /\ live_survive g0 g)

/// **#29 mid-sweep**: an allocation fails only when no free block is big
/// enough.
val sweeping_oom_no_fit (g0 g1 g: heap) (fp: U64.t) (st: sweep_state) (wz: nat)
                          (tag: U64.t{U64.v tag < 256})
  : Lemma (requires sweeping g0 g1 g fp st /\ wz >= 1 /\
                    (fst (AC.alloc_phase g fp (GC.Spec.Phase.Sweeping st) wz tag)).GC.Spec.Allocator.obj_out == 0UL)
          (ensures forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ is_blue x g ==>
                     U64.v (wosize_of_object x g) < wz)
