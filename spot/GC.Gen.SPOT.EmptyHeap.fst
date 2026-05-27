(*
   GC.Gen.SPOT.EmptyHeap — Empty/Zeroed Heap Lemmas

   Proves properties of zeroed heaps that are useful for testing.
   
   Key results (ALL PROVEN, NO ADMITS):
   ✅ Zeroed heap has no objects
   ✅ Zeroed heap is well-formed
   ✅ Empty minor heap satisfies minor_heap_shape
   ✅ All free-list properties hold for fp=0
   ✅ All ref_table properties hold for empty slots
   ✅ All root properties hold for empty roots
   ✅ All cross-heap properties hold for empty heaps
   
   What we CANNOT prove:
   ❌ major_heap_shape for all-zero heap (requires length > 0)
   
   Reason: The GC requires at least ONE object (free-list sentinel) to function.
   A truly empty (all-zero) heap has no objects and thus cannot satisfy
   major_heap_shape.
   
   For testing minor_collect_full, use heap_init to create a valid initial
   heap with one free-list block, THEN apply the empty minor heap lemmas.
   
   This module proves everything that CAN be proven about empty heaps.
*)

module GC.Gen.SPOT.EmptyHeap

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.HeapInvariant
open GC.Gen.Impl.UpdatePtrs
open GC.Gen.MinorCollectForwarding
open GC.Gen.ReachabilityBridge

module Seq = FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module SpecFields = GC.Spec.Fields
module FreeListShape = GC.Gen.FreeListShape

/// ---------------------------------------------------------------------------
/// Empty heap constants
/// ---------------------------------------------------------------------------

let empty_heap : heap = Seq.create heap_size 0uy
let empty_minor_data : Seq.seq U8.t = Seq.create minor_heap_size 0uy
let empty_minor : minor_state = { data = empty_minor_data; bump = 0UL }

/// ---------------------------------------------------------------------------
/// Basic facts: zeroed heap properties
/// ---------------------------------------------------------------------------

/// Zeroed heap reads zero at every word
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let zeroed_heap_read_zero (addr: hp_addr)
  : Lemma (read_word empty_heap addr == 0UL)
  = let offset = U64.v addr in
    // empty_heap = Seq.create heap_size 0uy, so all bytes are 0
    FStar.Seq.Base.lemma_index_create heap_size 0uy offset;
    FStar.Seq.Base.lemma_index_create heap_size 0uy (offset + 1);
    FStar.Seq.Base.lemma_index_create heap_size 0uy (offset + 2);
    FStar.Seq.Base.lemma_index_create heap_size 0uy (offset + 3);
    FStar.Seq.Base.lemma_index_create heap_size 0uy (offset + 4);
    FStar.Seq.Base.lemma_index_create heap_size 0uy (offset + 5);
    FStar.Seq.Base.lemma_index_create heap_size 0uy (offset + 6);
    FStar.Seq.Base.lemma_index_create heap_size 0uy (offset + 7);
    // Combine_bytes of all zeros is 0
    assert_norm (combine_bytes 0uy 0uy 0uy 0uy 0uy 0uy 0uy 0uy == 0UL)
#pop-options

/// A zero header means wosize=0, which excludes the object from being an object
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let zeroed_heap_objects_empty ()
  : Lemma (Seq.length (objects zero_addr empty_heap) == 0)
  = // Proof by extensional equality with Seq.empty
    // Step 1: Show that any object in the sequence has wosize 0 (contradiction)
    let objs = objects zero_addr empty_heap in
    let aux (i:nat)
      : Lemma (requires i < Seq.length objs)
              (ensures False)
      = if i < Seq.length objs then begin
          let obj = Seq.index objs i in
          // By definition of objects, obj has wosize > 0
          assert (U64.v (wosize_of_object obj empty_heap) > 0);
          // But header is 0 in zeroed heap
          let hdr_addr = hd_address obj in
          zeroed_heap_read_zero hdr_addr;
          let hdr = read_word empty_heap hdr_addr in
          assert (hdr == 0UL);
          // wosize = hdr >> 10 = 0, contradiction
          assert (U64.v (wosize_of_object obj empty_heap) == 0)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    // Since accessing any element leads to contradiction, length must be 0
    if Seq.length objs > 0 then aux 0
#pop-options

/// ---------------------------------------------------------------------------
/// Empty heap is well-formed
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let empty_heap_well_formed ()
  : Lemma (well_formed_heap empty_heap)
  = zeroed_heap_objects_empty ();
    assert (Seq.length (objects zero_addr empty_heap) == 0);
    // well_formed_heap requires forall obj in objects. properties hold
    // With empty object list, all universally quantified properties are vacuous
    let aux (obj: obj_addr)
      : Lemma (ensures
        (Seq.mem obj (objects zero_addr empty_heap) ==>
         (let wz = wosize_of_object obj empty_heap in
          U64.v obj + U64.v wz * 8 <= heap_size /\
          (U64.v obj + U64.v wz * 8) % 8 == 0)))
      = if Seq.mem obj (objects zero_addr empty_heap) then begin
          zeroed_heap_objects_empty ();
          assert False
        end
    in
    FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// Free-list properties for fp=0
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let empty_fl_valid ()
  : Lemma (AllocLemmas.fl_valid empty_heap 0UL (heap_size / U64.v mword))
  = zeroed_heap_objects_empty ();
    // fl_valid for fp=0 is vacuous: no chain to validate
    ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_fl_chain_terminates ()
  : Lemma (AllocLemmas.fl_chain_terminates empty_heap 0UL (heap_size / U64.v mword))
  = ()
#pop-options

#push-options "--z3rlimit 10"
let empty_fp_pointer_or_zero ()
  : Lemma (FreeListShape.fp_pointer_or_zero 0UL)
  = reveal_opaque (`%FreeListShape.fp_pointer_or_zero)
      (FreeListShape.fp_pointer_or_zero 0UL)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_blue_link_fields_valid ()
  : Lemma (FreeListShape.blue_link_fields_valid empty_heap)
  = zeroed_heap_objects_empty ();
    let aux (obj: obj_addr)
      : Lemma (ensures
        (Seq.mem obj (objects zero_addr empty_heap) /\
         is_blue obj empty_heap ==>
         U64.v obj + 8 <= heap_size /\
         (is_blue_link_field obj empty_heap 0 \/
          is_blue_link_field obj empty_heap 1)))
      = zeroed_heap_objects_empty ()
    in
    reveal_opaque (`%FreeListShape.blue_link_fields_valid)
      (FreeListShape.blue_link_fields_valid empty_heap);
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_heap_objects_dense ()
  : Lemma (heap_objects_dense empty_heap)
  = zeroed_heap_objects_empty ();
    let aux (obj: obj_addr)
      : Lemma (ensures
        (Seq.mem obj (objects zero_addr empty_heap) ==>
         ~(is_blue obj empty_heap)))
      = zeroed_heap_objects_empty ()
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_chain_objects_blue ()
  : Lemma (chain_objects_blue empty_heap 0UL)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_fp_valid ()
  : Lemma (SweepInv.fp_valid 0UL empty_heap)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_fp_in_heap ()
  : Lemma (Sweep.fp_in_heap 0UL empty_heap)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_no_black_objects ()
  : Lemma (Mark.no_black_objects empty_heap)
  = zeroed_heap_objects_empty ();
    let aux (obj: obj_addr)
      : Lemma (ensures
        (Seq.mem obj (objects zero_addr empty_heap) ==>
         ~(is_black obj empty_heap)))
      = zeroed_heap_objects_empty ()
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let empty_no_pointer_to_blue ()
  : Lemma (Mark.no_pointer_to_blue empty_heap)
  = zeroed_heap_objects_empty ();
    let aux (obj: obj_addr) (dst: obj_addr)
      : Lemma (ensures
        (Seq.mem obj (objects zero_addr empty_heap) /\
         points_to empty_heap obj dst ==>
         ~(is_blue dst empty_heap)))
      = zeroed_heap_objects_empty ()
    in
    FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_no_scan_invariant ()
  : Lemma (no_scan_invariant empty_heap)
  = zeroed_heap_objects_empty ();
    let aux (obj: obj_addr) (j: nat)
      : Lemma (ensures
        (Seq.mem obj (objects zero_addr empty_heap) /\
         tag_of_object obj empty_heap >= 251 /\
         j < U64.v (wosize_of_object obj empty_heap) ==>
         ~(is_pointer_field_nat obj empty_heap j)))
      = zeroed_heap_objects_empty ()
    in
    FStar.Classical.forall_intro_2 aux
#pop-options

/// ---------------------------------------------------------------------------
/// major_heap_shape for empty heap — IMPOSSIBLE
/// ---------------------------------------------------------------------------

/// NOTE: major_heap_shape requires Seq.length (objects zero_addr major) > 0
/// A truly empty (all-zero) heap has NO objects, so it CANNOT satisfy
/// major_heap_shape. This is a fundamental limitation: the GC requires
/// at least one object (typically the free-list sentinel) to function.
///
/// To create a valid initial heap, use heap_init from GC.Impl.Allocator,
/// which creates a heap with one large free block.
///
/// Therefore, we DO NOT provide empty_major_heap_shape. Instead, clients
/// should use the allocator's initialization routine.

(* REMOVED: impossible to prove
let empty_major_heap_shape ()
  : Lemma (major_heap_shape empty_heap 0UL)
  = ...
*)

/// ---------------------------------------------------------------------------
/// minor_heap_shape for empty heap
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let empty_minor_heap_shape ()
  : Lemma (minor_heap_shape empty_minor)
  = // minor_wf: bump within bounds and aligned
    assert (U64.v empty_minor.bump == 0);
    assert (0 <= minor_heap_size);
    assert (0 % 8 == 0);
    // minor_guards_complete: vacuous (no objects with wosize > 0 in zeroed heap)
    let guards_aux (addr: U64.t)
      : Lemma (ensures
        (U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
         U64.v addr % 8 == 0 /\
         minor_wosize empty_minor addr > 0 /\
         U64.v addr + minor_wosize empty_minor addr * 8 <= minor_heap_size /\
         minor_tag empty_minor addr <> 249 ==>
         Seq.mem addr (minor_objects empty_minor)))
      = // All headers are 0 in zeroed data, so wosize is always 0
        // Therefore the premise is always false
        ()
    in
    reveal_opaque (`%minor_guards_complete) (minor_guards_complete empty_minor);
    FStar.Classical.forall_intro (FStar.Classical.move_requires guards_aux);
    // minor_infix_wf: vacuous (no infix)
    let infix_aux (addr: U64.t)
      : Lemma (ensures
        (is_infix_in_minor empty_minor addr ==>
         (let wz = minor_wosize empty_minor addr in
          let parent = infix_parent empty_minor addr in
          wz > 0 /\
          wz * 8 <= U64.v addr - 8 /\
          U64.v parent >= 8 /\
          U64.v parent % 8 == 0 /\
          Seq.mem parent (minor_objects empty_minor) /\
          U64.v addr - U64.v parent < minor_wosize empty_minor parent * 8)))
      = ()
    in
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf empty_minor);
    FStar.Classical.forall_intro infix_aux;
    // minor_no_scan_invariant: vacuous (no objects)
    let noscan_aux (obj: U64.t) (j: nat)
      : Lemma (ensures
        (Seq.mem obj (minor_objects empty_minor) /\
         minor_tag empty_minor obj >= 251 /\
         j < minor_wosize empty_minor obj ==>
         ~(is_pointer_field (minor_read_field empty_minor obj j)) /\
         ~(is_minor_pointer (to_minor_offset (minor_read_field empty_minor obj j)))))
      = ()
    in
    FStar.Classical.forall_intro_2 noscan_aux;
    // minor_fields_no_infix_targets: vacuous (no objects)
    let noinfix_aux (obj: U64.t) (j: nat)
      : Lemma (ensures
        (Seq.mem obj (minor_objects empty_minor) /\
         j < minor_wosize empty_minor obj /\
         is_minor_pointer (to_minor_offset (minor_read_field empty_minor obj j)) ==>
         ~(is_infix_in_minor empty_minor
           (to_minor_offset (minor_read_field empty_minor obj j)))))
      = ()
    in
    reveal_opaque (`%minor_fields_no_infix_targets)
      (minor_fields_no_infix_targets empty_minor);
    FStar.Classical.forall_intro_2 noinfix_aux;
    // Combine
    reveal_opaque (`%minor_heap_shape) (minor_heap_shape empty_minor)
#pop-options

/// ---------------------------------------------------------------------------
/// Cross-heap invariants for empty heaps
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let empty_minor_major_fields_no_blue ()
  : Lemma (minor_major_fields_no_blue empty_minor empty_heap)
  = let aux (obj: U64.t) (j: nat)
      : Lemma (ensures
        (Seq.mem obj (minor_objects empty_minor) /\
         j < minor_wosize empty_minor obj /\
         is_pointer_field (minor_read_field empty_minor obj j) ==>
         Seq.mem ((minor_read_field empty_minor obj j) <: obj_addr)
                 (objects zero_addr empty_heap) /\
         ~(is_blue ((minor_read_field empty_minor obj j) <: obj_addr) empty_heap)))
      = ()
    in
    reveal_opaque (`%minor_major_fields_no_blue)
      (minor_major_fields_no_blue empty_minor empty_heap);
    FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let empty_major_minor_fields_no_infix ()
  : Lemma (major_minor_fields_no_infix_targets empty_minor empty_heap)
  = let aux (obj: obj_addr) (j: nat)
      : Lemma (ensures
        (Seq.mem obj (objects zero_addr empty_heap) /\
         ~(is_blue obj empty_heap) /\
         ~(is_no_scan obj empty_heap) /\
         j < U64.v (wosize_of_object obj empty_heap) /\
         U64.v obj + j * 8 + 8 <= heap_size /\
         (U64.v obj + j * 8) % 8 == 0 ==>
         (let v = to_minor_offset
            (read_word empty_heap (U64.uint_to_t (U64.v obj + j * 8))) in
          is_minor_pointer v ==> ~(is_infix_in_minor empty_minor v))))
      = zeroed_heap_objects_empty ()
    in
    reveal_opaque (`%major_minor_fields_no_infix_targets)
      (major_minor_fields_no_infix_targets empty_minor empty_heap);
    FStar.Classical.forall_intro_2 aux
#pop-options

/// ---------------------------------------------------------------------------
/// collection_heap_shape for empty heap — IMPOSSIBLE
/// ---------------------------------------------------------------------------

/// NOTE: Cannot provide collection_heap_shape for all-zero heap because
/// major_heap_shape requires at least one object. See note above.
///
/// For testing purposes, use a heap initialized by heap_init instead.

(* REMOVED: blocked on major_heap_shape impossibility
let empty_collection_heap_shape ()
  : Lemma (collection_heap_shape empty_minor empty_heap 0UL)
  = ...
*)

/// ---------------------------------------------------------------------------
/// Ref table properties for empty slots
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_ref_table_sound ()
  : Lemma (ref_table_sound empty_heap Seq.empty 0)
  = let aux (i: nat)
      : Lemma (ensures
        (i < 0 ==>
         (let slot_addr = Seq.index Seq.empty i in
          U64.v slot_addr < heap_size /\
          U64.v slot_addr % 8 == 0 /\
          (let field_val = to_minor_offset (read_word empty_heap slot_addr) in
           is_minor_pointer field_val ==>
           (exists (src: obj_addr) (j: nat).
             Seq.mem src (objects zero_addr empty_heap) /\
             ~(is_blue src empty_heap) /\
             ~(is_no_scan src empty_heap) /\
             j > 0 /\
             j < U64.v (wosize_of_object src empty_heap) /\
             U64.v src + j * 8 + 8 <= heap_size /\
             (U64.v src + j * 8) % 8 == 0 /\
             U64.v slot_addr == U64.v src + j * 8)))))
      = ()
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_ref_table_covers ()
  : Lemma (ref_table_covers_minor_ptrs empty_heap Seq.empty 0)
  = let aux (src: obj_addr) (j: nat)
      : Lemma (ensures
        (Seq.mem src (objects zero_addr empty_heap) /\
         ~(is_blue src empty_heap) /\
         ~(is_no_scan src empty_heap) /\
         j > 0 /\
         j < U64.v (wosize_of_object src empty_heap) /\
         U64.v src + j * 8 + 8 <= heap_size /\
         (U64.v src + j * 8) % 8 == 0 /\
         (let field_val = to_minor_offset
            (read_word empty_heap (U64.uint_to_t (U64.v src + j * 8))) in
          is_minor_pointer field_val) ==>
         (exists (i: nat). i < 0 /\
           U64.v (Seq.index Seq.empty i) == U64.v src + j * 8)))
      = zeroed_heap_objects_empty ()
    in
    FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let empty_slots_pairwise_distinct ()
  : Lemma (slots_pairwise_distinct Seq.empty 0)
  = let aux (i j: nat)
      : Lemma (ensures
        (i < 0 /\ j < 0 /\ i <> j ==>
         U64.v (Seq.index Seq.empty i) <> U64.v (Seq.index Seq.empty j)))
      = ()
    in
    FStar.Classical.forall_intro_2 aux
#pop-options

/// ---------------------------------------------------------------------------
/// Root and remembered set properties for empty
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_remembered_targets ()
  : Lemma (remembered_targets_in_roots empty_heap Seq.empty Seq.empty 0)
  = let aux (r: U64.t)
      : Lemma (ensures
        (Seq.mem r (remembered_slot_targets empty_heap Seq.empty 0) ==>
         Seq.mem r Seq.empty))
      = ()
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_major_field_zero_no_minor ()
  : Lemma (major_field_zero_no_minor empty_minor empty_heap)
  = let aux (src: obj_addr)
      : Lemma (ensures
        (Seq.mem src (objects zero_addr empty_heap) /\
         ~(is_no_scan src empty_heap) /\
         U64.v src + 8 <= heap_size ==>
         (let v = to_minor_offset (read_word empty_heap (U64.uint_to_t (U64.v src))) in
          ~(is_minor_pointer v /\ Seq.mem v (minor_objects empty_minor)))))
      = zeroed_heap_objects_empty ()
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_roots_valid_nonblue ()
  : Lemma (roots_valid_nonblue Seq.empty empty_heap)
  = let aux (r: U64.t)
      : Lemma (ensures
        (Seq.mem r Seq.empty /\ ~(is_minor_pointer r) /\
         is_val_addr r /\ Seq.mem (r <: obj_addr) (objects zero_addr empty_heap) ==>
         ~(is_blue (r <: obj_addr) empty_heap)))
      = ()
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let empty_roots_valid_for_minor ()
  : Lemma (roots_valid_for_minor_collection empty_minor empty_heap Seq.empty)
  = let aux (r: U64.t)
      : Lemma (ensures
        (Seq.mem r Seq.empty ==>
         ((is_minor_pointer r ==>
           Seq.mem r (minor_objects empty_minor) /\
           minor_wosize empty_minor r > 0) /\
          (~(is_minor_pointer r) ==>
           is_val_addr r /\
           Seq.mem (r <: obj_addr) (objects zero_addr empty_heap) /\
           ~(is_blue (r <: obj_addr) empty_heap)))))
      = ()
    in
    FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// Forwarding array properties
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let empty_fwd_array ()
  : (farr: Seq.seq U64.t{Seq.length farr == fwd_array_size /\
                          (forall (i: nat). i < Seq.length farr ==>
                            Seq.index farr i == 0UL)})
  = Seq.create fwd_array_size 0UL
#pop-options
