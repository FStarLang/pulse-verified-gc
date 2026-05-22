/// ---------------------------------------------------------------------------
/// GC.Gen.FreeListShape -- Free-list value-shape invariants
/// ---------------------------------------------------------------------------

module GC.Gen.FreeListShape

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
module Sweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas

let fp_pointer_or_zero (fp: U64.t) : prop =
  fp = 0UL \/ HeapGraph.is_pointer_field fp

[@@"opaque_to_smt"]
let blue_link_fields_valid (major: heap) : prop =
  forall (src: obj_addr).
    Seq.mem src (objects zero_addr major) /\
    is_blue src major /\
    U64.v (wosize_of_object src major) >= 1 /\
    U64.v (hd_address src) + 16 <= heap_size ==>
    (let v = read_word major src in
     v = 0UL \/ HeapGraph.is_pointer_field v)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let blue_link_fields_valid_elim (major: heap) (src: obj_addr)
  : Lemma (requires blue_link_fields_valid major /\
                    Seq.mem src (objects zero_addr major) /\
                    is_blue src major /\
                    U64.v (wosize_of_object src major) >= 1 /\
                    U64.v (hd_address src) + 16 <= heap_size)
          (ensures (let v = read_word major src in
                    v = 0UL \/ HeapGraph.is_pointer_field v))
  = reveal_opaque (`%blue_link_fields_valid) (blue_link_fields_valid major)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let blue_link_fields_valid_intro (major: heap)
  (proof: (src: obj_addr ->
    Lemma (requires Seq.mem src (objects zero_addr major) /\
                    is_blue src major /\
                    U64.v (wosize_of_object src major) >= 1 /\
                    U64.v (hd_address src) + 16 <= heap_size)
          (ensures (let v = read_word major src in
                    v = 0UL \/ HeapGraph.is_pointer_field v))))
  : Lemma (ensures blue_link_fields_valid major)
  =
    let aux (src: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr major) /\
                        is_blue src major /\
                        U64.v (wosize_of_object src major) >= 1 /\
                        U64.v (hd_address src) + 16 <= heap_size)
              (ensures (let v = read_word major src in
                        v = 0UL \/ HeapGraph.is_pointer_field v))
      = proof src
    in
    reveal_opaque (`%blue_link_fields_valid) (blue_link_fields_valid major);
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let fp_pointer_or_zero_implies_fp_in_heap (fp: U64.t) (g: heap)
  : Lemma (requires fp_pointer_or_zero fp /\ SweepInv.fp_valid fp g)
          (ensures Sweep.fp_in_heap fp g)
  = if fp = 0UL then ()
    else begin
      SweepInv.fp_valid_elim fp g;
      assert (HeapGraph.is_pointer_field fp);
      assert (U64.v fp >= U64.v mword /\
              U64.v fp < heap_size /\
              U64.v fp % U64.v mword == 0 /\
              Seq.mem (fp <: obj_addr) (objects zero_addr g))
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let fp_pointer_or_zero_fl_valid_implies_fp_valid
  (fp: U64.t) (g: heap) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    fp_pointer_or_zero fp /\
                    AllocLemmas.fl_valid g fp fuel)
          (ensures SweepInv.fp_valid fp g)
  =
    if is_pointer_field fp then begin
      if fp = 0UL then ()
      else begin
        assert (HeapGraph.is_pointer_field fp);
        assert (U64.v fp >= U64.v mword /\
                U64.v fp < heap_size /\
                U64.v fp % U64.v mword == 0);
        AllocLemmas.fl_valid_gives_mem g fp fuel;
        SweepInv.obj_in_objects_intro (fp <: obj_addr) g;
        SweepInv.fp_valid_from_obj fp g
      end
    end else
      SweepInv.fp_valid_not_pointer fp g
#pop-options
