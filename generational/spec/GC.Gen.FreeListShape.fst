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
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass

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

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let fp_pointer_or_zero_fl_valid_implies_fp_valid
  (fp: U64.t) (g: heap) (fuel: nat)
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

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let fls_pointer_or_zero_implies_fp_valid (fls: FLs.fl_state) (g: heap) =
  FLs.fls_valid_elim g fls;
  reveal_opaque (`%fls_pointer_or_zero) (fls_pointer_or_zero fls);
  reveal_opaque (`%fls_fp_valid) (fls_fp_valid fls g);
  reveal_opaque (`%fls_in_heap) (fls_in_heap fls g);
  let aux (i: nat{i < SC.n_lists})
    : Lemma (SweepInv.fp_valid (FLs.fls_head fls i) g /\
             Sweep.fp_in_heap (FLs.fls_head fls i) g)
    = fp_pointer_or_zero_fl_valid_implies_fp_valid (FLs.fls_head fls i) g heap_words;
      fp_pointer_or_zero_implies_fp_in_heap (FLs.fls_head fls i) g
  in
  FStar.Classical.forall_intro aux
#pop-options

let fls_pointer_or_zero_iff fls =
  reveal_opaque (`%fls_pointer_or_zero) (fls_pointer_or_zero fls)
