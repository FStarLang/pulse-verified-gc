module GC.Gen.PromoteUpdate.Positional

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas

val update_all_objects_positional_step
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major = false)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let major' = update_object_pointers major obj wz fwd 0 in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    well_formed_heap_part1 major' /\
                    heap_objects_dense major' /\
                    objects zero_addr major' == objects zero_addr major /\
                    (next_nat < heap_size ==>
                      update_all_objects_aux major' (objects (U64.uint_to_t next_nat) major') fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat >= heap_size ==>
                      major' == update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major') /\
                      Seq.length (objects (U64.uint_to_t next_nat) major') > 0)))

val update_all_objects_positional_step_blue
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    (next_nat < heap_size ==>
                      update_all_objects_aux major (objects (U64.uint_to_t next_nat) major) fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat >= heap_size ==>
                      major == update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major) /\
                      Seq.length (objects (U64.uint_to_t next_nat) major) > 0)))

val update_all_objects_positional_step_no_scan
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    (next_nat < heap_size ==>
                      update_all_objects_aux major (objects (U64.uint_to_t next_nat) major) fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat >= heap_size ==>
                      major == update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major) /\
                      Seq.length (objects (U64.uint_to_t next_nat) major) > 0)))

val update_all_objects_terminal_step
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major = false)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    (next_nat + 8 >= heap_size ==>
                      (let major' = update_object_pointers major obj wz fwd 0 in
                       major' == update_all_objects_aux major (objects pos major) fwd 0))))

val objects_initial_membership (g: heap)
  : Lemma (requires heap_size > 8 /\ well_formed_heap_part1 g /\
                    Seq.length (objects zero_addr g) > 0)
          (ensures Seq.mem (f_address 0UL) (objects zero_addr g))
