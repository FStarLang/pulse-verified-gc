/// ---------------------------------------------------------------------------
/// GC.Gen.NoBlueUtil -- proofs
/// ---------------------------------------------------------------------------

module GC.Gen.NoBlueUtil

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module Mark = GC.Spec.Mark

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --split_queries always"
let field_pointer_points_to_nat
  (g: heap) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
              Seq.mem src (objects zero_addr g) /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures points_to g src dst)
  =
  wfh_part1_obj_bound g src;
  assert (well_formed_object g src);
  wosize_of_object_bound src g;
  let wz = wosize_of_object src g in
  FStar.Math.Lemmas.pow2_lt_compat 61 54;
  assert (j < pow2 61);
  let k : U64.t = U64.uint_to_t j in
  assert (U64.v k == j);
  assert (U64.v k < U64.v wz);
  assert (U64.v k < pow2 61);
  assert (U64.v k * U64.v mword < pow2 64);
  FStar.Math.Lemmas.modulo_lemma (U64.v k * U64.v mword) (pow2 64);
  assert (U64.v (U64.mul_mod k mword) == U64.v k * U64.v mword);
  assert (U64.v src + U64.v k * U64.v mword < heap_size);
  assert (U64.v src + U64.v k * U64.v mword < pow2 64);
  FStar.Math.Lemmas.modulo_lemma (U64.v src + U64.v k * U64.v mword) (pow2 64);
  let far = U64.add_mod src (U64.mul_mod k mword) in
  assert (U64.v far == U64.v src + j * U64.v mword);
  assert (U64.v far < heap_size);
  assert (U64.v far % U64.v mword == 0);
  assert (far == U64.uint_to_t (U64.v src + j * U64.v mword));
  field_read_implies_exists_pointing g src wz k dst
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let field_pointer_no_blue_from_no_pointer_to_blue
  (g: heap) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
              Mark.no_pointer_to_blue g /\
              Seq.mem src (objects zero_addr g) /\
              ~(is_blue src g) /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures ~(is_blue dst g))
  =
  field_pointer_points_to_nat g src dst j

let field_pointer_target_in_objects_nat
  (g: heap) (src dst: obj_addr) (j: nat)
  : Lemma
    (requires well_formed_heap g /\
              Seq.mem src (objects zero_addr g) /\
              j < U64.v (wosize_of_object src g) /\
              U64.v src + j * U64.v mword + U64.v mword <= heap_size /\
              (U64.v src + j * U64.v mword) % U64.v mword == 0 /\
              is_pointer_to
                (read_word g (U64.uint_to_t (U64.v src + j * U64.v mword)))
                dst)
    (ensures Seq.mem dst (objects zero_addr g))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  field_pointer_points_to_nat g src dst j;
  points_to_target_in_objects g src dst
#pop-options
