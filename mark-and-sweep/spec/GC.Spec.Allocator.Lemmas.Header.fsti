(*
   GC.Spec.Allocator.Lemmas.Header — Foundation lemmas for allocator proofs.

   Section 1: make_header arithmetic
   Section 2: Header write preserves objects
   Section 3: efptu congruence/monotonicity
   Section 4: Header write field independence
*)
module GC.Spec.Allocator.Lemmas.Header

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64

/// Section 1: make_header arithmetic

val make_header_value : (wz: U64.t{U64.v wz < pow2 54}) ->
                        (c: U64.t{U64.v c < 4}) ->
                        (t: U64.t{U64.v t < 256}) ->
  Lemma (U64.v (make_header wz c t) == U64.v wz * 1024 + U64.v c * 256 + U64.v t)

val make_header_getWosize : (wz: U64.t{U64.v wz < pow2 54}) ->
                            (c: U64.t{U64.v c < 4}) ->
                            (t: U64.t{U64.v t < 256}) ->
  Lemma (getWosize (make_header wz c t) == wz)

val make_header_getTag : (wz: U64.t{U64.v wz < pow2 54}) ->
                         (c: U64.t{U64.v c < 4}) ->
                         (t: U64.t{U64.v t < 256}) ->
  Lemma (U64.v (getTag (make_header wz c t)) == U64.v t)

/// Section 2: Header write with same wosize preserves objects

val header_write_same_wosize_preserves_objects :
  (g: heap) -> (obj: obj_addr) -> (new_hdr: U64.t) ->
  Lemma (requires getWosize new_hdr == getWosize (read_word g (hd_address obj)))
        (ensures objects 0UL (write_word g (hd_address obj) new_hdr) == objects 0UL g)

/// Section 3: efptu congruence and monotonicity

val efptu_congruence :
  (g: heap) -> (g': heap) -> (src: obj_addr) ->
  (wz: U64.t{U64.v wz < pow2 54}) -> (dst: obj_addr) ->
  Lemma (requires (forall (k: nat{k < U64.v wz}).
                     let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
                     U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                     read_word g' fa == read_word g fa))
        (ensures exists_field_pointing_to_unchecked g' src wz dst ==
                 exists_field_pointing_to_unchecked g src wz dst)

val efptu_monotone :
  (g: heap) -> (src: obj_addr) ->
  (small_wz: U64.t{U64.v small_wz < pow2 54}) ->
  (big_wz: U64.t{U64.v big_wz < pow2 54}) ->
  (dst: obj_addr) ->
  Lemma (requires U64.v small_wz <= U64.v big_wz /\
                  well_formed_object g src /\
                  U64.v big_wz <= U64.v (wosize_of_object src g) /\
                  exists_field_pointing_to_unchecked g src small_wz dst)
        (ensures exists_field_pointing_to_unchecked g src big_wz dst)

/// Section 4: Header write field independence

val header_write_doesnt_change_own_fields :
  (g: heap) -> (obj: obj_addr) -> (new_hdr: U64.t) -> (k: nat) ->
  Lemma (requires k < U64.v (wosize_of_object obj g))
        (ensures (let fa = U64.add_mod obj (U64.mul_mod (U64.uint_to_t k) mword) in
                  let hd = hd_address obj in
                  U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                  read_word (write_word g hd new_hdr) fa == read_word g fa))

val header_write_doesnt_change_other_fields :
  (g: heap) -> (obj: obj_addr) -> (src: obj_addr) -> (new_hdr: U64.t) -> (k: nat) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects 0UL g) /\
                  Seq.mem src (objects 0UL g) /\
                  src <> obj /\
                  k < U64.v (wosize_of_object src g))
        (ensures (let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
                  let hd = hd_address obj in
                  U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                  read_word (write_word g hd new_hdr) fa == read_word g fa))
