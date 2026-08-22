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
        (ensures objects zero_addr (write_word g (hd_address obj) new_hdr) == objects zero_addr g)

/// Section 3: efptu congruence and monotonicity

/// Section 4: Header write field independence
