module GC.SPOT.InfixMajor

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module SpecHeap = GC.Spec.Heap
module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module Header = GC.Lib.Header
module GenInv = GC.Gen.HeapInvariant

/// A concrete major heap that contains a genuine OCaml *interior pointer*.
///
/// See the implementation for the ten-word picture.  In brief: a one-field
/// object `Q` whose single field points at `H`, an infix object living inside
/// the body of a five-word closure `P`, plus one blue free block `F` covering
/// the rest of the heap.
///
/// `H` is never enumerated by `objects` -- its header sits inside P's body --
/// so this heap is precisely the shape that the old `no_infix_field_targets`
/// conjunct of `major_heap_shape` ruled out.  The audit here is that the heap
/// nevertheless satisfies the *current* invariant, so `gen_gc` accepts it.
val spot_infix_room : prop

val spot_q_header : (r:unit{spot_infix_room}) -> Tot hp_addr
val spot_q : (r:unit{spot_infix_room}) -> Tot obj_addr
val spot_q_field0 : (r:unit{spot_infix_room}) -> Tot hp_addr
val spot_p_header : (r:unit{spot_infix_room}) -> Tot hp_addr
val spot_p : (r:unit{spot_infix_room}) -> Tot obj_addr
val spot_infix_header : (r:unit{spot_infix_room}) -> Tot hp_addr
val spot_h : (r:unit{spot_infix_room}) -> Tot obj_addr
val spot_free_header : (r:unit{spot_infix_room}) -> Tot hp_addr
val spot_free_obj : (r:unit{spot_infix_room}) -> Tot obj_addr
val spot_free_wosize : (r:unit{spot_infix_room}) -> Tot (n:nat{n < pow2 54})

val q_header_word : U64.t
val p_header_word : U64.t
val infix_header_word : U64.t
val free_header_word : (r:unit{spot_infix_room}) -> Tot U64.t

val spot_infix_heap : (r:unit{spot_infix_room}) -> Tot heap
val spot_infix_fp : (r:unit{spot_infix_room}) -> Tot U64.t

val spot_infix_layout_facts
  : r:unit{spot_infix_room} ->
    Lemma (ensures
      U64.v (spot_q_header r) == U64.v zero_addr /\
      U64.v (spot_q r) == U64.v zero_addr + 8 /\
      U64.v (spot_q_field0 r) == U64.v zero_addr + 8 /\
      U64.v (spot_p_header r) == U64.v zero_addr + 16 /\
      U64.v (spot_p r) == U64.v zero_addr + 24 /\
      U64.v (spot_infix_header r) == U64.v zero_addr + 40 /\
      U64.v (spot_h r) == U64.v zero_addr + 48 /\
      U64.v (spot_free_header r) == U64.v zero_addr + 64 /\
      U64.v (spot_free_obj r) == U64.v zero_addr + 72 /\
      U64.v (spot_infix_fp r) == U64.v (spot_free_obj r) /\
      spot_free_wosize r >= 1 /\
      U64.v (spot_free_header r) + (spot_free_wosize r + 1) * 8 == heap_size)

val spot_infix_read
  : r:unit{spot_infix_room} -> addr:hp_addr ->
    Lemma (ensures
      SpecHeap.read_word (spot_infix_heap r) addr ==
        (if addr = spot_q_header r then q_header_word
         else if addr = spot_q_field0 r then (spot_h r <: U64.t)
         else if addr = spot_p_header r then p_header_word
         else if addr = spot_infix_header r then infix_header_word
         else if addr = spot_free_header r then free_header_word r
         else 0UL))

/// The three constant header words, decoded.
val header_words_decode
  : r:unit{spot_infix_room} ->
    Lemma (ensures
      SpecObj.getWosize q_header_word == 1UL /\
      SpecObj.getTag q_header_word == 0UL /\
      SpecObj.getColor q_header_word == Header.White /\
      SpecObj.getWosize p_header_word == 5UL /\
      SpecObj.getTag p_header_word == SpecObj.closure_tag /\
      SpecObj.getColor p_header_word == Header.White /\
      SpecObj.getWosize infix_header_word == 3UL /\
      SpecObj.getTag infix_header_word == SpecObj.infix_tag /\
      SpecObj.getColor infix_header_word == Header.White /\
      SpecObj.getWosize (free_header_word r) ==
        U64.uint_to_t (spot_free_wosize r) /\
      SpecObj.getTag (free_header_word r) == 0UL /\
      SpecObj.getColor (free_header_word r) == Header.Blue)

val spot_infix_q_reads
  : r:unit{spot_infix_room} ->
    Lemma (ensures (
      let g = spot_infix_heap r in
      SpecObj.wosize_of_object (spot_q r) g == 1UL /\
      SpecObj.tag_of_object (spot_q r) g == 0UL /\
      SpecHeap.read_word g (spot_q_field0 r) == (spot_h r <: U64.t) /\
      ~(SpecObj.is_blue (spot_q r) g) /\
      ~(SpecObj.is_gray (spot_q r) g) /\
      ~(SpecObj.is_black (spot_q r) g) /\
      ~(SpecObj.is_infix (spot_q r) g) /\
      ~(SpecObj.is_closure (spot_q r) g) /\
      ~(SpecObj.is_no_scan (spot_q r) g)))

val spot_infix_p_reads
  : r:unit{spot_infix_room} ->
    Lemma (ensures (
      let g = spot_infix_heap r in
      SpecObj.wosize_of_object (spot_p r) g == 5UL /\
      SpecObj.tag_of_object (spot_p r) g == SpecObj.closure_tag /\
      SpecObj.is_closure (spot_p r) g /\
      ~(SpecObj.is_blue (spot_p r) g) /\
      ~(SpecObj.is_gray (spot_p r) g) /\
      ~(SpecObj.is_black (spot_p r) g) /\
      ~(SpecObj.is_infix (spot_p r) g) /\
      ~(SpecObj.is_no_scan (spot_p r) g)))

/// `H` really is an infix object: its header carries `infix_tag`.
val spot_infix_h_reads
  : r:unit{spot_infix_room} ->
    Lemma (ensures (
      let g = spot_infix_heap r in
      SpecObj.wosize_of_object (spot_h r) g == 3UL /\
      SpecObj.tag_of_object (spot_h r) g == SpecObj.infix_tag /\
      SpecObj.is_infix (spot_h r) g /\
      ~(SpecObj.is_blue (spot_h r) g) /\
      ~(SpecObj.is_gray (spot_h r) g) /\
      ~(SpecObj.is_black (spot_h r) g) /\
      ~(SpecObj.is_closure (spot_h r) g) /\
      ~(SpecObj.is_no_scan (spot_h r) g)))

val spot_infix_free_reads
  : r:unit{spot_infix_room} ->
    Lemma (ensures (
      let g = spot_infix_heap r in
      SpecObj.wosize_of_object (spot_free_obj r) g ==
        U64.uint_to_t (spot_free_wosize r) /\
      SpecObj.tag_of_object (spot_free_obj r) g == 0UL /\
      SpecHeap.read_word g (spot_free_obj r) == 0UL /\
      SpecObj.is_blue (spot_free_obj r) g /\
      ~(SpecObj.is_gray (spot_free_obj r) g) /\
      ~(SpecObj.is_black (spot_free_obj r) g) /\
      ~(SpecObj.is_infix (spot_free_obj r) g) /\
      ~(SpecObj.is_no_scan (spot_free_obj r) g)))

/// Q's field 0 holds a pointer, and that pointer is an infix address.  This is
/// the whole point of the scenario.
val spot_infix_h_is_interior
  : r:unit{spot_infix_room} ->
    Lemma (ensures (
      let g = spot_infix_heap r in
      SpecFields.is_pointer_field (SpecHeap.read_word g (spot_q_field0 r)) /\
      SpecObj.is_infix (spot_h r) g))

/// The object walk sees exactly three objects.  It steps *over* the infix
/// header, which lives inside P's body.
val spot_infix_objects
  : r:unit{spot_infix_room} ->
    Lemma (ensures
      SpecFields.objects zero_addr (spot_infix_heap r) ==
        Seq.cons (spot_q r)
          (Seq.cons (spot_p r) (Seq.cons (spot_free_obj r) Seq.empty)))

val spot_infix_mem
  : r:unit{spot_infix_room} ->
    Lemma (ensures
      Seq.mem (spot_q r) (SpecFields.objects zero_addr (spot_infix_heap r)) /\
      Seq.mem (spot_p r) (SpecFields.objects zero_addr (spot_infix_heap r)) /\
      Seq.mem (spot_free_obj r) (SpecFields.objects zero_addr (spot_infix_heap r)))

val spot_infix_object_cases
  : r:unit{spot_infix_room} -> obj:obj_addr ->
    Lemma (requires Seq.mem obj (SpecFields.objects zero_addr (spot_infix_heap r)))
          (ensures obj == spot_q r \/ obj == spot_p r \/ obj == spot_free_obj r)

/// The infix object is *not* enumerated, which is why part 4 holds and why the
/// raw formulation of part 2 would reject this heap.
val spot_infix_h_not_enumerated
  : r:unit{spot_infix_room} ->
    Lemma (ensures
      ~(Seq.mem (spot_h r) (SpecFields.objects zero_addr (spot_infix_heap r))))

val spot_infix_field_read
  : r:unit{spot_infix_room} -> src:obj_addr -> j:nat ->
    Lemma (requires
            Seq.mem src (SpecFields.objects zero_addr (spot_infix_heap r)) /\
            j < U64.v (SpecObj.wosize_of_object src (spot_infix_heap r)) /\
            U64.v src + j * 8 + 8 <= heap_size)
          (ensures (
            let g = spot_infix_heap r in
            let v = SpecHeap.read_word g (U64.uint_to_t (U64.v src + j * 8)) in
            if src = spot_q r then v == (spot_h r <: U64.t)
            else if src = spot_p r && j = 2 then v == infix_header_word
            else v == 0UL))

/// Q's field 0 is the only pointer-valued field in the heap.
val spot_infix_field_pointer_cases
  : r:unit{spot_infix_room} -> src:obj_addr -> j:nat ->
    Lemma (requires
            Seq.mem src (SpecFields.objects zero_addr (spot_infix_heap r)) /\
            j < U64.v (SpecObj.wosize_of_object src (spot_infix_heap r)) /\
            U64.v src + j * 8 + 8 <= heap_size)
          (ensures (
            let g = spot_infix_heap r in
            let v = SpecHeap.read_word g (U64.uint_to_t (U64.v src + j * 8)) in
            SpecFields.is_pointer_field v ==>
              (src == spot_q r /\ j == 0 /\ v == (spot_h r <: U64.t))))

/// The interior pointer resolves to the enclosing closure.
val spot_infix_h_resolves_to_p
  : r:unit{spot_infix_room} ->
    Lemma (ensures
      SpecObj.resolve_object (spot_h r) (spot_infix_heap r) == spot_p r)

val spot_infix_h_addr_wf
  : r:unit{spot_infix_room} ->
    Lemma (ensures
      SpecObj.infix_addr_wf (spot_infix_heap r)
        (SpecFields.objects zero_addr (spot_infix_heap r)) (spot_h r))

val spot_infix_well_formed_heap
  : r:unit{spot_infix_room} ->
    Lemma (ensures SpecFields.well_formed_heap (spot_infix_heap r))

/// The negative half of the audit.  Before the generational invariant was
/// relaxed, `major_heap_shape` carried `no_infix_field_targets`; this heap
/// refutes that clause, so it could not have been handed to `gen_gc` at all.
val spot_infix_violates_no_infix_field_targets
  : r:unit{spot_infix_room} ->
    Lemma (ensures ~(SpecFields.no_infix_field_targets (spot_infix_heap r)))

/// The positive half: the heap satisfies the invariant `gen_gc` demands.
val spot_infix_major_heap_shape
  : r:unit{spot_infix_room} ->
    Lemma (ensures
      GenInv.major_heap_shape (spot_infix_heap r) (spot_infix_fp r))
