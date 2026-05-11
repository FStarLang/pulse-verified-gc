(*
   Pulse GC - Write Barrier (Stage 2)

   Pulse implementation of `gen_modify`: writes a single 64-bit field
   of a major-heap object and conditionally appends a remembered-set
   entry when the new value is a minor-heap pointer (caller-supplied)
   and the holder's tag does not exclude intergenerational edges.

   The "is the new value in the minor heap?" decision is a CALLER
   concern (Stage 4's `GC.Impl.Gen.gen_modify`). This function takes
   the result as a plain `bool` parameter.
*)

module GC.Impl.WriteBarrier

#lang-pulse

open Pulse.Lib.Pervasives
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.RememberedSet
open GC.Spec.WriteBarrier

open GC.Impl.Heap
open GC.Impl.RememberedSet

module ImplObject = GC.Impl.Object
module SpecObject = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecHeap = GC.Spec.Heap

/// ---------------------------------------------------------------------------
/// Excluded-tag check (Pulse-callable)
/// ---------------------------------------------------------------------------

inline_for_extraction
let is_excluded_tag_impl (tag: U64.t) : (b:bool{b == is_excluded_tag tag}) =
  U64.eq tag 249UL || U64.eq tag 250UL ||
  U64.eq tag 254UL || U64.eq tag 255UL

/// ---------------------------------------------------------------------------
/// The write barrier
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
fn gen_modify
    (h: heap_t)
    (rs: rem_set)
    (holder: obj_addr)
    (idx: U64.t{U64.v idx < pow2 61 /\ field_addr_valid holder idx})
    (new_val: U64.t)
    (target_is_minor: bool)
  requires
    is_heap h 'g **
    is_rem_set rs 'rt **
    pure (
      // remembered set has capacity, in case we end up pushing
      Seq.length 'rt < rem_set_capacity rs
    )
  returns _: unit
  ensures
    exists* g' rt'. is_heap h g' ** is_rem_set rs rt' **
    pure (
      // Heap component: the field was written via the byte-level spec.
      g' == SpecHeap.write_word 'g (field_addr_of holder idx) new_val /\
      // Ref-table component: either unchanged or appended once.
      (let holder_tag = SpecObject.getTag (SpecHeap.read_word 'g (hd_address holder)) in
       if should_record target_is_minor holder_tag
       then rt' == add_ref 'rt ({ holder = holder; field_idx = idx })
       else rt' == 'rt)
    )
{
  // 1. Compute the field address. Bind to spec-side terms to bridge.
  let f_offset = SpecFields.field_offset idx;
  let f_raw = U64.add_mod holder f_offset;
  assert (pure (f_raw == SpecFields.field_address_raw holder idx));
  let f_addr : hp_addr = f_raw;

  // 2. Read the header to extract the holder's tag.
  let hd_addr : hp_addr = U64.sub holder mword;
  assert (pure (hd_addr == hd_address holder));
  let hdr = read_word h hd_addr;
  let holder_tag = ImplObject.getTag hdr;
  ImplObject.getTag_eq hdr;
  // Now: holder_tag == SpecObject.getTag (SpecHeap.read_word 'g (hd_address holder)).
  assert (pure (holder_tag == SpecObject.getTag (SpecHeap.read_word 'g (hd_address holder))));

  // 3. Write the new value into the field.
  write_word h f_addr new_val;

  // 4. Conditionally record the (holder, idx) entry.
  let excluded = is_excluded_tag_impl holder_tag;
  let record = target_is_minor && (not excluded);
  // record matches should_record on the same tag
  assert (pure (record == should_record target_is_minor holder_tag));
  if record {
    add_ref_impl rs holder idx
  } else {
    ()
  }
}
#pop-options
