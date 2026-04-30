(*
   Pulse GC (Generational) - Top-Level Entry Point Implementation

   Routes allocations by size and implements minor collection
   (copy minor objects to major heap, then reset minor).
*)

module GC.Gen.Impl

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl.Promote
open GC.Impl.Heap
module SpecFields = GC.Spec.Fields
module Alloc = GC.Impl.Allocator

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

/// Allocate: try minor first (if small enough), fall back to major.
#push-options "--z3rlimit 80"
fn gen_alloc (gh: gen_heap_t) (wosize: U64.t) (tag: U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (U64.v wosize > 0 /\ U64.v tag < 256 /\
                 SpecFields.well_formed_heap 's)
  returns obj: U64.t
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2
{
  unfold is_gen_heap;
  if U64.lte wosize max_young_wosize_u64 {
    // Small object → try minor heap
    let obj = minor_alloc gh.minor wosize tag;
    if U64.eq obj 0UL {
      // Minor full — allocate directly from major
      let fp = R.op_Bang gh.fp_ref;
      let res = Alloc.allocate gh.major fp wosize;
      R.op_Colon_Equals gh.fp_ref (fst res);
      fold (is_gen_heap gh _ _ _ _);
      snd res
    } else {
      fold (is_gen_heap gh _ _ _ _);
      obj
    }
  } else {
    // Large object → major heap directly
    let fp = R.op_Bang gh.fp_ref;
    let res = Alloc.allocate gh.major fp wosize;
    R.op_Colon_Equals gh.fp_ref (fst res);
    fold (is_gen_heap gh _ _ _ _);
    snd res
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Minor Collection
/// ---------------------------------------------------------------------------

/// Promote all minor objects then reset.
/// Walks the minor heap linearly, promoting each object found.
module AllocLemmas = GC.Spec.Allocator.Lemmas

#push-options "--z3rlimit 200"
fn minor_collect (gh: gen_heap_t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pure (SpecFields.well_formed_heap_part1 's /\
                 AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword))
  ensures exists* d2 b2 s2 fp2. is_gen_heap gh d2 b2 s2 fp2 **
          pure (U64.v b2 == 0)
{
  unfold is_gen_heap;
  // Read bump pointer — need to unfold is_minor temporarily
  unfold is_minor gh.minor 'd 'b;
  let bump = R.op_Bang gh.minor.bump_ref;
  fold (is_minor gh.minor 'd bump);
  let mut pos = 0UL;
  while (U64.lt !pos bump)
    invariant exists* md_i mb_i ms_i fp_i p_i.
      is_minor gh.minor md_i mb_i **
      is_heap gh.major ms_i **
      R.pts_to gh.fp_ref fp_i **
      R.pts_to pos p_i **
      pure (U64.v p_i <= U64.v bump /\
            U64.v p_i % 8 == 0 /\
            U64.v bump <= minor_heap_size /\
            U64.v bump % 8 == 0 /\
            md_i == 'd /\ mb_i == bump /\
            SpecFields.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i (heap_size / U64.v mword) /\
            AllocLemmas.fl_chain_terminates ms_i fp_i (heap_size / U64.v mword))
  {
    let p = !pos;
    // Read header at current position
    if U64.gte (U64.add p 8UL) bump {
      // Can't read past bump pointer
      pos := bump
    } else {
      let hdr = minor_read gh.minor p;
      let wosize = U64.shift_right hdr 10ul;
      if U64.eq wosize 0UL {
        // Skip empty/malformed — advance by 1 word
        pos := U64.add p 8UL
      } else {
        let obj_addr = U64.add p 8UL;
        // Guard against impossibly large wosize (header corruption)
        if U64.gte wosize minor_heap_size_u64 {
          pos := bump
        } else {
          // Check object fits within bump region
          let total_words = U64.add wosize 1UL;
          let total_bytes = U64.mul total_words 8UL;
          if U64.gt (U64.add p total_bytes) bump {
            // Object extends past bump — malformed
            pos := bump
          } else {
            // Promote this object
            assert (pure (U64.v obj_addr == U64.v p + 8));
            assert (pure (U64.v obj_addr >= 8));
            assert (pure (U64.v obj_addr < minor_heap_size));
            assert (pure (U64.v obj_addr % 8 == 0));
            // Connect wosize to minor_wosize:
            // hdr == minor_read_word_t 'd p
            // wosize == shift_right hdr 10
            // minor_wosize {data='d; bump=bump} obj_addr == shift_right (minor_read_word 'd p) 10
            // With p < bump <= minor_heap_size and p%8==0:
            //   minor_read_word_t 'd p == minor_read_word 'd p
            // So wosize == minor_wosize ... obj_addr
            assert (pure (U64.v obj_addr + U64.v wosize * 8 <= minor_heap_size));
            assert (pure (U64.v wosize == minor_wosize {data='d; bump=bump} obj_addr));
            let _new = promote_one gh.minor gh.major gh.fp_ref obj_addr;
            pos := U64.add p total_bytes
          }
        }
      }
    }
  };
  // Reset minor heap
  minor_heap_reset gh.minor;
  fold (is_gen_heap gh _ 0UL _ _)
}
#pop-options
