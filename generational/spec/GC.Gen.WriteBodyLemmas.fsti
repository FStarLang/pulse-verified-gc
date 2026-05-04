/// ---------------------------------------------------------------------------
/// GC.Gen.Promote.WriteBody — Write-body preservation lemmas
/// ---------------------------------------------------------------------------
///
/// This module contains the heavy proof obligations for showing that writing
/// within an object's body preserves heap structure: objects walk, free-list
/// validity, chain termination, and chain avoidance.
///
/// These proofs are isolated here to limit Z3 context pollution in the main
/// GC.Gen.Promote module.
///
/// NOTE: This module does NOT depend on GC.Gen.Promote to avoid a circular
/// dependency (Promote.fst imports WriteBody). The copy_fields_preserves_*
/// lemmas that build on these write_body lemmas remain in Promote.fst.

module GC.Gen.WriteBodyLemmas

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// copy_fields — core definition (owned by this module)
/// ---------------------------------------------------------------------------

/// Copy `n` fields (words) from minor heap at `src_obj + i*8` to major heap at `dst + i*8`
val copy_fields (minor: minor_state) (major: heap)
                (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : GTot heap

/// Base case: copy_fields with i >= n is identity
val copy_fields_base (minor: minor_state) (major: heap)
                     (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i >= n)
          (ensures copy_fields minor major src_obj dst_obj i n == major)
    [SMTPat (copy_fields minor major src_obj dst_obj i n)]

/// Step lemma: one recursive unfolding of copy_fields
val copy_fields_step (minor: minor_state) (major: heap)
                     (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i < n /\
                     U64.v dst_obj + i * 8 + 8 <= heap_size /\
                     (U64.v dst_obj + i * 8) % 8 == 0)
           (ensures copy_fields minor major src_obj dst_obj i n ==
                    copy_fields minor
                      (write_word major (U64.uint_to_t (U64.v dst_obj + i * 8))
                                       (minor_read_field minor src_obj i))
                      src_obj dst_obj (i + 1) n)
    [SMTPat (copy_fields minor major src_obj dst_obj i n)]

/// OOB lemma: when field offset is out of bounds, copy_fields returns major unchanged
val copy_fields_oob (minor: minor_state) (major: heap)
                    (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i < n /\
                     (U64.v dst_obj + i * 8 + 8 > heap_size \/
                      (U64.v dst_obj + i * 8) % 8 <> 0))
           (ensures copy_fields minor major src_obj dst_obj i n == major)

/// ---------------------------------------------------------------------------
/// not_in_fl_chain predicate
/// ---------------------------------------------------------------------------

/// Predicate: dst_obj is not reachable from fp via the free-list chain.
val not_in_fl_chain (g: heap) (fp: U64.t) (dst_obj: obj_addr) (fuel: nat)
  : Tot prop

/// Bridge: chain_avoids (bool) implies not_in_fl_chain (prop).
val chain_avoids_implies_not_in_fl_chain
  (g: heap) (fp: U64.t) (dst_obj: obj_addr) (fuel: nat)
  : Lemma (requires AllocLemmas.chain_avoids g fp dst_obj fuel = true)
          (ensures not_in_fl_chain g fp dst_obj fuel)

/// ---------------------------------------------------------------------------
/// write_body preservation lemmas
/// ---------------------------------------------------------------------------

/// Writing within an object body preserves the objects walk from zero_addr.
val write_body_preserves_objects
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires
      Seq.mem obj (objects zero_addr g) /\
      U64.v addr >= U64.v obj /\
      U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
      U64.v addr % 8 = 0)
    (ensures objects zero_addr (write_word g addr v) == objects zero_addr g)

/// Writing within dst_obj's body preserves fl_valid.
val write_body_preserves_fl_valid_aux
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel)
    (ensures AllocLemmas.fl_valid (write_word g addr v) fp fuel)

/// Writing within dst_obj's body preserves not_in_fl_chain.
val write_body_preserves_not_in_fl_chain
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel)
    (ensures not_in_fl_chain (write_word g addr v) fp dst_obj fuel)

/// Writing within dst_obj's body preserves fl_chain_terminates.
val write_body_preserves_fl_chain_terminates
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_chain_terminates g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel /\
      AllocLemmas.fl_valid g fp fuel)
    (ensures AllocLemmas.fl_chain_terminates (write_word g addr v) fp fuel)

/// Writing within dst_obj's body preserves chain_avoids for dst_obj itself.
val write_body_preserves_chain_avoids_self
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      AllocLemmas.chain_avoids g fp dst_obj fuel = true)
    (ensures AllocLemmas.chain_avoids (write_word g addr v) fp dst_obj fuel = true)

/// ---------------------------------------------------------------------------
/// copy_fields preserves heap structure
/// ---------------------------------------------------------------------------

/// copy_fields preserves the objects walk (membership unchanged).
val copy_fields_preserves_objects_aux
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n)
          (ensures
             objects zero_addr (copy_fields minor major src_obj dst_obj i n) ==
             objects zero_addr major)

/// copy_fields preserves fl_valid.
val copy_fields_preserves_fl_valid_aux
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             not_in_fl_chain major fp dst_obj fuel)
          (ensures
             AllocLemmas.fl_valid (copy_fields minor major src_obj dst_obj i n) fp fuel)

/// copy_fields preserves fl_chain_terminates.
val copy_fields_preserves_fl_chain_terminates
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             AllocLemmas.fl_chain_terminates major fp fuel /\
             not_in_fl_chain major fp dst_obj fuel)
          (ensures
             AllocLemmas.fl_chain_terminates (copy_fields minor major src_obj dst_obj i n) fp fuel)

/// copy_fields preserves chain_avoids for dst_obj itself.
val copy_fields_preserves_chain_avoids_self
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             AllocLemmas.chain_avoids major fp dst_obj fuel = true)
          (ensures
             AllocLemmas.chain_avoids (copy_fields minor major src_obj dst_obj i n) fp dst_obj fuel = true)

/// copy_fields does not modify reads at addresses outside its write range.
val copy_fields_preserves_other
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (a: hp_addr)
  : Lemma
    (requires
      U64.v dst_obj % 8 == 0 /\
      (n > i ==> U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size) /\
      (forall (k:nat). i <= k /\ k < n ==>
        (U64.v a + 8 <= U64.v dst_obj + k * 8 \/ U64.v dst_obj + k * 8 + 8 <= U64.v a)))
    (ensures
      read_word (copy_fields minor major src_obj dst_obj i n) a == read_word major a)

/// copy_fields preserves well_formed_heap_part1.
val copy_fields_preserves_wfh_part1
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             n > 0)
          (ensures
             well_formed_heap_part1 (copy_fields minor major src_obj dst_obj 0 n))
