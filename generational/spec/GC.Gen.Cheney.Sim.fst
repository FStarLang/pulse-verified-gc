/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney.Sim — Implementation of simulation lemmas
/// ---------------------------------------------------------------------------

module GC.Gen.Cheney.Sim

open FStar.Seq
module U64 = FStar.UInt64
module SZ = FStar.SizeT

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Impl.UpdatePtrs

module CheneySpec = GC.Gen.Cheney
module AllocLemmas = GC.Spec.Allocator.Lemmas
module SimOne = GC.Gen.Cheney.SimOne

/// ---------------------------------------------------------------------------
/// Initial state
/// ---------------------------------------------------------------------------

let represents_fwd_initial (farr: seq U64.t)
  = ()

/// ---------------------------------------------------------------------------
/// Forwarding array update
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let represents_fwd_update
  (farr: seq U64.t) (fwd: forwarding_map)
  (addr: U64.t) (new_addr: U64.t)
  =
  let idx = U64.v addr / 8 in
  assert (idx < fwd_array_size);
  let farr' = Seq.upd farr idx new_addr in
  let fwd' = extend_forwarding fwd addr new_addr in
  // For each i < fwd_array_size, show farr'[i] == fwd'(i*8)
  let aux (i: nat{i < fwd_array_size})
    : Lemma (Seq.index farr' i == fwd' (U64.uint_to_t (i * 8)))
    = if i = idx then begin
        // farr'[idx] = new_addr
        // fwd'(idx*8) = fwd'(addr) = new_addr (since addr = idx*8)
        assert (U64.uint_to_t (i * 8) == addr);
        assert (Seq.index farr' i == new_addr);
        assert (fwd' addr == new_addr)
      end else begin
        // farr'[i] = farr[i] (unchanged)
        // fwd'(i*8) = fwd(i*8) (since i*8 != addr)
        assert (U64.uint_to_t (i * 8) <> addr);
        assert (Seq.index farr' i == Seq.index farr i);
        assert (fwd' (U64.uint_to_t (i * 8)) == fwd (U64.uint_to_t (i * 8)))
      end
  in
  FStar.Classical.forall_intro aux

let represents_fwd_read
  (farr: seq U64.t) (fwd: forwarding_map) (addr: U64.t)
  =
  let idx = U64.v addr / 8 in
  assert (idx < fwd_array_size);
  // represents_fwd: farr[idx] == fwd (uint_to_t (idx * 8))
  // idx * 8 == addr (since addr % 8 == 0)
  assert (U64.uint_to_t (idx * 8) == addr)

let queue_update_correspondence
  (q: seq U64.t) (cs_queue: seq U64.t) (bk: nat) (addr: U64.t)
  =
  let q2 = Seq.upd q bk addr in
  let cq2 = Seq.append cs_queue (Seq.create 1 addr) in
  Seq.lemma_len_append cs_queue (Seq.create 1 addr);
  let aux (j: nat{j < bk + 1})
    : Lemma (Seq.index q2 j == Seq.index cq2 j)
    = if j < bk then begin
        Seq.lemma_index_app1 cs_queue (Seq.create 1 addr) j;
        assert (Seq.index cq2 j == Seq.index cs_queue j);
        assert (Seq.index q2 j == Seq.index q j)
      end else begin
        Seq.lemma_index_app2 cs_queue (Seq.create 1 addr) j;
        assert (Seq.index cq2 j == Seq.index (Seq.create 1 addr) (j - bk));
        assert (j - bk == 0);
        assert (Seq.index (Seq.create 1 addr) 0 == addr);
        assert (Seq.index q2 j == addr)
      end
  in
  FStar.Classical.forall_intro aux

#pop-options

/// ---------------------------------------------------------------------------
/// Non-minor addresses
/// ---------------------------------------------------------------------------

let not_minor_if_guards_fail (minor: minor_state) (addr: U64.t)
  = FStar.Classical.move_requires (minor_objects_valid minor) addr

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let not_minor_if_wosize_bounds_fail (minor: minor_state) (addr: U64.t)
  =
  // Contrapositive of minor_object_passes_guards
  FStar.Classical.move_requires (minor_objects_body_bound minor) addr

let promote_object_zero_noop
  (minor_st: minor_state) (ms: heap) (addr: U64.t) (fp: U64.t) (wz: nat)
  =
  let alloc_out = (GC.Spec.Allocator.alloc_spec ms fp wz).obj_out in
  if alloc_out = 0UL then
    GC.Gen.Promote.promote_object_oom minor_st ms addr fp wz
  else begin
    GC.Gen.Promote.promote_object_success minor_st ms addr fp wz;
    assert false
  end

#pop-options
/// ---------------------------------------------------------------------------
/// Queue validity through forward_fields and forward_roots (induction)
/// Uses opaque queue_valid predicate to prevent quantifier nesting.
/// Delegates to SimOne which has the recursive proofs with equation lemmas.
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Queue bound through forward_roots and scan (uses BFS invariant)
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Bridge: minor_read ↔ minor_read_field
/// ---------------------------------------------------------------------------

let minor_read_eq_field (ms: minor_state) (obj: U64.t) (fi: nat)
  =
  // minor_read_word_t h addr = minor_read_word h addr when in bounds
  // minor_read_field ms obj fi = minor_read_word ms.data (uint_to_t (v obj + fi*8)) when in bounds
  // Both conditions hold by our precondition
  let byte_offset = U64.v obj + fi * 8 in
  assert (byte_offset + 8 <= minor_heap_size);
  assert (byte_offset % 8 == 0)

/// ---------------------------------------------------------------------------
/// BFS invariant: strict room before enqueueing
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let cheney_bfs_inv_strict_room
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  =
  // From BFS invariant: |queue| + count_unforwarded <= |minor_objects|
  // addr is unforwarded (fwd addr = 0) and in minor_objects
  // So count_unforwarded >= 1 (addr contributes 1 to the count)
  // Therefore |queue| <= |minor_objects| - 1 < |minor_objects| <= queue_size
  SimOne.cheney_bfs_inv_bound minor cs;
  // We need strict inequality: the BFS inv has |queue| + unforwarded <= |minor_objects|
  // and unforwarded >= 1 (since addr is unforwarded), so |queue| < |minor_objects| <= queue_size
  SimOne.cheney_bfs_inv_strict_room minor cs addr
#pop-options

/// Trivial from minor_guards_complete: just instantiate the universal quantifier.
let minor_guards_sufficient (ms: minor_state) (addr: U64.t)
  = reveal_opaque (`%minor_guards_complete) (minor_guards_complete ms)
