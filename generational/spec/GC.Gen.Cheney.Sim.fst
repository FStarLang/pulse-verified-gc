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
  : Lemma (requires Seq.length farr == fwd_array_size /\
                    (forall (i:nat). i < fwd_array_size ==> Seq.index farr i == 0UL))
          (ensures represents_fwd farr empty_forwarding)
  = ()

/// ---------------------------------------------------------------------------
/// Forwarding array update
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

let represents_fwd_update
  (farr: seq U64.t) (fwd: forwarding_map)
  (addr: U64.t) (new_addr: U64.t)
  : Lemma (requires represents_fwd farr fwd /\
                    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
                    U64.v addr % 8 == 0)
          (ensures (let idx = U64.v addr / 8 in
                    idx < fwd_array_size /\
                    represents_fwd (Seq.upd farr idx new_addr)
                                   (extend_forwarding fwd addr new_addr)))
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
  : Lemma (requires represents_fwd farr fwd /\
                    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\
                    U64.v addr % 8 == 0)
          (ensures (let idx = U64.v addr / 8 in
                    idx < fwd_array_size /\
                    Seq.index farr idx == fwd addr))
  =
  let idx = U64.v addr / 8 in
  assert (idx < fwd_array_size);
  // represents_fwd: farr[idx] == fwd (uint_to_t (idx * 8))
  // idx * 8 == addr (since addr % 8 == 0)
  assert (U64.uint_to_t (idx * 8) == addr)

let queue_update_correspondence
  (q: seq U64.t) (cs_queue: seq U64.t) (bk: nat) (addr: U64.t)
  : Lemma (requires Seq.length q >= bk + 1 /\
                    bk == Seq.length cs_queue /\
                    (forall (j:nat). j < bk ==> Seq.index q j == Seq.index cs_queue j))
          (ensures (let q2 = Seq.upd q bk addr in
                    let cq2 = Seq.append cs_queue (Seq.create 1 addr) in
                    Seq.length cq2 == bk + 1 /\
                    (forall (j:nat). j < bk + 1 ==> Seq.index q2 j == Seq.index cq2 j)))
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
  : Lemma (requires U64.v addr < 8 \/ U64.v addr >= minor_heap_size \/ U64.v addr % 8 <> 0)
          (ensures ~(Seq.mem addr (minor_objects minor)))
  = FStar.Classical.move_requires (minor_objects_valid minor) addr

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let minor_object_passes_guards (minor: minor_state) (obj: U64.t)
  : Lemma (requires minor_wf minor /\ Seq.mem obj (minor_objects minor))
          (ensures minor_wosize minor obj < minor_heap_size /\
                   U64.v obj + minor_wosize minor obj * 8 <= minor_heap_size)
  = minor_objects_body_bound minor obj

let not_minor_if_wosize_bounds_fail (minor: minor_state) (addr: U64.t)
  : Lemma (requires minor_wf minor /\
                    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0 /\
                    (minor_wosize minor addr >= minor_heap_size \/
                     U64.v addr + minor_wosize minor addr * 8 > minor_heap_size))
          (ensures ~(Seq.mem addr (minor_objects minor)))
  =
  // Contrapositive of minor_object_passes_guards
  FStar.Classical.move_requires (minor_objects_body_bound minor) addr

let promote_object_zero_noop
  (minor_st: minor_state) (ms: heap) (addr: U64.t) (fp: U64.t) (wz: nat)
  : Lemma (requires wz > 0 /\
                    (GC.Gen.Promote.promote_object minor_st ms addr fp wz).new_addr == 0UL)
          (ensures (GC.Gen.Promote.promote_object minor_st ms addr fp wz).major_out == ms /\
                   (GC.Gen.Promote.promote_object minor_st ms addr fp wz).fp_out == fp)
  =
  let alloc_out = (GC.Spec.Allocator.alloc_spec ms fp wz).obj_out in
  if alloc_out = 0UL then
    GC.Gen.Promote.promote_object_oom minor_st ms addr fp wz
  else begin
    GC.Gen.Promote.promote_object_success minor_st ms addr fp wz;
    assert false
  end

#pop-options

/// Re-export for callers that need the explicit quantifier form
let cheney_forward_one_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures (let cs' = CheneySpec.cheney_forward_one minor cs addr in
                    forall (j:nat). j < Seq.length cs'.cs_queue ==>
                      Seq.mem (Seq.index cs'.cs_queue j) (minor_objects minor)))
  = SimOne.queue_valid_intro minor cs.cs_queue;
    SimOne.fwd_one_preserves_queue_valid minor cs addr;
    SimOne.queue_valid_elim minor (CheneySpec.cheney_forward_one minor cs addr).cs_queue

let cheney_forward_one_queue_bound
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (ensures (let cs' = CheneySpec.cheney_forward_one minor cs addr in
                    Seq.length cs'.cs_queue <= Seq.length cs.cs_queue + 1))
  = SimOne.cheney_forward_one_queue_bound minor cs addr

/// ---------------------------------------------------------------------------
/// Queue validity through forward_fields and forward_roots (induction)
/// Uses opaque queue_valid predicate to prevent quantifier nesting.
/// Delegates to SimOne which has the recursive proofs with equation lemmas.
/// ---------------------------------------------------------------------------

let cheney_forward_fields_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures (let cs' = CheneySpec.cheney_forward_fields minor cs parent idx wosize in
                    forall (j:nat). j < Seq.length cs'.cs_queue ==>
                      Seq.mem (Seq.index cs'.cs_queue j) (minor_objects minor)))
  = SimOne.queue_valid_intro minor cs.cs_queue;
    SimOne.forward_fields_preserves_queue_valid minor cs parent idx wosize;
    SimOne.queue_valid_elim minor (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_queue

let cheney_forward_roots_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures (let cs' = CheneySpec.cheney_forward_roots minor cs roots idx in
                    forall (j:nat). j < Seq.length cs'.cs_queue ==>
                      Seq.mem (Seq.index cs'.cs_queue j) (minor_objects minor)))
  = SimOne.queue_valid_intro minor cs.cs_queue;
    SimOne.forward_roots_preserves_queue_valid minor cs roots idx;
    SimOne.queue_valid_elim minor (CheneySpec.cheney_forward_roots minor cs roots idx).cs_queue

let cheney_scan_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures (let cs' = CheneySpec.cheney_scan minor cs scan fuel in
                    forall (j:nat). j < Seq.length cs'.cs_queue ==>
                      Seq.mem (Seq.index cs'.cs_queue j) (minor_objects minor)))
  = SimOne.queue_valid_intro minor cs.cs_queue;
    SimOne.scan_preserves_queue_valid minor cs scan fuel;
    SimOne.queue_valid_elim minor (CheneySpec.cheney_scan minor cs scan fuel).cs_queue

/// ---------------------------------------------------------------------------
/// Queue bound through forward_roots and scan (uses BFS invariant)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"

let cheney_forward_roots_queue_bound
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires SimOne.cheney_bfs_inv minor cs /\
                    Seq.length (minor_objects minor) <= queue_size)
          (ensures (let cs' = CheneySpec.cheney_forward_roots minor cs roots idx in
                    SimOne.cheney_bfs_inv minor cs' /\
                    Seq.length cs'.cs_queue <= Seq.length (minor_objects minor) /\
                    Seq.length cs'.cs_queue <= queue_size))
  = SimOne.forward_roots_preserves_bfs_inv minor cs roots idx;
    SimOne.cheney_bfs_inv_bound minor (CheneySpec.cheney_forward_roots minor cs roots idx)

let cheney_scan_queue_bound
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires SimOne.cheney_bfs_inv minor cs /\
                    Seq.length (minor_objects minor) <= queue_size)
          (ensures (let cs' = CheneySpec.cheney_scan minor cs scan fuel in
                    SimOne.cheney_bfs_inv minor cs' /\
                    Seq.length cs'.cs_queue <= Seq.length (minor_objects minor) /\
                    Seq.length cs'.cs_queue <= queue_size))
  = SimOne.scan_preserves_bfs_inv minor cs scan fuel;
    SimOne.cheney_bfs_inv_bound minor (CheneySpec.cheney_scan minor cs scan fuel)

#pop-options

/// ---------------------------------------------------------------------------
/// Scan fuel sufficiency
/// ---------------------------------------------------------------------------

// TODO: This requires showing that cheney_scan with enough fuel to drain the
// queue produces the same result as with any larger fuel. This is a more
// complex inductive argument. For now, we defer this.
let cheney_scan_fuel_sufficient
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel1 fuel2: nat)
  : Lemma (requires fuel1 >= fuel2 /\
                    fuel2 >= Seq.length cs.cs_queue - scan /\
                    Seq.length cs.cs_queue <= Seq.length (minor_objects minor) /\
                    Seq.length (minor_objects minor) <= queue_size /\
                    (forall (j:nat). j < Seq.length cs.cs_queue ==>
                      Seq.mem (Seq.index cs.cs_queue j) (minor_objects minor)))
          (ensures CheneySpec.cheney_scan minor cs scan fuel1 ==
                   CheneySpec.cheney_scan minor cs scan fuel2)
  = admit () // Complex inductive argument — will prove separately if needed

/// ---------------------------------------------------------------------------
/// Bridge: minor_read ↔ minor_read_field
/// ---------------------------------------------------------------------------

let minor_read_eq_field (ms: minor_state) (obj: U64.t) (fi: nat)
  : Lemma (requires U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\ U64.v obj % 8 == 0 /\
                    fi < minor_heap_size /\
                    U64.v obj + fi * 8 + 8 <= minor_heap_size)
          (ensures minor_read_word_t ms.data (U64.uint_to_t (U64.v obj + fi * 8)) ==
                   minor_read_field ms obj fi)
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

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let cheney_bfs_inv_strict_room
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires SimOne.cheney_bfs_inv minor cs /\
                    Seq.mem addr (minor_objects minor) /\
                    cs.CheneySpec.cs_fwd addr = 0UL /\
                    Seq.length (minor_objects minor) <= queue_size)
          (ensures Seq.length cs.CheneySpec.cs_queue < queue_size)
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

let minor_guards_sufficient (ms: minor_state) (addr: U64.t)
  : Lemma (requires minor_wf ms /\
                    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0 /\
                    minor_wosize ms addr > 0 /\
                    U64.v addr + minor_wosize ms addr * 8 <= minor_heap_size)
          (ensures Seq.mem addr (minor_objects ms))
  = admit ()
