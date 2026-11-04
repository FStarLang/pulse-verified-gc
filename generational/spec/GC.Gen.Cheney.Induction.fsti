/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney.Induction - induction over a Cheney run
/// ---------------------------------------------------------------------------
///
/// A Cheney run (`cheney_promote`) is roots, then scan; the scan forwards the
/// fields of each queued object; every step is one `cheney_forward_one`,
/// which forwards a normal object (one `promote_object`) or the parent of an
/// infix one.  An invariant of the Cheney state that every
/// `cheney_forward_one` keeps is therefore kept by the whole run.  This
/// module proves that once, at each level of the run, for two shapes of
/// invariant:
///
/// - `inv: cheney_state -> prop`, given the `cheney_forward_one` step
///   (`one_keeps`);
/// - `p: heap -> U64.t -> prop`, an invariant of the major heap and the free
///   pointer alone, given the `promote_object` step (`promote_keeps`); the
///   infix case and the no-op cases are handled here.
///
/// Both carry the allocator's invariant `alloc_ok` (blocks fit, the free
/// list is valid and terminates), which every step needs, so a step may
/// assume it.

module GC.Gen.Cheney.Induction

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// The allocator's invariant on the major heap and free pointer.
let alloc_ok (g: heap) (fp: U64.t) : prop =
  blocks_fit g /\
  AllocLemmas.fl_valid g fp heap_words /\
  AllocLemmas.fl_chain_terminates g fp heap_words

/// The state a run starts from, and the state it ends in.
let cheney_init (ph: gc_phase) (major: heap) (fp: U64.t) : cheney_state =
  { cs_major = major; cs_fp = fp; cs_fwd = empty_forwarding; cs_queue = Seq.empty; cs_phase = ph }

let cheney_run (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot cheney_state
  = cheney_scan minor (cheney_forward_roots minor (cheney_init ph major fp) roots 0)
      0 (cheney_fuel minor)

/// `cheney_promote` is the end state of the run.
val cheney_promote_is_run
  (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (let prom = cheney_promote ph minor major fp roots in
           let cs = cheney_run ph minor major fp roots in
           cs.cs_phase == ph /\
           prom.major_final == cs.cs_major /\
           prom.fp_final == cs.cs_fp /\
           prom.fwd_map == cs.cs_fwd)

/// ---------------------------------------------------------------------------
/// Invariants of the Cheney state
/// ---------------------------------------------------------------------------

/// The step obligation, for an invariant that needs nothing of the
/// allocator.
let one_keeps_plain (minor: minor_state) (inv: cheney_state -> prop) =
  cs: cheney_state -> addr: U64.t ->
  Lemma (requires inv cs)
        (ensures inv (cheney_forward_one minor cs addr))

val cheney_forward_fields_induction_plain
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps_plain minor inv)
  (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires inv cs)
          (ensures inv (cheney_forward_fields minor cs parent idx wosize))

val cheney_forward_roots_induction_plain
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps_plain minor inv)
  (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires inv cs)
          (ensures inv (cheney_forward_roots minor cs roots idx))

val cheney_scan_induction_plain
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps_plain minor inv)
  (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires inv cs)
          (ensures inv (cheney_scan minor cs scan fuel))

val cheney_promote_induction_plain
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps_plain minor inv)
  (ph: gc_phase) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires inv (cheney_init ph major fp))
          (ensures (let cs = cheney_run ph minor major fp roots in
                    let prom = cheney_promote ph minor major fp roots in
                    inv cs /\
                    prom.major_final == cs.cs_major /\
                    prom.fp_final == cs.cs_fp /\
                    prom.fwd_map == cs.cs_fwd))

/// The step obligation: one `cheney_forward_one` keeps `inv`.
let one_keeps (minor: minor_state) (inv: cheney_state -> prop) =
  cs: cheney_state -> addr: U64.t ->
  Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ inv cs)
        (ensures inv (cheney_forward_one minor cs addr))

val cheney_forward_fields_induction
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps minor inv)
  (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ inv cs)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    alloc_ok cs'.cs_major cs'.cs_fp /\ inv cs'))

val cheney_forward_roots_induction
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps minor inv)
  (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ inv cs)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    alloc_ok cs'.cs_major cs'.cs_fp /\ inv cs'))

val cheney_scan_induction
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps minor inv)
  (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ inv cs)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    alloc_ok cs'.cs_major cs'.cs_fp /\ inv cs'))

/// **The run keeps every invariant its steps keep.**
val cheney_promote_induction
  (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps minor inv)
  (ph: gc_phase) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires alloc_ok major fp /\ inv (cheney_init ph major fp))
          (ensures (let cs = cheney_run ph minor major fp roots in
                    let prom = cheney_promote ph minor major fp roots in
                    alloc_ok cs.cs_major cs.cs_fp /\ inv cs /\
                    prom.major_final == cs.cs_major /\
                    prom.fp_final == cs.cs_fp /\
                    prom.fwd_map == cs.cs_fwd))

/// ---------------------------------------------------------------------------
/// The allocator's invariant
/// ---------------------------------------------------------------------------

val cheney_forward_normal_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    blocks_fit cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))

val cheney_forward_one_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    blocks_fit cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))

val cheney_forward_fields_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    blocks_fit cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))

val cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    blocks_fit cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))

val cheney_scan_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires blocks_fit cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    blocks_fit cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))

/// ---------------------------------------------------------------------------
/// Invariants of the major heap and free pointer
/// ---------------------------------------------------------------------------

/// The step obligation: one successful promotion at the run's phase `ph`
/// keeps `p`.
let promote_keeps (minor: minor_state) (ph: gc_phase) (p: heap -> U64.t -> prop) =
  major: heap -> fp: U64.t -> obj: U64.t -> wz: nat{wz > 0} ->
  Lemma (requires alloc_ok major fp /\ p major fp /\
                  Seq.mem obj (minor_objects minor) /\
                  wz == minor_wosize minor obj /\ wz < pow2 54 /\
                  (promote_object minor major obj fp wz ph).new_addr <> 0UL)
        (ensures (let res = promote_object minor major obj fp wz ph in
                  p res.major_out res.fp_out))

/// `p` of the state's heap and free pointer, at the run's phase.
let heap_inv (ph: gc_phase) (p: heap -> U64.t -> prop) (cs: cheney_state) : prop =
  cs.cs_phase == ph /\ p cs.cs_major cs.cs_fp

val cheney_forward_normal_keeps
  (minor: minor_state) (ph: gc_phase) (p: heap -> U64.t -> prop) (step: promote_keeps minor ph p)
  (cs: cheney_state) (addr: U64.t)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ p cs.cs_major cs.cs_fp /\ cs.cs_phase == ph)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    alloc_ok cs'.cs_major cs'.cs_fp /\ p cs'.cs_major cs'.cs_fp))

val cheney_forward_one_keeps
  (minor: minor_state) (ph: gc_phase) (p: heap -> U64.t -> prop) (step: promote_keeps minor ph p)
  (cs: cheney_state) (addr: U64.t)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ p cs.cs_major cs.cs_fp /\ cs.cs_phase == ph)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    alloc_ok cs'.cs_major cs'.cs_fp /\ p cs'.cs_major cs'.cs_fp))

val cheney_forward_fields_keeps
  (minor: minor_state) (ph: gc_phase) (p: heap -> U64.t -> prop) (step: promote_keeps minor ph p)
  (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ p cs.cs_major cs.cs_fp /\ cs.cs_phase == ph)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    alloc_ok cs'.cs_major cs'.cs_fp /\ p cs'.cs_major cs'.cs_fp))

val cheney_forward_roots_keeps
  (minor: minor_state) (ph: gc_phase) (p: heap -> U64.t -> prop) (step: promote_keeps minor ph p)
  (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ p cs.cs_major cs.cs_fp /\ cs.cs_phase == ph)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    alloc_ok cs'.cs_major cs'.cs_fp /\ p cs'.cs_major cs'.cs_fp))

val cheney_scan_keeps
  (minor: minor_state) (ph: gc_phase) (p: heap -> U64.t -> prop) (step: promote_keeps minor ph p)
  (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp /\ p cs.cs_major cs.cs_fp /\ cs.cs_phase == ph)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    alloc_ok cs'.cs_major cs'.cs_fp /\ p cs'.cs_major cs'.cs_fp))

/// **The run keeps every heap invariant that promotion keeps.**
val cheney_promote_keeps
  (minor: minor_state) (ph: gc_phase) (p: heap -> U64.t -> prop) (step: promote_keeps minor ph p)
  (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires alloc_ok major fp /\ p major fp)
          (ensures (let prom = cheney_promote ph minor major fp roots in
                    alloc_ok prom.major_final prom.fp_final /\
                    p prom.major_final prom.fp_final))
