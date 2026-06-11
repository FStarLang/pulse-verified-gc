/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyBFS — BFS completeness for the Cheney collector
/// ---------------------------------------------------------------------------
///
/// Proves that cheney_promote's BFS produces a forwarding map that covers
/// all minor_reachable objects, provided no OOM occurs during the BFS.
///
/// Structure:
///   1. Pure graph lemma: roots-covered + successor-closed ⟹ reachable-covered
///   2. fwd monotonicity through forward_one / forward_fields / forward_roots / scan
///   3. forward_roots covers roots (under no-OOM)
///   4. scan yields successor-closure (under no-OOM)
///   5. Main theorem: cheney_promote_fwd_well_formed

module GC.Gen.CheneyBFS

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Reachability

module CheneySpec = GC.Gen.Cheney

/// ---------------------------------------------------------------------------
/// Predicates: well-formedness of the forwarding map
/// ---------------------------------------------------------------------------

/// The forwarding map covers all roots that are minor objects with wosize > 0
let fwd_covers_roots (minor: minor_state) (fwd: forwarding_map) (roots: seq U64.t) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\
    Seq.mem r (minor_objects minor) /\
    minor_wosize minor r > 0 ==>
    fwd r <> 0UL

/// The forwarding map is closed under minor_successors:
/// if x is forwarded and y is a successor with wosize > 0, then y is forwarded too
let fwd_closed (minor: minor_state) (fwd: forwarding_map) : prop =
  forall (x y: U64.t).
    Seq.mem x (minor_objects minor) /\
    fwd x <> 0UL /\
    Seq.mem y (minor_successors minor x) /\
    minor_wosize minor y > 0 ==>
    fwd y <> 0UL

/// Combined: the forwarding map is well-formed for BFS correctness
let fwd_well_formed (minor: minor_state) (fwd: forwarding_map) (roots: seq U64.t) : prop =
  fwd_covers_roots minor fwd roots /\
  fwd_closed minor fwd

/// ---------------------------------------------------------------------------
/// Graph lemma: fwd_well_formed ⟹ all reachable forwarded
/// ---------------------------------------------------------------------------

/// Pure graph theory: if fwd covers roots and is closed under successors,
/// then fwd covers the entire reachable set.
/// Proof by induction on the reachability structure.
val fwd_well_formed_covers_reachable
  (minor: minor_state) (fwd: forwarding_map) (roots: seq U64.t)
  : Lemma (requires fwd_well_formed minor fwd roots)
          (ensures forall (x: U64.t).
            Seq.mem x (minor_reachable minor roots) /\
            minor_wosize minor x > 0 ==>
            fwd x <> 0UL)

/// ---------------------------------------------------------------------------
/// fwd monotonicity: forward_one only extends the forwarding map
/// ---------------------------------------------------------------------------

val forward_one_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_forward_one minor cs addr).cs_fwd x <> 0UL)

val forward_fields_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_fwd x <> 0UL)

val forward_roots_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (roots: seq U64.t) (idx: nat) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_forward_roots minor cs roots idx).cs_fwd x <> 0UL)

val scan_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (scan: nat) (fuel: nat) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_scan minor cs scan fuel).cs_fwd x <> 0UL)

val scan_preserves_fwd_covers_roots
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (roots: seq U64.t) (scan fuel: nat)
  : Lemma (requires minor_infix_wf minor /\
                    fwd_covers_roots minor cs.cs_fwd roots)
          (ensures fwd_covers_roots minor
            (CheneySpec.cheney_scan minor cs scan fuel).cs_fwd roots)

val forward_one_queue_prefix
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) (k: nat)
  : Lemma (requires k < Seq.length cs.cs_queue)
          (ensures k < Seq.length (CheneySpec.cheney_forward_one minor cs addr).cs_queue /\
                   Seq.index (CheneySpec.cheney_forward_one minor cs addr).cs_queue k ==
                   Seq.index cs.cs_queue k)

val forward_fields_queue_prefix
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (k: nat)
  : Lemma (requires k < Seq.length cs.cs_queue)
          (ensures k < Seq.length (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_queue /\
                   Seq.index (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_queue k ==
                   Seq.index cs.cs_queue k)

[@@"opaque_to_smt"]
val addr_covered (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) : prop

val addr_covered_intro
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires (Seq.mem addr (minor_objects minor) /\
                     minor_wosize minor addr > 0 ==> cs.cs_fwd addr <> 0UL))
          (ensures addr_covered minor cs addr)

val addr_covered_elim
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires addr_covered minor cs addr /\
                    Seq.mem addr (minor_objects minor) /\ minor_wosize minor addr > 0)
          (ensures cs.cs_fwd addr <> 0UL)

val forward_one_preserves_addr_covered
  (minor: minor_state) (cs: CheneySpec.cheney_state) (step_addr x: U64.t)
  : Lemma (requires minor_infix_wf minor /\ addr_covered minor cs x)
          (ensures addr_covered minor (CheneySpec.cheney_forward_one minor cs step_addr) x)

[@@"opaque_to_smt"]
val root_prefix_covered
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat) : prop

val root_prefix_empty (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t)
  : Lemma (ensures root_prefix_covered minor cs roots 0)

val root_prefix_step
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires idx < Seq.length roots /\
                    minor_infix_wf minor /\
                    root_prefix_covered minor cs roots idx /\
                    addr_covered minor (CheneySpec.cheney_forward_one minor cs (Seq.index roots idx))
                      (Seq.index roots idx))
          (ensures root_prefix_covered minor
                    (CheneySpec.cheney_forward_one minor cs (Seq.index roots idx))
                    roots (idx + 1))

val root_prefix_step_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  (oom_before oom_after: bool)
  : Lemma (requires idx < Seq.length roots /\
                    minor_infix_wf minor /\
                    (oom_before == true ==> oom_after == true) /\
                    (not oom_before ==> root_prefix_covered minor cs roots idx) /\
                    (not oom_after ==> addr_covered minor
                      (CheneySpec.cheney_forward_one minor cs (Seq.index roots idx))
                      (Seq.index roots idx)))
          (ensures not oom_after ==> root_prefix_covered minor
                    (CheneySpec.cheney_forward_one minor cs (Seq.index roots idx))
                    roots (idx + 1))

val root_prefix_all_implies_covers
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t)
  : Lemma (requires root_prefix_covered minor cs roots (Seq.length roots))
          (ensures fwd_covers_roots minor cs.cs_fwd roots)

val root_prefix_all_implies_covers_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (oom: bool)
  : Lemma (requires (not oom ==> root_prefix_covered minor cs roots (Seq.length roots)))
          (ensures not oom ==> fwd_covers_roots minor cs.cs_fwd roots)

[@@"opaque_to_smt"]
val field_prefix_covered
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat) : prop

val field_prefix_empty
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t)
  : Lemma (ensures field_prefix_covered minor cs parent 0)

val field_prefix_step
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat)
  : Lemma (requires minor_infix_wf minor /\
                    field_prefix_covered minor cs parent idx /\
                    addr_covered minor
                      (CheneySpec.cheney_forward_one minor cs
                        (to_minor_offset (minor_read_field minor parent idx)))
                      (to_minor_offset (minor_read_field minor parent idx)))
          (ensures field_prefix_covered minor
                    (CheneySpec.cheney_forward_one minor cs
                      (to_minor_offset (minor_read_field minor parent idx)))
                    parent (idx + 1))

val field_prefix_step_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat)
  (oom_before oom_after: bool)
  : Lemma (requires minor_infix_wf minor /\
                    (oom_before == true ==> oom_after == true) /\
                    (not oom_before ==> field_prefix_covered minor cs parent idx) /\
                    (not oom_after ==> addr_covered minor
                      (CheneySpec.cheney_forward_one minor cs
                        (to_minor_offset (minor_read_field minor parent idx)))
                      (to_minor_offset (minor_read_field minor parent idx))))
          (ensures not oom_after ==> field_prefix_covered minor
                    (CheneySpec.cheney_forward_one minor cs
                      (to_minor_offset (minor_read_field minor parent idx)))
                    parent (idx + 1))

val field_prefix_all_implies_successors
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t)
  : Lemma (requires field_prefix_covered minor cs parent (minor_wosize minor parent))
          (ensures forall (y: U64.t).
            Seq.mem y (minor_successors minor parent) /\
            minor_wosize minor y > 0 ==> cs.cs_fwd y <> 0UL)

[@@"opaque_to_smt"]
val scanned_prefix_closed
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) : prop

val scanned_prefix_empty
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (ensures scanned_prefix_closed minor cs 0)

val scanned_prefix_step
  (minor: minor_state) (cs cs': CheneySpec.cheney_state) (scan: nat)
  : Lemma
    (requires
      minor_infix_wf minor /\
      scanned_prefix_closed minor cs scan /\
      scan < Seq.length cs.cs_queue /\
      cs' == CheneySpec.cheney_forward_fields minor cs
        (Seq.index cs.cs_queue scan) 0
        (minor_wosize minor (Seq.index cs.cs_queue scan)) /\
      field_prefix_covered minor cs'
        (Seq.index cs.cs_queue scan)
        (minor_wosize minor (Seq.index cs.cs_queue scan)))
    (ensures scanned_prefix_closed minor cs' (scan + 1))

val scanned_prefix_step_oom
  (minor: minor_state) (cs cs': CheneySpec.cheney_state) (scan: nat)
  (oom_before oom_after: bool)
  : Lemma
    (requires
      minor_infix_wf minor /\
      (oom_before == true ==> oom_after == true) /\
      (not oom_before ==> scanned_prefix_closed minor cs scan) /\
      scan < Seq.length cs.cs_queue /\
      cs' == CheneySpec.cheney_forward_fields minor cs
        (Seq.index cs.cs_queue scan) 0
        (minor_wosize minor (Seq.index cs.cs_queue scan)) /\
      (not oom_after ==> field_prefix_covered minor cs'
        (Seq.index cs.cs_queue scan)
        (minor_wosize minor (Seq.index cs.cs_queue scan))))
    (ensures not oom_after ==> scanned_prefix_closed minor cs' (scan + 1))

val scanned_exhausted_implies_fwd_closed
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat)
  : Lemma (requires GC.Gen.Cheney.SimOne.cheney_bfs_inv minor cs /\
                    scanned_prefix_closed minor cs scan /\
                    scan >= Seq.length cs.cs_queue)
          (ensures fwd_closed minor cs.cs_fwd)

val scanned_exhausted_implies_fwd_closed_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (oom: bool)
  : Lemma (requires GC.Gen.Cheney.SimOne.cheney_bfs_inv minor cs /\
                    (not oom ==> scanned_prefix_closed minor cs scan) /\
                    scan >= Seq.length cs.cs_queue)
          (ensures not oom ==> fwd_closed minor cs.cs_fwd)

/// ---------------------------------------------------------------------------
/// No-OOM predicate
/// ---------------------------------------------------------------------------

/// No OOM occurred during cheney_promote: the final forwarding map covers
/// roots and is closed under successors.  This is the structural guarantee
/// of the Cheney BFS when promote_object never fails.
///
/// A caller establishes this when they know the major heap has enough free
/// space to accommodate all reachable minor objects (a coarse but sufficient
/// condition: free_list_capacity >= minor.bump * 8).
///
/// NOTE: this is NOT a tautological restatement of the conclusion.
/// The conclusion says "all reachable objects are forwarded."
/// This precondition says "roots are forwarded AND forwarding is closed
/// under successors." The conclusion follows by graph-theoretic induction
/// (fwd_well_formed_covers_reachable), which is non-trivial.
let cheney_no_oom (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  fwd_well_formed minor (CheneySpec.cheney_promote minor major fp roots).fwd_map roots

val cheney_no_oom_from_loop_posts
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (oom_roots oom_final: bool)
  : Lemma (requires minor_infix_wf minor /\
                    (let cs0 : CheneySpec.cheney_state =
                       { CheneySpec.cs_major = major; CheneySpec.cs_fp = fp;
                         CheneySpec.cs_fwd = empty_forwarding; CheneySpec.cs_queue = Seq.empty } in
                     let cs1 = CheneySpec.cheney_forward_roots minor cs0 roots 0 in
                     let cs2 = CheneySpec.cheney_scan minor cs1 0 (CheneySpec.cheney_fuel minor) in
                     (oom_roots == true ==> oom_final == true) /\
                     (not oom_roots ==> fwd_covers_roots minor cs1.CheneySpec.cs_fwd roots) /\
                     (not oom_final ==> fwd_closed minor cs2.CheneySpec.cs_fwd)))
          (ensures not oom_final ==> cheney_no_oom minor major fp roots)

/// ---------------------------------------------------------------------------
/// Main theorem: BFS completeness under no-OOM
/// ---------------------------------------------------------------------------

/// All reachable minor objects with positive wosize are forwarded by
/// cheney_promote, provided no OOM occurred (the forwarding map covers
/// roots and is successor-closed).
val cheney_promotes_all_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires cheney_no_oom minor major fp roots)
          (ensures (let prom = CheneySpec.cheney_promote minor major fp roots in
                    forall (x: U64.t).
                      Seq.mem x (minor_reachable minor roots) /\
                      minor_wosize minor x > 0 ==>
                      prom.fwd_map x <> 0UL))
