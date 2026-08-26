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

/// The forwarding map covers every root that resolves to a minor object with
/// wosize > 0.  Resolution matters because a root may point into the interior
/// of a nursery closure; what has to be copied is the closure it points into.
let fwd_covers_roots (minor: minor_state) (fwd: forwarding_map) (roots: seq U64.t) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\
    Seq.mem (resolve_minor minor r) (minor_objects minor) /\
    minor_wosize minor (resolve_minor minor r) > 0 ==>
    fwd (resolve_minor minor r) <> 0UL

/// The forwarding map is closed under minor_successors:
/// if x is forwarded and y is a successor with wosize > 0, then y is forwarded too
let fwd_closed (minor: minor_state) (fwd: forwarding_map) : prop =
  forall (x y: U64.t).
    Seq.mem x (minor_objects minor) /\
    fwd x <> 0UL /\
    Seq.mem y (minor_successors minor x) /\
    minor_wosize minor y > 0 ==>
    fwd y <> 0UL

/// Every interior nursery pointer stored in a field of a forwarded closure has
/// a forwarding entry of its own, not merely an entry for the closure it points
/// into.  `update_major_pointers` and `rewrite_root` look the map up at the
/// address exactly as stored, so the enclosing closure's entry would leave such
/// a field pointing into the nursery that collection then abandons.
let fwd_covers_infix_fields (minor: minor_state) (fwd: forwarding_map) : prop =
  forall (x: U64.t) (j: nat).
    Seq.mem x (minor_objects minor) /\
    fwd x <> 0UL /\
    j < minor_wosize minor x /\
    is_infix_in_minor minor (to_minor_offset (minor_read_field minor x j)) ==>
    fwd (to_minor_offset (minor_read_field minor x j)) <> 0UL

/// The same obligation for an interior root: `rewrite_root` reads the map at
/// the root as the mutator stored it.
let fwd_covers_infix_roots (minor: minor_state) (fwd: forwarding_map) (roots: seq U64.t) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\ is_infix_in_minor minor r ==> fwd r <> 0UL

/// Combined: the forwarding map is well-formed for BFS correctness
let fwd_well_formed (minor: minor_state) (fwd: forwarding_map) (roots: seq U64.t) : prop =
  fwd_covers_roots minor fwd roots /\
  fwd_closed minor fwd /\
  fwd_covers_infix_fields minor fwd /\
  fwd_covers_infix_roots minor fwd roots

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

val scan_preserves_fwd_covers_infix_roots
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (roots: seq U64.t) (scan fuel: nat)
  : Lemma (requires minor_infix_wf minor /\
                    fwd_covers_infix_roots minor cs.cs_fwd roots)
          (ensures fwd_covers_infix_roots minor
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

/// Introduce coverage for an address that is not an interior pointer, so that
/// the address is its own resolution.
val addr_covered_intro
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires ~(is_infix_in_minor minor addr) /\
                    (Seq.mem addr (minor_objects minor) /\
                     minor_wosize minor addr > 0 ==> cs.cs_fwd addr <> 0UL))
          (ensures addr_covered minor cs addr)

/// Introduce coverage for an address that already has a forwarding entry.  The
/// BFS invariant supplies the enclosing closure's entry when the address is an
/// interior pointer, which is what the *already forwarded* branch of
/// `cheney_forward_one` needs: it returns the state untouched.
val addr_covered_intro_forwarded
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires GC.Gen.Cheney.SimOne.cheney_bfs_inv minor cs /\
                    minor_wf minor /\
                    cs.cs_fwd addr <> 0UL)
          (ensures addr_covered minor cs addr)

/// Introduce coverage for an interior pointer whose enclosing closure has been
/// forwarded.  The interior address is itself never a minor object, so the
/// closure's entry is all that coverage asks for.
val addr_covered_intro_infix
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires minor_wf minor /\
                    is_infix_in_minor minor addr /\
                    cs.cs_fwd addr <> 0UL /\
                    cs.cs_fwd (infix_parent minor addr) <> 0UL)
          (ensures addr_covered minor cs addr)

/// Coverage of an interior pointer after one forwarding step: forwarding the
/// interior address goes through its enclosing closure, so the closure's entry
/// after the step is all the caller has to exhibit.
/// The room bound below is what makes the interior branch's arithmetic guard
/// pass, so the step really does install an entry at the interior address --
/// coverage now asserts that entry, not just the closure's.
val addr_covered_infix_step
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires minor_wf minor /\
                    minor_infix_wf minor /\
                    is_infix_in_minor minor addr /\
                    cs.cs_fwd addr = 0UL /\
                    infix_parent minor addr <> addr /\
                    (let parent = infix_parent minor addr in
                     let cs' = CheneySpec.cheney_forward_normal minor cs parent in
                     cs'.cs_fwd parent <> 0UL /\
                     U64.v (cs'.cs_fwd parent) + minor_wosize minor parent * 8 <= heap_size))
          (ensures addr_covered minor (CheneySpec.cheney_forward_one minor cs addr) addr)

val addr_covered_elim
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires addr_covered minor cs addr /\
                    Seq.mem addr (minor_objects minor) /\ minor_wosize minor addr > 0)
          (ensures cs.cs_fwd addr <> 0UL)

/// Coverage also names the object an interior pointer keeps alive.
val addr_covered_elim_resolved
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires addr_covered minor cs addr /\
                    Seq.mem (resolve_minor minor addr) (minor_objects minor) /\
                    minor_wosize minor (resolve_minor minor addr) > 0)
          (ensures cs.cs_fwd (resolve_minor minor addr) <> 0UL)

/// Coverage of an interior pointer names the interior address itself, which is
/// where the field rewrite reads the forwarding map.
val addr_covered_elim_infix
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires addr_covered minor cs addr /\
                    is_infix_in_minor minor addr)
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
          (ensures fwd_covers_roots minor cs.cs_fwd roots /\
                   fwd_covers_infix_roots minor cs.cs_fwd roots)

val root_prefix_all_implies_covers_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (oom: bool)
  : Lemma (requires (not oom ==> root_prefix_covered minor cs roots (Seq.length roots)))
          (ensures not oom ==> (fwd_covers_roots minor cs.cs_fwd roots /\
                                fwd_covers_infix_roots minor cs.cs_fwd roots))

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

/// The interior half of the same aggregation: a scanned closure's interior
/// field targets are entries of the map in their own right.
val field_prefix_all_implies_infix
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t)
  : Lemma (requires field_prefix_covered minor cs parent (minor_wosize minor parent))
          (ensures forall (j: nat).
            j < minor_wosize minor parent /\
            is_infix_in_minor minor (to_minor_offset (minor_read_field minor parent j)) ==>
            cs.cs_fwd (to_minor_offset (minor_read_field minor parent j)) <> 0UL)

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
          (ensures fwd_closed minor cs.cs_fwd /\
                   fwd_covers_infix_fields minor cs.cs_fwd)

val scanned_exhausted_implies_fwd_closed_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (oom: bool)
  : Lemma (requires GC.Gen.Cheney.SimOne.cheney_bfs_inv minor cs /\
                    (not oom ==> scanned_prefix_closed minor cs scan) /\
                    scan >= Seq.length cs.cs_queue)
          (ensures not oom ==> (fwd_closed minor cs.cs_fwd /\
                                fwd_covers_infix_fields minor cs.cs_fwd))

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
                     (not oom_roots ==> (fwd_covers_roots minor cs1.CheneySpec.cs_fwd roots /\
                                         fwd_covers_infix_roots minor cs1.CheneySpec.cs_fwd roots)) /\
                     (not oom_final ==> (fwd_closed minor cs2.CheneySpec.cs_fwd /\
                                         fwd_covers_infix_fields minor cs2.CheneySpec.cs_fwd))))
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

/// ---------------------------------------------------------------------------
/// Out-of-memory witness
/// ---------------------------------------------------------------------------
///
/// `cheney_no_oom` is what the collector guarantees when it reports success.
/// The predicates below are what it guarantees when it reports *failure*: not
/// merely "something went wrong", but a concrete out-of-memory event -- a
/// specific object, at a specific point of this collection, that the major
/// free list had no room for.
///
/// Note these are not literal duals of `cheney_no_oom`.  `cheney_no_oom` is a
/// property of the collection's final forwarding map; deriving the negation of
/// it from a failed promotion would require proving that an object the
/// allocator once refused is never accepted later, i.e. a monotonicity theorem
/// about the first-fit free-list allocator.  The witness below says something
/// more direct and more useful to a caller: *here is the object that did not
/// fit, and here is the point in the collection at which it did not fit.*

/// A failed promotion: `addr` is an allocated minor object of positive size
/// that state `cs` has not forwarded yet, and `promote_object` cannot place it
/// -- the free list of `cs.cs_major` has no block big enough.  This is exactly
/// the hypothesis of `GC.Gen.Cheney.cheney_forward_normal_noop_oom`.
let promote_fails_at (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) : prop =
  Seq.mem addr (minor_objects minor) /\
  cs.CheneySpec.cs_fwd addr == 0UL /\
  minor_wosize minor addr > 0 /\
  (promote_object minor cs.CheneySpec.cs_major addr cs.CheneySpec.cs_fp
     (minor_wosize minor addr)).new_addr == 0UL

/// Forwarding `addr` from `cs` fails for lack of room.  For an ordinary
/// address that is a failed promotion of `addr` itself; for an interior
/// (infix) pointer it is a failed promotion of the enclosing object, which is
/// what `cheney_forward_one` actually tries to promote.
let promote_fails_for (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) : prop =
  promote_fails_at minor cs addr \/
  (is_infix_in_minor minor addr /\
   promote_fails_at minor cs (infix_parent minor addr))

/// `cs` is a state this collection passes through on its way to `final`, and
/// the very next thing the collector does there is to try to forward `addr`.
///
/// The two disjuncts are the two loops that call `cheney_forward_one`: the
/// root loop (about to forward `roots[ridx]`) and the field loop (about to
/// forward field `fld` of `parent`).  In both cases the tie to the run is the
/// residual equation "finishing the collection from here yields `final`",
/// which is precisely the invariant those loops already carry.
let cheney_attempts (minor: minor_state) (cs: CheneySpec.cheney_state)
                    (final: CheneySpec.cheney_state) (addr: U64.t) : prop =
  (exists (roots: seq U64.t) (ridx: nat) (fuel: nat).
     ridx < Seq.length roots /\ Seq.index roots ridx == addr /\
     CheneySpec.cheney_scan minor
       (CheneySpec.cheney_forward_roots minor cs roots ridx) 0 fuel == final) \/
  (exists (parent: U64.t) (fld: nat) (wz: nat) (scan: nat) (fuel: nat).
     fld < wz /\ to_minor_offset (minor_read_field minor parent fld) == addr /\
     CheneySpec.cheney_scan minor
       (CheneySpec.cheney_forward_fields minor cs parent fld wz) scan fuel == final)

/// The collection whose BFS ends in `final` ran out of major-heap room.
///
/// Opaque to SMT: this and `cheney_oom_fields` are carried by the collector's
/// loop invariants, where unfolding their existentials only slows Z3 down.
/// Use the intro/elim lemmas below.
[@@"opaque_to_smt"]
let cheney_oom_reaching (minor: minor_state) (final: CheneySpec.cheney_state) : prop =
  exists (cs: CheneySpec.cheney_state) (addr: U64.t).
    cheney_attempts minor cs final addr /\ promote_fails_for minor cs addr

/// The state `cheney_promote` ends in (its result is this state's projection).
let cheney_promote_state (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : GTot CheneySpec.cheney_state
  = let cs0 : CheneySpec.cheney_state =
      { CheneySpec.cs_major = major; CheneySpec.cs_fp = fp;
        CheneySpec.cs_fwd = empty_forwarding; CheneySpec.cs_queue = Seq.empty } in
    CheneySpec.cheney_scan minor
      (CheneySpec.cheney_forward_roots minor cs0 roots 0) 0 (CheneySpec.cheney_fuel minor)

/// `cheney_promote minor major fp roots` ran out of major-heap room.
let cheney_oom (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t) : prop =
  cheney_oom_reaching minor (cheney_promote_state minor major fp roots)

/// Introduction from the root loop: the collector was about to forward
/// `roots[ridx]` and the out-of-memory flag went up while it did so.
///
/// Stated in the flag-transition style of `root_prefix_step_oom` so that the
/// caller can invoke it unconditionally, without branching on a runtime flag.
val cheney_oom_intro_root
  (minor: minor_state) (cs: CheneySpec.cheney_state) (final: CheneySpec.cheney_state)
  (roots: seq U64.t) (ridx: nat) (fuel: nat) (oom_before oom_after: bool)
  : Lemma (requires ridx < Seq.length roots /\
                    ((not oom_before /\ oom_after) ==>
                     promote_fails_for minor cs (Seq.index roots ridx)) /\
                    CheneySpec.cheney_scan minor
                      (CheneySpec.cheney_forward_roots minor cs roots ridx) 0 fuel == final)
          (ensures (not oom_before /\ oom_after) ==> cheney_oom_reaching minor final)

/// The same witness, local to one pass of the field loop: scanning `parent`'s
/// fields from `cs` hit a promotion that did not fit.
///
/// The field loop carries this rather than `cheney_oom_reaching` because it
/// mentions only what that loop already has in its invariant -- the object
/// being scanned and the state the scan of it started from.  It is converted
/// to the run-level witness once, on the way out, where the enclosing scan
/// step's residual equation is in scope.
[@@"opaque_to_smt"]
let cheney_oom_fields (minor: minor_state) (cs: CheneySpec.cheney_state)
                      (parent: U64.t) (wz: nat) : prop =
  exists (cs': CheneySpec.cheney_state) (fld: nat).
    fld < wz /\
    CheneySpec.cheney_forward_fields minor cs' parent fld wz ==
      CheneySpec.cheney_forward_fields minor cs parent 0 wz /\
    promote_fails_for minor cs' (to_minor_offset (minor_read_field minor parent fld))

/// Introduction from the field loop: the collector was about to forward field
/// `fld` of `parent` and the out-of-memory flag went up while it did so.
val cheney_oom_intro_field
  (minor: minor_state) (cs: CheneySpec.cheney_state) (cs': CheneySpec.cheney_state)
  (parent: U64.t) (fld: nat) (wz: nat) (oom_before oom_after: bool)
  : Lemma (requires fld < wz /\
                    ((not oom_before /\ oom_after) ==>
                     promote_fails_for minor cs'
                       (to_minor_offset (minor_read_field minor parent fld))) /\
                    CheneySpec.cheney_forward_fields minor cs' parent fld wz ==
                      CheneySpec.cheney_forward_fields minor cs parent 0 wz)
          (ensures (not oom_before /\ oom_after) ==> cheney_oom_fields minor cs parent wz)

/// Elimination: a field-loop failure is a failure of the whole run, once the
/// scan step that owns this field loop is tied to the run's outcome.
val cheney_oom_fields_elim
  (minor: minor_state) (cs: CheneySpec.cheney_state) (final: CheneySpec.cheney_state)
  (parent: U64.t) (wz: nat) (scan: nat) (fuel: nat) (oom_before oom_after: bool)
  : Lemma (requires ((not oom_before /\ oom_after) ==> cheney_oom_fields minor cs parent wz) /\
                    CheneySpec.cheney_scan minor
                      (CheneySpec.cheney_forward_fields minor cs parent 0 wz)
                      scan fuel == final)
          (ensures (not oom_before /\ oom_after) ==> cheney_oom_reaching minor final)
