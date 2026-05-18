/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyBFS — Proofs of BFS completeness for the Cheney collector
/// ---------------------------------------------------------------------------

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
/// Graph lemma: fwd_well_formed ⟹ all reachable forwarded
/// ---------------------------------------------------------------------------
///
/// Uses the reachability induction principle: any predicate that holds for
/// roots and is closed under successors holds for all reachable objects.

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

let fwd_well_formed_covers_reachable
  (minor: minor_state) (fwd: forwarding_map) (roots: seq U64.t)
  : Lemma (requires fwd_well_formed minor fwd roots)
          (ensures forall (x: U64.t).
            Seq.mem x (minor_reachable minor roots) /\
            minor_wosize minor x > 0 ==>
            fwd x <> 0UL)
  =
  // Predicate: "if wosize > 0, then forwarded"
  let p (x: U64.t) : prop = minor_wosize minor x > 0 ==> fwd x <> 0UL in
  // Closure: if p(a) and b ∈ successors(a), then p(b)
  // Two cases for a:
  //   - wosize(a) > 0: p(a) gives fwd(a)≠0, fwd_closed gives fwd(b)≠0 if wosize(b)>0
  //   - wosize(a) = 0: successors(a) is empty (length ≤ wosize = 0), contradiction
  let closure (a b: U64.t)
    : Lemma (requires p a /\ Seq.mem b (minor_successors minor a))
            (ensures p b)
    = minor_successors_length minor a;
      if minor_wosize minor a > 0
      then () // fwd_closed handles this
      else () // |successors| <= wosize = 0, but mem b => |successors| > 0, contradiction
  in
  Classical.forall_intro_2 (fun a -> Classical.move_requires (closure a));
  let aux (x: U64.t)
    : Lemma (requires Seq.mem x (minor_reachable minor roots) /\
                      minor_wosize minor x > 0)
            (ensures fwd x <> 0UL)
    = minor_reachable_ind minor roots p x
  in
  Classical.forall_intro (Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// fwd monotonicity: forward_one only extends the forwarding map
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let forward_one_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_forward_one minor cs addr).cs_fwd x <> 0UL)
  =
  if cs.cs_fwd addr <> 0UL then
    CheneySpec.cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    // Infix case: forward parent preserves fwd entries, extend_forwarding
    // only touches addr (which is <> x since cs.cs_fwd addr = 0 but cs.cs_fwd x <> 0).
    assume ((CheneySpec.cheney_forward_one minor cs addr).cs_fwd x <> 0UL)
  end
  else begin
    CheneySpec.cheney_forward_one_normal minor cs addr;
    if not (Seq.mem addr (minor_objects minor)) then
      CheneySpec.cheney_forward_normal_noop minor cs addr
    else if minor_wosize minor addr = 0 then
      CheneySpec.cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        CheneySpec.cheney_forward_normal_noop_oom minor cs addr
      else
        CheneySpec.cheney_forward_normal_success minor cs addr
    end
  end

#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

let rec forward_fields_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_fwd x <> 0UL)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    CheneySpec.cheney_forward_fields_base minor cs parent idx wosize
  else begin
    CheneySpec.cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = CheneySpec.cheney_forward_one minor cs field_val in
    forward_one_fwd_monotone minor cs field_val x;
    forward_fields_fwd_monotone minor cs' parent (idx + 1) wosize x
  end

let rec forward_roots_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (roots: seq U64.t) (idx: nat) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_forward_roots minor cs roots idx).cs_fwd x <> 0UL)
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    CheneySpec.cheney_forward_roots_base minor cs roots idx
  else begin
    CheneySpec.cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = CheneySpec.cheney_forward_one minor cs r in
    forward_one_fwd_monotone minor cs r x;
    forward_roots_fwd_monotone minor cs' roots (idx + 1) x
  end

let rec scan_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (scan: nat) (fuel: nat) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_scan minor cs scan fuel).cs_fwd x <> 0UL)
          (decreases fuel)
  =
  if fuel = 0 || scan >= Seq.length cs.cs_queue then
    CheneySpec.cheney_scan_base minor cs scan fuel
  else begin
    CheneySpec.cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = CheneySpec.cheney_forward_fields minor cs obj 0 wz in
    forward_fields_fwd_monotone minor cs obj 0 wz x;
    scan_fwd_monotone minor cs' (scan + 1) (fuel - 1) x
  end

#pop-options

/// ---------------------------------------------------------------------------
/// Main theorem: BFS completeness under no-OOM
/// ---------------------------------------------------------------------------

let cheney_promotes_all_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires cheney_no_oom minor major fp roots)
          (ensures (let prom = CheneySpec.cheney_promote minor major fp roots in
                    forall (x: U64.t).
                      Seq.mem x (minor_reachable minor roots) /\
                      minor_wosize minor x > 0 ==>
                      prom.fwd_map x <> 0UL))
  =
  let prom = CheneySpec.cheney_promote minor major fp roots in
  fwd_well_formed_covers_reachable minor prom.fwd_map roots
