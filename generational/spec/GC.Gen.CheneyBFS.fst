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
module SimOne = GC.Gen.Cheney.SimOne

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
  let p (x: U64.t) : prop =
    Seq.mem x (minor_objects minor) /\ (minor_wosize minor x > 0 ==> fwd x <> 0UL) in
  let closure (a b: U64.t)
    : Lemma (requires p a /\ Seq.mem b (minor_successors minor a))
            (ensures p b)
    =
      let _i = Seq.index_mem b (minor_successors minor a) in
      minor_successors_length minor a;
      assert (minor_wosize minor a > 0);
      assert (fwd a <> 0UL);
      minor_successors_valid minor a b
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

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

/// Helper: cheney_forward_normal preserves forwarding entries
private let cheney_forward_normal_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL)
          (ensures (CheneySpec.cheney_forward_normal minor cs addr).cs_fwd x <> 0UL)
  =
  if cs.cs_fwd addr <> 0UL then
    CheneySpec.cheney_forward_normal_noop minor cs addr
  else if not (Seq.mem addr (minor_objects minor)) then
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

let forward_one_fwd_monotone
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) (x: U64.t)
  : Lemma (requires cs.cs_fwd x <> 0UL /\ minor_infix_wf minor)
          (ensures (CheneySpec.cheney_forward_one minor cs addr).cs_fwd x <> 0UL)
  =
  if cs.cs_fwd addr <> 0UL then
    CheneySpec.cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    // Infix case: for y <> addr, result's fwd y = cs'.fwd y where cs' = forward_normal parent.
    // We know x <> addr (since cs.cs_fwd x <> 0 but cs.cs_fwd addr = 0).
    // By normal monotone on parent, cs'.cs_fwd x <> 0.
    // By infix_fwd lemma, result.cs_fwd x = cs'.cs_fwd x <> 0.
    let parent = infix_parent minor addr in
    cheney_forward_normal_fwd_monotone minor cs parent x;
    CheneySpec.cheney_forward_one_infix_fwd minor cs addr x
  end
  else begin
    CheneySpec.cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_fwd_monotone minor cs addr x
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
    assert (fuel > 0);
    CheneySpec.cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = CheneySpec.cheney_forward_fields minor cs obj 0 wz in
    forward_fields_fwd_monotone minor cs obj 0 wz x;
    scan_fwd_monotone minor cs' (scan + 1) (fuel - 1) x
  end

let scan_preserves_fwd_covers_roots
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (roots: seq U64.t) (scan fuel: nat)
  : Lemma (requires minor_infix_wf minor /\
                    fwd_covers_roots minor cs.cs_fwd roots)
          (ensures fwd_covers_roots minor
            (CheneySpec.cheney_scan minor cs scan fuel).cs_fwd roots)
  =
    let aux (r: U64.t) : Lemma
      (requires Seq.mem r roots /\
                Seq.mem r (minor_objects minor) /\
                minor_wosize minor r > 0)
      (ensures (CheneySpec.cheney_scan minor cs scan fuel).cs_fwd r <> 0UL)
    =
      assert (cs.cs_fwd r <> 0UL);
      scan_fwd_monotone minor cs scan fuel r
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let forward_one_queue_prefix
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) (k: nat)
  : Lemma (requires k < Seq.length cs.cs_queue)
          (ensures k < Seq.length (CheneySpec.cheney_forward_one minor cs addr).cs_queue /\
                   Seq.index (CheneySpec.cheney_forward_one minor cs addr).cs_queue k ==
                   Seq.index cs.cs_queue k)
  =
    if cs.cs_fwd addr <> 0UL then
      CheneySpec.cheney_forward_one_noop minor cs addr
    else if is_infix_in_minor minor addr then begin
      CheneySpec.cheney_forward_one_infix minor cs addr;
      let parent = infix_parent minor addr in
      let csn = CheneySpec.cheney_forward_normal minor cs parent in
      if not (Seq.mem parent (minor_objects minor)) || cs.cs_fwd parent <> 0UL then
        CheneySpec.cheney_forward_normal_noop minor cs parent
      else if minor_wosize minor parent = 0 then
        CheneySpec.cheney_forward_normal_noop_wz0 minor cs parent
      else begin
        let res = promote_object minor cs.cs_major parent cs.cs_fp (minor_wosize minor parent) in
        if res.new_addr = 0UL then
          CheneySpec.cheney_forward_normal_noop_oom minor cs parent
        else begin
          CheneySpec.cheney_forward_normal_success minor cs parent;
          Seq.Base.lemma_index_app1 cs.cs_queue (Seq.create 1 parent) k
        end
      end
    end else begin
      CheneySpec.cheney_forward_one_normal minor cs addr;
      if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
        CheneySpec.cheney_forward_normal_noop minor cs addr
      else if minor_wosize minor addr = 0 then
        CheneySpec.cheney_forward_normal_noop_wz0 minor cs addr
      else begin
        let res = promote_object minor cs.cs_major addr cs.cs_fp (minor_wosize minor addr) in
        if res.new_addr = 0UL then
          CheneySpec.cheney_forward_normal_noop_oom minor cs addr
        else begin
          CheneySpec.cheney_forward_normal_success minor cs addr;
          Seq.Base.lemma_index_app1 cs.cs_queue (Seq.create 1 addr) k
        end
      end
    end

let rec forward_fields_queue_prefix
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (k: nat)
  : Lemma (requires k < Seq.length cs.cs_queue)
          (ensures k < Seq.length (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_queue /\
                   Seq.index (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_queue k ==
                   Seq.index cs.cs_queue k)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
    if idx >= wosize then
      CheneySpec.cheney_forward_fields_base minor cs parent idx wosize
    else begin
      CheneySpec.cheney_forward_fields_step minor cs parent idx wosize;
      let child = to_minor_offset (minor_read_field minor parent idx) in
      let cs' = CheneySpec.cheney_forward_one minor cs child in
      forward_one_queue_prefix minor cs child k;
      assert (k < Seq.length cs'.cs_queue);
      forward_fields_queue_prefix minor cs' parent (idx + 1) wosize k
    end
#pop-options

[@@"opaque_to_smt"]
let addr_covered (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t) : prop =
  Seq.mem addr (minor_objects minor) /\ minor_wosize minor addr > 0 ==>
  cs.cs_fwd addr <> 0UL

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let addr_covered_intro
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires (Seq.mem addr (minor_objects minor) /\
                     minor_wosize minor addr > 0 ==> cs.cs_fwd addr <> 0UL))
          (ensures addr_covered minor cs addr)
  = reveal_opaque (`%addr_covered) (addr_covered minor cs addr)

let addr_covered_elim
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires addr_covered minor cs addr /\
                    Seq.mem addr (minor_objects minor) /\ minor_wosize minor addr > 0)
          (ensures cs.cs_fwd addr <> 0UL)
  = reveal_opaque (`%addr_covered) (addr_covered minor cs addr)

let forward_one_preserves_addr_covered
  (minor: minor_state) (cs: CheneySpec.cheney_state) (step_addr x: U64.t)
  : Lemma (requires minor_infix_wf minor /\ addr_covered minor cs x)
          (ensures addr_covered minor (CheneySpec.cheney_forward_one minor cs step_addr) x)
  =
    reveal_opaque (`%addr_covered) (addr_covered minor cs x);
    reveal_opaque (`%addr_covered)
      (addr_covered minor (CheneySpec.cheney_forward_one minor cs step_addr) x);
    if Seq.mem x (minor_objects minor) && minor_wosize minor x > 0 then
      forward_one_fwd_monotone minor cs step_addr x
#pop-options

[@@"opaque_to_smt"]
let root_prefix_covered
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat) : prop =
  forall (j:nat). j < idx /\ j < Seq.length roots ==> addr_covered minor cs (Seq.index roots j)

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let root_prefix_empty (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t)
  : Lemma (ensures root_prefix_covered minor cs roots 0)
  = reveal_opaque (`%root_prefix_covered) (root_prefix_covered minor cs roots 0)

let root_prefix_step
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires idx < Seq.length roots /\
                    minor_infix_wf minor /\
                    root_prefix_covered minor cs roots idx /\
                    addr_covered minor (CheneySpec.cheney_forward_one minor cs (Seq.index roots idx))
                      (Seq.index roots idx))
          (ensures root_prefix_covered minor
                    (CheneySpec.cheney_forward_one minor cs (Seq.index roots idx))
                    roots (idx + 1))
  =
    let r = Seq.index roots idx in
    let cs' = CheneySpec.cheney_forward_one minor cs r in
    reveal_opaque (`%root_prefix_covered) (root_prefix_covered minor cs roots idx);
    reveal_opaque (`%root_prefix_covered) (root_prefix_covered minor cs' roots (idx + 1));
    let aux (j:nat{j < idx + 1 /\ j < Seq.length roots})
      : Lemma (addr_covered minor cs' (Seq.index roots j))
      =
        if j = idx then ()
        else begin
          assert (j < idx);
          forward_one_preserves_addr_covered minor cs r (Seq.index roots j)
        end
    in
    FStar.Classical.forall_intro aux

let root_prefix_step_oom
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
  =
    if not oom_after then begin
      assert (not oom_before);
      root_prefix_step minor cs roots idx
    end

let root_prefix_all_implies_covers
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t)
  : Lemma (requires root_prefix_covered minor cs roots (Seq.length roots))
          (ensures fwd_covers_roots minor cs.cs_fwd roots)
  =
    reveal_opaque (`%root_prefix_covered)
      (root_prefix_covered minor cs roots (Seq.length roots));
    let aux (r:U64.t)
      : Lemma (requires Seq.mem r roots /\ Seq.mem r (minor_objects minor) /\ minor_wosize minor r > 0)
              (ensures cs.cs_fwd r <> 0UL)
      =
        let j = Seq.index_mem r roots in
        assert (j < Seq.length roots);
        assert (Seq.index roots j == r);
        addr_covered_elim minor cs r
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let root_prefix_all_implies_covers_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (oom: bool)
  : Lemma (requires (not oom ==> root_prefix_covered minor cs roots (Seq.length roots)))
          (ensures not oom ==> fwd_covers_roots minor cs.cs_fwd roots)
  =
    if not oom then root_prefix_all_implies_covers minor cs roots
#pop-options

[@@"opaque_to_smt"]
let field_prefix_covered
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat) : prop =
  forall (j:nat). j < idx ==> addr_covered minor cs (to_minor_offset (minor_read_field minor parent j))

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let field_prefix_empty (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t)
  : Lemma (ensures field_prefix_covered minor cs parent 0)
  = reveal_opaque (`%field_prefix_covered) (field_prefix_covered minor cs parent 0)

let field_prefix_step
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
  =
    let child = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = CheneySpec.cheney_forward_one minor cs child in
    reveal_opaque (`%field_prefix_covered) (field_prefix_covered minor cs parent idx);
    reveal_opaque (`%field_prefix_covered) (field_prefix_covered minor cs' parent (idx + 1));
    let aux (j:nat{j < idx + 1}) : Lemma (addr_covered minor cs' (to_minor_offset (minor_read_field minor parent j)))
      =
        if j = idx then ()
        else begin
          assert (j < idx);
          forward_one_preserves_addr_covered minor cs child (to_minor_offset (minor_read_field minor parent j))
        end
    in
    FStar.Classical.forall_intro aux

let field_prefix_step_oom
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
  =
    if not oom_after then begin
      assert (not oom_before);
      field_prefix_step minor cs parent idx
    end

let field_prefix_all_implies_successors
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t)
  : Lemma (requires field_prefix_covered minor cs parent (minor_wosize minor parent))
          (ensures forall (y: U64.t).
            Seq.mem y (minor_successors minor parent) /\
            minor_wosize minor y > 0 ==> cs.cs_fwd y <> 0UL)
  =
    reveal_opaque (`%field_prefix_covered)
      (field_prefix_covered minor cs parent (minor_wosize minor parent));
    let aux (y: U64.t) : Lemma
      (requires Seq.mem y (minor_successors minor parent) /\ minor_wosize minor y > 0)
      (ensures cs.cs_fwd y <> 0UL)
    =
      minor_successors_char minor parent y;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun j -> j < minor_wosize minor parent /\
                  to_minor_offset (minor_read_field minor parent j) == y /\
                  is_minor_addr y /\ Seq.mem y (minor_objects minor)) in
      assert (j < minor_wosize minor parent);
      assert (to_minor_offset (minor_read_field minor parent j) == y);
      addr_covered_elim minor cs y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

[@@"opaque_to_smt"]
let scanned_prefix_closed
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) : prop =
  forall (k:nat) (y:U64.t).
    k < scan /\ k < Seq.length cs.cs_queue /\
    Seq.mem y (minor_successors minor (Seq.index cs.cs_queue k)) /\
    minor_wosize minor y > 0 ==> cs.cs_fwd y <> 0UL

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let scanned_prefix_empty
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (ensures scanned_prefix_closed minor cs 0)
  = reveal_opaque (`%scanned_prefix_closed) (scanned_prefix_closed minor cs 0)

let scanned_prefix_step
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
  =
    let parent = Seq.index cs.cs_queue scan in
    reveal_opaque (`%scanned_prefix_closed) (scanned_prefix_closed minor cs scan);
    reveal_opaque (`%scanned_prefix_closed) (scanned_prefix_closed minor cs' (scan + 1));
    let aux (k:nat) (y:U64.t) : Lemma
      (requires k < scan + 1 /\ k < Seq.length cs'.cs_queue /\
                Seq.mem y (minor_successors minor (Seq.index cs'.cs_queue k)) /\
                minor_wosize minor y > 0)
      (ensures cs'.cs_fwd y <> 0UL)
    =
      if k = scan then begin
        forward_fields_queue_prefix minor cs parent 0 (minor_wosize minor parent) scan;
        assert (Seq.index cs'.cs_queue k == parent);
        field_prefix_all_implies_successors minor cs' parent
      end else begin
        assert (k < scan);
        assert (k < Seq.length cs.cs_queue);
        forward_fields_queue_prefix minor cs parent 0 (minor_wosize minor parent) k;
        assert (Seq.index cs'.cs_queue k == Seq.index cs.cs_queue k);
        assert (cs.cs_fwd y <> 0UL);
        forward_fields_fwd_monotone minor cs parent 0 (minor_wosize minor parent) y
      end
    in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

let scanned_prefix_step_oom
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
  =
    if not oom_after then begin
      assert (not oom_before);
      scanned_prefix_step minor cs cs' scan
    end

let scanned_exhausted_implies_fwd_closed
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat)
  : Lemma (requires SimOne.cheney_bfs_inv minor cs /\
                    scanned_prefix_closed minor cs scan /\
                    scan >= Seq.length cs.cs_queue)
          (ensures fwd_closed minor cs.cs_fwd)
  =
    SimOne.cheney_bfs_inv_fwd_in_queue minor cs;
    reveal_opaque (`%scanned_prefix_closed) (scanned_prefix_closed minor cs scan);
    let aux (x y: U64.t) : Lemma
      (requires Seq.mem x (minor_objects minor) /\
                cs.cs_fwd x <> 0UL /\
                Seq.mem y (minor_successors minor x) /\
                minor_wosize minor y > 0)
      (ensures cs.cs_fwd y <> 0UL)
    =
      assert (Seq.mem x cs.cs_queue);
      let k = Seq.index_mem x cs.cs_queue in
      assert (k < Seq.length cs.cs_queue);
      assert (k < scan);
      assert (Seq.index cs.cs_queue k == x);
      assert (Seq.mem y (minor_successors minor (Seq.index cs.cs_queue k)));
      assert (cs.cs_fwd y <> 0UL)
    in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

let scanned_exhausted_implies_fwd_closed_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (oom: bool)
  : Lemma (requires SimOne.cheney_bfs_inv minor cs /\
                    (not oom ==> scanned_prefix_closed minor cs scan) /\
                    scan >= Seq.length cs.cs_queue)
          (ensures not oom ==> fwd_closed minor cs.cs_fwd)
  =
    if not oom then scanned_exhausted_implies_fwd_closed minor cs scan
#pop-options

/// ---------------------------------------------------------------------------
/// Main theorem: BFS completeness under no-OOM
/// ---------------------------------------------------------------------------

let cheney_no_oom_from_loop_posts
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
  =
    if not oom_final then begin
      let cs0 : CheneySpec.cheney_state =
        { CheneySpec.cs_major = major; CheneySpec.cs_fp = fp;
          CheneySpec.cs_fwd = empty_forwarding; CheneySpec.cs_queue = Seq.empty } in
      let cs1 = CheneySpec.cheney_forward_roots minor cs0 roots 0 in
      let cs2 = CheneySpec.cheney_scan minor cs1 0 (CheneySpec.cheney_fuel minor) in
      assert (not oom_roots);
      scan_preserves_fwd_covers_roots minor cs1 roots 0 (CheneySpec.cheney_fuel minor);
      assert (fwd_well_formed minor cs2.CheneySpec.cs_fwd roots);
      assert (cheney_no_oom minor major fp roots)
    end

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
