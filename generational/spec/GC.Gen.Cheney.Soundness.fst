module GC.Gen.Cheney.Soundness

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney
open GC.Gen.Reachability

module CG = GC.Gen.CheneyGeneric
module GenInv = GC.Gen.HeapInvariant
module CI = GC.Gen.Cheney.Induction
module CS = GC.Gen.Cheney.Steps
module Fwd = GC.Gen.CheneyPreservation.Forwarding
module Inj = GC.Gen.CheneyPreservation.Injectivity

/// ---------------------------------------------------------------------------
/// Soundness: the invariant
/// ---------------------------------------------------------------------------
///
/// Every forwarded address resolves into `r`, and every queued object is in
/// `r`.  A step forwards an address that resolves into `r` whenever it
/// resolves to a nursery object at all (`addr_ok`): a root does, for `r`
/// the reachable set; so does a field of a queued object.

let sound (minor: minor_state) (r: seq U64.t) (cs: cheney_state) : prop =
  (forall (x: U64.t). cs.cs_fwd x <> 0UL ==> Seq.mem (resolve_minor minor x) r) /\
  (forall (j: nat). j < Seq.length cs.cs_queue ==> Seq.mem (Seq.index cs.cs_queue j) r)

let addr_ok (minor: minor_state) (r: seq U64.t) (addr: U64.t) : prop =
  Seq.mem (resolve_minor minor addr) (minor_objects minor) ==>
  Seq.mem (resolve_minor minor addr) r

/// A nursery object is not an interior pointer, so it resolves to itself.
let minor_object_resolves (minor: minor_state) (o: U64.t)
  : Lemma (requires minor_wf minor /\ Seq.mem o (minor_objects minor))
          (ensures ~(is_infix_in_minor minor o) /\ resolve_minor minor o == o)
  = minor_objects_not_infix minor o;
    resolve_minor_non_infix minor o

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let forward_normal_sound (minor: minor_state) (r: seq U64.t) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires minor_wf minor /\ sound minor r cs /\
                    (Seq.mem addr (minor_objects minor) ==> Seq.mem addr r))
          (ensures sound minor r (cheney_forward_normal minor cs addr))
  = if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
    then cheney_forward_normal_noop minor cs addr
    else if minor_wosize minor addr = 0
    then cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz cs.cs_phase in
      if res.new_addr = 0UL
      then cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        minor_object_resolves minor addr;
        let cs' = cheney_forward_normal minor cs addr in
        let q1 = Seq.create 1 addr in
        let q = Seq.append cs.cs_queue q1 in
        assert (cs'.cs_queue == q);
        let aux (j: nat) : Lemma (j < Seq.length q ==> Seq.mem (Seq.index q j) r)
          = Seq.lemma_len_append cs.cs_queue q1;
            if j >= Seq.length q then ()
            else if j < Seq.length cs.cs_queue
            then assert (Seq.index q j == Seq.index cs.cs_queue j)
            else assert (Seq.index q j == Seq.index q1 (j - Seq.length cs.cs_queue))
        in
        FStar.Classical.forall_intro aux
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let forward_one_sound (minor: minor_state) (r: seq U64.t) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires minor_wf minor /\ minor_infix_wf minor /\ sound minor r cs /\ addr_ok minor r addr)
          (ensures sound minor r (cheney_forward_one minor cs addr))
  = if cs.cs_fwd addr <> 0UL then cheney_forward_one_noop minor cs addr
    else if is_infix_in_minor minor addr then begin
      let parent = infix_parent minor addr in
      infix_parent_in_minor_objects minor addr;
      assert (resolve_minor minor addr == parent);
      forward_normal_sound minor r cs parent;
      let cs' = cheney_forward_normal minor cs parent in
      if cs'.cs_fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then cheney_forward_one_infix_guard_pass minor cs addr
      else cheney_forward_one_infix_guard_fail minor cs addr
    end
    else begin
      cheney_forward_one_normal minor cs addr;
      resolve_minor_non_infix minor addr;
      forward_normal_sound minor r cs addr
    end
#pop-options

/// The roots: each resolves into the reachable set.
let rec forward_roots_sound (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires minor_wf minor /\ minor_infix_wf minor /\
                    sound minor (minor_reachable minor roots) cs)
          (ensures sound minor (minor_reachable minor roots) (cheney_forward_roots minor cs roots idx))
          (decreases (Seq.length roots - idx))
  = let r = minor_reachable minor roots in
    if idx >= Seq.length roots then cheney_forward_roots_base minor cs roots idx
    else begin
      cheney_forward_roots_step minor cs roots idx;
      let a = Seq.index roots idx in
      minor_reachable_roots minor roots;
      assert (Seq.mem a roots);
      assert (addr_ok minor r a);
      forward_one_sound minor r cs a;
      forward_roots_sound minor (cheney_forward_one minor cs a) roots (idx + 1)
    end

/// A field of an object of `r` resolves into `r`, when `r` is the reachable set.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let field_addr_ok (minor: minor_state) (roots: seq U64.t) (parent: U64.t) (i: nat)
  : Lemma (requires Seq.mem parent (minor_reachable minor roots) /\ i < minor_scan_wosize minor parent)
          (ensures addr_ok minor (minor_reachable minor roots)
                     (to_minor_offset (minor_read_field minor parent i)))
  = let a = to_minor_offset (minor_read_field minor parent i) in
    let y = resolve_minor minor a in
    if Seq.mem y (minor_objects minor) then begin
      minor_objects_valid minor y;
      is_minor_addr_from_bounds y;
      minor_successors_char minor parent y;
      minor_reachable_closed minor roots parent y
    end
#pop-options

let rec forward_fields_sound (minor: minor_state) (roots: seq U64.t) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires minor_wf minor /\ minor_infix_wf minor /\
                    sound minor (minor_reachable minor roots) cs /\
                    Seq.mem parent (minor_reachable minor roots) /\
                    wosize <= minor_scan_wosize minor parent)
          (ensures sound minor (minor_reachable minor roots)
                     (cheney_forward_fields minor cs parent idx wosize))
          (decreases (wosize - idx))
  = if idx >= wosize then cheney_forward_fields_base minor cs parent idx wosize
    else begin
      cheney_forward_fields_step minor cs parent idx wosize;
      let a = to_minor_offset (minor_read_field minor parent idx) in
      field_addr_ok minor roots parent idx;
      forward_one_sound minor (minor_reachable minor roots) cs a;
      forward_fields_sound minor roots (cheney_forward_one minor cs a) parent (idx + 1) wosize
    end

let rec scan_sound (minor: minor_state) (roots: seq U64.t) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires minor_wf minor /\ minor_infix_wf minor /\
                    sound minor (minor_reachable minor roots) cs)
          (ensures sound minor (minor_reachable minor roots) (cheney_scan minor cs scan fuel))
          (decreases fuel)
  = if fuel = 0 || scan >= Seq.length cs.cs_queue then cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_scan_wosize minor obj in
      forward_fields_sound minor roots cs obj 0 wz;
      scan_sound minor roots (cheney_forward_fields minor cs obj 0 wz) (scan + 1) (fuel - 1)
    end

let cheney_promote_fwd_sound ph minor major fp roots x =
  let r = minor_reachable minor roots in
  let cs0 = CI.cheney_init ph major fp in
  assert (sound minor r cs0);
  forward_roots_sound minor cs0 roots 0;
  scan_sound minor roots (cheney_forward_roots minor cs0 roots 0) 0 (cheney_fuel minor)

let cheney_collect_fwd_sound ph free minor major fp roots x =
  cheney_promote_fwd_sound ph minor major fp roots x

let cheney_collect_forwarded_reachable ph free minor major fp roots o =
  cheney_promote_fwd_sound ph minor major fp roots o;
  minor_object_resolves minor o

let promote_pre_of_shape ph free minor major fp =
  GenInv.collection_shape_with_elim ph free minor major fp;
  GenInv.major_shape_with_elim ph free major fp;
  GenInv.minor_heap_shape_elim minor

/// ---------------------------------------------------------------------------
/// Where the forwarding map points
/// ---------------------------------------------------------------------------

/// The facts about the end of the run that the two proofs below use.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let run_facts (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires CG.promote_pre minor major fp)
          (ensures (let prom = cheney_promote ph minor major fp roots in
                    let g = prom.major_final in
                    let fwd = prom.fwd_map in
                    blocks_fit g /\ no_infix_block g /\
                    fwd_bounded fwd /\
                    Fwd.fwd_noninfix_targets_valid minor fwd g /\
                    Fwd.fwd_infix_targets_wf minor fwd g /\
                    Fwd.fwd_infix_delta minor fwd /\
                    Inj.fwd_normal_injective fwd g /\
                    Inj.fwd_normal_targets_disjoint_from_old_nonblue fwd g major))
  = CS.cheney_promote_preserves_wfh_part1 ph minor major fp roots;
    CS.cheney_promote_preserves_wfh_part4 ph minor major fp roots;
    CS.cheney_promote_fwd_bounded ph minor major fp roots;
    Fwd.cheney_promote_fwd_noninfix_targets_valid ph minor major fp roots;
    Fwd.cheney_promote_fwd_infix_targets_wf ph minor major fp roots;
    Fwd.cheney_promote_fwd_infix_delta ph minor major fp roots;
    Inj.cheney_promote_fwd_normal_injective ph minor major fp roots;
    Inj.cheney_promote_fwd_normal_targets_disjoint_from_old_nonblue ph minor major fp roots
#pop-options

/// The target of a forwarded address that is not an interior pointer is a
/// block of the promoted heap, so not an infix one.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let noninfix_target (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t)
  : Lemma (requires CG.promote_pre minor major fp /\
                    (cheney_promote ph minor major fp roots).fwd_map x <> 0UL /\
                    ~(is_infix_in_minor minor x))
          (ensures (let prom = cheney_promote ph minor major fp roots in
                    let t = prom.fwd_map x in
                    is_val_addr t /\
                    Seq.mem (t <: obj_addr) (objects zero_addr prom.major_final) /\
                    is_infix (t <: obj_addr) prom.major_final = false))
  = run_facts ph minor major fp roots
#pop-options

/// ---------------------------------------------------------------------------
/// The new blocks are the forwarding targets
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_collect_new_blocks ph free un minor major fp roots x =
  let res = cheney_collect_spec_with ph free minor major fp roots in
  let prom = cheney_promote ph minor major fp roots in
  let pm = prom.major_final in
  let fwd = prom.fwd_map in
  run_facts ph minor major fp roots;
  assert (res.mc_major == update_walk pm (in_use free pm) fwd);
  assert (res.mc_fwd == fwd);
  CG.update_walk_keeps_in_use un pm (in_use free pm) fwd x;
  // a new block is a promoted copy
  FStar.Classical.move_requires (CG.cheney_promote_in_use_origin ph un minor major fp roots) x;
  // a promoted copy is a new block
  let back (o: U64.t)
    : Lemma (requires Seq.mem o (minor_objects minor) /\ fwd o == x)
            (ensures in_use un res.mc_major x /\ ~(in_use un major x))
    = CG.cheney_promote_image_not_free ph un minor major fp roots o x;
      minor_object_resolves minor o;
      noninfix_target ph minor major fp roots o;
      if in_use un major x then in_use_not_blue un major x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires back)
#pop-options

let cheney_collect_new_blocks_stw ph free minor major fp roots x =
  free_stw_ok ();
  free_stw_allocations_not_free ph;
  cheney_collect_new_blocks ph free free_stw minor major fp roots x

/// ---------------------------------------------------------------------------
/// The forwarding map is injective
/// ---------------------------------------------------------------------------

/// Two forwarded addresses that are not interior pointers.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let injective_normal (ph: gc_phase) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x y: U64.t)
  : Lemma (requires CG.promote_pre minor major fp /\
                    (let fwd = (cheney_promote ph minor major fp roots).fwd_map in
                     fwd x <> 0UL /\ fwd x == fwd y) /\
                    ~(is_infix_in_minor minor x) /\ ~(is_infix_in_minor minor y))
          (ensures x == y)
  = run_facts ph minor major fp roots;
    noninfix_target ph minor major fp roots x;
    noninfix_target ph minor major fp roots y
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cheney_promote_fwd_injective ph minor major fp roots x y =
  let prom = cheney_promote ph minor major fp roots in
  let fwd = prom.fwd_map in
  run_facts ph minor major fp roots;
  match is_infix_in_minor minor x, is_infix_in_minor minor y with
  | false, false -> injective_normal ph minor major fp roots x y
  | true, false -> noninfix_target ph minor major fp roots y
  | false, true -> noninfix_target ph minor major fp roots x
  | true, true ->
    let px = infix_parent minor x in
    let py = infix_parent minor y in
    infix_parent_in_minor_objects minor x;
    infix_parent_in_minor_objects minor y;
    minor_object_resolves minor px;
    minor_object_resolves minor py;
    assert (fwd px <> 0UL /\ fwd py <> 0UL);
    assert (fwd px == fwd py);
    injective_normal ph minor major fp roots px py;
    assert (U64.v (fwd x) == U64.v (fwd px) + (U64.v x - U64.v px));
    assert (U64.v (fwd y) == U64.v (fwd px) + (U64.v y - U64.v px));
    assert (U64.v x == U64.v y)
#pop-options

let cheney_collect_fwd_injective ph free minor major fp roots x y =
  cheney_promote_fwd_injective ph minor major fp roots x y
