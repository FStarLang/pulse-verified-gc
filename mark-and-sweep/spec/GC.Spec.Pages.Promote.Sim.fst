/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Sim - implementation
/// ---------------------------------------------------------------------------

module GC.Spec.Pages.Promote.Sim

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.ForwardingArray
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Promote

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag
module Inc = GC.Spec.Pages.Incr
module L = GC.Spec.Pages.Promote.Loop
module MS = GC.Spec.Pages.MidSweep
module PI = GC.Spec.Pages.PromoteInst
module PId = GC.Spec.Pages.Promote.Idle
module CSim = GC.Gen.Cheney.Sim

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator of a phase
/// ---------------------------------------------------------------------------

let at_phase (a: tal pstate) (ph: I.phase) : prop =
  contract a /\
  (forall (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t). a.alloc g st wz tag == AT.alloc_tag ph g st wz tag) /\
  (forall (g: heap) (st: pstate). a.inv g st ==> Inc.phase_inv ph g st)

let at_phase_alloc a ph g st wz tag = ()
let at_phase_inv a ph g st = ()
let at_phase_contract a ph = ()

/// An allocation from the invariant: nothing, or a block with room.
let alloc_room (a: tal pstate) (g: heap) (st: pstate) (wz: pos) (tag: AT.tag_t)
  : Lemma (requires contract a /\ a.inv g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = a.alloc g st wz tag in
                    (o == 0UL ==> g' == g /\ st' == st) /\
                    (o <> 0UL ==> U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                                  U64.v o + wz * 8 <= heap_size)))
  = contract_alloc a g st wz tag


#push-options "--ifuel 1"
let mark_at () = PI.mark_contract ()

let sw_at (pm0: page_map) = PI.sw_contract pm0

let idle_at () = PId.idle_contract ()
#pop-options

/// ---------------------------------------------------------------------------
/// The queue (akhil's `Cheney.SimOne`, over our state)
/// ---------------------------------------------------------------------------

/// The nursery objects not yet forwarded, from index `i`.
let rec count_unfwd (objs: seq U64.t) (fwd: forwarding_map) (i: nat)
  : GTot nat (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then 0
    else (if fwd (Seq.index objs i) = 0UL then 1 else 0) + count_unfwd objs fwd (i + 1)

#push-options "--fuel 1"
let rec count_empty (objs: seq U64.t) (i: nat)
  : Lemma (ensures count_unfwd objs empty_forwarding i == (if i < Seq.length objs then Seq.length objs - i else 0))
          (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then () else count_empty objs (i + 1)

let rec count_monotone (objs: seq U64.t) (fwd: forwarding_map) (addr v: U64.t) (i: nat)
  : Lemma (requires v <> 0UL)
          (ensures count_unfwd objs (extend_forwarding fwd addr v) i <= count_unfwd objs fwd i)
          (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then () else count_monotone objs fwd addr v (i + 1)

let rec count_decrease (objs: seq U64.t) (fwd: forwarding_map) (addr v: U64.t) (i k: nat)
  : Lemma (requires v <> 0UL /\ fwd addr == 0UL /\ i <= k /\ k < Seq.length objs /\ Seq.index objs k == addr)
          (ensures count_unfwd objs (extend_forwarding fwd addr v) i + 1 <= count_unfwd objs fwd i)
          (decreases (k - i))
  = if Seq.index objs i = addr then count_monotone objs fwd addr v (i + 1)
    else count_decrease objs fwd addr v (i + 1) k

let rec count_ext (objs: seq U64.t) (fwd1 fwd2: forwarding_map) (i: nat)
  : Lemma (requires forall (k: nat). k < Seq.length objs ==> fwd1 (Seq.index objs k) == fwd2 (Seq.index objs k))
          (ensures count_unfwd objs fwd1 i == count_unfwd objs fwd2 i)
          (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then () else count_ext objs fwd1 fwd2 (i + 1)

let rec count_positive (objs: seq U64.t) (fwd: forwarding_map) (i k: nat)
  : Lemma (requires i <= k /\ k < Seq.length objs /\ fwd (Seq.index objs k) == 0UL)
          (ensures count_unfwd objs fwd i >= 1)
          (decreases (k - i))
  = if fwd (Seq.index objs i) = 0UL then () else count_positive objs fwd (i + 1) k
#pop-options

/// The queue: nursery objects, forwarded; every forwarded nursery object is
/// in it; and it is no longer than the nursery objects not counted as
/// unforwarded.
let qinv (minor: minor_state) (cs: gstate pstate) : prop =
  (forall (j: nat). j < Seq.length cs.queue ==>
     Seq.mem (Seq.index cs.queue j) (minor_objects minor) /\ cs.fwd (Seq.index cs.queue j) <> 0UL) /\
  (forall (x: U64.t). Seq.mem x (minor_objects minor) /\ cs.fwd x <> 0UL ==> Seq.mem x cs.queue) /\
  Seq.length cs.queue + count_unfwd (minor_objects minor) cs.fwd 0 <= Seq.length (minor_objects minor)

[@@"opaque_to_smt"]
let sim (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) : prop =
  L.ctx a minor g0 /\ L.linv a minor g0 cs /\ qinv minor cs /\ fwd_injective minor cs.fwd

let sim_eq (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
  : Lemma (sim a minor g0 cs <==>
           (L.ctx a minor g0 /\ L.linv a minor g0 cs /\ qinv minor cs /\ fwd_injective minor cs.fwd))
  = reveal_opaque (`%sim) (sim a minor g0 cs)

/// A nursery object is not infix.
let mem_not_infix (minor: minor_state) (x: U64.t)
  : Lemma (requires minor_wf minor /\ Seq.mem x (minor_objects minor))
          (ensures ~(is_infix_in_minor minor x))
  = minor_objects_not_infix minor x

#push-options "--z3rlimit 30"
let sim_init a minor g0 st0
  = sim_eq a minor g0 (init g0 st0);
    contract_wf a g0 st0;
    let cs = init g0 st0 in
    assert (L.olds a g0 g0);
    assert (L.linv a minor g0 cs);
    count_empty (minor_objects minor) 0
#pop-options

let sim_facts a minor g0 cs = sim_eq a minor g0 cs; minor_objects_count_bound minor

let sim_queue a minor g0 cs j = sim_eq a minor g0 cs

#push-options "--z3rlimit 30"
let sim_room a minor g0 cs x
  = sim_eq a minor g0 cs;
    mem_not_infix minor x;
    assert (L.entry a minor g0 cs.major cs.fwd x);
    assert (L.copy_of a minor g0 cs.major x (cs.fwd x))
#pop-options

let sim_strict_room a minor g0 cs x
  = sim_eq a minor g0 cs;
    let k = Seq.index_mem x (minor_objects minor) in
    count_positive (minor_objects minor) cs.fwd 0 k

/// ---------------------------------------------------------------------------
/// The step keeps the queue's facts and injectivity
/// ---------------------------------------------------------------------------

/// The state after a successful promotion of `addr` to `o`.
let pushed (cs: gstate pstate) (g': heap) (st': pstate) (addr o: U64.t) : gstate pstate =
  { major = g'; st = st'; fwd = extend_forwarding cs.fwd addr o; queue = Seq.append cs.queue (Seq.create 1 addr) }

#push-options "--z3rlimit 40"
let qinv_pushed (minor: minor_state) (cs: gstate pstate) (g': heap) (st': pstate) (addr o: U64.t)
  : Lemma (requires qinv minor cs /\ Seq.mem addr (minor_objects minor) /\ cs.fwd addr == 0UL /\ o <> 0UL)
          (ensures qinv minor (pushed cs g' st' addr o))
  = let cs' = pushed cs g' st' addr o in
    let q1 = Seq.create 1 addr in
    Seq.lemma_len_append cs.queue q1;
    let qj (j: nat{j < Seq.length cs'.queue})
      : Lemma (Seq.mem (Seq.index cs'.queue j) (minor_objects minor) /\ cs'.fwd (Seq.index cs'.queue j) <> 0UL)
      = if j < Seq.length cs.queue then Seq.lemma_index_app1 cs.queue q1 j
        else Seq.lemma_index_app2 cs.queue q1 j
    in
    FStar.Classical.forall_intro qj;
    let cm (x: U64.t)
      : Lemma (requires Seq.mem x (minor_objects minor) /\ cs'.fwd x <> 0UL) (ensures Seq.mem x cs'.queue)
      = Seq.lemma_mem_snoc cs.queue addr
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires cm);
    let k = Seq.index_mem addr (minor_objects minor) in
    count_decrease (minor_objects minor) cs.fwd addr o 0 k
#pop-options

/// An infix address forwarded: no nursery object is touched.
#push-options "--z3rlimit 30"
let qinv_infix (minor: minor_state) (cs: gstate pstate) (addr v: U64.t)
  : Lemma (requires minor_wf minor /\ qinv minor cs /\ is_infix_in_minor minor addr)
          (ensures qinv minor ({ cs with fwd = extend_forwarding cs.fwd addr v }))
  = let cs' = { cs with fwd = extend_forwarding cs.fwd addr v } in
    let ne (x: U64.t) : Lemma (requires Seq.mem x (minor_objects minor)) (ensures cs'.fwd x == cs.fwd x)
      = mem_not_infix minor x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ne);
    let ek (k: nat) : Lemma (k < Seq.length (minor_objects minor) ==>
                              cs'.fwd (Seq.index (minor_objects minor) k) == cs.fwd (Seq.index (minor_objects minor) k))
      = if k < Seq.length (minor_objects minor) then ne (Seq.index (minor_objects minor) k)
    in
    FStar.Classical.forall_intro ek;
    count_ext (minor_objects minor) cs'.fwd cs.fwd 0
#pop-options

let inj_infix (minor: minor_state) (fwd: forwarding_map) (addr v: U64.t)
  : Lemma (requires fwd_injective minor fwd /\ is_infix_in_minor minor addr)
          (ensures fwd_injective minor (extend_forwarding fwd addr v))
  = ()

/// A new copy is a block not in use before, and every copy is in use.
#push-options "--z3rlimit 40"
let inj_pushed (a: tal pstate) (minor: minor_state) (g0 g: heap) (fwd: forwarding_map) (addr: U64.t) (o: obj_addr)
  : Lemma (requires minor_wf minor /\ fwd_injective minor fwd /\ L.entries a minor g0 g fwd /\
                    ~(in_use a.free g o) /\ Seq.mem addr (minor_objects minor))
          (ensures fwd_injective minor (extend_forwarding fwd addr (o <: U64.t)))
  = mem_not_infix minor addr;
    let ne (m: U64.t)
      : Lemma (requires fwd m <> 0UL /\ ~(is_infix_in_minor minor m)) (ensures fwd m <> (o <: U64.t))
      = assert (L.entry a minor g0 g fwd m);
        assert (L.copy_of a minor g0 g m (fwd m))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ne)
#pop-options

/// `forward_normal` keeps the invariant.
#push-options "--z3rlimit 40"
let sim_forward_normal (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (addr: U64.t)
  : Lemma (requires sim a minor g0 cs)
          (ensures sim a minor g0 (forward_normal a minor cs addr) /\
                   (forall (m: U64.t). m <> addr ==> (forward_normal a minor cs addr).fwd m == cs.fwd m))
  = sim_eq a minor g0 cs;
    sim_eq a minor g0 (forward_normal a minor cs addr);
    L.forward_normal_keeps a minor g0 cs addr;
    if not (Seq.mem addr (minor_objects minor)) || cs.fwd addr <> 0UL then ()
    else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then ()
      else begin
        L.promote_step a minor g0 cs.major cs.st addr;
        let (g2, s2, o) = promote_object a minor cs.major addr cs.st wz in
        if o = 0UL then ()
        else begin
          qinv_pushed minor cs g2 s2 addr o;
          inj_pushed a minor g0 cs.major cs.fwd addr o
        end
      end
    end
#pop-options

#push-options "--z3rlimit 40"
let sim_forward_one a minor g0 cs addr
  = sim_eq a minor g0 cs;
    sim_eq a minor g0 (forward_one a minor cs addr);
    L.forward_one_keeps a minor g0 cs addr;
    if cs.fwd addr <> 0UL then ()
    else if is_infix_in_minor minor addr then begin
      let parent = infix_parent minor addr in
      L.parent_facts minor addr;
      sim_forward_normal a minor g0 cs parent;
      let cs' = forward_normal a minor cs parent in
      sim_eq a minor g0 cs';
      if cs'.fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (cs'.fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then begin
        let v = U64.uint_to_t (U64.v (cs'.fwd parent) + (U64.v addr - U64.v parent)) in
        qinv_infix minor cs' addr v;
        inj_infix minor cs'.fwd addr v
      end
    end
    else sim_forward_normal a minor g0 cs addr
#pop-options

/// ---------------------------------------------------------------------------
/// The Pulse state and the model state
/// ---------------------------------------------------------------------------

let matches_core (cs: gstate pstate) (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat) : prop =
  g == cs.major /\ st == cs.st /\ represents_fwd farr cs.fwd /\
  (forall (j: nat). j < bk /\ j < Seq.length q /\ j < Seq.length cs.queue ==> Seq.index q j == Seq.index cs.queue j)

let matches_elim cs g st farr q bk = ()

let matches_init g st farr q = CSim.represents_fwd_initial farr

let matches_fwd cs g st farr q bk addr = CSim.represents_fwd_read farr cs.fwd addr

let matches_queue cs g st farr q bk j = ()

/// The queue after a push.
let matches_push (cs: gstate pstate) (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat)
                 (g': heap) (st': pstate) (addr o: U64.t)
  : Lemma (requires matches cs g st farr q bk /\ bk < queue_size /\
                    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0)
          (ensures U64.v addr / 8 < fwd_array_size /\
                   matches (pushed cs g' st' addr o) g' st' (Seq.upd farr (U64.v addr / 8) o) (Seq.upd q bk addr) (bk + 1))
  = CSim.represents_fwd_update farr cs.fwd addr o;
    CSim.queue_update_correspondence q cs.queue bk addr;
    Seq.lemma_len_append cs.queue (Seq.create 1 addr)

/// The forwarding of an infix address.
let matches_set (cs: gstate pstate) (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat) (addr v: U64.t)
  : Lemma (requires matches cs g st farr q bk /\
                    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0)
          (ensures U64.v addr / 8 < fwd_array_size /\
                   matches ({ cs with fwd = extend_forwarding cs.fwd addr v }) g st (Seq.upd farr (U64.v addr / 8) v) q bk)
  = CSim.represents_fwd_update farr cs.fwd addr v

/// ---------------------------------------------------------------------------
/// The forwarding step, branch by branch
/// ---------------------------------------------------------------------------

let step_skip a minor cs addr = ()

#push-options "--z3rlimit 30"
let step_normal_ok a minor cs g st farr q bk addr g' st' o
  = mem_not_infix minor addr;
    minor_objects_valid minor addr;
    assert (forward_one a minor cs addr == forward_normal a minor cs addr);
    assert (forward_normal a minor cs addr == pushed cs g' st' addr o);
    matches_push cs g st farr q bk g' st' addr o

let step_normal_oom a minor cs g st addr g' st'
  = mem_not_infix minor addr
#pop-options

/// The offset of an infix address in its closure, and the room for it.
#push-options "--z3rlimit 30"
let infix_offset (minor: minor_state) (addr: U64.t) (f: nat)
  : Lemma (requires L.mpre minor /\ is_infix_in_minor minor addr /\
                    f + minor_wosize minor (infix_parent minor addr) * 8 <= heap_size)
          (ensures (let p = infix_parent minor addr in
                    U64.v addr >= U64.v p /\ f + (U64.v addr - U64.v p) < heap_size /\
                    Seq.mem p (minor_objects minor) /\ ~(is_infix_in_minor minor p) /\ p <> addr /\
                    U64.v p >= 8 /\ U64.v p < minor_heap_size /\ U64.v p % 8 == 0))
  = infix_parent_value minor addr;
    infix_parent_in_minor_objects minor addr;
    L.parent_facts minor addr;
    minor_objects_valid minor (infix_parent minor addr)
#pop-options

#push-options "--z3rlimit 40"
let step_infix_fwd a minor g0 cs g st farr q bk addr
  = sim_eq a minor g0 cs;
    let p = infix_parent minor addr in
    infix_parent_in_minor_objects minor addr;
    sim_room a minor g0 cs p;
    infix_offset minor addr (U64.v (cs.fwd p));
    assert (forward_normal a minor cs p == cs);
    let v = U64.uint_to_t (U64.v (cs.fwd p) + (U64.v addr - U64.v p)) in
    assert (forward_one a minor cs addr == { cs with fwd = extend_forwarding cs.fwd addr v });
    matches_set cs g st farr q bk addr v
#pop-options

/// The infix step that promotes the closure, in the model: the closure
/// pushed, then the address at its offset in the copy.
#push-options "--z3rlimit 30"
let infix_new_eq (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (addr: U64.t)
                 (g': heap) (st': pstate) (o: U64.t)
  : Lemma (requires L.mpre minor /\ contract a /\ a.inv cs.major cs.st /\
                    cs.fwd addr == 0UL /\ is_infix_in_minor minor addr /\
                    (let p = infix_parent minor addr in
                     minor_wosize minor p > 0 /\ cs.fwd p == 0UL /\
                     promote_object a minor cs.major p cs.st (minor_wosize minor p) == (g', st', o) /\
                     o <> 0UL))
          (ensures (let p = infix_parent minor addr in
                    let v = U64.v o + (U64.v addr - U64.v p) in
                    U64.v addr >= U64.v p /\ v < heap_size /\
                    U64.v p >= 8 /\ U64.v p < minor_heap_size /\ U64.v p % 8 == 0 /\
                    (let cs1 = pushed cs g' st' p o in
                     forward_one a minor cs addr ==
                     { cs1 with fwd = extend_forwarding cs1.fwd addr (U64.uint_to_t v) })))
  = let p = infix_parent minor addr in
    infix_parent_in_minor_objects minor addr;
    L.tag_not_infix minor p;
    alloc_room a cs.major cs.st (minor_wosize minor p) (promoted_tag minor p);
    infix_offset minor addr (U64.v o);
    assert (forward_normal a minor cs p == pushed cs g' st' p o)
#pop-options

let div8 (x: U64.t)
  : Lemma (requires U64.v x < minor_heap_size)
          (ensures U64.v x / 8 >= 0 /\ U64.v x / 8 < fwd_array_size)
  = ()

#push-options "--z3rlimit 30"
let step_infix_new a minor g0 cs g st farr q bk addr g' st' o
  = sim_eq a minor g0 cs;
    infix_new_eq a minor cs addr g' st' o;
    let p = infix_parent minor addr in
    div8 p;
    div8 addr;
    let v = U64.uint_to_t (U64.v o + (U64.v addr - U64.v p)) in
    let cs1 = pushed cs g' st' p o in
    matches_push cs g st farr q bk g' st' p o;
    matches_set cs1 g' st' (Seq.upd farr (U64.v p / 8) o) (Seq.upd q bk p) (bk + 1) addr v
#pop-options

#push-options "--z3rlimit 30"
let step_infix_oom a minor g0 cs g st addr g' st'
  = sim_eq a minor g0 cs;
    let p = infix_parent minor addr in
    infix_parent_in_minor_objects minor addr;
    minor_objects_body_bound minor p;
    assert (forward_normal a minor cs p == cs)
#pop-options

/// ---------------------------------------------------------------------------
/// The loops
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let fields_step a minor cs p i wz = ()
let fields_base a minor cs p i wz = ()
let roots_step a minor cs roots i = ()
let roots_base a minor cs roots i = ()
let scan_step a minor cs sc fuel = ()
let scan_base a minor cs sc fuel = ()

let rec sim_fields_rec (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (p: U64.t) (i wz: nat)
  : Lemma (requires sim a minor g0 cs)
          (ensures sim a minor g0 (forward_fields a minor cs p i wz))
          (decreases (if i >= wz then 0 else wz - i))
  = if i >= wz then ()
    else begin
      let fv = to_minor_offset (minor_read_field minor p i) in
      sim_forward_one a minor g0 cs fv;
      sim_fields_rec a minor g0 (forward_one a minor cs fv) p (i + 1) wz
    end

let sim_fields a minor g0 cs p i wz = sim_fields_rec a minor g0 cs p i wz

let rec sim_roots (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (roots: seq U64.t) (i: nat)
  : Lemma (requires sim a minor g0 cs)
          (ensures sim a minor g0 (forward_roots a minor cs roots i))
          (decreases (if i >= Seq.length roots then 0 else Seq.length roots - i))
  = if i >= Seq.length roots then ()
    else begin
      sim_forward_one a minor g0 cs (Seq.index roots i);
      sim_roots a minor g0 (forward_one a minor cs (Seq.index roots i)) roots (i + 1)
    end

let rec sim_scan (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (sc fuel: nat)
  : Lemma (requires sim a minor g0 cs)
          (ensures sim a minor g0 (scan a minor cs sc fuel))
          (decreases fuel)
  = if fuel = 0 then ()
    else if sc >= Seq.length cs.queue then ()
    else begin
      let fuel' : nat = fuel - 1 in
      let obj = Seq.index cs.queue sc in
      let cs' = forward_fields a minor cs obj 0 (minor_scan_wosize minor obj) in
      sim_fields_rec a minor g0 cs obj 0 (minor_scan_wosize minor obj);
      assert (scan a minor cs sc fuel == scan a minor cs' (sc + 1) fuel');
      sim_scan a minor g0 cs' (sc + 1) fuel'
    end
#pop-options

let promote_sim a minor g0 st0 roots
  = sim_init a minor g0 st0;
    let cs1 = forward_roots a minor (init g0 st0) roots 0 in
    sim_roots a minor g0 (init g0 st0) roots 0;
    sim_scan a minor g0 cs1 0 (Seq.length (minor_objects minor))

let sim_end a minor g0 cs = sim_eq a minor g0 cs
