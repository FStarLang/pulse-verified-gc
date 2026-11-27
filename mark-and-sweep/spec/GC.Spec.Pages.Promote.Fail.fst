/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Fail - did a promotion's allocation fail?
/// ---------------------------------------------------------------------------
///
/// The promotion of GC.Spec.Pages.Promote skips an object whose allocation
/// finds no room and carries on.  `failed a minor major st roots` says
/// whether that happened, step by step along the same loop: a nursery
/// object (or an infix address's closure) not yet forwarded, with a body,
/// whose `promote_object` returned 0.  It is what the Pulse promotion's
/// `ok` flag computes (`GC.Impl.Pages.Cheney.promote_all`), and what the
/// minor collection of pages reports as `OutOfRoom` (design doc §18,
/// U5/U7).

module GC.Spec.Pages.Promote.Fail

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Promote

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The allocation for a nursery object that is not infix fails.
let fails_normal (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t) : GTot bool =
  Seq.mem addr (minor_objects minor) && cs.fwd addr = 0UL && minor_wosize minor addr > 0 &&
  (let (_, _, o) = promote_object a minor cs.major addr cs.st (minor_wosize minor addr) in o = 0UL)

/// Forwarding an address fails: its object's allocation, or its closure's.
let fails_one (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t) : GTot bool =
  cs.fwd addr = 0UL &&
  (if is_infix_in_minor minor addr then fails_normal a minor cs (infix_parent minor addr)
   else fails_normal a minor cs addr)

let rec fails_fields (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s)
                     (parent: U64.t) (idx: nat) (wz: nat)
  : GTot bool (decreases (if idx >= wz then 0 else wz - idx)) =
  if idx >= wz then false
  else
    let fv = to_minor_offset (minor_read_field minor parent idx) in
    fails_one a minor cs fv || fails_fields a minor (forward_one a minor cs fv) parent (idx + 1) wz

let rec fails_roots (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (roots: seq U64.t) (idx: nat)
  : GTot bool (decreases (if idx >= Seq.length roots then 0 else Seq.length roots - idx)) =
  if idx >= Seq.length roots then false
  else fails_one a minor cs (Seq.index roots idx) ||
       fails_roots a minor (forward_one a minor cs (Seq.index roots idx)) roots (idx + 1)

let rec fails_scan (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (sc: nat) (fuel: nat)
  : GTot bool (decreases fuel) =
  if fuel = 0 || sc >= Seq.length cs.queue then false
  else
    let obj = Seq.index cs.queue sc in
    fails_fields a minor cs obj 0 (minor_scan_wosize minor obj) ||
    fails_scan a minor (forward_fields a minor cs obj 0 (minor_scan_wosize minor obj)) (sc + 1) (fuel - 1)

/// **A promotion failed**: along `promote`, some allocation found no room.
let failed (#s: Type0) (a: tal s) (minor: minor_state) (major: heap) (st: s) (roots: seq U64.t) : GTot bool =
  let cs0 = { major = major; st = st; fwd = empty_forwarding; queue = Seq.empty } in
  fails_roots a minor cs0 roots 0 ||
  fails_scan a minor (forward_roots a minor cs0 roots 0) 0 (Seq.length (minor_objects minor))

/// ---------------------------------------------------------------------------
/// The loops, a step at a time
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let fields_step (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (p: U64.t) (i wz: nat)
  : Lemma (requires i < wz)
          (ensures (let fv = to_minor_offset (minor_read_field minor p i) in
                    fails_fields a minor cs p i wz ==
                    (fails_one a minor cs fv || fails_fields a minor (forward_one a minor cs fv) p (i + 1) wz)))
  = ()

let fields_base (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (p: U64.t) (i wz: nat)
  : Lemma (requires i >= wz) (ensures fails_fields a minor cs p i wz == false)
  = ()

let roots_step (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (roots: seq U64.t) (i: nat)
  : Lemma (requires i < Seq.length roots)
          (ensures fails_roots a minor cs roots i ==
                   (fails_one a minor cs (Seq.index roots i) ||
                    fails_roots a minor (forward_one a minor cs (Seq.index roots i)) roots (i + 1)))
  = ()

let roots_base (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (roots: seq U64.t) (i: nat)
  : Lemma (requires i >= Seq.length roots) (ensures fails_roots a minor cs roots i == false)
  = ()

let scan_step (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (sc fuel: nat)
  : Lemma (requires fuel > 0 /\ sc < Seq.length cs.queue)
          (ensures (let obj = Seq.index cs.queue sc in
                    let wz = minor_scan_wosize minor obj in
                    fails_scan a minor cs sc fuel ==
                    (fails_fields a minor cs obj 0 wz ||
                     fails_scan a minor (forward_fields a minor cs obj 0 wz) (sc + 1) (fuel - 1))))
  = ()

let scan_base (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (sc fuel: nat)
  : Lemma (requires fuel = 0 \/ sc >= Seq.length cs.queue) (ensures fails_scan a minor cs sc fuel == false)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// The forwarding step, by branch
/// ---------------------------------------------------------------------------

/// Nothing to forward: no failure.
let one_skip (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : Lemma (requires cs.fwd addr <> 0UL \/ (~(is_infix_in_minor minor addr) /\ ~(Seq.mem addr (minor_objects minor))))
          (ensures fails_one a minor cs addr == false)
  = ()

/// A nursery object: it fails exactly when its allocation does.
let one_normal (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t) (g': heap) (st': s) (o: U64.t)
  : Lemma (requires ~(is_infix_in_minor minor addr) /\ Seq.mem addr (minor_objects minor) /\ cs.fwd addr == 0UL /\
                    minor_wosize minor addr > 0 /\
                    promote_object a minor cs.major addr cs.st (minor_wosize minor addr) == (g', st', o))
          (ensures fails_one a minor cs addr == (o = 0UL))
  = ()

/// An infix address whose closure is forwarded: no failure.
let one_infix_done (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : Lemma (requires is_infix_in_minor minor addr /\ cs.fwd (infix_parent minor addr) <> 0UL)
          (ensures fails_one a minor cs addr == false)
  = ()

/// An infix address whose closure is not forwarded: it fails exactly when
/// the closure's allocation does.
let one_infix_new (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
                  (g': heap) (st': s) (o: U64.t)
  : Lemma (requires is_infix_in_minor minor addr /\ cs.fwd addr == 0UL /\
                    (let p = infix_parent minor addr in
                     Seq.mem p (minor_objects minor) /\ cs.fwd p == 0UL /\ minor_wosize minor p > 0 /\
                     promote_object a minor cs.major p cs.st (minor_wosize minor p) == (g', st', o)))
          (ensures fails_one a minor cs addr == (o = 0UL))
  = ()
