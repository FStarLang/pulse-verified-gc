/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFCheney - the first-fit minor collection is akhil's
/// ---------------------------------------------------------------------------
///
/// U4 (design doc §18.3): the minor collection of the first-fit component,
/// `Pages.Promote.collect` with first-fit's instance `FFPromote.fftal ph`, is
/// akhil's `GC.Gen.Cheney.cheney_collect_spec_with` at the phase `gph ph`
/// and with first-fit's definition of free (`FFAllocOk.ffree_of ph`): the same
/// major heap, free-list head, forwarding map and rewritten roots.  His Pulse
/// `minor_collect_with` ends in exactly that.
///
/// The two loops are the same statement for statement (`Promote` was copied
/// from akhil's and generalised over the allocator); one promotion is equal by
/// definition (`fftal ph` allocates with `AP.alloc_at (gph ph)`, as his
/// `promote_object` does).  The rest is an induction through each loop,
/// reading akhil's loop functions through his equation lemmas.

module GC.Spec.Top.FFCheney

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
module U64 = FStar.UInt64
module T = GC.Spec.Top.Iface
module P = GC.Spec.Pages.Promote
module C = GC.Gen.Cheney
module FFP = GC.Spec.Top.FFPromote
module FA = GC.Spec.Top.FFAlloc
module FAO = GC.Spec.Top.FFAllocOk

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// akhil's loop state for ours, at the phase `ph`.
let toc (ph: T.phase U64.t) (cs: P.gstate U64.t) : C.cheney_state =
  { C.cs_major = cs.P.major; C.cs_fp = cs.P.st; C.cs_fwd = cs.P.fwd; C.cs_queue = cs.P.queue;
    C.cs_phase = FA.gph ph }

/// A state of akhil's loop is its fields.
let eta (c: C.cheney_state)
  : Lemma (c == { C.cs_major = c.C.cs_major; C.cs_fp = c.C.cs_fp; C.cs_fwd = c.C.cs_fwd;
                  C.cs_queue = c.C.cs_queue; C.cs_phase = c.C.cs_phase })
  = ()

/// ---------------------------------------------------------------------------
/// One promotion, and one address
/// ---------------------------------------------------------------------------

/// **One promotion** is akhil's `promote_object`, by definition.
let promote_eq (ph: T.phase U64.t) (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (let (g, s, o) = P.promote_object (FFP.fftal ph) minor major obj fp wz in
           let r = promote_object minor major obj fp wz (FA.gph ph) in
           g == r.major_out /\ s == r.fp_out /\ o == r.new_addr)
  = ()

/// Forwarding an object that is not infix.
let normal_eq (ph: T.phase U64.t) (minor: minor_state) (cs: P.gstate U64.t) (addr: U64.t)
  : Lemma (C.cheney_forward_normal minor (toc ph cs) addr == toc ph (P.forward_normal (FFP.fftal ph) minor cs addr))
  = let c = toc ph cs in
    if not (Seq.mem addr (minor_objects minor)) || cs.P.fwd addr <> 0UL then
      C.cheney_forward_normal_noop minor c addr
    else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then C.cheney_forward_normal_noop_wz0 minor c addr
      else begin
        promote_eq ph minor cs.P.major addr cs.P.st wz;
        let r = promote_object minor cs.P.major addr cs.P.st wz (FA.gph ph) in
        if r.new_addr = 0UL then C.cheney_forward_normal_noop_oom minor c addr
        else C.cheney_forward_normal_success minor c addr
      end
    end

/// Forwarding an address: an infix one through its parent closure.
let one_eq (ph: T.phase U64.t) (minor: minor_state) (cs: P.gstate U64.t) (addr: U64.t)
  : Lemma (C.cheney_forward_one minor (toc ph cs) addr == toc ph (P.forward_one (FFP.fftal ph) minor cs addr))
  = let c = toc ph cs in
    if cs.P.fwd addr <> 0UL then C.cheney_forward_one_noop minor c addr
    else if is_infix_in_minor minor addr then begin
      let parent = infix_parent minor addr in
      normal_eq ph minor cs parent;
      let cs' = P.forward_normal (FFP.fftal ph) minor cs parent in
      if cs'.P.fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (cs'.P.fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then begin
        C.cheney_forward_one_infix_guard_pass minor c addr;
        eta (C.cheney_forward_one minor c addr)
      end
      else C.cheney_forward_one_infix_guard_fail minor c addr
    end
    else begin
      C.cheney_forward_one_normal minor c addr;
      normal_eq ph minor cs addr
    end

/// ---------------------------------------------------------------------------
/// The loops
/// ---------------------------------------------------------------------------

/// The fields `idx ..` of `parent`.
#push-options "--fuel 1"
let rec fields_eq (ph: T.phase U64.t) (minor: minor_state) (cs: P.gstate U64.t) (parent: U64.t) (idx wz: nat)
  : Lemma (ensures C.cheney_forward_fields minor (toc ph cs) parent idx wz ==
                   toc ph (P.forward_fields (FFP.fftal ph) minor cs parent idx wz))
          (decreases (if idx >= wz then 0 else wz - idx))
  = if idx >= wz then C.cheney_forward_fields_base minor (toc ph cs) parent idx wz
    else begin
      C.cheney_forward_fields_step minor (toc ph cs) parent idx wz;
      let fv = to_minor_offset (minor_read_field minor parent idx) in
      one_eq ph minor cs fv;
      fields_eq ph minor (P.forward_one (FFP.fftal ph) minor cs fv) parent (idx + 1) wz
    end

/// The roots `idx ..`.
let rec roots_eq (ph: T.phase U64.t) (minor: minor_state) (cs: P.gstate U64.t) (roots: seq U64.t) (idx: nat)
  : Lemma (ensures C.cheney_forward_roots minor (toc ph cs) roots idx ==
                   toc ph (P.forward_roots (FFP.fftal ph) minor cs roots idx))
          (decreases (if idx >= Seq.length roots then 0 else Seq.length roots - idx))
  = if idx >= Seq.length roots then C.cheney_forward_roots_base minor (toc ph cs) roots idx
    else begin
      C.cheney_forward_roots_step minor (toc ph cs) roots idx;
      one_eq ph minor cs (Seq.index roots idx);
      roots_eq ph minor (P.forward_one (FFP.fftal ph) minor cs (Seq.index roots idx)) roots (idx + 1)
    end

/// The scan of the queue from `sc`.
let rec scan_eq (ph: T.phase U64.t) (minor: minor_state) (cs: P.gstate U64.t) (sc fuel: nat)
  : Lemma (ensures C.cheney_scan minor (toc ph cs) sc fuel == toc ph (P.scan (FFP.fftal ph) minor cs sc fuel))
          (decreases fuel)
  = if fuel = 0 || sc >= Seq.length cs.P.queue then C.cheney_scan_base minor (toc ph cs) sc fuel
    else begin
      C.cheney_scan_step minor (toc ph cs) sc fuel;
      let obj = Seq.index cs.P.queue sc in
      fields_eq ph minor cs obj 0 (minor_scan_wosize minor obj);
      scan_eq ph minor (P.forward_fields (FFP.fftal ph) minor cs obj 0 (minor_scan_wosize minor obj)) (sc + 1) (fuel - 1)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The promotion and the collection
/// ---------------------------------------------------------------------------

/// **The promotion** is akhil's `cheney_promote`.
let promote_all_eq (ph: T.phase U64.t) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (let cs = P.promote (FFP.fftal ph) minor major fp roots in
           let r = C.cheney_promote (FA.gph ph) minor major fp roots in
           r.major_final == cs.P.major /\ r.fp_final == cs.P.st /\ r.fwd_map == cs.P.fwd)
  = let cs0 : P.gstate U64.t = { P.major = major; P.st = fp; P.fwd = empty_forwarding; P.queue = Seq.empty } in
    roots_eq ph minor cs0 roots 0;
    let cs1 = P.forward_roots (FFP.fftal ph) minor cs0 roots 0 in
    C.cheney_fuel_eq minor;
    scan_eq ph minor cs1 0 (Seq.length (minor_objects minor))

/// **The collection** is akhil's `cheney_collect_spec_with`, at `gph ph` and
/// first-fit's definition of free.
let collect_eq (ph: T.phase U64.t) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (let r = P.collect (FFP.fftal ph) minor major fp roots in
           let c = C.cheney_collect_spec_with (FA.gph ph) (FAO.ffree_of ph) minor major fp roots in
           c.mc_major == r.P.rmajor /\ c.mc_fp == r.P.rst /\ c.mc_roots == r.P.rroots /\
           c.mc_fwd == r.P.rfwd /\ c.mc_minor == r.P.rminor)
  = promote_all_eq ph minor major fp roots

/// ---------------------------------------------------------------------------
/// The flag: a collection akhil's code reports as not out of room
/// ---------------------------------------------------------------------------

module PR = GC.Spec.Top.PromoteRun
module CB = GC.Gen.CheneyBFS
module RC = GC.Gen.Reachability

/// A root akhil's map covers is covered.
let root_cov (minor: minor_state) (cs: P.gstate U64.t) (roots: seq U64.t) (i: nat)
  : Lemma (requires i < Seq.length roots /\ CB.fwd_covers_roots minor cs.P.fwd roots /\
                    CB.fwd_covers_infix_roots minor cs.P.fwd roots)
          (ensures PR.covered minor cs (Seq.index roots i))
  = Seq.Properties.lemma_index_is_nth roots i;
    Seq.Properties.mem_index (Seq.index roots i) roots;
    PR.covered_def minor cs (Seq.index roots i)

/// A field of a forwarded object akhil's map is closed under is covered.
let field_cov (minor: minor_state) (cs: P.gstate U64.t) (x: U64.t) (i: nat)
  : Lemma (requires Seq.mem x (minor_objects minor) /\ cs.P.fwd x <> 0UL /\ i < minor_scan_wosize minor x /\
                    CB.fwd_closed minor cs.P.fwd /\ CB.fwd_covers_infix_fields minor cs.P.fwd)
          (ensures PR.covered minor cs (PR.fld minor x i))
  = PR.fld_def minor x i;
    let f = to_minor_offset (minor_read_field minor x i) in
    let y = resolve_minor minor f in
    PR.covered_def minor cs f;
    if Seq.mem y (minor_objects minor) then begin
      minor_objects_valid minor y;
      is_minor_addr_from_bounds y;
      RC.minor_successors_char minor x y
    end

/// **akhil's `cheney_no_oom` is the closure** (`FFMinor.closure`): given the
/// queue's invariant, every root and every field of every queued object is
/// covered.  So a collection his code reports as not out of room is `Done`.
#push-options "--z3rlimit 40"
let no_oom_closure (ph: T.phase U64.t) (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires (let cs = P.promote (FFP.fftal ph) minor major fp roots in
                     PR.qok (FFP.fftal ph) minor major fp cs /\
                     CB.cheney_no_oom (FA.gph ph) minor major fp roots))
          (ensures (let cs = P.promote (FFP.fftal ph) minor major fp roots in
                    (forall (i: nat). i < Seq.length roots ==> PR.covered minor cs (Seq.index roots i)) /\
                    PR.scanned minor cs (Seq.length cs.P.queue)))
  = let cs = P.promote (FFP.fftal ph) minor major fp roots in
    promote_all_eq ph minor major fp roots;
    assert (CB.fwd_well_formed minor cs.P.fwd roots);
    let r (i: nat) : Lemma (i < Seq.length roots ==> PR.covered minor cs (Seq.index roots i))
      = if i < Seq.length roots then root_cov minor cs roots i in
    FStar.Classical.forall_intro r;
    let one (j i: nat)
      : Lemma (j < Seq.length cs.P.queue /\ j < Seq.length cs.P.queue /\
               i < PR.nsc minor (Seq.index cs.P.queue j) ==>
               PR.covered minor cs (PR.fld minor (Seq.index cs.P.queue j) i))
      = if j < Seq.length cs.P.queue && i < PR.nsc minor (Seq.index cs.P.queue j) then begin
          assert (PR.qentry (FFP.fftal ph) minor major fp cs j);
          PR.nsc_def minor (Seq.index cs.P.queue j);
          field_cov minor cs (Seq.index cs.P.queue j) i
        end in
    FStar.Classical.forall_intro_2 one
#pop-options
