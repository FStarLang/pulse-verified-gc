/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Cheney - the Cheney promotion with the page allocator
/// ---------------------------------------------------------------------------
///
/// Plan §30.  akhil's `GC.Gen.Impl.Cheney` loops (forward the roots, then
/// scan the queue of promoted objects, forwarding their fields), over
/// `GC.Impl.Pages.Forward.forward_if_minor`: every copy allocated by the page
/// allocator of the phase.  `promote_all` computes exactly the model's
/// promotion, `Spec.Pages.Promote.promote a`, for any allocator `a` that is
/// the page allocator of the phase (`Sim.at_phase`), and ends in the loop
/// invariant `Sim.sim`.
///
/// Each loop's body is its own function: `fwd_fields` forwards one object's
/// fields, `scan_one` one queue entry; the loops carry only the model state,
/// as a ghost witness of `Forward.cst`.

module GC.Impl.Pages.Cheney

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.ForwardingArray
open GC.Impl.Heap
open GC.Spec.Pages.Inv
open GC.Impl.Pages.State
open GC.Gen.Promote
open GC.Spec.Pages.Promote
open GC.Impl.Pages.Promote
open GC.Impl.Pages.Forward

module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module Sim = GC.Spec.Pages.Promote.Sim
module CSim = GC.Gen.Cheney.Sim
module L = GC.Spec.Pages.Promote.Loop
module FW = GC.Spec.Pages.Promote.Follow
module Fl = GC.Spec.Pages.Promote.Fail
module Gd = GC.Spec.Pages.Promote.Guard

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The address of field `i` of `obj`.
let field_addr_ok (obj wz i: nat)
  : Lemma (requires obj >= 8 /\ obj % 8 == 0 /\ obj + wz * 8 <= minor_heap_size /\ i < wz)
          (ensures obj < minor_heap_size /\ i < minor_heap_size /\ i * 8 < pow2 64 /\
                   obj + i * 8 < pow2 64 /\ obj + i * 8 + 8 <= minor_heap_size /\
                   (obj + i * 8) % 8 == 0 /\ i + 1 < pow2 64)
  = FStar.Math.Lemmas.lemma_mult_le_right 8 (i + 1) wz;
    FStar.Math.Lemmas.modulo_addition_lemma obj 8 i;
    assert_norm (pow2 57 < pow2 64)

/// **The fields `0 .. wz` of `obj`, forwarded**: exactly `forward_fields`.
#push-options "--z3rlimit 30"
fn fwd_fields (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (oom_ref: R.ref bool) (obj wz: U64.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs ** R.pts_to oom_ref 'oom **
           pure (pre a ph marking (mst 'md 'mb) g0 cs /\
                 U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\ U64.v obj + U64.v wz * 8 <= minor_heap_size /\
                 Seq.mem obj (minor_objects (mst 'md 'mb)) /\ U64.v wz == minor_scan_wosize (mst 'md 'mb) obj)
  ensures exists* oom'. is_minor minor 'md 'mb **
          cst major t fwd_arr queue back (forward_fields a (mst 'md 'mb) cs obj 0 (U64.v wz)) **
          R.pts_to oom_ref oom' **
          pure (pre a ph marking (mst 'md 'mb) g0 (forward_fields a (mst 'md 'mb) cs obj 0 (U64.v wz)) /\
                oom' == ('oom || Fl.fails_fields a (mst 'md 'mb) cs obj 0 (U64.v wz)))
{
  let mut i = 0UL;
  while (U64.lt !i wz)
    invariant exists* iv cs_i oom_i.
      R.pts_to i iv ** is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs_i **
      R.pts_to oom_ref oom_i **
      pure (U64.v iv <= U64.v wz /\ pre a ph marking (mst 'md 'mb) g0 cs_i /\
            forward_fields a (mst 'md 'mb) cs_i obj (U64.v iv) (U64.v wz) ==
            forward_fields a (mst 'md 'mb) cs obj 0 (U64.v wz) /\
            (oom_i || Fl.fails_fields a (mst 'md 'mb) cs_i obj (U64.v iv) (U64.v wz)) ==
            ('oom || Fl.fails_fields a (mst 'md 'mb) cs obj 0 (U64.v wz)))
    decreases (U64.v wz - U64.v !i)
  {
    let iv = !i;
    with cs_i. assert (cst major t fwd_arr queue back cs_i);
    field_addr_ok (U64.v obj) (U64.v wz) (U64.v iv);
    Sim.fields_step a (mst 'md 'mb) cs_i obj (U64.v iv) (U64.v wz);
    Fl.fields_step a (mst 'md 'mb) cs_i obj (U64.v iv) (U64.v wz);
    let raw = minor_read minor (U64.add obj (U64.mul iv 8UL));
    CSim.minor_read_eq_field (mst 'md 'mb) obj (U64.v iv);
    Sim.sim_facts a (mst 'md 'mb) g0 cs_i;
    FW.fields_follow_elim (mst 'md 'mb) obj (U64.v iv);
    Gd.fields_gd_elim (mst 'md 'mb) obj (U64.v iv);
    let child = to_minor_offset_u64 raw;
    forward_if_minor minor major t marking fwd_arr queue back oom_ref child #a #ph #g0 #cs_i;
    i := U64.add iv 1UL
  };
  with cs_e. assert (cst major t fwd_arr queue back cs_e);
  Sim.fields_base a (mst 'md 'mb) cs_e obj (U64.v wz) (U64.v wz);
  Fl.fields_base a (mst 'md 'mb) cs_e obj (U64.v wz) (U64.v wz);
  rewrite (cst major t fwd_arr queue back cs_e)
       as (cst major t fwd_arr queue back (forward_fields a (mst 'md 'mb) cs obj 0 (U64.v wz)))
}
#pop-options

/// The fields of queue entry `s` forwarded (the model's scan step).
let scan_entry (a: tal pstate) (ms: minor_state) (cs: gstate pstate) (s: nat) : GTot (gstate pstate) =
  if s < Seq.length cs.queue
  then forward_fields a ms cs (Seq.index cs.queue s) 0 (minor_scan_wosize ms (Seq.index cs.queue s))
  else cs

/// Whether forwarding the fields of queue entry `s` failed.
let scan_entry_fails (a: tal pstate) (ms: minor_state) (cs: gstate pstate) (s: nat) : GTot bool =
  if s < Seq.length cs.queue
  then Fl.fails_fields a ms cs (Seq.index cs.queue s) 0 (minor_scan_wosize ms (Seq.index cs.queue s))
  else false

/// **One queue entry scanned**: its fields forwarded.
#push-options "--z3rlimit 30"
fn scan_one (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (oom_ref: R.ref bool) (s: SZ.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs ** R.pts_to oom_ref 'oom **
           pure (pre a ph marking (mst 'md 'mb) g0 cs /\ SZ.v s < Seq.length cs.queue)
  ensures exists* oom'. is_minor minor 'md 'mb **
          cst major t fwd_arr queue back (scan_entry a (mst 'md 'mb) cs (SZ.v s)) **
          R.pts_to oom_ref oom' **
          pure (pre a ph marking (mst 'md 'mb) g0 (scan_entry a (mst 'md 'mb) cs (SZ.v s)) /\
                oom' == ('oom || scan_entry_fails a (mst 'md 'mb) cs (SZ.v s)))
{
  let obj = get_queue major t fwd_arr queue back s;
  Sim.sim_facts a (mst 'md 'mb) g0 cs;
  Sim.sim_queue a (mst 'md 'mb) g0 cs (SZ.v s);
  minor_objects_valid (mst 'md 'mb) obj;
  minor_objects_body_bound (mst 'md 'mb) obj;
  minor_scan_wosize_cases (mst 'md 'mb) obj;
  let wz = read_minor_scan_wosize minor obj;
  fwd_fields minor major t marking fwd_arr queue back oom_ref obj wz #a #ph #g0 #cs;
  rewrite (cst major t fwd_arr queue back (forward_fields a (mst 'md 'mb) cs obj 0 (U64.v wz)))
       as (cst major t fwd_arr queue back (scan_entry a (mst 'md 'mb) cs (SZ.v s)))
}
#pop-options

/// **The queue scanned**: exactly `scan` from 0, with the fuel of the
/// model (the number of nursery objects).
#push-options "--z3rlimit 30"
fn scan_loop (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (oom_ref: R.ref bool)
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs ** R.pts_to oom_ref 'oom **
           pure (pre a ph marking (mst 'md 'mb) g0 cs)
  ensures exists* oom'. is_minor minor 'md 'mb **
          cst major t fwd_arr queue back
            (scan a (mst 'md 'mb) cs 0 (Seq.length (minor_objects (mst 'md 'mb)))) **
          R.pts_to oom_ref oom' **
          pure (pre a ph marking (mst 'md 'mb) g0
                  (scan a (mst 'md 'mb) cs 0 (Seq.length (minor_objects (mst 'md 'mb)))) /\
                oom' == ('oom || Fl.fails_scan a (mst 'md 'mb) cs 0 (Seq.length (minor_objects (mst 'md 'mb)))))
{
  let mut sc = 0sz;
  while (
    let s = !sc;
    let b = get_back major t fwd_arr queue back;
    SZ.lt s b
  )
    invariant exists* sv cs_s oom_s.
      R.pts_to sc sv ** is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs_s **
      R.pts_to oom_ref oom_s **
      pure (pre a ph marking (mst 'md 'mb) g0 cs_s /\
            SZ.v sv <= Seq.length (minor_objects (mst 'md 'mb)) /\
            scan a (mst 'md 'mb) cs_s (SZ.v sv) (Seq.length (minor_objects (mst 'md 'mb)) - SZ.v sv) ==
            scan a (mst 'md 'mb) cs 0 (Seq.length (minor_objects (mst 'md 'mb))) /\
            (oom_s || Fl.fails_scan a (mst 'md 'mb) cs_s (SZ.v sv) (Seq.length (minor_objects (mst 'md 'mb)) - SZ.v sv)) ==
            ('oom || Fl.fails_scan a (mst 'md 'mb) cs 0 (Seq.length (minor_objects (mst 'md 'mb)))))
    decreases (queue_size - SZ.v !sc)
  {
    let s = !sc;
    with cs_s. assert (cst major t fwd_arr queue back cs_s);
    Sim.sim_facts a (mst 'md 'mb) g0 cs_s;
    Sim.scan_step a (mst 'md 'mb) cs_s (SZ.v s) (Seq.length (minor_objects (mst 'md 'mb)) - SZ.v s);
    Fl.scan_step a (mst 'md 'mb) cs_s (SZ.v s) (Seq.length (minor_objects (mst 'md 'mb)) - SZ.v s);
    scan_one minor major t marking fwd_arr queue back oom_ref s #a #ph #g0 #cs_s;
    sc := SZ.add s 1sz
  };
  with cs_e. assert (cst major t fwd_arr queue back cs_e);
  with sv. assert (R.pts_to sc sv);
  Sim.scan_base a (mst 'md 'mb) cs_e (SZ.v sv) (Seq.length (minor_objects (mst 'md 'mb)) - SZ.v sv);
  Fl.scan_base a (mst 'md 'mb) cs_e (SZ.v sv) (Seq.length (minor_objects (mst 'md 'mb)) - SZ.v sv);
  rewrite (cst major t fwd_arr queue back cs_e)
       as (cst major t fwd_arr queue back (scan a (mst 'md 'mb) cs 0 (Seq.length (minor_objects (mst 'md 'mb)))))
}
#pop-options

/// **The roots forwarded**: exactly `forward_roots` from 0.
#push-options "--z3rlimit 30"
fn fwd_roots (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (oom_ref: R.ref bool)
  (roots: array U64.t) (nroots: SZ.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs ** R.pts_to oom_ref 'oom **
           pts_to roots 'rs **
           pure (pre a ph marking (mst 'md 'mb) g0 cs /\ SZ.v nroots == Seq.length 'rs /\
                 FW.roots_follow (mst 'md 'mb) 'rs /\ Gd.roots_gd (mst 'md 'mb) 'rs)
  ensures exists* oom'. is_minor minor 'md 'mb **
          cst major t fwd_arr queue back (forward_roots a (mst 'md 'mb) cs 'rs 0) **
          R.pts_to oom_ref oom' ** pts_to roots 'rs **
          pure (pre a ph marking (mst 'md 'mb) g0 (forward_roots a (mst 'md 'mb) cs 'rs 0) /\
                oom' == ('oom || Fl.fails_roots a (mst 'md 'mb) cs 'rs 0))
{
  let mut i = 0sz;
  while (SZ.lt !i nroots)
    invariant exists* iv cs_i oom_i.
      R.pts_to i iv ** is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs_i **
      R.pts_to oom_ref oom_i ** pts_to roots 'rs **
      pure (SZ.v iv <= SZ.v nroots /\ pre a ph marking (mst 'md 'mb) g0 cs_i /\
            forward_roots a (mst 'md 'mb) cs_i 'rs (SZ.v iv) == forward_roots a (mst 'md 'mb) cs 'rs 0 /\
            (oom_i || Fl.fails_roots a (mst 'md 'mb) cs_i 'rs (SZ.v iv)) ==
            ('oom || Fl.fails_roots a (mst 'md 'mb) cs 'rs 0))
    decreases (SZ.v nroots - SZ.v !i)
  {
    let iv = !i;
    with cs_i. assert (cst major t fwd_arr queue back cs_i);
    Sim.roots_step a (mst 'md 'mb) cs_i 'rs (SZ.v iv);
    Fl.roots_step a (mst 'md 'mb) cs_i 'rs (SZ.v iv);
    let r = roots.(iv);
    forward_if_minor minor major t marking fwd_arr queue back oom_ref r #a #ph #g0 #cs_i;
    i := SZ.add iv 1sz
  };
  with cs_e. assert (cst major t fwd_arr queue back cs_e);
  Sim.roots_base a (mst 'md 'mb) cs_e 'rs (SZ.v nroots);
  Fl.roots_base a (mst 'md 'mb) cs_e 'rs (SZ.v nroots);
  rewrite (cst major t fwd_arr queue back cs_e)
       as (cst major t fwd_arr queue back (forward_roots a (mst 'md 'mb) cs 'rs 0))
}
#pop-options

/// **The promotion**: the roots forwarded, then the queue scanned; exactly
/// the model's `promote a`, ending in the loop invariant.  `ok` is false
/// exactly when an allocation failed (`Promote.Fail.failed`; design doc
/// §18, U5).  It reads only what it follows (`Loop.cpre_w`, §12).  The
/// forwarding array must be zero on entry; the queue's contents do not
/// matter.
#push-options "--z3rlimit 30"
fn promote_all (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (roots: array U64.t) (nroots: SZ.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase)
  requires is_minor minor 'md 'mb ** is_heap major 'g ** pages_st t 'st **
           pts_to fwd_arr 'farr ** pts_to queue 'qv ** pts_to roots 'rs **
           pure (Sim.at_phase a ph /\ marking == I.Marking? ph /\
                 L.cpre_w a (mst 'md 'mb) 'g 'st 'rs /\
                 Gd.fields_gd (mst 'md 'mb) /\ Gd.roots_gd (mst 'md 'mb) 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < fwd_array_size ==> Seq.index 'farr i == 0UL) /\
                 Seq.length 'qv == queue_size /\ SZ.v nroots == Seq.length 'rs)
  returns ok: bool
  ensures exists* g' st' farr' qv'. is_minor minor 'md 'mb ** is_heap major g' ** pages_st t st' **
          pts_to fwd_arr farr' ** pts_to queue qv' ** pts_to roots 'rs **
          pure (let cs = promote a (mst 'md 'mb) 'g 'st 'rs in
                ok == not (Fl.failed a (mst 'md 'mb) 'g 'st 'rs) /\
                g' == cs.major /\ st' == cs.st /\
                Seq.length farr' == fwd_array_size /\ represents_fwd farr' cs.fwd /\
                Sim.sim a (mst 'md 'mb) 'g cs)
{
  let mut back = 0sz;
  let mut oom = false;
  Sim.matches_init 'g 'st 'farr 'qv;
  Sim.sim_init a (mst 'md 'mb) 'g 'st 'rs;
  fold (cst major t fwd_arr queue back (Sim.init 'g 'st));
  fwd_roots minor major t marking fwd_arr queue back oom roots nroots #a #ph #'g #(Sim.init 'g 'st);
  scan_loop minor major t marking fwd_arr queue back oom
    #a #ph #'g #(forward_roots a (mst 'md 'mb) (Sim.init 'g 'st) 'rs 0);
  unfold cst;
  with g st farr q bk. assert (is_heap major g ** pages_st t st ** pts_to fwd_arr farr ** pts_to queue q **
                               R.pts_to back bk **
                               pure (Sim.matches (promote a (mst 'md 'mb) 'g 'st 'rs) g st farr q (SZ.v bk)));
  Sim.matches_elim (promote a (mst 'md 'mb) 'g 'st 'rs) g st farr q (SZ.v bk);
  let failed = !oom;
  not failed
}
#pop-options
