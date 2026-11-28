/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWMinor0 - a minor collection of the empty nursery
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  The witness runs collect the nursery while marking and
/// while sweeping, when it holds no object.  The first-fit minor collection
/// (`FFMinor.pcollect`) then promotes nothing: the roots are forwarded to
/// themselves, akhil's pointer update over the major heap writes nothing,
/// and the result is `Done` with the same major heap (its bytes below
/// `zero_addr` replaced by the state's), the same free list, the same roots
/// and no forwarding.  The empty nursery is the initial one, and every
/// reset one is it (`yreset_yinit`).

module GC.Spec.Top.FFWMinor0

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFReplay
open GC.Spec.Top.FFMinor
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PR = GC.Spec.Top.PromoteRun
module Q0 = GC.Spec.Top.PagesQueue
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module F = GC.Spec.Top.PagesFwd
module Y = GC.Spec.Top.Young

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The empty nursery.
let ms0 : minor_state = minor_init (Seq.create minor_heap_size 0uy)

let yinit_ms0 (n: nat) : Lemma (Y.yinit n == ms0) = ()

/// A reset nursery is the empty one.
let yreset_yinit (ms: minor_state) : Lemma (Y.yreset ms == ms0)
  = let a = minor_reset ms in
    let b = minor_init (Seq.create minor_heap_size 0uy) in
    U64.v_inj a.bump b.bump

/// It holds no object, and no infix address.
let ms0_empty (x: U64.t) : Lemma (~(Seq.mem x (minor_objects ms0)) /\ ~(is_infix_in_minor ms0 x))
  = yreset_yinit ms0;
    minor_reset_objects_not_mem ms0 x;
    minor_reset_no_infix ms0 x

/// ---------------------------------------------------------------------------
/// The promotion
/// ---------------------------------------------------------------------------

let forward_one_id (#s: Type0) (a: P.tal s) (cs: P.gstate s) (x: U64.t)
  : Lemma (requires cs.P.fwd == empty_forwarding) (ensures P.forward_one a ms0 cs x == cs)
  = ms0_empty x

#push-options "--fuel 1"
let rec forward_roots_id (#s: Type0) (a: P.tal s) (cs: P.gstate s) (roots: seq U64.t) (idx: nat)
  : Lemma (requires cs.P.fwd == empty_forwarding)
          (ensures P.forward_roots a ms0 cs roots idx == cs)
          (decreases (if idx >= Seq.length roots then 0 else Seq.length roots - idx))
  = if idx < Seq.length roots then begin
      forward_one_id a cs (Seq.index roots idx);
      forward_roots_id a cs roots (idx + 1)
    end

let scan_id (#s: Type0) (a: P.tal s) (cs: P.gstate s) (n: nat)
  : Lemma (requires Seq.length cs.P.queue == 0) (ensures P.scan a ms0 cs 0 n == cs)
  = ()
#pop-options

/// akhil's promotion promotes nothing.
let promote_id (#s: Type0) (a: P.tal s) (g: heap) (st: s) (roots: seq U64.t)
  : Lemma (let cs = P.promote a ms0 g st roots in
           cs.P.major == g /\ cs.P.st == st /\ cs.P.fwd == empty_forwarding /\ Seq.length cs.P.queue == 0)
  = let cs0 : P.gstate s = { P.major = g; P.st = st; P.fwd = empty_forwarding; P.queue = Seq.empty } in
    forward_roots_id a cs0 roots 0;
    scan_id a cs0 (Seq.length (minor_objects ms0))

/// ---------------------------------------------------------------------------
/// The pointer update writes nothing
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --z3rlimit 40"
let rec uop_id (g: heap) (obj: U64.t) (wz: nat) (i: nat)
  : Lemma (ensures update_object_pointers g obj wz empty_forwarding i == g) (decreases (wz - i))
  = if i < wz then begin
      let fo = U64.v obj + i * 8 in
      if fo + 8 <= heap_size && fo % 8 = 0 then update_object_pointers_step g obj wz empty_forwarding i;
      uop_id g obj wz (i + 1)
    end
#pop-options

#push-options "--fuel 1"
let rec uwa_id (g: heap) (objs: seq obj_addr) (upd: obj_addr -> GTot bool) (idx: nat)
  : Lemma (ensures update_walk_aux g objs upd empty_forwarding idx == g)
          (decreases (Seq.length objs - idx))
  = if idx < Seq.length objs then begin
      let obj = Seq.index objs idx in
      uop_id g obj (U64.v (wosize_of_object obj g)) 0;
      uwa_id g objs upd (idx + 1)
    end
#pop-options

let upw_id (free: free_def) (g: heap)
  : Lemma (update_pointers_with free g empty_forwarding == g)
  = uwa_id g (objects zero_addr g) (in_use free g) 0

/// ---------------------------------------------------------------------------
/// The collection
/// ---------------------------------------------------------------------------

/// Nothing is left unforwarded: the empty nursery has no object to attempt.
let closure_empty (cs: P.gstate U64.t) (roots: seq U64.t)
  : Lemma (requires Seq.length cs.P.queue == 0) (ensures closure ms0 cs roots)
  = let one (addr: U64.t) : Lemma (PR.covered ms0 cs addr)
      = PR.covered_def ms0 cs addr;
        ms0_empty addr;
        ms0_empty (resolve_minor ms0 addr) in
    FStar.Classical.forall_intro one

#push-options "--fuel 1"
let no_copies (q: seq U64.t) (fwd: forwarding_map)
  : Lemma (requires Seq.length q == 0) (ensures Q0.copies q fwd (Seq.length q) == [])
  = ()
#pop-options

/// **The collection of the empty nursery.**
#push-options "--z3rlimit 40"
let pcollect_empty (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state)
  : Lemma (requires cw.T.cyng == ms0)
          (ensures pcollect ph st cw ==
                   T.Done (gl cw.T.cmaj st) (tst (gl cw.T.cmaj st) st.fp)
                          (L.map (T.fwdv (Y.ycabs ms0) (F.fwd_of [])) cw.T.croots) (F.fwd_of []))
  = let tl = ptal ph st in
    let g0 = gl cw.T.cmaj st in
    let w = BM.cview cw in
    let roots = LV.roots_of w in
    promote_id tl g0 st.fp roots;
    closure_empty (P.promote tl ms0 g0 st.fp roots) roots;
    upw_id tl.P.free g0;
    let cs = P.promote tl ms0 g0 st.fp roots in
    no_copies cs.P.queue cs.P.fwd
#pop-options

/// No forwarding leaves every value as it is.
#push-options "--fuel 2"
let fwdv_none (y: M.mheap) (v: M.value) : Lemma (T.fwdv y (F.fwd_of []) v == v)
  = match v with
    | M.VPtr (M.Young a) ->
      (match M.resolve y a with
       | Some o -> assert (F.fwd_of [] o == None)
       | None -> ())
    | _ -> ()

let rec map_fwd_none (y: M.mheap) (rs: list M.value)
  : Lemma (ensures L.map (T.fwdv y (F.fwd_of [])) rs == rs) (decreases rs)
  = match rs with
    | [] -> ()
    | v :: tl -> fwdv_none y v; map_fwd_none y tl
#pop-options
