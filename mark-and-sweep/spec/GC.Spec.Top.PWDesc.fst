/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWDesc - describing a configuration of the pages collector
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  The pages witness runs never write the heap of pages in
/// closed form (the free pages and free slots are abstract in number, and
/// the page arithmetic is nonlinear in the abstract page size).  A
/// configuration is described by `holds x d`:
///   - its phase, nursery (exactly: the minor state and the model nursery it
///     represents), roots, an empty remembered set, the stop flag;
///   - the allocator's invariant, and the page budget (`PWPages.kinds_ok`);
///   - its blocks in use, read on the canonical model `mx x` (`cabs`): each
///     is described (`db`), with its header and, while the program may use
///     it, its fields.  A block not described is free.
/// A block is live (`blv`) or garbage.  While sweeping, a live block has the
/// colour rule's colour (black where unswept, white where swept), and a
/// garbage block is white and unswept while in use: the sweep may free it
/// at any step, so its description says nothing once it is free.
/// The description's world `wd x d` represents the configuration, and every
/// world that does reads the same (`views_wd`).

module GC.Spec.Top.PWDesc

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
open GC.Spec.Top.RunFacts
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module Y = GC.Spec.Top.Young
module PC = GC.Spec.Top.PagesComps
module PIn = GC.Spec.Top.PagesInst
module PWP = GC.Spec.Top.PWPages
module BM = GC.Spec.Top.ByteMark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let pc : comps = PC.pc

/// The components' contracts, sealed: each step takes the instance it needs.
[@@"opaque_to_smt"]
let cok : prop = components_ok pc

let cok_intro () : Lemma (requires components_ok pc) (ensures cok) = reveal_opaque (`%cok) cok

let cok_hyps (x: config pc) (e: event) : Lemma (requires cok) (ensures hyps_at pc x e)
  = reveal_opaque (`%cok) cok; hyps_of_ok pc x e

let cok_init () : Lemma (requires cok) (ensures T.init_at byte_rep pa msize)
  = reveal_opaque (`%cok) cok

let cok_alloc (ph: T.phase pprog) (h: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires cok) (ensures T.alloc_at byte_rep pa ph h s sz tag)
  = reveal_opaque (`%cok) cok

let cok_ok () : Lemma (requires cok) (ensures components_ok pc) = reveal_opaque (`%cok) cok

/// ---------------------------------------------------------------------------
/// Descriptions
/// ---------------------------------------------------------------------------

type phk = | DI | DM | DS

/// A block: its size, tag, colour (idle or marking), live or garbage, fields.
type bd = { bw: nat; bt: M.tag_t; bc: M.colour; blv: bool; bf: list M.value }

noeq type dsc = {
  dk  : phk;
  db  : nat -> GTot (option bd);
  dys : minor_state;
  dym : M.mheap;
  drt : list M.value;
  dj  : nat;
}

/// A list's element, or 0.
let vi (l: list M.value) (i: nat) : M.value = if i < L.length l then L.index l i else M.VInt 0

/// The canonical model of the major heap.
let mx (x: config pc) : GTot M.mheap = cabs x.w.cmaj

let stx (x: config pc) : pst = x.ast

/// In use.
let iu (x: config pc) (o: nat) : GTot bool = T.in_use pa (stx x) x.w.cmaj (mx x) o

let kph (x: config pc) (k: phk) : prop =
  match k with
  | DI -> T.Idle? x.ph
  | DM -> T.Marking? x.ph
  | DS -> T.Sweeping? x.ph

/// The colour a described block has.
let hcol (x: config pc) (b: bd) (o: nat) : GTot M.colour =
  match x.ph with
  | T.Sweeping p -> if b.blv && punswept p o then M.Black else M.White
  | _ -> b.bc

let unsw (x: config pc) (o: nat) : GTot bool =
  match x.ph with
  | T.Sweeping p -> punswept p o
  | _ -> false

/// The program may use the block: live, or not sweeping.
let usable (d: dsc) (b: bd) : bool = b.blv || not (DS? d.dk)

let bk (x: config pc) (d: dsc) (o: nat) (b: bd) : prop =
  let m = mx x in
  (usable d b ==> iu x o == true) /\
  (iu x o == true ==> m.M.hd o == Some ({ M.wz = b.bw; M.tag = b.bt; M.col = hcol x b o })) /\
  (iu x o == true /\ DS? d.dk /\ not b.blv ==> unsw x o == true) /\
  (usable d b ==> L.length b.bf == b.bw /\ (forall (i: nat). i < b.bw ==> M.field m o i == vi b.bf i))

let holds_body (x: config pc) (d: dsc) : prop =
  x.stopped == false /\ kph x d.dk /\
  x.w.cyng == d.dys /\ Y.yrepr d.dym d.dys /\ x.w.croots == d.drt /\ x.w.crem == [] /\ x.ms == None /\
  pa.T.inv x.ph x.w.cmaj (stx x) /\ PWP.kinds_ok (stx x).ps d.dj /\
  M.well_formed (mx x) /\
  (forall (o: nat). iu x o == true ==> Some? (d.db o)) /\
  (forall (o: nat). Some? (d.db o) ==> bk x d o (Some?.v (d.db o)))

[@@"opaque_to_smt"]
let holds (x: config pc) (d: dsc) : prop = holds_body x d

let holds_def (x: config pc) (d: dsc) : Lemma (holds x d <==> holds_body x d)
  = reveal_opaque (`%holds) (holds x d)

let reveal_holds (_: unit) : Lemma (forall (x: config pc) (d: dsc). holds x d <==> holds_body x d)
  = FStar.Classical.forall_intro_2 holds_def

/// The parts of a description, one at a time.
let holds_elim (x: config pc) (d: dsc)
  : Lemma (requires holds x d)
          (ensures x.stopped == false /\ kph x d.dk /\
                   x.w.cyng == d.dys /\ Y.yrepr d.dym d.dys /\ x.w.croots == d.drt /\ x.w.crem == [] /\ x.ms == None /\
                   pa.T.inv x.ph x.w.cmaj (stx x) /\ PWP.kinds_ok (stx x).ps d.dj /\ M.well_formed (mx x))
  = holds_def x d

let holds_blk (x: config pc) (d: dsc) (o: nat)
  : Lemma (requires holds x d /\ Some? (d.db o)) (ensures bk x d o (Some?.v (d.db o)))
  = holds_def x d

let holds_iu (x: config pc) (d: dsc) (o: nat)
  : Lemma (requires holds x d /\ iu x o == true) (ensures Some? (d.db o))
  = holds_def x d

let holds_intro (x: config pc) (d: dsc)
  : Lemma (requires holds_body x d) (ensures holds x d)
  = holds_def x d

/// ---------------------------------------------------------------------------
/// The description's world
/// ---------------------------------------------------------------------------

let wd (x: config pc) (d: dsc) : GTot M.world = { M.maj = mx x; M.yng = d.dym; M.roots = d.drt; M.rem = [] }

let views_two (x: config pc) (w1 w2: M.world)
  : Lemma (requires views x w1 /\ views x w2) (ensures wheq w1 w2)
  = BM.yrepr_heq w1.M.yng x.w.cyng; BM.yrepr_heq w2.M.yng x.w.cyng

let views_wd (x: config pc) (d: dsc)
  : Lemma (requires holds x d)
          (ensures views x (wd x d) /\ has_view x /\ wheq (vw x) (wd x d) /\
                   (forall (w1 w2: M.world). views x w1 /\ views x w2 ==> wheq w1 w2))
  = holds_def x d;
    brepr_cabs x.w.cmaj;
    FStar.Classical.forall_intro_2 (fun w1 w2 -> FStar.Classical.move_requires (views_two x w1) w2);
    assert (views x (wd x d));
    assert (has_view x);
    vw_views x

/// The program's obligations, on the description's world.
let mutator_wd (x: config pc) (d: dsc) (e: event)
  : Lemma (requires holds x d /\ mutator_ok_w pc (wd x d) e) (ensures mutator_ok x e)
  = views_wd x d;
    mutator_of_view x (wd x d) e

let mj_wd (x: config pc) (d: dsc) : Lemma (requires holds x d) (ensures R.heq (mj x) (mx x))
  = views_wd x d

let mark_done_wd (x: config pc) (d: dsc)
  : Lemma (requires holds x d) (ensures T.mark_done (mj x) <==> T.no_grey (mx x))
  = mj_wd x d

/// ---------------------------------------------------------------------------
/// Reading a description
/// ---------------------------------------------------------------------------

/// In use: a block that is not blue.
let iu_def (x: config pc) (o: nat)
  : Lemma (iu x o == (M.is_block (mx x) o && M.col_of (mx x) o <> M.Blue))
  = PIn.pfree_blue x.w.cmaj (stx x) x.w.cmaj o

/// In use, for any model the heap represents.
let iu_heq (x: config pc) (m: M.mheap) (o: nat)
  : Lemma (requires R.heq m (mx x)) (ensures T.in_use pa (stx x) x.w.cmaj m o == iu x o)
  = ()

/// A described block the program may use: in use, its header and fields.
let blk (x: config pc) (d: dsc) (o: nat)
  : Lemma (requires holds x d /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)))
          (ensures (let b = Some?.v (d.db o) in
                    iu x o == true /\ M.is_block (mx x) o /\
                    (mx x).M.hd o == Some ({ M.wz = b.bw; M.tag = b.bt; M.col = hcol x b o }) /\
                    M.wz_of (mx x) o == b.bw /\ M.tag_of (mx x) o == b.bt /\ M.col_of (mx x) o == hcol x b o /\
                    L.length b.bf == b.bw /\ (forall (i: nat). i < b.bw ==> M.field (mx x) o i == vi b.bf i)))
  = holds_def x d;
    iu_def x o

/// Not described: not in use.
let not_iu (x: config pc) (d: dsc) (o: nat)
  : Lemma (requires holds x d /\ None? (d.db o)) (ensures iu x o == false)
  = holds_def x d

/// A block is its own address.
let res_blk (m: M.mheap) (o: nat) : Lemma (requires M.is_block m o) (ensures M.resolve m o == Some o) = ()

/// An infix pointer `k + 2` into a closure of three fields whose second is
/// the infix header of offset 2.
let res_infix (m: M.mheap) (k: nat)
  : Lemma (requires M.well_formed m /\ M.is_block m k /\ M.tag_of m k == M.closure_tag /\ M.wz_of m k == 3 /\
                    M.field m k 1 == M.infix_word 2)
          (ensures M.resolve m (k + 2) == Some k)
  = assert (M.covers m k (k + 2));
    if M.is_block m (k + 2) then assert (M.covers m (k + 2) (k + 2));
    assert_norm (M.infix_hdr (M.infix_word 2) == Some 2)

/// ---------------------------------------------------------------------------
/// Reachability
/// ---------------------------------------------------------------------------

/// A set holding every outside reference, closed under edges, holds every
/// reachable block.
let rec reach_in_r (w: M.world) (s: nat -> prop) (o: nat) (r: M.reach w o)
  : Lemma (requires (forall (o: nat). M.outside_ref w o ==> s o) /\
                    (forall (o o': nat). s o /\ M.major_edge w.M.maj o o' ==> s o'))
          (ensures s o) (decreases r)
  = match r with
    | M.RBase _ _ -> ()
    | M.RStep o0 _ r0 _ -> reach_in_r w s o0 r0

let reach_in (w: M.world) (s: nat -> prop)
  : Lemma (requires (forall (o: nat). M.outside_ref w o ==> s o) /\
                    (forall (o o': nat). s o /\ M.major_edge w.M.maj o o' ==> s o'))
          (ensures forall (o: nat). M.reachable w o ==> s o)
  = let one (o: nat) : Lemma (M.reachable w o ==> s o)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (reach_in_r w s o)) in
    FStar.Classical.forall_intro one

/// A root resolving to `o`: reachable.
let reach_root (w: M.world) (a o: nat)
  : Lemma (requires L.memP (M.VPtr (M.Major a)) w.M.roots /\ M.resolve w.M.maj a == Some o)
          (ensures M.reachable w o)
  = let r : M.reach w o = M.RBase o () in
    assert (M.reachable w o)

/// Field `i` of a reachable block resolving to `o'`: reachable.
let reach_field (w: M.world) (o i a o': nat)
  : Lemma (requires M.reachable w o /\ M.ptr_field w.M.maj o i /\ M.field w.M.maj o i == M.VPtr (M.Major a) /\
                    M.resolve w.M.maj a == Some o')
          (ensures M.reachable w o')
  = eliminate exists (r: M.reach w o). True
    with begin
      let r' : M.reach w o' = M.RStep o o' r () in
      assert (M.reachable w o')
    end

/// ---------------------------------------------------------------------------
/// The initial configuration
/// ---------------------------------------------------------------------------

let ms0 : minor_state = minor_init (FStar.Seq.create GC.Gen.Base.minor_heap_size 0uy)

let yinit_ms0 (n: nat) : Lemma (Y.yinit n == ms0) = ()

let d0 : dsc = { dk = DI; db = (fun _ -> None); dys = ms0; dym = M.empty_heap ywords; drt = []; dj = 0 }

let init_holds ()
  : Lemma (requires cok)
          (ensures holds (init_config pc msize ywords) d0)
  = holds_def (init_config pc msize ywords) d0;
    let x = init_config pc msize ywords in
    cok_init ();
    let (h, st) = pa.T.init msize in
    eliminate exists (m: M.mheap). brepr m h /\ T.init_post pa msize h st m
    with begin
      PIn.wf_heq m (cabs h);
      assert (forall (o: nat). iu x o == T.in_use pa st h m o)
    end;
    Y.yinit_ok' ywords;
    yinit_ms0 ywords;
    PWP.kinds_init ()
