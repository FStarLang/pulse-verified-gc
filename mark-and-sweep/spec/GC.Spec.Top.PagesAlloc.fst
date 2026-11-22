/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesAlloc - the page allocator, as a component of the
/// top-level specification
/// ---------------------------------------------------------------------------
///
/// The page allocator of GC.Spec.Pages.* in incremental mode (plan §28:
/// `GC.Spec.Pages.Incr`), on the byte heap, through the byte representation
/// (GC.Spec.Top.ByteRep):
///   - allocation is the tagged allocator in the phase's colour
///     (`AllocTag.alloc_tag`), from the phase's page invariant
///     (`MidSweepAlloc.inv_sw`: `Idle` and `Marking` as `Pages.Allocator`
///     has them, `pages_ok_sw` mid-sweep);
///   - free means blue, read from the header (`pfree`);
///   - the sweep's progress is the page map and the cursor (`pprog`); a
///     model word is unswept when its page is (`G.uw`);
///   - the bytes below `zero_addr`, which the representation does not read,
///     are kept in the allocator's state (GC.Spec.Top.Low).
///
/// This module: the definitions, and what one allocation does to the byte
/// heap in every phase (`bfacts`), from the page modules' lemmas.

module GC.Spec.Top.PagesAlloc

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module L = FStar.List.Tot
module W = GC.Spec.Walk
module G = GC.Spec.Pages.Graft
module A = GC.Spec.Pages.Alloc
module B = GC.Spec.Pages.Blocks
module AT = GC.Spec.Pages.AllocTag
module ATO = GC.Spec.Pages.AllocTagOk
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module MSA = GC.Spec.Pages.MidSweepAlloc
module NO = GC.Spec.Pages.NewOnly
module PI = GC.Spec.Pages.Promote.Idle
module Incr = GC.Spec.Pages.Incr
module Init = GC.Spec.Pages.Init

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The component
/// ---------------------------------------------------------------------------

/// The sweep's progress: the page map (whose swept bits say what is left)
/// and the cursor of the next slice.
noeq type pprog = { ppm: page_map; cur: nat }

let punswept (p: pprog) (o: nat) : bool = G.uw p.ppm (pos o)

let pk : T.sweep_kind = { T.progress = pprog; T.unswept = punswept }

let iph (ph: T.phase pprog) : I.phase =
  match ph with
  | T.Idle -> I.Idle
  | T.Marking -> I.Marking
  | T.Sweeping _ -> I.Sweeping

/// The page allocator's state, and the bytes below the heap.
noeq type pst = { ps: pstate; lo: low_t }

/// The heap the page functions run on.
let gl (g: heap) (s: pst) : heap = set_low g s.lo

let pinv (ph: T.phase pprog) (g: heap) (s: pst) : prop =
  MSA.inv_sw (iph ph) (gl g s) s.ps /\
  (match ph with
   | T.Sweeping p -> MS.same_swept p.ppm s.ps.pm /\ Incr.swept_below s.ps.pm p.cur
   | _ -> True)

/// Free: a blue block.
let pfree (s: pst) (g: heap) (o: nat) : GTot bool =
  match abs_hd g o with Some h -> h.M.col = M.Blue | None -> false

/// A model tag, as a header's tag.
let tg (tag: M.tag_t) : AT.tag_t = assert_norm (256 < pow2 64); U64.uint_to_t tag

let tg_v (tag: M.tag_t) : Lemma (U64.v (tg tag) == tag) = assert_norm (256 < pow2 64)

let palloc (ph: T.phase pprog) (g: heap) (s: pst) (sz: M.size_t) (tag: M.tag_t) : GTot (heap & pst & T.result) =
  let (g', st', o) = AT.alloc_tag (iph ph) (gl g s) s.ps sz (tg tag) in
  if o = 0UL then (g, s, T.NoRoom)
  else (g', { ps = st'; lo = low g' }, T.Ok (maddr o))

/// Room: the allocation succeeds (the tag plays no part).
let proom (ph: T.phase pprog) (s: pst) (g: heap) (sz: M.size_t) : GTot bool =
  let (_, _, o) = A.alloc (gl g s) s.ps sz in o <> 0UL

let zero_heap : heap = Seq.create heap_size 0uy

let pinit (n: nat) : GTot (heap & pst) =
  let g = Init.init_heap zero_heap in (g, { ps = Init.init_state; lo = low g })

let pa : T.allocator heap pk = {
  T.state = pst;
  T.init = pinit;
  T.inv = pinv;
  T.free = pfree;
  T.room = proom;
  T.alloc = palloc;
}

/// ---------------------------------------------------------------------------
/// One allocation, on the byte heap, in every phase
/// ---------------------------------------------------------------------------

/// What the collector counts as free while the fields are written.
let free_of (ph: I.phase) (st: pstate) : free_def =
  match ph with
  | I.Sweeping -> MS.free_sw st.pm
  | _ -> free_stw

let bpost (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (o: U64.t)
  : prop =
  MS.same_swept st.pm st'.pm /\
  (o == 0UL ==> g' == g /\ st' == st) /\
  (o =!= 0UL ==>
     U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
     (let x : obj_addr = o in
      U64.v x + wz * 8 <= heap_size /\
      Seq.mem x (objects zero_addr g') /\
      U64.v (wosize_of_object x g') == wz /\ tag_of_object x g' == tag /\
      color_of_object x g' == I.new_colour ph /\
      not (MS.unswept_at st.pm x) /\
      ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
      NO.new_only g g' o /\
      (forall (g'': heap). AT.fields_written_away (free_of ph st') g' g'' x ==> MSA.inv_sw ph g'' st')) /\
     I.others_unchanged g g')

/// Every page swept: no word is unswept.
let all_swept_uw (st: pstate) (a: nat) : Lemma (requires PMP.all_swept st) (ensures not (G.uw st.pm a))
  = if U64.v zero_addr <= a && a < pages_end then begin page_of_spec a; MS2.uw_swept st.pm a end
    else MS2.uw_out st.pm a

let all_swept_same (st st': pstate)
  : Lemma (requires PMP.all_swept st /\ PMP.all_swept st') (ensures MS.same_swept st.pm st'.pm)
  = ()

/// Rewriting the header of `x` at its size keeps the objects, and every
/// other object's colour.
let hdr_rewrite (g: heap) (x: obj_addr) (v: U64.t)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ getWosize v == getWosize (read_word g (hd_address x)))
          (ensures (let g' = write_word g (hd_address x) v in
                    objects zero_addr g' == objects zero_addr g /\
                    (forall (y: obj_addr). y <> x ==> color_of_object y g' == color_of_object y g)))
  = W.walk_write g zero_addr (hd_address x) v;
    let g' = write_word g (hd_address x) v in
    let col (y: obj_addr) : Lemma (y <> x ==> color_of_object y g' == color_of_object y g)
      = if y <> x then begin
          hd_address_spec x; hd_address_spec y;
          read_write_different g (hd_address x) (hd_address y) v;
          color_of_object_spec y g; color_of_object_spec y g'
        end in
    FStar.Classical.forall_intro col

let new_only_rewrite (g g1: heap) (x: obj_addr) (v: U64.t)
  : Lemma (requires NO.new_only g g1 x /\ Seq.mem x (objects zero_addr g1) /\
                    getWosize v == getWosize (read_word g1 (hd_address x)))
          (ensures NO.new_only g (write_word g1 (hd_address x) v) x)
  = hdr_rewrite g1 x v;
    let g2 = write_word g1 (hd_address x) v in
    let one (y: obj_addr) : Lemma (y <> x ==> (is_blue y g2 <==> is_blue y g1))
      = is_blue_iff y g1; is_blue_iff y g2 in
    FStar.Classical.forall_intro one

/// While marking.
let bfacts_marking (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires PMP.mark_inv g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = AT.alloc_tag I.Marking g st wz tag in bpost I.Marking g st wz tag g' st' o))
  = ATO.alloc_tag_marking g st wz tag;
    let (g', st', o) = AT.alloc_tag I.Marking g st wz tag in
    all_swept_same st st';
    if o <> 0UL then begin
      let x : obj_addr = o in
      all_swept_uw st (U64.v x - 8);
      is_black_iff x g'; is_blue_iff x g';
      let nw (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr g') /\ ~(is_blue y g') /\ U64.v y <> U64.v o ==>
                                    Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
        = assert (in_use free_stw g' y == (in_use free_stw g y || y = x)) in
      FStar.Classical.forall_intro nw
    end

/// While sweeping.
#push-options "--z3rlimit 40"
let bfacts_sweeping (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires MS.pages_ok_sw g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = AT.alloc_tag I.Sweeping g st wz tag in bpost I.Sweeping g st wz tag g' st' o))
  = ATO.alloc_tag_sweeping g st wz tag;
    MS.pages_ok_sw_elim g st;
    let zs = MS.dead_list g st.pm in
    MS.alloc_facts g st zs wz;
    let (gA, stA, oA) = A.alloc g st wz in
    let (g', st', o) = AT.alloc_tag I.Sweeping g st wz tag in
    assert_norm (I.new_colour I.Sweeping == White);
    AT.alloc_col_tag_wz White tag g st wz;
    assert (st' == stA /\ o == oA);
    if o <> 0UL then begin
      let x : obj_addr = o in
      is_white_iff x g'; is_blue_iff x g';
      hd_address_spec x;
      let v = AT.tagged_hdr wz White tag in
      assert (g' == B.wr gA (U64.v o - 8) v);
      assert (B.wr gA (U64.v o - 8) v == write_word gA (hd_address x) v);
      wosize_of_object_spec x gA;
      makeHeader_getWosize (U64.uint_to_t wz) White tag;
      new_only_rewrite g gA x v
    end
#pop-options

/// The mid-sweep allocator's facts, at `Idle` (every page swept).
let fwa_idle (st: pstate) (g' g'': heap) (x: obj_addr)
  : Lemma (requires PMP.all_swept st /\ AT.fields_written_away free_stw g' g'' x)
          (ensures AT.fields_written_away (MS.free_sw st.pm) g' g'' x)
  = let eq (y: obj_addr) : Lemma (in_use (MS.free_sw st.pm) g'' y == in_use free_stw g'' y)
      = PI.swept_free st g'' y in
    FStar.Classical.forall_intro eq

#push-options "--z3rlimit 40"
let bfacts_idle (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires PA.inv I.Idle g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = AT.alloc_tag I.Idle g st wz tag in bpost I.Idle g st wz tag g' st' o))
  = PI.idle_sw g st;
    PI.idle_is_sweeping g st wz tag;
    bfacts_sweeping g st wz tag;
    assert_norm (I.new_colour I.Idle == White);
    assert_norm (I.new_colour I.Sweeping == White);
    let (g', st', o) = AT.alloc_tag I.Idle g st wz tag in
    assert (PMP.all_swept st');
    if o <> 0UL then begin
      let x : obj_addr = o in
      let fill (g'': heap)
        : Lemma (AT.fields_written_away free_stw g' g'' x ==> MSA.inv_sw I.Idle g'' st')
        = if FStar.IndefiniteDescription.strong_excluded_middle (AT.fields_written_away free_stw g' g'' x) then begin
            fwa_idle st' g' g'' x;
            MS2.sw_end g'' st'
          end in
      FStar.Classical.forall_intro fill
    end
#pop-options

let bfacts (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires MSA.inv_sw ph g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = AT.alloc_tag ph g st wz tag in bpost ph g st wz tag g' st' o))
  = match ph with
    | I.Idle -> bfacts_idle g st wz tag
    | I.Marking -> bfacts_marking g st wz tag
    | I.Sweeping -> bfacts_sweeping g st wz tag
