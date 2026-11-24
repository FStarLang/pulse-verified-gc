/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cycle.AllocTagged - the program's allocation with a tag, in
/// the page cycle
/// ---------------------------------------------------------------------------
///
/// Plan §29.2.  The page cycle's allocation events (`PAlloc`, `SAlloc`,
/// `CAlloc`, `CSAlloc`) allocate with tag 0 (`PA.alloc`).  akhil's take any
/// tag but the infix tag (`MC.Alloc`).  The page allocator with a tag
/// (`AT.alloc_tag`), which `GC.Impl.Pages.AllocInc.alloc_ph` computes for
/// every tag, gives the cycle's events their facts at every tag but 249:
///
///   * while marking (`mark_alloc_tag_facts`): what `CS.mark_alloc_facts`
///     gives at tag 0, the heap facts the account of the marking run needs;
///   * the page invariant once the fields are written, while marking
///     (`mark_tag_inv`) and mid-sweep (`sw_tag_inv`), from
///     `AllocTagOk.alloc_tag_marking` and `alloc_tag_sweeping`.
///
/// The fields' condition is `AT.fields_written_away`, the one the minor
/// collection's copies meet: in a scannable object, values the caller may
/// store, none a pointer into the object's own body (`away`); in a no-scan
/// object, anything.

module GC.Spec.Pages.Cycle.AllocTagged

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag
module ATO = GC.Spec.Pages.AllocTagOk
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module MPA = GC.Spec.MarkPhase.Alloc
module SPI = GC.Spec.SweepPhase.Intrinsic
module F = GC.Spec.Pages.Fill
module B = GC.Spec.Pages.Blocks
module CS = GC.Spec.Pages.Cycle.State
module PI = GC.Spec.Pages.PromoteInst

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The fields of `x` cleared are written as the caller may.
#push-options "--z3rlimit 30"
let cleared_away (free: free_def) (g': heap) (x: obj_addr)
  : Lemma (AT.fields_written_away free g' (B.zeros g' (U64.v x) (U64.v (wosize_of_object x g'))) x)
  = let n = U64.v (wosize_of_object x g') in
    let aux (a: hp_addr)
      : Lemma (read_word (B.zeros g' (U64.v x) n) a ==
               (if U64.v x <= U64.v a && U64.v a < U64.v x + n * 8 then 0UL else read_word g' a))
      = B.zeros_read g' (U64.v x) n a
    in
    FStar.Classical.forall_intro aux
#pop-options

/// **Allocation with a tag while marking, the heap facts**: those of
/// `CS.mark_alloc_facts` at tag 0.
#push-options "--z3rlimit 40"
let mark_alloc_tag_facts (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires PMP.mark_inv g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = AT.alloc_tag I.Marking g st wz tag in
                    o =!= 0UL ==>
                    U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    (let x : obj_addr = o in
                     Seq.mem x (objects zero_addr g') /\ is_black x g' /\
                     ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                     MPA.keeps_blocks free_stw g g' /\
                     (forall (y: obj_addr). in_use (MPA.free_or_new x) g' y == in_use free_stw g y) /\
                     no_infix_block g' /\ blocks_fit g')))
  = ATO.alloc_tag_marking g st wz tag;
    let (g', st', o) = AT.alloc_tag I.Marking g st wz tag in
    if o <> 0UL then begin
      let x : obj_addr = o in
      let kb (y: obj_addr)
        : Lemma (requires in_use free_stw g y)
                (ensures Seq.mem y (objects zero_addr g') /\
                         read_word g' (hd_address y) == read_word g (hd_address y) /\
                         SPI.same_block g g' (hd_address y))
        = CS.kept_same_block g g' y
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires kb);
      let g'' = B.zeros g' (U64.v x) (U64.v (wosize_of_object x g')) in
      cleared_away free_stw g' x;
      assert (PMP.mark_inv g'' st');
      F.cleared_written g' x;
      wf_with_parts ();
      CS.fill_back g' g'' x
    end
#pop-options

/// **The `Marking` page invariant once the fields are written.**
let mark_tag_inv (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
                 (g1: heap) (st1: pstate) (obj: obj_addr) (g': heap)
  : Lemma (requires PMP.mark_inv g st /\ U64.v tag <> 249 /\
                    AT.alloc_tag I.Marking g st wz tag == (g1, st1, (obj <: U64.t)) /\
                    AT.fields_written_away free_stw g1 g' obj)
          (ensures PMP.mark_inv g' st1)
  = ATO.alloc_tag_marking g st wz tag

/// **The mid-sweep invariant once the fields are written**, with what the
/// caller may write read at the page map before the allocation.
let sw_tag_inv (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
               (g1: heap) (st1: pstate) (obj: obj_addr) (g': heap)
  : Lemma (requires MS.pages_ok_sw g st /\ U64.v tag <> 249 /\
                    AT.alloc_tag I.Sweeping g st wz tag == (g1, st1, (obj <: U64.t)) /\
                    AT.fields_written_away (MS.free_sw st.pm) g1 g' obj)
          (ensures MS.pages_ok_sw g' st1)
  = ATO.alloc_tag_sweeping g st wz tag;
    PI.sw_written st.pm st1.pm g1 g' obj
