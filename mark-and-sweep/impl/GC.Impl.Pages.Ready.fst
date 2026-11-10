/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Ready - what the allocator's fast path reads from the state
/// ---------------------------------------------------------------------------
///
/// The prototype's and OCaml 5's small allocation takes the first free slot
/// of the first page on its class's list without checking the list: the
/// page is a pool page of the class with a free slot, and its free-slot
/// list starts at a slot.  The specification's allocator (`Pool.pop_as`) is
/// total, so it checks both, and finding the slot from the list entry takes
/// a division.  `heads_ready st` is those facts, of the state alone; under
/// it the checks always pass, and the Pulse `pop` skips them
/// (`GC.Impl.Pages.Pool`).
///
/// `heads_ready` follows from the allocator's invariant in both phases:
/// `pages_ok` (`pages_ok_ready`) and the marking phase's `pages_ok_mc`
/// (`mc_ready`), which are the preconditions of `alloc_meets` and
/// `alloc_col_correct`.  So asking it of the Pulse allocator loses nothing.

module GC.Impl.Pages.Ready

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module AP = GC.Spec.Pages.AllocPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The head of class `c`'s list is 0, or names a pool page of class `c`
/// with a free slot, whose free-slot list starts at a slot.
let head_ready (st: pstate) (c: nat{c < n_cls}) : prop =
  Seq.length st.avail == n_cls /\
  (let hd = Seq.index st.avail c in
   hd <> 0UL ==>
   (U64.v hd - 1 < n_pages /\
    (let e = entry st.pm (U64.v hd - 1) in
     e.kind == Pool c /\ e.nfree > 0 /\
     (exists (k: nat). k < n_slots c /\ U64.v e.free_head == slot_obj (U64.v hd - 1) c k))))

let heads_ready (st: pstate) : prop =
  forall (c: nat{c < n_cls}). head_ready st c

#push-options "--fuel 1"
/// The first page of a nonempty chain.
let chain_head (pm: page_map) (hd: U64.t) (ps: list nat)
  : Lemma (requires page_chain pm hd ps /\ hd <> 0UL)
          (ensures Cons? ps /\ Cons?.hd ps < n_pages /\ U64.v hd == Cons?.hd ps + 1)
  = ()

/// The first slot of a nonempty free-slot chain.
let slots_head (g: heap) (i: nat) (c: nat{c < n_cls}) (hd: U64.t) (ks: list nat)
  : Lemma (requires slot_chain g i c hd ks /\ Cons? ks)
          (ensures Cons?.hd ks < n_slots c /\ U64.v hd == slot_obj i c (Cons?.hd ks))
  = ()

let mem_head (#a: eqtype) (xs: list a)
  : Lemma (requires Cons? xs) (ensures L.mem (Cons?.hd xs) xs) = ()

let length_pos (#a: Type) (xs: list a)
  : Lemma (requires L.length xs > 0) (ensures Cons? xs) = ()
#pop-options

let head_ready_of (g: heap) (st: pstate) (c: nat{c < n_cls})
  : Lemma (requires avail_ok st /\
                    (forall (i: nat{i < n_pages}). pool_list_ok g st.pm i))
          (ensures head_ready st c)
  = let hd = Seq.index st.avail c in
    if hd <> 0UL then begin
      eliminate exists (ps: list nat).
        page_chain st.pm hd ps /\ L.noRepeats ps /\
        (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot st.pm c p)
      with begin
        chain_head st.pm hd ps;
        let p = Cons?.hd ps in
        mem_head ps;
        assert (has_free_slot st.pm c p);
        let e = entry st.pm p in
        assert (pool_list_ok g st.pm p);
        eliminate exists (ks: list nat).
          slot_chain g p c e.free_head ks /\ L.noRepeats ks /\
          (forall (k: nat). k < n_slots c ==> (L.mem k ks <==> slot_free g p c k)) /\
          e.nfree == L.length ks
        with (length_pos ks; slots_head g p c e.free_head ks)
      end
    end

/// **The invariant gives the fast path its facts.**
let pages_ok_ready (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st) (ensures heads_ready st)
  = reveal_opaque (`%pages_ok) pages_ok;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (head_ready_of g st))

/// ... and so does the marking phase's invariant.
let mc_ready (g: heap) (st: pstate)
  : Lemma (requires AP.pages_ok_mc g st) (ensures heads_ready st)
  = eliminate exists (ys: list GC.Spec.Base.obj_addr).
      GC.Spec.Pages.ColourFacts.live_list g ys /\ pages_ok (GC.Spec.Pages.Recolour.whiten g ys) st
    with pages_ok_ready (GC.Spec.Pages.Recolour.whiten g ys) st
