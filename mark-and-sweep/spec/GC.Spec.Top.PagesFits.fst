/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesFits - the page allocator's capacity condition
/// ---------------------------------------------------------------------------
///
/// The capacity condition (`Iface.capacity`) of the page allocator: the
/// phase's page invariant holds and something fits, as the page modules say
/// it (`Theorems.no_fit` fails: for a small request a free page or a page of
/// its class with a free slot; for a large one a large free block or a run
/// of free pages).
///   - `pfits_room`: room holds whenever the condition does, in every state
///     (`Allocator.alloc_no_fit`, `MidSweepAlloc.alloc_sw_ok`);
///   - `pfits_init`: the condition holds on the initial heap, for a request
///     of one field, when there is a page (`n_pages > 0`; the page count is
///     a function of the abstract `heap_size`, so this is an assumption on
///     the configuration, as in the page modules' own witnesses).

module GC.Spec.Top.PagesFits

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module A = GC.Spec.Pages.Alloc
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module MSA = GC.Spec.Pages.MidSweepAlloc
module Th = GC.Spec.Pages.Theorems
module Init = GC.Spec.Pages.Init

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let pfits : T.capacity heap pk pst = fun ph s h sz ->
  pinv ph h s /\ sz + 1 < pow2 54 /\ ~(Th.no_fit (gl h s) s.ps (sz + 1))

let pfits_room (ph: T.phase pprog) (s: pst) (h: heap) (sz: M.size_t)
  : Lemma (pfits ph s h sz ==> pa.T.room ph s h sz == true)
  = if FStar.IndefiniteDescription.strong_excluded_middle (pfits ph s h sz) then
      match iph ph with
      | I.Sweeping -> MSA.alloc_sw_ok (gl h s) s.ps sz
      | _ -> PA.alloc_no_fit (iph ph) (gl h s) s.ps sz

let init_inv () : Lemma (let (h, s) = pa.T.init msize in pinv T.Idle h s)
  = let (h, s) = pa.T.init msize in
    A.init_alloc_pre zero_heap;
    set_low_self h;
    assert (PMP.all_swept Init.init_state)

let init_fits () : Lemma (requires n_pages > 0) (ensures ~(Th.no_fit (Init.init_heap zero_heap) Init.init_state 2))
  = cls_bounds 0;
    assert ((entry Init.init_state.pm 0).kind == Free)

let pfits_init () : Lemma (requires n_pages > 0) (ensures T.fits_init byte_rep pa pfits)
  = let (h, s) = pa.T.init msize in
    init_inv ();
    init_fits ();
    set_low_self h;
    assert_norm (2 < pow2 54);
    assert (pfits T.Idle s h 1);
    assert (bsize_ok msize)
