/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFFits - first-fit's capacity condition
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  The capacity condition (`Iface.capacity`) of the
/// first-fit component: the phase's invariant holds and a block on the free
/// list (`FreeList.fl_cell`: a blue block of the walk with room for a link)
/// has at least `sz + 1` words, header included.
///   - `fffits_room`: room holds whenever the condition does, in every
///     phase.  The invariant keeps the free list ascending, so exactly the
///     cells are on it (`FreeList.Ascending.fl_ascending_exact`), and akhil's
///     `Allocator.Exact.alloc_spec_fits_succeeds` finds a fit; the phase
///     changes only the new header's colour (`Allocator.Phase.alloc_at_fields`);
///   - `fffits_init`: the condition holds on the initial heap, for a request
///     of one field, with no assumption on the configuration (the initial
///     block has at least one field, `FFAlloc.init_facts`).

module GC.Spec.Top.FFFits

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Top.Word
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
module M = GC.Spec.Top.Heap
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module EX = GC.Spec.Allocator.Exact
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module FB = GC.Spec.Top.FFBytes
module FAO = GC.Spec.Top.FFAllocOk
module FW = GC.Spec.Top.FFWrite
module FIn = GC.Spec.Top.FFInit

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A free-list block of at least `sz + 1` words.
let fl_fit (g: heap) (sz: nat) : prop =
  exists (x: obj_addr). FL.fl_cell g x /\ U64.v (wosize_of_object x g) >= sz

let fffits : T.capacity heap ffk ffst = fun ph s h sz ->
  ffa.T.inv ph h s /\ fl_fit (gl h s) sz

/// **Room holds whenever the condition does.**
#push-options "--z3rlimit 40"
let fffits_room (ph: T.phase U64.t) (s: ffst) (h: heap) (sz: M.size_t)
  : Lemma (fffits ph s h sz ==> ffa.T.room ph s h sz == true)
  = if FStar.IndefiniteDescription.strong_excluded_middle (fffits ph s h sz) then begin
      let g = gl h s in
      FW.fshape_inv ph h s;
      FAO.ready_of ph g s.fp;
      FLA.fl_ascending_valid g s.fp;
      FLA.fl_ascending_exact g s.fp;
      let x = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                (fun x -> FL.fl_cell g x /\ U64.v (wosize_of_object x g) >= sz) in
      assert_norm (U64.v 0UL < 256);
      EX.alloc_spec_fits_succeeds g s.fp sz x 0UL;
      tg_v 0;
      AP.alloc_at_fields (gph ph) g s.fp sz (tg 0)
    end
#pop-options

/// **The condition holds on the initial heap.**
#push-options "--z3rlimit 40"
let fffits_init () : Lemma (T.fits_init byte_rep ffa fffits)
  = let (h, s) = ffa.T.init msize in
    set_low_self h;
    FIn.idle ();
    FIn.objs ();
    init_facts ();
    assert (FL.fl_cell h FIn.x0);
    assert (fffits T.Idle s h 1);
    assert (bsize_ok msize)
#pop-options
