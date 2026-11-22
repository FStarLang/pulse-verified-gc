/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFSweep - akhil's fused sweep as the sweep component
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  The sweep record over the first-fit component:
///   - the progress is akhil's cursor; it starts at `zero_addr`
///     (`FusedSweep.sweep_start`);
///   - a step is one `FusedSweep.sweep_step` from the derived state
///     (`SweepPhase.Intrinsic.state_at`); the words it frees are the white
///     block's at the cursor, header included;
///   - it is done when no block has room after the cursor
///     (`SweepPhase.Intrinsic.sweep_done`).
/// This module: the definitions, and the start and end clauses of
/// `Iface.sweep_ok`.  The start is akhil's `sweep_inv_incremental_start`,
/// from the end of marking read on the bytes: no grey block
/// (`Mark.noGreyObjects`) and no black block pointing at a white one
/// (`Mark.tri_color_invariant`, from the model's `dark_closed`).

module GC.Spec.Top.FFSweep

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPE = GC.Spec.SweepPhase.Intrinsic.End
module SPU = GC.Spec.SweepPhase.Util
module Mark = GC.Spec.Mark
module FI = GC.Spec.Top.FFInst
module PIn = GC.Spec.Top.PagesInst

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The component
/// ---------------------------------------------------------------------------

/// The words a step at `c` frees: the block's, header included, when it is
/// white.
let ffw (g: heap) (c: U64.t) : nat =
  if U64.v c + 8 < heap_size && U64.v c % 8 = 0 && SPI.white_at g (c <: hp_addr)
  then FSI.wz_at g (c <: hp_addr) + 1 else 0

let ffstart (h: heap) (s: ffst) : GTot (U64.t & ffst) = (FS.sweep_start.FS.cursor, s)

let ffstep (c: U64.t) (h: heap) (s: ffst) : GTot (U64.t & heap & ffst & T.step_result) =
  let g = gl h s in
  let st = SPI.state_at g c in
  if U64.v c + 8 < heap_size && FS.can_sweep g st then begin
    let (g', fp', st') = FS.sweep_step g s.fp st in
    (st'.FS.cursor, g', { fp = fp'; lo = low g' }, { T.units = 1; T.freed_words = ffw g c })
  end
  else (c, h, s, { T.units = 0; T.freed_words = 0 })

let ffdone (c: U64.t) : bool = SPI.sweep_done c

let ffsweep : T.sweep heap ffk ffa = { T.start = ffstart; T.step = ffstep; T.done = ffdone }

/// ---------------------------------------------------------------------------
/// The end of marking, read on the bytes
/// ---------------------------------------------------------------------------

/// No grey block.
let no_grey_b (m: M.mheap) (g: heap)
  : Lemma (requires R.heq m (cabs g) /\ T.no_grey m) (ensures Mark.noGreyObjects g)
  = let one (x: obj_addr) : Lemma (Seq.mem x (objects zero_addr g) ==> not (is_gray x g))
      = if Seq.mem x (objects zero_addr g) then begin
          obj_maddr g x;
          abs_header g (maddr x);
          is_gray_iff x g
        end in
    FStar.Classical.forall_intro one

let dc_elim (m: M.mheap) (o i a x: nat)
  : Lemma (requires T.dark_closed m /\ M.is_block m o /\ M.dark (M.col_of m o) /\ M.ptr_field m o i /\
                    M.field m o i == M.VPtr (M.Major a) /\ M.resolve m a == Some x)
          (ensures M.col_of m x =!= M.White)
  = ()

/// No black block points at a white one.
#push-options "--z3rlimit 40"
let tri_b (m: M.mheap) (g: heap)
  : Lemma (requires R.heq m (cabs g) /\ well_formed_heap g /\ T.dark_closed m)
          (ensures Mark.tri_color_invariant g)
  = let one (obj child: obj_addr)
      : Lemma (Seq.mem obj (objects zero_addr g) ==> is_black obj g ==> ~(is_no_scan obj g) ==>
               points_to g obj child ==> ~(is_white (resolve_object child g) g))
      = if Seq.mem obj (objects zero_addr g) && is_black obj g && not (is_no_scan obj g) &&
           FStar.IndefiniteDescription.strong_excluded_middle (points_to g obj child) then begin
          Mark.colors_exclusive obj g;
          target_model g obj child;
          field_to_exists g obj child;
          let i = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun i -> field_to g obj child i) in
          field_model g obj child i;
          let o = maddr obj in
          obj_maddr g obj;
          abs_header g o;
          is_black_iff obj g;
          is_no_scan_spec obj g;
          no_scan_tag_val ();
          let r = resolve_object child g in
          obj_maddr g r;
          abs_header g (maddr r);
          is_white_iff r g;
          assert (M.is_block m o /\ M.col_of m o == M.Black);
          assert (M.ptr_field m o i);
          assert (M.field m o i == M.VPtr (M.Major (ptr_b child)));
          PIn.resolve_heq m (cabs g) (ptr_b child);
          dc_elim m o i (ptr_b child) (maddr r);
          assert (M.col_of (cabs g) (maddr r) =!= M.White);
          maddr_obj (maddr r)
        end in
    FStar.Classical.forall_intro_2 one
#pop-options

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let start_m (h: heap) (s: ffst) (m: M.mheap)
  : Lemma (requires brepr m h) (ensures T.sweep_start_m ffsweep h s m)
  = let pre () : Lemma (requires ffa.T.inv T.Marking h s /\ M.well_formed m /\ T.no_grey m /\ T.dark_closed m)
                       (ensures (let (p, s') = ffsweep.T.start h s in
                                 ffa.T.inv (T.Sweeping p) h s' /\
                                 (forall (o: nat). ffa.T.free s' h o == ffa.T.free s h o) /\
                                 (forall (o: nat). T.in_use ffa s h m o ==> ffk.T.unswept p o == true)))
      = let g = gl h s in
        FI.heq_low m h s;
        reveal_opaque (`%mshape) (mshape g s.fp);
        no_grey_b m g;
        tri_b m g;
        SPI.sweep_inv_incremental_start g s.fp;
        reveal_opaque (`%sshape) (sshape g s.fp FS.sweep_start.FS.cursor);
        assert (U64.v FS.sweep_start.FS.cursor == base)
    in
    FStar.Classical.move_requires pre ()
#pop-options

/// ---------------------------------------------------------------------------
/// The end
/// ---------------------------------------------------------------------------

/// A block in use has a field, so it ends before a done cursor.
let used_below (g: heap) (o: nat) (c: U64.t)
  : Lemma (requires nz g /\ M.is_block (cabs g) o /\ M.col_of (cabs g) o <> M.Blue /\ SPI.sweep_done c /\
                    M.well_formed (cabs g))
          (ensures pos o < U64.v c)
  = mblock (cabs g) g o;
    mhdr (cabs g) g o;
    is_blue_iff (obj_of o) g;
    obj_of_v o;
    assert (M.wz_of (cabs g) o >= 1)

#push-options "--z3rlimit 40"
let done_m (c: U64.t) (h: heap) (s: ffst) (m: M.mheap)
  : Lemma (requires brepr m h) (ensures T.sweep_done_m ffsweep c h s m)
  = let pre () : Lemma (requires ffa.T.inv (T.Sweeping c) h s /\ M.well_formed m /\ ffsweep.T.done c == true)
                       (ensures ffa.T.inv T.Idle h s /\
                                (forall (o: nat). T.in_use ffa s h m o ==> ffk.T.unswept c o == false) /\
                                (forall (o: nat). M.is_block m o ==> not (M.dark (M.col_of m o))))
      = let g = gl h s in
        FI.heq_low m h s;
        reveal_opaque (`%sshape) (sshape g s.fp c);
        assert (idle_at g s.fp c);
        reveal_opaque (`%ishape) (ishape g s.fp);
        SPE.sweep_inv_incremental_end g s.fp c;
        PIn.wf_heq m (cabs g);
        let iu (o: nat) : Lemma (T.in_use ffa s h m o ==> ffk.T.unswept c o == false)
          = if T.in_use ffa s h m o then begin
              FI.in_use_used m h s g o;
              used_below g o c
            end in
        FStar.Classical.forall_intro iu;
        let nd (o: nat) : Lemma (M.is_block m o ==> not (M.dark (M.col_of m o)))
          = if M.is_block m o then begin
              mblock (cabs g) g o;
              mhdr (cabs g) g o;
              is_white_iff (obj_of o) g;
              is_blue_iff (obj_of o) g
            end in
        FStar.Classical.forall_intro nd
    in
    FStar.Classical.move_requires pre ()
#pop-options
