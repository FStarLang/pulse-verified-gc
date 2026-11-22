/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWrite - the first-fit invariant across one word changed by
/// the program or the mark
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  The invariant of the first-fit component at a phase
/// (`fshape`), on the heap the first-fit functions run on, across:
///   - a program write (`SweepPhase.Mutator.program_write`: a word of the
///     body of a block in use, not a closure, a storable value):
///       * mid-sweep, akhil's `write_sweep_phase`;
///       * idle, the same at the cursor where the sweep stopped;
///       * while marking, colour-blind (`write_marking`, the
///         well-formedness part of akhil's proof);
///   - while marking, the recolouring of a block in use to a colour other
///     than blue (`recolour_marking`, akhil's `recolour_one`).

module GC.Spec.Top.FFWrite

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.FFAlloc
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module AP = GC.Spec.Allocator.Phase
module FLA = GC.Spec.FreeList.Ascending
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module SPU = GC.Spec.SweepPhase.Util
module FT = GC.Spec.FieldTarget
module FF = GC.Spec.Top.FFFill
module FAO = GC.Spec.Top.FFAllocOk

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The invariant at a phase, on the heap the first-fit functions run on.
let fshape (ph: T.phase U64.t) (g: heap) (fp: U64.t) : prop =
  match ph with
  | T.Idle -> ishape g fp
  | T.Marking -> mshape g fp
  | T.Sweeping c -> sshape g fp c

let fshape_inv (ph: T.phase U64.t) (h: heap) (s: ffst)
  : Lemma (ffinv ph h s <==> fshape ph (gl h s) s.fp)
  = ()

/// The invariant gives the walk to the end, no infix block and every block
/// fitting.
let fshape_walk (ph: T.phase U64.t) (g: heap) (fp: U64.t)
  : Lemma (requires fshape ph g fp)
          (ensures W.reaches g zero_addr heap_size /\ no_infix_block g /\ blocks_fit g)
  = FAO.ready_of ph g fp

/// ---------------------------------------------------------------------------
/// A program write
/// ---------------------------------------------------------------------------

/// Colour-blind: a program write keeps well-formedness for `free`, the walk,
/// the headers and the free list.
#push-options "--z3rlimit 40"
let write_wf (free: free_def) (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires free_def_ok free /\ well_formed_heap_with free g /\ FLA.fl_ascending g fp /\
                    SPM.program_write free g x a v)
          (ensures well_formed_heap_with free (write_word g a v) /\ SPI.same_heads g (write_word g a v) /\
                   FLA.fl_ascending (write_word g a v) fp)
  = let g' = write_word g a v in
    free_def_ok_elim free;
    wf_with_parts ();
    SPM.in_body_block g x a;
    SPI.colour_of g x;
    SPI.body_write g fp (hd_address x) a v;
    SPI.same_heads_facts g g';
    SPM.same_heads_part4 g g';
    SPU.part1_holds g';
    let kept (y: obj_addr)
      : Lemma (requires in_use free g y)
              (ensures read_word g' (hd_address y) == read_word g (hd_address y) /\
                       (is_closure y g ==> SPI.same_block g g' (hd_address y)))
      = if is_closure y g then begin
          SPM.other_body g x y a;
          SPI.obj_pos g y;
          let body (b: hp_addr)
            : Lemma (requires U64.v (hd_address y) < U64.v b /\ U64.v b < W.bnext g (hd_address y))
                    (ensures read_word g' b == read_word g b)
            = read_write_different g a b v
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires body)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
    assert (SPI.heads_kept free g g');
    let closure (src: obj_addr) (j: nat)
      : Lemma (requires in_use free g' src /\ ~(is_no_scan src g') /\
                        j < U64.v (wosize_of_object src g') /\ U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let w = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer w ==>
                        in_use free g' (resolve_object (w <: obj_addr) g') /\
                        infix_addr_wf g' (objects zero_addr g') (w <: obj_addr)))
      = let b : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
        let w = read_word g' b in
        SPI.colour_of g src; SPI.colour_of g' src;
        is_no_scan_spec src g; is_no_scan_spec src g';
        if b = a then begin
          read_write_same g a v;
          (if src <> x then begin
             assert (SPM.in_body g' src b);
             SPM.in_body_block g' src b;
             SPM.other_body g x src a
           end);
          SPI.storable_transfer g g' free free v
        end else begin
          read_write_different g a b v;
          if is_pointer w then begin
            FT.wf_with_field free g src j;
            SPI.storable_transfer g g' free free w
          end
        end
    in
    pointer_clauses_from_field_closure free g' closure
#pop-options

/// While marking.
#push-options "--z3rlimit 40"
let write_marking (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires mshape g fp /\ SPM.program_write free_stw g x a v)
          (ensures mshape (write_word g a v) fp)
  = reveal_opaque (`%mshape) (mshape g fp);
    free_stw_ok ();
    write_wf free_stw g fp x a v;
    FF.walk_after g (write_word g a v);
    FF.nz_heads g (write_word g a v);
    reveal_opaque (`%mshape) (mshape (write_word g a v) fp)
#pop-options

/// Mid-sweep.
let write_sweeping (c: U64.t) (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires sshape g fp c /\ SPM.program_write (SPI.free_incremental c) g x a v)
          (ensures sshape (write_word g a v) fp c)
  = reveal_opaque (`%sshape) (sshape g fp c);
    SPM.write_sweep_phase g fp c x a v;
    SPI.sweep_inv_incremental_elim g fp c;
    SPI.free_incremental_ok c;
    SPM.in_body_block g x a;
    SPI.colour_of g x;
    SPI.body_write g fp (hd_address x) a v;
    SPI.same_heads_facts g (write_word g a v);
    FF.nz_heads g (write_word g a v);
    reveal_opaque (`%sshape) (sshape (write_word g a v) fp c)

/// Idle: at the cursor where the sweep stopped.
#push-options "--z3rlimit 40"
let write_idle (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires ishape g fp /\ SPM.program_write free_stw g x a v)
          (ensures ishape (write_word g a v) fp)
  = reveal_opaque (`%ishape) (ishape g fp);
    let c = FStar.IndefiniteDescription.indefinite_description_ghost U64.t (fun c -> idle_at g fp c) in
    FStar.Classical.forall_intro (FAO.no_pending c g);
    assert (SPM.program_write (SPI.free_incremental c) g x a v);
    reveal_opaque (`%sshape) (sshape g fp c);
    write_sweeping c g fp x a v;
    reveal_opaque (`%sshape) (sshape (write_word g a v) fp c);
    reveal_opaque (`%ishape) (ishape (write_word g a v) fp)
#pop-options

/// **A program write keeps the invariant**, in every phase.
let write_phase (ph: T.phase U64.t) (g: heap) (fp: U64.t) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires fshape ph g fp /\ SPM.program_write (FAO.ffree_of ph) g x a v)
          (ensures fshape ph (write_word g a v) fp)
  = match ph with
    | T.Idle -> write_idle g fp x a v
    | T.Marking -> write_marking g fp x a v
    | T.Sweeping c -> write_sweeping c g fp x a v

/// ---------------------------------------------------------------------------
/// The mark's recolouring
/// ---------------------------------------------------------------------------

/// **While marking, recolouring a block in use keeps the shape.**
#push-options "--z3rlimit 40"
let recolour_marking (g: heap) (fp: U64.t) (x: obj_addr) (c: color)
  : Lemma (requires mshape g fp /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ c <> Blue)
          (ensures mshape (write_word g (hd_address x) (colorHeader (read_word g (hd_address x)) c)) fp)
  = reveal_opaque (`%mshape) (mshape g fp);
    let hd = read_word g (hd_address x) in
    let v = colorHeader hd c in
    let g' = write_word g (hd_address x) v in
    colorHeader_preserves_wosize hd c;
    colorHeader_getColor hd c;
    GC.Spec.Top.ByteWrite.colorHeader_abs hd c;
    assert (U64.v (getTag v) == U64.v (getTag hd));
    U64.v_inj (getTag v) (getTag hd);
    color_of_object_spec x g;
    is_blue_iff x g;
    AP.recolour_one g x v;
    AP.recoloured_facts g g';
    free_stw_ok ();
    AP.recoloured_wf g g' free_stw free_stw;
    FLA.fl_ascending_valid g fp;
    AP.recoloured_fl g g' fp;
    let nzr (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g') /\ ~(is_blue y g') ==> U64.v (wosize_of_object y g') >= 1)
      = () in
    FStar.Classical.forall_intro nzr;
    reveal_opaque (`%mshape) (mshape g' fp)
#pop-options
