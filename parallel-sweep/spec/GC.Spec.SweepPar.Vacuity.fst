/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPar.Vacuity — every proof lemma's precondition is satisfiable
///
/// Each check below calls one lemma of `GC.Spec.SweepPar` on arguments that
/// meet its precondition.  If a precondition were contradictory, the call
/// would not verify for these arguments.  Lemmas without a precondition need
/// no witness.
///
/// `heap_size` is abstract (at least 16), so a witness needing more room is
/// guarded by a bound on `heap_size`.  Witnesses that need objects in the
/// heap are guarded by `objects zero_addr g` being non-empty, which
/// `fused_pre` requires.
/// ---------------------------------------------------------------------------
module GC.Spec.SweepPar.Vacuity

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SweepPar

/// A one-word run (a wosize-0 fragment) at the bottom of the heap, and a
/// two-word one.
let r1 : run = { fb = 8UL; rw = 1 }
let r2 : run = { fb = 8UL; rw = 2 }

let flush_lemmas (h1 h2: heap) : unit =
  hd_address_spec 8UL;
  run_words_bound r1 8;
  flush_outside h1 no_run 0 0UL 0UL;
  flush_outside h1 r1 8 0UL 8UL;
  flush_head h1 r1 8 0UL;
  flush_link_word h1 r2 16 0UL;
  if heap_size >= 32 then flush_zero_word h1 8UL 3 0UL 16UL;
  flush_inside h1 h2 r1 8 0UL 1UL 0UL;
  flush_agree_at h1 h2 r1 8 0UL 1UL 0UL;
  white_other h1 8UL 8UL;
  white_same h1 h1 8UL

let walk_lemmas (g: heap) : unit =
  if Seq.length (objects zero_addr g) > 0 then begin
    objects_seg_last g zero_addr;
    seg_step g (U64.v zero_addr) heap_size
  end;
  seg_empty_end g (U64.v zero_addr) (U64.v zero_addr);
  objects_seg_split g zero_addr zero_addr

let run_lemmas (a b: run) (x: obj_addr) : unit =
  join_geom no_run no_run 0 0;
  join_geom r1 no_run 8 8;
  join_no_run r1

/// The segment lemmas, on the whole heap as one segment from `zero_addr`,
/// with the input heap on both sides: every invariant holds there.
let segment_lemmas (g: heap) : unit =
  let z = U64.v zero_addr in
  U64.v_inj (mk_hp_addr z) zero_addr;
  objects_seg_last g zero_addr;
  if Seq.length (objects zero_addr g) > 0 then begin
    seen_free g heap_size z g 0UL z g g no_run 0UL 0UL None;
    seen_black g heap_size z g 0UL z g g no_run 0UL 0UL None;
    lead_black g g no_run 0UL zero_addr heap_size z no_run
  end;
  seen_phase g heap_size z g 0UL no_run z g g no_run 0UL 0UL None;
  lead_phase g g no_run 0UL zero_addr heap_size z no_run;
  segment_correct g g no_run 0UL zero_addr heap_size
