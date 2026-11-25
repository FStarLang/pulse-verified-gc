/// ---------------------------------------------------------------------------
/// GC.SPOT.Observation - the trace of a concrete run
/// ---------------------------------------------------------------------------
///
/// Non-vacuity of `GC.Gen.Run.Observation`: on the concrete program and run
/// of `GC.SPOT.MutatorRun` (two nursery allocations, a nursery write of the
/// int 1, `3UL`, into field 0 of the second object, and a read of it back),
/// the real trace is the one-element list holding the written int -- the
/// read returns what was written, abstracted to the ideal value
/// `Word 3UL`.  The ideal trace is computed from the program; the real one
/// follows by `observational_equivalence`.

module GC.SPOT.Observation

open FStar.Seq
open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Gen.Run.Observation

module I = GC.Model.Ideal
module MR = GC.SPOT.MutatorRun

/// The ideal trace of the program: one read, returning the written int.
#push-options "--fuel 5 --ifuel 1 --z3rlimit 20"
let ideal_trace (_: unit) : Lemma (ideal_obs MR.ps4 == [I.FValue (I.Word 3UL)]) =
  let m1 = I.ideal_step I.empty_ideal MR.p_alloc in
  let m2 = I.ideal_step m1 MR.p_alloc in
  let m3 = I.ideal_step m2 MR.p_write in
  assert (Seq.length m2.I.objects == 2);
  assert (Seq.length m3.I.objects == 2);
  let o = Seq.index m2.I.objects 1 in
  assert (o.I.size == 1 /\ I.Scannable? o.I.fields);
  assert (Seq.index m3.I.objects 1 == I.update_field o 0 (I.Word MR.w));
  assert (I.field_at (Seq.index m3.I.objects 1) 0 == I.FValue (I.Word MR.w));
  assert (ideal_observe m3 MR.p_read == [I.FValue (I.Word 3UL)])
#pop-options

/// **The real trace of the concrete run** is that one-element list.
let real_trace (_: unit) : Lemma (real_obs (MR.rn4 ()) == [I.FValue (I.Word 3UL)]) =
  MR.wf_ps4 ();
  MR.executes_4 ();
  observational_equivalence (MR.rn4 ()) MR.ps4;
  ideal_trace ()
