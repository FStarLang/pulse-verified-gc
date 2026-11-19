module GC.Gen.Run.Invariant

open GC.Gen.Run.Step
open GC.Gen.Run.History

/// Stage 0: the per-step lemmas are admitted; the general step lemma, the
/// induction over a run, and the run forms of losslessness are proved from
/// them.

let initial_run_invariant _ = admit ()

let alloc_keeps_run_invariant r h site tag size init r' = admit ()

let write_keeps_run_invariant r h b i v r' = admit ()

let minor_keeps_run_invariant r h roots r' = admit ()

let start_keeps_run_invariant r h roots r' = admit ()

let slice_keeps_run_invariant r h budget r' = admit ()

let step_keeps_run_invariant r h e r' =
  match e with
  | Alloc site tag size init -> alloc_keeps_run_invariant r h site tag size init r'
  | Write b i v -> write_keeps_run_invariant r h b i v r'
  | Read _ _ | SetRoots _ -> ()
  | Minor roots -> minor_keeps_run_invariant r h roots r'
  | StartCycle roots -> start_keeps_run_invariant r h roots r'
  | Slice budget -> slice_keeps_run_invariant r h budget r'

let rec run_invariant_along h0 #r0 #es #r1 rn =
  match rn with
  | Done _ -> ()
  | Step #_ #_ #r1' rn' e r2 _ ->
      run_invariant_along h0 rn';
      step_keeps_run_invariant r1' (history_along h0 rn') e r2

let alloc_phase_major_alloc_step r tag size init = admit ()

let idle_lossless r h = admit ()

let idle_survives r h = admit ()

let cycle_lossless #es #r rn =
  initial_run_invariant ();
  run_invariant_along (initial_history ()) rn;
  idle_lossless r (history_of_run rn)

let cycle_survives #es #r rn =
  initial_run_invariant ();
  run_invariant_along (initial_history ()) rn;
  idle_survives r (history_of_run rn)
