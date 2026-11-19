module GC.Gen.Run.Simulation

/// Stage 0: the per-step lemmas, the allocation count, enabledness, the
/// stop-the-world case and the hoisted run are admitted; the case splits,
/// the induction over a run and the read corollary are proved from them.

open FStar.Seq
open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents

module I = GC.Model.Ideal

let initial_sim_inv _ = admit ()

let alloc_keeps_sim_inv r h im ids e pe r' = admit ()

let write_keeps_sim_inv r h im ids e pe r' = admit ()

let read_roots_keep_sim_inv r h im ids e pe r' = admit ()

let minor_keeps_sim_inv r h im ids roots r' = admit ()

let start_keeps_sim_inv r h im ids roots r' = admit ()

let slice_keeps_sim_inv r h im ids budget r' = admit ()

let program_step_keeps_sim_inv r h im ids e pe r' =
  match e with
  | Alloc _ _ _ _ -> alloc_keeps_sim_inv r h im ids e pe r'
  | Write _ _ _ -> write_keeps_sim_inv r h im ids e pe r'
  | Read _ _ | SetRoots _ -> read_roots_keep_sim_inv r h im ids e pe r'
  | _ -> ()

let collector_step_keeps_sim_inv r h im ids e r' =
  match e with
  | Minor roots -> minor_keeps_sim_inv r h im ids roots r'
  | StartCycle roots -> start_keeps_sim_inv r h im ids roots r'
  | Slice budget -> slice_keeps_sim_inv r h im ids budget r'
  | _ -> ()

let executes_alloc_count #es #r rn ps = admit ()

let rec simulation #es #r rn ps =
  match rn with
  | Done _ -> initial_sim_inv ()
  | Step #_ #es' #r1 rn' e r2 _ ->
      if is_program_event e then begin
        eliminate exists (ps': list I.program_event) (pe: I.program_event).
            ps == ps' @ [pe] /\ executes rn' ps' /\ translates (ids_of_run rn') e pe
        with begin
          I.ideal_run_snoc ps' pe;
          simulation rn' ps';
          executes_alloc_count rn' ps';
          program_step_keeps_sim_inv r1 (history_of_run rn') (I.ideal_run ps') (ids_of_run rn') e pe r2
        end
      end else begin
        simulation rn' ps;
        collector_step_keeps_sim_inv r1 (history_of_run rn') (I.ideal_run ps) (ids_of_run rn') e r2
      end

let simulation_exists #es #r rn ps =
  simulation rn ps;
  assert (represents r (history_of_run rn) (I.ideal_run ps) (ids_of_run rn))

let reads_agree_state r h im ids obj i = admit ()

let reads_agree #es #r rn ps obj i =
  simulation rn ps;
  reads_agree_state r (history_of_run rn) (I.ideal_run ps) (ids_of_run rn) obj i

let program_step_enabled r h im ids e pe = admit ()

let full_gc_collects #es0 #rs #rs' #r rn ps = admit ()

let hoisted_isomorphic #es #r rn #es_h #r_h rn_h ps = admit ()
