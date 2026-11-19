module GC.Gen.Run.Simulation

/// The per-step lemmas, the allocation count, enabledness, the
/// stop-the-world case, the case splits, the induction over a run and the
/// read corollary are proved; only the hoisted run is still admitted.

open FStar.Seq
open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents

module I = GC.Model.Ideal
module P = GC.Gen.Run.Simulation.Program
module C = GC.Gen.Run.Simulation.Collector

let initial_sim_inv _ = P.initial_sim_inv ()

let alloc_keeps_sim_inv r h im ids e pe r' = GC.Gen.Run.Simulation.Steps.alloc_keeps r h im ids e pe r'

let write_keeps_sim_inv r h im ids e pe r' = GC.Gen.Run.Simulation.Steps.write_keeps r h im ids e pe r'

let read_roots_keep_sim_inv r h im ids e pe r' = P.read_roots_keep_sim_inv r h im ids e pe r'

let minor_keeps_sim_inv r h im ids roots r' = GC.Gen.Run.Simulation.Minor.minor_keeps r h im ids roots r'

let start_keeps_sim_inv r h im ids roots r' = C.start_keeps r h im ids roots r'

let slice_keeps_sim_inv r h im ids budget r' =
  C.sweep_frame_holds ();
  C.slice_keeps r h im ids budget r'

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

let rec executes_alloc_count_aux (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                                  (ps: list I.program_event)
  : Lemma (requires executes rn ps)
          (ensures Seq.length (I.ideal_run ps).I.objects == alloc_count es)
          (decreases rn)
  = match rn with
    | Done _ -> ()
    | Step #_ #es' #r1 rn' e r2 _ ->
        P.alloc_count_snoc es' e;
        if is_program_event e then begin
          eliminate exists (ps': list I.program_event) (pe: I.program_event).
              ps == ps' @ [pe] /\ executes rn' ps' /\ translates r1.memory (ids_of_run rn') e pe
          with begin
            I.ideal_run_snoc ps' pe;
            executes_alloc_count_aux rn' ps';
            P.step_alloc_count (ids_of_run rn') r1 e r2 (I.ideal_run ps') pe
          end
        end else executes_alloc_count_aux rn' ps

let executes_alloc_count #es #r rn ps = executes_alloc_count_aux rn ps

let rec simulation #es #r rn ps =
  match rn with
  | Done _ -> initial_sim_inv ()
  | Step #_ #es' #r1 rn' e r2 _ ->
      if is_program_event e then begin
        eliminate exists (ps': list I.program_event) (pe: I.program_event).
            ps == ps' @ [pe] /\ executes rn' ps' /\ translates r1.memory (ids_of_run rn') e pe
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

let reads_agree_state r h im ids obj i = P.reads_agree_state r h im ids obj i

let reads_agree #es #r rn ps obj i =
  simulation rn ps;
  reads_agree_state r (history_of_run rn) (I.ideal_run ps) (ids_of_run rn) obj i

let program_step_enabled r h im ids e pe =
  GC.Gen.Run.Simulation.Enabled.program_step_enabled_given r h im ids e pe

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let full_gc_collects #es0 #rs #rs' #r rn ps =
  let u = unbounded_budget in
  let im = I.ideal_run ps in
  let l1 = es0 @ [Minor rs] in
  let l2 = l1 @ [StartCycle rs'] in
  let l3 = l2 @ [Slice u] in
  C.full_gc_events_snoc es0 rs rs';
  match rn with
  | Done _ -> C.snoc_nonempty l3 (Slice u)
  | Step #_ #es3 #r3 rn3 e4 _ _ ->
    C.snoc_inj es3 l3 e4 (Slice u);
    match rn3 with
    | Done _ -> C.snoc_nonempty l2 (Slice u)
    | Step #_ #es2 #r2 rn2 e3 _ _ ->
      C.snoc_inj es2 l2 e3 (Slice u);
      match rn2 with
      | Done _ -> C.snoc_nonempty l1 (StartCycle rs')
      | Step #_ #es1 #r1 rn1 e2 _ _ ->
        C.snoc_inj es1 l1 e2 (StartCycle rs');
        assert (executes rn3 ps);
        assert (executes rn2 ps);
        assert (executes rn1 ps);
        simulation rn1 ps;
        simulation rn3 ps;
        simulation rn ps;
        let ids1 = ids_of_run rn1 in
        assert (ids_of_run rn2 == restrict r2.memory ids1);
        assert (ids_of_run rn3 == restrict r3.memory (ids_of_run rn2));
        assert (ids_of_run rn == restrict r.memory (ids_of_run rn3));
        let h = history_of_run rn in
        assert (history_of_run rn3 == history_of_run rn2);
        assert (h == history_of_run rn2);
        assert (h.start_memory == r1.memory /\ h.start_roots == rs');
        assert (forall (x: GC.Spec.Base.obj_addr). ~(h.allocated_during_cycle x));
        let sub (b: block_addr) (id: I.obj_id)
          : Lemma (requires ids_of_run rn b == Some id) (ensures ids1 b == Some id)
          = ()
        in
        FStar.Classical.forall_intro_2 (fun b -> FStar.Classical.move_requires (sub b));
        C.full_gc_end r1 r2 r3 r rs' (history_of_run rn1) h im ids1 (ids_of_run rn)
#pop-options

let hoisted_isomorphic #es #r rn #es_h #r_h rn_h ps = admit ()
