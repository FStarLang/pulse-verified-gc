/// ---------------------------------------------------------------------------
/// GC.Gen.Run.FloatingGarbage - how long garbage survives
/// ---------------------------------------------------------------------------
///
/// The incremental collector keeps everything reachable when its cycle
/// started (snapshot at the beginning), so an object that becomes garbage
/// during a cycle survives that cycle: it is *floating garbage*.  This
/// module bounds how long it floats.
///
///   1. **Garbage stays garbage** (`garbage_stays_garbage`, ideal side): an
///      object that the program cannot reach is never reachable again.  A
///      well-formed allocation gets a fresh id and is initialised with values
///      the program can reach; a well-formed write stores such a value; new
///      roots are such values.
///   2. **Garbage is freed by the end of the next cycle**
///      (`floating_garbage_freed`): if an object that has been allocated is
///      unreachable at some point of a run, then at any later point where the
///      collector is idle, provided a cycle *started* after that point, no
///      block of the real memory holds it.  In particular at the first idle
///      point after that cycle.
///   3. **A freed object never comes back** (`gone_stays_gone`): once no
///      block holds an allocated object, none ever does again, at every later
///      point -- idle or not.  Ids are never reused: a block gets an id only
///      by an allocation (the next id) or by a minor collection's promotion
///      (the id of the nursery block it copies).
///
/// `floating_garbage_bound` puts 2 and 3 together.
///
/// **In words**: an object's block is freed by the end of the first complete
/// cycle that starts after the object becomes unreachable, and never
/// reappears.  So garbage lives at most the rest of the cycle in progress
/// (if any) plus one full cycle.  The cycle in progress may not free it: an
/// object reachable when that cycle started is in its snapshot, and idle,
/// the major heap's blocks are exactly the snapshot and what was allocated
/// or promoted since (`GC.Model.Represents.retains_snapshot`).  (A nursery
/// object can go sooner: a minor collection drops it if it is not
/// promoted.)
///
/// The proof goes through the address-free accounting of
/// `GC.Gen.Run.IdAccounting` and its tie to the real state
/// (`GC.Gen.Run.Hoisted.ids_at_idle`, `GC.Gen.Run.Hoisted.nursery_ids`):
/// once the object is unreachable, a cycle start drops it from the kept set
/// (it is not reachable, and the nursery is empty when a cycle starts), and
/// afterwards only fresh allocations and promoted nursery objects join; it is
/// neither.  Idle, the objects with a block are exactly the accounting's.
///
/// A point of a run is a run `rn1` that the rest of the run, `rn2`, extends
/// (`run_append rn1 rn2`).
module GC.Gen.Run.FloatingGarbage

open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Model.Represents
open GC.Gen.Run.Simulation

module Ph = GC.Spec.Phase
module I = GC.Model.Ideal

/// ---------------------------------------------------------------------------
/// The ideal side: garbage stays garbage
/// ---------------------------------------------------------------------------

/// **One well-formed event does not make garbage reachable.**
val garbage_stays_garbage_step (m: I.ideal_memory) (e: I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_event m e /\ I.valid_id m id /\ ~(I.reachable m id))
          (ensures I.valid_id (I.ideal_step m e) id /\ ~(I.reachable (I.ideal_step m e) id))

/// **Garbage stays garbage**, along a well-formed program.
val garbage_stays_garbage (m: I.ideal_memory) (ps: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program_from m ps /\ I.valid_id m id /\ ~(I.reachable m id))
          (ensures I.valid_id (I.ideal_run_from m ps) id /\ ~(I.reachable (I.ideal_run_from m ps) id))

/// The same from the start of a program: garbage after `ps1` is garbage
/// after `ps1 @ ps2`.
val garbage_stays_garbage_run (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\ I.valid_id (I.ideal_run ps1) id /\
                    ~(I.reachable (I.ideal_run ps1) id))
          (ensures I.valid_id (I.ideal_run (ps1 @ ps2)) id /\ ~(I.reachable (I.ideal_run (ps1 @ ps2)) id))

/// ---------------------------------------------------------------------------
/// Points of a run
/// ---------------------------------------------------------------------------

/// **A run extended by another**: `rn1` to the point, then `rn2` from there.
let rec run_append (#r0: real_state) (#es1: list event) (#r1: real_state) (rn1: run r0 es1 r1)
                   (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
  : Tot (run r0 (es1 @ es2) r2) (decreases rn2) =
  match rn2 with
  | Done _ -> List.Tot.Properties.append_l_nil es1; rn1
  | Step #_ #es2' #_ rn2' e r3 s ->
      List.Tot.Properties.append_assoc es1 es2' [e];
      Step (run_append rn1 rn2') e r3 s

/// Some event of `es` starts a cycle.
let rec starts_a_cycle (es: list event) : bool =
  match es with
  | [] -> false
  | e :: rest -> StartCycle? e || starts_a_cycle rest

/// No block of the run's real memory holds `id`.
let no_block (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r) (id: I.obj_id) : prop =
  ~(exists (b: block_addr). ids_of_run rn b == Some id)

/// ---------------------------------------------------------------------------
/// The real side
/// ---------------------------------------------------------------------------

/// **A freed object never comes back.**  If no block holds `id`, allocated
/// before the point `rn1`, then no block holds it at any later point: no
/// hypothesis on the program, the schedule or the phase.
val gone_stays_gone (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
                    (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2) (id: I.obj_id)
  : Lemma (requires id < alloc_count es1 /\ no_block rn1 id)
          (ensures no_block (run_append rn1 rn2) id)

/// A run that carries out `ps` has one program event per event of `ps`.
val executes_length (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                    (ps: list I.program_event)
  : Lemma (requires executes rn ps)
          (ensures GC.Gen.Run.IdAccounting.n_program (kinds es) == List.Tot.length ps)

/// The accounting's memory is the program's.
val account_mem (a: GC.Gen.Run.IdAccounting.acc) (ks: list kind) (ps: list I.program_event)
  : Lemma (requires GC.Gen.Run.IdAccounting.n_program ks == length ps)
          (ensures (GC.Gen.Run.IdAccounting.account a ks ps).GC.Gen.Run.IdAccounting.mem ==
                   I.ideal_run_from a.GC.Gen.Run.IdAccounting.mem ps)

/// **Garbage is freed by the end of the next cycle.**  The run carries out
/// a well-formed program `ps1 @ ps2`, its part `rn1` (to the point) carrying
/// out `ps1`.  The object `id` exists after `ps1` and the program cannot
/// reach it there.  If the rest of the run `rn2` starts a cycle and ends
/// idle (so that cycle, or a later one, has ended), no block holds `id`.
val floating_garbage_freed
      (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
      (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
      (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\ executes rn1 ps1 /\ executes (run_append rn1 rn2) (ps1 @ ps2) /\
                    I.valid_id (I.ideal_run ps1) id /\ ~(I.reachable (I.ideal_run ps1) id) /\
                    starts_a_cycle es2 /\ r2.phase == Ph.Idle)
          (ensures no_block (run_append rn1 rn2) id)

/// **The floating-garbage bound**: under the hypotheses of
/// `floating_garbage_freed`, no block holds `id` at the idle point, nor at
/// any point after it (`rn3`, any continuation of the run).
val floating_garbage_bound
      (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
      (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
      (ps1 ps2: list I.program_event) (id: I.obj_id)
      (#es3: list event) (#r3: real_state) (rn3: run r2 es3 r3)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\ executes rn1 ps1 /\ executes (run_append rn1 rn2) (ps1 @ ps2) /\
                    I.valid_id (I.ideal_run ps1) id /\ ~(I.reachable (I.ideal_run ps1) id) /\
                    starts_a_cycle es2 /\ r2.phase == Ph.Idle)
          (ensures no_block (run_append rn1 rn2) id /\ no_block (run_append (run_append rn1 rn2) rn3) id)

