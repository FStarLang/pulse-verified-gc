/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation - the program cannot tell the collector is there
/// ---------------------------------------------------------------------------
///
/// The mutator-equivalence theorem.
/// Two executions of the same program: the **real** one, a run of `step`
/// (`GC.Gen.Run.Step`) from the initial state, where the collector -- stop
/// the world or incremental -- runs whenever the runtime decides; and the
/// **ideal** one (`GC.Model.Ideal`), with no collector and unlimited memory.
/// `executes rn ps` says the real run `rn` carries out the program's events
/// `ps`: each real program event is the ideal one translated by the map from
/// blocks to objects at that point (`GC.Model.Represents.translates`), and
/// the collector calls that take roots are handed the ideal roots,
/// translated.
///
/// **The simulation** (`simulation`): for every well-formed program and every
/// run that carries it out -- any schedule of collector work, any slice
/// sizes, any allocation sites, as long as nothing runs out of memory (an
/// out-of-memory step is not a step) -- the real state represents the ideal
/// memory (`GC.Model.Represents.represents`): every object the program can
/// still reach has a faithful copy, pointers pointing at the copies, so
/// every read agrees (`reads_agree`); and when the collector is idle, the
/// major heap holds exactly what was reachable when the last cycle started
/// and what was allocated since.  It holds at every point of the run, since
/// every prefix of a run is a run.
///
/// It is proved by induction over the run (`simulation_step`) from one
/// lemma per kind of step, for the joint invariant `sim_inv`: the run
/// invariant (`GC.Gen.Run.Invariant`), `represents`, the ideal memory well
/// formed, and `reachable_in_kept` -- an object the program can reach now is
/// held by a nursery block or a kept major block (snapshot-at-the-beginning
/// on the ideal side: the program reaches only what was reachable when the
/// cycle started or was allocated since).  The last is what discharges the
/// program's obligations that the runtime trusts today
/// (`program_step_enabled`: a well-formed program's write, read or new roots
/// can always be carried out; `stores_in_kept`).
///
/// Corollaries: a stop-the-world collection leaves exactly the reachable
/// objects (`full_gc_collects`); and the incremental run is isomorphic, on
/// every allocated block, to its **hoisted** run -- the same program with
/// each cycle's slices moved to right after its start
/// (`GC.Gen.Run.Hoisted.hoisted_isomorphic`, over `isomorphic` below and
/// `GC.Gen.Run.Step.hoist`).

module GC.Gen.Run.Simulation

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module GBase = GC.Gen.Base
module I = GC.Model.Ideal

/// ---------------------------------------------------------------------------
/// A run carries out a program
/// ---------------------------------------------------------------------------

/// **The run `rn` carries out the program `ps`.**  Each program event of the
/// run translates the next event of `ps` through the map at that point
/// (`ids_of_run`); each `Minor` and `StartCycle` is handed the ideal roots
/// that are pointers at that point, translated (`ptr_values`; trusted, at
/// those two calls only).
let rec executes (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                 (ps: list I.program_event)
  : GTot prop (decreases rn) =
  match rn with
  | Done _ -> ps == []
  | Step #_ #_ #r1 rn' e _ _ ->
      if is_program_event e
      then exists (ps': list I.program_event) (pe: I.program_event).
             ps == ps' @ [pe] /\ executes rn' ps' /\ translates r1.memory (ids_of_run rn') e pe
      else executes rn' ps /\ collector_roots_represented (ids_of_run rn') (I.ideal_run ps).I.roots e

/// ---------------------------------------------------------------------------
/// The joint invariant
/// ---------------------------------------------------------------------------

/// A block holds an object reachable in the ideal memory only if it is in
/// the nursery or kept (snapshot or allocated since).
let reachable_in_kept (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) : prop =
  forall (x: obj_addr) (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id ==> kept h x

/// **The joint invariant** of the real state `r`, the history `h`, the ideal
/// memory `im` and the map `ids`.
let sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) : prop =
  run_invariant r h /\ represents r h im ids /\ I.wf_memory im /\ I.wf_objects im /\
  reachable_in_kept h im ids

/// **It holds at the start**: nothing allocated, nothing reachable.
val initial_sim_inv (_: unit)
  : Lemma (sim_inv (initial_state ()) (initial_history ()) I.empty_ideal empty_ids)

/// ---------------------------------------------------------------------------
/// Each kind of step keeps it
/// ---------------------------------------------------------------------------

/// The joint state after a program step.
let program_post (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                 (e: event) (pe: I.program_event) (r': real_state) : prop =
  sim_inv r' (update_history h r e r') (I.ideal_step im pe)
          (update_block_ids ids (Seq.length im.I.objects) r e r')

/// The hypotheses of a program step: the invariant, a well-formed event of
/// the program, carried out by `e`, and a step.
let program_pre (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                (e: event) (pe: I.program_event) (r': real_state) : prop =
  sim_inv r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe /\ step r e r'

/// **An allocation**: the new block (nursery or major) holds the new object,
/// with the next id.
val alloc_keeps_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires program_pre r h im ids e pe r' /\ Alloc? e)
          (ensures program_post r h im ids e pe r')

/// **A write**: the written field holds the translated value.
val write_keeps_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires program_pre r h im ids e pe r' /\ Write? e)
          (ensures program_post r h im ids e pe r')

/// **A read, or new roots**: the real state does not change; new roots
/// can only make less reachable.
val read_roots_keep_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires program_pre r h im ids e pe r' /\ (Read? e \/ SetRoots? e))
          (ensures program_post r h im ids e pe r')

/// The joint state after a collector step: the ideal memory does not change.
let collector_post (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                   (e: event) (r': real_state) : prop =
  sim_inv r' (update_history h r e r') im (update_block_ids ids (Seq.length im.I.objects) r e r')

/// **A minor collection**: a live nursery object's entry follows it to its
/// promoted copy (the forwarding map), a dead one's goes.
val minor_keeps_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (roots: seq U64.t) (r': real_state)
  : Lemma (requires sim_inv r h im ids /\ roots_represented ids (ptr_values im.I.roots) roots /\
                    step r (Minor roots) r')
          (ensures collector_post r h im ids (Minor roots) r')

/// **The start of a cycle**: colours only; the snapshot is what the ideal
/// roots reach.
val start_keeps_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (roots: seq U64.t) (r': real_state)
  : Lemma (requires sim_inv r h im ids /\ roots_represented ids (ptr_values im.I.roots) roots /\
                    step r (StartCycle roots) r')
          (ensures collector_post r h im ids (StartCycle roots) r')

/// **A slice**: mark moves recolour; a sweep slice frees only blocks the
/// program cannot reach, whose entries go.
val slice_keeps_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (budget: nat) (r': real_state)
  : Lemma (requires sim_inv r h im ids /\ step r (Slice budget) r')
          (ensures collector_post r h im ids (Slice budget) r')

/// **Every program step keeps it.**
val program_step_keeps_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event) (r': real_state)
  : Lemma (requires program_pre r h im ids e pe r')
          (ensures program_post r h im ids e pe r')

/// **Every collector step keeps it**, given the ideal roots at the calls
/// that take roots.
val collector_step_keeps_sim_inv (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (r': real_state)
  : Lemma (requires sim_inv r h im ids /\ ~(is_program_event e) /\
                    collector_roots_represented ids im.I.roots e /\ step r e r')
          (ensures collector_post r h im ids e r')

/// ---------------------------------------------------------------------------
/// The simulation
/// ---------------------------------------------------------------------------

/// The ideal memory after `ps` has one object per allocation of a run that
/// carries it out: the next id is the number of allocations so far.
val executes_alloc_count (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                         (ps: list I.program_event)
  : Lemma (requires executes rn ps)
          (ensures Seq.length (I.ideal_run ps).I.objects == alloc_count es)

/// **The simulation.**  For a well-formed program `ps` and any run `rn` of
/// the real runtime that carries it out, from the initial state: the run
/// invariant holds, and the real state represents the memory the program
/// would have with no collector, through the map the run defines -- every
/// reachable object has a faithful copy, and, idle, the major heap holds
/// exactly the snapshot of the last cycle and what was allocated since.
/// (Every prefix of a run is a run, so this holds at every point.)
val simulation (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
               (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps)
          (ensures sim_inv r (history_of_run rn) (I.ideal_run ps) (ids_of_run rn))
          (decreases rn)

/// The plan's form: some map from blocks to objects makes the real state
/// represent the ideal memory.
val simulation_exists (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                      (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps)
          (ensures exists (ids: block_id_map). represents r (history_of_run rn) (I.ideal_run ps) ids)

/// **Every read agrees.**  When the program reads field `i` of object `obj`
/// (a well-formed read), the block holding `obj` holds that field,
/// translated: the program cannot tell the collector is there.
val reads_agree_state (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                      (obj: I.obj_id) (i: nat)
  : Lemma (requires sim_inv r h im ids /\ I.wf_event im (I.Read obj i))
          (ensures exists (b: block_addr). ids b == Some obj /\ is_allocated r.memory b /\
                     i < block_size r.memory b /\
                     content_rep ids (I.field_at (Seq.index im.I.objects obj) i) (block_field r.memory b i))

/// The same at the end of any run that carries out a well-formed program.
val reads_agree (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                (ps: list I.program_event) (obj: I.obj_id) (i: nat)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ I.wf_event (I.ideal_run ps) (I.Read obj i))
          (ensures exists (b: block_addr). ids_of_run rn b == Some obj /\ is_allocated r.memory b /\
                     i < block_size r.memory b /\
                     content_rep (ids_of_run rn) (I.field_at (Seq.index (I.ideal_run ps).I.objects obj) i)
                                 (block_field r.memory b i))

/// What the runtime needs for an allocation: in the nursery, room for the
/// object; in the major heap, a block the allocator finds.
let room_for (r: real_state) (e: event) : prop =
  match e with
  | Alloc InNursery _ size _ -> size <= GBase.max_young_wosize /\ minor_can_alloc r.memory.nursery size
  | Alloc InMajor tag size _ -> (AC.alloc_phase r.memory.major r.free_list r.phase size tag).SA.obj_out <> 0UL
  | _ -> True

/// **A well-formed program's event can always be carried out** (given room
/// for an allocation): the obligations the runtime trusts today -- the
/// write barrier's `modify_ok` (a non-free, non-closure block, a storable
/// value, while marking one the marker will reach), the initialising
/// writes' values, the nursery's -- follow from the program's
/// well-formedness and the invariant.
///
/// **Trusted, for the nursery steps** (`GC.Gen.Run.Simulation.Enabled.nursery_trusted`):
/// nursery allocation and nursery stores are modelled steps on the trusted
/// boundary, so what they leave is assumed rather than derived: the
/// nursery's frame and shape (`GenInv.minor_heap_shape`: a stored word does
/// not read as a nursery header -- the mutator obligation of
/// `GC.Gen.MinorHeap`).  A value stored into a scannable nursery object may
/// be a major interior (infix) pointer, as in real OCaml (a pointer to one of
/// several mutually recursive closures): `Step.nursery_storable` is
/// `storable_value`.  It says nothing about the other steps.
val program_step_enabled (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (e: event) (pe: I.program_event)
  : Lemma (requires sim_inv r h im ids /\ I.wf_event im pe /\ translates r.memory ids e pe /\ room_for r e /\
                    GC.Gen.Run.Simulation.Enabled.nursery_trusted r e)
          (ensures exists (r': real_state). step r e r')

/// ---------------------------------------------------------------------------
/// Stop the world
/// ---------------------------------------------------------------------------

/// **A stop-the-world collection leaves exactly what the program can
/// reach.**  After `full_gc` (a minor collection, the start of a cycle, an
/// unbounded mark slice and an unbounded sweep slice) at the end of a run
/// that carries out a well-formed program, the collector is idle, the
/// nursery empty, and a block holds an object only if the program can
/// still reach it (with `covers_reachable`, exactly the reachable objects
/// have a block).  This subsumes `full_gc`'s isomorphism and safety.
val full_gc_collects (#es0: list event) (#rs #rs': seq U64.t) (#r: real_state)
                     (rn: run (initial_state ()) (es0 @ full_gc_events rs rs') r)
                     (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps)
          (ensures r.phase == Ph.Idle /\ r.memory.nursery == minor_reset r.memory.nursery /\
                   (forall (b: block_addr) (id: I.obj_id).
                      ids_of_run rn b == Some id ==> I.reachable (I.ideal_run ps) id))

/// ---------------------------------------------------------------------------
/// The hoisted run
/// ---------------------------------------------------------------------------

/// The word `w` of `m` points `k` words into the allocated block `c`.
let points_into (m: real_memory) (w: U64.t) (c: block_addr) (k: nat) : prop =
  is_allocated m c /\ k < block_size m c /\ w == ptr_value c k

/// The words `w1` of `m1` and `w2` of `m2` correspond through `f`: pointers
/// into corresponding blocks at the same offset, or the same word pointing
/// into no block of either.
let word_corresponds (m1 m2: real_memory) (f: block_addr -> GTot (option block_addr)) (w1 w2: U64.t) : prop =
  (exists (c: block_addr) (k: nat). points_into m1 w1 c k /\
     (exists (c': block_addr). f c == Some c' /\ points_into m2 w2 c' k)) \/
  (w1 == w2 /\ ~(exists (c: block_addr) (k: nat). points_into m1 w1 c k) /\
   ~(exists (c: block_addr) (k: nat). points_into m2 w2 c k))

/// **Isomorphic on every allocated block**: a bijection `f` between the
/// allocated blocks of `m1` and `m2` that keeps tags and sizes, and fields:
/// raw words equal in a no-scan block, corresponding words in a scannable
/// one.
let isomorphic (m1 m2: real_memory) : prop =
  exists (f: block_addr -> GTot (option block_addr)).
    (forall (b: block_addr). Some? (f b) <==> is_allocated m1 b) /\
    (forall (b b': block_addr). f b == Some b' ==> is_allocated m2 b') /\
    (forall (b': block_addr). is_allocated m2 b' ==> (exists (b: block_addr). f b == Some b')) /\
    (forall (b1 b2: block_addr). Some? (f b1) /\ f b1 == f b2 ==> b1 == b2) /\
    (forall (b b': block_addr). f b == Some b' ==>
       block_tag m1 b == block_tag m2 b' /\ block_size m1 b == block_size m2 b' /\
       (forall (i: nat). i < block_size m1 b ==>
          (if block_tag m1 b < 251
           then word_corresponds m1 m2 f (block_field m1 b i) (block_field m2 b' i)
           else block_field m1 b i == block_field m2 b' i)))

/// The corollary itself, that the incremental run and its hoisted run are
/// isomorphic once the collector is idle, is `GC.Gen.Run.Hoisted.hoisted_isomorphic`
/// (stated there, since its proof goes through the simulation).

/// ---------------------------------------------------------------------------
/// Later (not stated)
/// ---------------------------------------------------------------------------
///
/// From the plan's "later" row, kept here as text only:
///   * garbage stays garbage: an object the program cannot reach is never
///     reachable again;
///   * floating garbage is freed by the end of the first cycle that starts
///     after it becomes unreachable.
