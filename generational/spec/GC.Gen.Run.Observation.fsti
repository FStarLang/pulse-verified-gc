/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Observation - what the program sees is what it would see
/// ---------------------------------------------------------------------------
///
/// Observational equivalence, stated as an equality of traces.
///
///   * **The ideal trace** (`ideal_obs ps`): the field contents the reads of
///     the program `ps` return, in order, each read on the ideal memory
///     (`GC.Model.Ideal`) just before it.
///   * **The real trace** (`real_obs rn`): for each `Read b i` of the real
///     run `rn`, the word field `i` of the block `b` holds just before it,
///     **abstracted through the map from blocks to objects at that point**
///     (`ids_of_run`, `abs_content`): in a scannable block, a word that points
///     `k` words into an allocated block with id `id` is `Ptr { id; k }`, any
///     other word is `Word` itself; in a no-scan block the word is raw
///     (`FRaw`).  The abstraction inverts `GC.Model.Represents.value_rep` and
///     `content_rep` (`abs_value_rep`, `abs_content_rep`): a pointer names
///     exactly one block, at one offset (distinct blocks are disjoint,
///     `points_into_unique`), and a word that is not a pointer lies outside
///     both heaps (`outside_heaps`, trusted in `value_rep`), so it points into
///     no block.
///
/// **The theorem** (`observational_equivalence`): for a well-formed program
/// and any run of the real runtime that carries it out -- any schedule of
/// minor collections, cycle starts and slices, stop-the-world or
/// incremental, any allocation sites -- the real trace *is* the ideal trace.
/// The collector's events add nothing to either trace, and each read agrees
/// (`GC.Gen.Run.Simulation.reads_agree_state`).  So any two runs that carry
/// out the same program observe the same values (`same_program_same_obs`).
///
/// **Physical equality** (`physical_equality`, `physical_equality_run`): two
/// words that hold valid ideal values are equal exactly when the values are
/// -- the program's `==` on the real words is `==` on the ideal values.

module GC.Gen.Run.Observation

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Model.Represents
open GC.Gen.Run.Simulation

module U64 = FStar.UInt64
module I = GC.Model.Ideal
module ID = FStar.IndefiniteDescription

/// ---------------------------------------------------------------------------
/// The ideal trace
/// ---------------------------------------------------------------------------

/// What the event `e` lets the program observe in the memory `m`: for a
/// read, the field it reads (nothing for an ill-formed read); nothing for
/// any other event.
let ideal_observe (m: I.ideal_memory) (e: I.program_event) : list I.field_content =
  match e with
  | I.Read obj i ->
      if I.valid_id m obj && i < (Seq.index m.I.objects obj).I.size
      then [I.field_at (Seq.index m.I.objects obj) i]
      else []
  | _ -> []

/// The observations of the events `ps` from the memory `m`.
let rec ideal_obs_from (m: I.ideal_memory) (ps: list I.program_event)
  : Tot (list I.field_content) (decreases ps) =
  match ps with
  | [] -> []
  | e :: rest -> ideal_observe m e @ ideal_obs_from (I.ideal_step m e) rest

/// **The ideal trace** of the program `ps`.
let ideal_obs (ps: list I.program_event) : list I.field_content = ideal_obs_from I.empty_ideal ps

/// ---------------------------------------------------------------------------
/// The real trace
/// ---------------------------------------------------------------------------

/// The word `w` points `k` words into a block of `m` that holds an object.
let points_to_object (m: real_memory) (ids: block_id_map) (w: U64.t) (ck: block_addr & nat) : prop =
  points_into m w (fst ck) (snd ck) /\ Some? (ids (fst ck))

/// **The value a word holds**, read back through `ids`: a pointer into a
/// block with id `id`, `k` words in, is `Ptr { id; k }`; any other word is
/// itself.
let abs_value (m: real_memory) (ids: block_id_map) (w: U64.t) : GTot I.value =
  if ID.strong_excluded_middle (exists (ck: block_addr & nat). points_to_object m ids w ck)
  then
    let ck = ID.indefinite_description_ghost (block_addr & nat) (points_to_object m ids w) in
    I.Ptr { I.head = Some?.v (ids (fst ck)); I.infix_offset = snd ck }
  else I.Word w

/// **The content a field of the block `b` holds**: a value in a scannable
/// block, a raw word in a no-scan one.
let abs_content (m: real_memory) (ids: block_id_map) (b: block_addr) (w: U64.t) : GTot I.field_content =
  if block_tag m b < 251 then I.FValue (abs_value m ids w) else I.FRaw w

/// What the real event `e` lets the program observe in `m`, through `ids`.
let real_observe (m: real_memory) (ids: block_id_map) (e: event) : GTot (list I.field_content) =
  match e with
  | Read b i -> [abs_content m ids b (block_field m b i)]
  | _ -> []

/// **The real trace** of the run `rn`: each read, observed through the map
/// at that point.
let rec real_obs (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
  : GTot (list I.field_content) (decreases rn) =
  match rn with
  | Done _ -> []
  | Step #_ #_ #r1 rn' e _ _ -> real_obs rn' @ real_observe r1.memory (ids_of_run rn') e

/// ---------------------------------------------------------------------------
/// The abstraction inverts the representation
/// ---------------------------------------------------------------------------

/// **A word points into at most one block, at one offset.**
val points_into_unique (r: real_state) (h: cycle_history) (w: U64.t) (c1 c2: block_addr) (k1 k2: nat)
  : Lemma (requires GC.Gen.Run.Invariant.run_invariant r h /\
                    points_into r.memory w c1 k1 /\ points_into r.memory w c2 k2)
          (ensures c1 == c2 /\ k1 == k2)

/// **A word that holds a valid value reads back as that value.**
val abs_value_rep (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                  (v: I.value) (w: U64.t)
  : Lemma (requires sim_inv r h im ids /\ I.valid_value im v /\ value_rep ids v w)
          (ensures abs_value r.memory ids w == v)

/// **A field of a block that holds a field of its object reads back as that
/// field.**
val abs_content_rep (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                    (b: block_addr) (id: I.obj_id) (i: nat)
  : Lemma (requires sim_inv r h im ids /\ ids b == Some id /\ I.valid_id im id /\
                    i < (Seq.index im.I.objects id).I.size /\
                    content_rep ids (I.field_at (Seq.index im.I.objects id) i) (block_field r.memory b i))
          (ensures abs_content r.memory ids b (block_field r.memory b i) ==
                   I.field_at (Seq.index im.I.objects id) i)

/// ---------------------------------------------------------------------------
/// Observational equivalence
/// ---------------------------------------------------------------------------

/// The ideal trace grows at the end with the program.
val ideal_obs_snoc (ps: list I.program_event) (e: I.program_event)
  : Lemma (ideal_obs (ps @ [e]) == ideal_obs ps @ ideal_observe (I.ideal_run ps) e)

/// **Observational equivalence.**  For a well-formed program `ps` and any
/// run `rn` of the real runtime that carries it out, the reads of the run,
/// abstracted through the map from blocks to objects, return exactly what
/// the program's reads return with no collector.
val observational_equivalence (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                              (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps)
          (ensures real_obs rn == ideal_obs ps)
          (decreases rn)

/// **The schedule is invisible**: two runs that carry out the same
/// well-formed program -- whatever collections run when, incremental or
/// stop the world -- observe the same values.
val same_program_same_obs (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
                          (#es2: list event) (#r2: real_state) (rn2: run (initial_state ()) es2 r2)
                          (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn1 ps /\ executes rn2 ps)
          (ensures real_obs rn1 == real_obs rn2)

/// ---------------------------------------------------------------------------
/// Physical equality
/// ---------------------------------------------------------------------------

/// **Physical equality is preserved**: two words holding valid values are
/// equal exactly when the values are.
val physical_equality (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                      (v1 v2: I.value) (w1 w2: U64.t)
  : Lemma (requires sim_inv r h im ids /\ I.valid_value im v1 /\ I.valid_value im v2 /\
                    value_rep ids v1 w1 /\ value_rep ids v2 w2)
          (ensures w1 == w2 <==> v1 == v2)

/// The same at the end of any run that carries out a well-formed program.
val physical_equality_run (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                          (ps: list I.program_event) (v1 v2: I.value) (w1 w2: U64.t)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\
                    I.valid_value (I.ideal_run ps) v1 /\ I.valid_value (I.ideal_run ps) v2 /\
                    value_rep (ids_of_run rn) v1 w1 /\ value_rep (ids_of_run rn) v2 w2)
          (ensures w1 == w2 <==> v1 == v2)
