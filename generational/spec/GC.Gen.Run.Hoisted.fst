/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Hoisted - the incremental run and its hoisted run
/// ---------------------------------------------------------------------------
///
/// The corollary of the simulation (mutator-equivalence-plan.md, section 1):
/// once the incremental collector is idle, the real memory is isomorphic,
/// on every allocated block, to the memory of the hoisted run -- the same
/// program with each cycle's slices moved to right after its start.
///
///   1. **The id-level accounting along a run** (`acc_along`): at every state
///      of a run that carries out a well-formed program, the real state, its
///      history and its map from blocks to objects agree with the accounting
///      of the program and the schedule's kinds
///      (`GC.Gen.Run.IdAccounting.account`): the nursery's blocks hold its
///      `nurs`, the kept major blocks its `kept`, the remembered set its
///      `rt`.  Idle, every allocated major block is kept, so the objects
///      that have a block are exactly `live_ids ps (kinds es)`
///      (`ids_at_idle`).
///   2. **The hoisted run is idle at the end** (`hoisted_idle`): every start
///      is followed by two unbounded slices, which finish marking and then
///      the sweep.
///   3. Moving the slices does not change the accounting
///      (`GC.Gen.Run.IdAccounting.live_ids_hoist`), so both runs give a block
///      to the same objects; composing one run's map with the other's inverse
///      is the isomorphism (`iso_from_ids`): the blocks hold the same ideal
///      object, so the same tag, size and fields, a pointer field pointing at
///      corresponding blocks at the same offset.
///
/// The result (`hoisted_isomorphic_given`) is conditional on
///   * `program_no_young ps`: no new no-scan object has a raw word that looks
///     like a nursery address (`major_alloc_step` would remember its slot);
///   * `start_snapshot` and `minor_promotes` (`GC.Gen.Run.Hoisted.Steps`):
///     the snapshot of a cycle start holds only ideal-reachable objects, and
///     a minor collection promotes exactly `GC.Gen.Run.IdAccounting.promoted`.
///     (The other two step hypotheses, the nursery frames, are proved:
///     `GC.Gen.Run.Hoisted.Nursery`.)
module GC.Gen.Run.Hoisted

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
open GC.Gen.Run.Simulation
open GC.Gen.Run.IdAccounting
open GC.Gen.Run.Hoisted.Base
open GC.Gen.Run.Hoisted.Frame
open GC.Gen.Run.Hoisted.Steps
open GC.Gen.Run.Hoisted.Program
open GC.Gen.Run.Hoisted.Collector

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module GB = GC.Gen.Barrier
module GI = GC.Gen.Incremental
module ID = FStar.IndefiniteDescription

/// ---------------------------------------------------------------------------
/// 1. The accounting along a run
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let initial_acc (_: unit)
  : Lemma (acc_inv (initial_state ()) (initial_history ()) empty_ids empty_acc)
  = ()
#pop-options

let rec executes_length (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                        (ps: list I.program_event)
  : Lemma (requires executes rn ps) (ensures n_program (kinds es) == List.Tot.length ps) (decreases rn)
  = match rn with
    | Done _ -> ()
    | Step #_ #es' #_ rn' e _ _ ->
        kinds_snoc es' e;
        n_program_snoc (kinds es') (kind_of e);
        if is_program_event e then
          eliminate exists (ps': list I.program_event) (pe: I.program_event).
            ps == ps' @ [pe] /\ executes rn' ps' /\ translates (ids_of_run rn') e pe
          with begin
            executes_length rn' ps';
            List.Tot.Properties.append_length ps' [pe]
          end
        else executes_length rn' ps

/// The map and the history of a run that grows by a step.
let run_step_maps (#es': list event) (#r1: real_state) (rn': run (initial_state ()) es' r1)
                  (e: event) (r2: real_state) (s: squash (step r1 e r2))
  : Lemma (ids_of_run (Step rn' e r2 s) == update_block_ids (ids_of_run rn') (alloc_count es') r1 e r2 /\
           history_of_run (Step rn' e r2 s) == update_history (history_of_run rn') r1 e r2)
  = ()

/// **The accounting invariant at the end of every run** that carries out a
/// well-formed program that stores no young-looking word.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec acc_along (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                  (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ program_no_young ps /\ step_hyps)
          (ensures (let a = account empty_acc (kinds es) ps in
                    acc_inv r (history_of_run rn) (ids_of_run rn) a /\
                    a.mem == I.ideal_run ps))
          (decreases rn)
  = match rn with
    | Done _ -> initial_acc ()
    | Step #_ #es' #r1 rn' e r2 s ->
        kinds_snoc es' e;
        run_step_maps rn' e r2 s;
        simulation rn ps;
        if is_program_event e then
          eliminate exists (ps': list I.program_event) (pe: I.program_event).
            ps == ps' @ [pe] /\ executes rn' ps' /\ translates (ids_of_run rn') e pe
          with begin
            I.ideal_run_snoc ps' pe;
            program_no_young_snoc ps' pe;
            acc_along rn' ps';
            simulation rn' ps';
            executes_alloc_count rn' ps';
            executes_length rn' ps';
            account_snoc empty_acc (kinds es') ps' (kind_of e) pe;
            let im = I.ideal_run ps' in
            program_acc r1 (history_of_run rn') im (ids_of_run rn') (account empty_acc (kinds es') ps') e pe r2
          end
        else begin
          acc_along rn' ps;
          simulation rn' ps;
          executes_alloc_count rn' ps;
          executes_length rn' ps;
          account_snoc empty_acc (kinds es') ps (kind_of e) (I.Read 0 0);
          let a1 = account empty_acc (kinds es') ps in
          let h1 = history_of_run rn' in
          let ids1 = ids_of_run rn' in
          let im = I.ideal_run ps in
          match e with
          | Slice _ -> slice_acc r1 h1 im ids1 a1 e r2
          | StartCycle _ -> start_acc_lemma r1 h1 im ids1 a1 e r2
          | Minor _ -> minor_acc_lemma r1 h1 im ids1 a1 e r2
        end
#pop-options

/// **Idle, the objects with a block are those the accounting names.**
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let ids_at_idle (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ program_no_young ps /\ step_hyps /\ r.phase == Ph.Idle)
          (ensures forall (id: I.obj_id). (exists (b: block_addr). ids_of_run rn b == Some id) <==> live_ids ps (kinds es) id)
  = acc_along rn ps;
    simulation rn ps;
    let ids = ids_of_run rn in
    let h = history_of_run rn in
    introduce forall (id: I.obj_id). (exists (b: block_addr). ids b == Some id) <==> live_ids ps (kinds es) id
    with begin
      introduce (exists (b: block_addr). ids b == Some id) ==> live_ids ps (kinds es) id
      with eliminate exists (b: block_addr). ids b == Some id
           with (match b with
                 | Nursery _ -> ()
                 | Major x -> assert (is_allocated r.memory (Major x)); assert (kept h x))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// 2. The hoisted run ends idle
/// ---------------------------------------------------------------------------

/// The slices still owed by the cycle in progress (2 after a start, 1 after
/// the marking slice, 0 idle); `None` for a schedule not of the hoisted shape.
let pend_step (p: option nat) (k: kind) : option nat =
  match p with
  | None -> None
  | Some p ->
      (match k with
       | KStart -> if p = 0 then Some 2 else None
       | KSlice b -> if p > 0 then (if b >= unbounded_budget then Some (p - 1) else None) else Some 0
       | _ -> if p = 0 then Some 0 else None)

let pend (ks: list kind) : option nat = fold_left pend_step (Some 0) ks

let rec pend_hoist_from (ks: list kind)
  : Lemma (ensures fold_left pend_step (Some 0) (hoist ks) == Some 0) (decreases ks)
  = match ks with
    | [] -> ()
    | KSlice _ :: rest -> pend_hoist_from rest
    | KStart :: rest -> pend_hoist_from rest
    | _ :: rest -> pend_hoist_from rest

let pend_snoc (ks: list kind) (k: kind) : Lemma (pend (ks @ [k]) == pend_step (pend ks) k) =
  List.Tot.Properties.fold_left_append pend_step (Some 0) ks [k]

let phase_of (p: nat) (ph: Ph.gc_phase) : prop =
  (p == 0 ==> ph == Ph.Idle) /\ (p == 2 ==> ph == Ph.Marking) /\ (p == 1 ==> Ph.Sweeping? ph)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec phase_along (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                    (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ Some? (pend (kinds es)))
          (ensures phase_of (Some?.v (pend (kinds es))) r.phase)
          (decreases rn)
  = match rn with
    | Done _ -> ()
    | Step #_ #es' #r1 rn' e r2 _ ->
        kinds_snoc es' e;
        pend_snoc (kinds es') (kind_of e);
        let ps' : list I.program_event =
          if is_program_event e
          then ID.indefinite_description_ghost (list I.program_event)
                 (fun ps' -> exists (pe: I.program_event). ps == ps' @ [pe] /\ executes rn' ps' /\
                                                           translates (ids_of_run rn') e pe)
          else ps in
        if is_program_event e then begin
          eliminate exists (pe: I.program_event). ps == ps' @ [pe] /\ executes rn' ps' /\
                                                 translates (ids_of_run rn') e pe
          with I.ideal_run_snoc ps' pe
        end;
        phase_along rn' ps';
        simulation rn' ps';
        let p0 = Some?.v (pend (kinds es')) in
        (match e with
         | Slice b ->
             if p0 = 1 then begin
               let Ph.Sweeping c = r1.phase in
               GI.phase_slice_finishes r1.memory.nursery r1.memory.major r1.free_list r1.phase b r1.scan_pos
             end
             else ()
         | Write (Major x) i v -> assert (major_write_step r1 x i v r2)
         | _ -> ())
#pop-options

/// **The hoisted run is idle at the end.**
let hoisted_idle (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                 (ps: list I.program_event) (ks: list kind)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ kinds es == hoist ks)
          (ensures r.phase == Ph.Idle)
  = pend_hoist_from ks;
    phase_along rn ps

/// ---------------------------------------------------------------------------
/// 3. The isomorphism
/// ---------------------------------------------------------------------------

let block_of_spec (ids: block_id_map) (id: I.obj_id)
  : Lemma (requires exists (b: block_addr). ids b == Some id)
          (ensures Some? (block_of ids id) /\ ids (Some?.v (block_of ids id)) == Some id)
  = ()

/// The map from the blocks of one memory to the blocks of the other holding
/// the same object.
let compose (ids1 ids2: block_id_map) (b: block_addr) : GTot (option block_addr) =
  match ids1 b with
  | Some id -> block_of ids2 id
  | None -> None

/// A word that is neither a major pointer nor young points into no block.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let word_points_nowhere (m: real_memory) (w: U64.t)
  : Lemma (requires minor_wf m.nursery /\ blocks_fit m.major /\ ~(is_pointer w) /\ ~(GB.is_young w))
          (ensures ~(exists (c: block_addr) (k: nat). points_into m w c k))
  = introduce forall (c: block_addr) (k: nat). ~(points_into m w c k)
    with introduce points_into m w c k ==> False
    with (match c with
          | Major x -> major_ptr_shape m.major x k
          | Nursery o -> nursery_ptr_shape m.nursery o k)
#pop-options

/// A pointer value lands in the block holding its object, at its offset.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let ptr_points_into (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (hd: I.obj_id) (k: nat) (w: U64.t)
  : Lemma (requires keyed m ids /\ copies_faithful m h im ids /\ I.wf_objects im /\
                    I.valid_value im (I.Ptr { I.head = hd; I.infix_offset = k }) /\
                    value_rep ids (I.Ptr { I.head = hd; I.infix_offset = k }) w)
          (ensures exists (c: block_addr). ids c == Some hd /\ points_into m w c k)
  = eliminate exists (c: block_addr). ids c == Some hd /\ w == ptr_value c k
    with begin
      header_of m h im ids c hd;
      assert (points_into m w c k)
    end
#pop-options

/// **Two memories representing the same ideal memory, with blocks for the
/// same objects, are isomorphic.**
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let iso_from_ids (m1 m2: real_memory) (h1 h2: cycle_history) (im: I.ideal_memory) (ids1 ids2: block_id_map)
  : Lemma (requires keyed m1 ids1 /\ keyed m2 ids2 /\ copies_faithful m1 h1 im ids1 /\ copies_faithful m2 h2 im ids2 /\
                    (forall (b: block_addr). Some? (ids1 b) ==> faithful_block h1 b) /\
                    (forall (b: block_addr). Some? (ids2 b) ==> faithful_block h2 b) /\
                    I.wf_memory im /\ I.wf_objects im /\
                    minor_wf m1.nursery /\ blocks_fit m1.major /\ minor_wf m2.nursery /\ blocks_fit m2.major /\
                    (forall (id: I.obj_id). (exists (b: block_addr). ids1 b == Some id) <==>
                                            (exists (b: block_addr). ids2 b == Some id)))
          (ensures isomorphic m1 m2)
  = let f = compose ids1 ids2 in
    let fb (b: block_addr)
      : Lemma (match ids1 b with
               | Some id -> Some? (f b) /\ ids2 (Some?.v (f b)) == Some id
               | None -> f b == None)
      = match ids1 b with Some id -> block_of_spec ids2 id | None -> () in
    FStar.Classical.forall_intro fb;
    introduce forall (b': block_addr). is_allocated m2 b' ==> (exists (b: block_addr). f b == Some b')
    with introduce _ ==> _
    with begin
      let Some id = ids2 b' in
      eliminate exists (b: block_addr). ids1 b == Some id
      with (fb b; assert (f b == Some b'))
    end;
    let fields (b b': block_addr) (i: nat)
      : Lemma (requires f b == Some b' /\ i < block_size m1 b)
              (ensures block_tag m1 b == block_tag m2 b' /\ block_size m1 b == block_size m2 b' /\
                       (if block_tag m1 b < 251
                        then word_corresponds m1 m2 f (block_field m1 b i) (block_field m2 b' i)
                        else block_field m1 b i == block_field m2 b' i))
      = fb b;
        let Some id = ids1 b in
        rep_of m1 h1 im ids1 b id;
        rep_of m2 h2 im ids2 b' id;
        let o = Seq.index im.I.objects id in
        O.no_scan_tag_val ();
        assert (I.valid_id im id ==> (Scannable? o.I.fields <==> I.tag_scannable o.I.tag));
        let w1 = block_field m1 b i in
        let w2 = block_field m2 b' i in
        match o.I.fields with
        | I.Scannable vs ->
            let v = Seq.index vs i in
            assert (I.field_at o i == I.FValue v);
            assert (value_rep ids1 v w1 /\ value_rep ids2 v w2);
            assert (I.valid_value im v);
            (match v with
             | I.Word w -> word_points_nowhere m1 w; word_points_nowhere m2 w
             | I.Ptr { I.head = hd; I.infix_offset = k } ->
                 ptr_points_into m1 h1 im ids1 hd k w1;
                 ptr_points_into m2 h2 im ids2 hd k w2;
                 eliminate exists (c1: block_addr). ids1 c1 == Some hd /\ points_into m1 w1 c1 k
                 with eliminate exists (c2: block_addr). ids2 c2 == Some hd /\ points_into m2 w2 c2 k
                 with (fb c1; assert (f c1 == Some c2)))
        | I.NoScan ws -> assert (I.field_at o i == I.FRaw (Seq.index ws i))
    in
    introduce forall (b b': block_addr). f b == Some b' ==>
       block_tag m1 b == block_tag m2 b' /\ block_size m1 b == block_size m2 b' /\
       (forall (i: nat). i < block_size m1 b ==>
          (if block_tag m1 b < 251
           then word_corresponds m1 m2 f (block_field m1 b i) (block_field m2 b' i)
           else block_field m1 b i == block_field m2 b' i))
    with introduce _ ==> _
    with begin
      fb b;
      let Some id = ids1 b in
      header_of m1 h1 im ids1 b id;
      header_of m2 h2 im ids2 b' id;
      introduce forall (i: nat). i < block_size m1 b ==>
          (if block_tag m1 b < 251
           then word_corresponds m1 m2 f (block_field m1 b i) (block_field m2 b' i)
           else block_field m1 b i == block_field m2 b' i)
      with introduce _ ==> _ with fields b b' i
    end;
    assert (forall (b: block_addr). Some? (f b) <==> is_allocated m1 b);
    assert (forall (b b': block_addr). f b == Some b' ==> is_allocated m2 b');
    assert (forall (b1 b2: block_addr). Some? (f b1) /\ f b1 == f b2 ==> b1 == b2);
    assert (isomorphic m1 m2)
#pop-options

/// ---------------------------------------------------------------------------
/// The corollary
/// ---------------------------------------------------------------------------

/// **The incremental run is isomorphic to its hoisted run**, given that the
/// program stores no young-looking word and the step hypotheses
/// (`GC.Gen.Run.Hoisted.Steps.step_hyps`).
let hoisted_isomorphic_given (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                             (#es_h: list event) (#r_h: real_state) (rn_h: run (initial_state ()) es_h r_h)
                             (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ executes rn_h ps /\
                    kinds es_h == hoist (kinds es) /\ r.phase == Ph.Idle /\
                    program_no_young ps /\ start_snapshot /\ minor_promotes)
          (ensures isomorphic r.memory r_h.memory)
  = GC.Gen.Run.Hoisted.Nursery.nursery_frames ();
    hoisted_idle rn_h ps (kinds es);
    ids_at_idle rn ps;
    ids_at_idle rn_h ps;
    acc_along rn ps;
    let lh (id: I.obj_id) : Lemma (live_ids ps (kinds es_h) id <==> live_ids ps (kinds es) id) =
      live_ids_hoist ps (kinds es) id in
    FStar.Classical.forall_intro lh;
    simulation rn ps;
    simulation rn_h ps;
    let h = history_of_run rn in
    let h_h = history_of_run rn_h in
    real_shape r h;
    real_shape r_h h_h;
    assert (forall (b: block_addr). Some? (ids_of_run rn b) ==> faithful_block h b);
    assert (forall (b: block_addr). Some? (ids_of_run rn_h b) ==> faithful_block h_h b);
    iso_from_ids r.memory r_h.memory h h_h (I.ideal_run ps) (ids_of_run rn) (ids_of_run rn_h)
