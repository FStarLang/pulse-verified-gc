module GC.Gen.Run.FloatingGarbage

open FStar.List.Tot
open GC.Gen.Run.Step
open GC.Model.Represents
open GC.Gen.Run.Simulation
open GC.Gen.Run.IdAccounting

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module H = GC.Gen.Run.Hoisted
module MH = GC.Gen.MinorHeap
module LP = FStar.List.Tot.Properties
module Cl = FStar.Classical

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Reachability, closed sets
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let root_reach (m: I.ideal_memory) (x: I.obj_id)
  : Lemma (requires I.root_names m x) (ensures I.reachable m x)
  = assert (I.reach_within m 0 x)

let reach_step (m: I.ideal_memory) (src x: I.obj_id)
  : Lemma (requires I.reachable m src /\ I.points_to m src x) (ensures I.reachable m x)
  = eliminate exists (n: nat). I.reach_within m n src
    with assert (I.reach_within m (n + 1) x)

/// A set that holds the roots' targets and is closed under the edges holds
/// everything reachable.
let rec reach_closed_n (m: I.ideal_memory) (p: I.obj_id -> prop) (n: nat) (x: I.obj_id)
  : Lemma (requires (forall (y: I.obj_id). I.root_names m y ==> p y) /\
                    (forall (src y: I.obj_id). p src /\ I.points_to m src y ==> p y))
          (ensures I.reach_within m n x ==> p x)
          (decreases n)
  = if n = 0 then ()
    else begin
      reach_closed_n m p (n - 1) x;
      introduce forall (src: I.obj_id). I.reach_within m (n - 1) src ==> p src
      with reach_closed_n m p (n - 1) src
    end
#pop-options

let reach_closed (m: I.ideal_memory) (p: I.obj_id -> prop) (x: I.obj_id)
  : Lemma (requires (forall (y: I.obj_id). I.root_names m y ==> p y) /\
                    (forall (src y: I.obj_id). p src /\ I.points_to m src y ==> p y) /\
                    I.reachable m x)
          (ensures p x)
  = eliminate exists (n: nat). I.reach_within m n x
    with reach_closed_n m p n x

/// ---------------------------------------------------------------------------
/// One event
/// ---------------------------------------------------------------------------

/// What a value the program may use points at is reachable.
let usable_target (m: I.ideal_memory) (v: I.value) (x: I.obj_id)
  : Lemma (requires I.usable m v /\ I.target v == Some x) (ensures I.reachable m x)
  = ()

#push-options "--fuel 1 --ifuel 1"
let alloc_closed (m: I.ideal_memory) (tag: I.tag_t) (size: nat) (init: I.ideal_fields)
  : Lemma (requires I.wf_event m (I.Alloc tag size init))
          (ensures (let m' = I.ideal_step m (I.Alloc tag size init) in
                    let n = Seq.length m.I.objects in
                    (forall (y: I.obj_id). I.root_names m' y ==> (I.reachable m y \/ y == n)) /\
                    (forall (src y: I.obj_id). (I.reachable m src \/ src == n) /\ I.points_to m' src y ==>
                                               (I.reachable m y \/ y == n))))
  = let m' = I.ideal_step m (I.Alloc tag size init) in
    let n = Seq.length m.I.objects in
    let o : I.ideal_object = { I.tag = tag; I.size = size; I.fields = init } in
    assert (m'.I.objects == Seq.snoc m.I.objects o);
    assert (m'.I.roots == Seq.snoc m.I.roots (I.Ptr { I.head = n; I.infix_offset = 0 }));
    introduce forall (y: I.obj_id). I.root_names m' y ==> (I.reachable m y \/ y == n)
    with introduce _ ==> _
    with eliminate exists (i: nat). i < Seq.length m'.I.roots /\ I.target (Seq.index m'.I.roots i) == Some y
    with begin
      if i < Seq.length m.I.roots then begin
        assert (Seq.index m'.I.roots i == Seq.index m.I.roots i);
        root_reach m y
      end else
        assert (Seq.index m'.I.roots i == I.Ptr { I.head = n; I.infix_offset = 0 })
    end;
    introduce forall (src y: I.obj_id). (I.reachable m src \/ src == n) /\ I.points_to m' src y ==>
                                        (I.reachable m y \/ y == n)
    with introduce _ ==> _
    with begin
      if src < n then begin
        assert (Seq.index m'.I.objects src == Seq.index m.I.objects src);
        assert (I.points_to m src y);
        reach_step m src y
      end else begin
        assert (Seq.index m'.I.objects src == o);
        let vs = I.field_values o in
        eliminate exists (i: nat). i < Seq.length vs /\ I.target (Seq.index vs i) == Some y
        with (match init with
              | I.Scannable ws -> usable_target m (Seq.index ws i) y
              | I.NoScan _ -> ())
      end
    end

let write_closed (m: I.ideal_memory) (obj: I.obj_id) (j: nat) (v: I.value)
  : Lemma (requires I.wf_event m (I.Write obj j v))
          (ensures (let m' = I.ideal_step m (I.Write obj j v) in
                    (forall (y: I.obj_id). I.root_names m' y ==> I.reachable m y) /\
                    (forall (src y: I.obj_id). I.reachable m src /\ I.points_to m' src y ==> I.reachable m y)))
  = let m' = I.ideal_step m (I.Write obj j v) in
    let o = Seq.index m.I.objects obj in
    let o' = I.update_field o j v in
    assert (m'.I.objects == Seq.upd m.I.objects obj o');
    assert (m'.I.roots == m.I.roots);
    introduce forall (y: I.obj_id). I.root_names m' y ==> I.reachable m y
    with introduce _ ==> _ with root_reach m y;
    introduce forall (src y: I.obj_id). I.reachable m src /\ I.points_to m' src y ==> I.reachable m y
    with introduce _ ==> _
    with begin
      if src <> obj then begin
        assert (Seq.index m'.I.objects src == Seq.index m.I.objects src);
        assert (I.points_to m src y);
        reach_step m src y
      end else begin
        assert (Seq.index m'.I.objects src == o');
        match o.I.fields with
        | I.Scannable vs ->
            assert (I.field_values o' == Seq.upd vs j v);
            eliminate exists (i: nat). i < Seq.length (Seq.upd vs j v) /\ I.target (Seq.index (Seq.upd vs j v) i) == Some y
            with begin
              if i = j then usable_target m v y
              else begin
                assert (Seq.index (Seq.upd vs j v) i == Seq.index vs i);
                assert (I.points_to m obj y);
                reach_step m obj y
              end
            end
        | I.NoScan ws ->
            let I.Word w = v in
            assert (o'.I.fields == I.NoScan (Seq.upd ws j w));
            assert (I.field_values o' == Seq.empty)
      end
    end

let set_roots_closed (m: I.ideal_memory) (rs: Seq.seq I.value)
  : Lemma (requires I.wf_event m (I.SetRoots rs))
          (ensures (let m' = I.ideal_step m (I.SetRoots rs) in
                    (forall (y: I.obj_id). I.root_names m' y ==> I.reachable m y) /\
                    (forall (src y: I.obj_id). I.reachable m src /\ I.points_to m' src y ==> I.reachable m y)))
  = let m' = I.ideal_step m (I.SetRoots rs) in
    assert (m'.I.objects == m.I.objects);
    introduce forall (y: I.obj_id). I.root_names m' y ==> I.reachable m y
    with introduce _ ==> _
    with eliminate exists (i: nat). i < Seq.length rs /\ I.target (Seq.index rs i) == Some y
    with usable_target m (Seq.index rs i) y;
    introduce forall (src y: I.obj_id). I.reachable m src /\ I.points_to m' src y ==> I.reachable m y
    with introduce _ ==> _
    with begin
      assert (I.points_to m src y);
      reach_step m src y
    end
#pop-options

#push-options "--fuel 1 --ifuel 1"
let garbage_stays_garbage_step m e id =
  let m' = I.ideal_step m e in
  match e with
  | I.Alloc tag size init ->
      let n = Seq.length m.I.objects in
      alloc_closed m tag size init;
      let p (y: I.obj_id) : prop = I.reachable m y \/ y == n in
      Cl.move_requires (reach_closed m' p) id
  | I.Write obj j v ->
      write_closed m obj j v;
      Cl.move_requires (reach_closed m' (I.reachable m)) id
  | I.Read _ _ -> ()
  | I.SetRoots rs ->
      set_roots_closed m rs;
      Cl.move_requires (reach_closed m' (I.reachable m)) id
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec stays_garbage (m: I.ideal_memory) (ps: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program_from m ps /\ I.valid_id m id /\ ~(I.reachable m id))
          (ensures I.valid_id (I.ideal_run_from m ps) id /\ ~(I.reachable (I.ideal_run_from m ps) id))
          (decreases ps)
  = match ps with
    | [] -> ()
    | e :: rest ->
        garbage_stays_garbage_step m e id;
        stays_garbage (I.ideal_step m e) rest id

let garbage_stays_garbage m ps id = stays_garbage m ps id

let rec ideal_run_from_append (m: I.ideal_memory) (ps1 ps2: list I.program_event)
  : Lemma (ensures I.ideal_run_from m (ps1 @ ps2) == I.ideal_run_from (I.ideal_run_from m ps1) ps2 /\
                   (I.wf_program_from m (ps1 @ ps2) ==> I.wf_program_from (I.ideal_run_from m ps1) ps2))
          (decreases ps1)
  = match ps1 with
    | [] -> ()
    | e :: rest -> ideal_run_from_append (I.ideal_step m e) rest ps2
#pop-options

let garbage_stays_garbage_run ps1 ps2 id =
  ideal_run_from_append I.empty_ideal ps1 ps2;
  garbage_stays_garbage (I.ideal_run ps1) ps2 id

/// ---------------------------------------------------------------------------
/// Lists
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1"
let rec alloc_count_append (l1 l2: list event)
  : Lemma (ensures alloc_count (l1 @ l2) == alloc_count l1 + alloc_count l2) (decreases l1)
  = match l1 with [] -> () | _ :: t -> alloc_count_append t l2

let rec n_program_append (l1 l2: list kind)
  : Lemma (ensures n_program (l1 @ l2) == n_program l1 + n_program l2) (decreases l1)
  = match l1 with [] -> () | _ :: t -> n_program_append t l2

let rec starts_snoc (es: list event) (e: event)
  : Lemma (ensures starts_a_cycle (es @ [e]) == (starts_a_cycle es || StartCycle? e)) (decreases es)
  = match es with [] -> () | _ :: t -> starts_snoc t e
#pop-options

let kinds_append (l1 l2: list event) : Lemma (kinds (l1 @ l2) == kinds l1 @ kinds l2) =
  LP.map_append kind_of l1 l2

/// `l1` is a prefix of `l @ [x]` no longer than `l`: a prefix of `l`.
#push-options "--fuel 2 --ifuel 1"
let prefix_of_snoc (#t: Type) (l1 l2 l: list t) (x: t)
  : Lemma (requires l1 @ l2 == l @ [x] /\ length l1 <= length l)
          (ensures exists (l2': list t). l == l1 @ l2' /\ l2 == l2' @ [x])
  = LP.append_length l1 l2;
    LP.append_length l [x];
    let (l2', y) = unsnoc l2 in
    LP.lemma_unsnoc_snoc l2;
    assert (l2 == l2' @ [y]);
    LP.append_assoc l1 l2' [y];
    LP.append_length_inv_tail (l1 @ l2') [y] l [x]
#pop-options

/// ---------------------------------------------------------------------------
/// Runs
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1"
let run_append_done (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
  : Lemma (ids_of_run (run_append rn1 (Done r1)) == ids_of_run rn1 /\
           (forall (ps: list I.program_event). executes (run_append rn1 (Done r1)) ps <==> executes rn1 ps))
  = ()

let run_append_step (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
                    (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
                    (e: event) (r3: real_state) (s: squash (step r2 e r3))
  : Lemma (ids_of_run (run_append rn1 (Step rn2 e r3 s)) ==
             update_block_ids (ids_of_run (run_append rn1 rn2)) (alloc_count (es1 @ es2)) r2 e r3 /\
           (forall (ps: list I.program_event).
              executes (run_append rn1 (Step rn2 e r3 s)) ps <==>
              (if is_program_event e
               then exists (ps': list I.program_event) (pe: I.program_event).
                      ps == ps' @ [pe] /\ executes (run_append rn1 rn2) ps' /\
                      translates r2.memory (ids_of_run (run_append rn1 rn2)) e pe
               else executes (run_append rn1 rn2) ps /\
                    collector_roots_represented (ids_of_run (run_append rn1 rn2)) (I.ideal_run ps).I.roots e)))
  = ()
#pop-options

/// A step gives a block an id only if some block had it, or it is the next.
#push-options "--fuel 0 --ifuel 1"
let update_image (ids: block_id_map) (next: I.obj_id) (r: real_state) (e: event) (r': real_state)
                 (id: I.obj_id)
  : Lemma (requires id <> next /\ ~(exists (b: block_addr). ids b == Some id))
          (ensures ~(exists (b: block_addr). update_block_ids ids next r e r' b == Some id))
  = introduce forall (b: block_addr). update_block_ids ids next r e r' b =!= Some id
    with begin
      match e with
      | Alloc _ _ _ _ -> ()
      | Minor roots ->
          (match b with
           | Nursery _ -> ()
           | Major x -> ())
      | _ -> ()
    end
#pop-options

#push-options "--fuel 0 --ifuel 1"
let rec gone_aux (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
                 (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2) (id: I.obj_id)
  : Lemma (requires id < alloc_count es1 /\ no_block rn1 id)
          (ensures no_block (run_append rn1 rn2) id)
          (decreases rn2)
  = match rn2 with
    | Done _ -> run_append_done rn1
    | Step #_ #es2' #r' rn2' e r3 s ->
        gone_aux rn1 rn2' id;
        run_append_step rn1 rn2' e r3 s;
        alloc_count_append es1 es2';
        update_image (ids_of_run (run_append rn1 rn2')) (alloc_count (es1 @ es2')) r' e r3 id
#pop-options

let gone_stays_gone #es1 #r1 rn1 #es2 #r2 rn2 id = gone_aux rn1 rn2 id

/// ---------------------------------------------------------------------------
/// The accounting
/// ---------------------------------------------------------------------------

#push-options "--fuel 2 --ifuel 2"
let rec executes_length (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                        (ps: list I.program_event)
  : Lemma (requires executes rn ps) (ensures n_program (kinds es) == List.Tot.length ps) (decreases rn)
  = match rn with
    | Done _ -> ()
    | Step #_ #es' #r1 rn' e _ _ ->
        kinds_snoc es' e;
        n_program_snoc (kinds es') (kind_of e);
        if is_program_event e then
          eliminate exists (ps': list I.program_event) (pe: I.program_event).
            ps == ps' @ [pe] /\ executes rn' ps' /\ translates r1.memory (ids_of_run rn') e pe
          with begin
            executes_length rn' ps';
            LP.append_length ps' [pe]
          end
        else executes_length rn' ps
#pop-options

#push-options "--fuel 1 --ifuel 1"
/// The accounting's memory is the program's.
let rec account_mem (a: acc) (ks: list kind) (ps: list I.program_event)
  : Lemma (requires n_program ks == length ps)
          (ensures (account a ks ps).mem == I.ideal_run_from a.mem ps)
          (decreases ks)
  = match ks with
    | [] -> ()
    | k :: ks' ->
        if is_program_kind k
        then (match ps with pe :: ps' -> account_mem (kind_step a k (Some pe)) ks' ps')
        else account_mem (kind_step a k None) ks' ps

let rec promo_nurs (a: acc) (n: nat) (id: I.obj_id)
  : Lemma (requires promo_within a n id) (ensures a.nurs id) (decreases n)
  = if n = 0 then ()
    else Cl.move_requires (promo_nurs a (n - 1)) id
#pop-options

/// A minor collection promotes only nursery objects.
let promoted_nurs (a: acc) (id: I.obj_id)
  : Lemma (requires promoted a id) (ensures a.nurs id)
  = eliminate exists (n: nat). promo_within a n id
    with promo_nurs a n id

/// The object exists and the program cannot reach it.
let pending (a: acc) (id: I.obj_id) : prop =
  I.valid_id a.mem id /\ ~(I.reachable a.mem id)

/// ... and the accounting no longer counts it.
let dropped (a: acc) (id: I.obj_id) : prop =
  pending a id /\ ~(a.kept id) /\ ~(a.nurs id)

#push-options "--fuel 0 --ifuel 2"
let program_kind_step (a: acc) (k: kind) (pe: I.program_event) (id: I.obj_id)
  : Lemma (requires is_program_kind k /\ pending a id /\ I.wf_event a.mem pe)
          (ensures (let a' = kind_step a k (Some pe) in
                    a'.mem == I.ideal_step a.mem pe /\ pending a' id /\ (dropped a id ==> dropped a' id)))
  = garbage_stays_garbage_step a.mem pe id

let collector_kind_step (a: acc) (k: kind) (id: I.obj_id)
  : Lemma (requires ~(is_program_kind k) /\ pending a id)
          (ensures (let a' = kind_step a k None in
                    a'.mem == a.mem /\ pending a' id /\ (dropped a id ==> dropped a' id) /\
                    (KStart? k /\ ~(a.nurs id) ==> dropped a' id)))
  = Cl.move_requires (promoted_nurs a) id
#pop-options

/// When a cycle starts, the nursery is empty: the accounting has nothing in
/// it.
#push-options "--fuel 0 --ifuel 1"
let start_nursery_empty (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
                        (ps: list I.program_event) (roots: Seq.seq U64.t) (r': real_state) (id: I.obj_id)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ step r (StartCycle roots) r')
          (ensures ~((account empty_acc (kinds es) ps).nurs id))
  = H.nursery_ids rn ps;
    simulation rn ps;
    let ids = ids_of_run rn in
    let ms = r.memory.nursery in
    assert (ms == MH.minor_reset ms);
    introduce forall (o: U64.t). ids (Nursery o) =!= Some id
    with begin
      MH.minor_reset_objects_not_mem ms o;
      assert (~(is_allocated r.memory (Nursery o)))
    end
#pop-options

/// **Along the run after the point**: the object stays pending, and once a
/// cycle has started, the accounting has dropped it.
#push-options "--fuel 1 --ifuel 1"
let rec along (#es1: list event) (#r1: real_state) (rn1: run (initial_state ()) es1 r1)
              (#es2: list event) (#r2: real_state) (rn2: run r1 es2 r2)
              (ps1 ps2: list I.program_event) (id: I.obj_id)
  : Lemma (requires I.wf_program (ps1 @ ps2) /\ executes (run_append rn1 rn2) (ps1 @ ps2) /\
                    n_program (kinds es1) == length ps1 /\
                    I.valid_id (I.ideal_run ps1) id /\ ~(I.reachable (I.ideal_run ps1) id))
          (ensures (let a = account empty_acc (kinds (es1 @ es2)) (ps1 @ ps2) in
                    a.mem == I.ideal_run (ps1 @ ps2) /\
                    pending a id /\ (starts_a_cycle es2 ==> dropped a id)))
          (decreases rn2)
  = executes_length (run_append rn1 rn2) (ps1 @ ps2);
    account_mem empty_acc (kinds (es1 @ es2)) (ps1 @ ps2);
    match rn2 with
    | Done _ ->
        LP.append_l_nil es1;
        LP.append_length ps1 ps2;
        assert (ps2 == []);
        LP.append_l_nil ps1
    | Step #_ #es2' #r' rn2' e r3 s ->
        let rn' = run_append rn1 rn2' in
        run_append_step rn1 rn2' e r3 s;
        LP.append_assoc es1 es2' [e];
        kinds_snoc (es1 @ es2') e;
        starts_snoc es2' e;
        kinds_append es1 es2';
        n_program_append (kinds es1) (kinds es2');
        if is_program_event e then
          eliminate exists (ps': list I.program_event) (pe: I.program_event).
            ps1 @ ps2 == ps' @ [pe] /\ executes rn' ps' /\ translates r'.memory (ids_of_run rn') e pe
          with begin
            executes_length rn' ps';
            prefix_of_snoc ps1 ps2 ps' pe;
            eliminate exists (ps2': list I.program_event). ps' == ps1 @ ps2' /\ ps2 == ps2' @ [pe]
            with begin
              I.ideal_run_snoc ps' pe;
              along rn1 rn2' ps1 ps2' id;
              account_snoc empty_acc (kinds (es1 @ es2')) ps' (kind_of e) pe;
              program_kind_step (account empty_acc (kinds (es1 @ es2')) ps') (kind_of e) pe id
            end
          end
        else begin
          along rn1 rn2' ps1 ps2 id;
          executes_length rn' (ps1 @ ps2);
          account_snoc empty_acc (kinds (es1 @ es2')) (ps1 @ ps2) (kind_of e) (I.Read 0 0);
          (match e with
           | StartCycle roots -> start_nursery_empty rn' (ps1 @ ps2) roots r3 id
           | _ -> ());
          collector_kind_step (account empty_acc (kinds (es1 @ es2')) (ps1 @ ps2)) (kind_of e) id
        end
#pop-options

/// ---------------------------------------------------------------------------
/// The theorems
/// ---------------------------------------------------------------------------

let floating_garbage_freed #es1 #r1 rn1 #es2 #r2 rn2 ps1 ps2 id =
  executes_length rn1 ps1;
  along rn1 rn2 ps1 ps2 id;
  H.step_hyps_hold ();
  H.ids_at_idle (run_append rn1 rn2) (ps1 @ ps2)

let floating_garbage_bound #es1 #r1 rn1 #es2 #r2 rn2 ps1 ps2 id #es3 #r3 rn3 =
  floating_garbage_freed rn1 rn2 ps1 ps2 id;
  executes_alloc_count rn1 ps1;
  alloc_count_append es1 es2;
  gone_stays_gone (run_append rn1 rn2) rn3 id
