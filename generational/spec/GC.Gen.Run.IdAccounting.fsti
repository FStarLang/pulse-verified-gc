/// ---------------------------------------------------------------------------
/// GC.Gen.Run.IdAccounting - which objects have a block, from the program
/// and the schedule alone
/// ---------------------------------------------------------------------------
///
/// The id-level accounting of a run (mutator-equivalence-plan.md, section 1,
/// the hoisted-run corollary): which ideal objects have a block in the real
/// memory, computed from the program's events `ps` and the schedule's kinds
/// `ks` (`GC.Gen.Run.Step.kinds`) -- no addresses, no colours, no free list.
///
/// The accounting state (`acc`) is
///   * `mem`: the ideal memory so far (`GC.Model.Ideal.ideal_step` over the
///     program's events);
///   * `nurs`: the objects in the nursery -- allocated there since the last
///     minor collection;
///   * `kept`: the objects of the major heap's kept blocks -- what was
///     reachable in the ideal memory at the last cycle start, and what was
///     put into the major heap since (allocated there directly, or promoted
///     by a minor collection);
///   * `rt`: the remembered slots, as (object, field) -- the major slots into
///     which a nursery pointer was stored since the last minor collection
///     (an allocation's young initial values; a write of a young value over
///     a value that was not young, the barrier's `GB.modify_records`).
///
/// One step per kind (`kind_step`):
///   * an allocation adds the next id to the nursery or to `kept` (the
///     allocation site is part of the kind), and its young initial fields to
///     `rt` (major only);
///   * a write records its slot when the barrier would;
///   * a minor collection adds to `kept` the nursery objects it promotes
///     (`promoted`: the nursery objects reachable, through nursery objects,
///     from the roots and the values of the remembered slots) and empties the
///     nursery and `rt`;
///   * the start of a cycle makes `kept` what the program can reach;
///   * a slice changes nothing.
///
/// `live_ids ps ks`: the ids with a block when the collector is idle
/// (`GC.Gen.Run.Hoisted.ids_at_idle` proves that every run carrying out `ps`
/// with kinds `ks` has exactly these, idle).  Slices do not count, so
/// moving them does not change it: `live_ids ps (hoist ks) == live_ids ps ks`
/// (`account_hoist`).

module GC.Gen.Run.IdAccounting

open FStar.List.Tot
open GC.Gen.Run.Step

module I = GC.Model.Ideal

/// ---------------------------------------------------------------------------
/// The accounting state
/// ---------------------------------------------------------------------------

noeq type acc = {
  mem: I.ideal_memory;
  nurs: I.obj_id -> prop;
  kept: I.obj_id -> prop;
  rt: I.obj_id -> nat -> prop;
}

/// Nothing allocated.
let empty_acc : acc =
  { mem = I.empty_ideal; nurs = (fun _ -> False); kept = (fun _ -> False); rt = (fun _ _ -> False) }

/// A young value: a pointer to an object in the nursery.
let young (a: acc) (v: I.value) : prop =
  match v with
  | I.Ptr { head } -> a.nurs head
  | I.Word _ -> False

/// The value in field `j` of object `id` (a scannable object's field).
let field_value (m: I.ideal_memory) (id: I.obj_id) (j: nat) : option I.value =
  if I.valid_id m id then
    (let vs = I.field_values (Seq.index m.I.objects id) in
     if j < Seq.length vs then Some (Seq.index vs j) else None)
  else None

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

/// What a minor collection starts from: a nursery object named by a root or
/// by the value of a remembered slot.
let promo_seed (a: acc) (id: I.obj_id) : prop =
  a.nurs id /\
  (I.root_names a.mem id \/
   (exists (x: I.obj_id) (j: nat). a.rt x j /\
      (match field_value a.mem x j with Some v -> I.target v == Some id | None -> False)))

/// Reached from a seed in at most `n` edges, through nursery objects.
let rec promo_within (a: acc) (n: nat) (id: I.obj_id) : Tot prop (decreases n) =
  if n = 0 then promo_seed a id
  else promo_within a (n - 1) id \/
       (exists (src: I.obj_id). promo_within a (n - 1) src /\ I.points_to a.mem src id /\ a.nurs id)

/// **What a minor collection promotes.**
let promoted (a: acc) (id: I.obj_id) : prop = exists (n: nat). promo_within a n id

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

/// The remembered slots of a new major object: its young initial values.
let alloc_rt (a: acc) (init: I.ideal_fields) (j: nat) : prop =
  match init with
  | I.Scannable vs -> j < Seq.length vs /\ young a (Seq.index vs j)
  | I.NoScan _ -> False

/// A write remembers its slot: a scannable major object, a young value over
/// a value that was not young (`GB.modify_records`).
let write_records (a: acc) (obj: I.obj_id) (i: nat) (v: I.value) : prop =
  ~(a.nurs obj) /\ young a v /\
  (match field_value a.mem obj i with Some old -> ~(young a old) | None -> False)

/// A program event, allocated in the nursery or the major heap (`site`).
let program_step (a: acc) (site: alloc_site) (pe: I.program_event) : acc =
  let n = Seq.length a.mem.I.objects in
  let mem' = I.ideal_step a.mem pe in
  match pe with
  | I.Alloc _ _ init ->
      (match site with
       | InNursery -> { a with mem = mem'; nurs = (fun id -> a.nurs id \/ id == n) }
       | InMajor -> { a with mem = mem'; kept = (fun id -> a.kept id \/ id == n);
                             rt = (fun x j -> a.rt x j \/ (x == n /\ alloc_rt a init j)) })
  | I.Write obj i v ->
      { a with mem = mem'; rt = (fun x j -> a.rt x j \/ (x == obj /\ j == i /\ write_records a obj i v)) }
  | _ -> { a with mem = mem' }

/// A minor collection: the promoted objects join `kept`; the nursery and the
/// remembered set are emptied.
let minor_acc (a: acc) : acc =
  { a with kept = (fun id -> a.kept id \/ promoted a id); nurs = (fun _ -> False); rt = (fun _ _ -> False) }

/// The start of a cycle: `kept` is what the program can reach.
let start_acc (a: acc) : acc = { a with kept = I.reachable a.mem }

/// The kinds that carry a program event.
let is_program_kind (k: kind) : bool = KAlloc? k || KWrite? k || KRead? k || KSetRoots? k

let site_of (k: kind) : alloc_site =
  match k with
  | KAlloc s -> s
  | _ -> InMajor

/// **One step of the accounting.**
let kind_step (a: acc) (k: kind) (pe: option I.program_event) : acc =
  if is_program_kind k
  then (match pe with Some pe -> program_step a (site_of k) pe | None -> a)
  else (match k with
        | KMinor -> minor_acc a
        | KStart -> start_acc a
        | _ -> a)

/// **The accounting of a schedule**, consuming a program event at each
/// program kind.
let rec account (a: acc) (ks: list kind) (ps: list I.program_event) : Tot acc (decreases ks) =
  match ks with
  | [] -> a
  | k :: ks' ->
      if is_program_kind k
      then (match ps with
            | [] -> a
            | pe :: ps' -> account (kind_step a k (Some pe)) ks' ps')
      else account (kind_step a k None) ks' ps

/// **The ids with a block, idle**: kept, or in the nursery.
let live_ids (ps: list I.program_event) (ks: list kind) (id: I.obj_id) : prop =
  let a = account empty_acc ks ps in
  a.kept id \/ a.nurs id

/// The number of program kinds.
let rec n_program (ks: list kind) : nat =
  match ks with
  | [] -> 0
  | k :: ks' -> (if is_program_kind k then 1 else 0) + n_program ks'

/// ---------------------------------------------------------------------------
/// Facts
/// ---------------------------------------------------------------------------

/// The kind of an event carries a program event exactly when the event is one.
val program_kind_of (e: event)
  : Lemma (is_program_kind (kind_of e) == is_program_event e)
          [SMTPat (kind_of e)]

/// **Moving the slices does not change the accounting.**
val account_hoist (a: acc) (ks: list kind) (ps: list I.program_event)
  : Lemma (ensures account a (hoist ks) ps == account a ks ps) (decreases ks)

val live_ids_hoist (ps: list I.program_event) (ks: list kind) (id: I.obj_id)
  : Lemma (live_ids ps (hoist ks) id <==> live_ids ps ks id)

/// The accounting of a schedule that grows at the end (as runs do).
val account_snoc (a: acc) (ks: list kind) (ps: list I.program_event) (k: kind) (pe: I.program_event)
  : Lemma (requires n_program ks == List.Tot.length ps)
          (ensures (if is_program_kind k
                    then account a (ks @ [k]) (ps @ [pe]) == kind_step (account a ks ps) k (Some pe)
                    else account a (ks @ [k]) ps == kind_step (account a ks ps) k None))
          (decreases ks)

val n_program_snoc (ks: list kind) (k: kind)
  : Lemma (n_program (ks @ [k]) == n_program ks + (if is_program_kind k then 1 else 0))

val kinds_snoc (es: list event) (e: event)
  : Lemma (kinds (es @ [e]) == kinds es @ [kind_of e])
