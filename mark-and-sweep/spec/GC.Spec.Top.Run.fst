/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Run - runs of a collector built from components, and the
/// top-level theorem `gc_correct` (stated, not proved)
/// ---------------------------------------------------------------------------
///
/// A collector is a record of components `comps` (its heap and nursery types
/// and their representation, allocator, sweep, mark, minor collection,
/// barrier) and a style (`Sequential` | `Incremental`).  A configuration holds
/// the collector's own heaps; every statement about it is about a model
/// world that represents it (`views`).  The conclusions read one such world,
/// `vw x` (they all have the same blocks, headers and fields, by
/// faithfulness: GC.Spec.Top.Rep.repr_agree), and say that there is one; the
/// mutator's obligations hold of it.
/// A run is a list of events from the initial configuration; `step` is the
/// specification's semantics of one event, and keeps the ghost bookkeeping
/// of the cycle (snapshot, allocated set, heap at the start).
///
/// `gc_correct c sty` is the top-level theorem as a proposition: under the
/// components' contracts and the mutator's obligations, every run satisfies
/// `conclusions` (clauses (0)-(6)).  `gc_correct_local` takes the contracts
/// only at the steps the run takes; it implies `gc_correct`
/// (`gc_correct_local_implies`), so it is the stronger statement, and its
/// hypotheses are the ones a concrete run can discharge (GC.Spec.Top.Vacuity).

module GC.Spec.Top.Run

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
module L = FStar.List.Tot
module Seq = FStar.Seq

noeq type comps = {
  t : Type0;                     (* the collector's major heap *)
  yt : Type0;                    (* its nursery *)
  r : rep t yt;                  (* their representation *)
  k : sweep_kind;
  a : allocator t k;
  s : sweep t k a;
  m : mark t yt;
  n : minor t yt k a;
  b : barrier t;
  fits : capacity t k a.state;   (* the allocator's capacity condition *)
}

type style = | Sequential | Incremental

noeq type config (c: comps) = {
  w       : cworld c.t c.yt;
  ph      : phase c.k.progress;
  ast     : c.a.state;
  (* ghost bookkeeping, kept by the specification *)
  hs      : c.t;                (* the major heap at the cycle's start s *)
  snap    : nat -> prop;        (* snapshot_k = reachable(s) *)
  allocd  : nat -> prop;        (* allocated_k: allocated, or promoted copies, since s *)
  stopped : bool;               (* a minor collection ran out of room *)
}

noeq type event =
  | EAlloc      : sz:size_t -> tag:tag_t -> vs:list value -> event    (* Alloc;Fill *)
  | EYoungAlloc : sz:size_t -> tag:tag_t -> vs:list value -> event   (* YoungAlloc;Fill *)
  | EWrite      : p:ptr -> i:nat -> v:value -> event
  | ERead       : p:ptr -> i:nat -> event          (* load field i into a new root *)
  | ERoots      : roots:list value -> event
  | EMinor      : event
  | EStart      : event
  | ESlice      : event
  | EHandover   : event
  | ESweep      : event
  | EEnd        : event

let is_mutator_event (e: event) : bool =
  EAlloc? e || EYoungAlloc? e || EWrite? e || ERead? e || ERoots? e

/// ---------------------------------------------------------------------------
/// The semantics
/// ---------------------------------------------------------------------------

/// The model worlds that represent a configuration.
let views (#c: comps) (x: config c) (w: world) : prop = cviews c.r x.w w

let has_view (#c: comps) (x: config c) : prop = exists (w: world). views x w

let no_world : world = { maj = empty_heap 0; yng = empty_heap 0; roots = []; rem = [] }

/// One of them (any other has the same blocks, headers and fields).
let vw (#c: comps) (x: config c) : GTot world =
  if FStar.IndefiniteDescription.strong_excluded_middle (has_view x)
  then FStar.IndefiniteDescription.indefinite_description_ghost world (fun w -> views x w)
  else no_world

let wv (#c: comps) (x: config c) : GTot world = vw x
let mj (#c: comps) (x: config c) : GTot mheap = (vw x).maj

let vw_views (#c: comps) (x: config c)
  : Lemma (requires has_view x) (ensures views x (vw x))
  = ()

let init_config (c: comps) (n ny: nat) : GTot (config c) =
  let (h, st) = c.a.init n in
  { w = { cmaj = h; cyng = c.r.yinit ny; croots = []; crem = [] };
    ph = Idle; ast = st; hs = h;
    snap = (fun _ -> False); allocd = (fun _ -> False); stopped = false }

let step (c: comps) (x: config c) (e: event) : GTot (config c) =
  match e with
  | EAlloc sz tag vs ->
    let (h', st', r) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
    (match r with
     | NoRoom -> x
     | Ok o ->
       let (h'', rem') = c.b.binit h' x.w.crem o vs in
       { x with w = { x.w with cmaj = h''; crem = rem'; croots = VPtr (Major o) :: x.w.croots };
                ast = st'; allocd = (fun p -> x.allocd p \/ p == o) })
  | EYoungAlloc sz tag vs ->
    (match c.r.yalloc x.w.cyng sz tag vs with
     | Some (o, y') -> { x with w = { x.w with cyng = y'; croots = VPtr (Young o) :: x.w.croots } }
     | None -> x)
  | EWrite (Major o) i v ->
    let (h', rem') = c.b.bwrite (is_marking x.ph) x.w.cmaj x.w.crem o i v in
    { x with w = { x.w with cmaj = h'; crem = rem' } }
  | EWrite (Young o) i v ->
    { x with w = { x.w with cyng = c.r.ywrite x.w.cyng o i v } }
  | ERead (Major o) i ->
    { x with w = { x.w with croots = c.r.read x.w.cmaj o i :: x.w.croots } }
  | ERead (Young o) i ->
    { x with w = { x.w with croots = c.r.yread x.w.cyng o i :: x.w.croots } }
  | ERoots rs ->
    { x with w = { x.w with croots = rs } }
  | EMinor ->
    (match c.n.collect x.ph x.ast x.w with
     | OutOfRoom -> { x with stopped = true }
     | Done h' st' roots' fwd ->
       { x with w = { cmaj = h'; cyng = c.r.yreset x.w.cyng; croots = roots'; crem = [] };
                ast = st';
                allocd = (fun p -> x.allocd p \/ (exists (o: nat). fwd o == Some p)) })
  | EStart ->
    { x with w = { x.w with cmaj = c.m.mstart x.w }; ph = Marking; hs = x.w.cmaj;
             snap = reachable (vw x); allocd = (fun _ -> False) }
  | ESlice ->
    { x with w = { x.w with cmaj = c.m.mslice x.w.cmaj } }
  | EHandover ->
    let (p, st') = c.s.start x.w.cmaj x.ast in
    { x with ph = Sweeping p; ast = st' }
  | ESweep ->
    (match x.ph with
     | Sweeping p ->
       let (p', h', st', _) = c.s.step p x.w.cmaj x.ast in
       { x with w = { x.w with cmaj = h' }; ph = Sweeping p'; ast = st' }
     | _ -> x)
  | EEnd -> { x with ph = Idle }

let enabled (c: comps) (x: config c) (e: event) : prop =
  x.stopped == false /\
  (match e with
   | EYoungAlloc sz tag vs -> Some? (c.r.yalloc x.w.cyng sz tag vs)
   | EStart -> Idle? x.ph
   | ESlice -> Marking? x.ph /\ ~(mark_done (mj x))
   | EHandover -> Marking? x.ph /\ mark_done (mj x)
   | ESweep -> Sweeping? x.ph /\ c.s.done (Sweeping?._0 x.ph) == false
   | EEnd -> Sweeping? x.ph /\ c.s.done (Sweeping?._0 x.ph) == true
   | _ -> True)

/// Sequential: no mutator event while a cycle runs.
let style_ok (#c: comps) (sty: style) (x: config c) (e: event) : prop =
  Sequential? sty ==> (is_mutator_event e ==> Idle? x.ph)

/// ---------------------------------------------------------------------------
/// The mutator's obligations (trusted)
/// ---------------------------------------------------------------------------

/// A value the program may hold: a word of bytes, or a pointer resolving to
/// a reachable object (major or young).
let value_ok (w: world) (v: value) : prop =
  match v with
  | VInt _ -> True
  | VPtr (Major a) -> exists (o: nat). resolve w.maj a == Some o /\ reachable w o
  | VPtr (Young a) -> exists (o: nat). resolve w.yng a == Some o /\ yreachable w o

/// The Fill of a new object: no-scan fields hold any bytes (a closure's
/// infix headers are words of bytes).
let fill_ok (w: world) (tag: tag_t) (vs: list value) : prop =
  scannable tag ==> (forall (i: nat). i < L.length vs ==> value_ok w (L.index vs i))

/// Every word the program stores is one the collector's heap can hold.  The
/// program writes no closure (OCaml's closures are immutable after their
/// Fill; G29), so it never overwrites an infix header.
let mutator_ok_w (c: comps) (w: world) (e: event) : prop =
  match e with
  | EAlloc sz tag vs ->
    tag <> infix_tag /\ L.length vs == sz /\ fill_ok w tag vs /\ storable_all c.r vs
  | EYoungAlloc sz tag vs ->
    tag <> infix_tag /\ L.length vs == sz /\ fill_ok w tag vs /\ storable_all c.r vs
  | EWrite (Major o) i v ->
    is_block w.maj o /\ reachable w o /\ i < wz_of w.maj o /\ tag_of w.maj o <> closure_tag /\
    (scannable (tag_of w.maj o) ==> value_ok w v) /\ c.r.storable v
  | EWrite (Young o) i v ->
    is_block w.yng o /\ yreachable w o /\ i < wz_of w.yng o /\ tag_of w.yng o <> closure_tag /\
    (scannable (tag_of w.yng o) ==> value_ok w v) /\ c.r.storable v
  | ERead (Major o) i -> is_block w.maj o /\ reachable w o /\ i < wz_of w.maj o
  | ERead (Young o) i -> is_block w.yng o /\ yreachable w o /\ i < wz_of w.yng o
  | ERoots rs -> (forall (v: value). L.memP v rs ==> value_ok w v) /\ storable_all c.r rs
  | _ -> True

/// The obligations hold of a model world representing the configuration.
let mutator_ok (#c: comps) (x: config c) (e: event) : prop =
  has_view x /\ mutator_ok_w c (vw x) e

/// ---------------------------------------------------------------------------
/// Runs
/// ---------------------------------------------------------------------------

let rec exec (c: comps) (x: config c) (es: list event) : GTot (config c) (decreases es) =
  match es with
  | [] -> x
  | e :: tl -> exec c (step c x e) tl

let rec take (#t: Type) (n: nat) (l: list t) : list t =
  match l with
  | [] -> []
  | h :: tl -> if n = 0 then [] else h :: take (n - 1) tl

/// The configuration after the first `i` events.
let at (c: comps) (n ny: nat) (es: list event) (i: nat) : GTot (config c) =
  exec c (init_config c n ny) (take i es)

let ev (es: list event) (i: nat{i < L.length es}) : event = L.index es i

/// The run is allowed: heaps of the collector's sizes, every event enabled,
/// in the style, and meeting the mutator's obligations.
let run_ok (c: comps) (sty: style) (n ny: nat) (es: list event) : prop =
  c.r.size_ok n /\ c.r.ysize_ok ny /\
  (forall (i: nat). i < L.length es ==>
    (let x = at c n ny es i in
     let e = ev es i in
     enabled c x e /\ style_ok sty x e /\ mutator_ok x e))

/// The components' contracts at one step.
let hyps_at (c: comps) (x: config c) (e: event) : prop =
  let h = x.w.cmaj in
  let r = c.r in
  free_white_at r c.a x.ph h x.ast /\
  (forall (h': c.t). free_hd_at r c.a x.ast h h') /\
  (match e with
   | EAlloc sz tag vs ->
     alloc_at r c.a x.ph h x.ast sz tag /\
     (let (h', _, res) = c.a.alloc x.ph h x.ast sz tag in
      match res with
      | Ok o -> barrier_init_at r c.b h' x.w.crem o vs
      | NoRoom -> True)
   | EYoungAlloc sz tag vs -> yalloc_ok r x.w.cyng sz tag vs
   | EWrite (Major o) i v ->
     barrier_write_at r c.b (is_marking x.ph) h x.w.crem o i v /\
     inv_frame_at r c.a x.ph h x.ast (fst (c.b.bwrite (is_marking x.ph) h x.w.crem o i v))
   | EWrite (Young o) i v -> ywrite_ok r x.w.cyng o i v
   | EMinor ->
     minor_at r c.n x.ph x.ast x.w /\ yreset_ok r x.w.cyng
   | EStart ->
     mark_start_at r c.m x.w /\ inv_start_at c.a h x.ast /\
     inv_frame_at r c.a Marking h x.ast (c.m.mstart x.w)
   | ESlice ->
     mark_slice_at r c.m h x.snap x.allocd /\ inv_frame_at r c.a x.ph h x.ast (c.m.mslice h)
   | EHandover -> sweep_start_at r c.s h x.ast
   | ESweep -> (match x.ph with Sweeping p -> sweep_step_at r c.s p h x.ast | _ -> True)
   | EEnd -> (match x.ph with Sweeping p -> sweep_done_at r c.s p h x.ast | _ -> True)
   | _ -> True)

let run_hyps (c: comps) (n ny: nat) (es: list event) : prop =
  init_at c.r c.a n /\ yinit_ok c.r ny /\
  (forall (i: nat). i < L.length es ==> hyps_at c (at c n ny es i) (ev es i))

/// ---------------------------------------------------------------------------
/// The partition
/// ---------------------------------------------------------------------------

let live (#c: comps) (x: config c) (o: nat) : prop = x.snap o \/ x.allocd o

let in_use_c (#c: comps) (x: config c) (o: nat) : GTot bool = in_use c.a x.ast x.w.cmaj (mj x) o

let free_word_c (#c: comps) (x: config c) (w: nat) : prop = free_word c.a x.ast x.w.cmaj (mj x) w

let in_use_word_c (#c: comps) (x: config c) (w: nat) : prop = in_use_word c.a x.ast x.w.cmaj (mj x) w

/// kept: in use and in snapshot_k U allocated_k; while idle, all in use.
let kept (#c: comps) (x: config c) (o: nat) : prop =
  in_use_c x o == true /\ (Idle? x.ph \/ live x o)

let unswept_now (#c: comps) (x: config c) (o: nat) : bool =
  match x.ph with
  | Idle -> false
  | Marking -> true
  | Sweeping p -> c.k.unswept p o

/// pending: in use, not kept, not yet swept.
let pending (#c: comps) (x: config c) (o: nat) : prop =
  in_use_c x o == true /\ ~(Idle? x.ph) /\ ~(live x o) /\ unswept_now x o == true

let exactly_one (p q r: prop) : prop =
  (p \/ q \/ r) /\ ~(p /\ q) /\ ~(p /\ r) /\ ~(q /\ r)

let partition (#c: comps) (x: config c) : prop =
  forall (w: nat). w < (mj x).size ==>
    exactly_one (exists (o: nat). covers (mj x) o w /\ kept x o)
                (exists (o: nat). covers (mj x) o w /\ pending x o)
                (free_word_c x w)

/// ---------------------------------------------------------------------------
/// The conclusions
/// ---------------------------------------------------------------------------

/// A pointer the program or a reachable object holds resolves to an object
/// in use (major) or a young block.
let resolves_ok (#c: comps) (x: config c) (v: value) : prop =
  match v with
  | VPtr (Major a) -> exists (o: nat). resolve (mj x) a == Some o /\ in_use_c x o == true
  | VPtr (Young a) -> exists (o: nat). resolve (wv x).yng a == Some o
  | _ -> True

let held (#c: comps) (x: config c) (v: value) : prop =
  let w = wv x in
  L.memP v w.roots \/
  (exists (o i: nat). reachable w o /\ ptr_field w.maj o i /\ field w.maj o i == v) \/
  (exists (o i: nat). yreachable w o /\ ptr_field w.yng o i /\ field w.yng o i == v)

/// At every point: (1b) reachable is within snapshot U allocated (all of in
/// use while idle), no dangling pointer, the heaps the instance uses and well
/// formed, the allocator's invariant, (5) the partition.
let concl_point (#c: comps) (x: config c) : prop =
  has_view x /\
  (forall (o: nat). reachable (wv x) o ==> kept x o) /\
  (forall (v: value). held x v /\ VPtr? v ==> resolves_ok x v) /\
  well_formed (mj x) /\ young_ok (wv x).yng /\
  c.a.inv x.ph x.w.cmaj x.ast /\
  partition x

/// (1a) The contents of a kept object after one step: unchanged except by
/// the program's write, up to fwd at a minor collection.
let contents_step (#c: comps) (x: config c) (e: event) (x': config c) (o: nat) : prop =
  let h = mj x in
  let h' = mj x' in
  wz_of h' o == wz_of h o /\ tag_of h' o == tag_of h o /\
  (match e with
   | EWrite (Major t) i v ->
     (forall (j: nat). j < wz_of h o ==> field h' o j == (if o = t && j = i then v else field h o j))
   | EMinor ->
     (match c.n.collect x.ph x.ast x.w with
      | Done _ _ _ fwd -> (forall (j: nat). j < wz_of h o ==> field h' o j == fwd_field h o j (wv x).yng fwd)
      | OutOfRoom -> (forall (j: nat). j < wz_of h o ==> field h' o j == field h o j))
   | _ -> (forall (j: nat). j < wz_of h o ==> field h' o j == field h o j))

/// (2) Allocation as specified, succeeding exactly when room holds.
let alloc_step (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (x': config c) : prop =
  let (_, _, r) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
  (Ok? r <==> c.a.room x.ph x.ast x.w.cmaj sz == true) /\
  (match r with
   | NoRoom -> x' == x
   | Ok o ->
     in_use_c x o == false /\ in_use_c x' o == true /\ kept x' o /\
     (mj x').hd o == Some ({ wz = sz; tag = tag; col = colour_at c.k x.ph o }) /\
     (forall (i: nat). i < sz /\ i < L.length vs ==> field (mj x') o i == L.index vs i) /\
     (forall (y: nat). y <> o ==> (in_use_c x' y == in_use_c x y)))

let concl_step (#c: comps) (x: config c) (e: event) (x': config c) : prop =
  (* (1a) *)
  (forall (o: nat). kept x o ==> in_use_c x' o == true /\ contents_step x e x' o) /\
  (* (2) *)
  (match e with EAlloc sz tag vs -> alloc_step x sz tag vs x' | _ -> True) /\
  (* a read returns the field of the model *)
  (match e with
   | ERead (Major o) i -> x'.w.croots == field (mj x) o i :: x.w.croots
   | ERead (Young o) i -> x'.w.croots == field (wv x).yng o i :: x.w.croots
   | _ -> True) /\
  (* (3d) a minor collection promotes only young objects reachable from roots and remembered slots *)
  (match e with
   | EMinor -> (match c.n.collect x.ph x.ast x.w with
               | Done _ _ _ fwd -> (forall (o: nat). Some? (fwd o) ==> minor_live (wv x) o)
               | OutOfRoom -> True)
   | _ -> True) /\
  (* (5) words move only from in use to free (sweep) and free to in use (allocation) *)
  (forall (w: nat). w < (mj x).size ==>
     (in_use_word_c x w /\ free_word_c x' w ==> ESweep? e) /\
     (free_word_c x w /\ in_use_word_c x' w ==> EAlloc? e \/ EMinor? e)) /\
  (* (6) the measures: a slice decreases the mark's, no other event while marking increases it;
         a sweep step strictly shrinks the unswept set, which nothing else changes *)
  (Marking? x.ph /\ Marking? x'.ph ==>
     (ESlice? e ==> mark_decreases (mj x) (mj x') (live x')) /\
     (~(ESlice? e) ==> mark_no_increase (mj x) (mj x') (live x'))) /\
  (match x.ph, x'.ph with
   | Sweeping p, Sweeping p' ->
     (ESweep? e ==> (forall (o: nat). c.k.unswept p' o ==> c.k.unswept p o) /\
                    (exists (o: nat). o < (mj x).size /\ region c.k p p' o)) /\
     (~(ESweep? e) ==> p' == p)
   | _ -> True)

/// Cycle k: started by event s, ended by event j.
let is_cycle (es: list event) (s j: nat) : prop =
  s < j /\ j < L.length es /\ ev es s == EStart /\ ev es j == EEnd /\
  (forall (t: nat). s < t /\ t < j ==> ~(ev es t == EStart) /\ ~(ev es t == EEnd))

let freed_in (c: comps) (n ny: nat) (es: list event) (s j: nat) (o: nat) : prop =
  in_use_c (at c n ny es s) o == true /\
  (exists (t: nat). s <= t /\ t <= j /\ in_use_c (at c n ny es (t + 1)) o == false)

/// What a stop-the-world collection at s from outside_refs(s) frees.
let stw_freed (#c: comps) (x: config c) (o: nat) : prop =
  in_use_c x o == true /\ ~(reachable (wv x) o)

let concl_cycle (c: comps) (n ny: nat) (es: list event) (s j: nat) : prop =
  let x0 = at c n ny es s in          (* before Start *)
  let xs = at c n ny es (s + 1) in    (* after Start: snapshot_k *)
  let xe = at c n ny es j in          (* before End *)
  let xf = at c n ny es (j + 1) in    (* after End *)
  (* (3a) the words of every object in use at s and not in the snapshot are
     free, or handed out to an object allocated during the cycle *)
  (forall (o: nat). in_use_c x0 o == true /\ ~(xs.snap o) ==>
     (forall (w: nat). covers (mj x0) o w ==>
        free_word_c xf w \/
        (exists (y: nat). xe.allocd y /\ in_use_c xf y == true /\ covers (mj xf) y w))) /\
  (* (3b) the survivors are exactly snapshot_k U allocated_k *)
  (forall (o: nat). in_use_c xf o == true <==> (xe.snap o \/ xe.allocd o)) /\
  (* (4) the freed set is in_use(h_s) minus snapshot_k, the STW set at s *)
  (forall (o: nat). freed_in c n ny es s j o <==> stw_freed x0 o)

/// (3c) An object unreachable at some point of cycle k is freed by the end
/// of cycle k+1, when that cycle is triggered and completes.
let concl_two_cycles (c: comps) (n ny: nat) (es: list event) (s1 j1 s2 j2: nat) : prop =
  forall (t: nat) (o: nat). s1 <= t /\ t <= j1 /\
    in_use_c (at c n ny es t) o == true /\ ~(reachable (wv (at c n ny es t)) o) ==>
    (exists (t': nat). t < t' /\ t' <= j2 + 1 /\ in_use_c (at c n ny es t') o == false)

let conclusions (c: comps) (n ny: nat) (es: list event) : prop =
  (* (0) the initial heap has no objects *)
  (forall (o: nat). in_use_c (at c n ny es 0) o == false) /\
  (forall (i: nat). i <= L.length es ==> concl_point (at c n ny es i)) /\
  (forall (i: nat). i < L.length es ==> concl_step (at c n ny es i) (ev es i) (at c n ny es (i + 1))) /\
  (forall (s j: nat). is_cycle es s j ==> concl_cycle c n ny es s j) /\
  (forall (s1 j1 s2 j2: nat). is_cycle es s1 j1 /\ is_cycle es s2 j2 /\ j1 < s2 /\
     (forall (t: nat). j1 < t /\ t < s2 ==> ~(ev es t == EStart)) ==>
     concl_two_cycles c n ny es s1 j1 s2 j2)

/// ---------------------------------------------------------------------------
/// The top-level theorem, as propositions
/// ---------------------------------------------------------------------------

/// Non-triviality: in every state any run reaches (through every event:
/// allocations, the program's writes and root changes, mark slices, minor
/// collections, sweep steps), room holds whenever the capacity condition
/// does; and the condition is not vacuous.
let room_complete (c: comps) : prop =
  forall (sty: style) (n ny: nat) (es: list event) (i: nat).
    run_ok c sty n ny es /\ i <= L.length es ==>
    (let x = at c n ny es i in
     forall (sz: size_t). c.fits x.ph x.ast x.w.cmaj sz ==> c.a.room x.ph x.ast x.w.cmaj sz == true)

let nontrivial (c: comps) : prop = fits_init c.r c.a c.fits /\ room_complete c

let components_ok (c: comps) : prop =
  faithful c.r /\
  allocator_ok c.r c.a /\ nontrivial c /\ sweep_ok c.r c.s /\ mark_ok c.r c.m /\ minor_ok c.r c.n /\
  barrier_ok c.r c.b

/// gc_correct (A, S, C): under the contracts and the mutator's obligations,
/// every run meets (0)-(6).
let gc_correct (c: comps) (sty: style) : prop =
  components_ok c ==>
  (forall (n ny: nat) (es: list event). run_ok c sty n ny es ==> conclusions c n ny es)

/// The same, with the contracts required only at the steps taken (the
/// representation still faithful).
let gc_correct_local (c: comps) (sty: style) : prop =
  faithful c.r ==>
  (forall (n ny: nat) (es: list event). run_ok c sty n ny es /\ run_hyps c n ny es ==> conclusions c n ny es)

/// The contracts give the hypotheses of every step.
let hyps_of_ok (c: comps) (x: config c) (e: event)
  : Lemma (requires components_ok c) (ensures hyps_at c x e)
  = let r = c.r in
    assert (free_white_at r c.a x.ph x.w.cmaj x.ast);
    assert (forall (h': c.t). free_hd_at r c.a x.ast x.w.cmaj h');
    match e with
    | EAlloc sz tag vs ->
      let (h', _, res) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
      (match res with
       | Ok o -> assert (barrier_init_at r c.b h' x.w.crem o vs)
       | NoRoom -> ());
      assert (alloc_at r c.a x.ph x.w.cmaj x.ast sz tag)
    | EYoungAlloc sz tag vs -> assert (yalloc_ok r x.w.cyng sz tag vs)
    | EWrite (Major o) i v ->
      assert (barrier_write_at r c.b (is_marking x.ph) x.w.cmaj x.w.crem o i v);
      assert (inv_frame_at r c.a x.ph x.w.cmaj x.ast (fst (c.b.bwrite (is_marking x.ph) x.w.cmaj x.w.crem o i v)))
    | EWrite (Young o) i v -> assert (ywrite_ok r x.w.cyng o i v)
    | EMinor -> assert (minor_at r c.n x.ph x.ast x.w); assert (yreset_ok r x.w.cyng)
    | EStart ->
      assert (mark_start_at r c.m x.w);
      assert (inv_start_at c.a x.w.cmaj x.ast);
      assert (inv_frame_at r c.a Marking x.w.cmaj x.ast (c.m.mstart x.w))
    | ESlice ->
      assert (mark_slice_at r c.m x.w.cmaj x.snap x.allocd);
      assert (inv_frame_at r c.a x.ph x.w.cmaj x.ast (c.m.mslice x.w.cmaj))
    | EHandover -> assert (sweep_start_at r c.s x.w.cmaj x.ast)
    | ESweep -> (match x.ph with Sweeping p -> assert (sweep_step_at r c.s p x.w.cmaj x.ast) | _ -> ())
    | EEnd -> (match x.ph with Sweeping p -> assert (sweep_done_at r c.s p x.w.cmaj x.ast) | _ -> ())
    | _ -> ()

let gc_correct_local_implies (c: comps) (sty: style)
  : Lemma (gc_correct_local c sty ==> gc_correct c sty)
  = let aux (n ny: nat) (es: list event)
      : Lemma (requires components_ok c /\ gc_correct_local c sty /\ run_ok c sty n ny es)
              (ensures conclusions c n ny es)
      = let f (i: nat) : Lemma (i < L.length es ==> hyps_at c (at c n ny es i) (ev es i))
          = if i < L.length es then hyps_of_ok c (at c n ny es i) (ev es i) in
        FStar.Classical.forall_intro f;
        assert (init_at c.r c.a n);
        assert (yinit_ok c.r ny)
    in
    let aux' (n ny: nat) (es: list event)
      : Lemma ((components_ok c /\ gc_correct_local c sty /\ run_ok c sty n ny es) ==> conclusions c n ny es)
      = FStar.Classical.move_requires (aux n ny) es in
    FStar.Classical.forall_intro_3 aux'
