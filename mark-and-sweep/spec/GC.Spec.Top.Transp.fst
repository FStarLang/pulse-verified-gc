/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Transp - T1, as propositions: the collector is invisible to
/// the program
/// ---------------------------------------------------------------------------
///
/// Design doc §16.7, §16.15.  A reference semantics runs the program's
/// events on an unbounded store with no collector: objects are named by
/// allocation order and never move, never die and never fail to allocate.
///   - `transparent es prog ι`: the run `es` runs the reference program
///     `prog`.  At every point `i`, `ι i` renames the reference objects to
///     blocks (major or young), and the run's configuration corresponds to
///     the reference store after the program events so far (`scorr`).
///     Every program event of `es` is the image of the next event of
///     `prog` (`ev_corr`), which is a legal reference event (`rok`).  Every
///     value the program reads corresponds to the reference read.
///   - `t1_local` / `t1` (part 1): every run with no failed allocation is
///     transparent for some reference program.
///   - `t1` (part 2, what T2 does not cover): for a cycle `s..j`, the run
///     that collects stop-the-world at `s` and then replays the same
///     program events (with minor collections and whole stop-the-world
///     cycles where it needs room) runs the same reference program, so
///     matches `es` up to renaming at every program point.  It replays all
///     of it, or stops just before an allocation that no collection can
///     make room for (`stuck`).

module GC.Spec.Top.Transp

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Stw
module L = FStar.List.Tot

/// ---------------------------------------------------------------------------
/// The reference semantics
/// ---------------------------------------------------------------------------

/// A reference value: a word held as is (an integer; any word of a no-scan
/// object), or a pointer to object `obj` at offset `off` (0, or the offset
/// of an infix header in a closure).
type rval =
  | RWord : value -> rval
  | RPtr  : obj:nat -> off:nat -> rval

noeq type robj = { rtag: tag_t; rsz: nat; rf: nat -> rval }

noeq type rstore = {
  objs   : nat -> option robj;
  next   : nat;                 (* the next allocation's name *)
  rroots : list rval;
}

/// A program event on reference names.  `young` records which allocation
/// the program asked for; the reference semantics ignores it.
noeq type revent =
  | RAlloc : young:bool -> tag:tag_t -> vs:list rval -> revent
  | RWrite : obj:nat -> i:nat -> v:rval -> revent
  | RRead  : obj:nat -> i:nat -> revent
  | RRoots : rs:list rval -> revent

let rinit : rstore = { objs = (fun _ -> None); next = 0; rroots = [] }

let rlist (vs: list rval) (i: nat) : rval = if i < L.length vs then L.index vs i else RWord (VInt 0)

let rstep (r: rstore) (e: revent) : rstore =
  match e with
  | RAlloc _ tag vs ->
    { objs = (fun k -> if k = r.next then Some ({ rtag = tag; rsz = L.length vs; rf = rlist vs }) else r.objs k);
      next = r.next + 1;
      rroots = RPtr r.next 0 :: r.rroots }
  | RWrite k i v ->
    (match r.objs k with
     | Some o -> { r with objs = (fun k' -> if k' = k then Some ({ o with rf = (fun j -> if j = i then v else o.rf j) })
                                             else r.objs k') }
     | None -> r)
  | RRead k i ->
    (match r.objs k with
     | Some o -> { r with rroots = o.rf i :: r.rroots }
     | None -> r)
  | RRoots rs -> { r with rroots = rs }

let rec rexec (r: rstore) (ps: list revent) : Tot rstore (decreases ps) =
  match ps with
  | [] -> r
  | e :: tl -> rexec (rstep r e) tl

/// The reference store after the first `m` events of `prog`.
let rat (prog: list revent) (m: nat) : rstore = rexec rinit (take m prog)

/// Event `m` of `prog` (a dummy past its end).
let rev_at (prog: list revent) (m: nat) : revent =
  if m < L.length prog then L.index prog m else RRoots []

/// The objects the reference program can reach: from its roots, through
/// the pointer fields of scannable objects.
let rptr_field (r: rstore) (k i: nat) : prop =
  exists (o: robj). r.objs k == Some o /\ scannable o.rtag /\ i < o.rsz

noeq type rreach (r: rstore) : nat -> Type0 =
  | RRoot : k:nat -> d:nat -> squash (L.memP (RPtr k d) r.rroots /\ Some? (r.objs k)) -> rreach r k
  | RNext : k:nat -> k':nat -> i:nat -> d:nat -> rreach r k ->
            squash (rptr_field r k i /\ (Some?.v (r.objs k)).rf i == RPtr k' d /\ Some? (r.objs k')) -> rreach r k'

let rreachable (r: rstore) (k: nat) : prop = exists (_: rreach r k). True

/// A legal reference value (in a scannable field, or a root): a word that
/// is an integer, or a pointer to an allocated object.  (Not only a
/// reachable one: the collector keeps what the run can still name, which
/// is more than the reference program can reach (`visible`), and the
/// reference store never frees.)
let rval_ok (r: rstore) (scan: bool) (v: rval) : prop =
  match v with
  | RWord u -> scan ==> VInt? u
  | RPtr k _ -> scan /\ Some? (r.objs k)

let robj_of (r: rstore) (k: nat) : GTot robj =
  match r.objs k with Some o -> o | None -> { rtag = 0; rsz = 0; rf = (fun _ -> RWord (VInt 0)) }

/// A legal reference event: what `mutator_ok` asks, on reference names.
let rok (r: rstore) (e: revent) : prop =
  match e with
  | RAlloc _ tag vs ->
    tag <> infix_tag /\ L.length vs >= 1 /\
    (forall (i: nat). i < L.length vs ==> rval_ok r (scannable tag) (L.index vs i))
  | RWrite k i v ->
    Some? (r.objs k) /\ i < (robj_of r k).rsz /\ (robj_of r k).rtag <> closure_tag /\
    rval_ok r (scannable (robj_of r k).rtag) v
  | RRead k i ->
    Some? (r.objs k) /\ scannable (robj_of r k).rtag /\ i < (robj_of r k).rsz
  | RRoots rs -> forall (v: rval). L.memP v rs ==> rval_ok r true v

/// ---------------------------------------------------------------------------
/// Renaming: the run against the reference
/// ---------------------------------------------------------------------------

/// A renaming: reference object -> the block holding it now (a major or a
/// young block's address).
let renaming = nat -> option ptr

/// `v`, a word of world `w`, is the reference value `rv`.  A pointer is the
/// renamed object's address plus the offset, and resolves to it.  `scan`:
/// the word is a root or a field of a scannable object; a no-scan object's
/// words are held as they are.
let vcorr (ι: renaming) (w: world) (scan: bool) (v: value) (rv: rval) : prop =
  match rv with
  | RWord u -> v == u /\ (scan ==> VInt? u)
  | RPtr k d ->
    scan /\
    (match v with
     | VPtr (Major a) -> exists (o: nat). ι k == Some (Major o) /\ a == o + d /\ resolve w.maj a == Some o
     | VPtr (Young a) -> exists (o: nat). ι k == Some (Young o) /\ a == o + d /\ resolve w.yng a == Some o
     | _ -> False)

/// The block that holds reference object `ro`.
let ocorr (ι: renaming) (w: world) (p: ptr) (ro: robj) : prop =
  let (h, o) = (match p with Major o -> (w.maj, o) | Young o -> (w.yng, o)) in
  is_block h o /\ tag_of h o == ro.rtag /\ wz_of h o == ro.rsz /\
  (forall (i: nat). i < ro.rsz ==> vcorr ι w (scannable ro.rtag) (field h o i) (ro.rf i))

/// The blocks the run can still name (what `mutator_ok` lets the program
/// use): reachable major objects and reachable young ones.  This set is
/// closed under fields and holds the roots' targets.
let visible (w: world) (p: ptr) : prop =
  match p with
  | Major o -> reachable w o
  | Young o -> yreachable w o

/// A configuration is a reference store, up to `ι`: the roots one by one;
/// every visible block holds one reference object, and no other object is
/// renamed to it; every reachable reference object is in a visible block.
let scorr (#c: comps) (ι: renaming) (x: config c) (r: rstore) : prop =
  let w = wv x in
  L.length w.roots == L.length r.rroots /\
  (forall (i: nat). i < L.length w.roots ==> vcorr ι w true (L.index w.roots i) (L.index r.rroots i)) /\
  (forall (p: ptr). visible w p ==>
     (exists (k: nat). ι k == Some p /\ Some? (r.objs k) /\ ocorr ι w p (Some?.v (r.objs k)))) /\
  (forall (k k': nat) (p: ptr). ι k == Some p /\ ι k' == Some p /\ visible w p ==> k == k') /\
  (forall (k: nat). rreachable r k ==> (exists (p: ptr). ι k == Some p /\ visible w p))

let vcorr_list (ι: renaming) (w: world) (scan: bool) (vs: list value) (rvs: list rval) : prop =
  L.length vs == L.length rvs /\
  (forall (i: nat). i < L.length vs ==> vcorr ι w scan (L.index vs i) (L.index rvs i))

/// A program event of the run is the reference event, renamed.
let ev_corr (ι: renaming) (w: world) (r: rstore) (e: event) (re: revent) : prop =
  match e, re with
  | EAlloc sz tag vs, RAlloc false tag' rvs ->
    tag == tag' /\ sz == L.length rvs /\ vcorr_list ι w (scannable tag) vs rvs
  | EYoungAlloc sz tag vs, RAlloc true tag' rvs ->
    tag == tag' /\ sz == L.length rvs /\ vcorr_list ι w (scannable tag) vs rvs
  | EWrite p i v, RWrite k i' rv ->
    i == i' /\ ι k == Some p /\ vcorr ι w (scannable (robj_of r k).rtag) v rv
  | ERead p i, RRead k i' -> i == i' /\ ι k == Some p
  | ERoots vs, RRoots rvs -> vcorr_list ι w true vs rvs
  | _ -> False

/// The number of program events among the first `i`.
let rec mcount (es: list event) : nat =
  match es with
  | [] -> 0
  | e :: tl -> (if is_mutator_event e then 1 else 0) + mcount tl

let mc (es: list event) (i: nat) : nat = mcount (take i es)

let head_or (#t: Type) (d: t) (l: list t) : t = match l with [] -> d | h :: _ -> h

/// **`es` runs the reference program `prog`, through the renamings `ι`.**
let transparent (c: comps) (n ny: nat) (es: list event) (prog: list revent) (ι: nat -> renaming) : prop =
  L.length prog == mc es (L.length es) /\
  (* every point corresponds to the reference store after the program events so far *)
  (forall (i: nat). i <= L.length es ==> scorr (ι i) (at c n ny es i) (rat prog (mc es i))) /\
  (* every program event is the next reference event, renamed, and a legal one *)
  (forall (i: nat). i < L.length es /\ is_mutator_event (ev es i) ==>
     rok (rat prog (mc es i)) (rev_at prog (mc es i)) /\
     ev_corr (ι i) (wv (at c n ny es i)) (rat prog (mc es i)) (ev es i) (rev_at prog (mc es i))) /\
  (* every value the program reads is the reference read, renamed *)
  (forall (i: nat). i < L.length es /\ ERead? (ev es i) ==>
     vcorr (ι (i + 1)) (wv (at c n ny es (i + 1))) true
       (head_or (VInt 0) (wv (at c n ny es (i + 1))).roots)
       (head_or (RWord (VInt 0)) (rat prog (mc es (i + 1))).rroots))

/// ---------------------------------------------------------------------------
/// Allocation failures
/// ---------------------------------------------------------------------------

/// No major allocation of the run fails.  (A young allocation never fails
/// in a run: `enabled` asks for room, so a full nursery is a minor
/// collection first.  A minor collection that runs out of room stops the
/// run: nothing is enabled after it.)
let alloc_succeeds (#c: comps) (x: config c) (e: event) : prop =
  match e with
  | EAlloc sz tag _ -> (let (_, _, r) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in Ok? r)
  | _ -> True

let no_fail (c: comps) (n ny: nat) (es: list event) : prop =
  forall (i: nat). i < L.length es ==> alloc_succeeds (at c n ny es i) (ev es i)

/// `es` ends with `suf`.
let ends_with (es suf: list event) : prop = exists (pre: list event). es == L.append pre suf

/// The replay cannot perform the next program event `re`, an allocation,
/// even after the strongest collection:
///   - (S1) a major allocation the allocator refuses right after a minor
///     collection (the nursery is then empty) and a whole stop-the-world
///     cycle (which then frees every object not reachable from the roots);
///   - (S2) a young allocation with no room right after a minor
///     collection (the nursery is then empty);
///   - (S3) a minor collection that runs out of room right after a whole
///     stop-the-world cycle.
let stuck (#c: comps) (x: config c) (ι: renaming) (re: revent) (es2: list event) : prop =
  match re with
  | RAlloc false tag rvs ->
    if L.length rvs >= 1
    then (x.stopped == false /\ (exists (a: slices) (b: nat). ends_with es2 (EMinor :: stw_tail a b)) /\
          (let (_, _, r) = c.a.alloc x.ph x.w.cmaj x.ast (L.length rvs) tag in NoRoom? r)) \/
         (x.stopped == true /\ (exists (a: slices) (b: nat). ends_with es2 (L.append (stw_tail a b) [EMinor])))
    else False
  | RAlloc true tag rvs ->
    if L.length rvs >= 1
    then (x.stopped == false /\ ends_with es2 [EMinor] /\
          (forall (vs: list value). vcorr_list ι (wv x) (scannable tag) vs rvs ==>
             None? (c.r.yalloc x.w.cyng (L.length rvs) tag vs))) \/
         (x.stopped == true /\ (exists (a: slices) (b: nat). ends_with es2 (L.append (stw_tail a b) [EMinor])))
    else False
  | _ -> False

/// The replay's own events: program events, minor collections, and whole
/// stop-the-world cycles.
noeq type chunk =
  | CProg  : e:event -> chunk
  | CMinor : chunk
  | CCycle : a:slices -> b:nat -> chunk

let rec flat (cs: list chunk) : list event =
  match cs with
  | [] -> []
  | CProg e :: tl -> e :: flat tl
  | CMinor :: tl -> EMinor :: flat tl
  | CCycle a b :: tl -> L.append (stw_tail a b) (flat tl)

let replay_events (q: list event) : prop =
  exists (cs: list chunk). q == flat cs /\ (forall (ch: chunk). L.memP ch cs /\ CProg? ch ==> is_mutator_event (CProg?.e ch))

/// ---------------------------------------------------------------------------
/// T1
/// ---------------------------------------------------------------------------

/// Part 1, with the contracts at the steps taken.
let t1_local (c: comps) (sty: style) : prop =
  faithful c.r ==>
  (forall (n ny: nat) (es: list event).
     run_ok c sty n ny es /\ run_hyps c n ny es /\ no_fail c n ny es ==>
     (exists (prog: list revent) (ι: nat -> renaming). transparent c n ny es prog ι))

/// Part 2: the stop-the-world replay of the cycle `s..j` of `es`.
let stw_replay (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (prog: list revent) : prop =
  exists (a: slices) (b: nat) (q: list event) (m: nat) (ι2: nat -> renaming).
    let es2 = L.append (L.append (take s es) (stw_tail a b)) q in
    replay_events q /\
    run_ok c sty n ny es2 /\ no_fail c n ny es2 /\
    mc es s <= m /\ m <= L.length prog /\
    (* the replay runs the first m events of the same reference program *)
    transparent c n ny es2 (take m prog) ι2 /\
    (* all of them, or it stops before an allocation it cannot perform *)
    (m == L.length prog \/
     stuck (at c n ny es2 (L.length es2)) (ι2 (L.length es2)) (rev_at prog m) es2)

/// A reference value names a reachable object, if any.
let rval_reach (r: rstore) (v: rval) : prop =
  match v with
  | RPtr k _ -> rreachable r k
  | RWord _ -> True

/// The event names only objects the program reaches from its roots.
let names_reach (r: rstore) (e: revent) : prop =
  match e with
  | RAlloc _ _ vs -> forall (i: nat). i < L.length vs ==> rval_reach r (L.index vs i)
  | RWrite k _ v -> rreachable r k /\ rval_reach r v
  | RRead k _ -> rreachable r k
  | RRoots rs -> forall (v: rval). L.memP v rs ==> rval_reach r v

/// The program names only what it reaches (G53, §16.17): what OCaml's type
/// safety gives a real program.  `gc_correct` keeps the broader `value_ok`.
let names_reachable (prog: list revent) : prop =
  forall (m: nat). m < L.length prog ==> names_reach (rat prog m) (rev_at prog m)

/// **T1.**  Part 2 for programs that name only what they reach.
let t1 (c: comps) (sty: style) : prop =
  components_ok c ==>
  (forall (n ny: nat) (es: list event).
     run_ok c sty n ny es /\ no_fail c n ny es ==>
     (exists (prog: list revent) (ι: nat -> renaming).
        transparent c n ny es prog ι /\
        (names_reachable prog ==>
           (forall (s j: nat). is_cycle es s j ==> stw_replay c sty n ny es s prog))))
