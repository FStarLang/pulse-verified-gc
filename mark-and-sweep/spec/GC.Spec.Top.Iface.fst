/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Iface - the components of the top-level GC specification
/// ---------------------------------------------------------------------------
///
/// The plug-and-play components and their contracts:
///   - an allocator `A` (`allocator`, `allocator_ok`, per-allocator
///     `nontrivial`);
///   - its sweep `S` (`sweep`, `sweep_ok`);
///   - the mark (`mark`, `mark_ok`), fixed and allocator-free;
///   - the minor collection (`minor`, `minor_ok`), over any allocator;
///   - the write barrier (`barrier`, `barrier_ok`).
///
/// Every contract is a universally quantified implication `pre ==> post`.
/// Each also has a pointwise form `*_at` (the same implication at one input),
/// which is what a run uses (`GC.Spec.Top.Run`); `*_ok ==> *_at` is
/// instantiation.

module GC.Spec.Top.Iface

open GC.Spec.Top.Heap
module L = FStar.List.Tot
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Shared types
/// ---------------------------------------------------------------------------

type phase (pr: Type0) =
  | Idle     : phase pr
  | Marking  : phase pr
  | Sweeping : pr -> phase pr

type result =
  | Ok     : nat -> result
  | NoRoom : result

/// A request's wosize.
let size_t = sz:nat{sz >= 1}

/// What the allocator needs to know of the sweep: its progress, and which
/// addresses it has yet to visit.
noeq type sweep_kind = {
  progress : Type0;
  unswept  : progress -> nat -> bool;
}

let is_marking (#pr: Type0) (ph: phase pr) : bool = Marking? ph
let is_idle (#pr: Type0) (ph: phase pr) : bool = Idle? ph

/// The colour rule.
let colour_at (k: sweep_kind) (ph: phase k.progress) (o: nat) : colour =
  match ph with
  | Marking -> Black
  | Sweeping p -> if k.unswept p o then Black else White
  | Idle -> White

/// ---------------------------------------------------------------------------
/// The allocator A
/// ---------------------------------------------------------------------------

noeq type allocator (k: sweep_kind) = {
  state : Type0;
  init  : nat -> GTot (mheap & state);                          (* empty heap of n words *)
  inv   : phase k.progress -> mheap -> state -> prop;
  free  : state -> mheap -> nat -> GTot bool;                   (* allocation status of a block *)
  room  : phase k.progress -> state -> mheap -> size_t -> GTot bool;
  alloc : phase k.progress -> mheap -> state -> size_t -> tag_t -> GTot (mheap & state & result);
}

/// in_use(h): major blocks not free.
let in_use (#k: sweep_kind) (a: allocator k) (st: a.state) (h: mheap) (o: nat) : GTot bool =
  is_block h o && not (a.free st h o)

let free_word (#k: sweep_kind) (a: allocator k) (st: a.state) (h: mheap) (w: nat) : prop =
  exists (o: nat). covers h o w /\ a.free st h o

let in_use_word (#k: sweep_kind) (a: allocator k) (st: a.state) (h: mheap) (w: nat) : prop =
  exists (o: nat). covers h o w /\ in_use a st h o

/// What one allocation guarantees.
let alloc_post (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (h: mheap) (st: a.state)
    (sz: size_t) (tag: tag_t) (h': mheap) (st': a.state) (r: result) : prop =
  match r with
  | NoRoom -> h' == h /\ st' == st /\ a.room ph st h sz == false
  | Ok o ->
    a.room ph st h sz == true /\
    h'.size == h.size /\
    is_block h' o /\ h'.hd o == Some ({ wz = sz; tag = tag; col = colour_at k ph o }) /\
    (* o's words were free *)
    (forall (w: nat). covers h' o w ==> free_word a st h w) /\
    (* only o comes into use *)
    (forall (x: nat). in_use a st' h' x <==> (in_use a st h x \/ x == o)) /\
    (* every other in-use object unchanged *)
    (forall (x: nat). in_use a st h x ==> same_block h h' x) /\
    (* the walk reaches size *)
    well_formed h' /\
    (* the invariant again after Fill *)
    (forall (vs: list value). L.length vs == sz ==> a.inv ph (fill h' o vs) st')

let alloc_at (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (h: mheap) (st: a.state)
    (sz: size_t) (tag: tag_t) : prop =
  a.inv ph h st /\ well_formed h /\ tag <> infix_tag ==>
  (let (h', st', r) = a.alloc ph h st sz tag in alloc_post a ph h st sz tag h' st' r)

let alloc_ok (#k: sweep_kind) (a: allocator k) : prop =
  forall ph h st sz tag. alloc_at a ph h st sz tag

/// (0) The initial heap: no object, the walk reaches size, inv Idle.
let init_at (#k: sweep_kind) (a: allocator k) (n: nat) : prop =
  (let (h, st) = a.init n in
   h.size == n /\ well_formed h /\ a.inv Idle h st /\ (forall (o: nat). in_use a st h o == false))

/// The heaps the program and the collector make without the allocator:
/// writes to fields of blocks in use, and recolouring blocks in use while
/// marking.  Blocks, sizes, tags and every other word are unchanged.
let inv_frame_rel (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (st: a.state)
    (h h': mheap) : prop =
  h'.size == h.size /\
  (forall (o: nat). is_block h' o == is_block h o) /\
  (forall (o: nat). wz_of h' o == wz_of h o /\ tag_of h' o == tag_of h o) /\
  (forall (o: nat). col_of h' o =!= col_of h o ==> in_use a st h o /\ Marking? ph) /\
  (forall (w: nat). h'.body w =!= h.body w ==>
     (exists (o: nat). in_use a st h o /\ o < w /\ w <= o + wz_of h o))

/// The allocator's invariant reads no field of a block in use, nor (while
/// marking) its colour.
let inv_frame_at (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (h: mheap) (st: a.state)
    (h': mheap) : prop =
  a.inv ph h st /\ inv_frame_rel a ph st h h' ==>
  a.inv ph h' st /\ (forall (o: nat). a.free st h' o == a.free st h o)

/// Starting a cycle: the invariant moves from Idle to Marking.
let inv_start_at (#k: sweep_kind) (a: allocator k) (h: mheap) (st: a.state) : prop =
  a.inv Idle h st ==> a.inv Marking h st

/// Free blocks are white (the model's "blue"): the mark never sees them.
let free_white_at (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (h: mheap) (st: a.state) : prop =
  a.inv ph h st ==> (forall (o: nat). is_block h o /\ a.free st h o ==> col_of h o == White)

/// Allocation status is read from the headers alone: Fill and the program's
/// writes do not change it.
let free_hd_at (#k: sweep_kind) (a: allocator k) (st: a.state) (h h': mheap) : prop =
  h'.size == h.size /\ (forall (x: nat). h'.hd x == h.hd x) ==>
  (forall (o: nat). a.free st h' o == a.free st h o)

let allocator_ok (#k: sweep_kind) (a: allocator k) : prop =
  (forall n. init_at a n) /\
  (forall st h h'. free_hd_at a st h h') /\
  alloc_ok a /\
  (forall ph h st h'. inv_frame_at a ph h st h') /\
  (forall h st. inv_start_at a h st) /\
  (forall ph h st. free_white_at a ph h st)

/// Non-triviality, generic part: on some initial heap some request has room.
/// Each allocator adds its own capacity lemma (room holds given enough free
/// space of its kind).
let nontrivial (#k: sweep_kind) (a: allocator k) : prop =
  exists (n: nat) (sz: size_t). (let (h, st) = a.init n in a.room Idle st h sz == true)

/// ---------------------------------------------------------------------------
/// The sweep S
/// ---------------------------------------------------------------------------

type step_result = { units: nat; freed_words: nat }

noeq type sweep (k: sweep_kind) (a: allocator k) = {
  start : mheap -> a.state -> GTot (k.progress & a.state);
  step  : k.progress -> mheap -> a.state -> GTot (k.progress & mheap & a.state & step_result);
  done  : k.progress -> bool;
}

let no_grey (h: mheap) : prop = forall (o: nat). is_block h o ==> col_of h o <> Grey

/// The region a step swept.
let region (k: sweep_kind) (p p': k.progress) (o: nat) : bool =
  k.unswept p o && not (k.unswept p' o)

/// A white block in use in the region: what the step frees.
let swept_white (#k: sweep_kind) (a: allocator k) (st: a.state) (h: mheap) (p p': k.progress) (o: nat)
  : GTot bool =
  in_use a st h o && region k p p' o && col_of h o = White

let sweep_start_at (#k: sweep_kind) (#a: allocator k) (s: sweep k a) (h: mheap) (st: a.state) : prop =
  a.inv Marking h st /\ well_formed h /\ no_grey h ==>
  (let (p, st') = s.start h st in
   a.inv (Sweeping p) h st' /\
   (forall (o: nat). a.free st' h o == a.free st h o) /\       (* frees nothing *)
   (forall (o: nat). in_use a st h o ==> k.unswept p o == true))

/// The words a step frees, per block.
let swept_words (#k: sweep_kind) (a: allocator k) (st: a.state) (h: mheap) (p p': k.progress) (o: nat)
  : GTot nat =
  if swept_white a st h p p' o then wz_of h o + 1 else 0

let sweep_step_post (#k: sweep_kind) (#a: allocator k) (s: sweep k a) (p: k.progress) (h: mheap)
    (st: a.state) : prop =
  (let (p', h', st', r) = s.step p h st in
   (* unswept only shrinks, and strictly: the measure decreases *)
   (forall (o: nat). k.unswept p' o ==> k.unswept p o) /\
   (exists (o: nat). o < h.size /\ region k p p' o) /\
   h'.size == h.size /\
   (* white becomes free *)
   (forall (o: nat). swept_white a st h p p' o ==>
      in_use a st' h' o == false /\ (forall (w: nat). covers h o w ==> free_word a st' h' w)) /\
   (* black becomes white, contents unchanged *)
   (forall (o: nat). in_use a st h o /\ region k p p' o /\ col_of h o == Black ==>
      in_use a st' h' o /\ col_of h' o == White /\ same_contents h h' o) /\
   (* outside the region unchanged *)
   (forall (o: nat). in_use a st h o /\ not (region k p p' o) ==>
      in_use a st' h' o /\ same_block h h' o) /\
   (* nothing comes into use, nothing free leaves it *)
   (forall (o: nat). in_use a st' h' o ==> in_use a st h o) /\
   (forall (w: nat). free_word a st h w ==> free_word a st' h' w) /\
   (* freed_words moves exactly those words from pending to free *)
   (forall (w: nat). free_word a st' h' w ==>
      free_word a st h w \/ (exists (o: nat). covers h o w /\ swept_white a st h p p' o)) /\
   r.freed_words == sum h.size (swept_words a st h p p') /\
   a.inv (Sweeping p') h' st' /\ well_formed h')

let sweep_step_at (#k: sweep_kind) (#a: allocator k) (s: sweep k a) (p: k.progress) (h: mheap)
    (st: a.state) : prop =
  a.inv (Sweeping p) h st /\ well_formed h /\ no_grey h /\ s.done p == false ==>
  sweep_step_post s p h st

let sweep_done_at (#k: sweep_kind) (#a: allocator k) (s: sweep k a) (p: k.progress) (h: mheap)
    (st: a.state) : prop =
  a.inv (Sweeping p) h st /\ well_formed h /\ s.done p == true ==>
  a.inv Idle h st /\
  (forall (o: nat). in_use a st h o ==> k.unswept p o == false) /\     (* pending empty *)
  (forall (o: nat). is_block h o ==> col_of h o == White)

let sweep_ok (#k: sweep_kind) (#a: allocator k) (s: sweep k a) : prop =
  (forall h st. sweep_start_at s h st) /\
  (forall p h st. sweep_step_at s p h st) /\
  (forall p h st. sweep_done_at s p h st)

/// ---------------------------------------------------------------------------
/// The mark: fixed, allocator-free
/// ---------------------------------------------------------------------------

noeq type mark = {
  mstart : world -> GTot mheap;
  mslice : mheap -> GTot mheap;
}

let mark_done (h: mheap) : prop = no_grey h

/// A path from a grey object through white objects.
noeq type wpath (h: mheap) : nat -> Type0 =
  | WGrey : g:nat -> squash (is_block h g /\ col_of h g == Grey) -> wpath h g
  | WStep : o:nat -> o':nat -> wpath h o ->
            squash (major_edge h o o' /\ is_block h o' /\ col_of h o' == White) -> wpath h o'

/// `o` is grey, or reached from a grey object through white ones.
let grey_reached (h: mheap) (o: nat) : prop = exists (_: wpath h o). True

/// The marking invariant, relative to the snapshot and the objects
/// allocated since the cycle started (snapshot-at-the-beginning).
let tricolour (h: mheap) (snap allocd: nat -> prop) : prop =
  (forall (o: nat). snap o \/ allocd o ==> is_block h o) /\
  (forall (o: nat). is_block h o /\ col_of h o <> White ==> snap o \/ allocd o) /\
  (forall (o: nat). allocd o ==> col_of h o == Black) /\
  (forall (o: nat). snap o /\ col_of h o == White ==> grey_reached h o)

/// The live set is closed under pointer fields.
let closed (h: mheap) (live: nat -> prop) : prop =
  forall (o i a: nat). live o /\ ptr_field h o i /\ field h o i == VPtr (Major a) ==>
    (exists (o': nat). resolve h a == Some o' /\ live o')

let white_live (h: mheap) (live: nat -> prop) (o: nat) : prop =
  o < h.size /\ live o /\ is_block h o /\ col_of h o == White
let grey_live (h: mheap) (live: nat -> prop) (o: nat) : prop =
  o < h.size /\ live o /\ is_block h o /\ col_of h o == Grey

/// The mark's measure: the white, then the grey, live objects (finite sets
/// below `size`), lexicographically.  It strictly decreases ...
let mark_decreases (h h': mheap) (live: nat -> prop) : prop =
  (forall (o: nat). white_live h' live o ==> white_live h live o) /\
  ((exists (o: nat). white_live h live o /\ ~(white_live h' live o)) \/
   ((forall (o: nat). white_live h' live o <==> white_live h live o) /\
    (forall (o: nat). grey_live h' live o ==> grey_live h live o) /\
    (exists (o: nat). grey_live h live o /\ ~(grey_live h' live o))))

/// ... and does not increase.
let mark_no_increase (h h': mheap) (live: nat -> prop) : prop =
  (forall (o: nat). white_live h' live o ==> white_live h live o) /\
  ((exists (o: nat). white_live h live o /\ ~(white_live h' live o)) \/
   (forall (o: nat). grey_live h' live o ==> grey_live h live o))

let all_white (h: mheap) : prop = forall (o: nat). is_block h o ==> col_of h o == White

/// mark_start greys every object in outside_refs(s).
let mark_start_at (m: mark) (w: world) : prop =
  well_formed w.maj /\ all_white w.maj /\ (forall (o: nat). reachable w o ==> is_block w.maj o) ==>
  (let h' = m.mstart w in
   colours_only w.maj h' /\
   (forall (o: nat). outside_ref w o ==> col_of h' o <> White) /\
   tricolour h' (reachable w) (fun _ -> False))

let union (s1 s2: nat -> prop) (o: nat) : prop = s1 o \/ s2 o

/// A slice (when something is grey) changes colours only, keeps the
/// invariant and decreases the measure.
let mark_slice_at (m: mark) (h: mheap) (snap allocd: nat -> prop) : prop =
  well_formed h /\ tricolour h snap allocd /\ closed h (union snap allocd) /\ ~(mark_done h) ==>
  (let h' = m.mslice h in
   colours_only h h' /\ tricolour h' snap allocd /\ mark_decreases h h' (union snap allocd))

let mark_ok (m: mark) : prop =
  (forall w. mark_start_at m w) /\ (forall h snap allocd. mark_slice_at m h snap allocd)

/// ---------------------------------------------------------------------------
/// The minor collection
/// ---------------------------------------------------------------------------

noeq type minor_result (k: sweep_kind) (a: allocator k) =
  | Done      : maj:mheap -> st:a.state -> roots:list value -> fwd:(nat -> option nat) -> minor_result k a
  | OutOfRoom : minor_result k a

noeq type minor (k: sweep_kind) (a: allocator k) = {
  collect : phase k.progress -> a.state -> world -> GTot (minor_result k a);
}

/// The forwarding of a value: a pointer into a promoted young object is
/// rewritten to its copy, at the same offset (infix pointers included).
let fwdv (y: mheap) (fwd: nat -> option nat) (v: value) : value =
  match v with
  | VPtr (Young a) ->
    (match resolve y a with
     | Some o -> (match fwd o with Some c -> VPtr (Major (c + (a - o))) | None -> v)
     | None -> v)
  | _ -> v

/// The fields of a block after forwarding (a no-scan block keeps its bytes).
let fwd_field (src: mheap) (o i: nat) (y: mheap) (fwd: nat -> option nat) : value =
  if scannable (tag_of src o) then fwdv y fwd (field src o i) else field src o i

/// Every old-to-young pointer in a block in use is a remembered slot.
let rem_covers (#k: sweep_kind) (a: allocator k) (st: a.state) (w: world) : prop =
  forall (o i b: nat). in_use a st w.maj o /\ ptr_field w.maj o i /\ field w.maj o i == VPtr (Young b) ==>
    L.memP (o, i) w.rem

/// Promoting `ys` one by one through A.alloc, each copy filled with its
/// young fields: `None` if the allocator refuses one.
let rec alloc_fold (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (h: mheap) (st: a.state)
    (y: mheap) (ys: list nat) : GTot (option (mheap & a.state)) (decreases ys) =
  match ys with
  | [] -> Some (h, st)
  | o :: tl ->
    if wz_of y o >= 1 && tag_of y o <> infix_tag then
      (let (h', st', r) = a.alloc ph h st (wz_of y o) (tag_of y o) in
       match r with
       | NoRoom -> None
       | Ok c -> alloc_fold a ph (fill h' c (fields_of y o)) st' y tl)
    else None

/// OutOfRoom is justified: some promotion order of live young objects makes
/// the allocator refuse.
let oor_justified (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (st: a.state) (w: world) : prop =
  exists (ys: list nat). L.noRepeats ys /\
    (forall (o: nat). L.memP o ys ==> is_block w.yng o /\ minor_live w o) /\
    alloc_fold a ph w.maj st w.yng ys == None

let minor_pre (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (st: a.state) (w: world) : prop =
  a.inv ph w.maj st /\ well_formed w.maj /\ young_ok w.yng /\ rem_covers a st w

let minor_post (#k: sweep_kind) (a: allocator k) (ph: phase k.progress) (st: a.state) (w: world)
    (r: minor_result k a) : prop =
  match r with
  | OutOfRoom -> oor_justified a ph st w
  | Done h' st' roots' fwd ->
    let h = w.maj in
    let y = w.yng in
    h'.size == h.size /\
    (* exactly the young objects reachable from roots and remembered slots, each once *)
    (forall (o: nat). Some? (fwd o) <==> (is_block y o /\ minor_live w o)) /\
    (forall (o1 o2 c: nat). fwd o1 == Some c /\ fwd o2 == Some c ==> o1 == o2) /\
    (* the copies: on free words, in use, colour by colour_at, fields forwarded *)
    (forall (o c: nat). fwd o == Some c ==>
       (forall (w': nat). covers h' c w' ==> free_word a st h w') /\
       h'.hd c == Some ({ wz = wz_of y o; tag = tag_of y o; col = colour_at k ph c }) /\
       (forall (i: nat). i < wz_of y o ==> field h' c i == fwd_field y o i y fwd)) /\
    (forall (x: nat). in_use a st' h' x <==> (in_use a st h x \/ (exists (o: nat). fwd o == Some x))) /\
    (* other in-use objects unchanged except young pointers rewritten *)
    (forall (x: nat). in_use a st h x ==>
       h'.hd x == h.hd x /\ (forall (i: nat). i < wz_of h x ==> field h' x i == fwd_field h x i y fwd)) /\
    roots' == L.map (fwdv y fwd) w.roots /\
    a.inv ph h' st' /\ well_formed h'

let minor_at (#k: sweep_kind) (#a: allocator k) (n: minor k a) (ph: phase k.progress) (st: a.state)
    (w: world) : prop =
  minor_pre a ph st w ==> minor_post a ph st w (n.collect ph st w)

let minor_ok (#k: sweep_kind) (#a: allocator k) (n: minor k a) : prop =
  forall ph st w. minor_at n ph st w

/// ---------------------------------------------------------------------------
/// The write barrier
/// ---------------------------------------------------------------------------

noeq type barrier = {
  (* a store `v` into field `i` of major block `o`, `marking` or not *)
  bwrite : bool -> mheap -> list slot -> nat -> nat -> value -> GTot (mheap & list slot);
  (* the Fill of a new major block *)
  binit  : mheap -> list slot -> nat -> list value -> GTot (mheap & list slot);
}

/// Darken: a white block becomes grey; nothing else changes colour.
let darkened (h h': mheap) (t: option nat) : prop =
  forall (x: nat). col_of h' x == (if Some x = t && col_of h x = White then Grey else col_of h x)

/// The old value's target, if the field is a pointer field holding one.
let old_target (h: mheap) (o i: nat) : option nat =
  if ptr_field h o i then
    (match field h o i with VPtr (Major a) -> resolve h a | _ -> None)
  else None

let young_slot (h: mheap) (o i: nat) (v: value) : bool =
  is_block h o && scannable (tag_of h o) && VPtr? v && Young? (VPtr?._0 v)

let barrier_write_at (b: barrier) (marking: bool) (h: mheap) (rem: list slot) (o i: nat) (v: value) : prop =
  is_block h o /\ i < wz_of h o ==>
  (let (h', rem') = b.bwrite marking h rem o i v in
   h'.size == h.size /\
   (forall (x: nat). is_block h' x == is_block h x /\ wz_of h' x == wz_of h x /\ tag_of h' x == tag_of h x) /\
   (forall (w: nat). h'.body w == (if w = o + 1 + i then v else h.body w)) /\
   (* while marking the overwritten value is darkened; otherwise no colour changes *)
   darkened h h' (if marking then old_target h o i else None) /\
   (* every old-to-young pointer written is remembered *)
   (forall (sl: slot). L.memP sl rem ==> L.memP sl rem') /\
   (young_slot h o i v ==> L.memP (o, i) rem'))

let barrier_init_at (b: barrier) (h: mheap) (rem: list slot) (o: nat) (vs: list value) : prop =
  is_block h o /\ L.length vs == wz_of h o ==>
  (let (h', rem') = b.binit h rem o vs in
   h' == fill h o vs /\
   (forall (sl: slot). L.memP sl rem ==> L.memP sl rem') /\
   (forall (i: nat). i < L.length vs /\ young_slot h o i (L.index vs i) ==> L.memP (o, i) rem'))

let barrier_ok (b: barrier) : prop =
  (forall marking h rem o i v. barrier_write_at b marking h rem o i v) /\
  (forall h rem o vs. barrier_init_at b h rem o vs)
