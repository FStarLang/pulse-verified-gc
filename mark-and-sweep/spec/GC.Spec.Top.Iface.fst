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
///
/// The components work on the collector's own heap (`t`, and the nursery
/// `yt`).  Each contract is a model contract (a precondition on the model
/// heap, a guarantee relating it to the next one) lifted through the
/// representation relation `r.repr` (GC.Spec.Top.Rep.lifted), as in McCreight
/// et al. (PLDI 2007): for every model heap that represents the input and
/// satisfies the precondition, some model heap represents the output and is
/// related to it by the guarantee.  Where the model step is a function (the
/// Fill, a store) the guarantee is that its result represents the output.

module GC.Spec.Top.Iface

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
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

noeq type allocator (t: Type0) (k: sweep_kind) = {
  state : Type0;
  init  : nat -> GTot (t & state);                              (* empty heap of n words *)
  inv   : phase k.progress -> t -> state -> prop;
  free  : state -> t -> nat -> GTot bool;                       (* allocation status of a block *)
  room  : phase k.progress -> state -> t -> size_t -> GTot bool;
  alloc : phase k.progress -> t -> state -> size_t -> tag_t -> GTot (t & state & result);
}

/// in_use(h): major blocks (of the model heap `m` representing `h`) not free.
let in_use (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap) (o: nat)
  : GTot bool =
  is_block m o && not (a.free st h o)

let free_word (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap) (w: nat)
  : prop =
  exists (o: nat). covers m o w /\ a.free st h o

let in_use_word (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap) (w: nat)
  : prop =
  exists (o: nat). covers m o w /\ in_use a st h m o

/// A block the program may use: in use and, while sweeping, not a white
/// block the sweep has yet to free.
let live_target (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (st: a.state)
    (h: t) (m: mheap) (x: nat) : prop =
  in_use a st h m x == true /\
  (match ph with Sweeping p -> ~(col_of m x == White /\ k.unswept p x == true) | _ -> True)

/// A value the program may store in a scannable field: a word of bytes, a
/// young pointer, or a pointer resolving to a block it may use.  (G28: the
/// allocators' invariants read pointer fields: pages' `no_pointer_to_blue`
/// and `well_formed_heap`.)
let sound_value (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (st: a.state)
    (h: t) (m: mheap) (v: value) : prop =
  match v with
  | VPtr (Major b) -> exists (x: nat). resolve m b == Some x /\ live_target a ph st h m x
  | _ -> True

let alloc_pre (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (h: t) (st: a.state)
    (tag: tag_t) (m: mheap) : prop =
  a.inv ph h st /\ well_formed m /\ tag <> infix_tag

/// What one allocation guarantees.
let alloc_post (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress)
    (h: t) (st: a.state) (sz: size_t) (tag: tag_t) (h': t) (st': a.state) (res: result) (m m': mheap)
  : prop =
  match res with
  | NoRoom -> h' == h /\ st' == st /\ a.room ph st h sz == false
  | Ok o ->
    a.room ph st h sz == true /\
    m'.size == m.size /\
    is_block m' o /\ m'.hd o == Some ({ wz = sz; tag = tag; col = colour_at k ph o }) /\
    (* o's words were free *)
    (forall (w: nat). covers m' o w ==> free_word a st h m w) /\
    (* only o comes into use *)
    (forall (x: nat). in_use a st' h' m' x <==> (in_use a st h m x \/ x == o)) /\
    (* every other in-use object unchanged *)
    (forall (x: nat). in_use a st h m x ==> same_block m m' x) /\
    (* the walk reaches size *)
    well_formed m' /\
    (* the invariant again after Fill, with values the program may store *)
    (forall (vs: list value) (h'': t).
       L.length vs == sz /\ (scannable tag ==> (forall (v: value). L.memP v vs ==> sound_value a ph st h m v)) /\
       r.repr (fill m' o vs) h'' ==> a.inv ph h'' st')

let alloc_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress)
    (h: t) (st: a.state) (sz: size_t) (tag: tag_t) : prop =
  let (h', st', res) = a.alloc ph h st sz tag in
  lifted r (alloc_pre a ph h st tag) h h' (alloc_post r a ph h st sz tag h' st' res)

let alloc_ok (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) : prop =
  forall ph h st sz tag. alloc_at r a ph h st sz tag

let init_post (#t: Type0) (#k: sweep_kind) (a: allocator t k) (n: nat) (h: t) (st: a.state) (m: mheap)
  : prop =
  m.size == n /\ well_formed m /\ a.inv Idle h st /\ (forall (o: nat). in_use a st h m o == false)

/// (0) The initial heap: represented, no object, the walk reaches size, inv Idle.
let init_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (n: nat) : prop =
  r.size_ok n ==>
  (let (h, st) = a.init n in some_repr r h (init_post a n h st))

/// The heaps the program and the collector make without the allocator:
/// writes to fields of blocks the program may use (not closures, which
/// OCaml never writes after their Fill), of values it may store, and
/// recolouring blocks in use while marking.  Blocks, sizes, tags and every
/// other word are unchanged.
let inv_frame_rel (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (st: a.state)
    (h: t) (m m': mheap) : prop =
  m'.size == m.size /\
  (forall (o: nat). is_block m' o == is_block m o) /\
  (forall (o: nat). wz_of m' o == wz_of m o /\ tag_of m' o == tag_of m o) /\
  (forall (o: nat). col_of m' o =!= col_of m o ==> in_use a st h m o /\ Marking? ph /\ dark (col_of m' o)) /\
  (forall (w: nat). m'.body w =!= m.body w ==>
     (exists (o: nat). live_target a ph st h m o /\ o < w /\ w <= o + wz_of m o /\
        tag_of m o <> closure_tag /\
        (scannable (tag_of m o) ==> sound_value a ph st h m' (m'.body w))))

/// The allocator's invariant reads no field of a block in use, nor (while
/// marking) its colour.
let inv_frame_m (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (h: t) (st: a.state)
    (h': t) (m m': mheap) : prop =
  a.inv ph h st /\ inv_frame_rel a ph st h m m' ==>
  a.inv ph h' st /\ (forall (o: nat). a.free st h' o == a.free st h o)

let inv_frame_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress)
    (h: t) (st: a.state) (h': t) : prop =
  forall_repr2 r h h' (inv_frame_m a ph h st h')

/// Starting a cycle: the invariant moves from Idle to Marking.
let inv_start_at (#t: Type0) (#k: sweep_kind) (a: allocator t k) (h: t) (st: a.state) : prop =
  a.inv Idle h st ==> a.inv Marking h st

/// Free blocks are never grey or black (the mark never sees them), and a
/// blue block is free.
let free_white_m (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (h: t) (st: a.state)
    (m: mheap) : prop =
  a.inv ph h st ==>
  (forall (o: nat). is_block m o ==>
     (a.free st h o == true ==> not (dark (col_of m o))) /\ (col_of m o == Blue ==> a.free st h o == true))

let free_white_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress)
    (h: t) (st: a.state) : prop =
  forall_repr r h (free_white_m a ph h st)

/// Allocation status is read from the headers alone: Fill and the program's
/// writes do not change it.
let free_hd_m (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h h': t) (m m': mheap) : prop =
  m'.size == m.size /\ (forall (x: nat). m'.hd x == m.hd x) ==>
  (forall (o: nat). a.free st h' o == a.free st h o)

let free_hd_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h h': t)
  : prop =
  forall_repr2 r h h' (free_hd_m a st h h')

let allocator_ok (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) : prop =
  (forall n. init_at r a n) /\
  (forall st h h'. free_hd_at r a st h h') /\
  alloc_ok r a /\
  (forall ph h st h'. inv_frame_at r a ph h st h') /\
  (forall h st. inv_start_at a h st) /\
  (forall ph h st. free_white_at r a ph h st)

/// The allocator's capacity condition: "enough free space of its kind" for
/// a request of `sz` fields.  It is fixed by the specification, per
/// allocator (first-fit: a free-list block of at least `sz + 1` words;
/// pages: a swept page of the class with a free slot, or an empty page, or a
/// run of empty pages; the toy: the free tail), not chosen by the
/// component; `nontrivial` (GC.Spec.Top.Run) says room holds whenever it
/// does, in every state a run reaches.
let capacity (t: Type0) (k: sweep_kind) (state: Type0) =
  phase k.progress -> state -> t -> size_t -> prop

/// The capacity condition is not vacuous: it holds on some initial heap.
let fits_init (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (fits: capacity t k a.state)
  : prop =
  exists (n: nat) (sz: size_t). r.size_ok n /\ (let (h, st) = a.init n in fits Idle st h sz)

/// ---------------------------------------------------------------------------
/// The sweep S
/// ---------------------------------------------------------------------------

type step_result = { units: nat; freed_words: nat }

noeq type sweep (t: Type0) (k: sweep_kind) (a: allocator t k) = {
  start : t -> a.state -> GTot (k.progress & a.state);
  step  : k.progress -> t -> a.state -> GTot (k.progress & t & a.state & step_result);
  done  : k.progress -> bool;
}

let no_grey (h: mheap) : prop = forall (o: nat). is_block h o ==> col_of h o <> Grey

/// The region a step swept.
let region (k: sweep_kind) (p p': k.progress) (o: nat) : bool =
  k.unswept p o && not (k.unswept p' o)

/// A white block in use in the region: what the step frees.
let swept_white (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap)
    (p p': k.progress) (o: nat) : GTot bool =
  in_use a st h m o && region k p p' o && col_of m o = White

/// No block the mark has darkened points to a white block: the mark's
/// safety at its end (G31; with no grey block, every block of the snapshot
/// or allocated since is black, and they are closed under pointers).  A
/// sweep frees white blocks: without it, it could free the target of a
/// survivor (the page sweep's mid-sweep invariant needs it).
let dark_closed (m: mheap) : prop =
  forall (o i a x: nat). is_block m o /\ dark (col_of m o) /\ ptr_field m o i /\ field m o i == VPtr (Major a) /\
    resolve m a == Some x ==> col_of m x =!= White

let sweep_start_m (#t: Type0) (#k: sweep_kind) (#a: allocator t k) (s: sweep t k a) (h: t) (st: a.state)
    (m: mheap) : prop =
  a.inv Marking h st /\ well_formed m /\ no_grey m /\ dark_closed m ==>
  (let (p, st') = s.start h st in
   a.inv (Sweeping p) h st' /\
   (forall (o: nat). a.free st' h o == a.free st h o) /\       (* frees nothing *)
   (forall (o: nat). in_use a st h m o ==> k.unswept p o == true))

let sweep_start_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (#a: allocator t k) (s: sweep t k a)
    (h: t) (st: a.state) : prop =
  forall_repr r h (sweep_start_m s h st)

/// The words a step frees, per block.
let swept_words (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap)
    (p p': k.progress) (o: nat) : GTot nat =
  if swept_white a st h m p p' o then wz_of m o + 1 else 0

let sweep_step_pre (#t: Type0) (#k: sweep_kind) (#a: allocator t k) (s: sweep t k a) (p: k.progress)
    (h: t) (st: a.state) (m: mheap) : prop =
  a.inv (Sweeping p) h st /\ well_formed m /\ no_grey m /\ s.done p == false

let sweep_step_post (#t: Type0) (#k: sweep_kind) (a: allocator t k) (p: k.progress) (h: t) (st: a.state)
    (p': k.progress) (h': t) (st': a.state) (res: step_result) (m m': mheap) : prop =
  (* unswept only shrinks, and strictly: the measure decreases *)
  (forall (o: nat). k.unswept p' o ==> k.unswept p o) /\
  (exists (o: nat). o < m.size /\ region k p p' o) /\
  m'.size == m.size /\
  (* white becomes free *)
  (forall (o: nat). swept_white a st h m p p' o ==>
     in_use a st' h' m' o == false /\ (forall (w: nat). covers m o w ==> free_word a st' h' m' w)) /\
  (* black becomes white, contents unchanged *)
  (forall (o: nat). in_use a st h m o /\ region k p p' o /\ col_of m o == Black ==>
     in_use a st' h' m' o /\ col_of m' o == White /\ same_contents m m' o) /\
  (* outside the region unchanged *)
  (forall (o: nat). in_use a st h m o /\ not (region k p p' o) ==>
     in_use a st' h' m' o /\ same_block m m' o) /\
  (* nothing comes into use, nothing free leaves it *)
  (forall (o: nat). in_use a st' h' m' o ==> in_use a st h m o) /\
  (forall (w: nat). free_word a st h m w ==> free_word a st' h' m' w) /\
  (* freed_words moves exactly those words from pending to free *)
  (forall (w: nat). free_word a st' h' m' w ==>
     free_word a st h m w \/ (exists (o: nat). covers m o w /\ swept_white a st h m p p' o)) /\
  res.freed_words == sum m.size (swept_words a st h m p p') /\
  a.inv (Sweeping p') h' st' /\ well_formed m'

let sweep_step_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (#a: allocator t k) (s: sweep t k a)
    (p: k.progress) (h: t) (st: a.state) : prop =
  let (p', h', st', res) = s.step p h st in
  lifted r (sweep_step_pre s p h st) h h' (sweep_step_post a p h st p' h' st' res)

let sweep_done_m (#t: Type0) (#k: sweep_kind) (#a: allocator t k) (s: sweep t k a) (p: k.progress) (h: t)
    (st: a.state) (m: mheap) : prop =
  a.inv (Sweeping p) h st /\ well_formed m /\ s.done p == true ==>
  a.inv Idle h st /\
  (forall (o: nat). in_use a st h m o ==> k.unswept p o == false) /\     (* pending empty *)
  (forall (o: nat). is_block m o ==> not (dark (col_of m o)))

let sweep_done_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (#a: allocator t k) (s: sweep t k a)
    (p: k.progress) (h: t) (st: a.state) : prop =
  forall_repr r h (sweep_done_m s p h st)

let sweep_ok (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (#a: allocator t k) (s: sweep t k a) : prop =
  (forall h st. sweep_start_at r s h st) /\
  (forall p h st. sweep_step_at r s p h st) /\
  (forall p h st. sweep_done_at r s p h st)

/// ---------------------------------------------------------------------------
/// The world the collector sees, on its own heaps
/// ---------------------------------------------------------------------------

noeq type cworld (t yt: Type0) = {
  cmaj   : t;
  cyng   : yt;
  croots : list value;
  crem   : list slot;
}

/// `w` is a model world representing `cw`.
let cviews (#t #yt: Type0) (r: rep t yt) (cw: cworld t yt) (w: world) : prop =
  r.repr w.maj cw.cmaj /\ r.yrepr w.yng cw.cyng /\ w.roots == cw.croots /\ w.rem == cw.crem

/// A model statement about the world, for every model world representing it.
let forall_views (#t #yt: Type0) (r: rep t yt) (cw: cworld t yt) (f: world -> prop) : prop =
  forall (w: world). cviews r cw w ==> f w

/// ---------------------------------------------------------------------------
/// The mark: fixed, allocator-free
/// ---------------------------------------------------------------------------

noeq type mark (t yt: Type0) = {
  mstart : cworld t yt -> GTot t;
  mslice : t -> GTot t;
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
  (forall (o: nat). is_block h o /\ dark (col_of h o) ==> snap o \/ allocd o) /\
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

let no_dark (h: mheap) : prop = forall (o: nat). is_block h o ==> not (dark (col_of h o))

let mark_start_pre (w: world) : prop =
  well_formed w.maj /\ no_dark w.maj /\
  (forall (o: nat). reachable w o ==> is_block w.maj o /\ col_of w.maj o == White)

/// mark_start greys every object in outside_refs(s).
let mark_start_post (w: world) (m': mheap) : prop =
  colours_only w.maj m' /\
  (forall (o: nat). outside_ref w o ==> dark (col_of m' o)) /\
  tricolour m' (reachable w) (fun _ -> False)

let mark_start_m (#t #yt: Type0) (r: rep t yt) (mk: mark t yt) (cw: cworld t yt) (w: world) : prop =
  mark_start_pre w ==> (exists (m': mheap). r.repr m' (mk.mstart cw) /\ mark_start_post w m')

let mark_start_at (#t #yt: Type0) (r: rep t yt) (mk: mark t yt) (cw: cworld t yt) : prop =
  forall_views r cw (mark_start_m r mk cw)

let union (s1 s2: nat -> prop) (o: nat) : prop = s1 o \/ s2 o

let mark_slice_pre (snap allocd: nat -> prop) (m: mheap) : prop =
  well_formed m /\ tricolour m snap allocd /\ closed m (union snap allocd) /\ ~(mark_done m)

/// A slice (when something is grey) changes colours only, keeps the
/// invariant and decreases the measure.
let mark_slice_post (snap allocd: nat -> prop) (m m': mheap) : prop =
  colours_only m m' /\ tricolour m' snap allocd /\ mark_decreases m m' (union snap allocd)

let mark_slice_at (#t #yt: Type0) (r: rep t yt) (mk: mark t yt) (h: t) (snap allocd: nat -> prop) : prop =
  lifted r (mark_slice_pre snap allocd) h (mk.mslice h) (mark_slice_post snap allocd)

let mark_ok (#t #yt: Type0) (r: rep t yt) (mk: mark t yt) : prop =
  (forall w. mark_start_at r mk w) /\ (forall h snap allocd. mark_slice_at r mk h snap allocd)

/// ---------------------------------------------------------------------------
/// The minor collection
/// ---------------------------------------------------------------------------

noeq type minor_result (t: Type0) (k: sweep_kind) (a: allocator t k) =
  | Done      : maj:t -> st:a.state -> roots:list value -> fwd:(nat -> option nat) -> minor_result t k a
  | OutOfRoom : minor_result t k a

noeq type minor (t yt: Type0) (k: sweep_kind) (a: allocator t k) = {
  collect : phase k.progress -> a.state -> cworld t yt -> GTot (minor_result t k a);
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
let rem_covers (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (w: world) : prop =
  forall (o i b: nat). in_use a st h w.maj o /\ ptr_field w.maj o i /\ field w.maj o i == VPtr (Young b) ==>
    L.memP (o, i) w.rem

/// A heap that `m` represents, if there is one.
let some_heap (#t #yt: Type0) (r: rep t yt) (m: mheap) : GTot (option t) =
  if FStar.IndefiniteDescription.strong_excluded_middle (exists (h: t). r.repr m h)
  then Some (FStar.IndefiniteDescription.indefinite_description_ghost t (fun h -> r.repr m h))
  else None

/// A model heap that represents `h`, if there is one.
let some_model (#t #yt: Type0) (r: rep t yt) (h: t) : GTot (option mheap) =
  if FStar.IndefiniteDescription.strong_excluded_middle (exists (m: mheap). r.repr m h)
  then Some (FStar.IndefiniteDescription.indefinite_description_ghost mheap (fun m -> r.repr m h))
  else None

/// Promoting `ys` one by one through A.alloc, each copy filled with its
/// young fields (a heap that the Fill represents): `None` if the allocator
/// refuses one.
let rec alloc_fold (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress)
    (h: t) (st: a.state) (y: mheap) (ys: list nat) : GTot (option (t & a.state)) (decreases ys) =
  match ys with
  | [] -> Some (h, st)
  | o :: tl ->
    if wz_of y o >= 1 && tag_of y o <> infix_tag then
      (let (h', st', res) = a.alloc ph h st (wz_of y o) (tag_of y o) in
       match res with
       | NoRoom -> None
       | Ok c ->
         (match some_model r h' with
          | None -> None
          | Some m' ->
            (match some_heap r (fill m' c (fields_of y o)) with
             | None -> None
             | Some h'' -> alloc_fold r a ph h'' st' y tl)))
    else None

/// OutOfRoom is justified: some promotion order of live young objects makes
/// the allocator refuse.
let oor_justified (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress)
    (st: a.state) (cw: cworld t yt) (w: world) : prop =
  exists (ys: list nat). L.noRepeats ys /\
    (forall (o: nat). L.memP o ys ==> is_block w.yng o /\ minor_live w o) /\
    alloc_fold r a ph cw.cmaj st w.yng ys == None

/// The nursery's major pointers are values the program may store (G36: a
/// copy is a Fill of the allocator, whose invariant reads pointer fields).
/// An infix pointer into a major closure is one (G39, design doc §12: the
/// promotion asks only that it resolve to a block in use).
let young_sound (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (st: a.state)
    (h: t) (w: world) : prop =
  forall (y i b: nat). ptr_field w.yng y i /\ field w.yng y i == VPtr (Major b) ==>
    sound_value a ph st h w.maj (VPtr (Major b))

/// A young pointer to `a` is followed safely: if `a` is a field word that
/// reads as an infix header, `a` is an address the model resolves (G38,
/// design doc §12: the collection reads an infix header only below an
/// address it follows; ordinary data that looks like one, e.g. a field
/// holding the word 249, is never read so).
let follow_at (y: mheap) (a: nat) : prop =
  (exists (o: nat). covers y o a /\ o < a) /\ Some? (infix_hdr (y.body a)) ==> Some? (resolve y a)

/// Every young pointer a young block's fields hold is followed safely.
let young_follow_ok (y: mheap) : prop =
  forall (o i a: nat). ptr_field y o i /\ field y o i == VPtr (Young a) ==> follow_at y a

let minor_pre (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (st: a.state)
    (h: t) (w: world) : prop =
  a.inv ph h st /\ well_formed w.maj /\ young_ok w.yng /\ rem_covers a st h w /\ young_sound a ph st h w /\
  young_follow_ok w.yng

let minor_post_done (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (st: a.state)
    (hc: t) (w: world) (hc': t) (st': a.state) (roots': list value) (fwd: nat -> option nat) (h': mheap)
  : prop =
  let h = w.maj in
  let y = w.yng in
  h'.size == h.size /\
  (* exactly the young objects reachable from roots and remembered slots, each once *)
  (forall (o: nat). Some? (fwd o) <==> (is_block y o /\ minor_live w o)) /\
  (forall (o1 o2 c: nat). fwd o1 == Some c /\ fwd o2 == Some c ==> o1 == o2) /\
  (* the copies: on free words, in use, colour by colour_at, fields forwarded *)
  (forall (o c: nat). fwd o == Some c ==>
     (forall (w': nat). covers h' c w' ==> free_word a st hc h w') /\
     h'.hd c == Some ({ wz = wz_of y o; tag = tag_of y o; col = colour_at k ph c }) /\
     (forall (i: nat). i < wz_of y o ==> field h' c i == fwd_field y o i y fwd)) /\
  (forall (x: nat). in_use a st' hc' h' x <==> (in_use a st hc h x \/ (exists (o: nat). fwd o == Some x))) /\
  (* other in-use objects keep their header; those the program may use have
     their young pointers rewritten (G37: the sweep frees the others) *)
  (forall (x: nat). in_use a st hc h x ==>
     h'.hd x == h.hd x /\
     (live_target a ph st hc h x ==> (forall (i: nat). i < wz_of h x ==> field h' x i == fwd_field h x i y fwd))) /\
  roots' == L.map (fwdv y fwd) w.roots /\
  a.inv ph hc' st' /\ well_formed h'

let minor_m (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (#a: allocator t k) (n: minor t yt k a)
    (ph: phase k.progress) (st: a.state) (cw: cworld t yt) (w: world) : prop =
  minor_pre a ph st cw.cmaj w ==>
  (match n.collect ph st cw with
   | OutOfRoom -> oor_justified r a ph st cw w
   | Done hc' st' roots' fwd ->
     exists (h': mheap). r.repr h' hc' /\ minor_post_done a ph st cw.cmaj w hc' st' roots' fwd h')

let minor_at (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (#a: allocator t k) (n: minor t yt k a)
    (ph: phase k.progress) (st: a.state) (cw: cworld t yt) : prop =
  forall_views r cw (minor_m r n ph st cw)

let minor_ok (#t #yt: Type0) (r: rep t yt) (#k: sweep_kind) (#a: allocator t k) (n: minor t yt k a) : prop =
  forall ph st w. minor_at r n ph st w

/// ---------------------------------------------------------------------------
/// The write barrier
/// ---------------------------------------------------------------------------

noeq type barrier (t: Type0) = {
  (* a store `v` into field `i` of major block `o`, `marking` or not *)
  bwrite : bool -> t -> list slot -> nat -> nat -> value -> GTot (t & list slot);
  (* the Fill of a new major block *)
  binit  : t -> list slot -> nat -> list value -> GTot (t & list slot);
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

let write_pre (o i: nat) (v: value) (sv: bool) (h: mheap) : prop =
  is_block h o /\ i < wz_of h o /\ sv == true

let write_post (marking: bool) (rem rem': list slot) (o i: nat) (v: value) (h h': mheap) : prop =
  h'.size == h.size /\
  (forall (x: nat). is_block h' x == is_block h x /\ wz_of h' x == wz_of h x /\ tag_of h' x == tag_of h x) /\
  (forall (w: nat). field_word h w ==> h'.body w == (if w = o + 1 + i then v else h.body w)) /\
  (* while marking the overwritten value is darkened; otherwise no colour changes *)
  darkened h h' (if marking then old_target h o i else None) /\
  (* every old-to-young pointer written is remembered *)
  (forall (sl: slot). L.memP sl rem ==> L.memP sl rem') /\
  (young_slot h o i v ==> L.memP (o, i) rem')

let barrier_write_at (#t #yt: Type0) (r: rep t yt) (b: barrier t) (marking: bool) (hc: t) (rem: list slot)
    (o i: nat) (v: value) : prop =
  let (hc', rem') = b.bwrite marking hc rem o i v in
  lifted r (write_pre o i v (r.storable v)) hc hc' (write_post marking rem rem' o i v)

/// The Fill is a function of the model: its result represents the new heap.
let binit_m (#t #yt: Type0) (r: rep t yt) (b: barrier t) (hc: t) (rem: list slot) (o: nat) (vs: list value)
    (h: mheap) : prop =
  is_block h o /\ L.length vs == wz_of h o /\ storable_all r vs ==>
  (let (hc', rem') = b.binit hc rem o vs in
   r.repr (fill h o vs) hc' /\
   (forall (sl: slot). L.memP sl rem ==> L.memP sl rem') /\
   (forall (i: nat). i < L.length vs /\ young_slot h o i (L.index vs i) ==> L.memP (o, i) rem'))

let barrier_init_at (#t #yt: Type0) (r: rep t yt) (b: barrier t) (hc: t) (rem: list slot) (o: nat)
    (vs: list value) : prop =
  forall_repr r hc (binit_m r b hc rem o vs)

let barrier_ok (#t #yt: Type0) (r: rep t yt) (b: barrier t) : prop =
  (forall marking h rem o i v. barrier_write_at r b marking h rem o i v) /\
  (forall h rem o vs. barrier_init_at r b h rem o vs)
