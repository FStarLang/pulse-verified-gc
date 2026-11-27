/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWInv - the allocator's invariant along a witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §15.  `minor_pre` asks for the allocator's invariant.  Along a
/// first-fit witness run it follows from the components' contracts
/// (`FFComps.ff_components_ok`, through `Run.hyps_of_ok`), one event at a
/// time, on the closed-form model the description gives (`FFWStep.holds`):
///   - the initial heap meets it idle (`init_at`);
///   - an allocation, after its Fill with values the program may store
///     (`alloc_at`);
///   - a write, a mark start, a mark slice: the change is one the allocator's
///     invariant does not read (`inv_frame_at`, given `inv_frame_rel` on the
///     closed forms);
///   - the sweep's start, steps and end (`sweep_start_at`, `sweep_step_at`,
///     `sweep_done_at`);
///   - a minor collection, given `minor_pre` (`minor_at`);
///   - reads, root changes and young allocations leave it alone.

module GC.Spec.Top.FFWInv

open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteRep
open GC.Spec.Top.Run
open GC.Spec.Top.RunFacts
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFWModel
open GC.Spec.Top.FFWState
open GC.Spec.Top.FFWStep
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module FC = GC.Spec.Top.FFComps
module FWA = GC.Spec.Top.FFWAlloc
module FSt = GC.Spec.Top.FFWStart

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The allocator's invariant at a configuration.
let ivx (x: config fc) : prop = fc.a.T.inv x.ph x.w.cmaj x.ast

let hyps (x: config fc) (e: event) : Lemma (hyps_at fc x e)
  = FC.ff_components_ok ();
    hyps_of_ok fc x e

/// Free is blue, read off the model.
let free_model (x: config fc) (d: dsc) (o: nat)
  : Lemma (requires holds x d)
          (ensures fc.a.T.free x.ast x.w.cmaj o ==
                   (match (mk d.dst).M.hd o with Some h -> h.M.col = M.Blue | None -> false))
  = holds_def x d

/// A block in use: a block, not blue.
let in_use_model (x: config fc) (d: dsc) (o: nat)
  : Lemma (requires holds x d)
          (ensures T.in_use fc.a x.ast x.w.cmaj (mk d.dst) o ==
                   (M.is_block (mk d.dst) o && M.col_of (mk d.dst) o <> M.Blue))
  = free_model x d o

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let inv_init (es: list event)
  : Lemma (requires ff_room) (ensures ivx (at fc msize ywords es 0))
  = FC.ff_components_ok ();
    at_zero fc msize ywords es;
    init_facts ();
    assert (T.init_at fc.r fc.a msize)

/// Reads, root changes and young allocations leave the major heap alone.
let inv_same (x: config fc) (e: event)
  : Lemma (requires ivx x /\ (ERead? e \/ ERoots? e \/ EYoungAlloc? e))
          (ensures ivx (step fc x e))
  = match e with
    | ERead (M.Major _) _ -> ()
    | ERead (M.Young _) _ -> ()
    | ERoots _ -> ()
    | EYoungAlloc sz tag vs -> (match fc.r.R.yalloc x.w.cyng sz tag vs with Some _ -> () | None -> ())

/// ---------------------------------------------------------------------------
/// An allocation and its Fill
/// ---------------------------------------------------------------------------

let brepr_same (m1 m2: M.mheap) (g: GC.Spec.Base.heap)
  : Lemma (requires fc.r.R.repr m1 g /\ brepr m2 g) (ensures R.heq m1 m2)
  = R.heq_sym m2 (cabs g); R.heq_trans m1 (cabs g) m2

/// The post's last clause, instantiated.
let post_fill (x: config fc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (h': GC.Spec.Base.heap) (st1: ffst)
    (o: nat) (m m': M.mheap) (h'': GC.Spec.Base.heap)
  : Lemma (requires T.alloc_post fc.r fc.a x.ph x.w.cmaj x.ast sz tag h' st1 (T.Ok o) m m' /\
                    L.length vs == sz /\
                    (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==>
                                           T.sound_value fc.a x.ph x.ast x.w.cmaj m v)) /\
                    fc.r.R.repr (M.fill m' o vs) h'')
          (ensures fc.a.T.inv x.ph h'' st1)
  = ()

#push-options "--z3rlimit 40"
let inv_alloc (x: config fc) (d d': dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (st': wst)
  : Lemma (requires holds x d /\ ivx x /\ holds (step fc x (EAlloc sz tag vs)) d' /\ d'.dst == st' /\
                    sz + 2 <= d.dst.f /\ tag <> M.infix_tag /\ L.length vs == sz /\
                    R.storable_all byte_rep vs /\ no_young vs == true /\ d.dst.f < msize /\
                    R.heq (M.fill (FWA.split (mk d.dst) d.dst.f sz tag (T.colour_at ffk d.dph (d.dst.f - sz)))
                                  (d.dst.f - sz) vs) (mk st') /\
                    (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==>
                                           T.sound_value fc.a d.dph x.ast x.w.cmaj (mk d.dst) v)))
          (ensures ivx (step fc x (EAlloc sz tag vs)))
  = let m = mk d.dst in
    holds_def x d;
    okm_def m;
    FSt.brep_wf m;
    hyps x (EAlloc sz tag vs);
    let s : ffst = x.ast in
    assert (m.M.hd 0 == Some (FWA.free_hdr d.dst.f));
    alloc_fill x.ph x.w.cmaj s m d.dst.f sz tag vs (mk st');
    let (h', st1, res) = ffalloc x.ph x.w.cmaj s sz tag in
    let (h'', rem') = GC.Spec.Top.ByteBarrier.binit h' [] (d.dst.f - sz) vs in
    FWA.ffalloc_head x.ph x.w.cmaj s m d.dst.f sz tag;
    let m1 = FWA.split m d.dst.f sz tag (T.colour_at ffk d.dph (d.dst.f - sz)) in
    assert (T.alloc_pre fc.a x.ph x.w.cmaj x.ast tag m);
    let m' = FStar.IndefiniteDescription.indefinite_description_ghost M.mheap
               (fun m' -> fc.r.R.repr m' h' /\ T.alloc_post fc.r fc.a x.ph x.w.cmaj x.ast sz tag h' st1 res m m') in
    brepr_same m' m1 h';
    fill_heq m' m1 (d.dst.f - sz) vs;
    assert (fc.r.R.repr (M.fill m' (d.dst.f - sz) vs) h'');
    post_fill x sz tag vs h' st1 (d.dst.f - sz) m m' h'';
    assert (x.w.crem == []);
    assert ((step fc x (EAlloc sz tag vs)).w.cmaj == h'');
    assert ((step fc x (EAlloc sz tag vs)).ast == st1)
#pop-options

/// ---------------------------------------------------------------------------
/// Changes the invariant does not read
/// ---------------------------------------------------------------------------

/// The frame contract, used on given models (generic, so the allocator's
/// invariant stays abstract).
let frame_use_g (#t #yt: Type0) (r: R.rep t yt) (#k: T.sweep_kind) (a: T.allocator t k)
    (ph: T.phase k.T.progress) (h: t) (st: a.T.state) (h': t) (m m': M.mheap)
  : Lemma (requires T.inv_frame_at r a ph h st h' /\ r.R.repr m h /\ r.R.repr m' h' /\
                    a.T.inv ph h st /\ T.inv_frame_rel a ph st h m m')
          (ensures a.T.inv ph h' st)
  = assert (T.inv_frame_m a ph h st h' m m')

let frame_use (ph: T.phase U64.t) (h: GC.Spec.Base.heap) (st: ffst) (h': GC.Spec.Base.heap) (m m': M.mheap)
  : Lemma (requires T.inv_frame_at fc.r fc.a ph h st h' /\ fc.r.R.repr m h /\ fc.r.R.repr m' h' /\
                    fc.a.T.inv ph h st /\ T.inv_frame_rel fc.a ph st h m m')
          (ensures fc.a.T.inv ph h' st)
  = frame_use_g fc.r fc.a ph h st h' m m'

let inv_write (x: config fc) (d d': dsc) (o i: nat) (v: M.value)
  : Lemma (requires holds x d /\ ivx x /\ holds (step fc x (EWrite (M.Major o) i v)) d' /\
                    T.inv_frame_rel fc.a d.dph x.ast x.w.cmaj (mk d.dst) (mk d'.dst))
          (ensures ivx (step fc x (EWrite (M.Major o) i v)))
  = holds_def x d;
    holds_def (step fc x (EWrite (M.Major o) i v)) d';
    hyps x (EWrite (M.Major o) i v);
    let h' = fst (fc.b.T.bwrite (T.is_marking x.ph) x.w.cmaj x.w.crem o i v) in
    assert ((step fc x (EWrite (M.Major o) i v)).w.cmaj == h');
    frame_use x.ph x.w.cmaj x.ast h' (mk d.dst) (mk d'.dst)

let inv_start (x: config fc) (d d': dsc)
  : Lemma (requires holds x d /\ ivx x /\ d.dph == T.Idle /\ holds (step fc x EStart) d' /\
                    T.inv_frame_rel fc.a T.Marking x.ast x.w.cmaj (mk d.dst) (mk d'.dst))
          (ensures ivx (step fc x EStart))
  = holds_def x d;
    holds_def (step fc x EStart) d';
    hyps x EStart;
    let h' = fc.m.T.mstart x.w in
    assert ((step fc x EStart).w.cmaj == h');
    frame_use T.Marking x.w.cmaj x.ast h' (mk d.dst) (mk d'.dst)

let inv_slice (x: config fc) (d d': dsc) (mvs: list T.move)
  : Lemma (requires holds x d /\ ivx x /\ holds (step fc x (ESlice mvs)) d' /\
                    T.inv_frame_rel fc.a d.dph x.ast x.w.cmaj (mk d.dst) (mk d'.dst))
          (ensures ivx (step fc x (ESlice mvs)))
  = holds_def x d;
    holds_def (step fc x (ESlice mvs)) d';
    hyps x (ESlice mvs);
    let h' = fst (T.mmoves fc.m x.w.cmaj x.ms mvs) in
    assert ((step fc x (ESlice mvs)).w.cmaj == h');
    frame_use x.ph x.w.cmaj x.ast h' (mk d.dst) (mk d'.dst)

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

let inv_handover (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ ivx x /\ d.dph == T.Marking /\ T.no_grey (mk d.dst) /\ T.dark_closed (mk d.dst))
          (ensures ivx (step fc x EHandover))
  = holds_def x d;
    okm_def (mk d.dst);
    FSt.brep_wf (mk d.dst);
    hyps x EHandover

/// The sweep step's contract, used on a given model (generic).
let sweep_use_g (#t #yt: Type0) (r: R.rep t yt) (#k: T.sweep_kind) (#a: T.allocator t k) (s: T.sweep t k a)
    (p: k.T.progress) (h: t) (st: a.T.state) (m: M.mheap)
  : Lemma (requires T.sweep_step_at r s p h st /\ r.R.repr m h /\ T.sweep_step_pre s p h st m)
          (ensures (let (p', h', st', _) = s.T.step p h st in a.T.inv (T.Sweeping p') h' st'))
  = ()

#push-options "--z3rlimit 40"
let inv_sweep (x: config fc) (d: dsc) (p: U64.t)
  : Lemma (requires holds x d /\ ivx x /\ d.dph == T.Sweeping p /\ T.no_grey (mk d.dst) /\
                    GC.Spec.Top.FFSweep.ffdone p == false)
          (ensures ivx (step fc x ESweep))
  = holds_def x d;
    okm_def (mk d.dst);
    FSt.brep_wf (mk d.dst);
    hyps x ESweep;
    assert (T.sweep_step_pre fc.s p x.w.cmaj x.ast (mk d.dst));
    sweep_use_g fc.r fc.s p x.w.cmaj x.ast (mk d.dst);
    let (p', h', st', _) = fc.s.T.step p x.w.cmaj x.ast in
    assert (fc.a.T.inv (T.Sweeping p') h' st');
    let y = step fc x ESweep in
    assert (y.ph == T.Sweeping p' /\ y.w.cmaj == h' /\ y.ast == st')
#pop-options

/// The sweep's end, used on a given model (generic).
let done_use_g (#t #yt: Type0) (r: R.rep t yt) (#k: T.sweep_kind) (#a: T.allocator t k) (s: T.sweep t k a)
    (p: k.T.progress) (h: t) (st: a.T.state) (m: M.mheap)
  : Lemma (requires T.sweep_done_at r s p h st /\ r.R.repr m h /\ a.T.inv (T.Sweeping p) h st /\
                    M.well_formed m /\ s.T.done p == true)
          (ensures a.T.inv T.Idle h st)
  = assert (T.sweep_done_m s p h st m)

let inv_end (x: config fc) (d: dsc) (p: U64.t)
  : Lemma (requires holds x d /\ ivx x /\ d.dph == T.Sweeping p /\ GC.Spec.Top.FFSweep.ffdone p == true)
          (ensures ivx (step fc x EEnd))
  = holds_def x d;
    okm_def (mk d.dst);
    FSt.brep_wf (mk d.dst);
    hyps x EEnd;
    done_use_g fc.r fc.s p x.w.cmaj x.ast (mk d.dst);
    let y = step fc x EEnd in
    assert (y.ph == T.Idle /\ y.w.cmaj == x.w.cmaj /\ y.ast == x.ast)

/// ---------------------------------------------------------------------------
/// A minor collection
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let inv_minor (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ ivx x /\ T.minor_pre fc.a x.ph x.ast x.w.cmaj (wd d) /\
                    T.Done? (fc.n.T.collect x.ph x.ast x.w))
          (ensures ivx (step fc x EMinor))
  = views_d x d;
    hyps x EMinor;
    assert (T.minor_m fc.r fc.n x.ph x.ast x.w (wd d))
#pop-options

/// ---------------------------------------------------------------------------
/// `inv_frame_rel` on closed forms
/// ---------------------------------------------------------------------------

/// The same blocks, sizes and tags; colours changed only to dark on blocks
/// in use while marking; at most one word `k` of the bodies changed, a field
/// of a block the program may use (not a closure) holding a value it may
/// store.
/// Generic over the allocator: `in_use` is read through one equation.
let body_one (#t: Type0) (#sk: T.sweep_kind) (a: T.allocator t sk) (ph: T.phase sk.T.progress) (st: a.T.state)
    (h: t) (m m': M.mheap) (k o: nat)
  : Lemma (requires (forall (w: nat). w <> k ==> m'.M.body w == m.M.body w) /\
                    (m'.M.body k =!= m.M.body k ==>
                       T.live_target a ph st h m o /\ o < k /\ k <= o + M.wz_of m o /\
                       M.tag_of m o <> M.closure_tag /\
                       (M.scannable (M.tag_of m o) ==> T.sound_value a ph st h m' (m'.M.body k))))
          (ensures forall (w: nat). m'.M.body w =!= m.M.body w ==>
                     (exists (y: nat). T.live_target a ph st h m y /\ y < w /\ w <= y + M.wz_of m y /\
                        M.tag_of m y <> M.closure_tag /\
                        (M.scannable (M.tag_of m y) ==> T.sound_value a ph st h m' (m'.M.body w))))
  = let f (w: nat)
      : Lemma (m'.M.body w =!= m.M.body w ==>
                 (exists (y: nat). T.live_target a ph st h m y /\ y < w /\ w <= y + M.wz_of m y /\
                    M.tag_of m y <> M.closure_tag /\
                    (M.scannable (M.tag_of m y) ==> T.sound_value a ph st h m' (m'.M.body w))))
      = if w = k then () else () in
    FStar.Classical.forall_intro f

let rel_g (#t: Type0) (#sk: T.sweep_kind) (a: T.allocator t sk) (ph: T.phase sk.T.progress) (st: a.T.state)
    (h: t) (m m': M.mheap) (k o: nat)
  : Lemma (requires (forall (y: nat). T.in_use a st h m y == (M.is_block m y && M.col_of m y <> M.Blue)) /\
                    m'.M.size == m.M.size /\
                    (forall (y: nat). M.is_block m' y == M.is_block m y /\
                                      M.wz_of m' y == M.wz_of m y /\ M.tag_of m' y == M.tag_of m y) /\
                    (forall (y: nat). M.col_of m' y =!= M.col_of m y ==>
                       M.is_block m y /\ M.col_of m y <> M.Blue /\ T.Marking? ph /\ M.dark (M.col_of m' y)) /\
                    (forall (w: nat). w <> k ==> m'.M.body w == m.M.body w) /\
                    (m'.M.body k =!= m.M.body k ==>
                       T.live_target a ph st h m o /\ o < k /\ k <= o + M.wz_of m o /\
                       M.tag_of m o <> M.closure_tag /\
                       (M.scannable (M.tag_of m o) ==> T.sound_value a ph st h m' (m'.M.body k))))
          (ensures T.inv_frame_rel a ph st h m m')
  = body_one a ph st h m m' k o

/// The same blocks, sizes and tags; colours changed only to dark on blocks
/// in use while marking; at most one word `k` of the bodies changed, a field
/// of a block the program may use (not a closure) holding a value it may
/// store.
let rel_of (x: config fc) (d: dsc) (ph: T.phase U64.t) (m': M.mheap) (k o: nat)
  : Lemma (requires holds x d /\
                    m'.M.size == (mk d.dst).M.size /\
                    (forall (y: nat). M.is_block m' y == M.is_block (mk d.dst) y /\
                                      M.wz_of m' y == M.wz_of (mk d.dst) y /\ M.tag_of m' y == M.tag_of (mk d.dst) y) /\
                    (forall (y: nat). M.col_of m' y =!= M.col_of (mk d.dst) y ==>
                       M.is_block (mk d.dst) y /\ M.col_of (mk d.dst) y <> M.Blue /\ T.Marking? ph /\ M.dark (M.col_of m' y)) /\
                    (forall (w: nat). w <> k ==> m'.M.body w == (mk d.dst).M.body w) /\
                    (m'.M.body k =!= (mk d.dst).M.body k ==>
                       T.live_target fc.a ph x.ast x.w.cmaj (mk d.dst) o /\ o < k /\ k <= o + M.wz_of (mk d.dst) o /\
                       M.tag_of (mk d.dst) o <> M.closure_tag /\
                       (M.scannable (M.tag_of (mk d.dst) o) ==> T.sound_value fc.a ph x.ast x.w.cmaj m' (m'.M.body k))))
          (ensures T.inv_frame_rel fc.a ph x.ast x.w.cmaj (mk d.dst) m')
  = FStar.Classical.forall_intro (in_use_model x d);
    rel_g fc.a ph x.ast x.w.cmaj (mk d.dst) m' k o

/// ---------------------------------------------------------------------------
/// `minor_pre`
/// ---------------------------------------------------------------------------

module FM2 = GC.Spec.Top.FFWMinor2

let no_young_body (m: M.mheap) (o i b: nat)
  : Lemma (requires FM2.body_hv m) (ensures M.field m o i =!= M.VPtr (M.Young b))
  = assert (FM2.hv (m.M.body (o + 1 + i)))

/// `minor_pre` reads the world only up to `wheq` (generic over the
/// allocator, whose invariant and free set stay abstract).
let sound_heq (#t: Type0) (#sk: T.sweep_kind) (a: T.allocator t sk) (ph: T.phase sk.T.progress)
    (st: a.T.state) (h: t) (m m': M.mheap) (b: nat)
  : Lemma (requires R.heq m m' /\ T.sound_value a ph st h m (M.VPtr (M.Major b)))
          (ensures T.sound_value a ph st h m' (M.VPtr (M.Major b)))
  = resolve_heq m m' b;
    let x = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun x -> M.resolve m b == Some x /\ T.live_target a ph st h m x) in
    assert (M.is_block m' x == M.is_block m x);
    assert (M.col_of m' x == M.col_of m x);
    assert (T.live_target a ph st h m' x)

let rem_heq (#t: Type0) (#sk: T.sweep_kind) (a: T.allocator t sk) (ph: T.phase sk.T.progress) (st: a.T.state)
    (h: t) (w w': M.world)
  : Lemma (requires wheq w w' /\ T.rem_covers a ph st h w) (ensures T.rem_covers a ph st h w')
  = let one (o i b: nat)
      : Lemma (T.live_target a ph st h w'.M.maj o /\ M.ptr_field w'.M.maj o i /\
               M.field w'.M.maj o i == M.VPtr (M.Young b) ==> L.memP (o, i) w'.M.rem)
      = assert (M.is_block w'.M.maj o == M.is_block w.M.maj o);
        assert (M.hdr_of w'.M.maj o == M.hdr_of w.M.maj o);
        assert (M.field w'.M.maj o i == M.field w.M.maj o i);
        assert (T.in_use a st h w'.M.maj o == T.in_use a st h w.M.maj o);
        assert (M.col_of w'.M.maj o == M.col_of w.M.maj o);
        assert (M.ptr_field w'.M.maj o i == M.ptr_field w.M.maj o i) in
    FStar.Classical.forall_intro_3 one

let ysound_heq (#t: Type0) (#sk: T.sweep_kind) (a: T.allocator t sk) (ph: T.phase sk.T.progress)
    (st: a.T.state) (h: t) (w w': M.world)
  : Lemma (requires wheq w w' /\ T.young_sound a ph st h w) (ensures T.young_sound a ph st h w')
  = let one (y i b: nat)
      : Lemma (M.ptr_field w'.M.yng y i /\ M.field w'.M.yng y i == M.VPtr (M.Major b) ==>
               T.sound_value a ph st h w'.M.maj (M.VPtr (M.Major b)))
      = if M.ptr_field w'.M.yng y i && M.field w'.M.yng y i = M.VPtr (M.Major b) then begin
          assert (M.hdr_of w'.M.yng y == M.hdr_of w.M.yng y);
          assert (M.field w'.M.yng y i == M.field w.M.yng y i);
          assert (M.ptr_field w.M.yng y i);
          sound_heq a ph st h w.M.maj w'.M.maj b
        end in
    FStar.Classical.forall_intro_3 one

let minor_pre_heq (#t: Type0) (#sk: T.sweep_kind) (a: T.allocator t sk) (ph: T.phase sk.T.progress)
    (st: a.T.state) (h: t) (w w': M.world)
  : Lemma (requires wheq w w' /\ T.minor_pre a ph st h w) (ensures T.minor_pre a ph st h w')
  = GC.Spec.Top.PagesInst.wf_heq w.M.maj w'.M.maj;
    GC.Spec.Top.PagesMinor.young_ok_heq w.M.yng w'.M.yng;
    GC.Spec.Top.PagesMinor.yfollow_heq w.M.yng w'.M.yng;
    rem_heq a ph st h w w';
    ysound_heq a ph st h w w'

/// **The minor collection's precondition**, on the description's world:
/// the allocator's invariant, well formed, a well-formed nursery, no
/// old-to-young pointer (the remembered set is empty), the nursery's major
/// pointers values the program may store.
#push-options "--z3rlimit 40"
let mpre_d (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ ivx x /\ FM2.body_hv (mk d.dst) /\
                    M.young_ok d.dym /\ T.young_follow_ok d.dym /\
                    (forall (y i b: nat). M.ptr_field d.dym y i /\ M.field d.dym y i == M.VPtr (M.Major b) ==>
                       T.sound_value fc.a x.ph x.ast x.w.cmaj (mk d.dst) (M.VPtr (M.Major b))))
          (ensures T.minor_pre fc.a x.ph x.ast x.w.cmaj (wd d))
  = holds_def x d;
    okm_def (mk d.dst);
    FSt.brep_wf (mk d.dst);
    FStar.Classical.forall_intro_3 (fun o i b -> FStar.Classical.move_requires (no_young_body (mk d.dst) o i) b);
    assert (T.rem_covers fc.a x.ph x.ast x.w.cmaj (wd d));
    assert (T.young_sound fc.a x.ph x.ast x.w.cmaj (wd d))
#pop-options

/// The same, on any world reading as the description's.
let mpre (x: config fc) (d: dsc) (w: M.world)
  : Lemma (requires holds x d /\ ivx x /\ FM2.body_hv (mk d.dst) /\ wheq w (wd d) /\
                    M.young_ok d.dym /\ T.young_follow_ok d.dym /\
                    (forall (y i b: nat). M.ptr_field d.dym y i /\ M.field d.dym y i == M.VPtr (M.Major b) ==>
                       T.sound_value fc.a x.ph x.ast x.w.cmaj (mk d.dst) (M.VPtr (M.Major b))))
          (ensures T.minor_pre fc.a x.ph x.ast x.w.cmaj w)
  = mpre_d x d;
    R.heq_sym w.M.maj (wd d).M.maj;
    R.heq_sym w.M.yng (wd d).M.yng;
    minor_pre_heq fc.a x.ph x.ast x.w.cmaj (wd d) w
