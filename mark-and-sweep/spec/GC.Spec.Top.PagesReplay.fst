/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesReplay - the promotion, as allocations of the page
/// allocator component
/// ---------------------------------------------------------------------------
///
/// The minor collection of pages runs GC.Spec.Pages.Promote with the page
/// allocator's instance for the phase (`ptal`: `Promote.Idle.idle_tal`,
/// `PromoteInst.mark_tal`, `PromoteInst.sw_tal`), on the page heap
/// `gl h s` and the page state.  Each promotion is an allocation of the page
/// allocator component (`PagesAlloc.palloc`, `promote_palloc`) and the Fill
/// of the copy with the young block's fields (`PromoteCopy.copy_cabs`).
///
/// `ri`: along the promotions, by the allocator contract (`alloc_ok_pages`)
/// at each one,
///   * the page invariant holds, the reading is well formed;
///   * the blocks in use are those in use at the start and the copies;
///   * every block in use at the start keeps its block;
///   * each copy has the young block's size and tag, the colour of the
///     phase (`colour_at`), its fields, and lies on words free at the start;
///   * two copies are two blocks;
///   * the nursery's major pointers are still values the program may store.

module GC.Spec.Top.PagesReplay

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Pages.Inv
open GC.Spec.Top.PagesAlloc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module AT = GC.Spec.Pages.AllocTag
module P = GC.Spec.Pages.Promote
module PI = GC.Spec.Pages.Promote.Idle
module PPI = GC.Spec.Pages.PromoteInst
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module Y = GC.Spec.Top.Young
module PIn = GC.Spec.Top.PagesInst

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The promotion allocator of a phase
/// ---------------------------------------------------------------------------

let ptal (ph: T.phase pprog) (st0: pst) : P.tal pstate =
  match ph with
  | T.Idle -> PI.idle_tal
  | T.Marking -> PPI.mark_tal
  | T.Sweeping _ -> PPI.sw_tal st0.ps.pm

let ptal_alloc (ph: T.phase pprog) (st0: pst) (g: heap) (s: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma ((ptal ph st0).P.alloc g s wz tag == AT.alloc_tag (iph ph) g s wz tag)
  = ()

/// The page allocator's state over a page heap.
let tst (g: heap) (s: pstate) : pst = { ps = s; lo = low g }

let gl_tst (g: heap) (s: pstate) : Lemma (gl g (tst g s) == g) = set_low_self g

/// The tag of a nursery object, as a model tag.
let mtag (ms: minor_state) (m: U64.t) : GTot M.tag_t = minor_tag_bound ms m; minor_tag ms m

/// **One promotion is an allocation of the page allocator component.**
#push-options "--z3rlimit 40"
let promote_palloc (ph: T.phase pprog) (st0: pst) (ms: minor_state) (g: heap) (s: pstate) (m: U64.t)
  : Lemma (requires minor_wosize ms m > 0)
          (ensures (let (g2, s2, o) = PR.promote_at (ptal ph st0) ms g s m in
                    let (g1, st1, res) = palloc ph g (tst g s) (minor_wosize ms m) (mtag ms m) in
                    (o == 0UL ==> res == T.NoRoom /\ g2 == g /\ s2 == s) /\
                    (o =!= 0UL ==> res == T.Ok (maddr o) /\ s2 == st1.ps /\ st1.lo == low g1 /\
                                   g2 == copy_fields ms g1 m o 0 (minor_wosize ms m))))
  = gl_tst g s;
    minor_tag_bound ms m;
    tg_v (mtag ms m);
    U64.v_inj (tg (mtag ms m)) (promoted_tag ms m)
#pop-options

/// ---------------------------------------------------------------------------
/// The bytes below `zero_addr` stay
/// ---------------------------------------------------------------------------

let low_write (g: heap) (a: hp_addr) (v: U64.t)
  : Lemma (requires U64.v a >= base) (ensures low (write_word g a v) == low g)
  = base_facts ();
    write_word_spec g a v;
    Seq.lemma_eq_intro (low (write_word g a v)) (low g)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec low_copy (ms: minor_state) (g: heap) (src dst: U64.t) (i n: nat)
  : Lemma (requires U64.v dst >= base)
          (ensures low (copy_fields ms g src dst i n) == low g) (decreases (if i >= n then 0 else n - i))
  = if i >= n then copy_fields_base ms g src dst i n
    else if U64.v dst + i * 8 + 8 > heap_size || (U64.v dst + i * 8) % 8 <> 0 then copy_fields_oob ms g src dst i n
    else begin
      copy_fields_step ms g src dst i n;
      let a : hp_addr = U64.uint_to_t (U64.v dst + i * 8) in
      low_write g a (minor_read_field ms src i);
      low_copy ms (write_word g a (minor_read_field ms src i)) src dst (i + 1) n
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The invariant along the promotions
/// ---------------------------------------------------------------------------

/// A copy of the young block `o` at `c`.
[@@"opaque_to_smt"]
let copy_ok (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (m: M.mheap) (o c: nat) : prop =
  m.M.hd c == Some ({ M.wz = M.wz_of y o; M.tag = M.tag_of y o; M.col = T.colour_at pk ph c }) /\
  (forall (f: nat). f < M.wz_of y o ==> M.field m c f == M.field y o f) /\
  (forall (w: nat). M.covers m c w ==> T.free_word pa st0 h0 (cabs h0) w)

let copy_ok_def (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (m: M.mheap) (o c: nat)
  : Lemma (copy_ok ph st0 h0 y m o c <==>
           (m.M.hd c == Some ({ M.wz = M.wz_of y o; M.tag = M.tag_of y o; M.col = T.colour_at pk ph c }) /\
            (forall (f: nat). f < M.wz_of y o ==> M.field m c f == M.field y o f) /\
            (forall (w: nat). M.covers m c w ==> T.free_word pa st0 h0 (cabs h0) w)))
  = reveal_opaque (`%copy_ok) (copy_ok ph st0 h0 y m o c)

/// The nursery's major pointers may be stored.
[@@"opaque_to_smt"]
let ysound (ph: T.phase pprog) (st: pst) (g: heap) (m: M.mheap) (y: M.mheap) : prop =
  forall (yb i b: nat). M.ptr_field y yb i /\ M.field y yb i == M.VPtr (M.Major b) ==>
    T.sound_value pa ph st g m (M.VPtr (M.Major b))

let ysound_def (ph: T.phase pprog) (st: pst) (g: heap) (m: M.mheap) (y: M.mheap)
  : Lemma (ysound ph st g m y <==>
           (forall (yb i b: nat). M.ptr_field y yb i /\ M.field y yb i == M.VPtr (M.Major b) ==>
              T.sound_value pa ph st g m (M.VPtr (M.Major b))))
  = reveal_opaque (`%ysound) (ysound ph st g m y)

/// The blocks in use: those at the start, and the copies.
[@@"opaque_to_smt"]
let ri_iu (st0: pst) (h0: heap) (g: heap) (st: pst) (m: M.mheap) (cps: list (nat & nat)) : prop =
  forall (x: nat). T.in_use pa st g m x <==> (T.in_use pa st0 h0 (cabs h0) x \/ (exists (o: nat). L.memP (o, x) cps))

let ri_iu_def (st0: pst) (h0: heap) (g: heap) (st: pst) (m: M.mheap) (cps: list (nat & nat))
  : Lemma (ri_iu st0 h0 g st m cps <==>
           (forall (x: nat). T.in_use pa st g m x <==> (T.in_use pa st0 h0 (cabs h0) x \/ (exists (o: nat). L.memP (o, x) cps))))
  = reveal_opaque (`%ri_iu) (ri_iu st0 h0 g st m cps)

/// The blocks in use at the start keep their blocks.
[@@"opaque_to_smt"]
let ri_kept (st0: pst) (h0: heap) (m: M.mheap) : prop =
  forall (x: nat). T.in_use pa st0 h0 (cabs h0) x ==> M.same_block (cabs h0) m x

let ri_kept_def (st0: pst) (h0: heap) (m: M.mheap)
  : Lemma (ri_kept st0 h0 m <==> (forall (x: nat). T.in_use pa st0 h0 (cabs h0) x ==> M.same_block (cabs h0) m x))
  = reveal_opaque (`%ri_kept) (ri_kept st0 h0 m)

/// The copies, each once.
[@@"opaque_to_smt"]
let ri_copies (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (m: M.mheap) (cps: list (nat & nat)) : prop =
  (forall (o c: nat). L.memP (o, c) cps ==> copy_ok ph st0 h0 y m o c) /\
  (forall (o1 o2 c: nat). L.memP (o1, c) cps /\ L.memP (o2, c) cps ==> o1 == o2)

let ri_copies_def (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (m: M.mheap) (cps: list (nat & nat))
  : Lemma (ri_copies ph st0 h0 y m cps <==>
           ((forall (o c: nat). L.memP (o, c) cps ==> copy_ok ph st0 h0 y m o c) /\
            (forall (o1 o2 c: nat). L.memP (o1, c) cps /\ L.memP (o2, c) cps ==> o1 == o2)))
  = reveal_opaque (`%ri_copies) (ri_copies ph st0 h0 y m cps)

#push-options "--fuel 1"
let ri_copies_nil (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (m: M.mheap)
  : Lemma (ri_copies ph st0 h0 y m [])
  = ri_copies_def ph st0 h0 y m []
#pop-options

/// **The invariant**, at the page heap `g`, page state `st`, reading `m`,
/// after the promotions `cps` (young block, copy).
let ri (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (g: heap) (st: pst) (m: M.mheap)
       (cps: list (nat & nat)) : prop =
  R.heq m (cabs g) /\ gl g st == g /\ pa.T.inv ph g st /\ M.well_formed m /\
  ri_iu st0 h0 g st m cps /\ ri_kept st0 h0 m /\ ri_copies ph st0 h0 y m cps /\ ysound ph st g m y

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let gl_gl (h: heap) (lo: low_t) : Lemma (set_low (set_low h lo) lo == set_low h lo)
  = low_set_low h lo;
    set_low_self (set_low h lo)

/// The page heap of the start: `gl h0 st0`, with the page state of `st0`.
#push-options "--z3rlimit 40 --fuel 1"
let ri_start (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (w: M.world)
  : Lemma (requires pa.T.inv ph h0 st0 /\ M.well_formed w.M.maj /\ R.heq w.M.maj (cabs h0) /\
                    T.young_sound pa ph st0 h0 w /\ w.M.yng == y)
          (ensures ri ph st0 h0 y (gl h0 st0) st0 (cabs h0) [])
  = let g0 = gl h0 st0 in
    gl_gl h0 st0.lo;
    assert (pa.T.inv ph g0 st0);
    PIn.wf_heq w.M.maj (cabs h0);
    cabs_set_low h0 st0.lo;
    assert (R.heq (cabs h0) (cabs g0));
    let iu (x: nat) : Lemma (T.in_use pa st0 g0 (cabs h0) x == T.in_use pa st0 h0 (cabs h0) x)
      = assert ((cabs g0).M.hd x == (cabs h0).M.hd x) in
    FStar.Classical.forall_intro iu;
    let sv (b: nat)
      : Lemma (T.sound_value pa ph st0 h0 w.M.maj (M.VPtr (M.Major b)) ==>
               T.sound_value pa ph st0 g0 (cabs h0) (M.VPtr (M.Major b)))
      = assert (forall (a: nat). M.resolve w.M.maj a == M.resolve (cabs h0) a);
        assert (forall (x: nat). T.in_use pa st0 h0 w.M.maj x == T.in_use pa st0 g0 (cabs h0) x);
        assert (forall (x: nat). M.col_of w.M.maj x == M.col_of (cabs h0) x) in
    FStar.Classical.forall_intro sv;
    ysound_def ph st0 g0 (cabs h0) y;
    assert (ysound ph st0 g0 (cabs h0) y);
    ri_iu_def st0 h0 g0 st0 (cabs h0) [];
    assert (ri_iu st0 h0 g0 st0 (cabs h0) []);
    ri_kept_def st0 h0 (cabs h0);
    assert (ri_kept st0 h0 (cabs h0));
    ri_copies_nil ph st0 h0 y (cabs h0)
#pop-options

/// ---------------------------------------------------------------------------
/// Model facts for the step
/// ---------------------------------------------------------------------------

/// The Fill of `c` leaves every other block of a tiled heap.
let fill_keeps (m: M.mheap) (c: nat) (vs: list M.value) (x: nat)
  : Lemma (requires M.tiled m /\ M.is_block m c /\ L.length vs <= M.wz_of m c /\ M.is_block m x /\ x <> c)
          (ensures M.same_block m (M.fill m c vs) x)
  = let one (f: nat) : Lemma (f < M.wz_of m x ==> M.field (M.fill m c vs) x f == M.field m x f)
      = if f < M.wz_of m x then begin
          let w = x + 1 + f in
          if c < w && w - c - 1 < L.length vs then assert (M.covers m c w /\ M.covers m x w)
        end in
    FStar.Classical.forall_intro one

let fill_hd (m: M.mheap) (c: nat) (vs: list M.value)
  : Lemma ((M.fill m c vs).M.hd == m.M.hd /\ (M.fill m c vs).M.size == m.M.size) = ()

let wf_fill (m: M.mheap) (c: nat) (vs: list M.value)
  : Lemma (requires M.well_formed m) (ensures M.well_formed (M.fill m c vs))
  = let m2 = M.fill m c vs in
    assert (forall (o: nat). M.is_block m2 o == M.is_block m o);
    assert (forall (o: nat). M.hdr_of m2 o == M.hdr_of m o);
    assert (forall (o w: nat). M.covers m2 o w == M.covers m o w)

/// A word free now was free at the start.
#push-options "--z3rlimit 40"
let free_back (st0: pst) (h0: heap) (g: heap) (st: pst) (m: M.mheap) (cps: list (nat & nat)) (w: nat)
  : Lemma (requires ri_iu st0 h0 g st m cps /\ ri_kept st0 h0 m /\ M.tiled m /\ M.tiled (cabs h0) /\
                    m.M.size == (cabs h0).M.size /\ T.free_word pa st g m w)
          (ensures T.free_word pa st0 h0 (cabs h0) w)
  = ri_iu_def st0 h0 g st m cps;
    ri_kept_def st0 h0 m;
    let m0 = cabs h0 in
    let b = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun b -> M.covers m b w /\ pa.T.free st g b) in
    assert (w < m.M.size);
    assert (w < m0.M.size);
    let b0 = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun b0 -> M.covers m0 b0 w) in
    if T.in_use pa st0 h0 m0 b0 then begin
      assert (M.same_block m0 m b0);
      assert (M.covers m b0 w);
      assert (b0 == b);
      assert (T.in_use pa st g m b)
    end
    else assert (M.covers m0 b0 w /\ pa.T.free st0 h0 b0)
#pop-options

/// The pages' free: blue, read from the heap's headers.
let pfree_heq (st st': pst) (g g': heap) (x: nat)
  : Lemma (requires (cabs g).M.hd x == (cabs g').M.hd x) (ensures pa.T.free st g x == pa.T.free st' g' x)
  = ()

/// ---------------------------------------------------------------------------
/// The invariant, up to the reading
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let ri_heq (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (g: heap) (st: pst) (m m': M.mheap)
           (cps: list (nat & nat))
  : Lemma (requires ri ph st0 h0 y g st m cps /\ R.heq m m') (ensures ri ph st0 h0 y g st m' cps)
  = PIn.wf_heq m m';
    ri_iu_def st0 h0 g st m cps;
    ri_iu_def st0 h0 g st m' cps;
    assert (forall (x: nat). T.in_use pa st g m' x == T.in_use pa st g m x);
    ri_kept_def st0 h0 m;
    ri_kept_def st0 h0 m';
    ri_copies_def ph st0 h0 y m cps;
    ri_copies_def ph st0 h0 y m' cps;
    let cp (o c: nat) : Lemma (copy_ok ph st0 h0 y m o c ==> copy_ok ph st0 h0 y m' o c)
      = copy_ok_def ph st0 h0 y m o c; copy_ok_def ph st0 h0 y m' o c;
        assert (forall (w: nat). M.covers m' c w == M.covers m c w) in
    FStar.Classical.forall_intro_2 cp;
    ysound_def ph st g m y;
    ysound_def ph st g m' y;
    let sv (b: nat)
      : Lemma (T.sound_value pa ph st g m (M.VPtr (M.Major b)) ==> T.sound_value pa ph st g m' (M.VPtr (M.Major b)))
      = PIn.resolve_heq m m' b in
    FStar.Classical.forall_intro sv
#pop-options

/// ---------------------------------------------------------------------------
/// One promotion
/// ---------------------------------------------------------------------------

/// The allocator contract at one allocation.
let get_post (ph: T.phase pprog) (g: heap) (st: pst) (m: M.mheap) (wz: M.size_t) (tag: M.tag_t)
  : Lemma (requires R.heq m (cabs g) /\ pa.T.inv ph g st /\ M.well_formed m /\ tag <> M.infix_tag)
          (ensures (let (g1, st1, res) = pa.T.alloc ph g st wz tag in
                    exists (m': M.mheap). brepr m' g1 /\ T.alloc_post byte_rep pa ph g st wz tag g1 st1 res m m'))
  = PIn.alloc_ok_pages ();
    assert (T.alloc_at byte_rep pa ph g st wz tag)

#push-options "--fuel 1"
let mem_cons2 (o c x: nat) (cps: list (nat & nat))
  : Lemma ((exists (o': nat). L.memP (o', x) ((o, c) :: cps)) <==>
           (x == c \/ (exists (o': nat). L.memP (o', x) cps)))
  = ()

let mem_cons (p q: nat & nat) (cps: list (nat & nat))
  : Lemma (L.memP p (q :: cps) <==> (p == q \/ L.memP p cps))
  = ()
#pop-options

/// The blocks in use after.
#push-options "--z3rlimit 40"
let step_iu (ph: T.phase pprog) (st0: pst) (h0: heap) (g: heap) (st: pst) (m: M.mheap) (cps: list (nat & nat))
            (wz: M.size_t) (tag: M.tag_t) (g1 g2: heap) (st1: pst) (c: nat) (m' m2: M.mheap) (o: nat)
  : Lemma (requires ri_iu st0 h0 g st m cps /\ T.alloc_post byte_rep pa ph g st wz tag g1 st1 (T.Ok c) m m' /\
                    brepr m' g1 /\ R.heq m2 (cabs g2) /\ m2.M.hd == m'.M.hd /\ m2.M.size == m'.M.size)
          (ensures ri_iu st0 h0 g2 st1 m2 ((o, c) :: cps))
  = ri_iu_def st0 h0 g st m cps;
    ri_iu_def st0 h0 g2 st1 m2 ((o, c) :: cps);
    let one (x: nat) : Lemma (T.in_use pa st1 g2 m2 x == T.in_use pa st1 g1 m' x)
      = pfree_heq st1 st1 g2 g1 x in
    FStar.Classical.forall_intro one;
    FStar.Classical.forall_intro (fun (x: nat) -> mem_cons2 o c x cps)
#pop-options

/// The new block was not in use.
let new_not_in_use (ph: T.phase pprog) (g: heap) (st: pst) (m: M.mheap) (wz: M.size_t) (tag: M.tag_t)
                   (g1: heap) (st1: pst) (c: nat) (m': M.mheap)
  : Lemma (requires T.alloc_post byte_rep pa ph g st wz tag g1 st1 (T.Ok c) m m' /\ M.tiled m)
          (ensures ~(T.in_use pa st g m c))
  = assert (M.covers m' c c);
    let b = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun b -> M.covers m b c /\ pa.T.free st g b) in
    if T.in_use pa st g m c then assert (M.covers m c c)

/// The blocks in use at the start keep their blocks.
#push-options "--z3rlimit 40"
let step_kept (ph: T.phase pprog) (st0: pst) (h0: heap) (g: heap) (st: pst) (m: M.mheap) (cps: list (nat & nat))
              (wz: M.size_t) (tag: M.tag_t) (g1: heap) (st1: pst) (c: nat) (m': M.mheap) (vs: list M.value)
  : Lemma (requires ri_iu st0 h0 g st m cps /\ ri_kept st0 h0 m /\ M.tiled m /\
                    T.alloc_post byte_rep pa ph g st wz tag g1 st1 (T.Ok c) m m' /\ L.length vs == wz)
          (ensures ri_kept st0 h0 (M.fill m' c vs) /\
                   (forall (x: nat). T.in_use pa st g m x ==> M.same_block m (M.fill m' c vs) x))
  = ri_iu_def st0 h0 g st m cps;
    ri_kept_def st0 h0 m;
    ri_kept_def st0 h0 (M.fill m' c vs);
    new_not_in_use ph g st m wz tag g1 st1 c m';
    let one (x: nat) : Lemma (T.in_use pa st g m x ==> M.same_block m (M.fill m' c vs) x)
      = if T.in_use pa st g m x then begin
          assert (M.same_block m m' x);
          assert (x <> c);
          fill_keeps m' c vs x
        end in
    FStar.Classical.forall_intro one
#pop-options

let fill_field (m: M.mheap) (c: nat) (vs: list M.value) (f: nat)
  : Lemma (f < L.length vs ==> M.field (M.fill m c vs) c f == L.index vs f)
  = assert ((c + 1 + f) - c - 1 == f)

let copy_fields_y (m: M.mheap) (c: nat) (y: M.mheap) (o: nat)
  : Lemma (forall (f: nat). f < M.wz_of y o ==> M.field (M.fill m c (M.fields_of y o)) c f == M.field y o f)
  = M.fields_of_spec y o;
    FStar.Classical.forall_intro (fill_field m c (M.fields_of y o))

/// The new copy.
#push-options "--z3rlimit 40"
let copy_new (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (g: heap) (st: pst) (m: M.mheap)
             (cps: list (nat & nat)) (o: nat) (g1: heap) (st1: pst) (c: nat) (m': M.mheap)
  : Lemma (requires ri_iu st0 h0 g st m cps /\ ri_kept st0 h0 m /\
                    M.tiled m /\ M.tiled (cabs h0) /\ m.M.size == (cabs h0).M.size /\
                    M.is_block y o /\ M.wz_of y o > 0 /\
                    T.alloc_post byte_rep pa ph g st (M.wz_of y o) (M.tag_of y o) g1 st1 (T.Ok c) m m')
          (ensures copy_ok ph st0 h0 y (M.fill m' c (M.fields_of y o)) o c)
  = let m2 = M.fill m' c (M.fields_of y o) in
    copy_fields_y m' c y o;
    fill_hd m' c (M.fields_of y o);
    assert (m2.M.hd c == Some ({ M.wz = M.wz_of y o; M.tag = M.tag_of y o; M.col = T.colour_at pk ph c }));
    copy_ok_def ph st0 h0 y m2 o c;
    let fw (w: nat) : Lemma (M.covers m2 c w ==> T.free_word pa st0 h0 (cabs h0) w)
      = if M.covers m2 c w then begin
          assert (M.covers m' c w);
          free_back st0 h0 g st m cps w
        end in
    FStar.Classical.forall_intro fw
#pop-options

/// An earlier copy stays.
let copy_old (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (m m2: M.mheap) (o c: nat)
  : Lemma (requires copy_ok ph st0 h0 y m o c /\ M.same_block m m2 c /\ m2.M.size == m.M.size)
          (ensures copy_ok ph st0 h0 y m2 o c)
  = copy_ok_def ph st0 h0 y m o c;
    copy_ok_def ph st0 h0 y m2 o c;
    assert (forall (w: nat). M.covers m2 c w == M.covers m c w)

/// An earlier copy is in use.
let copy_in_use (st0: pst) (h0: heap) (g: heap) (st: pst) (m: M.mheap) (cps: list (nat & nat)) (o c: nat)
  : Lemma (requires ri_iu st0 h0 g st m cps /\ L.memP (o, c) cps) (ensures T.in_use pa st g m c)
  = ri_iu_def st0 h0 g st m cps

/// The copies after.
#push-options "--z3rlimit 40"
let step_copies (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (g: heap) (st: pst) (m: M.mheap)
                (cps: list (nat & nat)) (o: nat) (g1: heap) (st1: pst) (c: nat) (m': M.mheap)
  : Lemma (requires ri_iu st0 h0 g st m cps /\ ri_kept st0 h0 m /\ ri_copies ph st0 h0 y m cps /\
                    M.tiled m /\ M.tiled (cabs h0) /\ m.M.size == (cabs h0).M.size /\
                    M.is_block y o /\ M.wz_of y o > 0 /\
                    T.alloc_post byte_rep pa ph g st (M.wz_of y o) (M.tag_of y o) g1 st1 (T.Ok c) m m' /\
                    (forall (x: nat). T.in_use pa st g m x ==> M.same_block m (M.fill m' c (M.fields_of y o)) x))
          (ensures ri_copies ph st0 h0 y (M.fill m' c (M.fields_of y o)) ((o, c) :: cps))
  = let m2 = M.fill m' c (M.fields_of y o) in
    ri_copies_def ph st0 h0 y m cps;
    ri_copies_def ph st0 h0 y m2 ((o, c) :: cps);
    new_not_in_use ph g st m (M.wz_of y o) (M.tag_of y o) g1 st1 c m';
    copy_new ph st0 h0 y g st m cps o g1 st1 c m';
    let old (o' c': nat) : Lemma (L.memP (o', c') cps ==> copy_ok ph st0 h0 y m2 o' c' /\ c' <> c)
      = if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (o', c') cps) then begin
          copy_in_use st0 h0 g st m cps o' c';
          copy_old ph st0 h0 y m m2 o' c'
        end in
    FStar.Classical.forall_intro_2 old;
    let inj (o1 o2 c'': nat)
      : Lemma (L.memP (o1, c'') ((o, c) :: cps) /\ L.memP (o2, c'') ((o, c) :: cps) ==> o1 == o2)
      = mem_cons (o1, c'') (o, c) cps; mem_cons (o2, c'') (o, c) cps in
    FStar.Classical.forall_intro_3 inj;
    let all (o' c': nat) : Lemma (L.memP (o', c') ((o, c) :: cps) ==> copy_ok ph st0 h0 y m2 o' c')
      = mem_cons (o', c') (o, c) cps in
    FStar.Classical.forall_intro_2 all
#pop-options

/// What resolving through an infix header means.
let resolve_infix (m: M.mheap) (b x: nat)
  : Lemma (requires M.resolve m b == Some x /\ b <> x)
          (ensures M.is_block m x /\ ~(M.is_block m b) /\ x < b /\ b - x < M.wz_of m x /\
                   M.infix_hdr (m.M.body b) == Some (b - x) /\ M.tag_of m x == M.closure_tag)
  = ()

let body_field (m: M.mheap) (x b: nat)
  : Lemma (requires x < b) (ensures M.field m x (b - x - 1) == m.M.body b)
  = assert (x + 1 + (b - x - 1) == b)

/// A pointer to a block kept resolves as before.
#push-options "--z3rlimit 40"
let resolve_kept (m m2: M.mheap) (b x: nat)
  : Lemma (requires M.resolve m b == Some x /\ M.same_block m m2 x /\ m2.M.size == m.M.size /\ M.tiled m2)
          (ensures M.resolve m2 b == Some x)
  = if b = x then ()
    else begin
      resolve_infix m b x;
      body_field m x b;
      body_field m2 x b;
      assert (m2.M.body b == m.M.body b);
      if M.is_block m2 b then assert (M.covers m2 b b /\ M.covers m2 x b)
    end
#pop-options

/// The nursery's major pointers may still be stored.
#push-options "--z3rlimit 40"
let step_sound (ph: T.phase pprog) (y: M.mheap) (g: heap) (st: pst) (m: M.mheap)
               (wz: M.size_t) (tag: M.tag_t) (g1 g2: heap) (st1: pst) (c: nat) (m' m2: M.mheap)
  : Lemma (requires ysound ph st g m y /\ T.alloc_post byte_rep pa ph g st wz tag g1 st1 (T.Ok c) m m' /\
                    brepr m' g1 /\ R.heq m2 (cabs g2) /\ m2.M.hd == m'.M.hd /\ m2.M.size == m'.M.size /\
                    M.tiled m2 /\
                    (forall (x: nat). T.in_use pa st g m x ==> M.same_block m m2 x))
          (ensures ysound ph st1 g2 m2 y)
  = ysound_def ph st g m y;
    ysound_def ph st1 g2 m2 y;
    let iu (x: nat) : Lemma (T.in_use pa st1 g2 m2 x == T.in_use pa st1 g1 m' x)
      = pfree_heq st1 st1 g2 g1 x in
    FStar.Classical.forall_intro iu;
    let one (b: nat)
      : Lemma (T.sound_value pa ph st g m (M.VPtr (M.Major b)) ==> T.sound_value pa ph st1 g2 m2 (M.VPtr (M.Major b)))
      = if FStar.IndefiniteDescription.strong_excluded_middle (T.sound_value pa ph st g m (M.VPtr (M.Major b))) then begin
          let x = FStar.IndefiniteDescription.indefinite_description_ghost nat
                    (fun x -> M.resolve m b == Some x /\ T.live_target pa ph st g m x) in
          assert (M.same_block m m2 x);
          resolve_kept m m2 b x;
          assert (T.in_use pa st1 g2 m2 x);
          assert (M.col_of m2 x == M.col_of m x);
          assert (T.live_target pa ph st1 g2 m2 x)
        end in
    FStar.Classical.forall_intro one
#pop-options

/// A value of a young block's fields is one of its fields.
#push-options "--fuel 1 --ifuel 1"
let rec mem_fields (y: M.mheap) (o i n: nat) (v: M.value)
  : Lemma (requires L.memP v (M.fields_from y o i n))
          (ensures exists (j: nat). i <= j /\ j < i + n /\ v == M.field y o j) (decreases n)
  = if n > 0 then
      if FStar.IndefiniteDescription.strong_excluded_middle (v == M.field y o i) then ()
      else mem_fields y o (i + 1) (n - 1) v
#pop-options

/// The Fill of a copy is with values the program may store.
let fill_sound (ph: T.phase pprog) (y: M.mheap) (o: nat) (g: heap) (st: pst) (m: M.mheap)
  : Lemma (requires ysound ph st g m y /\ M.is_block y o)
          (ensures M.scannable (M.tag_of y o) ==>
                   (forall (v: M.value). L.memP v (M.fields_of y o) ==> T.sound_value pa ph st g m v))
  = ysound_def ph st g m y;
    let one (v: M.value) : Lemma (M.scannable (M.tag_of y o) /\ L.memP v (M.fields_of y o) ==> T.sound_value pa ph st g m v)
      = if M.scannable (M.tag_of y o) && FStar.IndefiniteDescription.strong_excluded_middle (L.memP v (M.fields_of y o))
        then begin
          mem_fields y o 0 (M.wz_of y o) v;
          let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
                    (fun j -> j < M.wz_of y o /\ v == M.field y o j) in
          assert (M.ptr_field y o j);
          match v with
          | M.VPtr (M.Major b) -> assert (T.sound_value pa ph st g m (M.VPtr (M.Major b)))
          | _ -> ()
        end in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// The step
/// ---------------------------------------------------------------------------

let st_eta (g: heap) (st: pst) : Lemma (requires gl g st == g) (ensures st == tst g st.ps)
  = low_set_low g st.lo

/// The page facts of the new block.
#push-options "--z3rlimit 40"
let step_block (ph: T.phase pprog) (g: heap) (st: pst) (wz: M.size_t) (tag: M.tag_t)
  : Lemma (requires pa.T.inv ph g st /\ gl g st == g /\ tag <> M.infix_tag /\
                    (let (_, _, o) = AT.alloc_tag (iph ph) g st.ps wz (tg tag) in o <> 0UL))
          (ensures (let (g1, _, o) = AT.alloc_tag (iph ph) g st.ps wz (tg tag) in
                    U64.v o >= 8 /\ pos (maddr o) + 8 == U64.v o /\ U64.v o >= base + 8 /\
                    M.is_block (cabs g1) (maddr o) /\ pos (maddr o) + 8 < heap_size /\ obj_of (maddr o) == o))
  = tg_v tag;
    bfacts (iph ph) g st.ps wz (tg tag);
    let (g1, st1, o) = AT.alloc_tag (iph ph) g st.ps wz (tg tag) in
    let x : obj_addr = o in
    GC.Spec.Top.PagesAllocOk.ok_alloc_intro (iph ph) g st.ps wz (tg tag) g1 st1 x;
    GC.Spec.Top.PagesAllocOk.new_block (iph ph) g st.ps wz (tg tag) g1 st1 x;
    base_facts ()
#pop-options

let copy_heq (m' : M.mheap) (g1 g2: heap) (c: nat) (vs: list M.value)
  : Lemma (requires brepr m' g1 /\ R.heq (cabs g2) (M.fill (cabs g1) c vs))
          (ensures R.heq (M.fill m' c vs) (cabs g2))
  = ()

let step_inv (ph: T.phase pprog) (g: heap) (st: pst) (m: M.mheap) (wz: M.size_t) (tag: M.tag_t)
             (g1 g2: heap) (st1: pst) (c: nat) (m': M.mheap) (vs: list M.value)
  : Lemma (requires T.alloc_post byte_rep pa ph g st wz tag g1 st1 (T.Ok c) m m' /\
                    R.heq (M.fill m' c vs) (cabs g2) /\ L.length vs == wz /\
                    (M.scannable tag ==> (forall (v: M.value). L.memP v vs ==> T.sound_value pa ph st g m v)))
          (ensures pa.T.inv ph g2 st1)
  = let p (vs': list M.value) (h'': heap) : prop =
      L.length vs' == wz /\ (M.scannable tag ==> (forall (v: M.value). L.memP v vs' ==> T.sound_value pa ph st g m v)) /\
      byte_rep.R.repr (M.fill m' c vs') h'' ==> pa.T.inv ph h'' st1 in
    assert (forall (vs': list M.value) (h'': heap). p vs' h'');
    assert (p vs g2)

let ri_mk (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (g: heap) (st: pst) (m: M.mheap)
          (cps: list (nat & nat))
  : Lemma (requires R.heq m (cabs g) /\ gl g st == g /\ pa.T.inv ph g st /\ M.well_formed m /\
                    ri_iu st0 h0 g st m cps /\ ri_kept st0 h0 m /\ ri_copies ph st0 h0 y m cps /\ ysound ph st g m y)
          (ensures ri ph st0 h0 y g st m cps)
  = ()

/// **One promotion keeps the invariant.**
#push-options "--z3rlimit 40"
let ri_step (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (ms: minor_state) (g: heap) (st: pst)
            (m: M.mheap) (cps: list (nat & nat)) (o: nat)
  : Lemma (requires ri ph st0 h0 y g st m cps /\ Y.yrepr y ms /\ M.is_block y o /\ M.well_formed (cabs h0) /\
                    8 * o + 8 < pow2 64 /\ M.wz_of y o >= 1 /\
                    (let (_, _, ob) = PR.promote_at (ptal ph st0) ms g st.ps (PC.yobj o) in ob <> 0UL))
          (ensures (let (g2, s2, ob) = PR.promote_at (ptal ph st0) ms g st.ps (PC.yobj o) in
                    let c = maddr ob in
                    pos c + 8 == U64.v ob /\ ~(T.in_use pa st g m c) /\
                    ri ph st0 h0 y g2 (tst g2 s2) (cabs g2) ((o, c) :: cps) /\
                    (let (g1, st1, res) = palloc ph g st (M.wz_of y o) (M.tag_of y o) in
                     res == T.Ok c /\ st1 == tst g2 s2 /\
                     R.heq (cabs g2) (M.fill (cabs g1) c (M.fields_of y o)))))
  = PC.young_obj y ms o;
    let mm = PC.yobj o in
    let wz : M.size_t = M.wz_of y o in
    let tag : M.tag_t = M.tag_of y o in
    st_eta g st;
    promote_palloc ph st0 ms g st.ps mm;
    let (g2, s2, ob) = PR.promote_at (ptal ph st0) ms g st.ps mm in
    let (g1, st1, res) = palloc ph g st wz tag in
    let c = maddr ob in
    gl_tst g st.ps;
    step_block ph g st wz tag;
    get_post ph g st m wz tag;
    let m' = FStar.IndefiniteDescription.indefinite_description_ghost M.mheap
               (fun m' -> brepr m' g1 /\ T.alloc_post byte_rep pa ph g st wz tag g1 st1 (T.Ok c) m m') in
    let vs = M.fields_of y o in
    M.fields_of_spec y o;
    assert (M.wz_of (cabs g1) c == wz);
    PC.copy_cabs y ms o g1 c;
    let m2 = M.fill m' c vs in
    copy_heq m' g1 g2 c vs;
    low_copy ms g1 mm ob 0 wz;
    set_low_self g2;
    assert (st1 == tst g2 s2);
    fill_hd m' c vs;
    wf_fill m' c vs;
    step_iu ph st0 h0 g st m cps wz tag g1 g2 st1 c m' m2 o;
    step_kept ph st0 h0 g st m cps wz tag g1 st1 c m' vs;
    step_copies ph st0 h0 y g st m cps o g1 st1 c m';
    step_sound ph y g st m wz tag g1 g2 st1 c m' m2;
    new_not_in_use ph g st m wz tag g1 st1 c m';
    fill_sound ph y o g st m;
    step_inv ph g st m wz tag g1 g2 st1 c m' vs;
    ri_mk ph st0 h0 y g2 st1 m2 ((o, c) :: cps);
    ri_heq ph st0 h0 y g2 st1 m2 (cabs g2) ((o, c) :: cps)
#pop-options

let ri_elim_wf (ph: T.phase pprog) (st0: pst) (h0: heap) (y: M.mheap) (g: heap) (st: pst) (m: M.mheap)
               (cps: list (nat & nat))
  : Lemma (requires ri ph st0 h0 y g st m cps)
          (ensures R.heq m (cabs g) /\ M.well_formed (cabs g) /\ gl g st == g)
  = PIn.wf_heq m (cabs g)
