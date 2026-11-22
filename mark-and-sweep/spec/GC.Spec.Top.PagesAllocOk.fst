/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesAllocOk - one page allocation, read as the model
/// ---------------------------------------------------------------------------
///
/// From the byte facts of one allocation (`PagesAlloc.bpost`), the model
/// facts the allocator contract asks for, on the canonical readings
/// `cabs g` (before) and `cabs g'` (after):
///   - the new block, with the size, tag and colour asked for (`new_block`);
///   - the blocks in use: those before, and the new one (`use_rel`);
///   - every other block in use is unchanged (`kept_block`);
///   - the reading after is well formed (`wf_after`), through the heap with
///     the new block's fields cleared, which meets the page invariant;
///   - the new block's words were free (`words_free`).

module GC.Spec.Top.PagesAllocOk

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.PagesAlloc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module B = GC.Spec.Pages.Blocks
module F = GC.Spec.Pages.Fill
module AT = GC.Spec.Pages.AllocTag
module PA = GC.Spec.Pages.Allocator
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module MSA = GC.Spec.Pages.MidSweepAlloc
module NO = GC.Spec.Pages.NewOnly
module CS = GC.Spec.Pages.Cycle.State
module AP = GC.Spec.Pages.AllocPhase
module G = GC.Spec.Pages.Graft
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A block in use of a reading: a block, not blue.
let used (m: M.mheap) (y: nat) : bool = M.is_block m y && M.col_of m y <> M.Blue

/// The byte facts of a successful allocation of `x` (sealed: the lemmas
/// below open it where they need it).
[@@"opaque_to_smt"]
let ok_alloc (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
  : prop =
  bpost ph g st wz tag g' st' x /\ x =!= 0UL

let ok_alloc_elim (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
  : Lemma (requires ok_alloc ph g st wz tag g' st' x) (ensures bpost ph g st wz tag g' st' x /\ x =!= 0UL)
  = reveal_opaque (`%ok_alloc) (ok_alloc ph g st wz tag g' st' x)

let ok_alloc_intro (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
  : Lemma (requires bpost ph g st wz tag g' st' x /\ x =!= 0UL) (ensures ok_alloc ph g st wz tag g' st' x)
  = reveal_opaque (`%ok_alloc) (ok_alloc ph g st wz tag g' st' x)

/// The facts of the new block the word lemmas read.
let alloc_basics (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
  : Lemma (requires ok_alloc ph g st wz tag g' st' x)
          (ensures Seq.mem x (objects zero_addr g') /\ U64.v (wosize_of_object x g') == wz /\
                   tag_of_object x g' == tag /\ MS.same_swept st.pm st'.pm)
  = ok_alloc_elim ph g st wz tag g' st' x

let used_iff (g: heap) (y: nat)
  : Lemma (used (cabs g) y <==> (pos y + 8 < heap_size /\ Seq.mem (obj_of y) (objects zero_addr g) /\
                                ~(is_blue (obj_of y) g)))
  = mblock (cabs g) g y;
    if M.is_block (cabs g) y then mhdr (cabs g) g y

/// ---------------------------------------------------------------------------
/// The new block
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let new_block (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
  : Lemma (requires ok_alloc ph g st wz tag g' st' x)
          (ensures (let mo = maddr x in
                    pos mo + 8 == U64.v x /\ obj_of mo == x /\
                    M.is_block (cabs g') mo /\
                    (cabs g').M.hd mo == Some ({ M.wz = wz; M.tag = U64.v tag; M.col = abs_col (I.new_colour ph) }) /\
                    ~(used (cabs g) mo)))
  = ok_alloc_elim ph g st wz tag g' st' x;
    obj_maddr g' x;
    let mo = maddr x in
    abs_header g' mo;
    used_iff g mo
#pop-options

/// ---------------------------------------------------------------------------
/// Blocks in use
/// ---------------------------------------------------------------------------

let use_rel (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
    (y: nat)
  : Lemma (requires ok_alloc ph g st wz tag g' st' x)
          (ensures used (cabs g') y <==> (used (cabs g) y \/ y == maddr x))
  = ok_alloc_elim ph g st wz tag g' st' x;
    used_iff g y; used_iff g' y;
    new_block ph g st wz tag g' st' x;
    is_blue_iff x g';
    if pos y + 8 < heap_size then begin
      let v = obj_of y in
      if v = x then maddr_obj y
      else if Seq.mem v (objects zero_addr g) && not (is_blue v g) then begin
        assert (Seq.mem v (objects zero_addr g') /\ read_word g' (hd_address v) == read_word g (hd_address v));
        color_of_object_spec v g; color_of_object_spec v g';
        is_blue_iff v g; is_blue_iff v g'
      end
    end

/// Every other block in use keeps its header and fields.
#push-options "--z3rlimit 40"
let kept_block (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
    (y: nat)
  : Lemma (requires ok_alloc ph g st wz tag g' st' x /\ used (cabs g) y)
          (ensures (cabs g').M.hd y == (cabs g).M.hd y /\
                   (forall (i: nat). i < M.wz_of (cabs g) y ==> M.field (cabs g') y i == M.field (cabs g) y i))
  = ok_alloc_elim ph g st wz tag g' st' x;
    used_iff g y;
    let v = obj_of y in
    assert (Seq.mem v (objects zero_addr g') /\ read_word g' (hd_address v) == read_word g (hd_address v));
    hd_of_obj y;
    abs_is_block g y; abs_is_block g' y;
    assert (word g' y == word g y);
    assert ((cabs g').M.hd y == (cabs g).M.hd y);
    let fld (i: nat) : Lemma (i < M.wz_of (cabs g) y ==> M.field (cabs g') y i == M.field (cabs g) y i)
      = if i < M.wz_of (cabs g) y then begin
          let w = y + 1 + i in
          abs_header g y;
          assert (M.covers (abs g) y w /\ M.covers (abs g') y w);
          is_fw_iff g w; is_fw_iff g' w;
          msize_pos w;
          abs_field g y i;
          abs_field g' y i;
          assert (U64.v (hp w) == U64.v v + 8 * i);
          assert (read_word g' (hp w) == read_word g (hp w))
        end in
    FStar.Classical.forall_intro fld
#pop-options

/// ---------------------------------------------------------------------------
/// The reading after is well formed
/// ---------------------------------------------------------------------------

/// The fields of `x` cleared.
let rec zero_fields (g: heap) (x: nat) (n: nat) : GTot heap (decreases n) =
  if n = 0 then g else zero_fields (B.wr g (x + 8 * (n - 1)) 0UL) x (n - 1)

#push-options "--fuel 1"
let rec zero_fields_read (g: heap) (x: nat) (n: nat) (a: hp_addr)
  : Lemma (requires x % 8 == 0)
          (ensures read_word (zero_fields g x n) a == (if x <= U64.v a && U64.v a < x + 8 * n then 0UL else read_word g a))
          (decreases n)
  = if n = 0 then ()
    else begin
      let g1 = B.wr g (x + 8 * (n - 1)) 0UL in
      zero_fields_read g1 x (n - 1) a;
      B.wr_read g (x + 8 * (n - 1)) 0UL a
    end
#pop-options

/// The cleared heap is one the caller may make.
let zero_written (free: free_def) (g': heap) (x: obj_addr)
  : Lemma (AT.fields_written_away free g' (zero_fields g' (U64.v x) (U64.v (wosize_of_object x g'))) x)
  = FStar.Classical.forall_intro (zero_fields_read g' (U64.v x) (U64.v (wosize_of_object x g')))

/// The page invariant gives the walk to the end and no infix block.
let inv_walk (ph: I.phase) (g: heap) (st: pstate)
  : Lemma (requires MSA.inv_sw ph g st)
          (ensures W.reaches g zero_addr heap_size /\ no_infix_block g /\ blocks_fit g)
  = wf_with_parts ();
    match ph with
    | I.Idle -> CS.ok_walk g st
    | I.Marking -> CS.mc_walk g st
    | I.Sweeping -> MS.pages_ok_sw_elim g st; CS.sw_walk g st

/// The walk does not stop inside the fields of an object.
let walk_apart (g: heap) (x: obj_addr) (q: hp_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ W.reaches g zero_addr (U64.v q))
          (ensures U64.v q < U64.v x \/ U64.v q >= U64.v x + 8 * U64.v (wosize_of_object x g))
  = W.objects_mem_iff g zero_addr x;
    hd_address_spec x;
    if U64.v q >= U64.v x then begin
      W.reaches_block_before g zero_addr (hd_address x) (U64.v q);
      wosize_of_object_spec x g
    end

#push-options "--z3rlimit 40"
let wf_after (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
  : Lemma (requires ok_alloc ph g st wz tag g' st' x)
          (ensures M.well_formed (cabs g') /\ W.reaches g' zero_addr heap_size /\ no_infix_block g')
  = ok_alloc_elim ph g st wz tag g' st' x;
    let n = U64.v (wosize_of_object x g') in
    let gz = zero_fields g' (U64.v x) n in
    zero_written (free_of ph st') g' x;
    inv_walk ph gz st';
    FStar.Classical.forall_intro (zero_fields_read g' (U64.v x) n);
    F.obj_same g' gz x x;
    let sz (q: hp_addr)
      : Lemma (W.reaches gz zero_addr (U64.v q) ==> getWosize (read_word g' q) == getWosize (read_word gz q))
      = if W.reaches gz zero_addr (U64.v q) then begin
          walk_apart gz x q;
          wosize_of_object_spec x gz; wosize_of_object_spec x g'
        end in
    FStar.Classical.forall_intro sz;
    W.walk_congr gz g' zero_addr;
    assert (F.fctx g' gz x);
    CS.fill_back g' gz x;
    abs_well_formed g';
    wf_cabs g'
#pop-options

/// ---------------------------------------------------------------------------
/// The new block's words were free
/// ---------------------------------------------------------------------------

let words_free (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) (g': heap) (st': pstate) (x: obj_addr)
    (w: nat)
  : Lemma (requires ok_alloc ph g st wz tag g' st' x /\ M.well_formed (cabs g) /\ M.covers (cabs g') (maddr x) w)
          (ensures exists (y: nat). M.covers (cabs g) y w /\ M.is_block (cabs g) y /\ M.col_of (cabs g) y == M.Blue)
  = wf_after ph g st wz tag g' st' x;
    new_block ph g st wz tag g' st' x;
    let mo = maddr x in
    assert (w < msize);
    let y = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun y -> M.covers (cabs g) y w) in
    if M.col_of (cabs g) y <> M.Blue then begin
      kept_block ph g st wz tag g' st' x y;
      assert (M.covers (cabs g') y w);
      assert (y == mo);
      use_rel ph g st wz tag g' st' x y
    end

/// ---------------------------------------------------------------------------
/// The invariant after the Fill
/// ---------------------------------------------------------------------------

/// A value the program may store, read on the byte heap before the
/// allocation: a pointer resolves to a block in use, not a white block of an
/// unswept page while sweeping.
let sound_b (ph: I.phase) (st: pstate) (g: heap) (v: M.value) : prop =
  match v with
  | M.VPtr (M.Major b) ->
    exists (y: nat). M.resolve (cabs g) b == Some y /\ used (cabs g) y /\
      (ph == I.Sweeping ==> ~(M.col_of (cabs g) y == M.White /\ G.uw st.pm (pos y)))
  | _ -> True

/// The heap the Fill makes, seen by the page functions.
let fill_ctx (ph: I.phase) (g: heap) (st: pstate) (wz: M.size_t) (tag: AT.tag_t) (g': heap) (st': pstate)
    (x: obj_addr) (vs: list M.value) (g3: heap) : prop =
  ok_alloc ph g st wz tag g' st' x /\ M.well_formed (cabs g) /\ L.length vs == wz /\
  R.agree (M.fill (cabs g') (maddr x) vs) (abs g3) /\ low g3 == low g'

/// The words of a word heap past `zero_addr`, by the model word they hold.
let word_pt (g g': heap) (j: nat)
  : Lemma (requires j < msize /\ (forall (o: nat). o < msize ==> (abs g).M.hd o == (abs g').M.hd o) /\
                    (M.is_block (abs g) j \/
                     (exists (o: nat). M.covers (abs g) o j /\ o < j /\ (abs g).M.body j == (abs g').M.body j)))
          (ensures word g j == word g' j)
  = if M.is_block (abs g) j then abs_hdr_inj (word g j) (word g' j)
    else absv_inj (word g j) (word g' j)

/// The new block's fields, in model words and in bytes.
let fields_pos (x: obj_addr) (mo wz: nat) (a: hp_addr)
  : Lemma (requires pos mo + 8 == U64.v x /\ U64.v a >= base)
          (ensures (let j = mpos (U64.v a) in
                    (U64.v x <= U64.v a /\ U64.v a < U64.v x + 8 * wz) <==> (mo < j /\ j <= mo + wz)))
  = base_facts ();
    FStar.Math.Lemmas.lemma_div_exact (U64.v a - base) 8

let low_word (g g': heap) (a: hp_addr)
  : Lemma (requires U64.v a < base /\ low g == low g') (ensures read_word g a == read_word g' a)
  = base_facts ();
    read_word_spec g a; read_word_spec g' a;
    let same (i: nat{i < heap_size}) : Lemma (requires i < base) (ensures Seq.index g i == Seq.index g' i)
      = assert (Seq.index (low g) i == Seq.index g i);
        assert (Seq.index (low g') i == Seq.index g' i) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires same)

/// The facts about the Fill's heap the word lemmas read.
let prep (g' g3: heap) (mo wz: nat) (vs: list M.value) : prop =
  M.tiled (abs g') /\ R.agree (M.fill (cabs g') mo vs) (abs g3) /\ low g3 == low g' /\ L.length vs == wz

let covers_le (h: M.mheap) (o j: nat) : Lemma (requires M.covers h o j) (ensures o <= j) = ()

let cabs_body_fw (g: heap) (o j: nat)
  : Lemma (requires M.covers (abs g) o j /\ o < j) (ensures (cabs g).M.body j == (abs g).M.body j)
  = is_fw_iff g j

let agree_fw (m1 m2: M.mheap) (o j: nat)
  : Lemma (requires R.agree m1 m2 /\ M.covers m1 o j /\ o < j) (ensures m1.M.body j == m2.M.body j)
  = assert (M.covers m2 o j)

/// Outside the new block's fields, the Fill's heap is the allocator's.
#push-options "--z3rlimit 40"
let outside_eq (g' g3: heap) (x: obj_addr) (mo wz: nat) (vs: list M.value) (a: hp_addr)
  : Lemma (requires prep g' g3 mo wz vs /\ pos mo + 8 == U64.v x /\
                    (U64.v a < U64.v x \/ U64.v a >= U64.v x + 8 * wz))
          (ensures read_word g3 a == read_word g' a)
  = if U64.v a < base then low_word g3 g' a
    else begin
      let mf = M.fill (cabs g') mo vs in
      word_at g3 a; word_at g' a;
      fields_pos x mo wz a;
      let j = mpos (U64.v a) in
      let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers (abs g') o j) in
      assert (forall (q: nat). q < msize ==> (abs g').M.hd q == (abs g3).M.hd q);
      covers_le (abs g') o j;
      if o = j then word_pt g' g3 j
      else begin
        assert (M.covers mf o j);
        agree_fw mf (abs g3) o j;
        assert (mf.M.body j == (cabs g').M.body j);
        cabs_body_fw g' o j;
        word_pt g' g3 j
      end
    end
#pop-options

let field_arith (x: obj_addr) (mo wz: nat) (i: nat) (a: hp_addr)
  : Lemma (requires pos mo + 8 == U64.v x /\ U64.v a == U64.v x + 8 * i /\ i < wz)
          (ensures U64.v a >= base /\ mo < mpos (U64.v a) /\ mpos (U64.v a) <= mo + wz /\
                   mpos (U64.v a) - mo - 1 == i)
  = base_facts ();
    FStar.Math.Lemmas.lemma_div_plus (pos mo + 8 - base) i 8

/// The index of a field address.
let field_index (x: obj_addr) (wz: nat) (a: hp_addr)
  : Lemma (requires U64.v x <= U64.v a /\ U64.v a < U64.v x + 8 * wz)
          (ensures (U64.v a - U64.v x) / 8 < wz /\ U64.v a == U64.v x + 8 * ((U64.v a - U64.v x) / 8))
  = FStar.Math.Lemmas.lemma_div_exact (U64.v a - U64.v x) 8

/// In the new block's fields, the Fill's values.
let field_val (g' g3: heap) (x: obj_addr) (mo wz: nat) (vs: list M.value) (i: nat) (a: hp_addr)
  : Lemma (requires prep g' g3 mo wz vs /\ pos mo + 8 == U64.v x /\ M.is_block (cabs g') mo /\
                    M.wz_of (cabs g') mo == wz /\ U64.v a == U64.v x + 8 * i /\ i < wz)
          (ensures absv (read_word g3 a) == L.index vs i)
  = field_arith x mo wz i a;
    word_at g3 a;
    let j = mpos (U64.v a) in
    let mf = M.fill (cabs g') mo vs in
    assert (M.covers mf mo j);
    agree_fw mf (abs g3) mo j

let plus_back (y b: nat) : Lemma (requires y < b) (ensures y + 1 + (b - y - 1) == b) = ()

/// In a tiled heap, a word of one block is in no other.
let kept_cover (mg': M.mheap) (mo wz b y: nat)
  : Lemma (requires M.tiled mg' /\ M.is_block mg' mo /\ M.wz_of mg' mo == wz /\ M.is_block mg' y /\ y <> mo /\
                    (b == y \/ (y < b /\ b <= y + M.wz_of mg' y)))
          (ensures (b < mo \/ b > mo + wz) /\ (b <> y ==> ~(M.is_block mg' b)))
  = assert (M.covers mg' y b);
    if mo <= b && b <= mo + wz then tiled_uniq mg' mo y b;
    if b <> y && M.is_block mg' b then tiled_uniq mg' b y b

/// The infix header of a pointer the model resolves through one.
let infix_parts (mg: M.mheap) (b y: nat)
  : Lemma (requires M.resolve mg b == Some y /\ ~(M.is_block mg b))
          (ensures (let Some k = M.infix_hdr (mg.M.body b) in
                    k >= 2 /\ y == b - k /\ y < b /\ b < y + M.wz_of mg y /\ M.is_block mg y /\
                    M.tag_of mg y == M.closure_tag))
  = ()

/// A pointer the program held before the allocation resolves, in the
/// Fill's heap, to the same block, which keeps its header; it lies outside
/// the new block.  On model heaps: `mg` before, `mg'` after the allocation,
/// `m3` the Fill's heap.
#push-options "--z3rlimit 40"
let resolve_kept_m (mg mg' m3: M.mheap) (mo wz: nat) (vs: list M.value) (b y: nat)
  : Lemma (requires M.tiled mg' /\ M.is_block mg' mo /\ M.wz_of mg' mo == wz /\ L.length vs == wz /\
                    mg.M.size == mg'.M.size /\ m3.M.size == mg'.M.size /\
                    M.is_block mg y /\ y <> mo /\ mg'.M.hd y == mg.M.hd y /\
                    (forall (i: nat). i < M.wz_of mg y ==> M.field mg' y i == M.field mg y i) /\
                    R.agree (M.fill mg' mo vs) m3 /\ M.resolve mg b == Some y)
          (ensures M.resolve m3 b == Some y /\ m3.M.hd y == mg.M.hd y /\ (b < mo \/ b > mo + wz))
  = let mf = M.fill mg' mo vs in
    assert (M.is_block mg' y /\ M.wz_of mg' y == M.wz_of mg y /\ M.tag_of mg' y == M.tag_of mg y);
    assert (m3.M.hd y == mf.M.hd y);
    if M.is_block mg b then begin
      kept_cover mg' mo wz b y;
      assert (m3.M.hd b == mf.M.hd b)
    end
    else begin
      infix_parts mg b y;
      kept_cover mg' mo wz b y;
      assert (m3.M.hd b == mf.M.hd b);
      let i : nat = b - y - 1 in
      plus_back y b;
      assert (M.field mg' y i == M.field mg y i);
      agree_fw mf m3 y b;
      assert (mf.M.body b == mg'.M.body b)
    end
#pop-options

/// The Fill's heap has the allocator's walk and headers.
let g3_walk (g' g3: heap) (x: obj_addr) (wz: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g') /\ U64.v (wosize_of_object x g') == wz /\ no_infix_block g' /\
                    (forall (a: hp_addr). U64.v a < U64.v x \/ U64.v a >= U64.v x + 8 * wz ==> read_word g3 a == read_word g' a))
          (ensures objects zero_addr g3 == objects zero_addr g' /\ no_infix_block g3 /\
                   (forall (y: obj_addr). Seq.mem y (objects zero_addr g') ==> read_word g3 (hd_address y) == read_word g' (hd_address y)))
  = let sz (q: hp_addr)
      : Lemma (W.reaches g' zero_addr (U64.v q) ==> read_word g3 q == read_word g' q)
      = if W.reaches g' zero_addr (U64.v q) then walk_apart g' x q in
    FStar.Classical.forall_intro sz;
    W.walk_congr g' g3 zero_addr;
    let hd (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g') ==> read_word g3 (hd_address y) == read_word g' (hd_address y) /\
                                                    ~(is_infix y g3))
      = if Seq.mem y (objects zero_addr g') then begin
          W.objects_mem_iff g' zero_addr y;
          hd_address_spec y;
          sz (hd_address y);
          resolve_object_locality y g' g3
        end in
    FStar.Classical.forall_intro hd

/// The target of a pointer the Fill writes is one the page invariant
/// accepts, away from the new block.
let away_arith (x: obj_addr) (mo wz b: nat) (v: U64.t)
  : Lemma (requires pos mo + 8 == U64.v x /\ pos b + 8 == U64.v v /\ (b < mo \/ b > mo + wz))
          (ensures AT.away x wz v)
  = ()

let target_use (ph: I.phase) (st st': pstate) (g g3: heap) (y: nat)
  : Lemma (requires used (cabs g) y /\ (abs g3).M.hd y == (cabs g).M.hd y /\
                    pos y + 8 < heap_size /\ Seq.mem (obj_of y) (objects zero_addr g3) /\
                    MS.same_swept st.pm st'.pm /\
                    (ph == I.Sweeping ==> ~(M.col_of (cabs g) y == M.White /\ G.uw st.pm (pos y))))
          (ensures in_use (free_of ph st') g3 (obj_of y))
  = abs_is_block g3 y;
    abs_header g3 y;
    abs_blue g3 y;
    let oy = obj_of y in
    obj_of_v y;
    is_white_iff oy g3;
    MS.uw_same st.pm st'.pm (pos y);
    match ph with
    | I.Sweeping -> assert (MS.unswept_at st'.pm oy == G.uw st'.pm (pos y))
    | _ -> ()

#push-options "--z3rlimit 40"
let target_ok (ph: I.phase) (st st': pstate) (g g' g3: heap) (x: obj_addr) (mo wz: nat) (vs: list M.value)
    (v: U64.t) (b y: nat)
  : Lemma (requires M.tiled (cabs g') /\ M.is_block (cabs g') mo /\ M.wz_of (cabs g') mo == wz /\
                    L.length vs == wz /\ pos mo + 8 == U64.v x /\
                    used (cabs g) y /\ y <> mo /\ (cabs g').M.hd y == (cabs g).M.hd y /\
                    (forall (i: nat). i < M.wz_of (cabs g) y ==> M.field (cabs g') y i == M.field (cabs g) y i) /\
                    R.agree (M.fill (cabs g') mo vs) (abs g3) /\ M.resolve (cabs g) b == Some y /\
                    is_pointer v /\ pos b + 8 == U64.v v /\ b + 1 < msize /\ obj_of b == v /\
                    no_infix_block g3 /\ MS.same_swept st.pm st'.pm /\
                    (ph == I.Sweeping ==> ~(M.col_of (cabs g) y == M.White /\ G.uw st.pm (pos y))))
          (ensures I.field_ok_with (free_of ph st') g3 v /\ AT.away x wz v)
  = resolve_kept_m (cabs g) (cabs g') (abs g3) mo wz vs b y;
    ptr_resolve g3 b y;
    target_use ph st st' g g3 y;
    away_arith x mo wz b v
#pop-options

/// A field the Fill writes holds a value the page invariant accepts.
#push-options "--z3rlimit 40"
let inside_ok (ph: I.phase) (g: heap) (st: pstate) (wz: M.size_t) (tag: AT.tag_t) (g': heap) (st': pstate)
    (x: obj_addr) (vs: list M.value) (g3: heap) (i: nat) (a: hp_addr)
  : Lemma (requires fill_ctx ph g st wz tag g' st' x vs g3 /\
                    (forall (v: M.value). L.memP v vs ==> sound_b ph st g v) /\
                    U64.v a == U64.v x + 8 * i /\ i < wz /\
                    objects zero_addr g3 == objects zero_addr g' /\ no_infix_block g3)
          (ensures I.field_ok_with (free_of ph st') g3 (read_word g3 a) /\ AT.away x wz (read_word g3 a))
  = wf_after ph g st wz tag g' st' x;
    new_block ph g st wz tag g' st' x;
    abs_well_formed g';
    let mo = maddr x in
    field_val g' g3 x mo wz vs i a;
    let v = read_word g3 a in
    L.lemma_index_memP vs i;
    if is_pointer v then begin
      ptr_decode v;
      let b = ptr_b v in
      let y = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun y -> M.resolve (cabs g) b == Some y /\ used (cabs g) y /\
                          (ph == I.Sweeping ==> ~(M.col_of (cabs g) y == M.White /\ G.uw st.pm (pos y)))) in
      kept_block ph g st wz tag g' st' x y;
      alloc_basics ph g st wz tag g' st' x;
      target_ok ph st st' g g' g3 x mo wz vs v b y
    end
#pop-options

let fidx (x: obj_addr) (a: hp_addr) : nat = if U64.v a >= U64.v x then (U64.v a - U64.v x) / 8 else 0

let noscan_tag (x: obj_addr) (g': heap) (tag: AT.tag_t)
  : Lemma (requires tag_of_object x g' == tag) (ensures is_no_scan x g' <==> U64.v tag >= 251)
  = is_no_scan_spec x g';
    no_scan_tag_val ()

let ins_at (ph: I.phase) (g: heap) (st: pstate) (wz: M.size_t) (tag: AT.tag_t) (g': heap) (st': pstate)
    (x: obj_addr) (vs: list M.value) (g3: heap) (a: hp_addr)
  : Lemma (requires fill_ctx ph g st wz tag g' st' x vs g3 /\
                    (forall (v: M.value). L.memP v vs ==> sound_b ph st g v) /\
                    objects zero_addr g3 == objects zero_addr g' /\ no_infix_block g3 /\
                    U64.v x <= U64.v a /\ U64.v a < U64.v x + 8 * wz)
          (ensures I.field_ok_with (free_of ph st') g3 (read_word g3 a) /\ AT.away x wz (read_word g3 a))
  = field_index x wz a;
    inside_ok ph g st wz tag g' st' x vs g3 (fidx x a) a

/// The facts of the Fill's setting the word lemmas read.
let fill_basics (ph: I.phase) (g: heap) (st: pstate) (wz: M.size_t) (tag: AT.tag_t) (g': heap) (st': pstate)
    (x: obj_addr) (vs: list M.value) (g3: heap)
  : Lemma (requires fill_ctx ph g st wz tag g' st' x vs g3)
          (ensures prep g' g3 (maddr x) wz vs /\ pos (maddr x) + 8 == U64.v x /\
                   Seq.mem x (objects zero_addr g') /\ U64.v (wosize_of_object x g') == wz /\
                   no_infix_block g' /\ (is_no_scan x g' <==> U64.v tag >= 251))
  = wf_after ph g st wz tag g' st' x;
    new_block ph g st wz tag g' st' x;
    abs_well_formed g';
    alloc_basics ph g st wz tag g' st' x;
    noscan_tag x g' tag

let out_all (g' g3: heap) (x: obj_addr) (mo wz: nat) (vs: list M.value)
  : Lemma (requires prep g' g3 mo wz vs /\ pos mo + 8 == U64.v x /\ U64.v (wosize_of_object x g') == wz)
          (ensures forall (a: hp_addr). U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x g') * 8 ==>
                     read_word g3 a == read_word g' a)
  = let out (a: hp_addr)
      : Lemma (U64.v a < U64.v x \/ U64.v a >= U64.v x + wz * 8 ==> read_word g3 a == read_word g' a)
      = if U64.v a < U64.v x || U64.v a >= U64.v x + 8 * wz then outside_eq g' g3 x mo wz vs a in
    FStar.Classical.forall_intro out

let ins_all (ph: I.phase) (g: heap) (st: pstate) (wz: M.size_t) (tag: AT.tag_t) (g': heap) (st': pstate)
    (x: obj_addr) (vs: list M.value) (g3: heap)
  : Lemma (requires fill_ctx ph g st wz tag g' st' x vs g3 /\
                    (forall (v: M.value). L.memP v vs ==> sound_b ph st g v) /\
                    objects zero_addr g3 == objects zero_addr g' /\ no_infix_block g3 /\
                    U64.v (wosize_of_object x g') == wz)
          (ensures forall (a: hp_addr). U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 ==>
                     I.field_ok_with (free_of ph st') g3 (read_word g3 a) /\
                     AT.away x (U64.v (wosize_of_object x g')) (read_word g3 a))
  = let ins (a: hp_addr)
      : Lemma (U64.v x <= U64.v a /\ U64.v a < U64.v x + wz * 8 ==>
               I.field_ok_with (free_of ph st') g3 (read_word g3 a) /\ AT.away x wz (read_word g3 a))
      = if U64.v x <= U64.v a && U64.v a < U64.v x + wz * 8 then ins_at ph g st wz tag g' st' x vs g3 a in
    FStar.Classical.forall_intro ins

let fwa_intro (free: free_def) (g' g3: heap) (x: obj_addr)
  : Lemma (requires (forall (a: hp_addr). U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x g') * 8 ==>
                       read_word g3 a == read_word g' a) /\
                    (~(is_no_scan x g') ==>
                       (forall (a: hp_addr). U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 ==>
                          I.field_ok_with free g3 (read_word g3 a) /\
                          AT.away x (U64.v (wosize_of_object x g')) (read_word g3 a))))
          (ensures AT.fields_written_away free g' g3 x)
  = ()

let fill_written (ph: I.phase) (g: heap) (st: pstate) (wz: M.size_t) (tag: AT.tag_t) (g': heap) (st': pstate)
    (x: obj_addr) (vs: list M.value) (g3: heap)
  : Lemma (requires fill_ctx ph g st wz tag g' st' x vs g3 /\
                    (U64.v tag < 251 ==> (forall (v: M.value). L.memP v vs ==> sound_b ph st g v)))
          (ensures AT.fields_written_away (free_of ph st') g' g3 x)
  = fill_basics ph g st wz tag g' st' x vs g3;
    out_all g' g3 x (maddr x) wz vs;
    g3_walk g' g3 x wz;
    if not (is_no_scan x g') then ins_all ph g st wz tag g' st' x vs g3;
    fwa_intro (free_of ph st') g' g3 x

/// **The invariant after the Fill.**
let fill_inv (ph: I.phase) (g: heap) (st: pstate) (wz: M.size_t) (tag: AT.tag_t) (g': heap) (st': pstate)
    (x: obj_addr) (vs: list M.value) (g3: heap)
  : Lemma (requires fill_ctx ph g st wz tag g' st' x vs g3 /\
                    (U64.v tag < 251 ==> (forall (v: M.value). L.memP v vs ==> sound_b ph st g v)))
          (ensures MSA.inv_sw ph g3 st')
  = fill_written ph g st wz tag g' st' x vs g3;
    ok_alloc_elim ph g st wz tag g' st' x
