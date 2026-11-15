/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Witness - a non-trivial state of the allocator, built
/// ---------------------------------------------------------------------------
///
/// The vacuity rule (docs/pages-allocator-proof-plan.md §18): every theorem
/// with hypotheses about heaps needs a constructive witness, a state shown to
/// satisfy all its hypotheses, with at least one root, one reachable object,
/// one unreachable object, one pool page and one large run.
///
/// This module builds the shared base state, from the empty heap of pages,
/// through the allocator's interface in `Idle`, with the caller's field
/// writes:
///
///   1. B, a large object (`small_max` fields): a run of pages; fields 0;
///   2. A, a small object (one field): a pool page; its field points to B;
///   3. C, a small object (one field): field 0.
///
/// The roots are `[A]`.  So A is a root, B is reachable but not a root, and C
/// is unreachable (`w_graph`).  The state is in the `Idle` invariant
/// (`w_inv`), A's page is a pool page and B's the head of a run (`w_pages`).
/// It needs only that the heap has `pages_for (small_max + 1) + 2` pages
/// (`big_enough`).
///
/// The vacuity modules derive the witnesses of the page theorems from it:
/// `GC.Spec.Pages.Vacuity` (sequential collector and allocator) and
/// `GC.Impl.Pages.ParWitness` (parallel mark and sweep).

module GC.Spec.Pages.Witness

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Blocks
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module A = GC.Spec.Pages.Alloc
module Pool = GC.Spec.Pages.Pool
module PI = GC.Spec.Pages.PoolInit
module NR = GC.Spec.Pages.NewRun
module LG = GC.Spec.Pages.Large
module Init = GC.Spec.Pages.Init
module Cells = GC.Spec.Pages.Cells
module FLs = GC.Spec.FreeLists
module F = GC.Spec.Pages.Fill
module Graph = GC.Spec.Graph
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module DFS = GC.Spec.DFS
module Mark = GC.Spec.Mark
module Corr = GC.Spec.Correctness
module GP = GC.Spec.Pages.GcPillars
module GcC = GC.Spec.Pages.GcCorrect

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// What an allocation does to the kinds of pages
/// ---------------------------------------------------------------------------

let kind_of (st: pstate) (j: nat{j < n_pages}) : page_kind = (entry st.pm j).kind

/// The first free page.
let first_free (st: pstate) : nat = Pool.find_free st.pm 0

/// Taking a slot changes no page's kind; the slot is in the page at the
/// head of `avail[c]`.
let pop_kinds (clr: bool) (g: heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{Pool.small_wz wz c})
  : Lemma (let (_, st', o) = Pool.pop_as clr g st c wz in
           (forall (j: nat{j < n_pages}). kind_of st' j == kind_of st j) /\
           (o =!= 0UL ==>
              U64.v (Pool.avail_at st c) >= 1 /\ U64.v (Pool.avail_at st c) - 1 < n_pages /\
              (exists (k: nat). k < n_slots c /\ U64.v o == slot_obj (U64.v (Pool.avail_at st c) - 1) c k)))
  = let hd = Pool.avail_at st c in
    if hd = 0UL || U64.v hd - 1 >= n_pages then ()
    else begin
      let p : nat = U64.v hd - 1 in
      let e = entry st.pm p in
      let k = Pool.slot_of p c e.free_head in
      if k >= n_slots c || e.nfree = 0 then ()
      else begin
        PI.slot_fits p c k;
        let e' = { e with free_head = hdr g (slot_obj p c k); nfree = e.nfree - 1 } in
        let aux (j: nat{j < n_pages}) : Lemma (kind_of ({ st with pm = Seq.upd st.pm p e' }) j == kind_of st j)
          = ()
        in
        FStar.Classical.forall_intro aux
      end
    end

/// Taking a free page for class `c` changes that page's kind only, and puts
/// it at the head of `avail[c]`.
let acq_kinds (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (let st1 = Pool.acq_state st i c in
           kind_of st1 i == Pool c /\
           (forall (j: nat{j < n_pages}). j <> i ==> kind_of st1 j == kind_of st j) /\
           (c < Seq.length st.avail ==> Pool.avail_at st1 c == U64.uint_to_t (i + 1)) /\
           (c >= Seq.length st.avail ==> Pool.avail_at st1 c == 0UL))
  = ()

/// A small allocation changes the kind of at most one page, the first free
/// one, from `Free` to a pool page of the request's class.  Through the
/// empty `avail` list it takes that page, and the new object is in it.
let small_kinds (clr: bool) (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max})
  : Lemma (let (_, st', o) = Pool.small_alloc_as clr g st wz in
           let c = class_of (wz + 1) in
           (forall (j: nat{j < n_pages}).
              kind_of st' j == kind_of st j \/
              (j == first_free st /\ kind_of st j == Free /\ kind_of st' j == Pool c)) /\
           (Pool.avail_at st c == 0UL /\ o =!= 0UL ==>
              first_free st < n_pages /\ kind_of st' (first_free st) == Pool c /\
              (exists (k: nat). k < n_slots c /\ U64.v o == slot_obj (first_free st) c k)))
  = let c = class_of (wz + 1) in
    class_of_fits (wz + 1);
    Pool.small_wz_intro wz c;
    if Pool.avail_at st c <> 0UL then pop_kinds clr g st c wz
    else begin
      let i = Pool.find_free st.pm 0 in
      Pool.find_free_spec st.pm 0;
      if i >= n_pages then ()
      else begin
        let (g1, st1) = Pool.acquire g st i c in
        acq_kinds st i c;
        pop_kinds clr g1 st1 c wz
      end
    end

/// ---------------------------------------------------------------------------
/// The sizes
/// ---------------------------------------------------------------------------

/// B: one word more than the largest slot, so a large object.
let wzL : (n: nat{n < pow2 54}) =
  cls_bounds 0; FStar.Math.Lemmas.pow2_lt_compat 54 20; small_max

/// A and C: one field.
let wzS : (n: nat{n == 1 /\ n < pow2 54}) = assert_norm (1 < pow2 54); 1

/// The class of A and C.
let cA : (c: nat{c < n_cls}) = cls_bounds 0; class_of (wzS + 1)

/// The pages B's run takes.
let kL : pos = pages_for (wzL + 1)

/// Room for B's run and two more pages.
let big_enough : prop = kL + 2 <= n_pages

let sizes () : Lemma (wzL + 1 > small_max /\ wzL + 1 <= pow2 20 /\ wzL + 1 < pow2 54 /\
                     wzS + 1 <= small_max /\ small_max <= page_wsize)
  = cls_bounds 0;
    FStar.Math.Lemmas.pow2_lt_compat 54 20

/// ---------------------------------------------------------------------------
/// A large allocation on the empty heap of pages
/// ---------------------------------------------------------------------------

/// Where B's run goes.
let i0 : nat = NR.find_run Init.init_state.pm kL 0

/// The empty heap's large list is empty.
#push-options "--fuel 1"
let init_no_large (g: heap)
  : Lemma (Cells.walk g (Cells.large_head Init.init_state) heap_words == [] /\
           LG.split_fit g [] (wzL + 1) == None)
  = ()
#pop-options

/// It takes a new run of `kL` pages, at `i0`: `i0` is its head, every page
/// outside it is still free, and `avail` is unchanged.
#push-options "--z3rlimit 40"
let large_init (g: heap)
  : Lemma (requires big_enough)
          (ensures (let (_, st1, o) = A.alloc (Init.init_heap g) Init.init_state wzL in
                    i0 + kL <= n_pages /\ U64.v o == page_base i0 + 8 /\
                    kind_of st1 i0 == LargeHead kL /\
                    (forall (j: nat{j < n_pages}). (j < i0 \/ j >= i0 + kL) ==> kind_of st1 j == Free) /\
                    st1.avail == Init.init_state.avail))
  = sizes ();
    let g0 = Init.init_heap g in
    let st0 = Init.init_state in
    init_no_large g0;
    NR.find_run_spec st0.pm kL 0;
    assert (free_run st0.pm 0 kL);
    page_base_mono i0 (i0 + kL);
    pages_end_bound ();
    let st1 = NR.run_state st0 i0 kL (wzL + 1) in
    assert (A.alloc g0 st0 wzL == NR.new_run_as false g0 st0 i0 kL wzL);
    LG.obj_at_spec (page_base i0 + 8);
    let k (j: nat{j < n_pages})
      : Lemma (kind_of st1 j == (if j = i0 then LargeHead kL
                                 else if i0 < j && j < i0 + kL then LargeCont else kind_of st0 j))
      = ()
    in
    FStar.Classical.forall_intro k
#pop-options

/// ---------------------------------------------------------------------------
/// One allocation in `Idle`
/// ---------------------------------------------------------------------------

/// What a successful allocation gives: a new white object with tag 0
/// (`ohdr`), the invariant once its fields are written, and every other
/// live object kept.
let fresh (g: heap) (st: pstate) (wz: nat{wz < pow2 54}) (g': heap) (st': pstate) (o: U64.t) : prop =
  U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
  (let x : obj_addr = o in
   Seq.mem x (objects zero_addr g') /\ U64.v (wosize_of_object x g') == wz /\
   read_word g' (hd_address x) == ohdr wz /\
   ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
   (forall (g'': heap). fields_written g' g'' x ==> pages_ok g'' st' /\ well_formed_heap g'') /\
   others_unchanged g g')

let alloc_fresh (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ wz + 1 < pow2 54)
          (ensures (let (g', st', o) = PA.alloc I.Idle g st wz in
                    (o == 0UL ==> no_fit g st (wz + 1)) /\
                    (o =!= 0UL ==> fresh g st wz g' st' o)))
  = PA.alloc_idle g st wz;
    A.alloc_clears g st wz;
    let (g', st', o) = A.alloc g st wz in
    if o <> 0UL then hd_address_spec (o <: obj_addr)

/// A small allocation succeeds when a page is free.
let small_some (g: heap) (st: pstate) (wz: nat) (j: nat{j < n_pages})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ wz + 1 <= small_max /\ kind_of st j == Free)
          (ensures (let (_, _, o) = PA.alloc I.Idle g st wz in o =!= 0UL))
  = cls_bounds 0;
    FStar.Math.Lemmas.pow2_lt_compat 54 20;
    alloc_fresh g st wz

/// ---------------------------------------------------------------------------
/// Objects, through later steps
/// ---------------------------------------------------------------------------

/// `x` is a live object of `g`, white with tag 0, `n` fields, and its field
/// words read as `f` says.
let holds (g: heap) (x: obj_addr) (n: nat{n < pow2 54}) (f: hp_addr -> U64.t) : prop =
  Seq.mem x (objects zero_addr g) /\ read_word g (hd_address x) == ohdr n /\
  (forall (b: hp_addr). U64.v x <= U64.v b /\ U64.v b < U64.v x + n * 8 ==> read_word g b == f b)

let holds_facts (g: heap) (x: obj_addr) (n: nat{n < pow2 54}) (f: hp_addr -> U64.t)
  : Lemma (requires holds g x n f)
          (ensures U64.v (wosize_of_object x g) == n /\ is_white x g /\ ~(is_blue x g) /\
                   ~(is_infix x g) /\ ~(is_no_scan x g) /\ ~(is_closure x g) /\
                   tag_of_object x g == 0UL)
  = ohdr_spec n;
    wosize_of_object_spec x g;
    color_of_object_spec x g;
    is_white_iff x g;
    is_blue_iff x g;
    tag_of_object_spec x g;
    is_infix_spec x g;
    is_no_scan_spec x g;
    is_closure_spec x g;
    infix_tag_val ();
    no_scan_tag_val ();
    closure_tag_val ()

/// An allocation keeps it.
let keep_alloc (g g': heap) (x: obj_addr) (n: nat{n < pow2 54}) (f: hp_addr -> U64.t)
  : Lemma (requires holds g x n f /\ others_unchanged g g')
          (ensures holds g' x n f)
  = holds_facts g x n f

/// Writing the fields of another object keeps it.
let keep_write (g' g'': heap) (y: obj_addr) (x: obj_addr) (n: nat{n < pow2 54}) (f: hp_addr -> U64.t)
  : Lemma (requires holds g' x n f /\ F.fctx g' g'' y /\ y <> x)
          (ensures holds g'' x n f)
  = holds_facts g' x n f;
    F.obj_same g' g'' y x;
    F.other_apart g' y x;
    hd_address_spec x

/// The fields of `x`, from `g` to `g''`, keep everything else.
let fctx_of (g' g'': heap) (x: obj_addr)
  : Lemma (requires fields_written g' g'' x /\ Seq.mem x (objects zero_addr g'))
          (ensures F.fctx g' g'' x)
  = ()

/// ---------------------------------------------------------------------------
/// The steps
/// ---------------------------------------------------------------------------

let fst3 (t: heap & pstate & U64.t) : heap = let (a, _, _) = t in a
let snd3 (t: heap & pstate & U64.t) : pstate = let (_, b, _) = t in b
let thd3 (t: heap & pstate & U64.t) : U64.t = let (_, _, c) = t in c

let as_obj (o: U64.t) : obj_addr =
  if U64.v o >= 8 && U64.v o < heap_size && U64.v o % 8 = 0 then o else 8UL

let const (v: U64.t) : hp_addr -> U64.t = fun _ -> v

let s0 : pstate = Init.init_state

/// 1. B.
let stepB (g: heap) : GTot (heap & pstate & U64.t) = PA.alloc I.Idle (Init.init_heap g) s0 wzL
let oB (g: heap) : GTot obj_addr = as_obj (thd3 (stepB g))
let g1 (g: heap) : GTot heap = zeros (fst3 (stepB g)) (U64.v (oB g)) wzL
let s1 (g: heap) : GTot pstate = snd3 (stepB g)

/// 2. A, whose field points to B.
let stepA (g: heap) : GTot (heap & pstate & U64.t) = PA.alloc I.Idle (g1 g) (s1 g) wzS
let oA (g: heap) : GTot obj_addr = as_obj (thd3 (stepA g))
let g2 (g: heap) : GTot heap = wr (fst3 (stepA g)) (U64.v (oA g)) (oB g)
let s2 (g: heap) : GTot pstate = snd3 (stepA g)

/// 3. C.
let stepC (g: heap) : GTot (heap & pstate & U64.t) = PA.alloc I.Idle (g2 g) (s2 g) wzS
let oC (g: heap) : GTot obj_addr = as_obj (thd3 (stepC g))

/// **The witness**: the heap, the allocator's state, and the roots.
let w_heap (g: heap) : GTot heap = zeros (fst3 (stepC g)) (U64.v (oC g)) wzS
let w_state (g: heap) : GTot pstate = snd3 (stepC g)
let w_roots (g: heap) : GTot (Seq.seq obj_addr) = Seq.create 1 (oA g)

/// The cleared fields of a new object are written (`fields_written`).
let zeros_written (g': heap) (x: obj_addr) (n: nat{n < pow2 54})
  : Lemma (requires Seq.mem x (objects zero_addr g') /\ read_word g' (hd_address x) == ohdr n)
          (ensures fields_written g' (zeros g' (U64.v x) n) x /\
                   holds (zeros g' (U64.v x) n) x n (const 0UL) /\
                   F.fctx g' (zeros g' (U64.v x) n) x)
  = holds_facts g' x n (fun b -> read_word g' b);
    F.cleared_written g' x;
    hd_address_spec x;
    zeros_read g' (U64.v x) n (hd_address x);
    let g'' = zeros g' (U64.v x) n in
    FStar.Classical.forall_intro (zeros_read g' (U64.v x) n);
    F.obj_same g' g'' x x

/// Step 1: B is allocated at the head of a new run; its fields are cleared.
#push-options "--z3rlimit 40"
let step1 (g: heap)
  : Lemma (requires big_enough)
          (ensures (let (g1', st1, o) = stepB g in
                    o =!= 0UL /\ fresh (Init.init_heap g) s0 wzL g1' st1 o /\
                    U64.v (oB g) == page_base i0 + 8 /\ i0 + kL <= n_pages /\
                    kind_of st1 i0 == LargeHead kL /\
                    (forall (j: nat{j < n_pages}). (j < i0 \/ j >= i0 + kL) ==> kind_of st1 j == Free) /\
                    st1.avail == s0.avail /\
                    fields_written g1' (g1 g) (oB g) /\
                    holds (g1 g) (oB g) wzL (const 0UL) /\
                    PA.inv I.Idle (g1 g) (s1 g)))
  = let g0 = Init.init_heap g in
    sizes ();
    A.init_alloc_pre g;
    PA.alloc_idle g0 s0 wzL;
    A.init_alloc_large_succeeds g wzL;
    alloc_fresh g0 s0 wzL;
    large_init g;
    let (g1', st1, o) = stepB g in
    assert (oB g == (o <: obj_addr));
    zeros_written g1' (oB g) wzL;
    GC.Spec.Pages.Alloc.init_alloc_pre g;
    GC.Spec.Pages.GcCorrect.reach_inv (GC.Spec.Pages.GcCorrect.Start g);
    GC.Spec.Pages.GcCorrect.alloc_keeps g0 s0 wzL (g1 g)
#pop-options

/// Writing a pointer to `y`, a live object, into the one field of `x`.
#push-options "--z3rlimit 40"
let write_ptr (g': heap) (x y: obj_addr) (ny: nat{ny < pow2 54})
  : Lemma (requires Seq.mem x (objects zero_addr g') /\ read_word g' (hd_address x) == ohdr wzS /\
                    holds g' y ny (const 0UL) /\ x <> y)
          (ensures (let g'' = wr g' (U64.v x) y in
                    fields_written g' g'' x /\ F.fctx g' g'' x /\
                    holds g'' x wzS (const y) /\ holds g'' y ny (const 0UL)))
  = let g'' = wr g' (U64.v x) y in
    holds_facts g' x wzS (fun b -> read_word g' b);
    FStar.Classical.forall_intro (wr_read g' (U64.v x) y);
    assert (F.fctx g' g'' x);
    keep_write g' g'' x y ny (const 0UL);
    holds_facts g'' y ny (const 0UL);
    resolve_non_infix y g'';
    infix_addr_wf_intro g'' (objects zero_addr g'') y;
    assert (field_ok g'' y);
    F.obj_same g' g'' x x;
    hd_address_spec x
#pop-options

/// A small allocation through the empty `avail` lists, as the allocator's
/// `small_alloc_as`.
let alloc_small_is (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ wz + 1 <= small_max)
          (ensures PA.alloc I.Idle g st wz == Pool.small_alloc_as false g st wz)
  = PA.alloc_idle g st wz;
    cls_bounds 0;
    FStar.Math.Lemmas.pow2_lt_compat 54 20

/// A page that is free in the first state.
let free1 : nat = if i0 > 0 then 0 else kL

/// Step 2: A is allocated in the first free page, which becomes a pool page;
/// its field points to B.
#push-options "--z3rlimit 40"
let step2 (g: heap)
  : Lemma (requires big_enough)
          (ensures (let (g2', st2, o) = stepA g in
                    let c = cA in
                    let ia = first_free (s1 g) in
                    o =!= 0UL /\ fresh (g1 g) (s1 g) wzS g2' st2 o /\ oA g <> oB g /\
                    ia < n_pages /\ ia <> i0 /\ kind_of (s1 g) ia == Free /\
                    kind_of st2 ia == Pool c /\
                    (exists (k: nat). k < n_slots c /\ U64.v (oA g) == slot_obj ia c k) /\
                    (forall (j: nat{j < n_pages}). j <> ia ==> kind_of st2 j == kind_of (s1 g) j) /\
                    fields_written g2' (g2 g) (oA g) /\
                    holds (g2 g) (oA g) wzS (const (oB g)) /\
                    holds (g2 g) (oB g) wzL (const 0UL) /\
                    PA.inv I.Idle (g2 g) (s2 g)))
  = step1 g;
    sizes ();
    let c = cA in
    let (g1', st1, ob) = stepB g in
    assert (kind_of st1 free1 == Free);
    small_some (g1 g) (s1 g) wzS free1;
    alloc_fresh (g1 g) (s1 g) wzS;
    alloc_small_is (g1 g) (s1 g) wzS;
    small_kinds false (g1 g) (s1 g) wzS;
    assert (Pool.avail_at (s1 g) c == 0UL);
    Pool.find_free_spec (s1 g).pm 0;
    let (g2', st2, o) = stepA g in
    assert (oA g == (o <: obj_addr));
    keep_alloc (g1 g) g2' (oB g) wzL (const 0UL);
    holds_facts (g1 g) (oB g) wzL (const 0UL);
    write_ptr g2' (oA g) (oB g) wzL;
    GC.Spec.Pages.GcCorrect.alloc_keeps (g1 g) (s1 g) wzS (g2 g)
#pop-options

/// Another page that is free in the first state.
let free1' : nat = if i0 >= 2 then 1 else kL + 1

/// A page still free after step 2.
let free2 (g: heap) : GTot nat = if first_free (s1 g) = free1 then free1' else free1

/// Step 3: C is allocated; its field is cleared.  A and B are kept, and so
/// are the kinds of their pages.
#push-options "--z3rlimit 40"
let step3 (g: heap)
  : Lemma (requires big_enough)
          (ensures (let (g3', st3, o) = stepC g in
                    let ia = first_free (s1 g) in
                    o =!= 0UL /\ fresh (g2 g) (s2 g) wzS g3' st3 o /\
                    fields_written g3' (w_heap g) (oC g) /\
                    oC g <> oA g /\ oC g <> oB g /\ oA g <> oB g /\
                    ia < n_pages /\ kind_of st3 ia == Pool cA /\
                    (exists (k: nat). k < n_slots cA /\ U64.v (oA g) == slot_obj ia cA k) /\
                    U64.v (oB g) == page_base i0 + 8 /\ i0 + kL <= n_pages /\
                    kind_of st3 i0 == LargeHead kL /\
                    holds (w_heap g) (oA g) wzS (const (oB g)) /\
                    holds (w_heap g) (oB g) wzL (const 0UL) /\
                    holds (w_heap g) (oC g) wzS (const 0UL) /\
                    PA.inv I.Idle (w_heap g) (w_state g)))
  = step1 g;
    step2 g;
    sizes ();
    let ia = first_free (s1 g) in
    assert (kind_of (s2 g) (free2 g) == Free);
    small_some (g2 g) (s2 g) wzS (free2 g);
    alloc_fresh (g2 g) (s2 g) wzS;
    alloc_small_is (g2 g) (s2 g) wzS;
    small_kinds false (g2 g) (s2 g) wzS;
    let (g3', st3, o) = stepC g in
    assert (oC g == (o <: obj_addr));
    keep_alloc (g2 g) g3' (oA g) wzS (const (oB g));
    keep_alloc (g2 g) g3' (oB g) wzL (const 0UL);
    holds_facts (g2 g) (oA g) wzS (const (oB g));
    holds_facts (g2 g) (oB g) wzL (const 0UL);
    zeros_written g3' (oC g) wzS;
    keep_write g3' (w_heap g) (oC g) (oA g) wzS (const (oB g));
    keep_write g3' (w_heap g) (oC g) (oB g) wzL (const 0UL);
    GC.Spec.Pages.GcCorrect.alloc_keeps (g2 g) (s2 g) wzS (w_heap g)
#pop-options

/// ---------------------------------------------------------------------------
/// The graph: A is a root, B is reachable through A, C is not reachable
/// ---------------------------------------------------------------------------

/// Field `i` of `x` reads as `holds` says.
let holds_field (g: heap) (x: obj_addr) (n: nat{n < pow2 54}) (f: hp_addr -> U64.t) (i: U64.t{U64.v i >= 1})
  : Lemma (requires holds g x n f /\ well_formed_heap g /\ U64.v i <= n)
          (ensures (let a = U64.v x + (U64.v i - 1) * 8 in
                    a < heap_size /\ a % 8 == 0 /\
                    HeapGraph.get_field g x i == f (U64.uint_to_t a)))
  = holds_facts g x n f;
    wf_object_bound g x;
    hd_address_spec x;
    HeapGraph.get_field_addr_eq g x i

/// An object whose fields are all 0 has no pointer field.
#push-options "--fuel 1"
let rec no_pointers (g: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires forall (j: U64.t{U64.v j >= 1}). U64.v i <= U64.v j /\ U64.v j <= U64.v ws ==>
                      HeapGraph.get_field g x j == 0UL)
          (ensures HeapGraph.get_pointer_fields_aux g x i ws == Seq.empty)
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else if U64.v i < U64.v ws then no_pointers g x (U64.add i 1UL) ws
#pop-options

let gr (g: heap) : GTot Graph.graph_state = HeapModel.create_graph (w_heap g)

/// A's one successor is B; B has none.
#push-options "--fuel 1 --z3rlimit 40"
let w_succ (g: heap)
  : Lemma (requires big_enough)
          (ensures Seq.equal (Graph.successors (gr g) (oA g)) (Seq.cons #Graph.vertex_id (oB g) Seq.empty) /\
                   Seq.equal (Graph.successors (gr g) (oB g)) Seq.empty)
  = step3 g;
    let h = w_heap g in
    let objs = objects zero_addr h in
    HeapModel.objects_is_vertex_set h;
    HeapGraph.successors_eq_pointer_fields h objs (oA g);
    HeapGraph.successors_eq_pointer_fields h objs (oB g);
    holds_facts h (oA g) wzS (const (oB g));
    holds_facts h (oB g) wzL (const 0UL);
    Mark.wf_implies_object_fits h (oA g);
    Mark.wf_implies_object_fits h (oB g);
    holds_field h (oA g) wzS (const (oB g)) 1UL;
    resolve_non_infix (oB g) h;
    let zero (j: U64.t{U64.v j >= 1})
      : Lemma (1 <= U64.v j /\ U64.v j <= wzL ==> HeapGraph.get_field h (oB g) j == 0UL)
      = if U64.v j <= wzL then holds_field h (oB g) wzL (const 0UL) j
    in
    FStar.Classical.forall_intro zero;
    no_pointers h (oB g) 1UL (U64.uint_to_t wzL)
#pop-options

/// In a graph where `a`'s one successor is `b` and `b` has none, every
/// vertex reachable from `a` is `a` or `b`.
#push-options "--fuel 1"
let rec reach_two (gv: Graph.graph_state) (a: Graph.vertex_id{Graph.mem_graph_vertex gv a})
                  (b: Graph.vertex_id) (x: Graph.vertex_id{Graph.mem_graph_vertex gv x})
                  (r: Graph.reach gv a x)
  : Lemma (requires Seq.equal (Graph.successors gv a) (Seq.cons b Seq.empty) /\
                    Seq.equal (Graph.successors gv b) Seq.empty)
          (ensures x == a \/ x == b)
          (decreases r)
  = match r with
    | Graph.ReachRefl _ -> ()
    | Graph.ReachTrans _ y z r' ->
      reach_two gv a b y r';
      Graph.edge_mem_successors gv y z;
      Seq.mem_cons b (Seq.empty #Graph.vertex_id)
#pop-options

#push-options "--fuel 2"
let coerce_one (a: obj_addr)
  : Lemma (HeapGraph.coerce_to_vertex_list (Seq.create 1 a) == Seq.create 1 a /\
           Graph.is_vertex_set (Seq.create 1 a) /\
           (forall (x: Graph.vertex_id). Seq.mem x (Seq.create #Graph.vertex_id 1 a) <==> x == a) /\
           (forall (x: obj_addr). Seq.mem x (Seq.create #obj_addr 1 a) <==> x == a))
  = let s = Seq.create #obj_addr 1 a in
    Seq.lemma_eq_elim (Seq.tail s) Seq.empty;
    Seq.lemma_eq_elim (Seq.cons a (Seq.empty #Graph.vertex_id)) (Seq.create #Graph.vertex_id 1 a);
    Graph.is_vertex_set_singleton a;
    Seq.mem_cons a (Seq.empty #Graph.vertex_id);
    Seq.lemma_eq_elim (Seq.cons a (Seq.empty #obj_addr)) s;
    Seq.mem_cons a (Seq.empty #obj_addr)
#pop-options

/// **The graph of the witness**: `graph_pre` holds of the roots `[A]`; A and
/// B are reachable, B is not a root, C is not reachable.
#push-options "--z3rlimit 40"
let w_graph (g: heap)
  : Lemma (requires big_enough)
          (ensures (let h = w_heap g in
                    let rs = w_roots g in
                    GP.graph_pre h rs /\
                    Seq.mem (oA g) rs /\ ~(Seq.mem (oB g) rs) /\
                    Corr.heap_reachable h rs (oA g) /\ Corr.heap_reachable h rs (oB g) /\
                    ~(Corr.heap_reachable h rs (oC g))))
  = step3 g;
    w_succ g;
    let h = w_heap g in
    let gv = gr g in
    let a = oA g in
    let b = oB g in
    let c = oC g in
    Mark.create_graph_wf_from_heap h;
    HeapModel.graph_vertices_mem h a;
    HeapModel.graph_vertices_mem h b;
    HeapModel.graph_vertices_mem h c;
    coerce_one a;
    let rs' = HeapGraph.coerce_to_vertex_list (w_roots g) in
    assert (Graph.subset_vertices rs' gv.Graph.vertices);
    DFS.reachable_set_correct gv rs';
    let r0 : Graph.reach gv a a = Graph.ReachRefl a in
    Seq.mem_cons b (Seq.empty #Graph.vertex_id);
    Graph.successors_mem_edge gv a b;
    let r1 : Graph.reach gv a b = Graph.ReachTrans a a b r0 in
    FStar.Classical.exists_intro (fun (_: Graph.reach gv a a) -> True) r0;
    FStar.Classical.exists_intro (fun (_: Graph.reach gv a b) -> True) r1;
    let not_c () : Lemma (~(Seq.mem c (DFS.reachable_set gv rs')))
      = let aux (r: Graph.vertex_id{Graph.mem_graph_vertex gv r})
          : Lemma (~(Seq.mem r rs' /\ Graph.reachable gv r c))
          = if Seq.mem r rs' then begin
              assert (r == a);
              let none (p: Graph.reach gv a c) : Lemma False = reach_two gv a b c p in
              FStar.Classical.forall_intro none
            end
        in
        FStar.Classical.forall_intro aux
    in
    not_c ();
    assert (Seq.mem a rs');
    assert (Graph.reachable gv a a);
    assert (Seq.mem a (DFS.reachable_set gv rs'));
    assert (Graph.reachable gv a b);
    assert (Seq.mem b (DFS.reachable_set gv rs'))
#pop-options

/// ---------------------------------------------------------------------------
/// The witness, summed up
/// ---------------------------------------------------------------------------

/// **It is a state of the cycle**: the empty heap of pages, then three
/// allocations through the interface, each followed by the caller's writes.
let w_reach (g: heap) (_: squash big_enough) : GTot (GcC.reach (w_heap g) (w_state g)) =
  step1 g;
  step2 g;
  step3 g;
  let r1 : GcC.reach (g1 g) (s1 g) = GcC.Alloc (GcC.Start g) wzL (g1 g) () in
  let r2 : GcC.reach (g2 g) (s2 g) = GcC.Alloc r1 wzS (g2 g) () in
  GcC.Alloc r2 wzS (w_heap g) ()

/// **What the witness has**: the `Idle` invariant; the roots `[A]`, live and
/// with `graph_pre`; A a root in a pool page; B in the first page of a run,
/// reachable and not a root; C unreachable; three distinct live objects.
let w_ok (g: heap)
  : Lemma (requires big_enough)
          (ensures (let h = w_heap g in
                    let st = w_state g in
                    let rs = w_roots g in
                    PA.inv I.Idle h st /\
                    (forall (r: obj_addr). Seq.mem r rs ==> Seq.mem r (objects zero_addr h) /\ ~(is_blue r h)) /\
                    GP.graph_pre h rs /\
                    Seq.mem (oA g) rs /\ ~(Seq.mem (oB g) rs) /\
                    Corr.heap_reachable h rs (oA g) /\ Corr.heap_reachable h rs (oB g) /\
                    ~(Corr.heap_reachable h rs (oC g)) /\
                    Seq.mem (oC g) (objects zero_addr h) /\ ~(is_blue (oC g) h) /\
                    Seq.mem (oB g) (objects zero_addr h) /\ ~(is_blue (oB g) h) /\
                    oA g <> oB g /\ oA g <> oC g /\ oB g <> oC g /\
                    (exists (i: nat{i < n_pages}). kind_of st i == Pool cA /\
                       page_base i <= U64.v (oA g) - 8 /\ U64.v (oA g) - 8 < page_base (i + 1)) /\
                    i0 < n_pages /\ kind_of st i0 == LargeHead kL /\ U64.v (oB g) - 8 == page_base i0))
  = step3 g;
    w_graph g;
    coerce_one (oA g);
    let h = w_heap g in
    holds_facts h (oA g) wzS (const (oB g));
    holds_facts h (oB g) wzL (const 0UL);
    holds_facts h (oC g) wzS (const 0UL);
    let ia = first_free (s1 g) in
    eliminate exists (k: nat). k < n_slots cA /\ U64.v (oA g) == slot_obj ia cA k
    with begin
      slots_fill_page ia cA;
      FStar.Math.Lemmas.lemma_mult_lt_right (cls cA * 8) k (n_slots cA);
      FStar.Math.Lemmas.paren_mul_right k (cls cA) 8;
      FStar.Math.Lemmas.paren_mul_right (n_slots cA) (cls cA) 8
    end
