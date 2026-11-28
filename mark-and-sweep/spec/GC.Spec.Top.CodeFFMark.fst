/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeFFMark - the first-fit mark, linked to akhil's Pulse mark
/// ---------------------------------------------------------------------------
///
/// Design doc §18, plan step 1 (first-fit mark and barrier).  The glue
/// `GC.Impl.FFGen` holds akhil's mark cache (`GC.Gen.Impl.mark_state`) at the
/// model's scan (`CodeFFGen.spof`).  This module:
///   - L8, a slice: akhil's `MarkSlice.mark_slice` ends `S.mark_steps` away;
///     each of his moves is a move of the byte mark (`ByteMark.bmove`) that
///     the model allows, so the slice is the event `ESlice mvs` for the moves
///     `slice_mvs` (none: no event).  The grey move's field resolves: the
///     block being scanned is live, and the live set is closed (the run's
///     marking invariant, `StepMark.minv_of`);
///   - the hand-over: when the slice returns that marking is over, the model
///     has nothing grey and nothing being scanned;
///   - L7, the start: akhil's root darkening depends only on which words are
///     roots (`darkened_mem`), so `start_cycle` on any array with the members
///     of the model's start words is `EStart`; the roots are valid for it,
///     and idle the stop-the-world shape holds of the empty nursery;
///   - the mark cache across the events the glue performs without mark code:
///     an allocation while marking (blocks kept, the new one black), its
///     Fill (headers kept), any change outside marking.

module GC.Spec.Top.CodeFFMark

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.Run
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module S = GC.Spec.MarkPhase.Slice
module MM = GC.Spec.MarkPhase.Mutator
module HG = GC.Spec.HeapGraph
module MS = GC.Gen.MarkState
module MV = GC.Spec.Top.MarkMoves
module BM = GC.Spec.Top.ByteMark
module BB = GC.Spec.Top.ByteBarrier
module SMk = GC.Spec.Top.StepMark
module RI = GC.Spec.Top.RInv
module FAl = GC.Spec.Top.FFAlloc
module CF = GC.Spec.Top.CodeFF
module CR = GC.Spec.Top.CodeRun
module G = GC.Spec.Top.CodeFFGen
module IDs = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Blocks, read both ways
/// ---------------------------------------------------------------------------

/// An object of the walk is the model block at `maddr x`.
let blk (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g))
          (ensures (let o = maddr x in
                    M.is_block (cabs g) o /\ pos o + 8 < heap_size /\ obj_of o == x /\
                    U64.v (hd_address x) >= base /\
                    M.col_of (cabs g) o == abs_col (color_of_object x g) /\
                    (is_no_scan x g <==> not (M.scannable (M.tag_of (cabs g) o))) /\
                    U64.v (wosize_of_object x g) == M.wz_of (cabs g) o))
  = obj_maddr g x;
    let o = maddr x in
    abs_header g o;
    BM.noscan_iff g o;
    hd_address_spec x

/// A block's object is on the walk, its colour read from its header.
let blk_obj (g: heap) (o: nat)
  : Lemma (requires M.is_block (cabs g) o)
          (ensures pos o + 8 < heap_size /\ Seq.mem (obj_of o) (objects zero_addr g) /\ maddr (obj_of o) == o /\
                   M.col_of (cabs g) o == abs_col (color_of_object (obj_of o) g))
  = abs_is_block g o;
    abs_header g o;
    maddr_obj o

/// Grey, both ways.
let grey_iff (g: heap) (x: obj_addr) : Lemma (is_gray x g <==> abs_col (color_of_object x g) == M.Grey)
  = is_gray_iff x g

/// The scan as akhil's position: none has no block; a block's has it.
let spof_some (g: heap) (o i: nat)
  : Lemma (requires M.is_block (cabs g) o)
          (ensures pos o + 8 < heap_size /\ (G.spof (Some (o, i))).MP.cur == obj_of o /\
                   (G.spof (Some (o, i))).MP.fld == i + 1 /\ (G.spof (Some (o, i))).MP.cur <> 0UL)
  = abs_is_block g o

/// What the marking invariant says of the scan, on the byte heap.
let scan_blk (g: heap) (m: M.mheap) (sc: T.scan) (s a: nat -> prop)
  : Lemma (requires brepr m g /\ MV.minv m sc s a)
          (ensures (match sc with
                    | Some (o, i) -> M.is_block (cabs g) o /\ i <= M.wz_of (cabs g) o /\ pos o + 8 < heap_size /\
                                     (G.spof sc).MP.cur == obj_of o /\ (G.spof sc).MP.fld == i + 1 /\
                                     (G.spof sc).MP.cur <> 0UL
                    | None -> G.spof sc == MP.scan_none))
  = match sc with
    | Some (o, i) -> spof_some g o i
    | None -> ()

/// Distinct blocks, distinct objects.
let obj_inj (o1 o2: nat)
  : Lemma (requires pos o1 + 8 < heap_size /\ pos o2 + 8 < heap_size /\ obj_of o1 == obj_of o2) (ensures o1 == o2)
  = ()

/// ---------------------------------------------------------------------------
/// The bytes below the heap stay
/// ---------------------------------------------------------------------------

let low_grey (g: heap) (x: obj_addr)
  : Lemma (requires U64.v (hd_address x) >= base) (ensures low (makeGray x g) == low g)
  = makeGray_spec x g;
    GC.Spec.Top.FFReplay.low_write g (hd_address x) (colorHeader (read_word g (hd_address x)) GC.Lib.Header.Gray)

let low_black (g: heap) (x: obj_addr)
  : Lemma (requires U64.v (hd_address x) >= base) (ensures low (makeBlack x g) == low g)
  = makeBlack_spec x g;
    GC.Spec.Top.FFReplay.low_write g (hd_address x) (colorHeader (read_word g (hd_address x)) GC.Lib.Header.Black)

let low_darken (g: heap) (w: U64.t) : Lemma (low (MM.darken g w) == low g)
  = if is_pointer w &&
       Seq.mem (resolve_object (w <: obj_addr) g) (objects zero_addr g) &&
       is_white (resolve_object (w <: obj_addr) g) g
    then begin
      let t = resolve_object (w <: obj_addr) g in
      obj_maddr g t;
      hd_address_spec t;
      low_grey g t
    end

/// ---------------------------------------------------------------------------
/// L8: one of akhil's moves is a move of the byte mark the model allows
/// ---------------------------------------------------------------------------

let good_mv (g: heap) (m: M.mheap) (sc: T.scan) (h: heap) (q: MP.scan_pos) (mv: T.move) : prop =
  T.move_ok m sc mv /\ BM.bmove g sc mv == (h, T.move_scan sc mv) /\ G.spof (T.move_scan sc mv) == q /\
  low h == low g

let pre (g: heap) (m: M.mheap) (sc: T.scan) (s a: nat -> prop) : prop = brepr m g /\ MV.minv m sc s a

/// **Starting a block.**
#push-options "--z3rlimit 40"
let begin_case (g: heap) (m: M.mheap) (sc: T.scan) (s a: nat -> prop) (h: heap) (q: MP.scan_pos) (x: obj_addr)
  : Lemma (requires pre g m sc s a /\ (G.spof sc).MP.cur == 0UL /\ S.scan_target g x /\ h == g /\
                    q == { MP.cur = x; MP.fld = 1 })
          (ensures good_mv g m sc h q (T.MBegin (maddr x)))
  = scan_blk g m sc s a;
    blk g x;
    grey_iff g x;
    let o = maddr x in
    MV.move_heq m (cabs g) sc (T.MBegin o);
    spof_some g o 0
#pop-options

/// The block being scanned resolves its fields.
let scan_ok_of (g: heap) (m: M.mheap) (o i: nat) (s a: nat -> prop)
  : Lemma (requires pre g m (Some (o, i)) s a) (ensures BM.scan_ok (cabs g) o)
  = assert (T.union s a o);
    assert (BM.scan_ok m o);
    BM.scan_ok_heq m (cabs g) o

/// **Scanning the next field.**
#push-options "--z3rlimit 40"
let grey_case (g: heap) (m: M.mheap) (sc: T.scan) (s a: nat -> prop) (h: heap) (q: MP.scan_pos) (x: obj_addr)
  : Lemma (requires pre g m sc s a /\ x == (G.spof sc).MP.cur /\ S.scan_target g x /\
                    1 <= (G.spof sc).MP.fld /\ (G.spof sc).MP.fld <= U64.v (wosize_of_object x g) /\
                    h == S.scan_field g x (U64.uint_to_t (G.spof sc).MP.fld) /\
                    q == { G.spof sc with MP.fld = (G.spof sc).MP.fld + 1 })
          (ensures good_mv g m sc h q T.MGrey)
  = scan_blk g m sc s a;
    match sc with
    | None -> ()
    | Some (o, i) ->
      blk g x;
      maddr_obj o;
      grey_iff g x;
      MV.move_heq m (cabs g) sc T.MGrey;
      scan_ok_of g m o i s a;
      BM.get_field_word g o i;
      BM.darken_old_model g o i;
      low_darken g (word g (o + 1 + i));
      spof_some g o (i + 1)
#pop-options

/// **Blackening a block.**  The model allows it ...
#push-options "--z3rlimit 40"
let black_allowed (g: heap) (sc: T.scan) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ is_gray x g /\ MP.all_scanned g (G.spof sc) x /\
                    (match sc with
                     | Some (c, j) -> M.is_block (cabs g) c /\ pos c + 8 < heap_size /\
                                      (G.spof sc).MP.cur == obj_of c /\ (G.spof sc).MP.fld == j + 1
                     | None -> G.spof sc == MP.scan_none))
          (ensures T.move_ok (cabs g) sc (T.MBlack (maddr x)))
  = blk g x;
    grey_iff g x;
    let o = maddr x in
    match sc with
    | None -> ()
    | Some (c, j) -> if c = o then () else (if obj_of c = obj_of o then obj_inj c o)
#pop-options

/// ... the byte mark blackens it, and the position is akhil's.
#push-options "--z3rlimit 40"
let black_moved (g: heap) (sc: T.scan) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\
                    (match sc with
                     | Some (c, j) -> M.is_block (cabs g) c /\ pos c + 8 < heap_size /\
                                      (G.spof sc).MP.cur == obj_of c /\ (G.spof sc).MP.fld == j + 1
                     | None -> G.spof sc == MP.scan_none))
          (ensures BM.bmove g sc (T.MBlack (maddr x)) == (makeBlack x g, T.move_scan sc (T.MBlack (maddr x))) /\
                   G.spof (T.move_scan sc (T.MBlack (maddr x))) == MP.blackened_pos (G.spof sc) x /\
                   low (makeBlack x g) == low g)
  = blk g x;
    low_black g x;
    let o = maddr x in
    match sc with
    | None -> ()
    | Some (c, j) -> if c = o then () else (if obj_of c = obj_of o then obj_inj c o)
#pop-options

let black_case (g: heap) (m: M.mheap) (sc: T.scan) (s a: nat -> prop) (h: heap) (q: MP.scan_pos) (x: obj_addr)
  : Lemma (requires pre g m sc s a /\ Seq.mem x (objects zero_addr g) /\ is_gray x g /\
                    MP.all_scanned g (G.spof sc) x /\ h == makeBlack x g /\ q == MP.blackened_pos (G.spof sc) x)
          (ensures good_mv g m sc h q (T.MBlack (maddr x)))
  = scan_blk g m sc s a;
    MV.move_heq m (cabs g) sc (T.MBlack (maddr x));
    black_allowed g sc x;
    black_moved g sc x

/// **Any move.**
let one_move (g: heap) (m: M.mheap) (sc: T.scan) (s a: nat -> prop) (h: heap) (q: MP.scan_pos)
  : Lemma (requires pre g m sc s a /\ S.mark_move g (G.spof sc) h q)
          (ensures exists (mv: T.move). good_mv g m sc h q mv)
  = let sp = G.spof sc in
    let fb (x: obj_addr)
      : Lemma (requires sp.MP.cur == 0UL /\ S.scan_target g x /\ h == g /\ q == { MP.cur = x; MP.fld = 1 })
              (ensures exists (mv: T.move). good_mv g m sc h q mv)
      = begin_case g m sc s a h q x in
    let fg (x: obj_addr)
      : Lemma (requires x == sp.MP.cur /\ S.scan_target g x /\ 1 <= sp.MP.fld /\
                        sp.MP.fld <= U64.v (wosize_of_object x g) /\
                        h == S.scan_field g x (U64.uint_to_t sp.MP.fld) /\ q == { sp with MP.fld = sp.MP.fld + 1 })
              (ensures exists (mv: T.move). good_mv g m sc h q mv)
      = grey_case g m sc s a h q x in
    let fk (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g) /\ is_gray x g /\ MP.all_scanned g sp x /\
                        h == makeBlack x g /\ q == MP.blackened_pos sp x)
              (ensures exists (mv: T.move). good_mv g m sc h q mv)
      = black_case g m sc s a h q x in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fb);
    FStar.Classical.forall_intro (FStar.Classical.move_requires fg);
    FStar.Classical.forall_intro (FStar.Classical.move_requires fk)

/// ---------------------------------------------------------------------------
/// L8: a run of akhil's moves is a list of moves of the byte mark
/// ---------------------------------------------------------------------------

/// The moves `mvs` the model allows from `(m, sc)` take the byte heap `g` to
/// `g'`, the scan to the position `sp'`, and keep the bytes below the heap.
let slice_ok (g: heap) (m: M.mheap) (sc: T.scan) (mvs: list T.move) (g': heap) (sp': MP.scan_pos) : prop =
  T.moves_ok m sc mvs /\ fst (T.mmoves BM.bmark g sc mvs) == g' /\
  G.spof (snd (T.mmoves BM.bmark g sc mvs)) == sp' /\ low g' == low g

#push-options "--fuel 1 --z3rlimit 40"
let rec slice_list (g: heap) (m: M.mheap) (sc: T.scan) (s a: nat -> prop)
    (l: list (heap & MP.scan_pos)) (g': heap) (sp': MP.scan_pos)
  : Lemma (requires pre g m sc s a /\ S.moves g (G.spof sc) l g' sp')
          (ensures exists (mvs: list T.move). slice_ok g m sc mvs g' sp')
          (decreases l)
  = match l with
    | [] -> assert (slice_ok g m sc [] g' sp')
    | (h, q) :: t ->
      one_move g m sc s a h q;
      eliminate exists (mv: T.move). good_mv g m sc h q mv
      with begin
        BM.bmove_m g sc mv m;
        MV.move_inv m sc s a mv;
        let m1 = T.move_heap m sc mv in
        let sc1 = T.move_scan sc mv in
        slice_list h m1 sc1 s a t g' sp';
        eliminate exists (tl: list T.move). slice_ok h m1 sc1 tl g' sp'
        with assert (slice_ok g m sc (mv :: tl) g' sp')
      end
#pop-options

/// akhil's slice, as moves of the byte mark.
let steps_list (g: heap) (m: M.mheap) (sc: T.scan) (s a: nat -> prop) (g': heap) (sp': MP.scan_pos)
  : Lemma (requires pre g m sc s a /\ S.mark_steps g (G.spof sc) g' sp')
          (ensures exists (mvs: list T.move). slice_ok g m sc mvs g' sp')
  = eliminate exists (l: list (heap & MP.scan_pos)). S.moves g (G.spof sc) l g' sp'
    with slice_list g m sc s a l g' sp'

/// ---------------------------------------------------------------------------
/// The run while marking
/// ---------------------------------------------------------------------------

/// While marking, the model view represents the code's heap and the marking
/// invariant holds of it with the scan.
let mark_pre (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\ T.Marking? (CF.xc es).ph)
          (ensures (let x = CF.xc es in pre (CF.hof x) (mj x) (scan_of x) x.snap x.allocd))
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur CF.fc sty msize ywords es;
    CR.point CF.fc sty msize ywords es;
    hyps_of_ok CF.fc x EHandover;
    vw_views x;
    SMk.minv_of x

/// The scan is none exactly when akhil's position is.
let scan_none_iff (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\ T.Marking? (CF.xc es).ph)
          (ensures (None? (scan_of (CF.xc es)) <==> (G.spof (scan_of (CF.xc es))).MP.cur == 0UL))
  = let x = CF.xc es in
    mark_pre sty es;
    scan_blk (CF.hof x) (mj x) (scan_of x) x.snap x.allocd

/// What the mark slice asks of the heap, while marking.
let slice_heap (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\ T.Marking? (CF.xc es).ph)
          (ensures (let g = CF.hof (CF.xc es) in
                    well_formed_heap g /\ heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0))
  = let x = CF.xc es in
    CF.good_inv sty es;
    G.mark_heap_ok (CF.hof x) (CF.sof x).FAl.fp

/// ---------------------------------------------------------------------------
/// L8: the slice as an event
/// ---------------------------------------------------------------------------

/// The moves of akhil's slice from `es` to the heap `g2` and position `sp2`.
let slice_mvs (es: list event) (g2: heap) (sp2: MP.scan_pos) : GTot (list T.move) =
  let x = CF.xc es in
  if IDs.strong_excluded_middle (exists (mvs: list T.move). slice_ok (CF.hof x) (mj x) (scan_of x) mvs g2 sp2)
  then IDs.indefinite_description_ghost (list T.move) (fun mvs -> slice_ok (CF.hof x) (mj x) (scan_of x) mvs g2 sp2)
  else []

let bmark_fc (_: unit) : Lemma (CF.fc.m == BM.bmark) = ()

/// **A slice of akhil's mark is the event `ESlice` of its moves**, or no
/// event when it made none.
#push-options "--fuel 1 --z3rlimit 40"
let slice_cfg (sty: style) (es: list event) (g2: heap) (sp2: MP.scan_pos)
  : Lemma (requires CF.good sty es /\ T.Marking? (CF.xc es).ph /\
                    S.mark_steps (CF.hof (CF.xc es)) (G.spof (scan_of (CF.xc es))) g2 sp2)
          (ensures (let x = CF.xc es in
                    let mvs = slice_mvs es g2 sp2 in
                    (mvs == [] ==> g2 == CF.hof x /\ sp2 == G.spof (scan_of x)) /\
                    (Cons? mvs ==>
                       CR.allowed CF.fc sty x (ESlice mvs) /\ CF.good sty (L.append es [ESlice mvs]) /\
                       (let x' = CF.xc (L.append es [ESlice mvs]) in
                        CF.hof x' == g2 /\ G.spof (scan_of x') == sp2 /\ x'.ph == x.ph /\
                        CF.sof x' == CF.sof x))))
  = let x = CF.xc es in
    mark_pre sty es;
    steps_list (CF.hof x) (mj x) (scan_of x) x.snap x.allocd g2 sp2;
    let mvs = slice_mvs es g2 sp2 in
    assert (slice_ok (CF.hof x) (mj x) (scan_of x) mvs g2 sp2);
    bmark_fc ();
    match mvs with
    | [] -> ()
    | _ :: _ ->
      CF.allowed_gc sty es (ESlice mvs);
      CF.snoc sty es (ESlice mvs)
#pop-options

/// ---------------------------------------------------------------------------
/// The hand-over
/// ---------------------------------------------------------------------------

/// Nothing grey on the bytes, nothing grey in the model.
let no_grey_model (g: heap) (m: M.mheap)
  : Lemma (requires brepr m g /\ GC.Spec.Mark.noGreyObjects g) (ensures T.mark_done m)
  = let one (o: nat) : Lemma (M.is_block m o ==> M.col_of m o <> M.Grey)
      = if M.is_block m o then begin
          blk_obj g o;
          grey_iff g (obj_of o)
        end in
    FStar.Classical.forall_intro one

/// **When akhil's slice says marking is over**, the hand-over is enabled:
/// nothing grey, nothing being scanned.
let handover_ready (sty: style) (es: list event) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires CF.good sty es /\ T.Marking? (CF.xc es).ph /\ MS.cache_off st ov p /\
                    GC.Spec.Mark.noGreyObjects (CF.hof (CF.xc es)) /\ MS.scan_of p == G.spof (scan_of (CF.xc es)))
          (ensures T.mark_done (mj (CF.xc es)) /\ None? (scan_of (CF.xc es)))
  = let x = CF.xc es in
    mark_pre sty es;
    scan_none_iff sty es;
    no_grey_model (CF.hof x) (mj x)

/// After the hand-over the cache is off at the sweep, the position none.
let handover_cache (g: heap) (c: U64.t) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires MS.cache_off st ov p)
          (ensures MS.mark_cache_ok g (Ph.Sweeping c) st ov p /\ MS.scan_of p == MP.scan_none)
  = MS.mark_cache_not_marking g (Ph.Sweeping c) st ov p

/// ---------------------------------------------------------------------------
/// L7: root darkening depends only on which words are roots
/// ---------------------------------------------------------------------------

module MB = GC.Impl.MarkBounded
module MBP = GC.Impl.MarkBoundedPrecondition
module MStart = GC.Gen.MarkPhase.Start
module HE = GC.Gen.HeapExtensional

/// The root `v` darkens the header at `a`.
let hitv (g: heap) (v: U64.t) (a: hp_addr) : prop =
  is_pointer v /\ hd_address (resolve_object (v <: obj_addr) g) == a

/// One of the first `idx` roots does.
let hitp (g: heap) (rs: Seq.seq U64.t) (idx: nat{idx <= Seq.length rs}) (a: hp_addr) : prop =
  exists (j: nat). j < idx /\ hitv g (Seq.index rs j) a

let wht (w: U64.t) : bool = getColor w = GC.Lib.Header.White

/// The words after darkening the first `idx` roots: a header some root
/// darkens is grey if it was white, every other word unchanged.
let dk (g g': heap) (rs: Seq.seq U64.t) (idx: nat{idx <= Seq.length rs}) : prop =
  forall (a: hp_addr).
    (hitp g rs idx a /\ wht (read_word g a) ==> read_word g' a == colorHeader (read_word g a) GC.Lib.Header.Gray) /\
    (~(hitp g rs idx a /\ wht (read_word g a)) ==> read_word g' a == read_word g a)

/// The header of `t`, as the bounded darkening finds it.
let hd_facts (t: obj_addr)
  : Lemma (U64.sub t mword == hd_address t /\ U64.v (hd_address t) + U64.v mword < heap_size /\
           f_address (hd_address t) == t)
  = hd_address_spec t;
    U64.v_inj (U64.sub t mword) (hd_address t);
    f_address_spec (hd_address t);
    U64.v_inj (f_address (hd_address t)) t

/// One word after one more root.
#push-options "--z3rlimit 40"
let step_at (g g0 g1: heap) (rs: Seq.seq U64.t) (idx: nat{0 < idx /\ idx <= Seq.length rs}) (t: obj_addr) (a: hp_addr)
  : Lemma (requires dk g g0 rs (idx - 1) /\ hitv g (Seq.index rs (idx - 1)) (hd_address t) /\
                    (forall (b: hp_addr). hitv g (Seq.index rs (idx - 1)) b ==> b == hd_address t) /\
                    g1 == (if wht (read_word g0 (hd_address t))
                           then write_word g0 (hd_address t) (colorHeader (read_word g0 (hd_address t)) GC.Lib.Header.Gray)
                           else g0))
          (ensures (hitp g rs idx a /\ wht (read_word g a) ==>
                      read_word g1 a == colorHeader (read_word g a) GC.Lib.Header.Gray) /\
                   (~(hitp g rs idx a /\ wht (read_word g a)) ==> read_word g1 a == read_word g a))
  = let ha = hd_address t in
    assert (hitp g rs idx a <==> hitp g rs (idx - 1) a \/ hitv g (Seq.index rs (idx - 1)) a);
    colorHeader_getColor (read_word g a) GC.Lib.Header.Gray;
    if wht (read_word g0 ha) then begin
      if a = ha then read_write_same g0 ha (colorHeader (read_word g0 ha) GC.Lib.Header.Gray)
      else read_write_different g0 ha a (colorHeader (read_word g0 ha) GC.Lib.Header.Gray)
    end
#pop-options

/// One more root, every word.
#push-options "--z3rlimit 40"
let dk_step (g g0: heap) (st0: Seq.seq obj_addr) (rs: Seq.seq U64.t) (idx: nat{0 < idx /\ idx <= Seq.length rs}) (cap: nat)
  : Lemma (requires dk g g0 rs (idx - 1) /\
                    (is_pointer (Seq.index rs (idx - 1)) ==>
                       resolve_object (Seq.index rs (idx - 1) <: obj_addr) g0 ==
                       resolve_object (Seq.index rs (idx - 1) <: obj_addr) g))
          (ensures dk g (fst (MB.check_and_darken_bounded_spec g0 st0 (Seq.index rs (idx - 1)) cap)) rs idx)
  = let v = Seq.index rs (idx - 1) in
    let g1 = fst (MB.check_and_darken_bounded_spec g0 st0 v cap) in
    if is_pointer v then begin
      let t : obj_addr = resolve_object (v <: obj_addr) g in
      hd_facts t;
      is_white_iff t g0;
      color_of_object_spec t g0;
      makeGray_spec t g0;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (step_at g g0 g1 rs idx t))
    end
    else begin
      assert (forall (a: hp_addr). hitp g rs idx a <==> hitp g rs (idx - 1) a)
    end
#pop-options

#push-options "--fuel 1"
let rec dk_prefix (g: heap) (st: Seq.seq obj_addr) (rs: Seq.seq U64.t) (idx: nat{idx <= Seq.length rs}) (cap: nat)
  : Lemma (ensures dk g (fst (MB.darken_roots_bounded_prefix_spec g st rs idx cap)) rs idx) (decreases idx)
  = if idx > 0 then begin
      dk_prefix g st rs (idx - 1) cap;
      MB.darken_roots_bounded_prefix_step g st rs (idx - 1) cap;
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st rs (idx - 1) cap in
      let v = Seq.index rs (idx - 1) in
      if is_pointer v then MB.darken_roots_bounded_prefix_preserves_resolve g st rs (idx - 1) cap v;
      dk_step g g0 st0 rs idx cap
    end
#pop-options

/// Some root darkens `a`, read by membership.
let hitp_mem (g: heap) (rs: Seq.seq U64.t) (a: hp_addr)
  : Lemma (hitp g rs (Seq.length rs) a <==> (exists (u: U64.t). Seq.mem u rs /\ hitv g u a))
  = let to (j: nat) : Lemma (j < Seq.length rs /\ hitv g (Seq.index rs j) a ==> (exists (u: U64.t). Seq.mem u rs /\ hitv g u a))
      = if j < Seq.length rs then BM.mem_of_index rs j in
    FStar.Classical.forall_intro to;
    let from (u: U64.t) : Lemma (Seq.mem u rs /\ hitv g u a ==> hitp g rs (Seq.length rs) a)
      = if Seq.mem u rs then FStar.Seq.Properties.mem_index u rs in
    FStar.Classical.forall_intro from

/// **Root darkening depends only on which words are roots.**
#push-options "--z3rlimit 40"
let darkened_mem (g: heap) (rs rs': Seq.seq U64.t)
  : Lemma (requires forall (u: U64.t). Seq.mem u rs <==> Seq.mem u rs')
          (ensures MStart.darkened g rs == MStart.darkened g rs')
  = let h = MStart.darkened g rs in
    let h' = MStart.darkened g rs' in
    dk_prefix g Seq.empty rs (Seq.length rs) (Seq.length rs + 1);
    dk_prefix g Seq.empty rs' (Seq.length rs') (Seq.length rs' + 1);
    let one (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==> read_word h (U64.uint_to_t b) == read_word h' (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then begin
          let a : hp_addr = U64.uint_to_t b in
          hitp_mem g rs a;
          hitp_mem g rs' a
        end in
    FStar.Classical.forall_intro one;
    HE.heap_read_word_ext h h'
#pop-options

/// The bytes below the heap stay, when every root names an object.
#push-options "--fuel 1 --z3rlimit 40"
let rec low_prefix (g: heap) (st: Seq.seq obj_addr) (rs: Seq.seq U64.t) (idx: nat{idx <= Seq.length rs}) (cap: nat)
  : Lemma (requires forall (u: U64.t). Seq.mem u rs /\ is_pointer u ==>
                      Seq.mem (resolve_object (u <: obj_addr) g) (objects zero_addr g))
          (ensures low (fst (MB.darken_roots_bounded_prefix_spec g st rs idx cap)) == low g) (decreases idx)
  = if idx > 0 then begin
      low_prefix g st rs (idx - 1) cap;
      MB.darken_roots_bounded_prefix_step g st rs (idx - 1) cap;
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g st rs (idx - 1) cap in
      let v = Seq.index rs (idx - 1) in
      BM.mem_of_index rs (idx - 1);
      if is_pointer v then begin
        MB.darken_roots_bounded_prefix_preserves_resolve g st rs (idx - 1) cap v;
        let t : obj_addr = resolve_object (v <: obj_addr) g in
        hd_facts t;
        blk g t;
        low_grey g0 t
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// L7: the start words name objects in use
/// ---------------------------------------------------------------------------

/// A start word's target is reachable, so kept, so not free.
#push-options "--z3rlimit 40"
let start_kept (sty: style) (es: list event) (u: U64.t) (t: nat)
  : Lemma (requires CF.good sty es /\ Seq.mem u (BM.start_ws (BM.cview (CF.xc es).w)) /\
                    M.resolve (cabs (CF.hof (CF.xc es))) (ptr_b u) == Some t)
          (ensures kept (CF.xc es) t)
  = let x = CF.xc es in
    let g = CF.hof x in
    let wc = BM.cview x.w in
    CF.components ();
    CR.point CF.fc sty msize ywords es;
    vw_views x;
    BM.start_facts g wc;
    assert (BM.hits g (BM.start_ws wc) t);
    BM.yrepr_heq (vw x).M.yng x.w.cyng;
    BM.outside_heq wc (vw x) t;
    let r : M.reach (vw x) t = M.RBase t () in
    FStar.Classical.exists_intro (fun (_: M.reach (vw x) t) -> True) r
#pop-options

/// Kept is not blue.
let kept_not_blue (x: config CF.fc) (t: nat)
  : Lemma (requires kept x t /\ M.is_block (cabs (CF.hof x)) t)
          (ensures pos t + 8 < heap_size /\ ~(is_blue (obj_of t) (CF.hof x)))
  = let g = CF.hof x in
    assert (M.is_block (abs g) t);
    abs_blue g t

/// The model's start words are valid roots for akhil's darkening.
#push-options "--z3rlimit 40"
let start_word (sty: style) (es: list event) (u: U64.t)
  : Lemma (requires CF.good sty es /\ Seq.mem u (BM.start_ws (BM.cview (CF.xc es).w)))
          (ensures MBP.root_valid_for_darkening (CF.hof (CF.xc es)) u)
  = let x = CF.xc es in
    let g = CF.hof x in
    let wc = BM.cview x.w in
    CF.components ();
    CR.point CF.fc sty msize ywords es;
    vw_views x;
    BM.start_facts g wc;
    let Some t = M.resolve (cabs g) (ptr_b u) in
    start_kept sty es u t;
    ptr_decode u;
    let b = ptr_b u in
    resolve_pos g b t;
    kept_not_blue x t;
    resolve_abs_of_cabs g b t;
    assert (no_infix_tags (cabs g));
    no_infix_of_model g;
    ptr_resolve g b t;
    assert (obj_of b == u);
    assert (resolve_object (u <: obj_addr) g == obj_of t)
#pop-options

/// ---------------------------------------------------------------------------
/// L7: the start
/// ---------------------------------------------------------------------------

/// Idle with the nursery empty, akhil's idle shape.
let nursery_reset (nm: GC.Gen.MinorHeap.minor_state)
  : Lemma (requires U64.v nm.GC.Gen.MinorHeap.bump == 0 /\
                    nm.GC.Gen.MinorHeap.data == Seq.create GC.Gen.Base.minor_heap_size 0uy)
          (ensures nm == GC.Gen.MinorHeap.minor_reset nm)
  = let r = GC.Gen.MinorHeap.minor_reset nm in
    U64.v_inj r.GC.Gen.MinorHeap.bump nm.GC.Gen.MinorHeap.bump

let idle_shape (sty: style) (es: list event) (nm: GC.Gen.MinorHeap.minor_state) (sp: MP.scan_pos)
  : Lemma (requires CF.good sty es /\ T.Idle? (CF.xc es).ph /\ U64.v nm.GC.Gen.MinorHeap.bump == 0 /\
                    nm.GC.Gen.MinorHeap.data == Seq.create GC.Gen.Base.minor_heap_size 0uy)
          (ensures GC.Gen.Incremental.phase_shape nm (CF.hof (CF.xc es)) (CF.sof (CF.xc es)).FAl.fp Ph.Idle sp)
  = let x = CF.xc es in
    CF.good_inv sty es;
    G.idle_major (CF.hof x) (CF.sof x).FAl.fp;
    nursery_reset nm;
    GC.Gen.HeapInvariant.collection_heap_shape_after_minor_reset nm (CF.hof x) (CF.sof x).FAl.fp;
    GC.Gen.Incremental.phase_shape_idle nm (CF.hof x) (CF.sof x).FAl.fp sp

/// **The start is akhil's `start_cycle`** on any array with the members of
/// the model's start words: valid roots for it, and the event `EStart`.
#push-options "--z3rlimit 40"
let start_cfg (sty: style) (es: list event) (rs: Seq.seq U64.t)
  : Lemma (requires CF.good sty es /\ T.Idle? (CF.xc es).ph /\
                    (forall (u: U64.t). Seq.mem u rs <==> Seq.mem u (BM.start_ws (BM.cview (CF.xc es).w))))
          (ensures (let x = CF.xc es in
                    (forall (i: nat). i < Seq.length rs ==> MBP.root_valid_for_darkening (CF.hof x) (Seq.index rs i)) /\
                    CR.allowed CF.fc sty x EStart /\ CF.good sty (L.append es [EStart]) /\
                    (let x' = CF.xc (L.append es [EStart]) in
                     CF.hof x' == MStart.darkened (CF.hof x) rs /\ x'.ph == T.Marking /\ scan_of x' == None /\
                     CF.sof x' == CF.sof x)))
  = let x = CF.xc es in
    let g = CF.hof x in
    let ws = BM.start_ws (BM.cview x.w) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (start_word sty es));
    let vi (i: nat) : Lemma (i < Seq.length rs ==> MBP.root_valid_for_darkening g (Seq.index rs i))
      = if i < Seq.length rs then BM.mem_of_index rs i in
    FStar.Classical.forall_intro vi;
    darkened_mem g ws rs;
    low_prefix g Seq.empty ws (Seq.length ws) (Seq.length ws + 1);
    bmark_fc ();
    CF.allowed_gc sty es EStart;
    CF.snoc sty es EStart
#pop-options

/// With an empty nursery the start words are the roots' major words.
#push-options "--fuel 1"
let rec root_ws_mem (h: M.mheap) (rs: list M.value) (u: U64.t)
  : Lemma (ensures Seq.mem u (BM.root_ws h rs) <==>
                   (exists (a: nat). L.memP (M.VPtr (M.Major a)) rs /\ Some? (M.resolve h a) /\
                                     u == concv (M.VPtr (M.Major a))))
          (decreases rs)
  = BM.mem_empty u;
    match rs with
    | [] -> ()
    | v :: tl ->
      root_ws_mem h tl u;
      FStar.Seq.Properties.lemma_mem_append (BM.maj_word h v) (BM.root_ws h tl);
      (match v with
       | M.VPtr (M.Major a) -> FStar.Seq.Properties.mem_cons (concv v) (Seq.empty #U64.t)
       | _ -> ())
#pop-options

let start_ws_roots (g: heap) (w: M.world) (u: U64.t)
  : Lemma (requires w.M.maj == cabs g /\ (forall (o: nat). ~(M.is_block w.M.yng o)))
          (ensures Seq.mem u (BM.start_ws w) <==> Seq.mem u (BM.root_ws (cabs g) w.M.roots))
  = BM.young_facts g w.M.yng w.M.yng.M.size;
    FStar.Seq.Properties.lemma_mem_append (BM.root_ws (cabs g) w.M.roots) (BM.young_ws (cabs g) w.M.yng w.M.yng.M.size);
    if Seq.mem u (BM.young_ws (cabs g) w.M.yng w.M.yng.M.size) then begin
      let Some t = M.resolve (cabs g) (ptr_b u) in
      assert (BM.hits g (BM.young_ws (cabs g) w.M.yng w.M.yng.M.size) t)
    end

/// An empty byte nursery has no young block.
let empty_young (ms: GC.Gen.MinorHeap.minor_state) (o: nat)
  : Lemma (requires U64.v ms.GC.Gen.MinorHeap.bump == 0) (ensures ~(M.is_block (GC.Spec.Top.Young.ycabs ms) o))
  = GC.Spec.Top.Young.yat_empty ms.GC.Gen.MinorHeap.data 0 (8 * o)

/// ---------------------------------------------------------------------------
/// The mark cache across the events with no mark code
/// ---------------------------------------------------------------------------

module SPI = GC.Spec.SweepPhase.Intrinsic
module MPA = GC.Spec.MarkPhase.Alloc
module AI = GC.Spec.AllocIface
module FB = GC.Spec.Top.FFBytes
module FAO = GC.Spec.Top.FFAllocOk
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module W = GC.Spec.Walk

/// The same header, the same colour, size and scanning.
let hdr_same (g g': heap) (x: obj_addr)
  : Lemma (requires read_word g' (hd_address x) == read_word g (hd_address x))
          (ensures is_white x g' == is_white x g /\ is_gray x g' == is_gray x g /\ is_blue x g' == is_blue x g /\
                   is_black x g' == is_black x g /\ is_no_scan x g' == is_no_scan x g /\
                   wosize_of_object x g' == wosize_of_object x g)
  = color_of_object_spec x g; color_of_object_spec x g';
    is_white_iff x g; is_white_iff x g'; is_gray_iff x g; is_gray_iff x g';
    is_blue_iff x g; is_blue_iff x g'; is_black_iff x g; is_black_iff x g';
    tag_of_object_spec x g; tag_of_object_spec x g'; is_no_scan_spec x g; is_no_scan_spec x g';
    wosize_of_object_spec x g; wosize_of_object_spec x g'

/// The cache reads only the walk and the headers: one object at a time ...
let obj_same (g g': heap) (y: obj_addr)
  : Lemma (requires SPI.same_heads g g' /\ Seq.mem y (objects zero_addr g))
          (ensures Seq.mem y (objects zero_addr g') /\
                   is_white y g' == is_white y g /\ is_gray y g' == is_gray y g /\ is_blue y g' == is_blue y g /\
                   is_no_scan y g' == is_no_scan y g /\ wosize_of_object y g' == wosize_of_object y g)
  = SPI.same_heads_facts g g';
    hdr_same g g' y

let grey_same (g g': heap) (y: obj_addr)
  : Lemma (requires SPI.same_heads g g' /\ MS.grey_obj g' y) (ensures MS.grey_obj g y)
  = SPI.same_heads_facts g g';
    obj_same g g' y

/// **... so the cache does.**
#push-options "--z3rlimit 40"
let cache_heads (g g': heap) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires SPI.same_heads g g' /\ MS.marking_cache g st ov p)
          (ensures MS.marking_cache g' st ov p)
  = let e (y: obj_addr) : Lemma (Seq.mem y st ==> MS.entry_ok g' y)
      = if Seq.mem y st then obj_same g g' y in
    FStar.Classical.forall_intro e;
    if p.MS.cur <> 0UL then obj_same g g' (p.MS.cur <: obj_addr);
    if p.MS.rc <> 0UL && p.MS.rc <> zero_addr then obj_same g g' (U64.add p.MS.rc mword <: obj_addr);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (grey_same g g'));
    assert (MS.covered g' st ov p)
#pop-options

/// The allocation keeps every block in use, header and fields.
#push-options "--z3rlimit 40"
let keeps_one (g g': heap) (y: obj_addr)
  : Lemma (requires AI.others_unchanged g g' /\ in_use free_stw g y)
          (ensures Seq.mem y (objects zero_addr g') /\ read_word g' (hd_address y) == read_word g (hd_address y) /\
                   SPI.same_block g g' (hd_address y))
  = hd_address_spec y;
    wosize_of_object_spec y g;
    is_blue_iff y g;
    let q = hd_address y in
    let body (a: hp_addr)
      : Lemma (requires U64.v q < U64.v a /\ U64.v a < W.bnext g q) (ensures read_word g' a == read_word g a)
      = assert (U64.v y <= U64.v a /\ U64.v a < U64.v y + U64.v (wosize_of_object y g) * 8) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body)
#pop-options

let keeps_of (g g': heap)
  : Lemma (requires AI.others_unchanged g g') (ensures MPA.keeps_blocks free_stw g g')
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (keeps_one g g'))

/// The allocation makes no block grey.
#push-options "--z3rlimit 40"
let no_new_grey (g g': heap) (x: obj_addr) (y: obj_addr)
  : Lemma (requires AI.others_unchanged g g' /\
                    (forall (z: obj_addr). in_use free_stw g' z == (in_use free_stw g z || z = x)) /\
                    color_of_object x g' == GC.Lib.Header.Black /\ MS.grey_obj g' y)
          (ensures MS.grey_obj g y)
  = is_gray_iff y g'; is_blue_iff y g'; is_gray_iff x g';
    assert (in_use free_stw g' y);
    if y = x then () else hdr_same g g' y
#pop-options

/// **An allocation while marking keeps the cache.**
#push-options "--z3rlimit 40"
let alloc_marking_cache (g: heap) (fp: U64.t) (wz: nat) (tag: U64.t) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires FB.ready g fp /\ well_formed_heap g /\ wz >= 1 /\ U64.v tag <> 249 /\ U64.v tag < 256 /\
                    MS.mark_cache_ok g Ph.Marking st ov p)
          (ensures MS.mark_cache_ok (GC.Spec.Allocator.Phase.alloc_at Ph.Marking g fp wz tag).SA.heap_out Ph.Marking st ov p)
  = FB.alloc_bytes Ph.Marking g fp wz tag;
    let r = GC.Spec.Allocator.Phase.alloc_at Ph.Marking g fp wz tag in
    if r.SA.obj_out <> 0UL then begin
      let x : obj_addr = r.SA.obj_out in
      keeps_of g r.SA.heap_out;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (no_new_grey g r.SA.heap_out x));
      MS.mark_cache_keeps_blocks g r.SA.heap_out st ov p
    end
#pop-options

/// **`EAlloc` (allocation and Fill) keeps the cache**, at every phase.
#push-options "--z3rlimit 40"
let alloc_cache (sty: style) (es: list event) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
    (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires CF.good sty es /\ CR.allowed CF.fc sty (CF.xc es) (EAlloc sz tag vs) /\
                    MS.mark_cache_ok (CF.hof (CF.xc es)) (FAl.gph (CF.xc es).ph) st ov p)
          (ensures (let x = CF.xc es in
                    let x' = step CF.fc x (EAlloc sz tag vs) in
                    MS.mark_cache_ok (CF.hof x') (FAl.gph x'.ph) st ov p /\ x'.ms == x.ms /\ x'.ph == x.ph))
  = let x = CF.xc es in
    let g = CF.hof x in
    let fp = (CF.sof x).FAl.fp in
    let r = AC.alloc_phase g fp (FAl.gph x.ph) sz (FAl.tg tag) in
    if r.SA.obj_out = 0UL then CF.alloc_none sty es sz tag vs
    else begin
      CF.alloc_some sty es sz tag vs;
      let x' = step CF.fc x (EAlloc sz tag vs) in
      if T.Marking? x.ph then begin
        CF.good_inv sty es;
        FAO.ready_of x.ph g fp;
        G.mark_heap_ok g fp;
        CF.ffres_eq x sz tag;
        CF.gl_ok x;
        FAl.tg_v tag;
        alloc_marking_cache g fp sz (FAl.tg tag) st ov p;
        MS.mark_cache_marking r.SA.heap_out st ov p;
        cache_heads r.SA.heap_out (CF.hof x') st ov p;
        MS.mark_cache_marking (CF.hof x') st ov p
      end
      else MS.mark_cache_off g (CF.hof x') (FAl.gph x.ph) (FAl.gph x.ph) st ov p
    end
#pop-options

/// **Outside marking the cache is off**, whatever the heap and the phase.
let off_cache (g g': heap) (ph ph': T.phase U64.t) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (requires MS.mark_cache_ok g (FAl.gph ph) st ov p /\ ~(T.Marking? ph) /\ ~(T.Marking? ph'))
          (ensures MS.mark_cache_ok g' (FAl.gph ph') st ov p)
  = MS.mark_cache_off g g' (FAl.gph ph) (FAl.gph ph') st ov p

/// While marking, the cache as the slice takes and gives it.
let cache_marking (g: heap) (st: Seq.seq obj_addr) (ov: bool) (p: MS.mark_pos)
  : Lemma (MS.mark_cache_ok g Ph.Marking st ov p <==> MS.marking_cache g st ov p)
  = MS.mark_cache_marking g st ov p
