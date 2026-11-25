/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWMut - the program's other events in a pages witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  On a described configuration (GC.Spec.Top.PWDesc):
///   - `step_write`: a write to a major block through the byte barrier
///     (`ByteBarrier.bwrite_cabs`): the field changes and, while marking,
///     a white old target turns grey; the allocator's invariant holds again
///     (`inv_frame_at`: the change is one it does not read);
///   - `step_read`, `step_roots`: the roots change;
///   - `step_yalloc`: a young allocation; `yal1`, `yal2`: the runs' two
///     one-field young blocks, at young addresses 0 and 2.

module GC.Spec.Top.PWMut

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Y = GC.Spec.Top.Young
module BB = GC.Spec.Top.ByteBarrier
module PIn = GC.Spec.Top.PagesInst
module PWP = GC.Spec.Top.PWPages
module FWS = GC.Spec.Top.FFWStep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// A write
/// ---------------------------------------------------------------------------

/// The list with element `i` replaced.
let rec setv (l: list M.value) (i: nat) (v: M.value) : list M.value =
  match l with
  | [] -> []
  | h :: tl -> if i = 0 then v :: tl else h :: setv tl (i - 1) v

#push-options "--fuel 1"
let rec setv_spec (l: list M.value) (i: nat) (v: M.value)
  : Lemma (ensures L.length (setv l i v) == L.length l /\
                   (forall (j: nat). vi (setv l i v) j == (if j = i && i < L.length l then v else vi l j)))
          (decreases l)
  = match l with
    | [] -> ()
    | h :: tl ->
      if i = 0 then ()
      else begin
        setv_spec tl (i - 1) v;
        let one (j: nat) : Lemma (vi (setv l i v) j == (if j = i && i < L.length l then v else vi l j))
          = if j > 0 then assert (vi (setv l i v) j == vi (setv tl (i - 1) v) (j - 1)) in
        FStar.Classical.forall_intro one
      end
#pop-options

/// The block the barrier darkens, if any.
let dt (x: config pc) (o i: nat) : GTot (option nat) =
  if T.is_marking x.ph then
    (match T.old_target (mx x) o i with
     | Some t -> if M.col_of (mx x) t = M.White then Some t else None
     | None -> None)
  else None

let grey_bd (b: bd) : bd = { b with bc = M.Grey }

/// The description after the write.
let dwrite (x: config pc) (d: dsc) (o i: nat) (v: M.value) : GTot dsc =
  let t = dt x o i in
  { d with db = (fun (y: nat) ->
      match d.db y with
      | Some b ->
        let b1 = if y = o then { b with bf = setv b.bf i v } else b in
        Some (if t = Some y then grey_bd b1 else b1)
      | None -> None) }

let wpre (x: config pc) (d: dsc) (o i: nat) (v: M.value) : prop =
  cok /\ holds x d /\ Some? (d.db o) /\ (Some?.v (d.db o)).blv /\
  i < (Some?.v (d.db o)).bw /\ (Some?.v (d.db o)).bt <> M.closure_tag /\
  storable_w v /\ FWS.no_young [v] == true /\
  (match dt x o i with Some t -> Some? (d.db t) /\ usable d (Some?.v (d.db t)) | None -> True) /\
  (M.scannable (Some?.v (d.db o)).bt ==>
     T.sound_value pa x.ph (stx x) x.w.cmaj (M.set_field (BB.tdark (T.is_marking x.ph) (mx x) o i) o i v) v)

/// The new model.
let mw (x: config pc) (o i: nat) (v: M.value) : GTot M.mheap = M.set_field (BB.tdark (T.is_marking x.ph) (mx x) o i) o i v

let write_bytes (x: config pc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires wpre x d o i v)
          (ensures (let (g', rem') = BB.bwrite (T.is_marking x.ph) x.w.cmaj [] o i v in
                    R.heq (mw x o i v) (cabs g') /\ rem' == []))
  = holds_elim x d;
    blk x d o;
    FWS.write_parts (T.is_marking x.ph) (mx x) (mw x o i v) x.w.cmaj o i v

/// The change is one the allocator's invariant does not read.
let wr_cols (x: config pc) (d: dsc) (o i: nat) (v: M.value) (y: nat)
  : Lemma (requires wpre x d o i v)
          (ensures M.col_of (mw x o i v) y =!= M.col_of (mx x) y ==>
                   T.in_use pa (stx x) x.w.cmaj (mx x) y /\ T.Marking? x.ph /\ M.dark (M.col_of (mw x o i v) y))
  = match dt x o i with
    | Some t -> holds_blk x d t; iu_def x t
    | None -> ()

let wr_body (x: config pc) (d: dsc) (o i: nat) (v: M.value) (w: nat)
  : Lemma (requires wpre x d o i v)
          (ensures (mw x o i v).M.body w =!= (mx x).M.body w ==>
                   (exists (o': nat). T.live_target pa x.ph (stx x) x.w.cmaj (mx x) o' /\ o' < w /\
                      w <= o' + M.wz_of (mx x) o' /\ M.tag_of (mx x) o' <> M.closure_tag /\
                      (M.scannable (M.tag_of (mx x) o') ==>
                         T.sound_value pa x.ph (stx x) x.w.cmaj (mw x o i v) ((mw x o i v).M.body w))))
  = holds_elim x d;
    blk x d o;
    BB.tdark_shape (T.is_marking x.ph) (mx x) o i;
    if w = o + 1 + i then begin
      holds_blk x d o;
      assert (T.live_target pa x.ph (stx x) x.w.cmaj (mx x) o)
    end

#push-options "--z3rlimit 40"
let write_rel (x: config pc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires wpre x d o i v)
          (ensures T.inv_frame_rel pa x.ph (stx x) x.w.cmaj (mx x) (mw x o i v))
  = BB.tdark_shape (T.is_marking x.ph) (mx x) o i;
    let m' = mw x o i v in
    assert (m'.M.size == (mx x).M.size);
    assert (forall (y: nat). M.is_block m' y == M.is_block (mx x) y);
    assert (forall (y: nat). M.wz_of m' y == M.wz_of (mx x) y /\ M.tag_of m' y == M.tag_of (mx x) y);
    FStar.Classical.forall_intro (wr_cols x d o i v);
    FStar.Classical.forall_intro (wr_body x d o i v)
#pop-options

/// In use is kept: the write recolours at most a white block, grey.
let mw_iu (x x': config pc) (d: dsc) (o i: nat) (v: M.value) (y: nat)
  : Lemma (requires wpre x d o i v /\ stx x' == stx x /\ R.heq (mx x') (mw x o i v))
          (ensures iu x' y == iu x y)
  = iu_def x y; iu_def x' y;
    BB.tdark_shape (T.is_marking x.ph) (mx x) o i

/// The header after the write.
let mw_hd (x: config pc) (o i: nat) (v: M.value) (y: nat)
  : Lemma ((mw x o i v).M.hd y ==
           (match (mx x).M.hd y with
            | Some hx -> if dt x o i = Some y then Some ({ hx with M.col = M.Grey }) else Some hx
            | None -> None))
  = ()

/// A field after the write: only field `i` of `o` changes.
let mw_field (x: config pc) (d: dsc) (o i: nat) (v: M.value) (y j: nat)
  : Lemma (requires wpre x d o i v /\ M.is_block (mx x) y /\ j < M.wz_of (mx x) y)
          (ensures M.field (mw x o i v) y j == (if y = o && j = i then v else M.field (mx x) y j))
  = holds_elim x d;
    blk x d o;
    let w = y + 1 + j in
    if w = o + 1 + i && y <> o then begin
      assert (M.covers (mx x) y w);
      assert (M.covers (mx x) o w)
    end

/// One block of the description after the write.
#push-options "--z3rlimit 40"
let write_blk (x x': config pc) (d: dsc) (o i: nat) (v: M.value) (y: nat)
  : Lemma (requires wpre x d o i v /\ x'.ph == x.ph /\ stx x' == stx x /\ R.heq (mx x') (mw x o i v) /\
                    Some? (d.db y))
          (ensures iu x' y == iu x y /\ bk x' (dwrite x d o i v) y (Some?.v ((dwrite x d o i v).db y)))
  = holds_elim x d;
    holds_blk x d y;
    let b = Some?.v (d.db y) in
    let d' = dwrite x d o i v in
    let b' = Some?.v (d'.db y) in
    mw_iu x x' d o i v y;
    iu_def x y;
    mw_hd x o i v y;
    blk x d o;
    setv_spec b.bf i v;
    (match dt x o i with Some t -> blk x d t | None -> ());
    if iu x y then begin
      assert ((mx x').M.hd y == (mw x o i v).M.hd y);
      assert (hcol x' b' y == (if dt x o i = Some y then M.Grey else hcol x b y));
      if usable d b then begin
        let fl (j: nat) : Lemma (j < b.bw ==> M.field (mx x') y j == vi b'.bf j)
          = if j < b.bw then mw_field x d o i v y j in
        FStar.Classical.forall_intro fl
      end
    end
#pop-options

/// The walk depends on blocks, sizes and tags only.
let wf_shape (m m': M.mheap)
  : Lemma (requires M.well_formed m /\ m'.M.size == m.M.size /\
                    (forall (y: nat). M.is_block m' y == M.is_block m y /\ M.wz_of m' y == M.wz_of m y /\
                                      M.tag_of m' y == M.tag_of m y))
          (ensures M.well_formed m')
  = assert (forall (y w: nat). M.covers m' y w == M.covers m y w)

/// The configuration after the write, on the models.
#push-options "--z3rlimit 40"
let write_after (x: config pc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires wpre x d o i v)
          (ensures (let x' = step pc x (EWrite (M.Major o) i v) in
                    R.heq (mx x') (mw x o i v) /\ x'.w.crem == [] /\ x'.ph == x.ph /\ stx x' == stx x /\
                    x'.stopped == x.stopped /\ x'.w.cyng == x.w.cyng /\ x'.w.croots == x.w.croots /\
                    pa.T.inv x'.ph x'.w.cmaj (stx x') /\ M.well_formed (mx x')))
  = holds_elim x d;
    write_bytes x d o i v;
    write_rel x d o i v;
    let x' = step pc x (EWrite (M.Major o) i v) in
    brepr_cabs x.w.cmaj;
    R.heq_sym (mw x o i v) (mx x');
    cok_hyps x (EWrite (M.Major o) i v);
    assert (T.inv_frame_at byte_rep pa x.ph x.w.cmaj (stx x) x'.w.cmaj);
    assert (T.inv_frame_m pa x.ph x.w.cmaj (stx x) x'.w.cmaj (mx x) (mw x o i v));
    BB.tdark_shape (T.is_marking x.ph) (mx x) o i;
    wf_shape (mx x) (mw x o i v);
    PIn.wf_heq (mw x o i v) (mx x')
#pop-options

let write_intro (x: config pc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires wpre x d o i v /\
                    (let x' = step pc x (EWrite (M.Major o) i v) in
                     let d' = dwrite x d o i v in
                     (forall (y: nat). Some? (d'.db y) ==> bk x' d' y (Some?.v (d'.db y))) /\
                     (forall (y: nat). iu x' y == true ==> Some? (d'.db y))))
          (ensures holds (step pc x (EWrite (M.Major o) i v)) (dwrite x d o i v))
  = holds_elim x d;
    write_after x d o i v;
    holds_intro (step pc x (EWrite (M.Major o) i v)) (dwrite x d o i v)

/// **EWrite** to a major block.
let step_write (x: config pc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires wpre x d o i v)
          (ensures holds (step pc x (EWrite (M.Major o) i v)) (dwrite x d o i v))
  = write_after x d o i v;
    let x' = step pc x (EWrite (M.Major o) i v) in
    let d' = dwrite x d o i v in
    let bl (y: nat) : Lemma (Some? (d'.db y) ==> bk x' d' y (Some?.v (d'.db y)))
      = if Some? (d.db y) then write_blk x x' d o i v y in
    FStar.Classical.forall_intro bl;
    let des (y: nat) : Lemma (iu x' y == true ==> Some? (d'.db y))
      = mw_iu x x' d o i v y;
        if iu x y then holds_iu x d y in
    FStar.Classical.forall_intro des;
    write_intro x d o i v

/// ---------------------------------------------------------------------------
/// Reads and roots
/// ---------------------------------------------------------------------------

/// A block's description, with the heap, state and phase unchanged.
let bk_same (x x': config pc) (d d': dsc) (y: nat) (b: bd)
  : Lemma (requires x'.w.cmaj == x.w.cmaj /\ x'.ast == x.ast /\ x'.ph == x.ph /\ d'.dk == d.dk /\ bk x d y b)
          (ensures bk x' d' y b)
  = assert (mx x' == mx x);
    assert (forall (z: nat). iu x' z == iu x z);
    assert (hcol x' b y == hcol x b y);
    assert (unsw x' y == unsw x y)

let step_read (x: config pc) (d: dsc) (o i: nat)
  : Lemma (requires holds x d /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)) /\ i < (Some?.v (d.db o)).bw)
          (ensures holds (step pc x (ERead (M.Major o) i))
                         ({ d with drt = vi (Some?.v (d.db o)).bf i :: d.drt }))
  = holds_elim x d;
    blk x d o;
    brepr_cabs x.w.cmaj;
    byte_major_reads (mx x) x.w.cmaj;
    let x' = step pc x (ERead (M.Major o) i) in
    let d' = { d with drt = vi (Some?.v (d.db o)).bf i :: d.drt } in
    assert (byte_rep.R.read x.w.cmaj o i == M.field (mx x) o i);
    assert (x'.w.croots == d'.drt);
    assert (x'.w.cmaj == x.w.cmaj /\ x'.ast == x.ast /\ x'.ph == x.ph);
    assert (forall (y: nat). iu x' y == iu x y);
    let bl (y: nat) : Lemma (Some? (d'.db y) ==> bk x' d' y (Some?.v (d'.db y)))
      = if Some? (d.db y) then (holds_blk x d y; bk_same x x' d d' y (Some?.v (d.db y))) in
    FStar.Classical.forall_intro bl;
    let des (y: nat) : Lemma (iu x' y == true ==> Some? (d'.db y))
      = if iu x y then holds_iu x d y in
    FStar.Classical.forall_intro des;
    holds_intro x' d'

let step_roots (x: config pc) (d: dsc) (rs: list M.value)
  : Lemma (requires holds x d) (ensures holds (step pc x (ERoots rs)) ({ d with drt = rs }))
  = holds_def x d;
    holds_def (step pc x (ERoots rs)) ({ d with drt = rs })

/// ---------------------------------------------------------------------------
/// Young allocations
/// ---------------------------------------------------------------------------

let step_yalloc (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (o: nat) (ms': minor_state)
  : Lemma (requires holds x d /\ Y.yalloc d.dys sz tag vs == Some (o, ms') /\ tag <> M.infix_tag /\
                    L.length vs == sz /\ (forall (v: M.value). L.memP v vs ==> storable_w v))
          (ensures holds (step pc x (EYoungAlloc sz tag vs))
                         ({ d with dys = ms'; dym = M.young_alloc d.dym o sz tag vs;
                                   drt = M.VPtr (M.Young o) :: d.drt }))
  = holds_def x d;
    Y.yalloc_repr d.dym d.dys sz tag vs;
    holds_def (step pc x (EYoungAlloc sz tag vs))
              ({ d with dys = ms'; dym = M.young_alloc d.dym o sz tag vs; drt = M.VPtr (M.Young o) :: d.drt })

let ms1 (v: M.value) : GTot minor_state =
  match Y.yalloc ms0 1 0 [v] with Some (_, ms) -> ms | None -> ms0

let ms2 (v w: M.value) : GTot minor_state =
  match Y.yalloc (ms1 v) 1 0 [w] with Some (_, ms) -> ms | None -> ms0

#push-options "--fuel 1"
let yal1 (v: M.value)
  : Lemma (requires 4 <= ywords)
          (ensures Y.yalloc ms0 1 0 [v] == Some (0, ms1 v) /\ U64.v (ms1 v).bump == 16)
  = base_facts ()

let yal2 (v w: M.value)
  : Lemma (requires 4 <= ywords)
          (ensures Y.yalloc (ms1 v) 1 0 [w] == Some (2, ms2 v w))
  = base_facts ();
    yal1 v
#pop-options

let ym1 (v: M.value) : M.mheap = M.young_alloc (M.empty_heap ywords) 0 1 0 [v]
let ym2 (v w: M.value) : M.mheap = M.young_alloc (ym1 v) 2 1 0 [w]
