/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFAllocOk - one first-fit allocation, read as the model
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  From the byte facts of one first-fit allocation
/// (`FFBytes.alloc_bytes`) and the invariant after the Fill (`FFFill`), the
/// model facts the allocator contract asks for (`Iface.alloc_post`), on the
/// canonical readings before and after:
///   - the new block, with the size, tag and the colour the phase gives its
///     header (`colour_at`: black at or above the cursor mid-sweep);
///   - the blocks in use: those before, and the new one;
///   - every other block in use is unchanged;
///   - the reading after is well formed;
///   - the new block's words were free;
///   - after the program's Fill with values it may store, the invariant.
/// Idle allocation is mid-sweep allocation at the cursor where the sweep
/// stopped (`idle_is_sweeping`: the colours agree below it).  The word-level
/// lemmas reading the Fill back are the allocator-independent ones of
/// GC.Spec.Top.PagesAllocOk (`PAO`).

module GC.Spec.Top.FFAllocOk

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module I = GC.Spec.AllocIface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module W = GC.Spec.Walk
module Ph = GC.Spec.Phase
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AC = GC.Spec.Allocator.Cursor
module SPI = GC.Spec.SweepPhase.Intrinsic
module AT = GC.Spec.Pages.AllocTag
module FB = GC.Spec.Top.FFBytes
module FF = GC.Spec.Top.FFFill
module PAO = GC.Spec.Top.PagesAllocOk
module PIn = GC.Spec.Top.PagesInst

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Idle allocation is mid-sweep allocation where the sweep stopped
/// ---------------------------------------------------------------------------

/// Where the sweep is done, nothing is pending free.
let no_pending (c: U64.t) (g: heap) (x: obj_addr)
  : Lemma (requires SPI.sweep_done c) (ensures in_use (SPI.free_incremental c) g x == in_use free_stw g x)
  = ()

/// Below a done cursor, the phase's colour is white, as idle.
#push-options "--z3rlimit 40"
let idle_is_sweeping (c: U64.t) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t)
  : Lemma (requires SPI.sweep_done c /\ FB.ready g fp /\ wz >= 1)
          (ensures AP.alloc_at Ph.Idle g fp wz tag == AP.alloc_at (Ph.Sweeping c) g fp wz tag)
  = FB.ready_ok g fp;
    AC.alloc_phase_fields g fp Ph.Idle wz tag;
    AC.alloc_phase_fields g fp (Ph.Sweeping c) wz tag;
    AC.alloc_phase_heap g fp Ph.Idle wz tag;
    AC.alloc_phase_heap g fp (Ph.Sweeping c) wz tag;
    AP.alloc_at_obj_body_within_heap Ph.Idle g fp wz tag;
    AP.alloc_at_obj_wosize Ph.Idle g fp wz tag;
    let r1 = AP.alloc_at Ph.Idle g fp wz tag in
    let r2 = AP.alloc_at (Ph.Sweeping c) g fp wz tag in
    if r1.SA.obj_out <> 0UL then begin
      let x : obj_addr = r1.SA.obj_out in
      hd_address_spec x;
      assert (U64.v (hd_address x) < U64.v c);
      assert (Ph.allocation_color (Ph.Sweeping c) (hd_address x) == Ph.allocation_color Ph.Idle (hd_address x))
    end;
    assert (r1.SA.heap_out == r2.SA.heap_out /\ r1.SA.fp_out == r2.SA.fp_out /\ r1.SA.obj_out == r2.SA.obj_out)
#pop-options

/// ---------------------------------------------------------------------------
/// The invariant gives what an allocation needs
/// ---------------------------------------------------------------------------

/// What counts as free while the new block's fields are written.
let ffree_of (ph: T.phase U64.t) : free_def =
  match ph with
  | T.Sweeping c -> SPI.free_incremental c
  | _ -> free_stw

let ffree_of_ok (ph: T.phase U64.t) : Lemma (free_def_ok (ffree_of ph))
  = match ph with
    | T.Sweeping c -> SPI.free_incremental_ok c
    | _ -> free_stw_ok ()

let ready_of (ph: T.phase U64.t) (g: heap) (fp: U64.t)
  : Lemma (requires (match ph with
                     | T.Idle -> ishape g fp
                     | T.Marking -> mshape g fp
                     | T.Sweeping c -> sshape g fp c))
          (ensures FB.ready g fp /\ well_formed_heap_with (ffree_of ph) g)
  = wf_with_parts ();
    match ph with
    | T.Idle ->
      reveal_opaque (`%ishape) (ishape g fp);
      let c = FStar.IndefiniteDescription.indefinite_description_ghost U64.t (fun c -> idle_at g fp c) in
      SPI.sweep_inv_incremental_elim g fp c;
      FStar.Classical.forall_intro (no_pending c g);
      SPI.well_formed_heap_with_congr (SPI.free_incremental c) free_stw g
    | T.Marking -> reveal_opaque (`%mshape) (mshape g fp); W.reaches_end_of_dense g
    | T.Sweeping c ->
      reveal_opaque (`%sshape) (sshape g fp c);
      FF.ready_of_sweep g fp c;
      SPI.sweep_inv_incremental_elim g fp c

/// ---------------------------------------------------------------------------
/// The byte facts, sealed
/// ---------------------------------------------------------------------------

let used = PAO.used

[@@"opaque_to_smt"]
let fok (ph: T.phase U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (fp': U64.t) (x: obj_addr) : prop =
  FB.new_ok (gph ph) g wz tag g' x /\ FB.ready g' fp'

let fok_elim (ph: T.phase U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (fp': U64.t) (x: obj_addr)
  : Lemma (requires fok ph g wz tag g' fp' x) (ensures FB.new_ok (gph ph) g wz tag g' x /\ FB.ready g' fp')
  = reveal_opaque (`%fok) (fok ph g wz tag g' fp' x)

let fok_intro (ph: T.phase U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (fp': U64.t) (x: obj_addr)
  : Lemma (requires FB.new_ok (gph ph) g wz tag g' x /\ FB.ready g' fp') (ensures fok ph g wz tag g' fp' x)
  = reveal_opaque (`%fok) (fok ph g wz tag g' fp' x)

/// The phase's colour is the model's.
let colour_eq (ph: T.phase U64.t) (mo: nat)
  : Lemma (requires pos mo + 8 < heap_size)
          (ensures abs_col (Ph.allocation_color (gph ph) (hd_address (obj_of mo))) == T.colour_at ffk ph mo)
  = hd_of_obj mo

/// ---------------------------------------------------------------------------
/// The model facts
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let new_block (ph: T.phase U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (fp': U64.t) (x: obj_addr)
  : Lemma (requires fok ph g wz tag g' fp' x)
          (ensures (let mo = maddr x in
                    pos mo + 8 == U64.v x /\ obj_of mo == x /\
                    M.is_block (cabs g') mo /\
                    (cabs g').M.hd mo == Some ({ M.wz = wz; M.tag = U64.v tag; M.col = T.colour_at ffk ph mo }) /\
                    ~(used (cabs g) mo)))
  = fok_elim ph g wz tag g' fp' x;
    obj_maddr g' x;
    let mo = maddr x in
    abs_header g' mo;
    PAO.used_iff g mo;
    colour_eq ph mo
#pop-options

let use_rel (ph: T.phase U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (fp': U64.t) (x: obj_addr) (y: nat)
  : Lemma (requires fok ph g wz tag g' fp' x)
          (ensures used (cabs g') y <==> (used (cabs g) y \/ y == maddr x))
  = fok_elim ph g wz tag g' fp' x;
    PAO.used_iff g y; PAO.used_iff g' y;
    new_block ph g wz tag g' fp' x;
    if pos y + 8 < heap_size then begin
      let v = obj_of y in
      if v = x then maddr_obj y
      else assert (in_use free_stw g' v == in_use free_stw g v)
    end

/// A body word of a block in use before stays.
let body_same (g g': heap) (v: obj_addr) (b: hp_addr)
  : Lemma (requires I.others_unchanged g g' /\ Seq.mem v (objects zero_addr g) /\ ~(is_blue v g) /\
                    U64.v v <= U64.v b /\ U64.v b < U64.v v + U64.v (wosize_of_object v g) * 8)
          (ensures read_word g' b == read_word g b)
  = ()

/// Every other block in use keeps its header and fields.
#push-options "--z3rlimit 40"
let kept_block (ph: T.phase U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (fp': U64.t) (x: obj_addr) (y: nat)
  : Lemma (requires fok ph g wz tag g' fp' x /\ used (cabs g) y)
          (ensures (cabs g').M.hd y == (cabs g).M.hd y /\
                   (forall (i: nat). i < M.wz_of (cabs g) y ==> M.field (cabs g') y i == M.field (cabs g) y i))
  = fok_elim ph g wz tag g' fp' x;
    PAO.used_iff g y;
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
          wosize_of_object_spec v g;
          body_same g g' v (hp w)
        end in
    FStar.Classical.forall_intro fld
#pop-options

/// The reading after is well formed.
let wf_after (ph: T.phase U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (fp': U64.t) (x: obj_addr)
  : Lemma (requires fok ph g wz tag g' fp' x)
          (ensures M.well_formed (cabs g') /\ W.reaches g' zero_addr heap_size /\ no_infix_block g')
  = fok_elim ph g wz tag g' fp' x;
    abs_well_formed g';
    wf_cabs g'

/// The new block's words were free.
let words_free (ph: T.phase U64.t) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (fp': U64.t) (x: obj_addr) (w: nat)
  : Lemma (requires fok ph g wz tag g' fp' x /\ M.well_formed (cabs g) /\ M.covers (cabs g') (maddr x) w)
          (ensures exists (y: nat). M.covers (cabs g) y w /\ M.is_block (cabs g) y /\ M.col_of (cabs g) y == M.Blue)
  = wf_after ph g wz tag g' fp' x;
    new_block ph g wz tag g' fp' x;
    let mo = maddr x in
    assert (w < msize);
    let y = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun y -> M.covers (cabs g) y w) in
    if M.col_of (cabs g) y <> M.Blue then begin
      kept_block ph g wz tag g' fp' x y;
      assert (M.covers (cabs g') y w);
      assert (y == mo);
      use_rel ph g wz tag g' fp' x y
    end

/// ---------------------------------------------------------------------------
/// The invariant after the Fill
/// ---------------------------------------------------------------------------

/// A value the program may store, read on the byte heap before the
/// allocation: a pointer resolves to a block in use, not, mid-sweep, a white
/// block at or above the cursor.
let sound_f (ph: T.phase U64.t) (g: heap) (v: M.value) : prop =
  match v with
  | M.VPtr (M.Major b) ->
    exists (y: nat). M.resolve (cabs g) b == Some y /\ used (cabs g) y /\
      (match ph with T.Sweeping c -> ~(M.col_of (cabs g) y == M.White /\ pos y >= U64.v c) | _ -> True)
  | _ -> True

/// Mid-sweep, the cursor is a word address.
let aligned_ph (ph: T.phase U64.t) : prop =
  match ph with T.Sweeping c -> U64.v c % 8 == 0 | _ -> True

/// The heap the Fill makes, seen by the first-fit functions.
let fill_ctx (ph: T.phase U64.t) (g: heap) (wz: M.size_t) (tag: AP.tag_t) (g': heap) (fp': U64.t)
    (x: obj_addr) (vs: list M.value) (g3: heap) : prop =
  fok ph g wz tag g' fp' x /\ M.well_formed (cabs g) /\ L.length vs == wz /\ aligned_ph ph /\
  R.agree (M.fill (cabs g') (maddr x) vs) (abs g3) /\ low g3 == low g'

/// The target of a stored pointer is in use for what counts as free.
#push-options "--z3rlimit 40"
let target_use (ph: T.phase U64.t) (g g3: heap) (y: nat)
  : Lemma (requires used (cabs g) y /\ (abs g3).M.hd y == (cabs g).M.hd y /\
                    pos y + 8 < heap_size /\ Seq.mem (obj_of y) (objects zero_addr g3) /\ aligned_ph ph /\
                    (match ph with T.Sweeping c -> ~(M.col_of (cabs g) y == M.White /\ pos y >= U64.v c) | _ -> True))
          (ensures in_use (ffree_of ph) g3 (obj_of y))
  = abs_is_block g3 y;
    abs_header g3 y;
    abs_blue g3 y;
    let oy = obj_of y in
    obj_of_v y;
    is_white_iff oy g3;
    assert (Seq.mem oy (objects zero_addr g3) /\ ~(is_blue oy g3));
    assert (M.col_of (abs g3) y == M.col_of (cabs g) y);
    match ph with
    | T.Sweeping c ->
      if is_white oy g3 then begin
        assert (abs_col (color_of_object oy g3) == M.White);
        assert (pos y < U64.v c);
        base_facts ();
        assert (pos y % 8 == 0)
      end;
      assert (not (SPI.pending_free c g3 oy))
    | _ -> ()
#pop-options

#push-options "--z3rlimit 40"
let target_ok (ph: T.phase U64.t) (g g' g3: heap) (x: obj_addr) (mo wz: nat) (vs: list M.value)
    (v: U64.t) (b y: nat)
  : Lemma (requires M.tiled (cabs g') /\ M.is_block (cabs g') mo /\ M.wz_of (cabs g') mo == wz /\
                    L.length vs == wz /\ pos mo + 8 == U64.v x /\
                    used (cabs g) y /\ y <> mo /\ (cabs g').M.hd y == (cabs g).M.hd y /\
                    (forall (i: nat). i < M.wz_of (cabs g) y ==> M.field (cabs g') y i == M.field (cabs g) y i) /\
                    R.agree (M.fill (cabs g') mo vs) (abs g3) /\ M.resolve (cabs g) b == Some y /\
                    is_pointer v /\ pos b + 8 == U64.v v /\ b + 1 < msize /\ obj_of b == v /\
                    no_infix_block g3 /\ aligned_ph ph /\
                    (match ph with T.Sweeping c -> ~(M.col_of (cabs g) y == M.White /\ pos y >= U64.v c) | _ -> True))
          (ensures I.field_ok_with (ffree_of ph) g3 v /\ AT.away x wz v)
  = PAO.resolve_kept_m (cabs g) (cabs g') (abs g3) mo wz vs b y;
    ptr_resolve g3 b y;
    target_use ph g g3 y;
    PAO.away_arith x mo wz b v
#pop-options

/// A field the Fill writes holds a value the invariant accepts.
#push-options "--z3rlimit 40"
let inside_ok (ph: T.phase U64.t) (g: heap) (wz: M.size_t) (tag: AP.tag_t) (g': heap) (fp': U64.t)
    (x: obj_addr) (vs: list M.value) (g3: heap) (i: nat) (a: hp_addr)
  : Lemma (requires fill_ctx ph g wz tag g' fp' x vs g3 /\
                    (forall (v: M.value). L.memP v vs ==> sound_f ph g v) /\
                    U64.v a == U64.v x + 8 * i /\ i < wz /\
                    objects zero_addr g3 == objects zero_addr g' /\ no_infix_block g3)
          (ensures I.field_ok_with (ffree_of ph) g3 (read_word g3 a) /\ AT.away x wz (read_word g3 a))
  = wf_after ph g wz tag g' fp' x;
    new_block ph g wz tag g' fp' x;
    abs_well_formed g';
    let mo = maddr x in
    PAO.field_val g' g3 x mo wz vs i a;
    let v = read_word g3 a in
    L.lemma_index_memP vs i;
    if is_pointer v then begin
      ptr_decode v;
      let b = ptr_b v in
      let y = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun y -> M.resolve (cabs g) b == Some y /\ used (cabs g) y /\
                          (match ph with T.Sweeping c -> ~(M.col_of (cabs g) y == M.White /\ pos y >= U64.v c)
                                       | _ -> True)) in
      kept_block ph g wz tag g' fp' x y;
      target_ok ph g g' g3 x mo wz vs v b y
    end
#pop-options

let ins_at (ph: T.phase U64.t) (g: heap) (wz: M.size_t) (tag: AP.tag_t) (g': heap) (fp': U64.t)
    (x: obj_addr) (vs: list M.value) (g3: heap) (a: hp_addr)
  : Lemma (requires fill_ctx ph g wz tag g' fp' x vs g3 /\
                    (forall (v: M.value). L.memP v vs ==> sound_f ph g v) /\
                    objects zero_addr g3 == objects zero_addr g' /\ no_infix_block g3 /\
                    U64.v x <= U64.v a /\ U64.v a < U64.v x + 8 * wz)
          (ensures I.field_ok_with (ffree_of ph) g3 (read_word g3 a) /\ AT.away x wz (read_word g3 a))
  = PAO.field_index x wz a;
    inside_ok ph g wz tag g' fp' x vs g3 (PAO.fidx x a) a

/// The facts of the Fill's setting the word lemmas read.
let fill_basics (ph: T.phase U64.t) (g: heap) (wz: M.size_t) (tag: AP.tag_t) (g': heap) (fp': U64.t)
    (x: obj_addr) (vs: list M.value) (g3: heap)
  : Lemma (requires fill_ctx ph g wz tag g' fp' x vs g3)
          (ensures PAO.prep g' g3 (maddr x) wz vs /\ pos (maddr x) + 8 == U64.v x /\
                   Seq.mem x (objects zero_addr g') /\ U64.v (wosize_of_object x g') == wz /\
                   no_infix_block g' /\ (is_no_scan x g' <==> U64.v tag >= 251))
  = wf_after ph g wz tag g' fp' x;
    new_block ph g wz tag g' fp' x;
    abs_well_formed g';
    fok_elim ph g wz tag g' fp' x;
    PAO.noscan_tag x g' tag

let ins_all (ph: T.phase U64.t) (g: heap) (wz: M.size_t) (tag: AP.tag_t) (g': heap) (fp': U64.t)
    (x: obj_addr) (vs: list M.value) (g3: heap)
  : Lemma (requires fill_ctx ph g wz tag g' fp' x vs g3 /\
                    (forall (v: M.value). L.memP v vs ==> sound_f ph g v) /\
                    objects zero_addr g3 == objects zero_addr g' /\ no_infix_block g3 /\
                    U64.v (wosize_of_object x g') == wz)
          (ensures forall (a: hp_addr). U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 ==>
                     I.field_ok_with (ffree_of ph) g3 (read_word g3 a) /\
                     AT.away x (U64.v (wosize_of_object x g')) (read_word g3 a))
  = let ins (a: hp_addr)
      : Lemma (U64.v x <= U64.v a /\ U64.v a < U64.v x + wz * 8 ==>
               I.field_ok_with (ffree_of ph) g3 (read_word g3 a) /\ AT.away x wz (read_word g3 a))
      = if U64.v x <= U64.v a && U64.v a < U64.v x + wz * 8 then ins_at ph g wz tag g' fp' x vs g3 a in
    FStar.Classical.forall_intro ins

/// **The Fill writes the new block's fields away, with storable values.**
let fill_written (ph: T.phase U64.t) (g: heap) (wz: M.size_t) (tag: AP.tag_t) (g': heap) (fp': U64.t)
    (x: obj_addr) (vs: list M.value) (g3: heap)
  : Lemma (requires fill_ctx ph g wz tag g' fp' x vs g3 /\
                    (U64.v tag < 251 ==> (forall (v: M.value). L.memP v vs ==> sound_f ph g v)))
          (ensures AT.fields_written_away (ffree_of ph) g' g3 x)
  = fill_basics ph g wz tag g' fp' x vs g3;
    PAO.out_all g' g3 x (maddr x) wz vs;
    PAO.g3_walk g' g3 x wz;
    if not (is_no_scan x g') then ins_all ph g wz tag g' fp' x vs g3;
    PAO.fwa_intro (ffree_of ph) g' g3 x
