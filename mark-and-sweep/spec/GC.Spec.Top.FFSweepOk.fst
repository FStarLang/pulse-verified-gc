/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFSweepOk - akhil's fused sweep meets the sweep contract
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  One step of the fused sweep, restated with free meaning
/// blue, as GC.Spec.Top.PagesFree did for the page sweep (G16).  akhil's
/// statement of a step (`FusedSweep.Step.sweep_inv_incremental_step`) counts
/// the white blocks in front of the cursor as free (`free_incremental`), so
/// for it the blocks in use do not change.  With only blue free, a step frees
/// the white block at the cursor:
///   - `bfacts`: his facts of the step on the bytes, the heap in front of the
///     new cursor unchanged (GC.Spec.Top.FFStep), the walk to the end and
///     every block in use with a field;
///   - the model clauses of `Iface.sweep_step_post`, on the canonical
///     readings, from these and the tiling of both readings;
///   - `freed_words`: the words of the white block at the cursor, header
///     included (`FFSweep.ffw`), the model's sum.

module GC.Spec.Top.FFSweepOk

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
open GC.Spec.Top.FFSweep
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module FSS = GC.Spec.FusedSweep.Step
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPU = GC.Spec.SweepPhase.Util
module FF = GC.Spec.Top.FFFill
module FI = GC.Spec.Top.FFInst
module FST = GC.Spec.Top.FFStep
module PIn = GC.Spec.Top.PagesInst
module PAO = GC.Spec.Top.PagesAllocOk
module Mark = GC.Spec.Mark
module FAO = GC.Spec.Top.FFAllocOk

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The byte facts of one step
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let bfacts (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) : prop =
  sshape g' fp' c' /\ U64.v c < U64.v c' /\ U64.v c + 8 < heap_size /\
  W.reaches g zero_addr (U64.v c) /\ W.can_step g c /\ U64.v c' == W.bnext g c /\
  W.reaches g zero_addr heap_size /\ nz g /\
  (forall (x: obj_addr). in_use (SPI.free_incremental c') g' x == in_use (SPI.free_incremental c) g x) /\
  (forall (x: obj_addr). in_use (SPI.free_incremental c) g x ==> SPI.same_block g g' (hd_address x)) /\
  (forall (x: obj_addr). SPI.pending_free c' g' x ==> SPI.pending_free c g x) /\
  (forall (a: hp_addr). U64.v a >= U64.v c' ==> read_word g' a == read_word g a)

let bfacts_elim (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires bfacts c g fp g' fp' c')
          (ensures sshape g' fp' c' /\ U64.v c < U64.v c' /\ U64.v c + 8 < heap_size /\
                   W.reaches g zero_addr (U64.v c) /\ W.can_step g c /\
                   U64.v c' == W.bnext g c /\
                   W.reaches g zero_addr heap_size /\ nz g /\
                   (forall (x: obj_addr). in_use (SPI.free_incremental c') g' x == in_use (SPI.free_incremental c) g x) /\
                   (forall (x: obj_addr). in_use (SPI.free_incremental c) g x ==> SPI.same_block g g' (hd_address x)) /\
                   (forall (x: obj_addr). SPI.pending_free c' g' x ==> SPI.pending_free c g x) /\
                   (forall (a: hp_addr). U64.v a >= U64.v c' ==> read_word g' a == read_word g a))
  = reveal_opaque (`%bfacts) (bfacts c g fp g' fp' c')

/// The walk from the new cursor on is the walk before.
#push-options "--z3rlimit 40"
let walk_on (g g': heap) (c c': nat)
  : Lemma (requires W.reaches g zero_addr c /\ c < heap_size /\ c % 8 == 0 /\ W.can_step g (mk_hp_addr c) /\
                    c' == W.bnext g (mk_hp_addr c) /\ W.reaches g zero_addr heap_size /\
                    W.reaches g' zero_addr c' /\
                    (forall (a: hp_addr). U64.v a >= c' ==> read_word g' a == read_word g a))
          (ensures W.reaches g' zero_addr heap_size)
  = W.reaches_snoc g zero_addr (mk_hp_addr c);
    W.reaches_bounds g zero_addr c';
    if c' < heap_size then begin
      let ca = mk_hp_addr c' in
      W.reaches_det g zero_addr ca heap_size;
      W.walk_frame_from g g' ca;
      W.reaches_trans g' zero_addr ca heap_size
    end
#pop-options

/// A block's header in front of the new cursor is the one before.
let ahead_hd (g g': heap) (c': nat) (x: obj_addr)
  : Lemma (requires (forall (a: hp_addr). U64.v a >= c' ==> read_word g' a == read_word g a) /\
                    U64.v x > c' /\ c' % 8 == 0)
          (ensures read_word g' (hd_address x) == read_word g (hd_address x))
  = hd_address_spec x

/// Every block in use has a field after the step.
#push-options "--z3rlimit 40"
let nz_after (c c': U64.t) (g g': heap)
  : Lemma (requires nz g /\ U64.v c' % 8 == 0 /\
                    (forall (x: obj_addr). in_use (SPI.free_incremental c') g' x == in_use (SPI.free_incremental c) g x) /\
                    (forall (x: obj_addr). in_use (SPI.free_incremental c) g x ==> SPI.same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). SPI.pending_free c' g' x ==> SPI.pending_free c g x) /\
                    (forall (a: hp_addr). U64.v a >= U64.v c' ==> read_word g' a == read_word g a))
          (ensures nz g')
  = let one (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') ==> U64.v (wosize_of_object x g') >= 1)
      = if Seq.mem x (objects zero_addr g') && not (is_blue x g') then begin
          SPI.colour_of g x; SPI.colour_of g' x;
          hd_address_spec x;
          if SPI.pending_free c' g' x then begin
            ahead_hd g g' (U64.v c') x;
            wosize_of_object_spec x g; wosize_of_object_spec x g'
          end
          else assert (in_use (SPI.free_incremental c) g x)
        end in
    FStar.Classical.forall_intro one
#pop-options

/// **One step's byte facts.**
#push-options "--z3rlimit 40"
let bstep (c: hp_addr) (g: heap) (fp: U64.t)
  : Lemma (requires sshape g fp c /\ U64.v c + 8 < heap_size)
          (ensures FS.can_sweep g (SPI.state_at g c) /\
                   (let (g', fp', st') = FS.sweep_step g fp (SPI.state_at g c) in
                    bfacts c g fp g' fp' st'.FS.cursor))
  = reveal_opaque (`%sshape) (sshape g fp c);
    FSS.sweep_inv_incremental_step g fp c;
    SPI.sweep_inv_incremental_elim g fp c;
    let st = SPI.state_at g c in
    let (g', fp', st') = FS.sweep_step g fp st in
    let c' = st'.FS.cursor in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (FST.step_front g fp c));
    SPI.sweep_inv_incremental_elim g' fp' c';
    walk_on g g' (U64.v c) (U64.v c');
    SPI.free_incremental_ok c;
    nz_after c c' g g';
    reveal_opaque (`%sshape) (sshape g' fp' c');
    reveal_opaque (`%bfacts) (bfacts c g fp g' fp' c')
#pop-options

/// ---------------------------------------------------------------------------
/// What happens to each block, on the bytes
/// ---------------------------------------------------------------------------

/// The facts of a step, unsealed where a lemma needs them.
let ctx (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) : prop =
  bfacts c g fp g' fp' c' /\ SPI.sweep_inv_incremental g fp c

let ctx_open (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c')
          (ensures (let n = U64.v c in let n' = U64.v c' in
                    SPI.sweep_inv_incremental g' fp' c' /\ n < n' /\ n + 8 < heap_size /\
                    W.reaches g zero_addr n /\ W.can_step g c /\ n' == W.bnext g c /\ n' % 8 == 0 /\ n % 8 == 0 /\
                    W.reaches g zero_addr heap_size /\ W.reaches g' zero_addr heap_size /\ nz g /\ nz g' /\
                    SPI.behind_swept g n /\ SPI.behind_swept g' n' /\ SPI.front_unswept g n /\
                    W.reaches g' zero_addr n' /\
                    (forall (x: obj_addr). in_use (SPI.free_incremental c') g' x == in_use (SPI.free_incremental c) g x) /\
                    (forall (x: obj_addr). in_use (SPI.free_incremental c) g x ==> SPI.same_block g g' (hd_address x)) /\
                    (forall (x: obj_addr). SPI.pending_free c' g' x ==> SPI.pending_free c g x) /\
                    (forall (a: hp_addr). U64.v a >= U64.v c' ==> read_word g' a == read_word g a)))
  = bfacts_elim c g fp g' fp' c';
    reveal_opaque (`%sshape) (sshape g' fp' c');
    SPI.sweep_inv_incremental_elim g fp c;
    SPI.sweep_inv_incremental_elim g' fp' c'

/// An object at or in front of the new cursor is one before, with its
/// header and body.
#push-options "--z3rlimit 40"
let ahead_obj (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (x: obj_addr)
  : Lemma (requires ctx c g fp g' fp' c' /\ U64.v (hd_address x) >= U64.v c')
          (ensures (Seq.mem x (objects zero_addr g') <==> Seq.mem x (objects zero_addr g)) /\
                   read_word g' (hd_address x) == read_word g (hd_address x) /\
                   (forall (b: hp_addr). U64.v b > U64.v (hd_address x) ==> read_word g' b == read_word g b))
  = ctx_open c g fp g' fp' c';
    hd_address_spec x;
    let q = hd_address x in
    W.objects_mem_iff g zero_addr x;
    W.objects_mem_iff g' zero_addr x;
    if U64.v q < heap_size then begin
      let ca : hp_addr = mk_hp_addr (U64.v c') in
      W.reaches_bounds g' zero_addr (U64.v c');
      W.reaches_snoc g zero_addr c;
      W.walk_frame_from g g' ca;
      (if W.reaches g zero_addr (U64.v q) then begin
         W.reaches_det g zero_addr ca (U64.v q);
         W.reaches_trans g' zero_addr ca (U64.v q)
       end);
      (if W.reaches g' zero_addr (U64.v q) then begin
         W.reaches_det g' zero_addr ca (U64.v q);
         W.reaches_trans g zero_addr ca (U64.v q)
       end)
    end
#pop-options

/// A block in use behind the cursor is white, before and after.
let behind_white (g: heap) (n: nat) (x: obj_addr)
  : Lemma (requires SPI.behind_swept g n /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    U64.v (hd_address x) < n)
          (ensures is_white x g)
  = SPI.obj_pos g x;
    SPI.colour_of g x;
    SPI.behind_swept_elim g n (hd_address x)

/// **Outside the cursor's block, a block in use stays, with its header and
/// body.**
#push-options "--z3rlimit 40"
let kept_out (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (x: obj_addr)
  : Lemma (requires ctx c g fp g' fp' c' /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    (U64.v (hd_address x) < U64.v c \/ U64.v (hd_address x) >= U64.v c'))
          (ensures Seq.mem x (objects zero_addr g') /\ ~(is_blue x g') /\
                   read_word g' (hd_address x) == read_word g (hd_address x) /\
                   (forall (b: hp_addr). U64.v (hd_address x) < U64.v b /\ U64.v b < W.bnext g (hd_address x) ==>
                      read_word g' b == read_word g b))
  = ctx_open c g fp g' fp' c';
    SPI.colour_of g x;
    SPI.obj_pos g x;
    if U64.v (hd_address x) >= U64.v c' then begin
      ahead_obj c g fp g' fp' c' x;
      SPI.colour_of g' x
    end
    else begin
      // behind the cursor: in use (not pending), so kept, and white both times
      hd_address_spec x;
      assert (not (SPI.pending_free c g x));
      assert (in_use (SPI.free_incremental c) g x);
      assert (in_use (SPI.free_incremental c') g' x);
      assert (SPI.same_block g g' (hd_address x));
      behind_white g (U64.v c) x;
      behind_white g' (U64.v c') x;
      SPI.colour_of g' x;
      SPU.header_eq (read_word g' (hd_address x)) (read_word g (hd_address x))
    end
#pop-options

/// The object of the block at the cursor.
let xc (c: hp_addr) : obj_addr = if U64.v c + 8 < heap_size then f_address c else mword

/// The block at the cursor is a block before.
let cur_obj (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c')
          (ensures Seq.mem (xc c) (objects zero_addr g) /\ hd_address (xc c) == c /\ U64.v (xc c) == U64.v c + 8)
  = ctx_open c g fp g' fp' c';
    f_address_spec c;
    hd_address_spec (xc c);
    SPI.obj_pos g (xc c)

/// **A black block at the cursor turns white, with its contents.**
#push-options "--z3rlimit 40"
let black_cur (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c' /\ FSI.black_at g c)
          (ensures Seq.mem (xc c) (objects zero_addr g') /\ is_white (xc c) g' /\
                   SPI.same_block g g' c)
  = ctx_open c g fp g' fp' c';
    cur_obj c g fp g' fp' c';
    let x = xc c in
    SPI.colour_of g x;
    assert (in_use (SPI.free_incremental c) g x);
    assert (in_use (SPI.free_incremental c') g' x);
    SPI.colour_of g' x;
    SPI.obj_pos g' x;
    SPI.behind_swept_elim g' (U64.v c') c
#pop-options

/// **A white block at the cursor is freed.**
#push-options "--z3rlimit 40"
let white_cur (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c' /\ SPI.white_at g c)
          (ensures ~(Seq.mem (xc c) (objects zero_addr g') /\ ~(is_blue (xc c) g')))
  = ctx_open c g fp g' fp' c';
    cur_obj c g fp g' fp' c';
    let x = xc c in
    SPI.colour_of g x;
    assert (SPI.pending_free c g x);
    assert (~(in_use (SPI.free_incremental c') g' x))
#pop-options

/// **Nothing comes into use.**
let after_was (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (x: obj_addr)
  : Lemma (requires ctx c g fp g' fp' c' /\ Seq.mem x (objects zero_addr g') /\ ~(is_blue x g'))
          (ensures Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
  = ctx_open c g fp g' fp' c';
    if SPI.pending_free c' g' x then ()
    else assert (in_use (SPI.free_incremental c) g x)

/// ---------------------------------------------------------------------------
/// On the model
/// ---------------------------------------------------------------------------

let used = PAO.used

/// A block kept with its header and body keeps its model block.
#push-options "--z3rlimit 40"
let kept_model (g g': heap) (y: nat)
  : Lemma (requires pos y + 8 < heap_size /\ Seq.mem (obj_of y) (objects zero_addr g) /\
                    Seq.mem (obj_of y) (objects zero_addr g') /\
                    read_word g' (hd_address (obj_of y)) == read_word g (hd_address (obj_of y)) /\
                    (forall (b: hp_addr). U64.v (hd_address (obj_of y)) < U64.v b /\
                       U64.v b < W.bnext g (hd_address (obj_of y)) ==> read_word g' b == read_word g b))
          (ensures (cabs g').M.hd y == (cabs g).M.hd y /\ M.is_block (cabs g) y /\
                   (forall (i: nat). i < M.wz_of (cabs g) y ==> M.field (cabs g') y i == M.field (cabs g) y i))
  = let v = obj_of y in
    hd_of_obj y;
    abs_is_block g y; abs_is_block g' y;
    assert (word g' y == word g y);
    let fld (i: nat) : Lemma (i < M.wz_of (cabs g) y ==> M.field (cabs g') y i == M.field (cabs g) y i)
      = if i < M.wz_of (cabs g) y then begin
          let w = y + 1 + i in
          abs_header g y;
          assert (M.covers (abs g) y w /\ M.covers (abs g') y w);
          is_fw_iff g w; is_fw_iff g' w;
          msize_pos w;
          abs_field g y i;
          abs_field g' y i;
          wosize_of_object_spec v g;
          assert (U64.v (hp w) == U64.v v + 8 * i);
          assert (U64.v (hd_address v) < U64.v (hp w) /\ U64.v (hp w) < W.bnext g (hd_address v));
          assert (read_word g' (hp w) == read_word g (hp w))
        end in
    FStar.Classical.forall_intro fld
#pop-options

/// The block at the cursor, on the model.
let oc (c: hp_addr) : nat = maddr (xc c)

#push-options "--z3rlimit 40"
let oc_facts (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c')
          (ensures (let o = oc c in
                    pos o == U64.v c /\ obj_of o == xc c /\ M.is_block (cabs g) o /\
                    U64.v c' == pos (o + M.wz_of (cabs g) o + 1) /\ o < msize))
  = ctx_open c g fp g' fp' c';
    cur_obj c g fp g' fp' c';
    obj_maddr g (xc c);
    let o = oc c in
    abs_header g o;
    wosize_of_object_spec (xc c) g;
    abs_is_block g o
#pop-options

let pos_order (a b: nat) : Lemma ((pos a <= pos b <==> a <= b) /\ (pos a < pos b <==> a < b)) = ()

/// The cursor's block is the only block of the region.
let in_region (c: hp_addr) (c': U64.t) (o: nat) : bool = U64.v c <= pos o && pos o < U64.v c'

#push-options "--z3rlimit 40"
let region_one (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (o: nat)
  : Lemma (requires ctx c g fp g' fp' c' /\ M.well_formed (cabs g) /\ M.is_block (cabs g) o /\ in_region c c' o)
          (ensures o == oc c)
  = oc_facts c g fp g' fp' c';
    let oo = oc c in
    pos_order oo o;
    pos_order o (oo + M.wz_of (cabs g) oo + 1);
    assert (oo <= o /\ o <= oo + M.wz_of (cabs g) oo);
    assert (M.covers (cabs g) oo o);
    assert (M.covers (cabs g) o o)
#pop-options

/// Field `i` of the block at `y` lies in its body.
let in_block (g: heap) (y i: nat)
  : Lemma (requires pos y + 8 < heap_size /\ i < U64.v (wosize_of_object (obj_of y) g) /\ pos (y + 1 + i) < heap_size)
          (ensures U64.v (hd_address (obj_of y)) < U64.v (hp (y + 1 + i)) /\
                   U64.v (hp (y + 1 + i)) < W.bnext g (hd_address (obj_of y)))
  = obj_of_v y;
    hd_address_spec (obj_of y);
    wosize_of_object_spec (obj_of y) g

/// Same size, tag and body: same contents on the model.
#push-options "--z3rlimit 40"
let contents_model (g g': heap) (y: nat)
  : Lemma (requires pos y + 8 < heap_size /\ Seq.mem (obj_of y) (objects zero_addr g) /\
                    Seq.mem (obj_of y) (objects zero_addr g') /\
                    SPI.same_block g g' (hd_address (obj_of y)))
          (ensures M.same_contents (cabs g) (cabs g') y)
  = let v = obj_of y in
    hd_of_obj y;
    obj_of_v y;
    hd_address_spec v;
    abs_is_block g y; abs_is_block g' y;
    abs_header g y; abs_header g' y;
    wosize_of_object_spec v g; wosize_of_object_spec v g';
    tag_of_object_spec v g; tag_of_object_spec v g';
    let fld (i: nat) : Lemma (i < M.wz_of (cabs g) y ==> M.field (cabs g') y i == M.field (cabs g) y i)
      = if i < M.wz_of (cabs g) y then begin
          let w = y + 1 + i in
          assert (M.covers (abs g) y w /\ M.covers (abs g') y w);
          is_fw_iff g w; is_fw_iff g' w;
          msize_pos w;
          abs_field g y i;
          abs_field g' y i;
          in_block g y i;
          assert (read_word g' (hp w) == read_word g (hp w))
        end in
    FStar.Classical.forall_intro fld
#pop-options

/// A block in use after was in use before.
let used_after (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (o: nat)
  : Lemma (requires ctx c g fp g' fp' c' /\ used (cabs g') o) (ensures used (cabs g) o)
  = PAO.used_iff g' o; PAO.used_iff g o;
    after_was c g fp g' fp' c' (obj_of o)

/// A block in use outside the region stays, with its block.
#push-options "--z3rlimit 40"
let kept_m (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (o: nat)
  : Lemma (requires ctx c g fp g' fp' c' /\ used (cabs g) o /\ not (in_region c c' o))
          (ensures used (cabs g') o /\ M.same_block (cabs g) (cabs g') o)
  = PAO.used_iff g o;
    hd_of_obj o;
    obj_of_v o;
    hd_address_spec (obj_of o);
    kept_out c g fp g' fp' c' (obj_of o);
    PAO.used_iff g' o;
    kept_model g g' o
#pop-options

/// The block at the cursor, black: white after, same contents.
#push-options "--z3rlimit 40"
let black_m (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c' /\ used (cabs g) (oc c) /\ M.col_of (cabs g) (oc c) == M.Black)
          (ensures used (cabs g') (oc c) /\ M.col_of (cabs g') (oc c) == M.White /\
                   M.same_contents (cabs g) (cabs g') (oc c))
  = oc_facts c g fp g' fp' c';
    let o = oc c in
    let x = xc c in
    abs_header g o;
    is_black_iff x g;
    SPI.colour_of g x;
    black_cur c g fp g' fp' c';
    obj_maddr g' x;
    abs_header g' o;
    is_white_iff x g';
    Mark.colors_exclusive x g';
    PAO.used_iff g' o;
    cur_obj c g fp g' fp' c';
    assert (obj_of o == x /\ hd_address x == c);
    contents_model g g' o
#pop-options

/// The block at the cursor, white: freed.
#push-options "--z3rlimit 40"
let white_m (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c' /\ used (cabs g) (oc c) /\ M.col_of (cabs g) (oc c) == M.White)
          (ensures ~(used (cabs g') (oc c)))
  = oc_facts c g fp g' fp' c';
    let o = oc c in
    let x = xc c in
    abs_header g o;
    is_white_iff x g;
    SPI.colour_of g x;
    white_cur c g fp g' fp' c';
    PAO.used_iff g' o
#pop-options

/// ---------------------------------------------------------------------------
/// Words
/// ---------------------------------------------------------------------------

/// Both readings are well formed.
let wf_both (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c')
          (ensures M.well_formed (cabs g) /\ M.well_formed (cabs g'))
  = ctx_open c g fp g' fp' c';
    bfacts_elim c g fp g' fp' c';
    reveal_opaque (`%sshape) (sshape g fp c);
    FAO.ready_of (T.Sweeping c) g fp;
    FAO.ready_of (T.Sweeping c') g' fp';
    wf_with_parts ();
    abs_well_formed g; wf_cabs g;
    abs_well_formed g'; wf_cabs g'

/// The colours of a block in use, without grey.
let used_col (gm: M.mheap) (o: nat)
  : Lemma (requires used gm o /\ T.no_grey gm) (ensures M.col_of gm o == M.White \/ M.col_of gm o == M.Black)
  = ()

/// The block covering a word.
let cover_of (gm: M.mheap) (w: nat) : Ghost nat (requires M.well_formed gm /\ w < gm.M.size)
                                              (ensures fun o -> M.covers gm o w)
  = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers gm o w)

let tile_uniq (gm: M.mheap) (o1 o2 w: nat)
  : Lemma (requires M.well_formed gm /\ M.covers gm o1 w /\ M.covers gm o2 w) (ensures o1 == o2)
  = ()

/// A block covering a word, kept with its size, covers it after.
let covers_kept (gm gm': M.mheap) (o w: nat)
  : Lemma (requires M.covers gm o w /\ M.is_block gm' o /\ M.wz_of gm' o == M.wz_of gm o)
          (ensures M.covers gm' o w)
  = ()

/// **The words of the white block at the cursor are free after.**
#push-options "--z3rlimit 40"
let words_white (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (w: nat)
  : Lemma (requires ctx c g fp g' fp' c' /\ used (cabs g) (oc c) /\ M.col_of (cabs g) (oc c) == M.White /\
                    M.covers (cabs g) (oc c) w)
          (ensures exists (o': nat). M.covers (cabs g') o' w /\ M.is_block (cabs g') o' /\ M.col_of (cabs g') o' == M.Blue)
  = wf_both c g fp g' fp' c';
    white_m c g fp g' fp' c';
    oc_facts c g fp g' fp' c';
    let o' = cover_of (cabs g') w in
    if used (cabs g') o' then begin
      used_after c g fp g' fp' c' o';
      if in_region c c' o' then region_one c g fp g' fp' c' o'
      else begin
        kept_m c g fp g' fp' c' o';
        covers_kept (cabs g') (cabs g) o' w;
        tile_uniq (cabs g) o' (oc c) w
      end
    end
#pop-options

/// **Free words stay free.**
#push-options "--z3rlimit 40"
let words_kept (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (w: nat) (o: nat)
  : Lemma (requires ctx c g fp g' fp' c' /\ T.no_grey (cabs g) /\
                    M.covers (cabs g) o w /\ M.col_of (cabs g) o == M.Blue)
          (ensures exists (o': nat). M.covers (cabs g') o' w /\ M.is_block (cabs g') o' /\ M.col_of (cabs g') o' == M.Blue)
  = wf_both c g fp g' fp' c';
    oc_facts c g fp g' fp' c';
    let o' = cover_of (cabs g') w in
    if used (cabs g') o' then begin
      used_after c g fp g' fp' c' o';
      if in_region c c' o' then begin
        region_one c g fp g' fp' c' o';
        used_col (cabs g) (oc c);
        if M.col_of (cabs g) (oc c) = M.White then white_m c g fp g' fp' c'
        else begin
          black_m c g fp g' fp' c';
          covers_kept (cabs g') (cabs g) o' w;
          tile_uniq (cabs g) o' o w
        end
      end
      else begin
        kept_m c g fp g' fp' c' o';
        covers_kept (cabs g') (cabs g) o' w;
        tile_uniq (cabs g) o' o w
      end
    end
#pop-options

/// **A free word after was free, or a word of the white block at the
/// cursor.**
#push-options "--z3rlimit 40"
let words_back (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (w: nat) (o': nat)
  : Lemma (requires ctx c g fp g' fp' c' /\ T.no_grey (cabs g) /\
                    M.covers (cabs g') o' w /\ M.col_of (cabs g') o' == M.Blue)
          (ensures (exists (o: nat). M.covers (cabs g) o w /\ M.is_block (cabs g) o /\ M.col_of (cabs g) o == M.Blue) \/
                   (M.covers (cabs g) (oc c) w /\ used (cabs g) (oc c) /\ M.col_of (cabs g) (oc c) == M.White))
  = wf_both c g fp g' fp' c';
    oc_facts c g fp g' fp' c';
    let o = cover_of (cabs g) w in
    if used (cabs g) o then begin
      if in_region c c' o then begin
        region_one c g fp g' fp' c' o;
        used_col (cabs g) o;
        if M.col_of (cabs g) o = M.Black then begin
          black_m c g fp g' fp' c';
          covers_kept (cabs g) (cabs g') o w;
          tile_uniq (cabs g') o o' w
        end
      end
      else begin
        kept_m c g fp g' fp' c' o;
        covers_kept (cabs g) (cabs g') o w;
        tile_uniq (cabs g') o o' w
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The words freed
/// ---------------------------------------------------------------------------

/// The byte count is the white block's words at the cursor.
#push-options "--z3rlimit 40"
let freed_cur (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c')
          (ensures ffw g c == (if used (cabs g) (oc c) && M.col_of (cabs g) (oc c) = M.White
                               then M.wz_of (cabs g) (oc c) + 1 else 0))
  = oc_facts c g fp g' fp' c';
    cur_obj c g fp g' fp' c';
    let o = oc c in
    let x = xc c in
    abs_header g o;
    is_white_iff x g;
    SPI.colour_of g x;
    wosize_of_object_spec x g;
    hd_address_spec x
#pop-options

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

/// The step's context, from its precondition.
let pre_ctx (c: U64.t) (h: heap) (s: ffst)
  : Lemma (requires ffinv (T.Sweeping c) h s /\ U64.v c + 8 < heap_size)
          (ensures (let g = gl h s in
                    U64.v c % 8 == 0 /\
                    (let cc : hp_addr = c in
                     FS.can_sweep g (SPI.state_at g c) /\
                     (let (g', fp', st') = FS.sweep_step g s.fp (SPI.state_at g c) in
                      ctx cc g s.fp g' fp' st'.FS.cursor))))
  = let g = gl h s in
    reveal_opaque (`%sshape) (sshape g s.fp c);
    SPI.sweep_inv_incremental_elim g s.fp c;
    bstep (c <: hp_addr) g s.fp

/// In use and free words, read on the canonical readings.
let use_at (m: M.mheap) (h: heap) (s: ffst) (o: nat)
  : Lemma (requires R.heq m (cabs (gl h s)))
          (ensures T.in_use ffa s h m o == used (cabs (gl h s)) o)
  = cabs_set_low h s.lo;
    R.heq_trans m (cabs (gl h s)) (cabs h);
    FI.in_use_used m h s (gl h s) o

let fw_at (m: M.mheap) (h: heap) (s: ffst) (w: nat)
  : Lemma (requires R.heq m (cabs (gl h s)))
          (ensures T.free_word ffa s h m w <==>
                   (exists (o: nat). M.covers (cabs (gl h s)) o w /\ M.is_block (cabs (gl h s)) o /\
                                     M.col_of (cabs (gl h s)) o == M.Blue))
  = cabs_set_low h s.lo;
    FStar.Classical.forall_intro (FI.ffree_blue h s (gl h s))

/// The state after the step.
let after (g': heap) (fp': U64.t) : ffst = { fp = fp'; lo = low g' }

let gl_after (g': heap) (fp': U64.t) : Lemma (gl g' (after g' fp') == g') = set_low_self g'

/// The model clauses, on the canonical readings, with `m` read as `cabs g`.
#push-options "--z3rlimit 40"
let blocks_m (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (o: nat)
  : Lemma (requires ctx c g fp g' fp' c' /\ T.no_grey (cabs g))
          (ensures (let gm = cabs g in let gm' = cabs g' in
                    (used gm o /\ in_region c c' o /\ M.col_of gm o == M.White ==> ~(used gm' o)) /\
                    (used gm o /\ in_region c c' o /\ M.col_of gm o == M.Black ==>
                       used gm' o /\ M.col_of gm' o == M.White /\ M.same_contents gm gm' o) /\
                    (used gm o /\ not (in_region c c' o) ==> used gm' o /\ M.same_block gm gm' o) /\
                    (used gm' o ==> used gm o)))
  = wf_both c g fp g' fp' c';
    (if used (cabs g') o then used_after c g fp g' fp' c' o);
    if used (cabs g) o then begin
      if in_region c c' o then begin
        region_one c g fp g' fp' c' o;
        used_col (cabs g) o;
        if M.col_of (cabs g) o = M.White then white_m c g fp g' fp' c'
        else black_m c g fp g' fp' c'
      end
      else kept_m c g fp g' fp' c' o
    end
#pop-options

let oc_region (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t)
  : Lemma (requires ctx c g fp g' fp' c') (ensures in_region c c' (oc c))
  = oc_facts c g fp g' fp' c';
    pos_order (oc c) (oc c + M.wz_of (cabs g) (oc c) + 1)

#push-options "--z3rlimit 40"
let words_m (c: hp_addr) (g: heap) (fp: U64.t) (g': heap) (fp': U64.t) (c': U64.t) (w: nat)
  : Lemma (requires ctx c g fp g' fp' c' /\ T.no_grey (cabs g))
          (ensures (let gm = cabs g in let gm' = cabs g' in
                    let fwd (k: M.mheap) = exists (o: nat). M.covers k o w /\ M.is_block k o /\ M.col_of k o == M.Blue in
                    (fwd gm ==> fwd gm') /\
                    (fwd gm' ==> fwd gm \/ (exists (o: nat). M.covers gm o w /\ used gm o /\ in_region c c' o /\
                                                         M.col_of gm o == M.White)) /\
                    (forall (o: nat). used gm o /\ in_region c c' o /\ M.col_of gm o == M.White /\ M.covers gm o w ==>
                       fwd gm')))
  = wf_both c g fp g' fp' c';
    oc_facts c g fp g' fp' c';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (words_kept c g fp g' fp' c' w));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (words_back c g fp g' fp' c' w));
    let sw (o: nat)
      : Lemma (requires used (cabs g) o /\ in_region c c' o /\ M.col_of (cabs g) o == M.White /\ M.covers (cabs g) o w)
              (ensures exists (o': nat). M.covers (cabs g') o' w /\ M.is_block (cabs g') o' /\ M.col_of (cabs g') o' == M.Blue)
      = region_one c g fp g' fp' c' o;
        words_white c g fp g' fp' c' w in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sw);
    oc_region c g fp g' fp' c'
#pop-options

/// The step's results, named.
let sres (c: U64.t) (h: heap) (s: ffst) : GTot (heap & U64.t & U64.t) =
  let g = gl h s in
  let st = SPI.state_at g c in
  if FS.can_sweep g st then begin
    let (g', fp', st') = FS.sweep_step g s.fp st in
    (g', fp', st'.FS.cursor)
  end
  else (g, s.fp, c)

/// The record's step is akhil's step.
let step_is (c: U64.t) (h: heap) (s: ffst)
  : Lemma (requires ffinv (T.Sweeping c) h s /\ U64.v c + 8 < heap_size)
          (ensures (let (g', fp', c') = sres c h s in
                    ffsweep.T.step c h s == (c', g', after g' fp', { T.units = 1; T.freed_words = ffw (gl h s) c })))
  = pre_ctx c h s

/// The context of a step, read on the record.
let sctx (c: U64.t) (h: heap) (s: ffst) (m: M.mheap) : prop =
  U64.v c % 8 == 0 /\ U64.v c + 8 < heap_size /\ R.heq m (cabs (gl h s)) /\ T.no_grey (cabs (gl h s)) /\
  (let (g', fp', c') = sres c h s in ctx (c <: hp_addr) (gl h s) s.fp g' fp' c')

let sctx_intro (c: U64.t) (h: heap) (s: ffst) (m: M.mheap)
  : Lemma (requires brepr m h /\ T.sweep_step_pre ffsweep c h s m) (ensures sctx c h s m)
  = pre_ctx c h s;
    FI.heq_low m h s

/// Blocks, on the record.
#push-options "--z3rlimit 40"
let clause_blocks (c: U64.t) (h: heap) (s: ffst) (m: M.mheap) (o: nat)
  : Lemma (requires sctx c h s m)
          (ensures (let (g', fp', c') = sres c h s in
                    let s' = after g' fp' in
                    (T.swept_white ffa s h m c c' o ==> T.in_use ffa s' g' (cabs g') o == false) /\
                    (T.in_use ffa s h m o /\ T.region ffk c c' o /\ M.col_of m o == M.Black ==>
                       T.in_use ffa s' g' (cabs g') o /\ M.col_of (cabs g') o == M.White /\
                       M.same_contents m (cabs g') o) /\
                    (T.in_use ffa s h m o /\ not (T.region ffk c c' o) ==>
                       T.in_use ffa s' g' (cabs g') o /\ M.same_block m (cabs g') o) /\
                    (T.in_use ffa s' g' (cabs g') o ==> T.in_use ffa s h m o)))
  = let (g', fp', c') = sres c h s in
    let g = gl h s in
    use_at m h s o;
    gl_after g' fp';
    R.heq_refl (cabs g');
    use_at (cabs g') g' (after g' fp') o;
    blocks_m (c <: hp_addr) g s.fp g' fp' c' o;
    assert (T.region ffk c c' o == in_region (c <: hp_addr) c' o)
#pop-options

/// Free words, on the record.
#push-options "--z3rlimit 40"
let clause_words (c: U64.t) (h: heap) (s: ffst) (m: M.mheap) (w: nat)
  : Lemma (requires sctx c h s m)
          (ensures (let (g', fp', c') = sres c h s in
                    let s' = after g' fp' in
                    (T.free_word ffa s h m w ==> T.free_word ffa s' g' (cabs g') w) /\
                    (T.free_word ffa s' g' (cabs g') w ==>
                       T.free_word ffa s h m w \/ (exists (o: nat). M.covers m o w /\ T.swept_white ffa s h m c c' o)) /\
                    (forall (o: nat). T.swept_white ffa s h m c c' o /\ M.covers m o w ==>
                       T.free_word ffa s' g' (cabs g') w)))
  = let (g', fp', c') = sres c h s in
    let g = gl h s in
    fw_at m h s w;
    gl_after g' fp';
    R.heq_refl (cabs g');
    fw_at (cabs g') g' (after g' fp') w;
    words_m (c <: hp_addr) g s.fp g' fp' c' w;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (use_at m h s));
    assert (forall (o: nat). T.region ffk c c' o == in_region (c <: hp_addr) c' o)
#pop-options

/// The words freed, on the record.
#push-options "--z3rlimit 40"
let freed_pt (c: U64.t) (h: heap) (s: ffst) (m: M.mheap) (o: nat)
  : Lemma (requires sctx c h s m)
          (ensures (let (g', fp', c') = sres c h s in
                    T.swept_words ffa s h m c c' o == GC.Spec.Top.PagesFreed.ind (oc (c <: hp_addr)) (ffw (gl h s) c) o))
  = let (g', fp', c') = sres c h s in
    let g = gl h s in
    let cc : hp_addr = c in
    use_at m h s o;
    wf_both cc g s.fp g' fp' c';
    freed_cur cc g s.fp g' fp' c';
    oc_region cc g s.fp g' fp' c';
    if used (cabs g) o && in_region cc c' o then region_one cc g s.fp g' fp' c' o
#pop-options

let clause_freed (c: U64.t) (h: heap) (s: ffst) (m: M.mheap)
  : Lemma (requires sctx c h s m)
          (ensures (let (g', fp', c') = sres c h s in
                    ffw (gl h s) c == M.sum m.M.size (T.swept_words ffa s h m c c')))
  = let (g', fp', c') = sres c h s in
    let cc : hp_addr = c in
    oc_facts cc (gl h s) s.fp g' fp' c';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (freed_pt c h s m));
    GC.Spec.Top.PagesFreed.sum_ext m.M.size (T.swept_words ffa s h m c c')
      (GC.Spec.Top.PagesFreed.ind (oc cc) (ffw (gl h s) c));
    GC.Spec.Top.PagesFreed.sum_ind m.M.size (oc cc) (ffw (gl h s) c)

/// Progress, sizes, the invariant after.
#push-options "--z3rlimit 40"
let clause_rest (c: U64.t) (h: heap) (s: ffst) (m: M.mheap)
  : Lemma (requires sctx c h s m)
          (ensures (let (g', fp', c') = sres c h s in
                    (forall (o: nat). ffk.T.unswept c' o ==> ffk.T.unswept c o) /\
                    (exists (o: nat). o < m.M.size /\ T.region ffk c c' o) /\
                    (cabs g').M.size == m.M.size /\
                    ffa.T.inv (T.Sweeping c') g' (after g' fp') /\ M.well_formed (cabs g')))
  = let (g', fp', c') = sres c h s in
    let cc : hp_addr = c in
    let g = gl h s in
    ctx_open cc g s.fp g' fp' c';
    bfacts_elim cc g s.fp g' fp' c';
    wf_both cc g s.fp g' fp' c';
    oc_facts cc g s.fp g' fp' c';
    oc_region cc g s.fp g' fp' c';
    gl_after g' fp'
#pop-options

/// **One step.**
#push-options "--z3rlimit 40"
let step_m (c: U64.t) (h: heap) (s: ffst) (m: M.mheap)
  : Lemma (requires brepr m h /\ T.sweep_step_pre ffsweep c h s m)
          (ensures (let (c', h', s', res) = ffsweep.T.step c h s in
                    T.sweep_step_post ffa c h s c' h' s' res m (cabs h')))
  = sctx_intro c h s m;
    step_is c h s;
    let (g', fp', c') = sres c h s in
    let s' = after g' fp' in
    let res = { T.units = 1; T.freed_words = ffw (gl h s) c } in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (clause_blocks c h s m));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (clause_words c h s m));
    clause_freed c h s m;
    clause_rest c h s m;
    GC.Spec.Top.PagesStepOk.post_intro ffa c h s c' g' s' res m (cabs g')
#pop-options

let step_ok (c: U64.t) (h: heap) (s: ffst) : Lemma (T.sweep_step_at byte_rep ffsweep c h s)
  = let (_, h', _, _) = ffsweep.T.step c h s in
    brepr_cabs h';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (step_m c h s))

let start_ok (h: heap) (s: ffst) : Lemma (T.sweep_start_at byte_rep ffsweep h s)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (start_m h s))

let done_ok (c: U64.t) (h: heap) (s: ffst) : Lemma (T.sweep_done_at byte_rep ffsweep c h s)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (done_m c h s))

/// **akhil's fused sweep meets the sweep contract.**
let ff_sweep_ok () : Lemma (T.sweep_ok byte_rep ffsweep)
  = FStar.Classical.forall_intro_2 start_ok;
    FStar.Classical.forall_intro_3 step_ok;
    FStar.Classical.forall_intro_3 done_ok
