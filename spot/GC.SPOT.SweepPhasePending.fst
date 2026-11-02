/// ---------------------------------------------------------------------------
/// GC.SPOT.SweepPhasePending - a mid-sweep heap with a pending object
/// ---------------------------------------------------------------------------
///
/// The sweep phase is stated except the pending objects (the white objects in
/// front of the cursor), whose fields may point into blocks the sweep has
/// already freed and merged.  This SPOT builds such a heap from the concrete
/// two-block heap of `GC.SPOT.ConcreteMajorGen` with the program's events and
/// the sweep's steps, and shows that the sweep phase and the minor
/// collection's shape hold of it with a non-empty pending set, and that a
/// minor collection then keeps both:
///
///   1. sweep the concrete heap completely (nothing is marked): one free block;
///   2. allocate `P` and then `G` at the end of the sweep phase (behind the
///      cursor, so white) and initialise them, and store `G` into `P`'s field;
///   3. end that sweep phase, and start the next one (nothing is marked);
///   4. two steps: the free block at the start of the heap absorbs `G`.
///
/// Then `P` is pending, its field points at `G`, and `G` is no longer an
/// object: its word lies inside the merged free block at the start of the
/// heap (`sweep_phase_pending_spot`).  The heap is in the sweep phase and in the
/// minor collection's shape for that pending set, and the minor collection at
/// the sweep's phase keeps the sweep phase with `P` still pending.

module GC.SPOT.SweepPhasePending

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module FL = GC.Spec.FreeList
module Gen = GC.SPOT.ConcreteMajorGen
module GenInv = GC.Gen.HeapInvariant
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv
module SPE = GC.Spec.SweepPhase.Intrinsic.End
module GSP = GC.Gen.SweepPhase
module SPM = GC.Gen.SweepPhase.Minor
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Ph = GC.Spec.Phase
module CA = GC.Gen.CheneyAt
module Promote = GC.Gen.Promote

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// Room for the fixture.
let room : prop = Gen.spot_major_room /\ U64.v zero_addr + 128 <= heap_size

let mp : Gen.minor_ptr = 8UL

/// ---------------------------------------------------------------------------
/// Helpers
/// ---------------------------------------------------------------------------

let no_black_pos (g: heap) : prop = forall (p: hp_addr). pos g p ==> not (black_at g p)

let no_black_pos_of (g: heap)
  : Lemma (requires forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_black x g))
          (ensures no_black_pos g)
  = let one (p: hp_addr) : Lemma (requires pos g p) (ensures not (black_at g p))
      = let x = obj_of p in
        obj_of_facts p; obj_pos g x; colour_of g x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// A heap whose objects are all white or free can start a sweep.
let can_start (g: heap) (fp: U64.t)
  : Lemma (requires well_formed_heap g /\ swept_clean g fp)
          (ensures sweep_pre g fp /\ Mark.noGreyObjects g /\ Mark.tri_color_invariant g /\
                   no_black_pos g)
  = let cl (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g) ==> ~(is_black x g) /\ ~(is_gray x g))
      = Mark.colors_exclusive x g
    in
    FStar.Classical.forall_intro cl;
    no_black_pos_of g

/// Below a cursor at the end of the walk, the only block of a heap whose
/// sweep left one free block is that block.
let only_block (g: heap) (c: nat) : prop =
  pos g zero_addr /\ blue_at g zero_addr /\ W.bnext g zero_addr == c /\
  (forall (x: nat). W.reaches g zero_addr x /\ x < c ==> x == U64.v zero_addr)

/// ---------------------------------------------------------------------------
/// Stage 0: the concrete heap, nothing marked
/// ---------------------------------------------------------------------------

let g0 (r: unit{room}) : heap = Gen.spot_major_heap r mp
let fp0 (r: unit{room}) : U64.t = Gen.spot_major_fp r

#push-options "--z3rlimit 20"
let stage0 (r: unit{room})
  : Lemma (sweep_pre (g0 r) (fp0 r) /\ Mark.noGreyObjects (g0 r) /\
           Mark.tri_color_invariant (g0 r) /\ no_black_pos (g0 r))
  = Gen.spot_major_heap_shape r mp;
    GenInv.major_heap_shape_elim (g0 r) (fp0 r);
    let ng (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr (g0 r)) ==> ~(is_gray x (g0 r)))
      = if Seq.mem x (objects zero_addr (g0 r)) then SweepInv.no_gray_elim x (g0 r)
    in
    FStar.Classical.forall_intro ng;
    no_black_pos_of (g0 r)
#pop-options

/// ---------------------------------------------------------------------------
/// Stage 1: sweep it completely
/// ---------------------------------------------------------------------------

let s1 (r: unit{room}) : GTot (heap & U64.t & sweep_state) =
  sweep_steps (g0 r) (fp0 r) sweep_start heap_words

let g1 (r: unit{room}) : GTot heap = Mktuple3?._1 (s1 r)
let fp1 (r: unit{room}) : GTot U64.t = Mktuple3?._2 (s1 r)
let st1 (r: unit{room}) : GTot sweep_state = Mktuple3?._3 (s1 r)
let c1 (r: unit{room}) : GTot nat = U64.v (st1 r).cursor

#push-options "--z3rlimit 20"
let stage1 (r: unit{room})
  : Lemma (sweep_phase_inv (g1 r) (fp1 r) (st1 r) /\ sweep_done (st1 r) /\
           c1 r <= heap_size /\ U64.v zero_addr + 120 <= c1 r /\
           W.reaches (g1 r) zero_addr (c1 r) /\
           only_block (g1 r) (c1 r))
  = stage0 r;
    sweep_phase_start (g0 r) (fp0 r);
    sweep_phase_steps (g0 r) (fp0 r) sweep_start heap_words;
    sweep_phase_steps_stw (g0 r) (g0 r) (fp0 r) sweep_start heap_words;
    assert (heap_words * 8 == heap_size);
    sweep_steps_done (g0 r) (fp0 r) sweep_start heap_words;
    sweep_phase_inv_elim (g1 r) (fp1 r) (st1 r);
    SPE.nothing_live_one_block (g0 r) (g1 r) (fp1 r) (st1 r)
#pop-options

/// The end of the first sweep, with its bounds.
let cend (r: unit{room}) : GTot (c: nat{c % 8 == 0 /\ U64.v zero_addr + 120 <= c /\ c <= heap_size}) =
  stage1 r;
  sweep_phase_inv_elim (g1 r) (fp1 r) (st1 r);
  c1 r

/// ---------------------------------------------------------------------------
/// Allocating one word at the end of the free block at the start
/// ---------------------------------------------------------------------------

/// The heap before: in the sweep phase, finished; one free block at the start
/// ending at `e`, and no other free block.
let before (g: heap) (fp: U64.t) (st: sweep_state) (e: nat) : prop =
  sweep_phase_inv g fp st /\ sweep_done st /\ U64.v zero_addr + 64 <= e /\ e <= U64.v st.cursor /\
  only_block g e /\
  (forall (q: hp_addr). pos g q /\ blue_at g q ==> q == zero_addr)

let ar (g: heap) (fp: U64.t) (st: sweep_state) : GTot SA.alloc_result =
  fst (AC.alloc_phase g fp (SA.Sweeping st) 1 0UL)

let new_obj (g: heap) (fp: U64.t) (st: sweep_state) : GTot U64.t = (ar g fp st).SA.obj_out

/// The allocation succeeds: the free block at the start is big enough
/// (`sweep_phase_oom_no_fit`, #29 mid-sweep).
#push-options "--z3rlimit 20"
let alloc_ok (g: heap) (fp: U64.t) (st: sweep_state) (e: nat)
  : Lemma (requires before g fp st e) (ensures new_obj g fp st <> 0UL)
  = if new_obj g fp st = 0UL then begin
      SPE.sweep_phase_oom_no_fit g fp st 1 0UL;
      let x = obj_of zero_addr in
      obj_of_facts zero_addr;
      obj_pos g x; colour_of g x;
      W.bnext_facts g zero_addr;
      assert (wz_at g zero_addr >= 1)
    end
#pop-options

/// Where it lands: at the end of the free block at the start.
#push-options "--z3rlimit 30"
let alloc_where (g: heap) (fp: U64.t) (st: sweep_state) (e: nat)
  : Lemma (requires before g fp st e)
          (ensures (let g' = (ar g fp st).SA.heap_out in
                    let o = new_obj g fp st in
                    is_obj o /\ U64.v o == e - 8 /\
                    GSP.allocated g g' st o 1 0UL /\
                    sweep_shape g' (ar g fp st).SA.fp_out (GSP.alloc_state g fp 1 st) /\
                    pos g' zero_addr /\ blue_at g' zero_addr /\ W.bnext g' zero_addr == e - 16 /\
                    (forall (x: nat). W.reaches g' zero_addr x /\ x < e - 16 ==> x == U64.v zero_addr) /\
                    (forall (x: nat). x >= e ==> (W.reaches g' zero_addr x <==> W.reaches g zero_addr x)) /\
                    (forall (a: hp_addr). W.reaches g zero_addr (U64.v a) /\ U64.v a >= e ==>
                       read_word g' a == read_word g a) /\
                    (forall (x: nat). e - 16 < x /\ x < e ==> ~(W.reaches g' zero_addr x))))
  = alloc_ok g fp st e;
    sweep_phase_inv_iff g fp st;
    GSP.alloc_sweep_shape g fp st 1 0UL;
    GSP.alloc_carved g fp st 1 0UL;
    let g' = (ar g fp st).SA.heap_out in
    let o : obj_addr = new_obj g fp st in
    let p = hd_address o in
    hd_address_spec o;
    sweep_phase_inv_elim g fp st;
    eliminate exists (q: hp_addr). GSP.carved_from g g' q p
    with begin
      // the block it came from is the one at the start
      assert (q == zero_addr);
      assert (W.bnext g' p == e);
      assert (U64.v p == e - 16);
      assert (U64.v zero_addr < U64.v p)
    end
#pop-options

/// The heap after the allocation and its initialisation (field 0 := 0).
let init_heap (g: heap) (fp: U64.t) (st: sweep_state) : GTot heap =
  let o = new_obj g fp st in
  if is_obj o then write_word (ar g fp st).SA.heap_out (o <: hp_addr) 0UL
  else (ar g fp st).SA.heap_out

#push-options "--z3rlimit 30"
let alloc_init (g: heap) (fp: U64.t) (st: sweep_state) (e: nat)
  : Lemma (requires before g fp st e)
          (ensures is_obj (new_obj g fp st) /\
                   (let g'' = init_heap g fp st in
                    let fp' = (ar g fp st).SA.fp_out in
                    let st' = GSP.alloc_state g fp 1 st in
                    let o : obj_addr = new_obj g fp st in
                    U64.v o == e - 8 /\
                    sweep_phase_inv g'' fp' st' /\ st'.cursor == st.cursor /\
                    pos g'' zero_addr /\ blue_at g'' zero_addr /\ W.bnext g'' zero_addr == e - 16 /\
                    (forall (x: nat). W.reaches g'' zero_addr x /\ x < e - 16 ==> x == U64.v zero_addr) /\
                    (forall (x: nat). x >= e ==> (W.reaches g'' zero_addr x <==> W.reaches g zero_addr x)) /\
                    (forall (a: hp_addr). W.reaches g zero_addr (U64.v a) /\ U64.v a >= e ==>
                       read_word g'' a == read_word g a) /\
                    (forall (x: nat). e - 16 < x /\ x < e ==> ~(W.reaches g'' zero_addr x)) /\
                    pos g'' (hd_address o) /\ white_at g'' (hd_address o) /\
                    wz_at g'' (hd_address o) == 1 /\ getTag (read_word g'' (hd_address o)) == 0UL /\
                    Seq.mem o (objects zero_addr g'') /\ is_white o g'' /\
                    ~(is_closure o g'') /\ ~(is_infix o g'')))
  = alloc_where g fp st e;
    infix_tag_val ();
    GSP.alloc_sweep_phase g fp st 1 0UL;
    let g' = (ar g fp st).SA.heap_out in
    let fp' = (ar g fp st).SA.fp_out in
    let st' = GSP.alloc_state g fp 1 st in
    let o : obj_addr = new_obj g fp st in
    let a : hp_addr = o in
    colour_of g' o;
    assert (GSP.in_body g' o a);
    GSP.fresh_write g' fp' st' o a 0UL;
    let g'' = write_word g' a 0UL in
    same_heads_facts g' g'';
    colour_of g'' o;
    read_write_same g' a 0UL;
    assert (GSP.field_val g'' o 0 == 0UL);
    GSP.fresh_close g'' fp' st' o;
    is_closure_spec o g''; closure_tag_val ();
    is_infix_spec o g''; infix_tag_val ()
#pop-options

/// ---------------------------------------------------------------------------
/// Stage 2: allocate P, then G, behind the cursor
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let stage1_before (r: unit{room})
  : Lemma (before (g1 r) (fp1 r) (st1 r) (c1 r))
  = stage1 r;
    sweep_phase_inv_elim (g1 r) (fp1 r) (st1 r);
    let bl (q: hp_addr) : Lemma (requires pos (g1 r) q /\ blue_at (g1 r) q) (ensures q == zero_addr)
      = W.reaches_stuck (g1 r) zero_addr (c1 r) (U64.v q)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bl)
#pop-options

let g2 (r: unit{room}) : GTot heap = init_heap (g1 r) (fp1 r) (st1 r)
let fp2 (r: unit{room}) : GTot U64.t = (ar (g1 r) (fp1 r) (st1 r)).SA.fp_out
let st2 (r: unit{room}) : GTot sweep_state = GSP.alloc_state (g1 r) (fp1 r) 1 (st1 r)
let spot_p (r: unit{room}) : GTot U64.t = new_obj (g1 r) (fp1 r) (st1 r)

/// What one allocation and its initialisation leave, as the next one needs it.
#push-options "--z3rlimit 20"
let after_before (g: heap) (fp: U64.t) (st: sweep_state) (e: nat)
  : Lemma (requires before g fp st e /\ U64.v zero_addr + 80 <= e /\
                    (forall (q: hp_addr). pos g q ==> U64.v q < e \/ U64.v q + 8 >= U64.v st.cursor + 8))
          (ensures before (init_heap g fp st) (ar g fp st).SA.fp_out (GSP.alloc_state g fp 1 st) (e - 16))
  = alloc_init g fp st e;
    let g'' = init_heap g fp st in
    let bl (q: hp_addr) : Lemma (requires pos g'' q /\ blue_at g'' q) (ensures q == zero_addr)
      = if U64.v q >= e then begin
          assert (W.reaches g zero_addr (U64.v q));
          assert (read_word g'' q == read_word g q);
          assert (pos g q)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bl)
#pop-options

/// The first heap has no block at or beyond its end.
#push-options "--z3rlimit 20"
let stage1_end (r: unit{room})
  : Lemma (forall (q: hp_addr). pos (g1 r) q ==> U64.v q < cend r)
  = stage1 r;
    let one (q: hp_addr) : Lemma (requires pos (g1 r) q) (ensures U64.v q < cend r)
      = W.reaches_stuck (g1 r) zero_addr (c1 r) (U64.v q)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

#push-options "--z3rlimit 20"
let stage2 (r: unit{room})
  : Lemma (before (g2 r) (fp2 r) (st2 r) (cend r - 16) /\
           U64.v (spot_p r) == cend r - 8 /\ (st2 r).cursor == (st1 r).cursor)
  = stage1_before r;
    stage1_end r;
    alloc_init (g1 r) (fp1 r) (st1 r) (cend r);
    after_before (g1 r) (fp1 r) (st1 r) (cend r)
#pop-options

/// In the second heap the blocks at or beyond the free block's end are `P`'s.
#push-options "--z3rlimit 20"
let stage2_end (r: unit{room})
  : Lemma (forall (q: hp_addr). pos (g2 r) q ==> U64.v q < cend r - 16 \/ U64.v q == cend r - 16)
  = stage1_end r;
    stage1_before r;
    alloc_init (g1 r) (fp1 r) (st1 r) (cend r);
    let one (q: hp_addr)
      : Lemma (requires pos (g2 r) q) (ensures U64.v q < cend r - 16 \/ U64.v q == cend r - 16)
      = if U64.v q >= cend r then assert (pos (g1 r) q)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

let g3 (r: unit{room}) : GTot heap = init_heap (g2 r) (fp2 r) (st2 r)
let fp3 (r: unit{room}) : GTot U64.t = (ar (g2 r) (fp2 r) (st2 r)).SA.fp_out
let st3 (r: unit{room}) : GTot sweep_state = GSP.alloc_state (g2 r) (fp2 r) 1 (st2 r)
let spot_g (r: unit{room}) : GTot U64.t = new_obj (g2 r) (fp2 r) (st2 r)

/// `P`'s block, in the second heap.
#push-options "--z3rlimit 20"
let p_block2 (r: unit{room})
  : Lemma (let q = mk_hp_addr (cend r - 16) in
           pos (g2 r) q /\ white_at (g2 r) q /\ wz_at (g2 r) q == 1 /\
           getTag (read_word (g2 r) q) == 0UL /\
           (forall (x: nat). cend r - 16 < x /\ x < cend r ==> ~(W.reaches (g2 r) zero_addr x)))
  = stage1_before r;
    alloc_init (g1 r) (fp1 r) (st1 r) (cend r);
    hd_address_spec (spot_p r <: obj_addr)
#pop-options

/// The third heap: the free block at the start, `G`, `P`.
#push-options "--z3rlimit 20"
let stage3 (r: unit{room})
  : Lemma (let g = g3 r in
           let c = cend r in
           sweep_phase_inv g (fp3 r) (st3 r) /\ sweep_done (st3 r) /\ U64.v (st3 r).cursor == c /\
           U64.v (spot_g r) == c - 24 /\
           only_block g (c - 32) /\
           pos g (mk_hp_addr (c - 32)) /\ white_at g (mk_hp_addr (c - 32)) /\
           wz_at g (mk_hp_addr (c - 32)) == 1 /\ getTag (read_word g (mk_hp_addr (c - 32))) == 0UL /\
           (forall (x: nat). c - 32 < x /\ x < c - 16 ==> ~(W.reaches g zero_addr x)))
  = stage1 r;
    stage2 r;
    alloc_init (g2 r) (fp2 r) (st2 r) (cend r - 16);
    hd_address_spec (spot_g r <: obj_addr)
#pop-options

/// `P`'s block, in the third heap.
#push-options "--z3rlimit 20"
let p_block3 (r: unit{room})
  : Lemma (let q = mk_hp_addr (cend r - 16) in
           pos (g3 r) q /\ white_at (g3 r) q /\ wz_at (g3 r) q == 1 /\
           getTag (read_word (g3 r) q) == 0UL /\
           (forall (x: nat). cend r - 16 < x /\ x < cend r ==> ~(W.reaches (g3 r) zero_addr x)))
  = stage2 r;
    p_block2 r;
    alloc_init (g2 r) (fp2 r) (st2 r) (cend r - 16);
    let q = mk_hp_addr (cend r - 16) in
    assert (W.reaches (g3 r) zero_addr (cend r - 16));
    assert (read_word (g3 r) q == read_word (g2 r) q)
#pop-options

/// ---------------------------------------------------------------------------
/// Stage 3: store G into P's field (a program write)
/// ---------------------------------------------------------------------------

/// `P` and `G`, with their addresses.
let pp (r: unit{room}) : GTot (x: obj_addr{U64.v x == cend r - 8}) = stage2 r; spot_p r
let gg (r: unit{room}) : GTot (x: obj_addr{U64.v x == cend r - 24}) = stage3 r; spot_g r

let g4 (r: unit{room}) : GTot heap = write_word (g3 r) (pp r <: hp_addr) (gg r)

#push-options "--z3rlimit 20"
let stage4 (r: unit{room})
  : Lemma (let g = g4 r in
           let c = cend r in
           sweep_phase_inv g (fp3 r) (st3 r) /\ same_heads (g3 r) g /\
           read_word g (pp r <: hp_addr) == (gg r <: U64.t))
  = stage2 r; stage3 r; p_block3 r;
    let c = cend r in
    let g = g3 r in
    let p : obj_addr = pp r in
    let q : obj_addr = gg r in
    hd_address_spec p; hd_address_spec q;
    obj_pos g p; colour_of g p;
    obj_pos g q; colour_of g q;
    is_closure_spec p g; closure_tag_val ();
    is_infix_spec q g; infix_tag_val ();
    resolve_non_infix q g;
    infix_addr_wf_non_infix g (objects zero_addr g) q;
    assert (GSP.program_write g (pending g (st3 r)) p (p <: hp_addr) q);
    GSP.write_sweep_phase g (fp3 r) (st3 r) p (p <: hp_addr) q;
    sweep_phase_inv_iff g (fp3 r) (st3 r);
    GSP.body_write_shape g (fp3 r) (st3 r) p (p <: hp_addr) q;
    read_write_same g (p <: hp_addr) q
#pop-options

/// ---------------------------------------------------------------------------
/// Stage 4: end this sweep phase and start the next (nothing marked)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let stage5 (r: unit{room})
  : Lemma (let g = g4 r in
           let c = cend r in
           sweep_phase_inv g (fp3 r) sweep_start /\ stw_rel g g (U64.v zero_addr) /\
           no_black_pos g /\
           only_block g (c - 32) /\
           pos g (mk_hp_addr (c - 32)) /\ wz_at g (mk_hp_addr (c - 32)) == 1 /\
           Seq.mem (gg r) (objects zero_addr g) /\
           pos g (mk_hp_addr (c - 16)) /\ white_at g (mk_hp_addr (c - 16)) /\
           wz_at g (mk_hp_addr (c - 16)) == 1 /\ read_word g (pp r <: hp_addr) == (gg r <: U64.t))
  = stage3 r; stage4 r; p_block3 r;
    let g = g4 r in
    same_heads_facts (g3 r) g;
    sweep_phase_inv_elim g (fp3 r) (st3 r);
    SPE.sweep_phase_end g (fp3 r) (st3 r);
    can_start g (fp3 r);
    sweep_phase_start g (fp3 r);
    hd_address_spec (gg r);
    obj_pos g (gg r)
#pop-options

/// ---------------------------------------------------------------------------
/// Stage 5: two steps -- the free block at the start absorbs G
/// ---------------------------------------------------------------------------

let s5 (r: unit{room}) : GTot (heap & U64.t & sweep_state) = sweep_steps (g4 r) (fp3 r) sweep_start 2
let g5 (r: unit{room}) : GTot heap = Mktuple3?._1 (s5 r)
let fp5 (r: unit{room}) : GTot U64.t = Mktuple3?._2 (s5 r)
let st5 (r: unit{room}) : GTot sweep_state = Mktuple3?._3 (s5 r)

let sa_ok (r: unit{room}) : Lemma (can_sweep (g4 r) sweep_start) =
  stage5 r; sweep_phase_step (g4 r) (fp3 r) sweep_start

let sa (r: unit{room}) : GTot (heap & U64.t & sweep_state) =
  sa_ok r; sweep_step (g4 r) (fp3 r) sweep_start

/// The first step: the free block at the start stays, and becomes `swept_tail`.
#push-options "--z3rlimit 20"
let step_a (r: unit{room})
  : Lemma (let (ga, fpa, sta) = sa r in
           sweep_phase_inv ga fpa sta /\ U64.v sta.cursor == cend r - 32 /\
           stw_rel (g4 r) ga (cend r - 32) /\ not (sweep_done sweep_start) /\
           can_sweep (g4 r) sweep_start)
  = stage5 r;
    sweep_phase_step (g4 r) (fp3 r) sweep_start;
    sweep_phase_step_stw (g4 r) (g4 r) (fp3 r) sweep_start
#pop-options

/// The second step: `G` is garbage next to a free block, which absorbs it.
#push-options "--z3rlimit 20"
let step_b (r: unit{room})
  : Lemma (let (ga, fpa, sta) = sa r in
           can_sweep ga sta /\ not (sweep_done sta) /\
           (let (gb, fpb, stb) = sweep_step ga fpa sta in
            sweep_phase_inv gb fpb stb /\ U64.v stb.cursor == cend r - 16 /\
            stw_rel (g4 r) gb (cend r - 16)))
  = stage5 r;
    step_a r;
    let (ga, fpa, sta) = sa r in
    let q = mk_hp_addr (cend r - 32) in
    front_same_elim (g4 r) ga (cend r - 32) q;
    sweep_phase_step ga fpa sta;
    sweep_phase_step_stw (g4 r) ga fpa sta
#pop-options

#push-options "--z3rlimit 20"
let stage6 (r: unit{room})
  : Lemma (sweep_phase_inv (g5 r) (fp5 r) (st5 r) /\ U64.v (st5 r).cursor == cend r - 16 /\
           stw_rel (g4 r) (g5 r) (cend r - 16))
  = step_a r; step_b r; sa_ok r;
    let (ga, fpa, sta) = sa r in
    let (gb, fpb, stb) = sweep_step ga fpa sta in
    sweep_steps_unfold (g4 r) (fp3 r) sweep_start 2;
    sweep_steps_unfold ga fpa sta 1;
    sweep_steps_unfold gb fpb stb 0
#pop-options

/// ---------------------------------------------------------------------------
/// The heap: P pending, pointing into the merged free block
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let stage7 (r: unit{room})
  : Lemma (let g = g5 r in
           let st = st5 r in
           let p = pp r in
           let q = gg r in
           pending g st p /\
           read_word g (p <: hp_addr) == (q <: U64.t) /\
           ~(Seq.mem q (objects zero_addr g)) /\
           pos g zero_addr /\ blue_at g zero_addr /\
           U64.v zero_addr < U64.v q /\ U64.v q < W.bnext g zero_addr)
  = stage5 r; stage6 r;
    let g = g5 r in
    let st = st5 r in
    let c = cend r in
    let p = pp r in
    let q = gg r in
    sweep_phase_inv_elim g (fp5 r) st;
    let hp = mk_hp_addr (c - 16) in
    hd_address_spec p; hd_address_spec q;
    front_same_elim (g4 r) g (c - 16) hp;
    front_same_elim (g4 r) g (c - 16) (p <: hp_addr);
    obj_pos g p; colour_of g p;
    obj_pos (g4 r) p; colour_of (g4 r) p;
    SPE.nothing_live_one_block (g4 r) g (fp5 r) st;
    obj_pos g q
#pop-options

/// **The SPOT.**  A heap in the sweep phase with a pending object `P` whose
/// field points at `G`, an object of the heap the sweep started on, which the
/// sweep has merged into the free block at the start of the heap.  The minor
/// collection's shape holds for that pending set, and the minor collection at
/// the sweep's phase keeps the sweep phase, with `P` still pending.
#push-options "--z3rlimit 20"
let sweep_phase_pending_spot (r: unit{room}) (m: minor_state) (roots: seq U64.t)
  : Lemma (let g = g5 r in
           let fp = fp5 r in
           let st = st5 r in
           let p = pp r in
           let q = gg r in
           sweep_phase_inv g fp st /\
           pending g st p /\
           Seq.mem q (objects zero_addr (g4 r)) /\
           read_word g (p <: hp_addr) == (q <: U64.t) /\
           ~(Seq.mem q (objects zero_addr g)) /\
           pos g zero_addr /\ blue_at g zero_addr /\
           U64.v zero_addr < U64.v q /\ U64.v q < W.bnext g zero_addr /\
           GenInv.collection_shape_except (minor_reset m) g fp (pending g st) /\
           (let (res, ph') = CA.cheney_collect_spec_except_at (Ph.Sweeping st) (minor_reset m) g fp roots
                               (pending g st) in
            let st' = SPM.state_after st
                        (GC.Gen.Cheney.cheney_collect_spec_except (minor_reset m) g fp roots
                           (pending g st)).Promote.mc_major in
            ph' == Ph.Sweeping st' /\
            sweep_phase_inv res.Promote.mc_major res.Promote.mc_fp st' /\
            pending res.Promote.mc_major st' p))
  = stage5 r; stage6 r; stage7 r;
    let g = g5 r in
    let fp = fp5 r in
    let st = st5 r in
    let pf = pending g st in
    SPM.sweep_major_shape g fp st;
    GenInv.collection_shape_except_after_minor_reset m g fp pf;
    GenInv.collection_shape_except_elim (minor_reset m) g fp pf;
    GenInv.minor_reset_heap_shape m;
    SPM.minor_keeps_sweep_phase (minor_reset m) g fp st roots
#pop-options
