module GC.Spec.FusedSweep.Lossless

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module FSS = GC.Spec.FusedSweep.Step
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPE = GC.Spec.SweepPhase.Intrinsic.End
module FSE = GC.Spec.FusedSweep.End
module W = GC.Spec.Walk
module Mark = GC.Spec.Mark
module SEM = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Counting addresses
/// ---------------------------------------------------------------------------

let rec count (f: nat -> GTot bool) (lo hi: nat)
  : GTot nat (decreases (if lo < hi then hi - lo else 0))
  = if lo >= hi then 0 else (if f lo then 1 else 0) + count f (lo + 1) hi

#push-options "--fuel 1"
let rec count_split (f: nat -> GTot bool) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures count f lo hi == count f lo mid + count f mid hi)
          (decreases (mid - lo))
  = if lo = mid then () else count_split f (lo + 1) mid hi

let rec count_ext (f1 f2: nat -> GTot bool) (lo hi: nat)
  : Lemma (requires forall (q: nat). lo <= q /\ q < hi ==> f1 q == f2 q)
          (ensures count f1 lo hi == count f2 lo hi)
          (decreases (if lo < hi then hi - lo else 0))
  = if lo >= hi then () else count_ext f1 f2 (lo + 1) hi

let rec count_const (f: nat -> GTot bool) (b: bool) (lo hi: nat)
  : Lemma (requires lo <= hi /\ (forall (q: nat). lo <= q /\ q < hi ==> f q == b))
          (ensures count f lo hi == (if b then hi - lo else 0))
          (decreases (hi - lo))
  = if lo = hi then () else count_const f b (lo + 1) hi
#pop-options

/// ---------------------------------------------------------------------------
/// The walk tiles what it covers
/// ---------------------------------------------------------------------------

/// `q` is covered by an object of the walk from `a` satisfying `pr`.
let covered (g: heap) (pr: obj_addr -> GTot bool) (a: hp_addr) (q: nat) : prop =
  exists (x: obj_addr). Seq.mem x (objects a g) /\ pr x /\ in_extent g x q

let cov (g: heap) (pr: obj_addr -> GTot bool) (a: hp_addr) (q: nat) : GTot bool =
  SEM.strong_excluded_middle (covered g pr a q)

/// The first object of the walk from `a`.
let first_facts (g: heap) (a: hp_addr)
  : Lemma (requires W.can_step g a)
          (ensures U64.v a + 8 < heap_size /\
                   (let x0 = f_address a in
                    U64.v x0 == U64.v a + 8 /\ hd_address x0 == a /\
                    next_pos g x0 == W.bnext g a))
  = f_address_spec a;
    hd_f_roundtrip a;
    wosize_of_object_spec (f_address a) g

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let objects_unfold (g: heap) (a: hp_addr)
  : Lemma (ensures
      (if not (W.can_step g a) then objects a g == Seq.empty
       else begin
         U64.v a + 8 < heap_size /\
         (let n = W.bnext g a in
          if n >= heap_size then objects a g == Seq.cons (f_address a) Seq.empty
          else (n < heap_size /\ n % 8 == 0 /\
                objects a g == Seq.cons (f_address a) (objects (mk_hp_addr n) g)))
       end))
  = W.bnext_facts g a
#pop-options

let walk_end_ge (g: heap) (a: hp_addr)
  : Lemma (U64.v a <= W.walk_end g a /\ W.walk_end g a <= heap_size)
  = W.reaches_walk_end g a;
    W.reaches_bounds g a (W.walk_end g a)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let walk_end_unfold (g: heap) (a: hp_addr)
  : Lemma (requires W.can_step g a)
          (ensures (let n = W.bnext g a in
                    if n >= heap_size then W.walk_end g a == n
                    else (n % 8 == 0 /\ W.walk_end g a == W.walk_end g (mk_hp_addr n))))
  = W.bnext_facts g a
#pop-options

/// The words the objects of a walk satisfying `pr` cover are, in number, 8
/// times their whole size; and the walk covers only words in
/// `[a, walk_end g a)`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec walk_count (g: heap) (pr: obj_addr -> GTot bool) (a: hp_addr)
  : Lemma (ensures
      space g pr (objects a g) * 8 == count (cov g pr a) (U64.v a) (W.walk_end g a) /\
      (forall (q: nat). covered g pr a q ==> U64.v a <= q /\ q < W.walk_end g a))
    (decreases (heap_size - U64.v a))
  = objects_unfold g a;
    walk_end_ge g a;
    if not (W.can_step g a) then begin
      assert (W.walk_end g a == U64.v a);
      assert (forall (q: nat). ~(covered g pr a q))
    end else begin
      first_facts g a;
      walk_end_unfold g a;
      let x0 = f_address a in
      let n = W.bnext g a in
      let e = W.walk_end g a in
      let hd_cov (q: nat) : Lemma (in_extent g x0 q <==> U64.v a <= q /\ q < n) = () in
      FStar.Classical.forall_intro hd_cov;
      if n >= heap_size then begin
        assert (e == n);
        let objs = objects a g in
        Seq.head_cons x0 (Seq.empty #obj_addr);
        Seq.lemma_tl x0 (Seq.empty #obj_addr);
        assert (Seq.head objs == x0 /\ Seq.length (Seq.tail objs) == 0);
        assert (space g pr (Seq.tail objs) == 0);
        let c1 (q: nat) : Lemma (covered g pr a q <==> (pr x0 /\ in_extent g x0 q)) =
          Seq.mem_cons x0 (Seq.empty #obj_addr) in
        FStar.Classical.forall_intro c1;
        count_const (cov g pr a) (pr x0) (U64.v a) n;
        assert (whsize g x0 * 8 == n - U64.v a)
      end else begin
        let a' = mk_hp_addr n in
        walk_count g pr a';
        walk_end_ge g a';
        let objs = objects a g in
        assert (objs == Seq.cons x0 (objects a' g));
        let c1 (q: nat) : Lemma (covered g pr a q <==>
                                 ((pr x0 /\ in_extent g x0 q) \/ covered g pr a' q)) =
          Seq.mem_cons x0 (objects a' g) in
        FStar.Classical.forall_intro c1;
        count_split (cov g pr a) (U64.v a) n e;
        count_const (cov g pr a) (pr x0) (U64.v a) n;
        count_ext (cov g pr a) (cov g pr a') n e;
        Seq.head_cons x0 (objects a' g);
        Seq.lemma_tl x0 (objects a' g);
        assert (Seq.head objs == x0);
        assert (Seq.equal (Seq.tail objs) (objects a' g));
        assert (whsize g x0 * 8 == n - U64.v a)
      end
    end
#pop-options

/// Two objects of a walk that cover the same word are the same object.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let same_cover (g: heap) (x y: obj_addr) (p: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
                    in_extent g x p /\ in_extent g y p)
          (ensures x == y)
  = objects_separated zero_addr g x y;
    objects_separated zero_addr g y x;
    hd_address_spec x; hd_address_spec y;
    wosize_of_object_spec x g; wosize_of_object_spec y g
#pop-options

/// ---------------------------------------------------------------------------
/// Where the walk ends
/// ---------------------------------------------------------------------------

/// The stop-the-world sweep invariant keeps the cursor a position of both
/// walks; at the end of the heap both walks therefore end there.
#push-options "--fuel 1"
let rec from_walk_end (g0 g: heap) (fp: U64.t) (st: FS.sweep_state)
  : Lemma (requires SPI.sweep_inv_stw g0 g fp st.cursor /\ st == SPI.state_at g st.cursor)
          (ensures W.walk_end (fst (FS.sweep_from g fp st)) zero_addr == W.walk_end g0 zero_addr)
          (decreases (heap_size - U64.v st.cursor))
  = if U64.v st.cursor + 8 < heap_size then begin
      FSS.sweep_inv_incremental_step g fp st.cursor;
      FSS.sweep_inv_stw_step g0 g fp st.cursor;
      let (g', fp', st') = FS.sweep_step g fp st in
      FS.sweep_from_step g fp st;
      from_walk_end g0 g' fp' st'
    end else begin
      FS.sweep_from_stop g fp st;
      SPI.sweep_inv_incremental_elim g fp st.cursor;
      W.walk_end_of_reaches g0 zero_addr (U64.v st.cursor);
      W.walk_end_of_reaches g zero_addr (U64.v st.cursor)
    end
#pop-options

let fused_sweep_walk_end g0 fp =
  SPI.sweep_inv_stw_start g0 fp;
  SPI.state_at_start g0;
  from_walk_end g0 g0 fp FS.sweep_start

/// ---------------------------------------------------------------------------
/// Coverage
/// ---------------------------------------------------------------------------

/// A dead block lies inside a free block of the result, so its words do too.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let dead_inside (g0 g: heap) (x y: obj_addr) (p: nat)
  : Lemma (requires FSE.inside g0 g x y /\ in_extent g0 x p)
          (ensures in_extent g y p)
  = hd_address_spec x; hd_address_spec y
#pop-options

let fused_dead_covered g0 fp x p =
  let r = FS.fused_sweep_coalesce g0 fp in
  let g = fst r in
  SPE.fused_sweep_post g0 fp;
  FSE.sweep_post_elim g0 g (snd r);
  eliminate exists (y: obj_addr).
    Seq.mem y (objects zero_addr g) /\ is_blue y g /\ FSE.inside g0 g x y
  with dead_inside g0 g x y p

/// The object of `g`'s walk holding a word below the end of a dense walk.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let block_of (g: heap) (p: nat)
  : Ghost obj_addr
    (requires heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0 /\
              U64.v zero_addr <= p /\ p < W.walk_end g zero_addr)
    (ensures fun x -> Seq.mem x (objects zero_addr g) /\ in_extent g x p)
  = W.reaches_end_of_dense g;
    let e = W.walk_end g zero_addr in
    let q = W.block_at g zero_addr e p in
    W.reaches_bounds g zero_addr (U64.v q);
    first_facts g q;
    let x = f_address q in
    W.objects_mem_iff g zero_addr x;
    x
#pop-options

/// A word of a free block of the result was in a dead block of `g0`.  The
/// block of `g0`'s walk that holds it is not black: a black one survives, at
/// the same place and size, as a white block of the result, which would then
/// share the word with the free one.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let blue_was_dead (g0: heap) (fp: U64.t) (p: nat)
  : Lemma (requires FSI.sweep_pre g0 fp /\ FSE.marked g0 /\ blue_covered (fst (FS.fused_sweep_coalesce g0 fp)) p)
          (ensures dead_covered g0 p)
  = let r = FS.fused_sweep_coalesce g0 fp in
    let g = fst r in
    SPE.fused_sweep_post g0 fp;
    FSE.sweep_post_elim g0 g (snd r);
    fused_sweep_walk_end g0 fp;
    walk_count g (fun x -> is_blue x g) zero_addr;
    assert (covered g (fun x -> is_blue x g) zero_addr p);
    let e = W.walk_end g0 zero_addr in
    assert (U64.v zero_addr <= p /\ p < e);
    let x = block_of g0 p in
    if is_black x g0 then begin
      assert (FSE.survives g0 g x);
      assert (in_extent g x p);
      eliminate exists (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_blue y g /\ in_extent g y p
      with begin
        same_cover g x y p;
        Mark.colors_exclusive x g
      end
    end else ()
#pop-options

/// ---------------------------------------------------------------------------
/// Free space
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let free_is_dead (g0: heap) (fp: U64.t)
  : Lemma (requires FSI.sweep_pre g0 fp /\ FSE.marked g0)
          (ensures total_free_space (fst (FS.fused_sweep_coalesce g0 fp)) == total_dead_space g0)
  = let r = FS.fused_sweep_coalesce g0 fp in
    let g = fst r in
    let pb = (fun x -> is_blue x g) in
    let pd = (fun x -> not (is_black x g0)) in
    fused_sweep_walk_end g0 fp;
    walk_count g pb zero_addr;
    walk_count g0 pd zero_addr;
    let e = W.walk_end g0 zero_addr in
    let pt (q: nat) : Lemma (cov g pb zero_addr q == cov g0 pd zero_addr q) =
      SPE.fused_sweep_post g0 fp;
      FSE.sweep_post_elim g0 g (snd r);
      if cov g0 pd zero_addr q then begin
        eliminate exists (x: obj_addr).
          Seq.mem x (objects zero_addr g0) /\ pd x /\ in_extent g0 x q
        with fused_dead_covered g0 fp x q
      end else if cov g pb zero_addr q then blue_was_dead g0 fp q
      else ()
    in
    FStar.Classical.forall_intro pt;
    count_ext (cov g pb zero_addr) (cov g0 pd zero_addr) (U64.v zero_addr) e
#pop-options

/// ---------------------------------------------------------------------------
/// The statement
/// ---------------------------------------------------------------------------

let adjacent_iff (g: heap) (x y: obj_addr)
  : Lemma (requires adjacent g x y) (ensures FSE.adjacent g x y)
  = hd_address_spec x; hd_address_spec y

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let fused_sweep_lossless g0 fp =
  let r = FS.fused_sweep_coalesce g0 fp in
  let g = fst r in
  SPE.fused_sweep_post g0 fp;
  FSE.sweep_post_elim g0 g (snd r);
  free_is_dead g0 fp;
  let cv (p: nat) : Lemma (p < heap_size ==> (blue_covered g p <==> dead_covered g0 p)) =
    if blue_covered g p then blue_was_dead g0 fp p
    else if dead_covered g0 p then begin
      eliminate exists (x: obj_addr).
        Seq.mem x (objects zero_addr g0) /\ ~(is_black x g0) /\ in_extent g0 x p
      with fused_dead_covered g0 fp x p
    end
  in
  FStar.Classical.forall_intro cv;
  let adj (x y: obj_addr)
    : Lemma (Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
             is_blue x g /\ is_blue y g /\ adjacent g x y ==> False)
    = if adjacent g x y then adjacent_iff g x y
  in
  FStar.Classical.forall_intro_2 adj
#pop-options
