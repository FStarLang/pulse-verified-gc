/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ByteBarrier - the write barrier on the byte heap
/// ---------------------------------------------------------------------------
///
/// The barrier of the byte-level collectors, as a component of
/// GC.Spec.Top.Iface over `byte_rep`.  It needs no allocator, so pages and
/// first-fit share it.
///
///   * `bwrite`: OCaml 4.14's `caml_modify` (akhil's `GC.Gen.Barrier.modify_heap`):
///     while marking, the old value's target is darkened (`caml_darken`),
///     then the word is written; the slot is remembered when the block is
///     scannable and the value young.  The target darkened is the block the
///     model resolves the old value to.  On a heap where akhil's barrier
///     runs (his `modify_ok`: a body word of a scannable block in use, in a
///     well-formed heap) it is the block `MM.darken` darkens, so `bwrite` is
///     `GB.modify_heap` there (`bwrite_marking_real`, `bwrite_idle_real`).
///     On other heaps `MM.darken` may darken through a word that looks like
///     an infix header but that the model does not resolve (gap G35).
///   * `binit`: `caml_initialize` for every field of a new block: the
///     words written in order, each young value's slot remembered.
///
/// Proved: `byte_barrier_ok : barrier_ok byte_rep bbarrier`, from the toy
/// barrier's model proofs (`GC.Spec.Top.ToyMark`): the canonical reading
/// of the byte result is the toy's result on the model
/// (`GC.Spec.Top.ByteWrite`).

module GC.Spec.Top.ByteBarrier

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.ByteRep
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Seq = FStar.Seq
module TM = GC.Spec.Top.ToyMark
module GB = GC.Gen.Barrier
module MM = GC.Spec.MarkPhase.Mutator
module Ph = GC.Spec.Phase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The barrier
/// ---------------------------------------------------------------------------

/// The old value's target, as the model resolves it, darkened if white.
let darken_old (g: heap) (o i: nat) : GTot heap =
  match T.old_target (cabs g) o i with
  | Some t -> if pos t + 8 < heap_size && is_white (obj_of t) g then makeGray (obj_of t) g else g
  | None -> g

/// The slot is remembered once, at the back: the order of C's
/// `caml_ref_table` (design doc §18.3, U3).
let remember (g: heap) (rem: list M.slot) (o i: nat) (v: M.value) : GTot (list M.slot) =
  if T.young_slot (cabs g) o i v && not (L.mem (o, i) rem) then L.append rem [(o, i)] else rem

/// What the contract asks of the remembered set.
let remember_ok (g: heap) (rem: list M.slot) (o i: nat) (v: M.value)
  : Lemma ((forall (sl: M.slot). L.memP sl rem ==> L.memP sl (remember g rem o i v)) /\
           (T.young_slot (cabs g) o i v ==> L.memP (o, i) (remember g rem o i v)))
  = L.mem_memP (o, i) rem;
    let one (sl: M.slot) : Lemma (L.memP sl rem ==> L.memP sl (L.append rem [(o, i)]))
      = L.append_memP rem [(o, i)] sl in
    FStar.Classical.forall_intro one;
    L.append_memP rem [(o, i)] (o, i);
    assert_norm (L.memP (o, i) [(o, i)])

/// **`caml_modify`**: darken the old value while marking, then write.
let bwrite (marking: bool) (g: heap) (rem: list M.slot) (o i: nat) (v: M.value) : GTot (heap & list M.slot) =
  let g1 = if marking then darken_old g o i else g in
  let rem' = remember g rem o i v in
  if pos (o + 1 + i) < heap_size then (write_word g1 (hp (o + 1 + i)) (concv v), rem') else (g1, rem')

/// **`caml_initialize`** of the fields `i ..` of the block at `o`.
let rec binit_from (g: heap) (rem: list M.slot) (o i: nat) (vs: list M.value)
  : GTot (heap & list M.slot) (decreases vs) =
  match vs with
  | [] -> (g, rem)
  | v :: tl ->
    let rem' = remember g rem o i v in
    let g1 = if pos (o + 1 + i) < heap_size then write_word g (hp (o + 1 + i)) (concv v) else g in
    binit_from g1 rem' o (i + 1) tl

let binit (g: heap) (rem: list M.slot) (o: nat) (vs: list M.value) : GTot (heap & list M.slot) =
  binit_from g rem o 0 vs

let bbarrier : T.barrier heap = { T.bwrite = bwrite; T.binit = binit }

/// ---------------------------------------------------------------------------
/// It is akhil's barrier where his runs
/// ---------------------------------------------------------------------------

/// A field pointing to `t` makes `points_to`.
#push-options "--fuel 1 --z3rlimit 40"
let rec efptu_intro (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (t: obj_addr) (i: nat)
  : Lemma (requires i < U64.v wz /\ U64.v h + 8 * (U64.v wz - 1) < heap_size /\
                    (let a : hp_addr = U64.uint_to_t (U64.v h + 8 * i) in
                     is_pointer (read_word g a) /\ read_word g a == t))
          (ensures exists_field_pointing_to_unchecked g h wz t)
          (decreases U64.v wz)
  = let idx = U64.sub wz 1UL in
    assert_norm (pow2 54 * 8 == pow2 57);
    assert_norm (pow2 57 + pow2 57 < pow2 64);
    let far = U64.add_mod h (U64.mul_mod idx mword) in
    FStar.Math.Lemmas.small_mod (U64.v idx * 8) (pow2 64);
    FStar.Math.Lemmas.small_mod (U64.v h + U64.v idx * 8) (pow2 64);
    assert (U64.v far == U64.v h + 8 * U64.v idx);
    if i = U64.v idx then begin
      let a : hp_addr = U64.uint_to_t (U64.v h + 8 * i) in
      U64.v_inj a far;
      assert (is_pointer_field (read_word g far));
      assert (is_pointer_to (read_word g far) t)
    end
    else begin
      assert (U64.v far < heap_size /\ U64.v far % 8 == 0);
      efptu_intro g h idx t i
    end
#pop-options

/// The field `i` of the block at `o`, as a byte word.
let fword_addr (o i: nat)
  : Lemma (requires pos o + 8 < heap_size /\ pos (o + 1 + i) < heap_size)
          (ensures U64.v (hp (o + 1 + i)) == U64.v (obj_of o) + 8 * i)
  = ()

/// While akhil's barrier runs, the old value's target as the model resolves
/// it is the block `MM.darken` darkens.
#push-options "--z3rlimit 40"
let darken_old_real (free: free_def) (g: heap) (o i: nat)
  : Lemma (requires M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\
                    well_formed_heap_with free g /\ in_use free g (obj_of o) /\ scannable g (obj_of o))
          (ensures pos (o + 1 + i) < heap_size /\ darken_old g o i == MM.darken g (word g (o + 1 + i)))
  = let m = cabs g in
    let k = o + 1 + i in
    abs_block_walk g o;
    abs_is_block g o;
    abs_header g o;
    msize_pos k;
    msize_pos (o + M.wz_of m o);
    let x = obj_of o in
    let w = word g k in
    fword_addr o i;
    is_no_scan_spec x g;
    no_scan_tag_val ();
    is_fw_iff g k;
    assert (M.covers (abs g) o k);
    assert (M.field m o i == absv w);
    if is_pointer w then begin
      ptr_decode w;
      wosize_of_object_bound x g;
      efptu_intro g x (wosize_of_object x g) w i;
      assert (points_to g x w);
      points_to_target_not_free free g x w;
      wf_with_parts ();
      ptr_resolve_back g w;
      let r = resolve_object w g in
      resolve_cabs g (ptr_b w) (maddr r);
      obj_maddr g r;
      U64.v_inj (obj_of (maddr r)) r;
      assert (M.ptr_field m o i);
      assert (T.old_target m o i == Some (maddr r))
    end
    else assert (T.old_target m o i == None)
#pop-options

let bwrite_idle_real (g: heap) (rem: list M.slot) (o i: nat) (v: M.value)
  : Lemma (requires pos (o + 1 + i) < heap_size)
          (ensures fst (bwrite false g rem o i v) == GB.modify_heap Ph.Idle g (hp (o + 1 + i)) (concv v))
  = ()

/// **While marking, `bwrite` is akhil's `caml_modify`** wherever his barrier
/// runs: a field of a scannable block in use, in a well-formed heap.
let bwrite_marking_real (free: free_def) (g: heap) (rem: list M.slot) (o i: nat) (v: M.value)
  : Lemma (requires M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\
                    well_formed_heap_with free g /\ in_use free g (obj_of o) /\ scannable g (obj_of o))
          (ensures pos (o + 1 + i) < heap_size /\
                   fst (bwrite true g rem o i v) == GB.modify_heap Ph.Marking g (hp (o + 1 + i)) (concv v))
  = darken_old_real free g o i

/// ---------------------------------------------------------------------------
/// The write, read as the model
/// ---------------------------------------------------------------------------

/// The toy barrier's darkening, on a model heap.
let tdark (marking: bool) (h: M.mheap) (o i: nat) : M.mheap =
  if marking then
    (match T.old_target h o i with
     | Some t -> if M.col_of h t = M.White then M.set_col h t M.Grey else h
     | None -> h)
  else h

let tdark_heq (marking: bool) (h h': M.mheap) (o i: nat)
  : Lemma (requires R.heq h h') (ensures R.heq (tdark marking h o i) (tdark marking h' o i) /\
                                         T.old_target h o i == T.old_target h' o i)
  = assert (forall (a: nat). M.resolve h a == M.resolve h' a);
    assert (M.ptr_field h o i == M.ptr_field h' o i);
    assert (M.field h o i == M.field h' o i);
    (match M.field h o i with
     | M.VPtr (M.Major a) -> assert (M.resolve h a == M.resolve h' a)
     | _ -> ());
    assert (T.old_target h o i == T.old_target h' o i);
    if marking then
      match T.old_target h o i with
      | Some t ->
        assert (M.col_of h t == M.col_of h' t);
        if M.col_of h t = M.White then begin
          let a = M.set_col h t M.Grey in
          let b = M.set_col h' t M.Grey in
          assert (forall (x: nat). a.M.hd x == b.M.hd x);
          assert (R.heq a b)
        end
      | None -> ()

let tbwrite_eq (marking: bool) (h: M.mheap) (rem: list M.slot) (o i: nat) (v: M.value)
  : Lemma (TM.tbwrite marking h rem o i v ==
           (M.set_field (tdark marking h o i) o i v, (if T.young_slot h o i v then (o, i) :: rem else rem)))
  = ()

/// Darkening the old value is the toy's on the reading.
#push-options "--z3rlimit 40"
let darken_cabs (marking: bool) (g: heap) (o i: nat)
  : Lemma (requires M.is_block (cabs g) o)
          (ensures R.heq (cabs (if marking then darken_old g o i else g)) (tdark marking (cabs g) o i))
  = if marking then
      match T.old_target (cabs g) o i with
      | Some t ->
        TM.resolve_resolves (cabs g) (match M.field (cabs g) o i with M.VPtr (M.Major a) -> a | _ -> 0) t;
        assert (M.is_block (cabs g) t);
        abs_block_walk g t;
        abs_header g t;
        is_white_iff (obj_of t) g;
        if is_white (obj_of t) g then begin
          makeGray_eq (obj_of t) g;
          cabs_recolour g t GC.Lib.Header.Gray
        end
      | None -> ()
#pop-options

let tdark_shape (marking: bool) (h: M.mheap) (o i: nat)
  : Lemma ((forall (x: nat). M.is_block (tdark marking h o i) x == M.is_block h x /\
                             M.wz_of (tdark marking h o i) x == M.wz_of h x /\
                             M.tag_of (tdark marking h o i) x == M.tag_of h x) /\
           (tdark marking h o i).M.body == h.M.body)
  = ()

/// **The write**: the reading of the byte heap after `bwrite` is the toy
/// barrier's heap, on any model heap the byte heap represents.
#push-options "--z3rlimit 40"
let bwrite_cabs (marking: bool) (m: M.mheap) (g: heap) (rem: list M.slot) (o i: nat) (v: M.value)
  : Lemma (requires R.heq m (cabs g) /\ M.is_block m o /\ i < M.wz_of m o /\ storable_w v)
          (ensures (let (g', rem') = bwrite marking g rem o i v in
                    let (m', _) = TM.tbwrite marking m rem o i v in
                    R.heq m' (cabs g') /\ rem' == remember g rem o i v))
  = let g1 = if marking then darken_old g o i else g in
    darken_cabs marking g o i;
    tdark_heq marking m (cabs g) o i;
    tdark_shape marking (cabs g) o i;
    tbwrite_eq marking m rem o i v;
    assert (M.is_block (cabs g1) o /\ i < M.wz_of (cabs g1) o);
    cabs_write_field g1 o i (concv v);
    absv_concv v
#pop-options

let bwrite_ok (marking: bool) (g: heap) (rem: list M.slot) (o i: nat) (v: M.value)
  : Lemma (T.barrier_write_at byte_rep bbarrier marking g rem o i v)
  = let (g', rem') = bwrite marking g rem o i v in
    remember_ok g rem o i v;
    let one (m: M.mheap)
      : Lemma (requires byte_rep.R.repr m g /\ T.write_pre o i v (byte_rep.R.storable v) m)
              (ensures exists (m': M.mheap). byte_rep.R.repr m' g' /\ T.write_post marking rem rem' o i v m m')
      = bwrite_cabs marking m g rem o i v;
        TM.tbwrite_m marking m rem o i v;
        let (m', _) = TM.tbwrite marking m rem o i v in
        assert (T.young_slot m o i v == T.young_slot (cabs g) o i v);
        assert (byte_rep.R.repr m' g') in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// ---------------------------------------------------------------------------
/// The Fill, read as the model
/// ---------------------------------------------------------------------------

/// The fields `i ..` of the block at `o` filled with `vs`.
let fill_at (h: M.mheap) (o i: nat) (vs: list M.value) : M.mheap =
  { h with M.body = (fun (w: nat) ->
      if o + 1 + i <= w && w - o - 1 - i < L.length vs then L.index vs (w - o - 1 - i) else h.M.body w) }

#push-options "--fuel 2 --ifuel 1"
let fill_at_cons (h: M.mheap) (o i: nat) (v: M.value) (tl: list M.value) (h1: M.mheap)
  : Lemma (requires R.heq h1 (M.set_field h o i v))
          (ensures R.heq (fill_at h1 o (i + 1) tl) (fill_at h o i (v :: tl)))
  = let bd (w: nat) : Lemma ((fill_at h1 o (i + 1) tl).M.body w == (fill_at h o i (v :: tl)).M.body w)
      = if o + 2 + i <= w && w - o - 2 - i < L.length tl then
          assert (L.index (v :: tl) (w - o - 1 - i) == L.index tl (w - o - 2 - i))
        else if w = o + 1 + i then assert (L.index (v :: tl) 0 == v) in
    FStar.Classical.forall_intro bd
#pop-options

let fill_at_zero (h: M.mheap) (o: nat) (vs: list M.value) : Lemma (R.heq (M.fill h o vs) (fill_at h o 0 vs))
  = ()

let young_slot_heq (h h': M.mheap) (o i: nat) (v: M.value)
  : Lemma (requires (forall (x: nat). h'.M.hd x == h.M.hd x) /\ h'.M.size == h.M.size)
          (ensures T.young_slot h' o i v == T.young_slot h o i v)
  = ()

#push-options "--fuel 1 --ifuel 1"
let ys_step (g g1: heap) (o i: nat) (v: M.value) (tl: list M.value) (rem1 rem': list M.slot)
  : Lemma (requires (T.young_slot (cabs g) o i v ==> L.memP (o, i) rem1) /\
                    (forall (sl: M.slot). L.memP sl rem1 ==> L.memP sl rem') /\
                    (forall (j: nat). j < L.length tl /\ T.young_slot (cabs g1) o ((i + 1) + j) (L.index tl j) ==>
                                     L.memP (o, (i + 1) + j) rem') /\
                    (forall (x: nat). (cabs g1).M.hd x == (cabs g).M.hd x))
          (ensures (forall (j: nat). j < L.length (v :: tl) /\ T.young_slot (cabs g) o (i + j) (L.index (v :: tl) j) ==>
                                    L.memP (o, i + j) rem'))
  = let one (j: nat)
      : Lemma (j < L.length (v :: tl) /\ T.young_slot (cabs g) o (i + j) (L.index (v :: tl) j) ==> L.memP (o, i + j) rem')
      = if j > 0 && j < L.length (v :: tl) then begin
          young_slot_heq (cabs g) (cabs g1) o (i + j) (L.index tl (j - 1));
          assert (i + j == (i + 1) + (j - 1))
        end in
    FStar.Classical.forall_intro one
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec binit_from_ok (g: heap) (rem: list M.slot) (o i: nat) (vs: list M.value)
  : Lemma (requires M.is_block (cabs g) o /\ i + L.length vs <= M.wz_of (cabs g) o /\
                    (forall (v: M.value). L.memP v vs ==> storable_w v))
          (ensures (let (g', rem') = binit_from g rem o i vs in
                    R.heq (cabs g') (fill_at (cabs g) o i vs) /\
                    (forall (sl: M.slot). L.memP sl rem ==> L.memP sl rem') /\
                    (forall (j: nat). j < L.length vs /\ T.young_slot (cabs g) o (i + j) (L.index vs j) ==>
                                     L.memP (o, i + j) rem')))
          (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl ->
      let rem1 = remember g rem o i v in
      remember_ok g rem o i v;
      cabs_write_field g o i (concv v);
      absv_concv v;
      let g1 = write_word g (hp (o + 1 + i)) (concv v) in
      assert (R.heq (cabs g1) (M.set_field (cabs g) o i v));
      binit_from_ok g1 rem1 o (i + 1) tl;
      fill_at_cons (cabs g) o i v tl (cabs g1);
      let (g', rem') = binit_from g1 rem1 o (i + 1) tl in
      assert (binit_from g rem o i vs == (g', rem'));
      young_slot_heq (cabs g) (cabs g1) o i v;
      ys_step g g1 o i v tl rem1 rem'
#pop-options

let binit_ok (g: heap) (rem: list M.slot) (o: nat) (vs: list M.value)
  : Lemma (T.barrier_init_at byte_rep bbarrier g rem o vs)
  = let one (m: M.mheap)
      : Lemma (requires byte_rep.R.repr m g) (ensures T.binit_m byte_rep bbarrier g rem o vs m)
      = let pre () : Lemma (requires M.is_block m o /\ L.length vs == M.wz_of m o /\ R.storable_all byte_rep vs)
                           (ensures (let (g', rem') = binit g rem o vs in
                                     byte_rep.R.repr (M.fill m o vs) g' /\
                                     (forall (sl: M.slot). L.memP sl rem ==> L.memP sl rem') /\
                                     (forall (i: nat). i < L.length vs /\ T.young_slot m o i (L.index vs i) ==>
                                                      L.memP (o, i) rem')))
          = binit_from_ok g rem o 0 vs;
            fill_at_zero m o vs;
            assert (R.heq (fill_at m o 0 vs) (fill_at (cabs g) o 0 vs)) in
        FStar.Classical.move_requires pre () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// **The byte barrier meets the barrier contract.**
let byte_barrier_ok () : Lemma (T.barrier_ok byte_rep bbarrier)
  = let w (marking: bool) (g: heap) (rem: list M.slot)
      : Lemma (forall o i v. T.barrier_write_at byte_rep bbarrier marking g rem o i v)
      = let w1 (o: nat) : Lemma (forall i v. T.barrier_write_at byte_rep bbarrier marking g rem o i v)
          = FStar.Classical.forall_intro_2 (bwrite_ok marking g rem o) in
        FStar.Classical.forall_intro w1 in
    FStar.Classical.forall_intro_3 w;
    let i (g: heap) (rem: list M.slot) : Lemma (forall o vs. T.barrier_init_at byte_rep bbarrier g rem o vs)
      = FStar.Classical.forall_intro_2 (binit_ok g rem) in
    FStar.Classical.forall_intro_2 i
