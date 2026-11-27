/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StepFacts - what the allocation, the barrier and the minor
/// collection keep
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (modules 7-9).  These three steps rewrite the major heap
/// beyond colours: the Fill of a new block, a store, the copies of a minor
/// collection and its forwarding of young pointers.  What they keep of a
/// block in use is `keepsy`: the same header, and every field that is not a
/// young pointer.  That is enough for
///   - a pointer to such a block to resolve as before (`resolve_keepy`; an
///     infix header is a word of bytes, not a young pointer);
///   - a path from a live grey block through white ones to survive, when the
///     live set is closed and every live block is kept (`lpath_keepy`).

module GC.Spec.Top.StepFacts

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let is_young (v: value) : bool = VPtr? v && Young? (VPtr?._0 v)

/// `m2` keeps block `y` up to its young pointers.
let keepsy (m m2: mheap) (y: nat) : prop =
  m2.size == m.size /\ is_block m y /\ m2.hd y == m.hd y /\
  (forall (i: nat). i < wz_of m y /\ not (is_young (field m y i)) ==> field m2 y i == field m y i)

let keeps_keepsy (m m2: mheap) (y: nat)
  : Lemma (requires keeps m m2 y /\ m2.size == m.size /\ m2.hd y == m.hd y) (ensures keepsy m m2 y)
  = ()

let keepsy_block (m m2: mheap) (y: nat)
  : Lemma (requires keepsy m m2 y)
          (ensures is_block m2 y /\ wz_of m2 y == wz_of m y /\ tag_of m2 y == tag_of m y /\ col_of m2 y == col_of m y)
  = ()

/// **A pointer to a block kept up to its young pointers resolves to it.**
let resolve_keepy (m m2: mheap) (a y: nat)
  : Lemma (requires resolve m a == Some y /\ keepsy m m2 y /\ unique_cover m2)
          (ensures resolve m2 a == Some y)
  = if a = y then ()
    else begin
      resolve_infix m a y;
      assert (field m y (a - y - 1) == m.body a);
      assert (not (is_young (field m y (a - y - 1))));
      body_of_field m m2 y a;
      assert (covers m2 y a);
      field_not_block m2 y a;
      resolve_infix_intro m2 a y
    end

/// An edge out of a kept block, to a kept block.
let edge_keepy (m m2: mheap) (sc: scan) (y z: nat)
  : Lemma (requires uedge m sc y z /\ keepsy m m2 y /\ keepsy m m2 z /\ unique_cover m2)
          (ensures uedge m2 sc y z)
  = eliminate exists (i a: nat). ptr_field m y i /\ unscanned sc y i /\ field m y i == VPtr (Major a) /\
                                 resolve m a == Some z
    with begin
      resolve_keepy m m2 a z;
      assert (ptr_field m2 y i /\ field m2 y i == VPtr (Major a))
    end

/// The target of an edge out of a closed set is in it.
let edge_closed (m: mheap) (lv: nat -> prop) (y z: nat)
  : Lemma (requires closed m lv /\ lv y /\ major_edge m y z) (ensures lv z)
  = eliminate exists (i a: nat). ptr_field m y i /\ field m y i == VPtr (Major a) /\ resolve m a == Some z
    with assert (exists (z': nat). resolve m a == Some z' /\ lv z')

let rec lpath_keepy_rec (m m2: mheap) (sc: scan) (lv lv': nat -> prop) (z: nat) (p: lpath m sc lv z)
  : Lemma (requires closed m lv /\ (forall (y: nat). lv y ==> keepsy m m2 y /\ lv' y) /\ unique_cover m2)
          (ensures lv z /\ live_reached m2 sc lv' z) (decreases p)
  = match p with
    | PGrey _ _ ->
      keepsy_block m m2 z;
      let q : lpath m2 sc lv' z = PGrey z () in ()
    | PStep y _ p0 _ ->
      lpath_keepy_rec m m2 sc lv lv' y p0;
      uedge_major m sc y z;
      edge_closed m lv y z;
      edge_keepy m m2 sc y z;
      keepsy_block m m2 z;
      let q0 = FStar.IndefiniteDescription.indefinite_description_ghost (lpath m2 sc lv' y) (fun _ -> True) in
      let q : lpath m2 sc lv' z = PStep y z q0 () in ()

/// **Paths from a live grey block survive a step that keeps the live blocks.**
let lpath_keepy (m m2: mheap) (sc: scan) (lv lv': nat -> prop) (z: nat)
  : Lemma (requires closed m lv /\ (forall (y: nat). lv y ==> keepsy m m2 y /\ lv' y) /\ unique_cover m2 /\
                    live_reached m sc lv z)
          (ensures live_reached m2 sc lv' z)
  = let f (p: lpath m sc lv z) : Lemma (live_reached m2 sc lv' z) = lpath_keepy_rec m m2 sc lv lv' z p in
    C.forall_intro f

/// The block being scanned is live, so kept: the scan stays valid.
let scan_keepy (#c: comps) (x x': config c) (m m2: mheap)
  : Lemma (requires scan_of x' == scan_of x /\ scan_ok x m /\
                    (forall (y: nat). union x.snap x.allocd y ==> keepsy m m2 y /\ union x'.snap x'.allocd y))
          (ensures scan_ok x' m2)
  = match scan_of x with
    | Some (o, _) -> keepsy_block m m2 o
    | None -> ()

/// ... and its measure is unchanged.
let fleft_keepy (#c: comps) (x: config c) (m m2: mheap)
  : Lemma (requires m2.size == m.size /\ (match scan_of x with Some (o, _) -> keepsy m m2 o | None -> True))
          (ensures fleft m2 (scan_of x) == fleft m (scan_of x))
  = match scan_of x with
    | Some (o, _) -> keepsy_block m m2 o
    | None -> ()

/// The measure reads only the size and the scanned block's width.
let fleft_same (m m': mheap) (sc: scan)
  : Lemma (requires m'.size == m.size /\
                    (match sc with Some (s, _) -> is_block m' s == is_block m s /\ wz_of m' s == wz_of m s | None -> True))
          (ensures fleft m' sc == fleft m sc)
  = ()

/// A list member is at some index.
let rec mem_index (#t: Type) (v: t) (l: list t)
  : Lemma (requires L.memP v l) (ensures exists (i: nat). i < L.length l /\ L.index l i == v)
  = match l with
    | hd :: tl ->
      if FStar.IndefiniteDescription.strong_excluded_middle (v == hd) then assert (L.index l 0 == v)
      else begin
        mem_index v tl;
        eliminate exists (i: nat). i < L.length tl /\ L.index tl i == v
        with assert (L.index l (i + 1) == v)
      end

/// The Fill keeps the blocks, so the tiling.
let fill_blocks (m: mheap) (o: nat) (vs: list value) (y: nat)
  : Lemma (is_block (fill m o vs) y == is_block m y /\ wz_of (fill m o vs) y == wz_of m y /\
           tag_of (fill m o vs) y == tag_of m y /\ col_of (fill m o vs) y == col_of m y /\
           (fill m o vs).hd y == m.hd y /\ (fill m o vs).size == m.size)
  = ()

let fill_wf (m: mheap) (o: nat) (vs: list value)
  : Lemma (requires well_formed m) (ensures well_formed (fill m o vs) /\ unique_cover (fill m o vs))
  = C.forall_intro (fill_blocks m o vs);
    assert (forall (y w: nat). covers (fill m o vs) y w == covers m y w)

/// While marking, the live set is closed and in use.
let live_iu (#c: comps) (x: config c) (z: nat)
  : Lemma (requires Marking? x.ph /\ r_live x (vw x) /\ union x.snap x.allocd z) (ensures in_use_c x z)
  = reveal_opaque (`%r_live) (r_live #c)

let closed_step (#c: comps) (x: config c) (z i a: nat)
  : Lemma (requires Marking? x.ph /\ r_col x (vw x) /\ r_live x (vw x) /\ union x.snap x.allocd z /\
                    ptr_field (mj x) z i /\ field (mj x) z i == VPtr (Major a))
          (ensures in_use_c x z /\
                   (exists (t: nat). resolve (mj x) a == Some t /\ union x.snap x.allocd t /\ in_use_c x t))
  = reveal_opaque (`%r_col) (r_col #c);
    live_iu x z;
    eliminate exists (t: nat). resolve (mj x) a == Some t /\ union x.snap x.allocd t
    with live_iu x t

let cover_unique_c (m: mheap) (o1 o2 w: nat)
  : Lemma (requires unique_cover m /\ covers m o1 w /\ covers m o2 w) (ensures o1 == o2)
  = ()

/// Same blocks, sizes and tags, and every word but `n0` unchanged, where
/// `n0` is a field word of a block that is not a closure: `resolve` is
/// unchanged (an infix header lies in a closure).
let same_shape (m m': mheap) : prop =
  m'.size == m.size /\
  (forall (y: nat). is_block m' y == is_block m y /\ wz_of m' y == wz_of m y /\ tag_of m' y == tag_of m y)

let one_word_resolve (m m': mheap) (o0 n0 b: nat)
  : Lemma (requires unique_cover m /\ same_shape m m' /\ (forall (n: nat). n <> n0 ==> m'.body n == m.body n) /\
                    covers m o0 n0 /\ o0 < n0 /\ tag_of m o0 <> closure_tag)
          (ensures resolve m' b == resolve m b)
  = if is_block m b then ()
    else if b <> n0 then begin
      assert (m'.body b == m.body b);
      match infix_hdr (m.body b) with
      | Some k -> if k <= b then assert (is_block m' (b - k) == is_block m (b - k) /\ tag_of m' (b - k) == tag_of m (b - k) /\
                                       wz_of m' (b - k) == wz_of m (b - k))
      | None -> ()
    end else begin
      (match resolve m b with
       | Some t -> resolve_infix m b t; assert (covers m t b); cover_unique_c m t o0 b
       | None -> ());
      (match resolve m' b with
       | Some t -> resolve_infix m' b t;
                  assert (is_block m t /\ tag_of m t == closure_tag /\ wz_of m t == wz_of m' t);
                  assert (covers m t b); cover_unique_c m t o0 b
       | None -> ())
    end

/// `r_live` depends only on the phase, the live sets and what is in use.
let r_live_iu (#c: comps) (x x': config c) (w w': world)
  : Lemma (requires r_live x w /\ x'.ph == x.ph /\ x'.snap == x.snap /\ x'.allocd == x.allocd /\
                    (forall (z: nat). iu x' w'.maj z == iu x w.maj z))
          (ensures r_live x' w')
  = reveal_opaque (`%r_live) (r_live #c)

/// Outside marking, `r_col` depends only on the colours of blocks in use.
let r_col_iu (#c: comps) (x x': config c) (w w': world)
  : Lemma (requires r_col x w /\ ~(Marking? x.ph) /\ x'.ph == x.ph /\ x'.snap == x.snap /\ x'.allocd == x.allocd /\
                    scan_of x' == scan_of x /\
                    (forall (z: nat). iu x' w'.maj z == iu x w.maj z /\ (iu x w.maj z ==> col_of w'.maj z == col_of w.maj z)))
          (ensures r_col x' w')
  = reveal_opaque (`%r_col) (r_col #c);
    match x.ph with
    | Sweeping p -> assert (forall (z: nat). live x' z <==> live x z)
    | _ -> ()

/// A copy whose fields are its young object's, forwarded: an infix pointer
/// into the object resolves to the copy at the same offset (an infix header
/// is a word of bytes, which forwarding keeps).
let infix_word (y m': mheap) (b q cp: nat)
  : Lemma (requires resolve y b == Some q /\ b <> q /\ field m' cp (b - q - 1) == field y q (b - q - 1))
          (ensures m'.body (cp + (b - q)) == y.body b)
  = ()

let copy_infix (y m': mheap) (fwd: nat -> option nat) (b q cp: nat)
  : Lemma (requires resolve y b == Some q /\ b <> q /\ is_block m' cp /\ unique_cover m' /\
                    wz_of m' cp == wz_of y q /\ tag_of m' cp == tag_of y q /\
                    (forall (j: nat). j < wz_of y q ==> field m' cp j == fwd_field y q j y fwd))
          (ensures resolve m' (cp + (b - q)) == Some cp)
  = resolve_infix y b q;
    let j : nat = b - q - 1 in
    assert (field y q j == y.body b);
    assert (VInt? (field y q j));
    assert (field m' cp j == fwd_field y q j y fwd);
    assert (field m' cp j == field y q j);
    infix_word y m' b q cp;
    assert (covers m' cp (cp + (b - q)));
    field_not_block m' cp (cp + (b - q));
    resolve_infix_intro m' (cp + (b - q)) cp
