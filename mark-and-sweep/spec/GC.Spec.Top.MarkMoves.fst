/// ---------------------------------------------------------------------------
/// GC.Spec.Top.MarkMoves - the mark's moves on the model
/// ---------------------------------------------------------------------------
///
/// Design doc §18 (U1).  A slice is a list of moves (`MBegin`, `MGrey`,
/// `MBlack`).  `minv` is the marking invariant on a model heap with the
/// mark's scan: the tricolour invariant over all blocks, with paths along the
/// fields still to scan (`lpath`), the live set closed, and the block being
/// scanned a live grey scannable block.  Every move the model allows keeps
/// `minv`, changes colours only, only darkens, and strictly decreases the
/// measure (`mark_dec`); so does a non-empty list of them.  `moves_repr`
/// follows the mark's contract along a slice.

module GC.Spec.Top.MarkMoves

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.RInv
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

let mscan_ok (m: mheap) (sc: scan) (lv: nat -> prop) : prop =
  match sc with
  | Some (o, i) -> is_block m o /\ col_of m o == Grey /\ scannable (tag_of m o) /\ lv o /\ i <= wz_of m o
  | None -> True

let minv (m: mheap) (sc: scan) (s a: nat -> prop) : prop =
  well_formed m /\
  (forall (o: nat). union s a o ==> is_block m o) /\
  (forall (o: nat). is_block m o /\ dark (col_of m o) ==> union s a o) /\
  (forall (o: nat). a o ==> col_of m o == Black) /\
  (forall (o: nat). s o /\ col_of m o == White ==> live_reached m sc (union s a) o) /\
  closed m (union s a) /\
  mscan_ok m sc (union s a)

/// ---------------------------------------------------------------------------
/// Colours only
/// ---------------------------------------------------------------------------

let co_covers (m m': mheap) (o w: nat)
  : Lemma (requires colours_only m m') (ensures covers m' o w == covers m o w)
  = ()

let co_wf (m m': mheap)
  : Lemma (requires colours_only m m' /\ well_formed m) (ensures well_formed m')
  = C.forall_intro_2 (co_covers m m')

let co_resolve (m m': mheap) (a: nat)
  : Lemma (requires colours_only m m') (ensures resolve m' a == resolve m a)
  = ()

let co_closed1 (m m': mheap) (lv: nat -> prop) (o i a: nat)
  : Lemma (requires colours_only m m' /\ closed m lv /\ lv o /\ ptr_field m' o i /\ field m' o i == VPtr (Major a))
          (ensures exists (o': nat). resolve m' a == Some o' /\ lv o')
  = co_resolve m m' a;
    assert (ptr_field m o i /\ field m o i == VPtr (Major a))

let co_closed (m m': mheap) (lv: nat -> prop)
  : Lemma (requires colours_only m m' /\ closed m lv) (ensures closed m' lv)
  = C.forall_intro_3 (fun o i a -> C.move_requires (co_closed1 m m' lv o i) a)

let co_trans (m1 m2 m3: mheap)
  : Lemma (requires colours_only m1 m2 /\ colours_only m2 m3 /\ darken_only m1 m2 /\ darken_only m2 m3)
          (ensures colours_only m1 m3 /\ darken_only m1 m3)
  = ()

let co_refl (m: mheap) : Lemma (colours_only m m /\ darken_only m m) = ()

/// ---------------------------------------------------------------------------
/// The measure
/// ---------------------------------------------------------------------------

let dec_trans (m1 m2 m3: mheap) (s1 s2 s3: scan) (lv: nat -> prop)
  : Lemma (requires mark_dec m1 s1 m2 s2 lv /\ mark_dec m2 s2 m3 s3 lv) (ensures mark_dec m1 s1 m3 s3 lv)
  = ()

/// ---------------------------------------------------------------------------
/// Paths, move by move
/// ---------------------------------------------------------------------------

/// A path in `m` with scan `sc` gives one in `m'` with scan `sc'`, given
/// that the grey starts are reached (or excepted) and each edge carries
/// over.
let rec ptrans (m m': mheap) (sc sc': scan) (lv ex: nat -> prop) (z: nat) (p: lpath m sc lv z)
  : Lemma (requires closed m lv /\
                    (forall (g: nat). is_block m g /\ col_of m g == Grey /\ lv g ==> live_reached m' sc' lv g \/ ex g) /\
                    (forall (y z: nat). (live_reached m' sc' lv y \/ ex y) /\ lv y /\ uedge m sc y z /\
                                   is_block m z /\ col_of m z == White /\ lv z ==> live_reached m' sc' lv z))
          (ensures lv z /\ (live_reached m' sc' lv z \/ ex z)) (decreases p)
  = match p with
    | PGrey _ _ -> ()
    | PStep y _ p0 _ ->
      ptrans m m' sc sc' lv ex y p0;
      uedge_major m sc y z;
      eliminate exists (i a: nat). ptr_field m y i /\ field m y i == VPtr (Major a) /\ resolve m a == Some z
      with assert (exists (t: nat). resolve m a == Some t /\ lv t)

let ptrans_all (m m': mheap) (sc sc': scan) (lv ex: nat -> prop) (z: nat)
  : Lemma (requires closed m lv /\
                    (forall (g: nat). is_block m g /\ col_of m g == Grey /\ lv g ==> live_reached m' sc' lv g \/ ex g) /\
                    (forall (y z: nat). (live_reached m' sc' lv y \/ ex y) /\ lv y /\ uedge m sc y z /\
                                   is_block m z /\ col_of m z == White /\ lv z ==> live_reached m' sc' lv z) /\
                    live_reached m sc lv z)
          (ensures live_reached m' sc' lv z \/ ex z)
  = let f (p: lpath m sc lv z) : Lemma (live_reached m' sc' lv z \/ ex z) = ptrans m m' sc sc' lv ex z p in
    C.forall_intro f

/// A grey block is reached.
let grey_lr (m: mheap) (sc: scan) (lv: nat -> prop) (g: nat)
  : Lemma (requires is_block m g /\ col_of m g == Grey /\ lv g) (ensures live_reached m sc lv g)
  = let p : lpath m sc lv g = PGrey g () in ()

/// A white block one edge on.
let step_lr (m: mheap) (sc: scan) (lv: nat -> prop) (y z: nat)
  : Lemma (requires live_reached m sc lv y /\ uedge m sc y z /\ is_block m z /\ col_of m z == White)
          (ensures live_reached m sc lv z)
  = let q0 = FStar.IndefiniteDescription.indefinite_description_ghost (lpath m sc lv y) (fun _ -> True) in
    let q : lpath m sc lv z = PStep y z q0 () in ()

/// ---------------------------------------------------------------------------
/// MBegin
/// ---------------------------------------------------------------------------

let begin_edge (m: mheap) (o y z: nat)
  : Lemma (requires uedge m None y z) (ensures uedge m (Some (o, 0)) y z)
  = ()

let begin_ok (m: mheap) (sc: scan) (s a: nat -> prop) (o: nat)
  : Lemma (requires minv m sc s a /\ move_ok m sc (MBegin o))
          (ensures minv m (Some (o, 0)) s a /\ mark_dec m sc m (Some (o, 0)) (union s a))
  = let lv = union s a in
    let sc' = Some (o, 0) in
    C.forall_intro (C.move_requires (grey_lr m sc' lv));
    C.forall_intro_2 (fun y z -> C.move_requires (begin_edge m o y) z);
    C.forall_intro_2 (fun y z -> C.move_requires (step_lr m sc' lv y) z);
    C.forall_intro (C.move_requires (ptrans_all m m None sc' lv (fun _ -> False)));
    assert (fleft m sc' < fleft m sc)

/// ---------------------------------------------------------------------------
/// MGrey
/// ---------------------------------------------------------------------------

let grey_col (m: mheap) (o i x: nat)
  : Lemma (col_of (darken_field m o i) x ==
             (if Some x = field_target m o i && col_of m x = White then Grey else col_of m x) /\
           colours_only m (darken_field m o i) /\ darken_only m (darken_field m o i))
  = ()

let grey_edge (m: mheap) (o i y z: nat)
  : Lemma (requires uedge m (Some (o, i)) y z /\ field_target m o i =!= Some z)
          (ensures uedge (darken_field m o i) (Some (o, i + 1)) y z)
  = let m' = darken_field m o i in
    grey_col m o i 0;
    eliminate exists (k a: nat). ptr_field m y k /\ unscanned (Some (o, i)) y k /\ field m y k == VPtr (Major a) /\
                                 resolve m a == Some z
    with begin
      co_resolve m m' a;
      assert (ptr_field m' y k /\ field m' y k == VPtr (Major a) /\ resolve m' a == Some z)
    end

let grey_target (m: mheap) (lv: nat -> prop) (o i: nat)
  : Lemma (requires closed m lv /\ lv o)
          (ensures (match field_target m o i with Some t -> lv t /\ is_block m t | None -> True))
  = match field_target m o i with
    | Some t ->
      let VPtr (Major a) = field m o i in
      assert (exists (t': nat). resolve m a == Some t' /\ lv t')
    | None -> ()

let grey_h2 (m: mheap) (lv: nat -> prop) (o i y z: nat)
  : Lemma (requires live_reached (darken_field m o i) (Some (o, i + 1)) lv y /\ uedge m (Some (o, i)) y z /\
                    is_block m z /\ col_of m z == White /\ lv z)
          (ensures live_reached (darken_field m o i) (Some (o, i + 1)) lv z)
  = let m' = darken_field m o i in
    grey_col m o i z;
    if field_target m o i = Some z then grey_lr m' (Some (o, i + 1)) lv z
    else begin grey_edge m o i y z; step_lr m' (Some (o, i + 1)) lv y z end

let grey_ok (m: mheap) (s a: nat -> prop) (o i: nat)
  : Lemma (requires minv m (Some (o, i)) s a /\ move_ok m (Some (o, i)) MGrey)
          (ensures (let m' = darken_field m o i in
                    minv m' (Some (o, i + 1)) s a /\ colours_only m m' /\ darken_only m m' /\
                    mark_dec m (Some (o, i)) m' (Some (o, i + 1)) (union s a)))
  = let lv = union s a in
    let sc = Some (o, i) in
    let sc' = Some (o, i + 1) in
    let m' = darken_field m o i in
    C.forall_intro (grey_col m o i);
    grey_target m lv o i;
    co_wf m m';
    co_closed m m' lv;
    let h1 (g: nat) : Lemma (is_block m g /\ col_of m g == Grey /\ lv g ==> live_reached m' sc' lv g)
      = if is_block m g && col_of m g = Grey then grey_lr m' sc' lv g in
    C.forall_intro h1;
    C.forall_intro_2 (fun y z -> C.move_requires (grey_h2 m lv o i y) z);
    C.forall_intro (C.move_requires (ptrans_all m m' sc sc' lv (fun _ -> False)));
    assert (well_formed m');
    assert (forall (x: nat). lv x ==> is_block m' x);
    assert (forall (x: nat). is_block m' x /\ dark (col_of m' x) ==> lv x);
    assert (forall (x: nat). a x ==> col_of m' x == Black);
    assert (forall (x: nat). s x /\ col_of m' x == White ==> live_reached m' sc' lv x);
    assert (mscan_ok m' sc' lv);
    match field_target m o i with
    | Some t -> if col_of m t = White then assert (white_live m lv t /\ ~(white_live m' lv t))
    | None -> ()

/// ---------------------------------------------------------------------------
/// MBlack
/// ---------------------------------------------------------------------------

let black_scan (sc: scan) (o: nat) : scan = move_scan sc (MBlack o)

let black_col (m: mheap) (o x: nat)
  : Lemma (requires is_block m o)
          (ensures col_of (set_col m o Black) x == (if x = o then Black else col_of m x) /\
                   colours_only m (set_col m o Black))
  = ()

/// No field of the block blackened is still to scan.
let black_noedge (m: mheap) (sc: scan) (o z: nat)
  : Lemma (requires move_ok m sc (MBlack o) /\ uedge m sc o z) (ensures False)
  = ()

let black_edge (m: mheap) (sc: scan) (o y z: nat)
  : Lemma (requires is_block m o /\ uedge m sc y z)
          (ensures uedge (set_col m o Black) (black_scan sc o) y z)
  = let m' = set_col m o Black in
    black_col m o 0;
    eliminate exists (k a: nat). ptr_field m y k /\ unscanned sc y k /\ field m y k == VPtr (Major a) /\
                                 resolve m a == Some z
    with begin
      co_resolve m m' a;
      assert (ptr_field m' y k /\ field m' y k == VPtr (Major a) /\ resolve m' a == Some z)
    end

let black_h2 (m: mheap) (sc: scan) (lv: nat -> prop) (o y z: nat)
  : Lemma (requires move_ok m sc (MBlack o) /\ (live_reached (set_col m o Black) (black_scan sc o) lv y \/ y == o) /\
                    uedge m sc y z /\ is_block m z /\ col_of m z == White)
          (ensures live_reached (set_col m o Black) (black_scan sc o) lv z)
  = if y = o then black_noedge m sc o z
    else begin
      black_edge m sc o y z;
      black_col m o z;
      step_lr (set_col m o Black) (black_scan sc o) lv y z
    end

let black_ok (m: mheap) (sc: scan) (s a: nat -> prop) (o: nat)
  : Lemma (requires minv m sc s a /\ move_ok m sc (MBlack o))
          (ensures (let m' = set_col m o Black in
                    minv m' (black_scan sc o) s a /\ colours_only m m' /\ darken_only m m' /\
                    mark_dec m sc m' (black_scan sc o) (union s a)))
  = let lv = union s a in
    let sc' = black_scan sc o in
    let m' = set_col m o Black in
    C.forall_intro (black_col m o);
    co_wf m m';
    co_closed m m' lv;
    let ex (z: nat) : prop = z == o in
    let h1 (g: nat) : Lemma (is_block m g /\ col_of m g == Grey /\ lv g ==> live_reached m' sc' lv g \/ ex g)
      = if is_block m g && col_of m g = Grey && g <> o then grey_lr m' sc' lv g in
    C.forall_intro h1;
    C.forall_intro_2 (fun y z -> C.move_requires (black_h2 m sc lv o y) z);
    C.forall_intro (C.move_requires (ptrans_all m m' sc sc' lv ex));
    assert (well_formed m');
    assert (forall (x: nat). lv x ==> is_block m' x);
    assert (forall (x: nat). is_block m' x /\ dark (col_of m' x) ==> lv x);
    assert (forall (x: nat). a x ==> col_of m' x == Black);
    assert (forall (x: nat). s x /\ col_of m' x == White ==> live_reached m' sc' lv x);
    assert (mscan_ok m' sc' lv);
    assert (darken_only m m');
    assert (grey_live m lv o /\ ~(grey_live m' lv o))

/// ---------------------------------------------------------------------------
/// One move, then a slice
/// ---------------------------------------------------------------------------

let move_inv (m: mheap) (sc: scan) (s a: nat -> prop) (mv: move)
  : Lemma (requires minv m sc s a /\ move_ok m sc mv)
          (ensures (let m' = move_heap m sc mv in let sc' = move_scan sc mv in
                    minv m' sc' s a /\ colours_only m m' /\ darken_only m m' /\
                    mark_dec m sc m' sc' (union s a)))
  = match mv with
    | MBegin o -> begin_ok m sc s a o; co_refl m
    | MGrey -> let Some (o, i) = sc in grey_ok m s a o i
    | MBlack o -> black_ok m sc s a o

/// The model's slice.
let rec mfold (m: mheap) (sc: scan) (mvs: list move) : Tot (mheap & scan) (decreases mvs) =
  match mvs with
  | [] -> (m, sc)
  | mv :: tl -> mfold (move_heap m sc mv) (move_scan sc mv) tl

let rec moves_inv (m: mheap) (sc: scan) (s a: nat -> prop) (mvs: list move)
  : Lemma (requires minv m sc s a /\ moves_ok m sc mvs)
          (ensures (let (m', sc') = mfold m sc mvs in
                    minv m' sc' s a /\ colours_only m m' /\ darken_only m m' /\
                    (Cons? mvs ==> mark_dec m sc m' sc' (union s a))))
          (decreases mvs)
  = match mvs with
    | [] -> co_refl m
    | mv :: tl ->
      move_inv m sc s a mv;
      let m1 = move_heap m sc mv in
      let sc1 = move_scan sc mv in
      moves_inv m1 sc1 s a tl;
      let (m', sc') = mfold m1 sc1 tl in
      co_trans m m1 m';
      if Cons? tl then dec_trans m m1 m' sc sc1 sc' (union s a)

/// **The mark's contract along a slice**: the code's heap after the slice
/// represents the model's, and its state reads as the model's scan.
let rec moves_repr (#t #yt: Type0) (r: rep t yt) (mk: mark t yt) (h: t) (ms: mk.mstate) (mvs: list move)
    (m: mheap) (s a: nat -> prop)
  : Lemma (requires moves_at r mk h ms mvs /\ r.repr m h /\ minv m (mk.mscan ms) s a /\
                    moves_ok m (mk.mscan ms) mvs)
          (ensures (let (h', ms') = mmoves mk h ms mvs in
                    r.repr (fst (mfold m (mk.mscan ms) mvs)) h' /\ mk.mscan ms' == snd (mfold m (mk.mscan ms) mvs)))
          (decreases mvs)
  = match mvs with
    | [] -> ()
    | mv :: tl ->
      let sc = mk.mscan ms in
      assert (mark_move_m r mk h ms mv m);
      move_inv m sc s a mv;
      let (h1, ms1) = mk.mmove h ms mv in
      moves_repr r mk h1 ms1 tl (move_heap m sc mv) s a

/// ---------------------------------------------------------------------------
/// For instances and witness runs
/// ---------------------------------------------------------------------------

/// A move keeps the heap well formed.
let move_wf (m: mheap) (sc: scan) (mv: move)
  : Lemma (requires well_formed m /\ move_ok m sc mv) (ensures well_formed (move_heap m sc mv))
  = match mv with
    | MBegin _ -> ()
    | MGrey -> let Some (o, i) = sc in grey_col m o i 0; co_wf m (darken_field m o i)
    | MBlack o -> black_col m o 0; co_wf m (set_col m o Black)

/// Heaps with the same headers and words allow the same moves, to such heaps.
let field_target_heq (m m': mheap) (o i: nat)
  : Lemma (requires heq m m') (ensures field_target m o i == field_target m' o i)
  = assert (ptr_field m o i == ptr_field m' o i);
    assert (field m o i == field m' o i);
    match field m o i with
    | VPtr (Major a) -> assert (resolve m a == resolve m' a)
    | _ -> ()

let move_heq (m m': mheap) (sc: scan) (mv: move)
  : Lemma (requires heq m m') (ensures move_ok m sc mv == move_ok m' sc mv /\ heq (move_heap m sc mv) (move_heap m' sc mv))
  = match mv, sc with
    | MGrey, Some (o, i) -> field_target_heq m m' o i
    | _ -> ()

let rec moves_ok_heq (m m': mheap) (sc: scan) (mvs: list move)
  : Lemma (requires heq m m') (ensures moves_ok m sc mvs == moves_ok m' sc mvs) (decreases mvs)
  = match mvs with
    | [] -> ()
    | mv :: tl -> move_heq m m' sc mv; moves_ok_heq (move_heap m sc mv) (move_heap m' sc mv) (move_scan sc mv) tl
