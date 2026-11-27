/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ByteMark - the mark on the byte heap
/// ---------------------------------------------------------------------------
///
/// The mark of the byte-level collectors as a component of
/// GC.Spec.Top.Iface over `byte_rep`.  It needs no allocator, so pages and
/// first-fit share it.  It is akhil's incremental mark, the one the page
/// cycle runs (`GC.Spec.Pages.Cycle.Mark`):
///
///   * `bstart`: root darkening (akhil's `GC.Gen.MarkPhase.Start.darkened`,
///     4.14's `caml_darken_all_roots_start`) of the major pointers in the
///     roots and in the nursery's fields that the model resolves;
///   * `bmove`: akhil's moves of `GC.Spec.MarkPhase.Slice` one at a time --
///     start to scan a block, scan its next field (the target darkened),
///     blacken it; the state is the scan.
///   * `bslice` (kept for the account of akhil's slice): one object, at the
///     lowest grey block, scanned whole; `bslice_moves`: it is
///     `S.mark_steps` from no partly scanned object back to none.
///
/// Proved: `byte_mark_ok : mark_ok byte_rep bmark`: each move, read as the
/// model, is the model's move (`move_grey`, `move_black`); the start's
/// canonical reading is the toy start (`GC.Spec.Top.ToyMark`), whose model
/// proofs give the contract.  `bslice_ok`: the whole-object slice is the
/// toy slice at the same grey block.

module GC.Spec.Top.ByteMark

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
module BB = GC.Spec.Top.ByteBarrier
module S = GC.Spec.MarkPhase.Slice
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module HG = GC.Spec.HeapGraph
module MStart = GC.Gen.MarkPhase.Start
module MB = GC.Impl.MarkBounded
module MV = GC.Spec.Top.MarkMoves

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The slice
/// ---------------------------------------------------------------------------

/// Scanning the fields `k ..` of `x`: akhil's grey moves.
let rec scan_from (g: heap) (x: obj_addr) (k: Prims.pos) (wz: nat)
  : GTot heap (decreases (if k > wz then 0 else wz + 1 - k)) =
  if k > wz || k >= pow2 64 then g
  else scan_from (S.scan_field g x (U64.uint_to_t k)) x (k + 1) wz

/// One object: scan its fields, then blacken it (a no-scan block is only
/// blackened).
let scan_obj (g: heap) (x: obj_addr) : GTot heap =
  if is_no_scan x g then makeBlack x g
  else makeBlack x (scan_from g x 1 (U64.v (wosize_of_object x g)))

/// **A slice**: one object, the lowest grey block.
let bslice (g: heap) : GTot heap =
  match TM.find_grey (cabs g) msize with
  | Some t -> if pos t + 8 < heap_size then scan_obj g (obj_of t) else g
  | None -> g

/// ---------------------------------------------------------------------------
/// The slice in the model
/// ---------------------------------------------------------------------------

/// The fields `j .. n` of `o` scanned: each target greyed if white (the
/// barrier's darkening, `BB.tdark`).
let rec mscan (h: M.mheap) (o: nat) (j n: nat) : Tot M.mheap (decreases (if j >= n then 0 else n - j)) =
  if j >= n then h else mscan (BB.tdark true h o j) o (j + 1) n

/// A field among `j .. n` of `o` resolves to `x`.
let rec tin (h: M.mheap) (o: nat) (j n: nat) (x: nat) : Tot bool (decreases (if j >= n then 0 else n - j)) =
  if j >= n then false else (T.old_target h o j = Some x) || tin h o (j + 1) n x

/// Two heaps with the same blocks, sizes, tags and words.
let same_but_cols (h h': M.mheap) : prop =
  h'.M.size == h.M.size /\ (forall (w: nat). h'.M.body w == h.M.body w) /\
  (forall (x: nat). Some? (h'.M.hd x) == Some? (h.M.hd x) /\ M.wz_of h' x == M.wz_of h x /\ M.tag_of h' x == M.tag_of h x)

let old_target_cols (h h': M.mheap) (o j: nat)
  : Lemma (requires same_but_cols h h') (ensures T.old_target h' o j == T.old_target h o j)
  = assert (forall (a: nat). M.resolve h' a == M.resolve h a);
    assert (M.ptr_field h' o j == M.ptr_field h o j);
    (match M.field h o j with
     | M.VPtr (M.Major a) -> assert (M.resolve h a == M.resolve h' a)
     | _ -> ())

#push-options "--fuel 1"
let rec tin_cols (h h': M.mheap) (o j n x: nat)
  : Lemma (requires same_but_cols h h') (ensures tin h' o j n x == tin h o j n x)
          (decreases (if j >= n then 0 else n - j))
  = if j < n then begin old_target_cols h h' o j; tin_cols h h' o (j + 1) n x end

let rec tin_iff (h: M.mheap) (o j n x: nat)
  : Lemma (ensures tin h o j n x == true <==> (exists (i: nat). j <= i /\ i < n /\ T.old_target h o i == Some x))
          (decreases (if j >= n then 0 else n - j))
  = if j < n then tin_iff h o (j + 1) n x
#pop-options

let tdark_cols (h: M.mheap) (o j: nat)
  : Lemma (same_but_cols h (BB.tdark true h o j) /\
           (forall (x: nat). M.col_of (BB.tdark true h o j) x ==
              (if M.col_of h x = M.White && M.is_block h x && T.old_target h o j = Some x then M.Grey
               else M.col_of h x)))
  = match T.old_target h o j with
    | Some t -> TM.resolve_resolves h (match M.field h o j with M.VPtr (M.Major a) -> a | _ -> 0) t
    | None -> ()

/// The colours after scanning.
#push-options "--fuel 1 --z3rlimit 40"
let rec mscan_spec (h: M.mheap) (o j n: nat)
  : Lemma (ensures same_but_cols h (mscan h o j n) /\
                   (forall (x: nat). M.col_of (mscan h o j n) x ==
                      (if M.col_of h x = M.White && M.is_block h x && tin h o j n x then M.Grey else M.col_of h x)))
          (decreases (if j >= n then 0 else n - j))
  = if j < n then begin
      let h1 = BB.tdark true h o j in
      tdark_cols h o j;
      mscan_spec h1 o (j + 1) n;
      let c (x: nat) : Lemma (tin h1 o (j + 1) n x == tin h o (j + 1) n x) = tin_cols h h1 o (j + 1) n x in
      FStar.Classical.forall_intro c
    end
#pop-options

/// The edges of `o` are the targets of its fields.
let edge_tin (h: M.mheap) (o x: nat)
  : Lemma (TM.edge_b h o x == tin h o 0 (M.wz_of h o) x)
  = TM.edge_b_iff h o x;
    tin_iff h o 0 (M.wz_of h o) x;
    let one (i: nat) : Lemma (T.old_target h o i == Some x <==>
                              (exists (a: nat). M.ptr_field h o i /\ M.field h o i == M.VPtr (M.Major a) /\
                                                M.resolve h a == Some x))
      = match M.field h o i with
        | M.VPtr (M.Major a) -> ()
        | _ -> () in
    FStar.Classical.forall_intro one

/// One header of the toy slice.
let hd_point (h h1: M.mheap) (o x n: nat)
  : Lemma (requires Some? (h1.M.hd x) == Some? (h.M.hd x) /\ M.wz_of h1 x == M.wz_of h x /\
                    M.tag_of h1 x == M.tag_of h x /\
                    M.col_of h1 x == (if M.col_of h x = M.White && M.is_block h x && tin h o 0 n x then M.Grey
                                      else M.col_of h x) /\
                    TM.edge_b h o x == tin h o 0 n x /\
                    (tin h o 0 n x ==> M.is_block h x))
          (ensures (TM.tmslice_with h o).M.hd x == (M.set_col h1 o M.Black).M.hd x)
  = match h.M.hd x with
    | None -> ()
    | Some hx ->
      let Some hy = h1.M.hd x in
      assert (hy == ({ M.wz = hx.M.wz; M.tag = hx.M.tag; M.col = hy.M.col }))

let tin_block (h: M.mheap) (o n x: nat) : Lemma (tin h o 0 n x ==> M.is_block h x)
  = tin_iff h o 0 n x;
    let one (i: nat) : Lemma (T.old_target h o i == Some x ==> M.is_block h x)
      = match M.field h o i with
        | M.VPtr (M.Major a) -> TM.resolve_resolves h a x
        | _ -> () in
    FStar.Classical.forall_intro one

/// **The toy slice at `o` is scanning every field of `o`, then blackening it.**
let tmslice_scan (h: M.mheap) (o: nat)
  : Lemma (requires M.is_block h o /\ M.col_of h o == M.Grey)
          (ensures R.heq (TM.tmslice_with h o) (M.set_col (mscan h o 0 (M.wz_of h o)) o M.Black))
  = let n = M.wz_of h o in
    mscan_spec h o 0 n;
    let h1 = mscan h o 0 n in
    let one (x: nat) : Lemma ((TM.tmslice_with h o).M.hd x == (M.set_col h1 o M.Black).M.hd x)
      = edge_tin h o x;
        tin_block h o n x;
        hd_point h h1 o x n in
    FStar.Classical.forall_intro one

/// A slice with no fields to scan only blackens.
let tmslice_noscan (h: M.mheap) (o: nat)
  : Lemma (requires M.is_block h o /\ not (M.scannable (M.tag_of h o)))
          (ensures R.heq (TM.tmslice_with h o) (M.set_col h o M.Black))
  = let one (x: nat) : Lemma ((TM.tmslice_with h o).M.hd x == (M.set_col h o M.Black).M.hd x)
      = TM.edge_b_iff h o x in
    FStar.Classical.forall_intro one

let mscan_heq (h h': M.mheap) (o j n: nat)
  : Lemma (requires R.heq h h') (ensures R.heq (mscan h o j n) (mscan h' o j n))
  = mscan_spec h o j n;
    mscan_spec h' o j n;
    let c (x: nat) : Lemma (tin h o j n x == tin h' o j n x)
      = tin_cols h h' o j n x in
    FStar.Classical.forall_intro c

let set_col_heq (h h': M.mheap) (o: nat) (c: M.colour)
  : Lemma (requires R.heq h h') (ensures R.heq (M.set_col h o c) (M.set_col h' o c))
  = ()

let tmslice_heq (h h': M.mheap) (o: nat)
  : Lemma (requires R.heq h h') (ensures R.heq (TM.tmslice_with h o) (TM.tmslice_with h' o))
  = let one (x: nat) : Lemma ((TM.tmslice_with h o).M.hd x == (TM.tmslice_with h' o).M.hd x)
      = TM.edge_b_iff h o x; TM.edge_b_iff h' o x;
        assert (forall (a: nat). M.resolve h a == M.resolve h' a) in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// The slice, read as the model
/// ---------------------------------------------------------------------------

/// What scanning `o` needs of the model: no infix blocks, and each pointer
/// field of `o` resolves.
let scan_ok (m: M.mheap) (o: nat) : prop =
  M.is_block m o /\ no_infix_tags m /\
  (forall (i a: nat). M.ptr_field m o i /\ M.field m o i == M.VPtr (M.Major a) ==> Some? (M.resolve m a))

let scan_ok_cols (h h': M.mheap) (o: nat)
  : Lemma (requires scan_ok h o /\ same_but_cols h h') (ensures scan_ok h' o)
  = assert (forall (a: nat). M.resolve h' a == M.resolve h a)

/// akhil's field read is the model's word.
#push-options "--z3rlimit 40"
let get_field_word (g: heap) (o i: nat)
  : Lemma (requires M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o)
          (ensures pos o + 8 < heap_size /\ i + 1 < pow2 64 /\ pos (o + 1 + i) < heap_size /\
                   HG.get_field g (obj_of o) (U64.uint_to_t (i + 1)) == word g (o + 1 + i))
  = abs_block_walk g o;
    abs_is_block g o;
    abs_header g o;
    wosize_of_object_bound (obj_of o) g;
    msize_pos (o + 1 + i);
    hd_of_obj o;
    let k = U64.uint_to_t (i + 1) in
    let fa = U64.add (hd_address (obj_of o)) (U64.mul mword k) in
    U64.v_inj fa (hp (o + 1 + i))
#pop-options

/// Scanning a field darkens the target the model resolves it to.
#push-options "--z3rlimit 40"
let darken_old_model (g: heap) (o i: nat)
  : Lemma (requires scan_ok (cabs g) o /\ i < M.wz_of (cabs g) o /\ M.scannable (M.tag_of (cabs g) o))
          (ensures pos (o + 1 + i) < heap_size /\ BB.darken_old g o i == MM.darken g (word g (o + 1 + i)))
  = let m = cabs g in
    let k = o + 1 + i in
    abs_block_walk g o;
    msize_pos k;
    msize_pos (o + M.wz_of m o);
    no_infix_of_model g;
    is_fw_iff g k;
    assert (M.covers (abs g) o k);
    let w = word g k in
    assert (M.field m o i == absv w);
    if is_pointer w then begin
      ptr_decode w;
      let b = ptr_b w in
      assert (M.ptr_field m o i);
      let Some y = M.resolve m b in
      resolve_abs_of_cabs g b y;
      ptr_resolve g b y;
      assert (T.old_target m o i == Some y)
    end
    else assert (T.old_target m o i == None)
#pop-options

let scan_step (g: heap) (o i: nat)
  : Lemma (requires scan_ok (cabs g) o /\ i < M.wz_of (cabs g) o /\ M.scannable (M.tag_of (cabs g) o))
          (ensures pos o + 8 < heap_size /\ i + 1 < pow2 64 /\
                   R.heq (cabs (S.scan_field g (obj_of o) (U64.uint_to_t (i + 1)))) (BB.tdark true (cabs g) o i))
  = get_field_word g o i;
    darken_old_model g o i;
    BB.darken_cabs true g o i

#push-options "--fuel 1 --z3rlimit 40"
let rec scan_from_cabs (g: heap) (o: nat) (k: Prims.pos) (wz: nat)
  : Lemma (requires scan_ok (cabs g) o /\ wz == M.wz_of (cabs g) o /\ M.scannable (M.tag_of (cabs g) o) /\
                    pos o + 8 < heap_size /\ wz < pow2 54)
          (ensures R.heq (cabs (scan_from g (obj_of o) k wz)) (mscan (cabs g) o (k - 1) wz))
          (decreases (if k > wz then 0 else wz + 1 - k))
  = if k <= wz then begin
      scan_step g o (k - 1);
      let g1 = S.scan_field g (obj_of o) (U64.uint_to_t k) in
      tdark_cols (cabs g) o (k - 1);
      scan_ok_cols (BB.tdark true (cabs g) o (k - 1)) (cabs g1) o;
      assert (same_but_cols (cabs g) (cabs g1));
      scan_ok_cols (cabs g) (cabs g1) o;
      scan_from_cabs g1 o (k + 1) wz;
      mscan_heq (cabs g1) (BB.tdark true (cabs g) o (k - 1)) o k wz
    end
#pop-options

let noscan_iff (g: heap) (t: nat)
  : Lemma (requires M.is_block (cabs g) t)
          (ensures pos t + 8 < heap_size /\
                   (is_no_scan (obj_of t) g <==> not (M.scannable (M.tag_of (cabs g) t))) /\
                   U64.v (wosize_of_object (obj_of t) g) == M.wz_of (cabs g) t /\
                   M.wz_of (cabs g) t < pow2 54)
  = abs_block_walk g t;
    abs_header g t;
    is_no_scan_spec (obj_of t) g;
    no_scan_tag_val ();
    wosize_of_object_bound (obj_of t) g

/// **A slice at a grey block, read as the model**, is the toy slice there.
#push-options "--z3rlimit 40"
let scan_obj_cabs (g: heap) (t: nat)
  : Lemma (requires scan_ok (cabs g) t /\ M.col_of (cabs g) t == M.Grey)
          (ensures pos t + 8 < heap_size /\ R.heq (cabs (scan_obj g (obj_of t))) (TM.tmslice_with (cabs g) t))
  = noscan_iff g t;
    let x = obj_of t in
    makeBlack_eq x g;
    if is_no_scan x g then begin
      cabs_recolour g t GC.Lib.Header.Black;
      tmslice_noscan (cabs g) t
    end
    else begin
      let wz = M.wz_of (cabs g) t in
      scan_from_cabs g t 1 wz;
      let g1 = scan_from g x 1 wz in
      mscan_spec (cabs g) t 0 wz;
      assert (M.is_block (cabs g1) t);
      makeBlack_eq x g1;
      cabs_recolour g1 t GC.Lib.Header.Black;
      set_col_heq (cabs g1) (mscan (cabs g) t 0 wz) t M.Black;
      tmslice_scan (cabs g) t
    end
#pop-options

/// The lowest grey block, when there is a grey block.
let some_grey (m: M.mheap) (g: heap)
  : Lemma (requires R.heq m (cabs g) /\ ~(T.mark_done m))
          (ensures (match TM.find_grey (cabs g) msize with
                    | Some t -> M.is_block m t /\ M.col_of m t == M.Grey
                    | None -> False))
  = TM.find_grey_spec (cabs g) msize

let scan_ok_of_pre (m: M.mheap) (snap allocd: nat -> prop) (t: nat)
  : Lemma (requires T.mark_slice_pre snap allocd m /\ M.is_block m t /\ M.col_of m t == M.Grey)
          (ensures scan_ok m t)
  = assert (T.union snap allocd t)

let scan_ok_heq (m m': M.mheap) (o: nat)
  : Lemma (requires scan_ok m o /\ R.heq m m') (ensures scan_ok m' o)
  = scan_ok_cols m m' o

/// **A slice meets the contract.**
#push-options "--z3rlimit 40"
let bslice_m (g: heap) (m: M.mheap) (snap allocd: nat -> prop)
  : Lemma (requires R.heq m (cabs g) /\ T.mark_slice_pre snap allocd m)
          (ensures exists (m': M.mheap). brepr m' (bslice g) /\ T.mark_slice_post snap allocd m m')
  = some_grey m g;
    let Some t = TM.find_grey (cabs g) msize in
    scan_ok_of_pre m snap allocd t;
    scan_ok_heq m (cabs g) t;
    scan_obj_cabs g t;
    assert (bslice g == scan_obj g (obj_of t));
    TM.tmslice_with_m m snap allocd t;
    tmslice_heq m (cabs g) t;
    assert (brepr (TM.tmslice_with m t) (bslice g))
#pop-options

let bslice_ok (g: heap) (snap allocd: nat -> prop)
  : Lemma (R.lifted byte_rep (T.mark_slice_pre snap allocd) g (bslice g) (T.mark_slice_post snap allocd))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (fun m -> bslice_m g m snap allocd))

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

/// The canonical view of the collector's world.
let cview (cw: T.cworld heap GC.Gen.MinorHeap.minor_state) : GTot M.world =
  { M.maj = cabs cw.T.cmaj; M.yng = GC.Spec.Top.Young.ycabs cw.T.cyng; M.roots = cw.T.croots; M.rem = cw.T.crem }

/// The word of a major pointer the model resolves.
let maj_word (h: M.mheap) (v: M.value) : GTot (Seq.seq U64.t) =
  match v with
  | M.VPtr (M.Major a) -> if Some? (M.resolve h a) then Seq.cons (concv v) Seq.empty else Seq.empty
  | _ -> Seq.empty

let rec root_ws (h: M.mheap) (rs: list M.value) : GTot (Seq.seq U64.t) (decreases rs) =
  match rs with
  | [] -> Seq.empty
  | v :: tl -> Seq.append (maj_word h v) (root_ws h tl)

/// The fields `< n` of the young block `o`.
let yhead (h y: M.mheap) (o i: nat) : GTot (Seq.seq U64.t) =
  if M.ptr_field y o i then maj_word h (M.field y o i) else Seq.empty

let rec yfield_ws (h y: M.mheap) (o n: nat) : GTot (Seq.seq U64.t) (decreases n) =
  if n = 0 then Seq.empty else Seq.append (yhead h y o (n - 1)) (yfield_ws h y o (n - 1))

/// The young blocks `< n`.
let rec young_ws (h y: M.mheap) (n: nat) : GTot (Seq.seq U64.t) (decreases n) =
  if n = 0 then Seq.empty else Seq.append (yfield_ws h y (n - 1) (M.wz_of y (n - 1))) (young_ws h y (n - 1))

/// The roots the start darkens: the major pointers the model resolves, in
/// the roots and in the fields of young blocks.
let start_ws (w: M.world) : GTot (Seq.seq U64.t) =
  Seq.append (root_ws w.M.maj w.M.roots) (young_ws w.M.maj w.M.yng w.M.yng.M.size)

/// **The start**: akhil's root darkening.
let bstart (cw: T.cworld heap GC.Gen.MinorHeap.minor_state) : GTot heap =
  MStart.darkened cw.T.cmaj (start_ws (cview cw))

/// ---------------------------------------------------------------------------
/// The moves
/// ---------------------------------------------------------------------------

/// akhil's moves on the byte heap: starting a block changes nothing; a grey
/// move darkens the target the model resolves the field to (the barrier's
/// `BB.darken_old`; akhil's `S.scan_field` when the field resolves,
/// `darken_old_model`); a black move blackens the block.
let bmove (g: heap) (sc: T.scan) (mv: T.move) : GTot (heap & T.scan) =
  match mv with
  | T.MBegin _ -> (g, T.move_scan sc mv)
  | T.MGrey -> (match sc with Some (o, i) -> (BB.darken_old g o i, T.move_scan sc mv) | None -> (g, sc))
  | T.MBlack o -> ((if pos o + 8 < heap_size then makeBlack (obj_of o) g else g), T.move_scan sc mv)

let bmark : T.mark heap GC.Gen.MinorHeap.minor_state = {
  T.mstate = T.scan; T.mscan = (fun sc -> sc); T.mnone = None; T.mstart = bstart; T.mmove = bmove }

/// ---------------------------------------------------------------------------
/// The words, read as the model
/// ---------------------------------------------------------------------------

/// Every word is a pointer the model resolves.
let good (g: heap) (ws: Seq.seq U64.t) : prop =
  forall (u: U64.t). Seq.mem u ws ==> is_pointer u /\ Some? (M.resolve (cabs g) (ptr_b u))

/// Some word resolves to `x`.
let hits (g: heap) (ws: Seq.seq U64.t) (x: nat) : prop =
  exists (u: U64.t). Seq.mem u ws /\ M.resolve (cabs g) (ptr_b u) == Some x

let concv_major (g: heap) (a y: nat)
  : Lemma (requires M.resolve (cabs g) a == Some y)
          (ensures is_pointer (concv (M.VPtr (M.Major a))) /\ ptr_b (concv (M.VPtr (M.Major a))) == a)
  = resolve_pos g a y;
    base_facts ();
    let u = concv (M.VPtr (M.Major a)) in
    assert (U64.v u == pos a + 8);
    ptr_decode u

let mem_empty (u: U64.t) : Lemma (~(Seq.mem u (Seq.empty #U64.t)))
  = assert_norm (Seq.count u (Seq.empty #U64.t) == 0)

let maj_word_facts (g: heap) (v: M.value)
  : Lemma (good g (maj_word (cabs g) v) /\
           (forall (x: nat). hits g (maj_word (cabs g) v) x <==>
              (exists (a: nat). v == M.VPtr (M.Major a) /\ M.resolve (cabs g) a == Some x)))
  = FStar.Classical.forall_intro mem_empty;
    match v with
    | M.VPtr (M.Major a) ->
      FStar.Seq.Properties.mem_cons (concv v) (Seq.empty #U64.t);
      (match M.resolve (cabs g) a with
       | Some y -> concv_major g a y
       | None -> ())
    | _ -> ()

let append_facts (g: heap) (s1 s2: Seq.seq U64.t)
  : Lemma (requires good g s1 /\ good g s2)
          (ensures good g (Seq.append s1 s2) /\
                   (forall (x: nat). hits g (Seq.append s1 s2) x <==> hits g s1 x \/ hits g s2 x))
  = FStar.Seq.Properties.lemma_mem_append s1 s2

#push-options "--fuel 1"
let rec root_facts (g: heap) (rs: list M.value)
  : Lemma (ensures good g (root_ws (cabs g) rs) /\
                   (forall (x: nat). hits g (root_ws (cabs g) rs) x <==>
                      (exists (a: nat). L.memP (M.VPtr (M.Major a)) rs /\ M.resolve (cabs g) a == Some x)))
          (decreases rs)
  = FStar.Classical.forall_intro mem_empty;
    match rs with
    | [] -> ()
    | v :: tl ->
      maj_word_facts g v;
      root_facts g tl;
      append_facts g (maj_word (cabs g) v) (root_ws (cabs g) tl)

let yhit (g: heap) (y: M.mheap) (o i: nat) (x: nat) : prop =
  exists (a: nat). M.ptr_field y o i /\ M.field y o i == M.VPtr (M.Major a) /\ M.resolve (cabs g) a == Some x

let yfield_head (g: heap) (y: M.mheap) (o i: nat)
  : Lemma (good g (yhead (cabs g) y o i) /\
           (forall (x: nat). hits g (yhead (cabs g) y o i) x <==> yhit g y o i x))
  = FStar.Classical.forall_intro mem_empty;
    maj_word_facts g (M.field y o i)

let rec yfield_good (g: heap) (y: M.mheap) (o n: nat)
  : Lemma (ensures good g (yfield_ws (cabs g) y o n)) (decreases n)
  = FStar.Classical.forall_intro mem_empty;
    if n > 0 then begin
      yfield_head g y o (n - 1);
      yfield_good g y o (n - 1);
      append_facts g (yhead (cabs g) y o (n - 1)) (yfield_ws (cabs g) y o (n - 1))
    end

let append_hit (g: heap) (s1 s2: Seq.seq U64.t) (x: nat)
  : Lemma (hits g (Seq.append s1 s2) x <==> hits g s1 x \/ hits g s2 x)
  = FStar.Seq.Properties.lemma_mem_append s1 s2

let yhead_hit (g: heap) (y: M.mheap) (o i x: nat)
  : Lemma (hits g (yhead (cabs g) y o i) x <==> yhit g y o i x)
  = yfield_head g y o i

#push-options "--fuel 1"
let yfield_unfold (h y: M.mheap) (o n: nat)
  : Lemma (requires n > 0) (ensures yfield_ws h y o n == Seq.append (yhead h y o (n - 1)) (yfield_ws h y o (n - 1)))
  = ()
#pop-options

let rec yfield_intro (g: heap) (y: M.mheap) (o n j x: nat)
  : Lemma (requires j < n /\ yhit g y o j x) (ensures hits g (yfield_ws (cabs g) y o n) x) (decreases n)
  = if j = n - 1 then begin
      yfield_unfold (cabs g) y o n;
      append_hit g (yhead (cabs g) y o (n - 1)) (yfield_ws (cabs g) y o (n - 1)) x;
      yhead_hit g y o j x
    end
    else begin
      yfield_intro g y o (n - 1) j x;
      yfield_unfold (cabs g) y o n;
      append_hit g (yhead (cabs g) y o (n - 1)) (yfield_ws (cabs g) y o (n - 1)) x
    end

let rec yfield_elim (g: heap) (y: M.mheap) (o n x: nat)
  : Lemma (requires hits g (yfield_ws (cabs g) y o n) x) (ensures exists (j: nat). j < n /\ yhit g y o j x)
          (decreases n)
  = if n = 0 then begin
      assert_norm (yfield_ws (cabs g) y o 0 == Seq.empty);
      FStar.Classical.forall_intro mem_empty
    end
    else begin
      yfield_unfold (cabs g) y o n;
      append_hit g (yhead (cabs g) y o (n - 1)) (yfield_ws (cabs g) y o (n - 1)) x;
      yhead_hit g y o (n - 1) x;
      if hits g (yhead (cabs g) y o (n - 1)) x then () else yfield_elim g y o (n - 1) x
    end

let yfield_facts (g: heap) (y: M.mheap) (o n: nat)
  : Lemma (ensures good g (yfield_ws (cabs g) y o n) /\
                   (forall (x: nat). hits g (yfield_ws (cabs g) y o n) x <==>
                      (exists (i a: nat). i < n /\ M.ptr_field y o i /\ M.field y o i == M.VPtr (M.Major a) /\
                                          M.resolve (cabs g) a == Some x)))
  = yfield_good g y o n;
    let one (x: nat)
      : Lemma (hits g (yfield_ws (cabs g) y o n) x <==>
               (exists (i a: nat). i < n /\ M.ptr_field y o i /\ M.field y o i == M.VPtr (M.Major a) /\
                                   M.resolve (cabs g) a == Some x))
      = FStar.Classical.move_requires (yfield_elim g y o n) x;
        let b (j a: nat)
          : Lemma (j < n /\ M.ptr_field y o j /\ M.field y o j == M.VPtr (M.Major a) /\ M.resolve (cabs g) a == Some x ==>
                   hits g (yfield_ws (cabs g) y o n) x)
          = FStar.Classical.move_requires (yfield_intro g y o n j) x in
        FStar.Classical.forall_intro_2 b in
    FStar.Classical.forall_intro one

let yblock (h y: M.mheap) (o: nat) : GTot (Seq.seq U64.t) = yfield_ws h y o (M.wz_of y o)

#push-options "--fuel 1"
let young_unfold (h y: M.mheap) (n: nat)
  : Lemma (requires n > 0) (ensures young_ws h y n == Seq.append (yblock h y (n - 1)) (young_ws h y (n - 1)))
  = ()
#pop-options

let rec young_good (g: heap) (y: M.mheap) (n: nat)
  : Lemma (ensures good g (young_ws (cabs g) y n)) (decreases n)
  = FStar.Classical.forall_intro mem_empty;
    if n > 0 then begin
      young_unfold (cabs g) y n;
      yfield_good g y (n - 1) (M.wz_of y (n - 1));
      young_good g y (n - 1);
      append_facts g (yblock (cabs g) y (n - 1)) (young_ws (cabs g) y (n - 1))
    end

let rec young_intro (g: heap) (y: M.mheap) (n o i x: nat)
  : Lemma (requires o < n /\ yhit g y o i x) (ensures hits g (young_ws (cabs g) y n) x) (decreases n)
  = if o < n - 1 then begin
      young_intro g y (n - 1) o i x;
      young_unfold (cabs g) y n;
      append_hit g (yblock (cabs g) y (n - 1)) (young_ws (cabs g) y (n - 1)) x
    end else begin
      assert (o == n - 1);
      yfield_intro g y o (M.wz_of y o) i x;
      young_unfold (cabs g) y n;
      append_hit g (yblock (cabs g) y (n - 1)) (young_ws (cabs g) y (n - 1)) x
    end

let rec young_elim (g: heap) (y: M.mheap) (n x: nat)
  : Lemma (requires hits g (young_ws (cabs g) y n) x)
          (ensures exists (o i: nat). o < n /\ yhit g y o i x) (decreases n)
  = if n = 0 then begin
      assert_norm (young_ws (cabs g) y 0 == Seq.empty);
      FStar.Classical.forall_intro mem_empty
    end
    else begin
      young_unfold (cabs g) y n;
      append_hit g (yblock (cabs g) y (n - 1)) (young_ws (cabs g) y (n - 1)) x;
      if hits g (yblock (cabs g) y (n - 1)) x then yfield_elim g y (n - 1) (M.wz_of y (n - 1)) x
      else young_elim g y (n - 1) x
    end

let young_facts (g: heap) (y: M.mheap) (n: nat)
  : Lemma (ensures good g (young_ws (cabs g) y n) /\
                   (forall (x: nat). hits g (young_ws (cabs g) y n) x <==>
                      (exists (o i a: nat). o < n /\ M.ptr_field y o i /\ M.field y o i == M.VPtr (M.Major a) /\
                                            M.resolve (cabs g) a == Some x)))
  = young_good g y n;
    let one (x: nat)
      : Lemma (hits g (young_ws (cabs g) y n) x <==>
               (exists (o i a: nat). o < n /\ M.ptr_field y o i /\ M.field y o i == M.VPtr (M.Major a) /\
                                     M.resolve (cabs g) a == Some x))
      = FStar.Classical.move_requires (young_elim g y n) x;
        let b (o i a: nat)
          : Lemma (o < n /\ M.ptr_field y o i /\ M.field y o i == M.VPtr (M.Major a) /\ M.resolve (cabs g) a == Some x ==>
                   hits g (young_ws (cabs g) y n) x)
          = FStar.Classical.move_requires (young_intro g y n o i) x in
        FStar.Classical.forall_intro_3 b in
    FStar.Classical.forall_intro one
#pop-options

/// **The words name exactly the outside references.**
let start_facts (g: heap) (w: M.world)
  : Lemma (requires w.M.maj == cabs g)
          (ensures good g (start_ws w) /\ (forall (x: nat). hits g (start_ws w) x <==> M.outside_ref w x))
  = root_facts g w.M.roots;
    young_facts g w.M.yng w.M.yng.M.size;
    append_facts g (root_ws (cabs g) w.M.roots) (young_ws (cabs g) w.M.yng w.M.yng.M.size)

/// ---------------------------------------------------------------------------
/// Root darkening, read as the model
/// ---------------------------------------------------------------------------

/// One of the first `idx` words resolves to `x`.
let rec hit (h: M.mheap) (ws: Seq.seq U64.t) (idx: nat{idx <= Seq.length ws}) (x: nat) : GTot bool (decreases idx) =
  if idx = 0 then false else (M.resolve h (ptr_b (Seq.index ws (idx - 1))) = Some x) || hit h ws (idx - 1) x

#push-options "--fuel 1 --ifuel 1"
let rec mem_of_index (#a: eqtype) (s: Seq.seq a) (i: nat{i < Seq.length s})
  : Lemma (ensures Seq.mem (Seq.index s i) s) (decreases i)
  = if i = 0 then ()
    else begin
      mem_of_index (Seq.tail s) (i - 1);
      FStar.Seq.Properties.lemma_tl (Seq.head s) (Seq.tail s);
      FStar.Seq.Properties.mem_cons (Seq.head s) (Seq.tail s);
      assert (Seq.equal s (Seq.cons (Seq.head s) (Seq.tail s)))
    end

let rec hit_index (h: M.mheap) (ws: Seq.seq U64.t) (idx: nat{idx <= Seq.length ws}) (x: nat)
  : Lemma (ensures hit h ws idx x == true <==>
                   (exists (j: nat). j < idx /\ M.resolve h (ptr_b (Seq.index ws j)) == Some x))
          (decreases idx)
  = if idx > 0 then hit_index h ws (idx - 1) x
#pop-options

let hit_hits (g: heap) (ws: Seq.seq U64.t) (x: nat)
  : Lemma (hit (cabs g) ws (Seq.length ws) x == true <==> hits g ws x)
  = hit_index (cabs g) ws (Seq.length ws) x;
    let to (j: nat) : Lemma (j < Seq.length ws /\ M.resolve (cabs g) (ptr_b (Seq.index ws j)) == Some x ==> hits g ws x)
      = if j < Seq.length ws then mem_of_index ws j in
    FStar.Classical.forall_intro to;
    let from (u: U64.t) : Lemma (Seq.mem u ws /\ M.resolve (cabs g) (ptr_b u) == Some x ==> hit (cabs g) ws (Seq.length ws) x)
      = if Seq.mem u ws then FStar.Seq.Properties.mem_index u ws in
    FStar.Classical.forall_intro from

let good_index (g: heap) (ws: Seq.seq U64.t) (j: nat)
  : Lemma (requires good g ws /\ j < Seq.length ws)
          (ensures is_pointer (Seq.index ws j) /\ Some? (M.resolve (cabs g) (ptr_b (Seq.index ws j))))
  = mem_of_index ws j

/// The colours after darkening the first `idx` words.
let dk_spec (g g': heap) (ws: Seq.seq U64.t) (idx: nat{idx <= Seq.length ws}) : prop =
  same_but_cols (cabs g) (cabs g') /\
  (forall (x: nat). M.col_of (cabs g') x ==
     (if M.col_of (cabs g) x = M.White && M.is_block (cabs g) x && hit (cabs g) ws idx x then M.Grey
      else M.col_of (cabs g) x))

let hd_sub (x: obj_addr) : Lemma (U64.sub x mword == hd_address x /\ U64.v (hd_address x) + 8 == U64.v x)
  = hd_address_spec x;
    U64.v_inj (U64.sub x mword) (hd_address x)

/// One root darkened (akhil's `check_and_darken_bounded_spec`): its target
/// greyed if white.
#push-options "--z3rlimit 40"
let darken_one (g g0: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat) (t: nat)
  : Lemma (requires no_infix_tags (cabs g) /\ same_but_cols (cabs g) (cabs g0) /\ is_pointer v /\
                    M.resolve (cabs g) (ptr_b v) == Some t /\
                    resolve_object v g0 == resolve_object v g)
          (ensures M.is_block (cabs g0) t /\
                   R.heq (cabs (fst (MB.check_and_darken_bounded_spec g0 st v cap)))
                         (if M.col_of (cabs g0) t = M.White then M.set_col (cabs g0) t M.Grey else cabs g0))
  = ptr_decode v;
    let b = ptr_b v in
    resolve_pos g b t;
    resolve_abs_of_cabs g b t;
    no_infix_of_model g;
    ptr_resolve g b t;
    let tg = resolve_object v g0 in
    assert (tg == obj_of t);
    assert (M.is_block (cabs g0) t);
    abs_block_walk g0 t;
    abs_header g0 t;
    is_white_iff (obj_of t) g0;
    hd_sub tg;
    let ha : hp_addr = hd_address tg in
    f_address_spec ha;
    U64.v_inj (f_address ha) tg;
    if is_white (obj_of t) g0 then begin
      makeGray_eq (obj_of t) g0;
      cabs_recolour g0 t GC.Lib.Header.Gray
    end
#pop-options

#push-options "--fuel 1 --z3rlimit 40"
let darken_step_cols (g g0 g1: heap) (ws: Seq.seq U64.t) (idx: nat{0 < idx /\ idx <= Seq.length ws}) (t: nat)
  : Lemma (requires dk_spec g g0 ws (idx - 1) /\ M.resolve (cabs g) (ptr_b (Seq.index ws (idx - 1))) == Some t /\
                    M.is_block (cabs g0) t /\
                    R.heq (cabs g1) (if M.col_of (cabs g0) t = M.White then M.set_col (cabs g0) t M.Grey else cabs g0))
          (ensures dk_spec g g1 ws idx)
  = let h = cabs g in
    let h0 = cabs g0 in
    let h1 = cabs g1 in
    assert (same_but_cols h h1);
    let one (x: nat)
      : Lemma (M.col_of h1 x == (if M.col_of h x = M.White && M.is_block h x && hit h ws idx x then M.Grey
                                 else M.col_of h x))
      = assert (hit h ws idx x == ((M.resolve h (ptr_b (Seq.index ws (idx - 1))) = Some x) || hit h ws (idx - 1) x));
        assert (M.col_of h0 x == (if M.col_of h x = M.White && M.is_block h x && hit h ws (idx - 1) x then M.Grey
                                  else M.col_of h x));
        if x = t then () else () in
    FStar.Classical.forall_intro one
#pop-options

#push-options "--fuel 1 --z3rlimit 40"
let rec darken_prefix (g: heap) (ws: Seq.seq U64.t) (idx: nat{idx <= Seq.length ws}) (cap: nat)
  : Lemma (requires good g ws /\ no_infix_tags (cabs g))
          (ensures dk_spec g (fst (MB.darken_roots_bounded_prefix_spec g Seq.empty ws idx cap)) ws idx)
          (decreases idx)
  = if idx > 0 then begin
      darken_prefix g ws (idx - 1) cap;
      let (g0, st0) = MB.darken_roots_bounded_prefix_spec g Seq.empty ws (idx - 1) cap in
      let v = Seq.index ws (idx - 1) in
      good_index g ws (idx - 1);
      let Some t = M.resolve (cabs g) (ptr_b v) in
      ptr_decode v;
      MB.darken_roots_bounded_prefix_preserves_resolve g Seq.empty ws (idx - 1) cap v;
      darken_one g g0 st0 v cap t;
      darken_step_cols g g0 (fst (MB.check_and_darken_bounded_spec g0 st0 v cap)) ws idx t
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The start meets the contract
/// ---------------------------------------------------------------------------

let outside_heq (w w': M.world) (x: nat)
  : Lemma (requires R.heq w.M.maj w'.M.maj /\ R.heq w.M.yng w'.M.yng /\ w.M.roots == w'.M.roots)
          (ensures M.outside_ref w x <==> M.outside_ref w' x)
  = assert (forall (a: nat). M.resolve w.M.maj a == M.resolve w'.M.maj a);
    assert (forall (y i: nat). M.ptr_field w.M.yng y i == M.ptr_field w'.M.yng y i /\
                               M.field w.M.yng y i == M.field w'.M.yng y i)

/// One header of the toy start.
let start_point (h h1: M.mheap) (x: nat) (b: bool)
  : Lemma (requires Some? (h1.M.hd x) == Some? (h.M.hd x) /\ M.wz_of h1 x == M.wz_of h x /\
                    M.tag_of h1 x == M.tag_of h x /\
                    M.col_of h1 x == (if Some? (h.M.hd x) && b && M.col_of h x = M.White then M.Grey else M.col_of h x))
          (ensures h1.M.hd x ==
                   (match h.M.hd x with
                    | Some hx -> if b && hx.M.col = M.White then Some ({ hx with M.col = M.Grey }) else Some hx
                    | None -> None))
  = match h.M.hd x with
    | None -> ()
    | Some hx ->
      let Some hy = h1.M.hd x in
      assert (hy == ({ M.wz = hx.M.wz; M.tag = hx.M.tag; M.col = hy.M.col }))

let yrepr_heq (m: M.mheap) (ms: GC.Gen.MinorHeap.minor_state)
  : Lemma (requires GC.Spec.Top.Young.yrepr m ms) (ensures R.heq m (GC.Spec.Top.Young.ycabs ms))
  = reveal_opaque (`%GC.Spec.Top.Young.yrepr) (GC.Spec.Top.Young.yrepr m ms)

let cabs_hd_size (g: heap) (x: nat) : Lemma (Some? ((cabs g).M.hd x) ==> x < msize)
  = msize_pos x

/// One header of the start.
let start_hd (g g': heap) (ws: Seq.seq U64.t) (w: M.world) (x: nat)
  : Lemma (requires dk_spec g g' ws (Seq.length ws) /\ R.heq w.M.maj (cabs g) /\
                    (hit (cabs g) ws (Seq.length ws) x == true <==> TM.outside_b w x == true))
          (ensures (TM.tmstart w).M.hd x == (cabs g').M.hd x)
  = cabs_hd_size g x;
    start_point (cabs g) (cabs g') x (TM.outside_b w x)

#push-options "--z3rlimit 40"
let bstart_cabs (cw: T.cworld heap GC.Gen.MinorHeap.minor_state) (w: M.world)
  : Lemma (requires T.cviews byte_rep cw w /\ T.mark_start_pre w)
          (ensures R.heq (TM.tmstart w) (cabs (bstart cw)))
  = let g = cw.T.cmaj in
    let wc = cview cw in
    let ws = start_ws wc in
    yrepr_heq w.M.yng cw.T.cyng;
    start_facts g wc;
    assert (no_infix_tags (cabs g));
    darken_prefix g ws (Seq.length ws) (Seq.length ws + 1);
    let g' = bstart cw in
    assert (dk_spec g g' ws (Seq.length ws));
    let one (x: nat) : Lemma ((TM.tmstart w).M.hd x == (cabs g').M.hd x)
      = hit_hits g ws x;
        outside_heq wc w x;
        TM.outside_b_iff w x;
        start_hd g g' ws w x in
    FStar.Classical.forall_intro one
#pop-options

let bstart_ok (cw: T.cworld heap GC.Gen.MinorHeap.minor_state) : Lemma (T.mark_start_at byte_rep bmark cw)
  = let one (w: M.world) : Lemma (requires T.cviews byte_rep cw w) (ensures T.mark_start_m byte_rep bmark cw w)
      = let pre () : Lemma (requires T.mark_start_pre w)
                           (ensures exists (m': M.mheap). byte_rep.R.repr m' (bmark.T.mstart cw) /\ T.mark_start_post w m')
          = bstart_cabs cw w;
            TM.tmstart_m w;
            assert (byte_rep.R.repr (TM.tmstart w) (bstart cw)) in
        FStar.Classical.move_requires pre () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// The model's grey move is the barrier's darkening.
let tdark_field (h: M.mheap) (o i: nat) : Lemma (BB.tdark true h o i == T.darken_field h o i) = ()

let move_grey (m: M.mheap) (g: heap) (o i: nat)
  : Lemma (requires brepr m g /\ M.is_block m o)
          (ensures brepr (T.darken_field m o i) (BB.darken_old g o i))
  = BB.darken_cabs true g o i;
    BB.tdark_heq true m (cabs g) o i;
    tdark_field m o i;
    tdark_field (cabs g) o i;
    R.heq_sym (cabs (BB.darken_old g o i)) (BB.tdark true (cabs g) o i);
    R.heq_trans (T.darken_field m o i) (T.darken_field (cabs g) o i) (cabs (BB.darken_old g o i))

let move_black (m: M.mheap) (g: heap) (o: nat)
  : Lemma (requires brepr m g /\ M.is_block m o)
          (ensures pos o + 8 < heap_size /\ brepr (M.set_col m o M.Black) (makeBlack (obj_of o) g))
  = noscan_iff g o;
    makeBlack_eq (obj_of o) g;
    cabs_recolour g o GC.Lib.Header.Black;
    set_col_heq m (cabs g) o M.Black;
    R.heq_sym (cabs (makeBlack (obj_of o) g)) (M.set_col (cabs g) o M.Black);
    R.heq_trans (M.set_col m o M.Black) (M.set_col (cabs g) o M.Black) (cabs (makeBlack (obj_of o) g))

let bmove_m (g: heap) (sc: T.scan) (mv: T.move) (m: M.mheap)
  : Lemma (requires brepr m g) (ensures T.mark_move_m byte_rep bmark g sc mv m)
  = match mv with
    | T.MBegin _ -> ()
    | T.MGrey -> (match sc with Some (o, i) -> if M.is_block m o then move_grey m g o i | None -> ())
    | T.MBlack o -> if M.is_block m o then move_black m g o

let bmove_ok (g: heap) (sc: bmark.T.mstate) (mv: T.move) : Lemma (T.mark_move_at byte_rep bmark g sc mv)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (bmove_m g sc mv))

/// Along a list of moves the model allows, the byte heap follows the model.
#push-options "--fuel 1"
let rec bmoves_repr (g: heap) (m: M.mheap) (sc: T.scan) (mvs: list T.move)
  : Lemma (requires brepr m g /\ M.well_formed m /\ T.moves_ok m sc mvs)
          (ensures brepr (fst (MV.mfold m sc mvs)) (fst (T.mmoves bmark g sc mvs)) /\
                   snd (T.mmoves bmark g sc mvs) == snd (MV.mfold m sc mvs))
          (decreases mvs)
  = match mvs with
    | [] -> ()
    | mv :: tl ->
      bmove_m g sc mv m;
      MV.move_wf m sc mv;
      let (g1, sc1) = bmove g sc mv in
      bmoves_repr g1 (T.move_heap m sc mv) sc1 tl
#pop-options

/// ---------------------------------------------------------------------------
/// A whole object as moves
/// ---------------------------------------------------------------------------

let rec greys (n: nat) : list T.move = if n = 0 then [] else T.MGrey :: greys (n - 1)

/// Scanning the block at `t` whole: start it, scan each of its `wz` fields,
/// blacken it; a block with no field to scan is only blackened.
let obj_moves (t wz: nat) (scn: bool) : list T.move =
  if scn && wz > 0 then T.MBegin t :: L.append (greys wz) [T.MBlack t] else [T.MBlack t]

let obj_mv (m: M.mheap) (t: nat) : list T.move = obj_moves t (M.wz_of m t) (M.scannable (M.tag_of m t))

#push-options "--fuel 2"
let rec greys_fold (h: M.mheap) (o j n: nat)
  : Lemma (requires M.is_block h o /\ M.col_of h o == M.Grey /\ M.scannable (M.tag_of h o) /\ j <= n /\
                    n == M.wz_of h o)
          (ensures T.moves_ok h (Some (o, j)) (L.append (greys (n - j)) [T.MBlack o]) /\
                   MV.mfold h (Some (o, j)) (L.append (greys (n - j)) [T.MBlack o]) ==
                     (M.set_col (mscan h o j n) o M.Black, None))
          (decreases (n - j))
  = if j = n then ()
    else begin
      tdark_cols h o j;
      tdark_field h o j;
      greys_fold (BB.tdark true h o j) o (j + 1) n
    end
#pop-options

/// **The object's moves are the toy slice there**, and the model allows them.
#push-options "--fuel 2"
let obj_moves_model (h: M.mheap) (t: nat)
  : Lemma (requires M.is_block h t /\ M.col_of h t == M.Grey)
          (ensures T.moves_ok h None (obj_mv h t) /\
                   R.heq (fst (MV.mfold h None (obj_mv h t))) (TM.tmslice_with h t) /\
                   snd (MV.mfold h None (obj_mv h t)) == None)
  = let wz = M.wz_of h t in
    if M.scannable (M.tag_of h t) then begin
      tmslice_scan h t;
      if wz > 0 then greys_fold h t 0 wz
    end
    else tmslice_noscan h t
#pop-options

/// **A whole-object slice, on the byte heap**: the toy slice, nothing left
/// being scanned.
let obj_moves_bytes (g: heap) (m: M.mheap) (t: nat)
  : Lemma (requires brepr m g /\ M.well_formed m /\ M.is_block m t /\ M.col_of m t == M.Grey)
          (ensures T.moves_ok m None (obj_mv m t) /\
                   brepr (TM.tmslice_with m t) (fst (T.mmoves bmark g None (obj_mv m t))) /\
                   snd (T.mmoves bmark g None (obj_mv m t)) == None)
  = obj_moves_model m t;
    bmoves_repr g m None (obj_mv m t);
    let m1 = fst (MV.mfold m None (obj_mv m t)) in
    R.heq_sym m1 (TM.tmslice_with m t);
    R.heq_trans (TM.tmslice_with m t) m1 (cabs (fst (T.mmoves bmark g None (obj_mv m t))))

/// **The byte mark meets the mark contract.**
let byte_mark_ok () : Lemma (T.mark_ok byte_rep bmark)
  = FStar.Classical.forall_intro bstart_ok;
    FStar.Classical.forall_intro_3 bmove_ok

/// ---------------------------------------------------------------------------
/// A slice is akhil's moves
/// ---------------------------------------------------------------------------

/// The block at `t` is the scan target: on the walk, grey, scannable.
let target_bytes (g: heap) (t: nat)
  : Lemma (requires M.is_block (cabs g) t)
          (ensures pos t + 8 < heap_size /\ Seq.mem (obj_of t) (objects zero_addr g) /\
                   (is_gray (obj_of t) g <==> M.col_of (cabs g) t == M.Grey) /\
                   (is_no_scan (obj_of t) g <==> not (M.scannable (M.tag_of (cabs g) t))) /\
                   U64.v (wosize_of_object (obj_of t) g) == M.wz_of (cabs g) t)
  = noscan_iff g t;
    abs_is_block g t;
    abs_header g t;
    is_gray_iff (obj_of t) g;
    let c = color_of_object (obj_of t) g in
    assert (M.col_of (cabs g) t == abs_col c);
    assert (abs_col c == M.Grey <==> c == GC.Lib.Header.Gray)

/// The grey moves over the fields `k ..` of `t`.
#push-options "--fuel 1 --z3rlimit 40"
let rec scan_moves (g: heap) (t: nat) (k: Prims.pos) (wz: nat)
  : Lemma (requires scan_ok (cabs g) t /\ wz == M.wz_of (cabs g) t /\ M.scannable (M.tag_of (cabs g) t) /\
                    M.col_of (cabs g) t == M.Grey /\ pos t + 8 < heap_size /\ wz < pow2 54 /\ k <= wz + 1)
          (ensures S.mark_steps g ({ MP.cur = obj_of t; MP.fld = k }) (scan_from g (obj_of t) k wz)
                                  ({ MP.cur = obj_of t; MP.fld = wz + 1 }) /\
                   scan_ok (cabs (scan_from g (obj_of t) k wz)) t /\
                   same_but_cols (cabs g) (cabs (scan_from g (obj_of t) k wz)) /\
                   M.col_of (cabs (scan_from g (obj_of t) k wz)) t == M.Grey)
          (decreases (wz + 1 - k))
  = let x = obj_of t in
    let sp : MP.scan_pos = { MP.cur = x; MP.fld = k } in
    if k > wz then S.mark_steps_refl g sp
    else begin
      target_bytes g t;
      scan_step g t (k - 1);
      let g1 = S.scan_field g x (U64.uint_to_t k) in
      let sp1 : MP.scan_pos = { MP.cur = x; MP.fld = k + 1 } in
      assert (S.grey_move g sp g1 sp1);
      S.mark_steps_move g g1 sp sp1;
      tdark_cols (cabs g) t (k - 1);
      scan_ok_cols (cabs g) (cabs g1) t;
      assert (M.col_of (cabs g1) t == M.Grey);
      scan_moves g1 t (k + 1) wz;
      S.mark_steps_trans g g1 (scan_from g x k wz) sp sp1 ({ MP.cur = x; MP.fld = wz + 1 })
    end
#pop-options

/// **A slice is a run of akhil's moves** (`GC.Spec.MarkPhase.Slice`), from
/// no partly scanned object back to none, on any heap whose reading meets
/// the slice's precondition.
#push-options "--z3rlimit 40"
let bslice_moves (g: heap) (snap allocd: nat -> prop)
  : Lemma (requires T.mark_slice_pre snap allocd (cabs g))
          (ensures S.mark_steps g MP.scan_none (bslice g) MP.scan_none)
  = some_grey (cabs g) g;
    let Some t = TM.find_grey (cabs g) msize in
    scan_ok_of_pre (cabs g) snap allocd t;
    target_bytes g t;
    let x = obj_of t in
    makeBlack_eq x g;
    if is_no_scan x g then begin
      assert (MP.all_scanned g MP.scan_none x);
      assert (S.black_move g MP.scan_none (makeBlack x g) MP.scan_none);
      S.mark_steps_move g (makeBlack x g) MP.scan_none MP.scan_none
    end
    else begin
      let wz = M.wz_of (cabs g) t in
      let sp1 : MP.scan_pos = { MP.cur = x; MP.fld = 1 } in
      assert (S.begin_move g MP.scan_none g sp1);
      S.mark_steps_move g g MP.scan_none sp1;
      scan_moves g t 1 wz;
      let g2 = scan_from g x 1 wz in
      let sp2 : MP.scan_pos = { MP.cur = x; MP.fld = wz + 1 } in
      target_bytes g2 t;
      assert (MP.all_scanned g2 sp2 x);
      assert (S.black_move g2 sp2 (makeBlack x g2) MP.scan_none);
      S.mark_steps_snoc g g2 (makeBlack x g2) sp1 sp2 MP.scan_none;
      S.mark_steps_trans g g (makeBlack x g2) MP.scan_none sp1 MP.scan_none
    end
#pop-options
