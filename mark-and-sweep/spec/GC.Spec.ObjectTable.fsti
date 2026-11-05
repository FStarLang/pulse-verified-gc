/// ---------------------------------------------------------------------------
/// GC.Spec.ObjectTable - the object-start table of the major heap
/// ---------------------------------------------------------------------------
///
/// The major heap `[zero_addr, heap_size)` is cut into windows of 64 KB.
/// Window `j` begins at `boundary j = zero_addr + j * 65536`, and the table
/// has one entry per window, `n_windows` in all.  Entry `j` names the header
/// of the block (object or free block) of the heap walk that contains
/// `boundary j` (docs/allocator-table-and-size-lists.md, section 1.2, option
/// A3): the last walk position at or below the boundary.
///
/// The table is a function of the walk alone (`tbl_entry`), so it stays
/// valid across every step that keeps the walk positions -- the mark (colours
/// only), the mutator's and the collector's field writes, promotion's header
/// rewrite -- and has to be rewritten only where the walk changes:
///
///   * the allocator, which adds one walk position (`p`, the object it
///     carves from the top of a block) and writes the entries of the
///     boundaries inside the new object (`emit`, from `first_window p`);
///   * the fused sweep, which rebuilds every entry in one ascending pass
///     (`cursor` over the output walk positions).
///
/// `table_ok g t` is "`t` is that function of `g`'s walk" plus density of
/// `g` (`heap_objects_dense`: the walk tiles the heap).  Density is what
/// lets the allocator decide where the new object's entries stop without
/// reading the heap again.
///
/// Exactness is not what always holds.  The OCaml runtime writes headers
/// inside major blocks behind the collector's back (`intern.c` re-tiles the
/// block it unmarshals into; `caml_obj_truncate` splits one), which adds
/// walk positions the table never hears of.  So the invariant the collector
/// keeps at all times is the weaker `table_sound` (section 1.2, option (b)):
/// every entry is a header of the walk, at or below its boundary, and the
/// entries do not decrease.  It survives any step that keeps every walk
/// position, whatever it adds.  Exactness (`table_ok`) is a separate fact:
/// the fused sweep's rebuild establishes it, and an allocation keeps it; the
/// allocator's writes are there for balance, not for `table_sound`.

module GC.Spec.ObjectTable

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Windows
/// ---------------------------------------------------------------------------

/// log2 of the window size, as the code uses it.
inline_for_extraction noextract
let window_shift : FStar.UInt32.t = 16ul

let window_bytes : pos = 65536

inline_for_extraction noextract
let window_bytes_u64 : (w: U64.t{U64.v w == window_bytes}) = 0x10000UL

/// The bytes of the major heap.
let heap_bytes : pos = heap_size - U64.v zero_addr

/// Number of windows: `ceil (heap_bytes / window_bytes)`.
let n_windows : pos = (heap_bytes + window_bytes - 1) / window_bytes

/// The first address of window `j`.
let boundary (j: nat) : nat = U64.v zero_addr + j * window_bytes

/// Boundaries increase with the window.
val boundary_mono (i j: nat)
  : Lemma (requires i <= j) (ensures boundary i <= boundary j)

/// Every boundary up to the one past the last window fits in a word.
val boundary_bound (k: nat)
  : Lemma (requires k <= n_windows)
          (ensures boundary k < heap_size + window_bytes /\
                   boundary k + window_bytes < pow2 64)

/// A boundary lies in the heap exactly when its window exists.
val boundary_lt (j: nat)
  : Lemma (j < n_windows <==> boundary j < heap_size)

/// The first window whose boundary is at or above `a`.
let first_window (a: nat{a >= U64.v zero_addr}) : nat =
  (a - U64.v zero_addr + window_bytes - 1) / window_bytes

val first_window_spec (a: nat{a >= U64.v zero_addr}) (j: nat)
  : Lemma (j >= first_window a <==> boundary j >= a)

val first_window_le (a: nat{a >= U64.v zero_addr /\ a <= heap_size})
  : Lemma (first_window a <= n_windows)

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

/// The header of an object address.
let hd_of (x: obj_addr) : U64.t = U64.sub x mword

/// The walk from a position, `Seq.empty` past the end of the heap.
let objs_from (g: heap) (s: nat) : GTot (seq obj_addr) =
  if s < heap_size && s % 8 = 0 then objects (mk_hp_addr s) g else Seq.empty

/// One step of the walk.
val walk_shape (start: hp_addr) (g: heap)
  : Lemma (requires Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next = U64.v start + (U64.v wz + 1) * 8 in
                    U64.v start + 8 < heap_size /\ next <= heap_size /\ next % 8 == 0 /\
                    Seq.head (objects start g) == f_address start /\
                    Seq.tail (objects start g) == objs_from g next /\
                    U64.v (f_address start) == U64.v start + 8))

/// The walk at a position whose header fits: the block, then the walk from
/// its end.
val objs_from_cons (g: heap) (s: nat)
  : Lemma (requires s % 8 == 0 /\ s + 8 < heap_size /\
                    s + (U64.v (getWosize (read_word g (mk_hp_addr s))) + 1) * 8 <= heap_size)
          (ensures (let hs = mk_hp_addr s in
                    let next = s + (U64.v (getWosize (read_word g hs)) + 1) * 8 in
                    U64.v (f_address hs) == s + 8 /\
                    U64.v (hd_of (f_address hs)) == s /\
                    objs_from g s == Seq.cons (f_address hs) (objs_from g next)))

val objs_from_zero (g: heap)
  : Lemma (objs_from g (U64.v zero_addr) == objects zero_addr g)

/// ... and where it stops: no room for a block, or a header that overruns.
val objs_from_stop (g: heap) (s: nat)
  : Lemma (requires s % 8 == 0 /\ s <= heap_size /\
                    (s + 8 >= heap_size \/
                     (s < heap_size /\
                      s + (U64.v (getWosize (read_word g (mk_hp_addr s))) + 1) * 8 > heap_size)))
          (ensures objs_from g s == Seq.empty)

/// ---------------------------------------------------------------------------
/// The entry of a window
/// ---------------------------------------------------------------------------

/// Walk `s` (in ascending order) while headers stay at or below `a`; the last
/// header seen, or `d` if there is none.
let rec last_le (s: seq obj_addr) (a: nat) (d: U64.t)
  : Tot U64.t (decreases Seq.length s)
  = if Seq.length s = 0 then d
    else
      let h = hd_of (Seq.head s) in
      if U64.v h <= a then last_le (Seq.tail s) a h else d

/// Entry `j` of the table of a walk.
let tbl_entry (objs: seq obj_addr) (j: nat) : U64.t =
  last_le objs (boundary j) zero_addr

/// `t` is the table of `g`'s walk.
val table_matches (g: heap) (t: seq U64.t) : prop

/// ... and `g`'s walk tiles the heap.
val table_ok (g: heap) (t: seq U64.t) : prop

val table_matches_intro (g: heap) (t: seq U64.t)
  : Lemma (requires Seq.length t == n_windows /\
                    (forall (j: nat). j < n_windows ==>
                       Seq.index t j == tbl_entry (objects zero_addr g) j))
          (ensures table_matches g t)

val table_matches_elim (g: heap) (t: seq U64.t)
  : Lemma (requires table_matches g t)
          (ensures Seq.length t == n_windows /\
                   (forall (j: nat). j < n_windows ==>
                      Seq.index t j == tbl_entry (objects zero_addr g) j))

val table_ok_intro (g: heap) (t: seq U64.t)
  : Lemma (requires table_matches g t /\ heap_objects_dense g)
          (ensures table_ok g t)

val table_ok_elim (g: heap) (t: seq U64.t)
  : Lemma (requires table_ok g t)
          (ensures table_matches g t /\ heap_objects_dense g /\
                   Seq.length t == n_windows)

/// The table depends on the walk alone.
val table_matches_transfer (g1 g2: heap) (t: seq U64.t)
  : Lemma (requires table_matches g1 t /\ objects zero_addr g1 == objects zero_addr g2)
          (ensures table_matches g2 t)

val table_ok_transfer (g1 g2: heap) (t: seq U64.t)
  : Lemma (requires table_ok g1 t /\ objects zero_addr g1 == objects zero_addr g2 /\
                    heap_objects_dense g2)
          (ensures table_ok g2 t)

/// ---------------------------------------------------------------------------
/// What an entry means (section 1.2's A3 invariant)
/// ---------------------------------------------------------------------------

/// The walk position directly above `x`.
let next_pos (g: heap) (x: obj_addr) : GTot nat =
  U64.v x + U64.v (wosize_of_object x g) * 8

/// For every window `j`, with `x` the block entry `j` names:
///
///   (W) `x` is a block of the walk;
///   (C) `x` contains `boundary j`: `hd x <= boundary j < next_pos x`.  The
///       one exception is a heap whose walk stops a word short of
///       `heap_size` (density allows that one-word tail): a boundary in the
///       tail names the last block;
///   (E) exactness: no walk position lies in `(hd x, boundary j]`;
///   (M) entries do not decrease.
val table_ok_meaning (g: heap) (t: seq U64.t) (j: nat)
  : Lemma (requires table_ok g t /\ Seq.length (objects zero_addr g) > 0 /\ j < n_windows)
          (ensures Seq.length t == n_windows /\
                   (exists (x: obj_addr).
                      Seq.mem x (objects zero_addr g) /\
                      Seq.index t j == hd_of x /\
                      U64.v (hd_of x) <= boundary j /\
                      (boundary j < next_pos g x \/
                       (next_pos g x + 8 >= heap_size /\
                        (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                           U64.v y <= U64.v x))) /\
                      (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\
                         U64.v (hd_of y) <= boundary j ==> U64.v y <= U64.v x)) /\
                   (j + 1 < n_windows ==>
                      U64.v (Seq.index t j) <= U64.v (Seq.index t (j + 1))))

/// ---------------------------------------------------------------------------
/// The invariant that always holds (option (b))
/// ---------------------------------------------------------------------------

/// `a` is the header of a block of `g`'s walk.
let walk_hd (g: heap) (a: U64.t) : prop =
  exists (x: obj_addr). Seq.mem x (objects zero_addr g) /\ a == hd_of x

/// Every entry is a header of the walk (or `zero_addr`, the walk's first
/// header, which only an empty walk lacks), at or below its boundary, and
/// the entries do not decrease.
val table_sound (g: heap) (t: seq U64.t) : prop

val table_sound_intro (g: heap) (t: seq U64.t)
  : Lemma (requires Seq.length t == n_windows /\
                    (forall (j: nat). j < n_windows ==>
                       (Seq.index t j == zero_addr \/ walk_hd g (Seq.index t j)) /\
                       U64.v (Seq.index t j) <= boundary j) /\
                    (forall (j: nat). j + 1 < n_windows ==>
                       U64.v (Seq.index t j) <= U64.v (Seq.index t (j + 1))))
          (ensures table_sound g t)

val table_sound_elim (g: heap) (t: seq U64.t)
  : Lemma (requires table_sound g t)
          (ensures Seq.length t == n_windows /\
                   (forall (j: nat). j < n_windows ==>
                      (Seq.index t j == zero_addr \/ walk_hd g (Seq.index t j)) /\
                      U64.v (Seq.index t j) <= boundary j) /\
                   (forall (j: nat). j + 1 < n_windows ==>
                      U64.v (Seq.index t j) <= U64.v (Seq.index t (j + 1))))

/// On a heap with a walk, every entry is a header of it.
val table_sound_meaning (g: heap) (t: seq U64.t) (j: nat)
  : Lemma (requires table_sound g t /\ Seq.length (objects zero_addr g) > 0 /\ j < n_windows)
          (ensures Seq.length t == n_windows /\
                   walk_hd g (Seq.index t j) /\ U64.v (Seq.index t j) <= boundary j /\
                   (j + 1 < n_windows ==>
                      U64.v (Seq.index t j) <= U64.v (Seq.index t (j + 1))))

/// It survives every step that keeps the walk positions, whatever it adds.
val table_sound_grow (g1 g2: heap) (t: seq U64.t)
  : Lemma (requires table_sound g1 t /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g1) ==>
                       Seq.mem x (objects zero_addr g2)))
          (ensures table_sound g2 t)

/// The table of a walk is sound: exactness is the stronger fact.
val table_matches_sound (g: heap) (t: seq U64.t)
  : Lemma (requires table_matches g t) (ensures table_sound g t)

val table_ok_sound (g: heap) (t: seq U64.t)
  : Lemma (requires table_ok g t) (ensures table_sound g t)

/// ---------------------------------------------------------------------------
/// Writing a run of entries
/// ---------------------------------------------------------------------------

/// Write `v` into every entry from `k` up whose boundary is below `h`; return
/// the table and the first window not written.
let rec emit (t: seq U64.t) (k: nat) (v: U64.t) (h: nat)
  : Tot (seq U64.t & nat) (decreases (if k < n_windows then n_windows - k else 0))
  = if k < n_windows && k < Seq.length t && boundary k < h
    then emit (Seq.upd t k v) (k + 1) v h
    else (t, k)

/// `emit` in closed form: the entries from `k` with boundary below `h`.
val emit_spec (t: seq U64.t) (k: nat) (v: U64.t) (h: nat)
  : Lemma (requires Seq.length t == n_windows /\ k <= n_windows)
          (ensures (let (t', k') = emit t k v h in
                    Seq.length t' == n_windows /\
                    k <= k' /\ k' <= n_windows /\
                    (k' == n_windows \/ boundary k' >= h) /\
                    (forall (j: nat). k <= j /\ j < k' ==> boundary j < h) /\
                    (forall (j: nat). j < n_windows ==>
                       Seq.index t' j ==
                         (if k <= j && boundary j < h then v else Seq.index t j))))

/// One step of `emit`, as the code takes it.  Below `h` the boundary is in
/// the heap, so its window exists.
val emit_step (t: seq U64.t) (k: nat) (v: U64.t) (h: nat)
  : Lemma (requires Seq.length t == n_windows /\ h <= heap_size /\ boundary k < h)
          (ensures k < n_windows /\ emit t k v h == emit (Seq.upd t k v) (k + 1) v h)

val emit_stop (t: seq U64.t) (k: nat) (v: U64.t) (h: nat)
  : Lemma (requires boundary k >= h)
          (ensures emit t k v h == (t, k))

/// ---------------------------------------------------------------------------
/// The ascending rebuild
/// ---------------------------------------------------------------------------

/// The rebuild over the walk positions `s` still to come: `prev` is the last
/// header passed, `k` the first window not yet written.  At each header `h`,
/// the windows whose boundary is below `h` get `prev`; at the end, every
/// remaining window gets `prev`.
let rec cursor (s: seq obj_addr) (prev: U64.t) (k: nat) (t: seq U64.t)
  : Tot (seq U64.t) (decreases Seq.length s)
  = if Seq.length s = 0 then fst (emit t k prev heap_size)
    else
      let h = hd_of (Seq.head s) in
      let r = emit t k prev (U64.v h) in
      cursor (Seq.tail s) h (snd r) (fst r)

val cursor_cons (s: seq obj_addr) (prev: U64.t) (k: nat) (t: seq U64.t)
  : Lemma (requires Seq.length s > 0)
          (ensures cursor s prev k t ==
                   (let h = hd_of (Seq.head s) in
                    let r = emit t k prev (U64.v h) in
                    cursor (Seq.tail s) h (snd r) (fst r)))

val cursor_empty (prev: U64.t) (k: nat) (t: seq U64.t)
  : Lemma (cursor Seq.empty prev k t == fst (emit t k prev heap_size))

/// One step of the rebuild along the walk of a heap, at a position whose
/// header fits.
val cursor_walk_step (g: heap) (c: U64.t) (prev: U64.t) (k: nat) (t: seq U64.t)
  : Lemma (requires U64.v c % 8 == 0 /\ U64.v c + 8 < heap_size /\
                    U64.v c + (U64.v (getWosize (read_word g (mk_hp_addr (U64.v c)))) + 1) * 8
                      <= heap_size)
          (ensures (let next = U64.v c + (U64.v (getWosize (read_word g (mk_hp_addr (U64.v c)))) + 1) * 8 in
                    let r = emit t k prev (U64.v c) in
                    cursor (objs_from g (U64.v c)) prev k t ==
                    cursor (objs_from g next) c (snd r) (fst r)))

/// The rebuild of a walk is its table, whatever the table held before.
val cursor_matches (g: heap) (t: seq U64.t)
  : Lemma (requires Seq.length t == n_windows)
          (ensures table_matches g (cursor (objects zero_addr g) zero_addr 0 t))

/// The same, for any sequence of walk positions that is the walk of `g`.
val cursor_matches_seq (g: heap) (s: seq obj_addr) (t: seq U64.t)
  : Lemma (requires Seq.length t == n_windows /\ s == objects zero_addr g)
          (ensures table_matches g (cursor s zero_addr 0 t))

/// ---------------------------------------------------------------------------
/// One new walk position
/// ---------------------------------------------------------------------------

/// Where the entries of a new block at `p` stop: at the block above it, or at
/// the end of the heap when nothing can follow it.
let new_block_limit (p_end: nat) : nat =
  if p_end + 8 >= heap_size then heap_size else p_end

/// The window the entries of a new block ending at `p_end` stop before.
let alloc_stop (p_end: nat{p_end >= U64.v zero_addr}) : nat =
  first_window (new_block_limit p_end)

/// The guard: the entry just above the new block's windows is below its
/// header `hp`.  That cannot happen while the table is exact (the block above
/// the new one is a walk position at or below that boundary), but a sound
/// table may name, there, a block that a runtime re-tiling has since cut up
/// and that lies below `hp`.  Writing `hp` would then break (M), so the
/// allocator writes nothing.
let alloc_stale (t: seq U64.t) (hp: U64.t) (p_end: nat{p_end >= U64.v zero_addr}) : bool =
  let k = alloc_stop p_end in
  k < n_windows && k < Seq.length t && U64.v (Seq.index t k) < U64.v hp

/// The table writes of an allocation that returned `obj` (0 when nothing was
/// allocated) for `wz` words: the entries of the boundaries inside the new
/// object name its header, unless the guard holds.
let alloc_table (t: seq U64.t) (obj: U64.t) (wz: nat) : seq U64.t =
  if U64.v obj >= U64.v zero_addr + 8 && U64.v obj < heap_size && U64.v obj % 8 = 0
  then (if alloc_stale t (U64.sub obj 8UL) (U64.v obj + wz * 8) then t
        else fst (emit t (first_window (U64.v obj - 8)) (U64.sub obj 8UL)
                       (new_block_limit (U64.v obj + wz * 8))))
  else t

/// **Exactness after an allocation.**  The table after the walk of `g` gains
/// the one block `p`, of wosize `wz`, carved from the top of a block of `g`
/// (the walk of `g2` is the walk of `g` with `p` added, `p` may already be a
/// walk position).
val table_add_block (g g2: heap) (t: seq U64.t) (p: obj_addr) (wz: nat)
  : Lemma (requires table_ok g t /\
                    heap_objects_dense g2 /\
                    Seq.mem p (objects zero_addr g2) /\
                    U64.v (wosize_of_object p g2) == wz /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       Seq.mem x (objects zero_addr g2)) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g2) ==>
                       Seq.mem x (objects zero_addr g) \/ x == p))
          (ensures U64.v p >= U64.v zero_addr + 8 /\ table_ok g2 (alloc_table t p wz))

/// **Soundness after an allocation.**  The walk keeps every position and
/// gains `p`; nothing else is needed, the guard keeps (M).
val table_sound_add_block (g g2: heap) (t: seq U64.t) (p: obj_addr) (wz: nat)
  : Lemma (requires table_sound g t /\
                    Seq.mem p (objects zero_addr g2) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       Seq.mem x (objects zero_addr g2)))
          (ensures table_sound g2 (alloc_table t p wz))
