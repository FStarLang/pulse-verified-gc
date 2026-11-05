module GC.Spec.ObjectTable

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Seq = FStar.Seq
module WE = GC.Spec.WalkEnd

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Windows
/// ---------------------------------------------------------------------------

let boundary_mono i j =
  FStar.Math.Lemmas.lemma_mult_le_right window_bytes i j

let boundary_bound k =
  let w = window_bytes in
  let m = heap_bytes + w - 1 in
  FStar.Math.Lemmas.lemma_mult_le_right w k n_windows;
  FStar.Math.Lemmas.lemma_div_mod m w;
  FStar.Math.Lemmas.modulo_range_lemma m w;
  assert (n_windows * w <= m);
  assert (k * w <= m);
  assert (boundary k <= heap_size + w - 1);
  assert_norm (pow2 57 + 65536 + 65536 < pow2 64)

let boundary_lt j =
  let d = heap_bytes in
  let w = window_bytes in
  FStar.Math.Lemmas.lemma_div_mod (d + w - 1) w;
  if j < n_windows then begin
    // j <= (d + w - 1) / w - 1, so j * w <= d - 1
    FStar.Math.Lemmas.lemma_mult_le_right w j (n_windows - 1);
    FStar.Math.Lemmas.lemma_div_mod (d + w - 1) w
  end
  else begin
    // j >= ceil (d / w), so j * w >= d
    FStar.Math.Lemmas.lemma_mult_le_right w n_windows j
  end

let first_window_spec a j =
  let d = a - U64.v zero_addr in
  let w = window_bytes in
  let f = first_window a in
  FStar.Math.Lemmas.lemma_div_mod (d + w - 1) w;
  if j >= f then FStar.Math.Lemmas.lemma_mult_le_right w f j
  else FStar.Math.Lemmas.lemma_mult_le_right w j (f - 1)

let first_window_le a =
  FStar.Math.Lemmas.lemma_div_le (a - U64.v zero_addr + window_bytes - 1)
                                 (heap_bytes + window_bytes - 1) window_bytes

/// One step of the walk.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let walk_shape start g
  = WE.walk_end_step g start;
    f_address_spec start;
    let wz = getWosize (read_word g start) in
    let next = U64.v start + (U64.v wz + 1) * 8 in
    if next >= heap_size then begin
      Seq.lemma_tl (f_address start) (Seq.empty #obj_addr);
      assert (Seq.equal (Seq.tail (objects start g)) (Seq.empty #obj_addr))
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let objs_from_cons g s =
  let hs = mk_hp_addr s in
  f_address_spec hs;
  let w = U64.v (getWosize (read_word g hs)) in
  let next = s + (w + 1) * 8 in
  aligned_plus_mul8 s (w + 1);
  if next >= heap_size then objects_cons_end hs g
  else objects_cons_step_to hs g (mk_hp_addr next)

let objs_from_zero g =
  U64.v_inj (mk_hp_addr (U64.v zero_addr)) zero_addr

let objs_from_stop g s =
  if s < heap_size then begin
    let hs = mk_hp_addr s in
    assert (Seq.length (objects hs g) == 0);
    Seq.lemma_empty (objects hs g)
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The predicates
/// ---------------------------------------------------------------------------

let entries_of (objs: seq obj_addr) (t: seq U64.t) : prop =
  Seq.length t == n_windows /\
  (forall (j: nat). j < n_windows ==> Seq.index t j == tbl_entry objs j)

let table_matches g t = entries_of (objects zero_addr g) t

let table_ok g t = heap_objects_dense g /\ table_matches g t

let table_matches_intro g t = ()
let table_matches_elim g t = ()
let table_ok_intro g t = ()
let table_ok_elim g t = ()
let table_matches_transfer g1 g2 t = ()
let table_ok_transfer g1 g2 t = ()

/// ---------------------------------------------------------------------------
/// The walk, ordered
/// ---------------------------------------------------------------------------


/// Headers along a walk strictly increase.
let rec sorted (s: seq obj_addr) : Tot prop (decreases Seq.length s) =
  if Seq.length s = 0 then True
  else (forall (y: obj_addr). Seq.mem y (Seq.tail s) ==> U64.v (Seq.head s) < U64.v y) /\
       sorted (Seq.tail s)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec objects_sorted (start: hp_addr) (g: heap)
  : Lemma (ensures sorted (objects start g))
          (decreases (heap_size - U64.v start))
  = if Seq.length (objects start g) = 0 then ()
    else begin
      walk_shape start g;
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next < heap_size then begin
        let nx = mk_hp_addr next in
        objects_sorted nx g;
        let gt (y: obj_addr)
          : Lemma (Seq.mem y (objects nx g) ==> U64.v (f_address start) < U64.v y)
          = objects_addresses_gt_start nx g y
        in
        FStar.Classical.forall_intro gt
      end
      else begin
        let tl = Seq.tail (objects start g) in
        assert (Seq.length tl == 0);
        assert (sorted tl);
        let none (y: obj_addr) : Lemma (~(Seq.mem y tl)) = () in
        FStar.Classical.forall_intro none
      end
    end
#pop-options

/// A member of the walk from `start` is the head of the walk from its header.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec objects_at_member (start: hp_addr) (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects start g))
          (ensures U64.v x >= 8 /\
                   Seq.length (objects (mk_hp_addr (U64.v x - 8)) g) > 0)
          (decreases (heap_size - U64.v start))
  = walk_shape start g;
    let wz = getWosize (read_word g start) in
    let next = U64.v start + (U64.v wz + 1) * 8 in
    let s = objects start g in
    Seq.lemma_cons_inj (Seq.head s) (Seq.head s) (Seq.tail s) (Seq.tail s);
    Seq.cons_head_tail s;
    mem_cons_lemma x (Seq.head s) (Seq.tail s);
    if x = f_address start then ()
    else objects_at_member (mk_hp_addr next) g x
#pop-options

/// Density at one walk position.
let heap_objects_dense_elim_at (g: heap) (start: hp_addr)
  : Lemma (requires heap_objects_dense g /\
                    U64.v start + 8 < heap_size /\
                    Seq.mem (f_address start) (objects zero_addr g) /\
                    Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next = U64.v start + ((U64.v wz + 1) * 8) in
                    next + 8 < heap_size ==>
                    Seq.length (objects (U64.uint_to_t next) g) > 0 /\
                    Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g)))
  = reveal_opaque (`%heap_objects_dense) (heap_objects_dense g)

/// Every block of the walk from `zero_addr` has its header at or above it.
let objects_hd_ge (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g))
          (ensures U64.v (hd_of x) >= U64.v zero_addr /\ U64.v (hd_of x) == U64.v x - 8)
  = objects_addresses_gt_start zero_addr g x;
    FStar.Math.Lemmas.lemma_mod_sub (U64.v x) 8 1

/// Two blocks of the walk: the higher one starts at or above the lower one's
/// end.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let objects_apart (g: heap) (x y: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
                    U64.v x < U64.v y)
          (ensures U64.v (hd_of y) >= next_pos g x)
  = objects_separated zero_addr g x y;
    wosize_of_object_bound x g
#pop-options

/// ---------------------------------------------------------------------------
/// last_le
/// ---------------------------------------------------------------------------

/// The result is the default or a header at or below `a`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec last_le_mem (s: seq obj_addr) (a: nat) (d: U64.t)
  : Lemma (ensures last_le s a d == d \/
                   (exists (x: obj_addr). Seq.mem x s /\ last_le s a d == hd_of x /\
                                        U64.v (hd_of x) <= a))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let h = hd_of (Seq.head s) in
      Seq.cons_head_tail s;
      if U64.v h <= a then begin
        last_le_mem (Seq.tail s) a h;
        let aux (x: obj_addr)
          : Lemma (Seq.mem x (Seq.tail s) ==> Seq.mem x s)
          = mem_cons_lemma x (Seq.head s) (Seq.tail s)
        in
        FStar.Classical.forall_intro aux;
        mem_cons_lemma (Seq.head s) (Seq.head s) (Seq.tail s)
      end
    end
#pop-options

/// On a sorted walk whose headers are all at or above `d`, the result is at
/// or above `d`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec last_le_ge (s: seq obj_addr) (a: nat) (d: U64.t)
  : Lemma (requires sorted s /\
                    (forall (x: obj_addr). Seq.mem x s ==> U64.v d <= U64.v (hd_of x)))
          (ensures U64.v d <= U64.v (last_le s a d))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let h = hd_of (Seq.head s) in
      Seq.cons_head_tail s;
      mem_cons_lemma (Seq.head s) (Seq.head s) (Seq.tail s);
      if U64.v h <= a then begin
        let aux (x: obj_addr)
          : Lemma (Seq.mem x (Seq.tail s) ==> U64.v h <= U64.v (hd_of x))
          = ()
        in
        FStar.Classical.forall_intro aux;
        last_le_ge (Seq.tail s) a h
      end
    end
#pop-options

/// On a sorted walk, the result is at or above every header at or below `a`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec last_le_max (s: seq obj_addr) (a: nat) (d: U64.t) (y: obj_addr)
  : Lemma (requires sorted s /\ Seq.mem y s /\ U64.v (hd_of y) <= a)
          (ensures U64.v (hd_of y) <= U64.v (last_le s a d))
          (decreases Seq.length s)
  = let x0 = Seq.head s in
    let h = hd_of x0 in
    Seq.cons_head_tail s;
    mem_cons_lemma y x0 (Seq.tail s);
    if y = x0 then begin
      let aux (x: obj_addr)
        : Lemma (Seq.mem x (Seq.tail s) ==> U64.v h <= U64.v (hd_of x))
        = ()
      in
      FStar.Classical.forall_intro aux;
      last_le_ge (Seq.tail s) a h
    end
    else last_le_max (Seq.tail s) a h y
#pop-options

/// The entry of a window, characterised by the set of walk positions: the
/// greatest header at or below the boundary.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let entry_char (g: heap) (j: nat)
  : Lemma (let s = objects zero_addr g in
           let e = tbl_entry s j in
           U64.v zero_addr <= U64.v e /\
           (e == zero_addr \/
            (exists (x: obj_addr). Seq.mem x s /\ e == hd_of x /\
                                  U64.v (hd_of x) <= boundary j)) /\
           (forall (y: obj_addr). Seq.mem y s /\ U64.v (hd_of y) <= boundary j ==>
              U64.v (hd_of y) <= U64.v e))
  = let s = objects zero_addr g in
    objects_sorted zero_addr g;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (objects_hd_ge g));
    last_le_ge s (boundary j) zero_addr;
    last_le_mem s (boundary j) zero_addr;
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (last_le_max s (boundary j) zero_addr))
#pop-options

/// ---------------------------------------------------------------------------
/// Meaning
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let table_ok_meaning g t j =
  let s = objects zero_addr g in
  let e = tbl_entry s j in
  entry_char g j;
  // The walk starts at zero_addr: its head is the block there.
  walk_shape zero_addr g;
  let x0 = Seq.head s in
  Seq.cons_head_tail s;
  mem_cons_lemma x0 x0 (Seq.tail s);
  objects_hd_ge g x0;
  // the block entry j names
  let x : obj_addr =
    if e = hd_of x0 then x0
    else FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
           (fun (x: obj_addr) -> Seq.mem x s /\ e == hd_of x /\ U64.v (hd_of x) <= boundary j)
  in
  assert (Seq.mem x s /\ e == hd_of x /\ U64.v (hd_of x) <= boundary j);
  objects_hd_ge g x;
  let maxed (y: obj_addr)
    : Lemma (Seq.mem y s /\ U64.v (hd_of y) <= boundary j ==> U64.v y <= U64.v x)
    = objects_addresses_gt_start zero_addr g y
  in
  FStar.Classical.forall_intro maxed;
  // (C): the block above x, when there is one, is above the boundary
  wosize_of_object_spec x g;
  wosize_of_object_bound x g;
  let hx = mk_hp_addr (U64.v x - 8) in
  objects_at_member zero_addr g x;
  f_address_spec hx;
  hd_address_spec x;
  U64.v_inj (hd_address x) hx;
  U64.v_inj (f_address hx) x;
  let np = next_pos g x in
  if np + 8 < heap_size then begin
    heap_objects_dense_elim_at g hx;
    let q = f_address (mk_hp_addr np) in
    f_address_spec (mk_hp_addr np);
    objects_hd_ge g q;
    if boundary j >= np then begin
      objects_sorted zero_addr g;
      last_le_max s (boundary j) zero_addr q;
      ()
    end
  end
  else begin
    let last (y: obj_addr)
      : Lemma (Seq.mem y s ==> U64.v y <= U64.v x)
      = if Seq.mem y s && U64.v y > U64.v x then objects_apart g x y
    in
    FStar.Classical.forall_intro last
  end;
  assert (exists (x: obj_addr).
            Seq.mem x s /\ Seq.index t j == hd_of x /\ U64.v (hd_of x) <= boundary j /\
            (boundary j < next_pos g x \/
             (next_pos g x + 8 >= heap_size /\
              (forall (y: obj_addr). Seq.mem y s ==> U64.v y <= U64.v x))) /\
            (forall (y: obj_addr). Seq.mem y s /\ U64.v (hd_of y) <= boundary j ==>
               U64.v y <= U64.v x));
  // (M)
  if j + 1 < n_windows then begin
    entry_char g (j + 1);
    objects_sorted zero_addr g;
    boundary_mono j (j + 1);
    last_le_max s (boundary (j + 1)) zero_addr x
  end
#pop-options

/// ---------------------------------------------------------------------------
/// The invariant that always holds
/// ---------------------------------------------------------------------------

let table_sound g t =
  Seq.length t == n_windows /\
  (forall (j: nat). j < n_windows ==>
     (Seq.index t j == zero_addr \/ walk_hd g (Seq.index t j)) /\
     U64.v (Seq.index t j) <= boundary j) /\
  (forall (j: nat). j + 1 < n_windows ==>
     U64.v (Seq.index t j) <= U64.v (Seq.index t (j + 1)))

let table_sound_intro g t = ()
let table_sound_elim g t = ()

let table_sound_meaning g t j =
  let s = objects zero_addr g in
  walk_shape zero_addr g;
  let x0 = Seq.head s in
  Seq.cons_head_tail s;
  mem_cons_lemma x0 x0 (Seq.tail s);
  U64.v_inj (hd_of x0) zero_addr;
  assert (walk_hd g zero_addr)

let table_sound_grow g1 g2 t = ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let table_matches_sound g t =
  table_matches_elim g t;
  let aux (j: nat)
    : Lemma (j < Seq.length t ==>
             (Seq.index t j == zero_addr \/ walk_hd g (Seq.index t j)) /\
             U64.v (Seq.index t j) <= boundary j /\
             (j + 1 < Seq.length t ==>
                U64.v (Seq.index t j) <= U64.v (Seq.index t (j + 1))))
    = if j < n_windows then begin
        entry_char g j;
        if j + 1 < n_windows then begin
          entry_char g (j + 1);
          boundary_mono j (j + 1)
        end
      end
  in
  FStar.Classical.forall_intro aux
#pop-options

let table_ok_sound g t = table_matches_sound g t

/// ---------------------------------------------------------------------------
/// emit
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec emit_spec_aux (t: seq U64.t) (k: nat) (v: U64.t) (h: nat)
  : Lemma (requires Seq.length t == n_windows /\ k <= n_windows)
          (ensures (let (t', k') = emit t k v h in
                    Seq.length t' == n_windows /\
                    k <= k' /\ k' <= n_windows /\
                    (k' == n_windows \/ boundary k' >= h) /\
                    (forall (j: nat). k <= j /\ j < k' ==> boundary j < h) /\
                    (forall (j: nat). j < n_windows ==>
                       Seq.index t' j ==
                         (if k <= j && boundary j < h then v else Seq.index t j))))
          (decreases (n_windows - k))
  = if k < n_windows && k < Seq.length t && boundary k < h then begin
    let t1 = Seq.upd t k v in
    emit_spec_aux t1 (k + 1) v h;
    let (t', k') = emit t1 (k + 1) v h in
    let aux (j: nat)
      : Lemma (j < n_windows ==>
               Seq.index t' j == (if k <= j && boundary j < h then v else Seq.index t j))
      = if j < n_windows then begin
          if j = k then () else ()
        end
    in
    FStar.Classical.forall_intro aux
  end
  else begin
    let aux (j: nat)
      : Lemma (j < n_windows /\ k <= j ==> boundary j >= h)
      = if j < n_windows && k <= j then boundary_mono k j
    in
    FStar.Classical.forall_intro aux
  end
#pop-options

let emit_spec t k v h = emit_spec_aux t k v h

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let emit_step t k v h =
  boundary_lt k
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let emit_stop t k v h = ()
#pop-options

/// ---------------------------------------------------------------------------
/// cursor
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let cursor_cons s prev k t = ()
let cursor_empty prev k t = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let cursor_walk_step g c prev k t =
  objs_from_cons g (U64.v c);
  let hs = mk_hp_addr (U64.v c) in
  let x = f_address hs in
  let w = U64.v (getWosize (read_word g hs)) in
  let tl = objs_from g (U64.v c + (w + 1) * 8) in
  Seq.lemma_tl x tl;
  Seq.head_cons x tl;
  U64.v_inj (hd_of x) c
#pop-options

/// The rebuild over the suffix `s` of `full`, past `prev`, with the windows
/// below `k` already written.
let cursor_inv (full s: seq obj_addr) (prev: U64.t) (k: nat) (t: seq U64.t) : prop =
  Seq.length t == n_windows /\ k <= n_windows /\
  (forall (j: nat). j < n_windows /\ j >= k ==>
     last_le full (boundary j) zero_addr == last_le s (boundary j) prev) /\
  (forall (j: nat). j < k ==> Seq.index t j == last_le full (boundary j) zero_addr)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let rec cursor_correct (full s: seq obj_addr) (prev: U64.t) (k: nat) (t: seq U64.t)
  : Lemma (requires cursor_inv full s prev k t)
          (ensures entries_of full (cursor s prev k t))
          (decreases Seq.length s)
  = if Seq.length s = 0 then begin
      emit_spec t k prev heap_size;
      let aux (j: nat)
        : Lemma (j < n_windows ==> boundary j < heap_size)
        = boundary_lt j
      in
      FStar.Classical.forall_intro aux
    end
    else begin
      let h = hd_of (Seq.head s) in
      let r = emit t k prev (U64.v h) in
      emit_spec t k prev (U64.v h);
      let t' = fst r in
      let k' = snd r in
      let below (j: nat)
        : Lemma (requires j < n_windows /\ j >= k' )
                (ensures boundary j >= U64.v h)
        = if k' < n_windows then boundary_mono k' j
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires below);
      let lo (j: nat)
        : Lemma (requires j < k')
                (ensures j < Seq.length t' ==>
                         Seq.index t' j == last_le full (boundary j) zero_addr)
        = if j < k then ()
          else begin
            assert (boundary j < U64.v h);
            assert (Seq.index t' j == prev);
            assert (last_le full (boundary j) zero_addr == last_le s (boundary j) prev);
            assert (last_le s (boundary j) prev == prev)
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires lo);
      assert (cursor_inv full (Seq.tail s) h k' t');
      cursor_correct full (Seq.tail s) h k' t'
    end
#pop-options

let cursor_matches g t =
  cursor_correct (objects zero_addr g) (objects zero_addr g) zero_addr 0 t

let cursor_matches_seq g s t =
  cursor_correct s s zero_addr 0 t

/// ---------------------------------------------------------------------------
/// One new block
/// ---------------------------------------------------------------------------

/// Two results of `last_le` over sets of walk positions that agree below `a`.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let table_add_block_emit (g g2: heap) (t: seq U64.t) (p: obj_addr) (wz: nat)
  : Lemma (requires table_ok g t /\
                    heap_objects_dense g2 /\
                    Seq.mem p (objects zero_addr g2) /\
                    U64.v (wosize_of_object p g2) == wz /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       Seq.mem x (objects zero_addr g2)) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g2) ==>
                       Seq.mem x (objects zero_addr g) \/ x == p))
          (ensures (let hp = U64.v (hd_of p) in
                    hp >= U64.v zero_addr /\
                    table_ok g2
                      (fst (emit t (first_window hp) (hd_of p)
                                 (new_block_limit (U64.v p + wz * 8))))))
  =
  let s = objects zero_addr g in
  let s2 = objects zero_addr g2 in
  objects_hd_ge g2 p;
  let hp = U64.v (hd_of p) in
  let lim = new_block_limit (U64.v p + wz * 8) in
  table_ok_elim g t;
  emit_spec t (first_window hp) (hd_of p) lim;
  let t' = fst (emit t (first_window hp) (hd_of p) lim) in
  wosize_of_object_bound p g2;
  let p_end = U64.v p + wz * 8 in
  assert (p_end == next_pos g2 p);
  let entry (j: nat)
    : Lemma (requires j < n_windows)
            (ensures j < Seq.length t' ==> Seq.index t' j == tbl_entry s2 j)
    = let a = boundary j in
      first_window_spec hp j;
      entry_char g j;
      entry_char g2 j;
      let e = tbl_entry s j in
      let e2 = tbl_entry s2 j in
      FStar.Classical.forall_intro (FStar.Classical.move_requires (objects_hd_ge g));
      FStar.Classical.forall_intro (FStar.Classical.move_requires (objects_hd_ge g2));
      objects_sorted zero_addr g2;
      if a < hp then begin
        // the same headers lie at or below a
        if e <> zero_addr then begin
          let x = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                    (fun (x: obj_addr) -> Seq.mem x s /\ e == hd_of x /\ U64.v (hd_of x) <= a) in
          last_le_max s2 a zero_addr x
        end;
        if e2 <> zero_addr then begin
          let y = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                    (fun (y: obj_addr) -> Seq.mem y s2 /\ e2 == hd_of y /\ U64.v (hd_of y) <= a) in
          assert (Seq.mem y s);
          ()
        end;
        assert (U64.v e == U64.v e2)
      end
      else if a < lim then begin
        // p is the last header at or below a
        last_le_max s2 a zero_addr p;
        if e2 <> zero_addr then begin
          let y = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                    (fun (y: obj_addr) -> Seq.mem y s2 /\ e2 == hd_of y /\ U64.v (hd_of y) <= a) in
          if U64.v y > U64.v p then objects_apart g2 p y
        end;
        assert (U64.v e2 == hp)
      end
      else begin
        // the block above p settles it, and it was already there
        assert (p_end + 8 < heap_size);
        let hpa = mk_hp_addr hp in
        objects_at_member zero_addr g2 p;
        f_address_spec hpa;
        wosize_of_object_spec p g2;
        hd_address_spec p;
        U64.v_inj (hd_address p) hpa;
        U64.v_inj (f_address hpa) p;
        heap_objects_dense_elim_at g2 hpa;
        let q = f_address (mk_hp_addr p_end) in
        f_address_spec (mk_hp_addr p_end);
        last_le_max s2 a zero_addr q;
        let y = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                  (fun (y: obj_addr) -> Seq.mem y s2 /\ e2 == hd_of y /\ U64.v (hd_of y) <= a) in
        assert (y <> p);
        assert (Seq.mem y s);
        objects_sorted zero_addr g;
        last_le_max s a zero_addr y;
        if e <> zero_addr then begin
          let x = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                    (fun (x: obj_addr) -> Seq.mem x s /\ e == hd_of x /\ U64.v (hd_of x) <= a) in
          last_le_max s2 a zero_addr x
        end;
        assert (U64.v e == U64.v e2)
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires entry);
  table_ok_intro g2 t'
#pop-options

/// The guard never holds after an exact table's writes: the entry above the
/// new block's windows is at or above the block's header, by (M) of the
/// result.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let table_add_block g g2 t p wz =
  table_add_block_emit g g2 t p wz;
  objects_hd_ge g2 p;
  let hp = hd_of p in
  let p_end = U64.v p + wz * 8 in
  let j0 = first_window (U64.v hp) in
  let lim = new_block_limit p_end in
  let t' = fst (emit t j0 hp lim) in
  table_ok_elim g t;
  first_window_le (U64.v hp);
  emit_spec t j0 hp lim;
  table_ok_sound g2 t';
  table_sound_elim g2 t';
  let k = alloc_stop p_end in
  first_window_le lim;
  assert (U64.v (U64.sub p 8UL) == U64.v hp);
  U64.v_inj (U64.sub p 8UL) hp;
  if alloc_stale t hp p_end then begin
    first_window_spec lim j0;
    if boundary j0 < lim then begin
      first_window_spec lim (k - 1);
      first_window_spec lim k;
      first_window_spec (U64.v hp) (k - 1);
      assert (Seq.index t' (k - 1) == hp);
      assert (Seq.index t' k == Seq.index t k);
      assert False
    end
    else begin
      let same (j: nat) : Lemma (j < n_windows ==> Seq.index t' j == Seq.index t j)
        = if j < n_windows && j0 <= j then boundary_mono j0 j
      in
      FStar.Classical.forall_intro same;
      assert (Seq.equal t' t)
    end
  end
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let table_sound_add_block g g2 t p wz =
  table_sound_elim g t;
  table_sound_grow g g2 t;
  table_sound_elim g2 t;
  objects_hd_ge g2 p;
  let hp = hd_of p in
  let p_end = U64.v p + wz * 8 in
  assert (U64.v (U64.sub p 8UL) == U64.v hp);
  U64.v_inj (U64.sub p 8UL) hp;
  if alloc_stale t hp p_end then ()
  else begin
    let j0 = first_window (U64.v hp) in
    let lim = new_block_limit p_end in
    let k = alloc_stop p_end in
    first_window_le (U64.v hp);
    first_window_le lim;
    emit_spec t j0 hp lim;
    let t' = fst (emit t j0 hp lim) in
    assert (walk_hd g2 hp);
    let aux (j: nat)
      : Lemma (j < Seq.length t' ==>
               (Seq.index t' j == zero_addr \/ walk_hd g2 (Seq.index t' j)) /\
               U64.v (Seq.index t' j) <= boundary j /\
               (j + 1 < Seq.length t' ==>
                  U64.v (Seq.index t' j) <= U64.v (Seq.index t' (j + 1))))
      = if j < n_windows then begin
          first_window_spec (U64.v hp) j;
          first_window_spec lim j;
          if j + 1 < n_windows then begin
            first_window_spec (U64.v hp) (j + 1);
            first_window_spec lim (j + 1);
            boundary_mono j (j + 1)
          end
        end
    in
    FStar.Classical.forall_intro aux;
    table_sound_intro g2 t'
  end
#pop-options
