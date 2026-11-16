module GC.Spec.Walk

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module SweepInv = GC.Spec.SweepInv

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

let bnext_facts (g: heap) (p: hp_addr)
  = aligned_plus_mul8 (U64.v p) (U64.v (getWosize (read_word g p)) + 1)

/// The next position, as an address.
private let next_addr (g: heap) (a: hp_addr{bnext g a < heap_size}) : (r: hp_addr{U64.v r == bnext g a}) =
  bnext_facts g a;
  mk_hp_addr (bnext g a)

/// `reaches`, unfolded once at a target beyond the start.
#push-options "--fuel 1 --ifuel 0"
private let reaches_eq (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires U64.v a < b /\ can_step g a)
          (ensures reaches g a b ==
                   (bnext g a = b ||
                    (bnext g a < b && bnext g a < heap_size &&
                     reaches g (next_addr g a) b)))
  = bnext_facts g a
#pop-options

#push-options "--fuel 1 --ifuel 0"
private let reaches_not_step (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires U64.v a <> b /\ (U64.v a > b \/ not (can_step g a)))
          (ensures reaches g a b == false)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// Walk positions
/// ---------------------------------------------------------------------------

let rec reaches_bounds (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires reaches g a b)
          (ensures U64.v a <= b /\ b <= heap_size /\ b % 8 == 0)
          (decreases (heap_size - U64.v a))
  = if U64.v a = b then ()
    else begin
      if U64.v a > b || not (can_step g a) then reaches_not_step g a b
      else begin
        reaches_eq g a b;
        bnext_facts g a;
        if bnext g a = b then ()
        else reaches_bounds g (next_addr g a) b
      end
    end

#push-options "--fuel 1 --ifuel 0"
let reaches_refl (g: heap) (a: hp_addr) = ()
#pop-options

let reaches_step (g: heap) (a: hp_addr)
  = bnext_facts g a; reaches_eq g a (bnext g a)

let reaches_unfold (g: heap) (a: hp_addr) (b: nat)
  = if not (can_step g a) then reaches_not_step g a b
    else reaches_eq g a b

/// Prepend a step.
private let reaches_cons (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires can_step g a /\ bnext g a < heap_size /\ reaches g (next_addr g a) b)
          (ensures reaches g a b)
  = reaches_bounds g (next_addr g a) b;
    bnext_facts g a;
    reaches_eq g a b

let rec reaches_snoc (g: heap) (a p: hp_addr)
  : Lemma (requires reaches g a (U64.v p) /\ can_step g p)
          (ensures reaches g a (bnext g p))
          (decreases (heap_size - U64.v a))
  = if U64.v a = U64.v p then reaches_step g p
    else begin
      reaches_bounds g a (U64.v p);
      reaches_unfold g a (U64.v p);
      bnext_facts g p;
      if bnext g a = U64.v p then begin
        reaches_step g p;
        reaches_cons g a (bnext g p)
      end else begin
        reaches_snoc g (next_addr g a) p;
        reaches_cons g a (bnext g p)
      end
    end

let rec reaches_trans (g: heap) (a b: hp_addr) (c: nat)
  : Lemma (requires reaches g a (U64.v b) /\ reaches g b c)
          (ensures reaches g a c)
          (decreases (heap_size - U64.v a))
  = if U64.v a = U64.v b then ()
    else begin
      reaches_bounds g a (U64.v b);
      reaches_unfold g a (U64.v b);
      if bnext g a = U64.v b then reaches_cons g a c
      else begin
        reaches_trans g (next_addr g a) b c;
        reaches_cons g a c
      end
    end

let rec reaches_det (g: heap) (a b: hp_addr) (c: nat)
  : Lemma (requires reaches g a (U64.v b) /\ reaches g a c /\ U64.v b <= c)
          (ensures reaches g b c)
          (decreases (heap_size - U64.v a))
  = if U64.v a = U64.v b then ()
    else begin
      reaches_bounds g a (U64.v b);
      reaches_unfold g a (U64.v b);
      reaches_unfold g a c;
      if bnext g a = U64.v b then begin
        if bnext g a = c then reaches_refl g b
        else ()
      end
      else reaches_det g (next_addr g a) b c
    end

let reaches_block_before (g: heap) (a p: hp_addr) (q: nat)
  = reaches_det g a p q;
    reaches_unfold g p q

let rec last_block (g: heap) (a: hp_addr) (b: nat{reaches g a b /\ U64.v a < b})
  : GTot (p: hp_addr{reaches g a (U64.v p) /\ can_step g p /\ bnext g p == b})
        (decreases (heap_size - U64.v a))
  = reaches_unfold g a b;
    reaches_refl g a;
    if bnext g a = b then a
    else begin
      let n = next_addr g a in
      let p = last_block g n b in
      reaches_step g a;
      reaches_trans g a n (U64.v p);
      p
    end

let rec block_at (g: heap) (a: hp_addr) (c: nat) (q: nat{reaches g a c /\ U64.v a <= q /\ q < c})
  : GTot (p: hp_addr{reaches g a (U64.v p) /\ U64.v p <= q /\ q < bnext g p /\
                     can_step g p /\ bnext g p <= c})
        (decreases (heap_size - U64.v a))
  = reaches_unfold g a c;
    reaches_refl g a;
    if q < bnext g a then a
    else begin
      let n = next_addr g a in
      let p = block_at g n c q in
      reaches_step g a;
      reaches_trans g a n (U64.v p);
      p
    end

let reaches_stuck (g: heap) (a: hp_addr) (e: nat) (q: nat)
  = reaches_bounds g a e;
    reaches_bounds g a q;
    if q > e then begin
      let ea = mk_hp_addr e in
      reaches_det g a ea q;
      reaches_unfold g ea q
    end

/// ---------------------------------------------------------------------------
/// The walk and `objects`
/// ---------------------------------------------------------------------------

private let hd_pos (x: obj_addr)
  : Lemma (U64.v (hd_address x) == U64.v x - 8 /\ hd_address x == mk_hp_addr (U64.v x - 8))
  = hd_address_spec x;
    U64.v_inj (hd_address x) (mk_hp_addr (U64.v x - 8))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec objects_mem_iff (g: heap) (a: hp_addr) (x: obj_addr)
  : Lemma (ensures Seq.mem x (objects a g) <==>
                   (U64.v x >= U64.v a + 8 /\ reaches g a (U64.v x - 8) /\
                    can_step g (hd_address x)))
          (decreases (heap_size - U64.v a))
  = hd_pos x;
    let hx = hd_address x in
    if not (can_step g a) then begin
      if U64.v x - 8 = U64.v a then ()
      else if U64.v x - 8 > U64.v a then reaches_not_step g a (U64.v x - 8)
      else ()
    end
    else begin
      f_address_spec a;
      let n = bnext g a in
      bnext_facts g a;
      if n >= heap_size then begin
        objects_cons_end a g;
        mem_cons_lemma x (f_address a) Seq.empty;
        if U64.v x = U64.v a + 8 then U64.v_inj x (f_address a);
        if U64.v x - 8 > U64.v a then reaches_eq g a (U64.v x - 8)
      end
      else begin
        let na = next_addr g a in
        objects_cons_step_to a g na;
        mem_cons_lemma x (f_address a) (objects na g);
        if U64.v x = U64.v a + 8 then U64.v_inj x (f_address a);
        objects_mem_iff g na x;
        if U64.v x - 8 > U64.v a then begin
          reaches_eq g a (U64.v x - 8);
          if U64.v x - 8 = n then reaches_refl g na
          else if U64.v x - 8 > n then ()
          else if reaches g na (U64.v x - 8) then reaches_bounds g na (U64.v x - 8)
        end
      end
    end
#pop-options

let hd_address_pos (x: obj_addr) = hd_pos x

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

private let aligned_apart (p x: hp_addr)
  : Lemma (requires p <> x)
          (ensures U64.v p + U64.v mword <= U64.v x \/ U64.v x + U64.v mword <= U64.v p)
  = ()

/// Two heaps whose headers at `a` have the same size step the same way at `a`.
#push-options "--fuel 1 --ifuel 0"
private let reaches_same_step (g g': heap) (a: hp_addr) (b: nat)
  : Lemma (requires getWosize (read_word g' a) == getWosize (read_word g a) /\
                    (can_step g a /\ U64.v a < b /\ bnext g a < b /\ bnext g a < heap_size ==>
                     reaches g' (next_addr g a) b == reaches g (next_addr g a) b))
          (ensures reaches g' a b == reaches g a b)
  = if U64.v a = b then ()
    else if U64.v a > b || not (can_step g a) then begin
      reaches_not_step g a b; reaches_not_step g' a b
    end else begin
      reaches_eq g a b; reaches_eq g' a b
    end
#pop-options

let rec reaches_frame_below (g g': heap) (a: hp_addr) (b: nat)
  : Lemma (requires forall (w: hp_addr). U64.v w < b ==> read_word g' w == read_word g w)
          (ensures reaches g' a b == reaches g a b)
          (decreases (heap_size - U64.v a))
  = if U64.v a < b then begin
      assert (read_word g' a == read_word g a);
      if can_step g a && bnext g a < b && bnext g a < heap_size then
        reaches_frame_below g g' (next_addr g a) b
    end;
    if U64.v a < b then reaches_same_step g g' a b
    else if U64.v a = b then begin reaches_refl g a; reaches_refl g' a end
    else begin reaches_not_step g a b; reaches_not_step g' a b end

private let rec reaches_frame_from (g g': heap) (a: hp_addr) (b: nat)
  : Lemma (requires forall (w: hp_addr). U64.v w >= U64.v a ==> read_word g' w == read_word g w)
          (ensures reaches g' a b == reaches g a b)
          (decreases (heap_size - U64.v a))
  = assert (read_word g' a == read_word g a);
    if can_step g a && U64.v a < b && bnext g a < b && bnext g a < heap_size then begin
      bnext_facts g a;
      reaches_frame_from g g' (next_addr g a) b
    end;
    reaches_same_step g g' a b

/// `objects` at `a`, one step, in terms of the walk's size at `a`.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
private let objects_same_step (g g': heap) (a: hp_addr)
  : Lemma (requires getWosize (read_word g' a) == getWosize (read_word g a) /\
                    (can_step g a /\ bnext g a < heap_size ==>
                     objects (next_addr g a) g' == objects (next_addr g a) g))
          (ensures objects a g' == objects a g)
  = ()
#pop-options

private let rec objects_frame_from (g g': heap) (a: hp_addr)
  : Lemma (requires forall (w: hp_addr). U64.v w >= U64.v a ==> read_word g' w == read_word g w)
          (ensures objects a g' == objects a g)
          (decreases (heap_size - U64.v a))
  = assert (read_word g' a == read_word g a);
    if can_step g a && bnext g a < heap_size then begin
      bnext_facts g a;
      objects_frame_from g g' (next_addr g a)
    end;
    objects_same_step g g' a

let walk_frame_from (g g': heap) (a: hp_addr)
  = objects_frame_from g g' a;
    let aux (b: nat) : Lemma (reaches g' a b == reaches g a b) = reaches_frame_from g g' a b in
    FStar.Classical.forall_intro aux

private let rec walk_write_from (g: heap) (a: hp_addr) (x: hp_addr) (v: U64.t) (p: hp_addr)
  : Lemma (requires (reaches g a (U64.v x) ==> getWosize v == getWosize (read_word g x)) /\
                    reaches g a (U64.v p))
          (ensures (let g' = write_word g x v in
                    objects p g' == objects p g /\
                    (forall (b: nat). reaches g' p b == reaches g p b)))
          (decreases (heap_size - U64.v p))
  = let g' = write_word g x v in
    (if p = x then read_write_same g x v
     else begin aligned_apart p x; read_write_different g x p v end);
    assert (getWosize (read_word g' p) == getWosize (read_word g p));
    if can_step g p && bnext g p < heap_size then begin
      bnext_facts g p;
      reaches_snoc g a p;
      walk_write_from g a x v (next_addr g p)
    end;
    objects_same_step g g' p;
    let aux (b: nat) : Lemma (reaches g' p b == reaches g p b) = reaches_same_step g g' p b in
    FStar.Classical.forall_intro aux

let walk_write (g: heap) (a: hp_addr) (x: hp_addr) (v: U64.t)
  = reaches_refl g a;
    walk_write_from g a x v a

private let rec walk_congr_from (g g': heap) (a: hp_addr) (p: hp_addr)
  : Lemma (requires (forall (q: hp_addr). reaches g a (U64.v q) ==>
                       getWosize (read_word g' q) == getWosize (read_word g q)) /\
                    reaches g a (U64.v p))
          (ensures objects p g' == objects p g /\
                   (forall (b: nat). reaches g' p b == reaches g p b))
          (decreases (heap_size - U64.v p))
  = assert (getWosize (read_word g' p) == getWosize (read_word g p));
    if can_step g p && bnext g p < heap_size then begin
      bnext_facts g p;
      reaches_snoc g a p;
      walk_congr_from g g' a (next_addr g p)
    end;
    objects_same_step g g' p;
    let aux (b: nat) : Lemma (reaches g' p b == reaches g p b) = reaches_same_step g g' p b in
    FStar.Classical.forall_intro aux

let walk_congr (g g': heap) (a: hp_addr)
  = reaches_refl g a;
    walk_congr_from g g' a a

#push-options "--z3rlimit 40"
private let rec merge_from (g: heap) (a p: hp_addr) (v: U64.t) (q: hp_addr)
  : Lemma (requires reaches g a (U64.v p) /\ can_step g p /\ bnext g p < heap_size /\
                    can_step g (mk_hp_addr (bnext g p)) /\
                    U64.v (getWosize v) ==
                      U64.v (getWosize (read_word g p)) +
                      U64.v (getWosize (read_word g (mk_hp_addr (bnext g p)))) + 1 /\
                    reaches g a (U64.v q) /\ U64.v q <= U64.v p)
          (ensures (let g' = write_word g p v in
                    let b = bnext g p in
                    can_step g' p /\ bnext g' p == bnext g (mk_hp_addr b) /\
                    (forall (c: nat). reaches g' q c == (reaches g q c && c <> b))))
          (decreases (heap_size - U64.v q))
  = let g' = write_word g p v in
    let b = bnext g p in
    bnext_facts g p;
    let ba = mk_hp_addr b in
    bnext_facts g ba;
    let nb = bnext g ba in
    read_write_same g p v;
    assert (bnext g' p == nb);
    assert (can_step g' p);
    if U64.v q = U64.v p then begin
      write_preserves_after g p v;
      let aux (c: nat) : Lemma (reaches g' p c == (reaches g p c && c <> b)) =
        if U64.v p = c then begin reaches_refl g p; reaches_refl g' p end
        else if U64.v p > c then begin reaches_not_step g p c; reaches_not_step g' p c end
        else begin
          reaches_eq g p c; reaches_eq g' p c;
          if c > b then begin
            assert (next_addr g p == ba);
            reaches_eq g ba c;
            if nb < c && nb < heap_size then begin
              let na = next_addr g ba in
              assert (next_addr g' p == na);
              reaches_frame_from g g' na c
            end
          end
        end
      in
      FStar.Classical.forall_intro aux
    end else begin
      reaches_bounds g a (U64.v q);
      reaches_block_before g a q (U64.v p);
      reaches_det g a q (U64.v p);
      aligned_apart q p;
      read_write_different g p q v;
      let n = bnext g q in
      bnext_facts g q;
      let na = next_addr g q in
      reaches_snoc g a q;
      merge_from g a p v na;
      let aux (c: nat) : Lemma (reaches g' q c == (reaches g q c && c <> b)) =
        if U64.v q = c then begin reaches_refl g q; reaches_refl g' q end
        else if U64.v q > c then begin reaches_not_step g q c; reaches_not_step g' q c end
        else begin
          reaches_eq g q c; reaches_eq g' q c;
          assert (next_addr g' q == na)
        end
      in
      FStar.Classical.forall_intro aux
    end
#pop-options

let walk_merge (g: heap) (a p: hp_addr) (v: U64.t)
  = reaches_refl g a;
    reaches_bounds g a (U64.v p);
    merge_from g a p v a

/// ---------------------------------------------------------------------------
/// Lemmas about `walk_end`, phrased against `objects`
/// ---------------------------------------------------------------------------

/// One step of the walk, phrased against `objects` so that callers never have
/// to unfold `walk_end` themselves.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let walk_end_step (g: heap) (start: hp_addr)
  : Lemma
    (requires Seq.length (objects start g) > 0)
    (ensures (
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      U64.v start + 8 < heap_size /\ next <= heap_size /\ next % 8 == 0 /\
      (next >= heap_size ==>
       walk_end g start == heap_size /\
       objects start g == Seq.cons (f_address start) Seq.empty) /\
      (next < heap_size ==>
       Seq.length (objects start g) == 1 + Seq.length (objects (mk_hp_addr next) g) /\
       Seq.head (objects start g) == f_address start /\
       Seq.tail (objects start g) == objects (mk_hp_addr next) g /\
       walk_end g start == walk_end g (mk_hp_addr next))))
  = let wz = getWosize (read_word g start) in
    let next = U64.v start + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
    if next < heap_size then
      Seq.lemma_tl (f_address start) (objects (mk_hp_addr next) g)
#pop-options

/// The head of a non-empty walk is the object at the walk position.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
private let walk_head (g: heap) (start: hp_addr)
  : Lemma
    (requires Seq.length (objects start g) > 0)
    (ensures Seq.mem (f_address start) (objects start g) /\
             Seq.head (objects start g) == f_address start)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// `walk_end` reaches the end of the heap  <==>  the walk is dense
/// ---------------------------------------------------------------------------

/// A walk with no room left for a header stops where it starts.
#push-options "--fuel 1 --ifuel 1"
private let walk_end_at_tail (g: heap) (q: hp_addr)
  : Lemma (requires U64.v q + 8 >= heap_size)
          (ensures walk_end g q == U64.v q)
  = ()
#pop-options

/// A walk whose end lies at the end of the heap is non-empty: had the block at
/// `q` overrun the heap, the walk would have stopped at `q` itself.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let walk_nonempty_of_walk_end (g: heap) (q: hp_addr)
  : Lemma
    (requires U64.v q + 8 < heap_size /\ walk_end g q + 8 >= heap_size)
    (ensures Seq.length (objects q g) > 0)
  = ()
#pop-options

/// Density at a single walk position, given that the walk containing it runs
/// all the way to the end of the heap.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
private let rec dense_at (g: heap) (p: hp_addr) (start: hp_addr)
  : Lemma
    (requires U64.v start + 8 < heap_size /\
              walk_end g p + 8 >= heap_size /\
              Seq.mem (f_address start) (objects p g))
    (ensures (
      let wz = getWosize (read_word g start) in
      let next = U64.v start + ((U64.v wz + 1) * 8) in
      next + 8 < heap_size ==>
      Seq.length (objects (U64.uint_to_t next) g) > 0 /\
      Seq.mem (f_address (U64.uint_to_t next)) (objects p g)))
    (decreases (heap_size - U64.v p))
  = walk_end_step g p;
    walk_head g p;
    f_address_spec p;
    f_address_spec start;
    let wzp = getWosize (read_word g p) in
    let np = U64.v p + (U64.v wzp + 1) * 8 in
    let wz = getWosize (read_word g start) in
    let next = U64.v start + ((U64.v wz + 1) * 8) in
    if next + 8 >= heap_size then ()
    else begin
      if np >= heap_size then begin
        // The walk from `p` holds exactly one object, so `start == p`, and then
        // `next == np >= heap_size` contradicts `next + 8 < heap_size`.
        mem_cons_lemma (f_address start) (f_address p) Seq.empty;
        assert (U64.v start == U64.v p);
        assert False
      end
      else begin
        let npa : hp_addr = mk_hp_addr np in
        if U64.v start = U64.v p then begin
          assert (next == np);
          walk_nonempty_of_walk_end g npa;
          walk_head g npa;
          mem_cons_lemma (f_address npa) (f_address p) (objects npa g)
        end
        else begin
          mem_cons_lemma (f_address start) (f_address p) (objects npa g);
          assert (Seq.mem (f_address start) (objects npa g));
          dense_at g npa start;
          mem_cons_lemma (f_address (U64.uint_to_t next)) (f_address p) (objects npa g)
        end
      end;
      assert (Seq.length (objects (U64.uint_to_t next) g) > 0);
      assert (Seq.mem (f_address (U64.uint_to_t next)) (objects p g))
    end
#pop-options

/// A walk that reaches the end of the heap is dense.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
private let dense_from_walk_end (g: heap)
  : Lemma
    (requires Seq.length (objects zero_addr g) > 0 /\
              walk_end g zero_addr + 8 >= heap_size)
    (ensures heap_objects_dense g)
  = let aux (start: hp_addr)
      : Lemma
        (ensures
          U64.v start + 8 < heap_size ==>
          Seq.mem (f_address start) (objects zero_addr g) ==>
          Seq.length (objects start g) > 0 ==>
          (let wz = getWosize (read_word g start) in
           let next = U64.v start + ((U64.v wz + 1) * 8) in
           next + 8 < heap_size ==>
           Seq.length (objects (U64.uint_to_t next) g) > 0 /\
           Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g)))
      = if U64.v start + 8 < heap_size &&
           Seq.mem (f_address start) (objects zero_addr g)
        then dense_at g zero_addr start
    in
    FStar.Classical.forall_intro aux;
    SweepInv.heap_objects_dense_intro g
#pop-options

/// Conversely, a dense walk reaches the end of the heap.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let rec walk_end_of_dense (g: heap) (p: hp_addr)
  : Lemma
    (requires U64.v p + 8 < heap_size /\
              heap_objects_dense g /\
              Seq.mem (f_address p) (objects zero_addr g) /\
              Seq.length (objects p g) > 0)
    (ensures walk_end g p + 8 >= heap_size)
    (decreases (heap_size - U64.v p))
  = walk_end_step g p;
    let wz = getWosize (read_word g p) in
    let np = U64.v p + (U64.v wz + 1) * 8 in
    if np >= heap_size then ()
    else begin
      let npa : hp_addr = mk_hp_addr np in
      if np + 8 >= heap_size then walk_end_at_tail g npa
      else begin
        SweepInv.objects_dense_step p g;
        SweepInv.objects_dense_obj_in p g;
        f_address_spec npa;
        SweepInv.obj_in_objects_elim (f_address npa) g;
        walk_end_of_dense g npa
      end
    end
#pop-options

/// Top-level form: density is exactly "the walk from `zero_addr` reaches the
/// end of the heap".
#push-options "--z3rlimit 40"
private let walk_end_of_dense_top (g: heap)
  : Lemma
    (requires heap_objects_dense g /\
              Seq.length (objects zero_addr g) > 0)
    (ensures walk_end g zero_addr + 8 >= heap_size)
  = walk_head g zero_addr;
    walk_end_of_dense g zero_addr
#pop-options

/// ---------------------------------------------------------------------------
/// Where the walk stops
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec walk_end_of_reaches (g: heap) (a: hp_addr) (e: nat)
  : Lemma (requires reaches g a e /\ e + 8 >= heap_size)
          (ensures walk_end g a == e)
          (decreases (heap_size - U64.v a))
  = reaches_bounds g a e;
    if U64.v a = e then walk_end_at_tail g a
    else begin
      reaches_unfold g a e;
      bnext_facts g a;
      if bnext g a >= heap_size then ()
      else begin
        let na = next_addr g a in
        if bnext g a = e then walk_end_at_tail g na
        else walk_end_of_reaches g na e
      end
    end

let rec reaches_walk_end (g: heap) (a: hp_addr)
  : Lemma (ensures reaches g a (walk_end g a))
          (decreases (heap_size - U64.v a))
  = reaches_refl g a;
    if U64.v a + 8 >= heap_size then ()
    else if not (can_step g a) then ()
    else begin
      bnext_facts g a;
      if bnext g a >= heap_size then reaches_step g a
      else begin
        let na = next_addr g a in
        reaches_walk_end g na;
        reaches_cons g a (walk_end g a)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Density
/// ---------------------------------------------------------------------------

private let mem_nonempty (x: obj_addr) (s: seq obj_addr)
  : Lemma (requires Seq.mem x s) (ensures Seq.length s > 0)
  = Seq.Properties.mem_index x s

let dense_of_reaches_end (g: heap) (e: nat)
  = walk_end_of_reaches g zero_addr e;
    f_address_spec zero_addr;
    let x = f_address zero_addr in
    hd_f_roundtrip zero_addr;
    reaches_refl g zero_addr;
    objects_mem_iff g zero_addr x;
    mem_nonempty x (objects zero_addr g);
    dense_from_walk_end g

let reaches_end_of_dense (g: heap)
  = walk_end_of_dense_top g;
    reaches_walk_end g zero_addr;
    walk_head g zero_addr;
    let x = f_address zero_addr in
    hd_f_roundtrip zero_addr;
    objects_mem_iff g zero_addr x

let can_step_before_end (g: heap) (a p: hp_addr) (e: nat)
  = reaches_stuck g a e (U64.v p);
    reaches_block_before g a p e
