module GC.Spec.FreeList.Ascending

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocChain = GC.Spec.Allocator.Lemmas.Chain

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Opening and closing
/// ---------------------------------------------------------------------------

let fl_ascending_intro g fp = reveal_opaque (`%fl_ascending) (fl_ascending g fp)

let fl_ascending_head g fp = reveal_opaque (`%fl_ascending) (fl_ascending g fp)

let fl_ascending_next g fp c = reveal_opaque (`%fl_ascending) (fl_ascending g fp)

/// Two ordered word-aligned numbers are at least a word apart.
private let aligned_gap (a b: nat)
  : Lemma (requires a % 8 == 0 /\ b % 8 == 0 /\ a < b) (ensures a + 8 <= b)
  = FStar.Math.Lemmas.lemma_div_mod a 8;
    FStar.Math.Lemmas.lemma_div_mod b 8

let fl_cell_facts g x =
  let o : obj_addr = x in
  objects_addresses_gt_start zero_addr g o;
  aligned_gap (U64.v zero_addr) (U64.v x);
  aligned_gap (U64.v x) heap_size;
  hd_address_spec o

let fl_ascending_head_cell g fp = fl_ascending_head g fp

let fl_ascending_next_cell g fp c = fl_ascending_next g fp c

/// ---------------------------------------------------------------------------
/// `first_cell_from` under a change of cells
/// ---------------------------------------------------------------------------

/// The cells of `g'` are those of `g`, less `r`, plus `a` when `has_a`.
let cells_eq (g g': heap) (r a: U64.t) (has_a: bool) : prop =
  forall (x: U64.t). fl_cell g' x <==> ((fl_cell g x /\ x <> r) \/ (has_a /\ x == a))

private let fcf_same (g g': heap) (lo: nat) (n: U64.t)
  : Lemma (requires first_cell_from g lo n /\ (forall (x: U64.t). fl_cell g' x <==> fl_cell g x))
          (ensures first_cell_from g' lo n)
  = ()

/// The first cell from `lo` survives, as long as it is not the one removed and
/// the one added does not come before it.
private let fcf_mod (g g': heap) (lo: nat) (n r a: U64.t) (has_a: bool)
  : Lemma (requires first_cell_from g lo n /\ cells_eq g g' r a has_a /\ n <> r /\
                    (has_a ==> (U64.v a < lo \/ (n <> 0UL /\ U64.v n < U64.v a))))
          (ensures first_cell_from g' lo n)
  = ()

/// No cell between `lo1` and `lo2`: the first cell is the same from either.
private let fcf_shift (g: heap) (lo1 lo2: nat) (n: U64.t)
  : Lemma (requires first_cell_from g lo1 n /\ lo1 <= lo2 /\
                    (forall (x: U64.t). fl_cell g x /\ lo1 <= U64.v x ==> lo2 <= U64.v x))
          (ensures first_cell_from g lo2 n)
  = ()

/// `b` is the first cell from `lo`; once it is removed, the first cell from
/// `lo` is the first one after `b`.
private let fcf_skip (g g': heap) (lo: nat) (b n a: U64.t) (has_a: bool)
  : Lemma (requires first_cell_from g (U64.v b + 1) n /\ cells_eq g g' b a has_a /\
                    lo <= U64.v b /\
                    (forall (x: U64.t). fl_cell g x /\ lo <= U64.v x ==> U64.v b <= U64.v x) /\
                    (has_a ==> U64.v a < lo))
          (ensures first_cell_from g' lo n)
  = ()

/// The added cell `a` is the first one from `lo`.
private let fcf_new (g g': heap) (lo: nat) (r a: U64.t)
  : Lemma (requires cells_eq g g' r a true /\ lo <= U64.v a /\
                    (forall (x: U64.t). fl_cell g x /\ lo <= U64.v x /\ x <> r ==>
                       U64.v a <= U64.v x))
          (ensures first_cell_from g' lo a)
  = ()

/// ---------------------------------------------------------------------------
/// Keeping the list
/// ---------------------------------------------------------------------------

let fl_ascending_transfer g g' fp =
  fl_ascending_head g fp;
  fcf_same g g' 0 fp;
  let aux (c: U64.t)
    : Lemma (requires fl_cell g' c)
            (ensures first_cell_from g' (U64.v c + 1) (FL.fl_next g' c))
    = fl_ascending_next g fp c;
      fcf_same g g' (U64.v c + 1) (FL.fl_next g c)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  fl_ascending_intro g' fp

#push-options "--z3rlimit 40"
let fl_ascending_insert g g' fp fp' t b =
  assert (cells_eq g g' b b true);
  fl_ascending_head g fp;
  (if t = 0UL then fcf_new g g' 0 b b
   else fcf_mod g g' 0 fp b b true);
  let aux (c: U64.t)
    : Lemma (requires fl_cell g' c)
            (ensures first_cell_from g' (U64.v c + 1) (FL.fl_next g' c))
    = if c = b then begin
        let n = if t = 0UL then fp else FL.fl_next g t in
        let lo1 = if t = 0UL then 0 else U64.v t + 1 in
        (if t <> 0UL then fl_ascending_next g fp t);
        assert (first_cell_from g lo1 n);
        fcf_shift g lo1 (U64.v b + 1) n;
        fcf_mod g g' (U64.v b + 1) n b b true
      end
      else if t <> 0UL && c = t then begin
        fl_ascending_next g fp t;
        fcf_new g g' (U64.v t + 1) b b
      end
      else begin
        assert (fl_cell g c);
        fl_ascending_next g fp c;
        let n = FL.fl_next g c in
        if U64.v c < U64.v b then begin
          assert (t <> 0UL /\ U64.v c < U64.v t);
          assert (n <> 0UL /\ U64.v n <= U64.v t);
          fcf_mod g g' (U64.v c + 1) n b b true
        end
        else fcf_mod g g' (U64.v c + 1) n b b true
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  fl_ascending_intro g' fp'
#pop-options

#push-options "--z3rlimit 40"
let fl_ascending_remove g g' fp fp' t b =
  assert (cells_eq g g' b b false);
  fl_ascending_head g fp;
  (if t = 0UL then begin
     fl_ascending_next g fp b;
     fcf_skip g g' 0 b (FL.fl_next g b) b false
   end else begin
     fl_ascending_next g fp t;
     fcf_mod g g' 0 fp b b false
   end);
  let aux (c: U64.t)
    : Lemma (requires fl_cell g' c)
            (ensures first_cell_from g' (U64.v c + 1) (FL.fl_next g' c))
    = assert (fl_cell g c);
      fl_ascending_next g fp c;
      if t <> 0UL && c = t then begin
        fl_ascending_next g fp b;
        fcf_skip g g' (U64.v t + 1) b (FL.fl_next g b) b false
      end
      else begin
        let n = FL.fl_next g c in
        (if t <> 0UL then begin
           fl_ascending_next g fp t;
           if U64.v c < U64.v t then assert (n <> 0UL /\ U64.v n <= U64.v t)
           else assert (U64.v b < U64.v c)
         end
         else assert (U64.v b < U64.v c));
        assert (n <> b);
        fcf_mod g g' (U64.v c + 1) n b b false
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  fl_ascending_intro g' fp'
#pop-options

#push-options "--z3rlimit 40"
let fl_ascending_replace g g' fp fp' t b f =
  assert (cells_eq g g' b f true);
  fl_ascending_head g fp;
  fl_ascending_next g fp b;
  (if t <> 0UL then fl_ascending_next g fp t);
  // Every cell of `g` past `t` is at or above `b`.
  assert (forall (x: U64.t). fl_cell g x /\ (t == 0UL \/ U64.v t + 1 <= U64.v x) ==>
            U64.v b <= U64.v x);
  (if t = 0UL then fcf_new g g' 0 b f
   else fcf_mod g g' 0 fp b f true);
  let aux (c: U64.t)
    : Lemma (requires fl_cell g' c)
            (ensures first_cell_from g' (U64.v c + 1) (FL.fl_next g' c))
    = if c = f then
        fcf_skip g g' (U64.v f + 1) b (FL.fl_next g b) f true
      else if t <> 0UL && c = t then
        fcf_new g g' (U64.v t + 1) b f
      else begin
        assert (fl_cell g c);
        fl_ascending_next g fp c;
        let n = FL.fl_next g c in
        if t <> 0UL && U64.v c < U64.v t then begin
          assert (n <> 0UL /\ U64.v n <= U64.v t);
          fcf_mod g g' (U64.v c + 1) n b f true
        end
        else begin
          assert (U64.v b < U64.v c);
          fcf_mod g g' (U64.v c + 1) n b f true
        end
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  fl_ascending_intro g' fp'
#pop-options

/// ---------------------------------------------------------------------------
/// Exactness
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 0"
private let rec sound_from (g: heap) (fp p obj: U64.t) (n: nat)
  : Lemma (requires fl_ascending g fp /\ (p == 0UL \/ fl_cell g p) /\ FL.on_fl g p obj n)
          (ensures fl_cell g obj)
          (decreases n)
  = if n = 0 then ()
    else if not (FL.fl_node p) then ()
    else if p = obj then ()
    else begin
      fl_ascending_next_cell g fp p;
      sound_from g fp (FL.fl_next g p) obj (n - 1)
    end
#pop-options

private let sound (g: heap) (fp: U64.t)
  : Lemma (requires fl_ascending g fp) (ensures FL.fl_sound g fp)
  = fl_ascending_head_cell g fp;
    let aux (obj: U64.t)
      : Lemma (requires FL.reachable_on_fl g fp obj)
              (ensures fl_cell g obj /\ FL.fl_node obj)
      = eliminate exists (n: nat). FL.on_fl g fp obj n
        with (sound_from g fp fp obj n; fl_cell_facts g obj)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
private let rec complete_from (g: heap) (fp: U64.t) (lo: nat) (c y: U64.t)
  : Lemma (requires fl_ascending g fp /\ first_cell_from g lo c /\ fl_cell g y /\ lo <= U64.v y)
          (ensures FL.reachable_on_fl g c y)
          (decreases (if U64.v y >= U64.v c then U64.v y - U64.v c else 0))
  = assert (c <> 0UL);
    fl_cell_facts g c;
    if c = y then FL.reachable_head g c
    else begin
      fl_ascending_next g fp c;
      let n = FL.fl_next g c in
      assert (n <> 0UL /\ U64.v c < U64.v n /\ U64.v n <= U64.v y);
      complete_from g fp (U64.v c + 1) n y;
      FL.reachable_cons g c y
    end
#pop-options

private let complete (g: heap) (fp: U64.t)
  : Lemma (requires fl_ascending g fp) (ensures FL.fl_complete g fp)
  = fl_ascending_head g fp;
    let aux (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr g) /\ is_blue obj g /\
                        U64.v (wosize_of_object obj g) >= 1)
              (ensures FL.reachable_on_fl g fp obj)
      = assert (fl_cell g (obj <: U64.t));
        complete_from g fp 0 fp (obj <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let fl_ascending_exact g fp = sound g fp; complete g fp

/// ---------------------------------------------------------------------------
/// The allocator's entry conditions
/// ---------------------------------------------------------------------------

private let fuel_pos (p: nat)
  : Lemma (requires p < heap_size /\ p % 8 == 0) (ensures (heap_size - p) / 8 >= 1)
  = aligned_gap p heap_size

private let fuel_step (p n: nat)
  : Lemma (requires p < n /\ n < heap_size /\ p % 8 == 0 /\ n % 8 == 0)
          (ensures (heap_size - n) / 8 + 1 <= (heap_size - p) / 8)
  = aligned_gap p n;
    FStar.Math.Lemmas.lemma_div_le (heap_size - n) (heap_size - p - 8) 8;
    FStar.Math.Lemmas.lemma_div_plus (heap_size - p - 8) 1 8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
private let rec walk (g: heap) (fp p: U64.t) (fuel: nat)
  : Lemma (requires fl_ascending g fp /\
                    (p == 0UL \/ (fl_cell g p /\ (heap_size - U64.v p) / 8 <= fuel)))
          (ensures AllocLemmas.fl_valid g p fuel /\ AllocLemmas.fl_chain_terminates g p fuel)
          (decreases fuel)
  = if p = 0UL then begin
      AllocLemmas.fl_chain_terminates_terminal g p fuel;
      if fuel = 0 then AllocLemmas.fl_valid_zero g p
      else AllocLemmas.fl_valid_terminal g p fuel
    end
    else begin
      fl_cell_facts g p;
      fuel_pos (U64.v p);
      let o : obj_addr = p in
      hd_address_spec o;
      fl_ascending_next_cell g fp p;
      let n = read_word g o in
      assert (n == FL.fl_next g p);
      if n = 0UL then walk g fp n (fuel - 1)
      else begin
        fuel_step (U64.v p) (U64.v n);
        walk g fp n (fuel - 1)
      end;
      AllocLemmas.fl_valid_step g p fuel;
      AllocLemmas.fl_chain_terminates_step g p fuel
    end
#pop-options

let fl_ascending_valid g fp =
  fl_ascending_head_cell g fp;
  if fp = 0UL then walk g fp fp heap_words
  else begin
    FStar.Math.Lemmas.lemma_div_le (heap_size - U64.v fp) heap_size 8;
    walk g fp fp heap_words
  end

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
private let rec avoids_from (g: heap) (fp p x: U64.t) (n: nat)
  : Lemma (requires fl_ascending g fp /\ (p == 0UL \/ fl_cell g p) /\ ~(fl_cell g x))
          (ensures AllocLemmas.chain_avoids g p x n = true)
          (decreases n)
  = if p = 0UL then AllocChain.chain_avoids_null g x n
    else if n = 0 then AllocChain.chain_avoids_zero g p x
    else begin
      fl_cell_facts g p;
      let o : obj_addr = p in
      hd_address_spec o;
      assert (p <> x);
      AllocChain.chain_avoids_unfold_step g p x n;
      fl_ascending_next_cell g fp p;
      assert (read_word g o == FL.fl_next g p);
      avoids_from g fp (read_word g o) x (n - 1)
    end
#pop-options

let fl_ascending_avoids g fp x n =
  fl_ascending_head_cell g fp;
  avoids_from g fp fp x n

let fl_ascending_null g =
  let aux (c: U64.t)
    : Lemma (requires fl_cell g c)
            (ensures first_cell_from g (U64.v c + 1) (FL.fl_next g c))
    = ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  fl_ascending_intro g 0UL

let fl_ascending_single (g: heap) (fp: U64.t) =
  fl_ascending_intro g fp
