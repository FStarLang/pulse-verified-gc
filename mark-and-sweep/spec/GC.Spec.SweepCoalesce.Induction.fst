/// ---------------------------------------------------------------------------
/// GC.Spec.SweepCoalesce.Induction — fused_aux agrees with coalesce_aux
///
/// The fused pass and `coalesce (sweep ..)` produce the same free pointer and
/// heaps that agree along the object walk (`GC.Spec.HeapAgree.walk_agree`):
/// same headers, same fields of live blocks, same free-list links.  They are
/// not equal: `sweep` writes a blue header and a link into every dead object,
/// the fused pass does not, and neither overwrites those words once the dead
/// objects are merged into a free block.
/// ---------------------------------------------------------------------------

module GC.Spec.SweepCoalesce.Induction

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header

module SpecCoalesce = GC.Spec.Coalesce
module SCH = GC.Spec.SweepCoalesce.Helpers
module HeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator
module HA = GC.Spec.HeapAgree

open GC.Spec.SweepCoalesce.Defs

#set-options "--z3rlimit 12 --fuel 2 --ifuel 1 --warn_error -321"

/// ========================================================================
/// Predicates
/// ========================================================================

let rec objs_well_separated (g: heap) (objs: seq obj_addr)
  : GTot prop (decreases Seq.length objs)
  = if Seq.length objs <= 1 then True
    else
      (forall (x: obj_addr). Seq.mem x (Seq.tail objs) ==>
        U64.v x > U64.v (Seq.head objs) +
                  U64.v (wosize_of_object (Seq.head objs) g) * 8) /\
      objs_well_separated g (Seq.tail objs)

let rec objs_contiguous (g: heap) (objs: seq obj_addr)
  : GTot prop (decreases Seq.length objs)
  = if Seq.length objs <= 1 then True
    else
      U64.v (Seq.head (Seq.tail objs)) ==
        U64.v (Seq.head objs) + (U64.v (wosize_of_object (Seq.head objs) g) + 1) * 8 /\
      objs_contiguous g (Seq.tail objs)

/// One-step unfolding of `objs_contiguous`.  Proved here, in a small context,
/// so callers do not have to pay for the unfolding inside a large proof.
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let contiguous_head (g: heap) (objs: seq obj_addr)
  : Lemma (requires objs_contiguous g objs /\ Seq.length objs > 1)
          (ensures
            U64.v (Seq.head (Seq.tail objs)) ==
              U64.v (Seq.head objs) + (U64.v (wosize_of_object (Seq.head objs) g) + 1) * 8 /\
            objs_contiguous g (Seq.tail objs))
  = ()
#pop-options

/// ========================================================================
/// zero_fields reads 0UL within its range.  No longer used by `flush_blue`,
/// which stopped zeroing free blocks.
/// ========================================================================

#push-options "--z3rlimit 10"
let rec zero_fields_read_within
    (g: heap) (start: U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires
      U64.v start + n * 8 <= heap_size /\
      U64.v start % 8 == 0 /\
      U64.v addr >= U64.v start /\
      U64.v addr < U64.v start + n * 8)
    (ensures read_word (Alloc.zero_fields g start n) addr == 0UL)
    (decreases n)
  = if n = 0 then ()
    else begin
      let start_hp : hp_addr = start in
      let g' = write_word g start_hp 0UL in
      if U64.v addr = U64.v start then begin
        read_write_same g start_hp 0UL;
        let next = U64.uint_to_t (U64.v start + 8) in
        SpecCoalesce.zero_fields_preserves_before g' next (n - 1) addr
      end else begin
        let next = U64.uint_to_t (U64.v start + 8) in
        read_write_different g start_hp addr 0UL;
        zero_fields_read_within g' next (n - 1) addr
      end
    end
#pop-options

/// ========================================================================
/// Helper 5: flush_blue preserves outside for a pair of heaps
/// ========================================================================

#push-options "--z3rlimit 12 --fuel 2 --ifuel 1"
let flush_pair_preserves_outside
    (h1 h2: heap) (fb: U64.t) (rw: nat) (fp: U64.t) (addr: hp_addr)
  : Lemma
    (requires rw > 0 /\
      U64.v fb >= U64.v mword /\
      U64.v fb < heap_size /\
      U64.v fb % U64.v mword == 0 /\
      (U64.v addr + U64.v mword <= U64.v fb - U64.v mword \/
       U64.v addr >= U64.v fb - U64.v mword + rw * U64.v mword))
    (ensures
      read_word (fst (SpecCoalesce.flush_blue h1 fb rw fp)) addr == read_word h1 addr /\
      read_word (fst (SpecCoalesce.flush_blue h2 fb rw fp)) addr == read_word h2 addr)
  = SpecCoalesce.flush_blue_preserves_outside h1 fb rw fp addr;
    SpecCoalesce.flush_blue_preserves_outside h2 fb rw fp addr
#pop-options


/// Pointwise: for a single black rest object, header match + white in h_c'
#push-options "--z3rlimit 12 --fuel 2 --ifuel 1"
private let black_case_rest_headers
  (g: heap) (h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  (x: obj_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      (* 6 *) (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==>
                getWosize (read_word h_f (hd_address x)) == getWosize (read_word h_c (hd_address x)) /\
                getTag (read_word h_f (hd_address x)) == getTag (read_word h_c (hd_address x))) /\
      (* 8 *) (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==> is_white x h_c) /\
      (* 9 *) (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x >= U64.v fb + rw * 8)) /\
      (* 10 *) (rw > 0 ==>
                (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                 U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
                 U64.v fb - 8 + rw * 8 <= heap_size)) /\
      (* 11 *) objs_well_separated g objs /\
      (* 14 *) (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
      Seq.mem x (Seq.tail objs) /\ is_black x g)
    (ensures
      (let obj = Seq.head objs in
       let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
       let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
       let h_f'' = makeWhite obj h_f' in
       getWosize (read_word h_f'' (hd_address x)) == getWosize (read_word h_c' (hd_address x)) /\
       getTag (read_word h_f'' (hd_address x)) == getTag (read_word h_c' (hd_address x)) /\
       is_white x h_c'))
  = let obj = Seq.head objs in
    hd_address_spec obj;
    let hd_obj = hd_address obj in
    let wz_obj = U64.v (wosize_of_object obj g) in
    let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
    makeWhite_spec obj h_f';
    SpecCoalesce.flush_blue_preserves_outside h_f fb rw fp hd_obj;
    SpecCoalesce.flush_blue_preserves_outside h_c fb rw fp hd_obj;
    hd_address_spec x;
    let hd_x = hd_address x in
    assert (Seq.mem x objs);
    assert (U64.v x > U64.v obj + wz_obj * 8);
    assert (U64.v hd_x > U64.v obj + wz_obj * 8 - 8);
    assert (U64.v hd_x >= U64.v obj + wz_obj * 8);
    assert (U64.v hd_x > U64.v hd_obj);
    (if rw > 0 then
      flush_pair_preserves_outside h_f h_c fb rw fp hd_x
    else ());
    read_write_different h_f' hd_obj hd_x
      (colorHeader (read_word h_f' hd_obj) White);
    color_of_header_eq x h_c' h_c
#pop-options

/// Pointwise: for a single body word of a black rest object, h_f'' and h_c' agree
#push-options "--z3rlimit 12 --fuel 2 --ifuel 1"
private let black_case_body_agree_aux
  (g: heap) (h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  (x: obj_addr) (a: hp_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      (* 7 *) (forall (x: obj_addr) (a: hp_addr).
                Seq.mem x objs /\ is_black x g /\
                U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                read_word h_f a == read_word h_c a) /\
      (* 9 *) (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x >= U64.v fb + rw * 8)) /\
      (* 10 *) (rw > 0 ==>
                (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                 U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
                 U64.v fb - 8 + rw * 8 <= heap_size)) /\
      (* 11 *) objs_well_separated g objs /\
      (* 14 *) (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
      Seq.mem x (Seq.tail objs) /\ is_black x g /\
      U64.v a >= U64.v x /\
      U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8)
    (ensures
      (let obj = Seq.head objs in
       read_word (makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp))) a ==
       read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) a))
  = let obj = Seq.head objs in
    hd_address_spec obj;
    let hd_obj = hd_address obj in
    let wz_obj = U64.v (wosize_of_object obj g) in
    let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    makeWhite_spec obj h_f';
    SpecCoalesce.flush_blue_preserves_outside h_f fb rw fp hd_obj;
    SpecCoalesce.flush_blue_preserves_outside h_c fb rw fp hd_obj;
    assert (Seq.mem x objs);
    assert (U64.v x > U64.v obj + wz_obj * 8);
    assert (U64.v a >= U64.v x /\ U64.v x > U64.v obj + wz_obj * 8);
    assert (U64.v a > U64.v hd_obj);
    (if rw > 0 then
      flush_pair_preserves_outside h_f h_c fb rw fp a
    else ());
    read_write_different h_f' hd_obj a
      (colorHeader (read_word h_f' hd_obj) White);
    assert (read_word h_f a == read_word h_c a)
#pop-options

/// For a given black rest object, universalize body agreement over addresses.
/// Uses forall_intro on the top-level black_case_body_agree_aux (trivial VC).
#push-options "--z3rlimit 12 --fuel 2 --ifuel 1"
private let black_case_body_agree
  (g: heap) (h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
  (x: obj_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      is_black (Seq.head objs) g /\
      Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
      (forall (x: obj_addr) (a: hp_addr).
        Seq.mem x objs /\ is_black x g /\
        U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
        read_word h_f a == read_word h_c a) /\
      (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==>
        U64.v x >= U64.v fb + rw * 8)) /\
      (rw > 0 ==>
        (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
         U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
         U64.v fb - 8 + rw * 8 <= heap_size)) /\
      objs_well_separated g objs /\
      (forall (x: obj_addr). Seq.mem x objs ==>
        U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
      Seq.mem x (Seq.tail objs) /\ is_black x g)
    (ensures
      (let obj = Seq.head objs in
       forall (a: hp_addr).
         U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
         read_word (makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp))) a ==
         read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) a))
  = // Thin wrapper calling the top-level pointwise lemma — trivial VC for forall_intro
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (black_case_body_agree_aux g h_f h_c objs fb rw fp x))
#pop-options

/// ========================================================================
/// Non-black case helper: geometric condition for rest objects
/// ========================================================================
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
private let nonblack_case_geo_ok
    (g: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (x: obj_addr)
  : Lemma
    (requires
      Seq.length objs > 0 /\
      (let obj = Seq.head objs in
       let ws = U64.v (wosize_of_object obj g) in
       let new_fb = if rw = 0 then U64.v obj else U64.v fb in
       let new_rw = rw + ws + 1 in
       Seq.mem x (Seq.tail objs) /\
       (forall (y: obj_addr). Seq.mem y (Seq.tail objs) ==>
         U64.v y > U64.v obj + ws * 8) /\
       U64.v obj % 8 == 0 /\
       (rw > 0 ==> U64.v obj >= U64.v fb + rw * 8)))
    (ensures
      (let obj = Seq.head objs in
       let ws = U64.v (wosize_of_object obj g) in
       let new_fb = if rw = 0 then U64.v obj else U64.v fb in
       let new_rw = rw + ws + 1 in
       U64.v x >= new_fb + new_rw * 8))
  = let obj = Seq.head objs in
    let ws = U64.v (wosize_of_object obj g) in
    assert (U64.v x > U64.v obj + ws * 8);
    assert (U64.v x % 8 == 0);
    assert (U64.v obj % 8 == 0);
    ML.cancel_mul_mod ws 8;
    ML.modulo_addition_lemma 0 8 ws;
    assert ((U64.v obj + ws * 8) % 8 == 0);
    assert (U64.v x >= U64.v obj + ws * 8 + 8);
    ML.distributivity_add_left ws 1 8;
    assert (U64.v x >= U64.v obj + (ws + 1) * 8);
    if rw = 0 then ()
    else begin
      assert (U64.v obj >= U64.v fb + rw * 8);
      ML.distributivity_add_left rw (ws + 1) 8
    end
#pop-options

/// ========================================================================
/// Small arithmetic / termination facts used by `walk_proof`.
///
/// Query splitting makes every leaf goal carry the whole (very large)
/// precondition of `walk_proof`, so even these trivial facts time out when
/// left to the SMT solver inline. Proving them here, in an empty context, and
/// applying them as lemmas removes the SMT call at the use site.
/// ========================================================================
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"

/// `new_fb - 8 + new_rw * 8 == obj + ws * 8` when the run starts at `obj`
/// (`rw = 0`, so `new_fb = obj` and `new_rw = ws + 1`).
private let rw0_run_bound (o: int) (ws: nat)
  : Lemma (o - 8 + (ws + 1) * 8 == o + ws * 8)
  = ML.distributivity_add_left ws 1 8

/// `fb + new_rw * 8 == obj + (ws + 1) * 8` when extending an existing run
/// (`new_rw = rw + ws + 1` and `fb + rw * 8 == obj`).
private let rwpos_run_contig (fbv: int) (rw ws: nat)
  : Lemma (fbv + (rw + ws + 1) * 8 == (fbv + rw * 8) + (ws + 1) * 8)
  = ML.distributivity_add_left rw (ws + 1) 8

/// The tail of a non-empty sequence is strictly shorter (termination measure).
private let rwpos_run_bound (fbv ov: int) (rw ws: nat)
  : Lemma (requires fbv + rw * 8 == ov)
          (ensures fbv - 8 + (rw + ws + 1) * 8 == ov + ws * 8)
  = ML.distributivity_add_left rw (ws + 1) 8;
    ML.distributivity_add_left ws 1 8

private let tail_len_lt (#a: Type) (s: Seq.seq a)
  : Lemma (requires Seq.length s > 0)
          (ensures Seq.length (Seq.tail s) < Seq.length s)
  = ()
#pop-options

/// ========================================================================
/// Walk agreement from a position (`n >= heap_size` is the end of the walk)
/// ========================================================================

let wa (n: nat) (h1 h2: heap) : prop =
  if n >= heap_size then True
  else if n % 8 = 0 then HA.walk_agree (U64.uint_to_t n) h1 h2
  else False

/// Heaps equal from `n` on agree along the walk from `n`.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let wa_of_equal_from (n: nat) (h1 h2: heap)
  : Lemma (requires n % 8 == 0 /\
                    (forall (a: hp_addr). U64.v a >= n ==> read_word h1 a == read_word h2 a))
          (ensures wa n h1 h2)
  = if n >= heap_size then () else HA.walk_agree_of_equal_from (U64.uint_to_t n) h1 h2
#pop-options

/// A merged free block followed by an agreeing walk.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let wa_run_step (f c: heap) (fb: obj_addr) (rw: pos) (start: nat)
  : Lemma (requires rw - 1 < pow2 54 /\
                    U64.v fb - 8 + rw * 8 == start /\ start <= heap_size /\
                    read_word f (hd_address fb) == makeHeader (U64.uint_to_t (rw - 1)) Blue 0UL /\
                    read_word c (hd_address fb) == makeHeader (U64.uint_to_t (rw - 1)) Blue 0UL /\
                    (rw >= 2 ==> read_word f fb == read_word c fb) /\
                    wa start f c)
          (ensures wa (U64.v fb - 8) f c)
  = hd_address_spec fb;
    let wz : wosize = U64.uint_to_t (rw - 1) in
    makeHeader_getWosize wz Blue 0UL;
    makeHeader_getColor wz Blue 0UL;
    color_of_object_spec fb c;
    is_blue_iff fb c;
    wosize_of_object_spec fb c;
    f_address_spec (hd_address fb);
    hd_f_roundtrip (hd_address fb);
    f_hd_roundtrip fb;
    HA.walk_agree_step (hd_address fb) f c
#pop-options

/// A live block followed by an agreeing walk.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let wa_survivor_step (f c: heap) (obj: obj_addr) (next: nat)
  : Lemma (requires read_word f (hd_address obj) == read_word c (hd_address obj) /\
                    U64.v obj + U64.v (getWosize (read_word c (hd_address obj))) * 8 == next /\
                    next <= heap_size /\
                    ~(is_blue obj c) /\
                    (forall (a: hp_addr). U64.v a >= U64.v obj /\ U64.v a + 8 <= next ==>
                       read_word f a == read_word c a) /\
                    wa next f c)
          (ensures wa (U64.v obj - 8) f c)
  = hd_address_spec obj;
    wosize_of_object_spec obj c;
    f_address_spec (hd_address obj);
    hd_f_roundtrip (hd_address obj);
    f_hd_roundtrip obj;
    HA.walk_agree_step (hd_address obj) f c
#pop-options

/// ========================================================================
/// The rest of the walk leaves lower addresses alone
/// ========================================================================

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let rec fused_aux_preserves_low
    (g h: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t) (a: hp_addr)
  : Lemma (requires
             (rw > 0 ==> U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                         U64.v fb % U64.v mword == 0 /\ U64.v a + 8 <= U64.v fb - 8) /\
             (forall (x: obj_addr). Seq.mem x objs ==> U64.v a + 8 <= U64.v x - 8))
          (ensures read_word (fst (fused_aux g h objs fb rw fp)) a == read_word h a)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then begin
      if rw > 0 then SpecCoalesce.flush_blue_preserves_outside h fb rw fp a
    end else begin
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      Seq.Properties.cons_head_tail objs;
      GC.Spec.Fields.mem_cons_lemma obj obj rest;
      let sub (x: obj_addr) : Lemma (Seq.mem x rest ==> Seq.mem x objs)
        = GC.Spec.Fields.mem_cons_lemma x obj rest
      in
      FStar.Classical.forall_intro sub;
      hd_address_spec obj;
      if is_black obj g then begin
        let h' = fst (SpecCoalesce.flush_blue h fb rw fp) in
        let fp' = snd (SpecCoalesce.flush_blue h fb rw fp) in
        (if rw > 0 then SpecCoalesce.flush_blue_preserves_outside h fb rw fp a);
        makeWhite_spec obj h';
        read_write_different h' (hd_address obj) a (colorHeader (read_word h' (hd_address obj)) White);
        fused_aux_preserves_low g (makeWhite obj h') rest 0UL 0 fp' a
      end else begin
        let ws = U64.v (wosize_of_object obj g) in
        let new_fb : U64.t = if rw = 0 then obj else fb in
        fused_aux_preserves_low g h rest new_fb (rw + ws + 1) fp a
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let rec coalesce_aux_preserves_low
    (g0 h: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t) (a: hp_addr)
  : Lemma (requires
             (rw > 0 ==> U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                         U64.v fb % U64.v mword == 0 /\ U64.v a + 8 <= U64.v fb - 8) /\
             (forall (x: obj_addr). Seq.mem x objs ==> U64.v a + 8 <= U64.v x - 8))
          (ensures read_word (fst (SpecCoalesce.coalesce_aux g0 h objs fb rw fp)) a == read_word h a)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then begin
      if rw > 0 then SpecCoalesce.flush_blue_preserves_outside h fb rw fp a
    end else begin
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      Seq.Properties.cons_head_tail objs;
      GC.Spec.Fields.mem_cons_lemma obj obj rest;
      let sub (x: obj_addr) : Lemma (Seq.mem x rest ==> Seq.mem x objs)
        = GC.Spec.Fields.mem_cons_lemma x obj rest
      in
      FStar.Classical.forall_intro sub;
      if is_blue obj g0 then begin
        let ws = U64.v (wosize_of_object obj g0) in
        let new_fb : U64.t = if rw = 0 then obj else fb in
        coalesce_aux_preserves_low g0 h rest new_fb (rw + ws + 1) fp a
      end else begin
        let h' = fst (SpecCoalesce.flush_blue h fb rw fp) in
        let fp' = snd (SpecCoalesce.flush_blue h fb rw fp) in
        (if rw > 0 then SpecCoalesce.flush_blue_preserves_outside h fb rw fp a);
        coalesce_aux_preserves_low g0 h' rest 0UL 0 fp' a
      end
    end
#pop-options

/// Every later object starts at least a word past the end of the head.
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let tail_beyond_head (g: heap) (objs: seq obj_addr) (x: obj_addr)
  : Lemma (requires Seq.length objs > 0 /\ objs_well_separated g objs /\ Seq.mem x (Seq.tail objs))
          (ensures U64.v x >= U64.v (Seq.head objs) + U64.v (wosize_of_object (Seq.head objs) g) * 8 + 8)
  = let o = Seq.head objs in
    let w = U64.v (wosize_of_object o g) in
    assert (U64.v x > U64.v o + w * 8);
    ML.lemma_mod_plus_distr_l (U64.v o) (w * 8) 8;
    ML.cancel_mul_mod w 8
#pop-options

/// ========================================================================
/// The step cases
/// ========================================================================

/// The common shape of the induction's hypotheses.
let walk_hyps (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (start: nat) : prop =
  Seq.length h_f == heap_size /\ Seq.length h_c == heap_size /\
  (forall (x: obj_addr). Seq.mem x objs ==> (is_black x g <==> ~(is_blue x gs))) /\
  (forall (x: obj_addr). Seq.mem x objs ==> wosize_of_object x g == wosize_of_object x gs) /\
  (forall (a: hp_addr).
     U64.v a >= start /\
     (forall (x: obj_addr). Seq.mem x objs ==>
        U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8) ==>
     read_word h_f a == read_word h_c a) /\
  (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==>
     getWosize (read_word h_f (hd_address x)) == getWosize (read_word h_c (hd_address x)) /\
     getTag (read_word h_f (hd_address x)) == getTag (read_word h_c (hd_address x)) /\
     U64.v (getWosize (read_word h_c (hd_address x))) == U64.v (wosize_of_object x g)) /\
  (forall (x: obj_addr) (a: hp_addr).
     Seq.mem x objs /\ is_black x g /\
     U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
     read_word h_f a == read_word h_c a) /\
  (forall (x: obj_addr). Seq.mem x objs /\ is_black x g ==> is_white x h_c) /\
  (rw > 0 ==> (forall (x: obj_addr). Seq.mem x objs ==> U64.v x >= U64.v fb + rw * 8)) /\
  (rw > 0 ==>
    (U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\ U64.v fb % U64.v mword == 0 /\
     rw - 1 < pow2 54 /\ U64.v fb - 8 + rw * 8 <= heap_size)) /\
  objs_well_separated g objs /\
  objs_contiguous g objs /\
  (rw > 0 /\ Seq.length objs > 0 ==> U64.v fb + rw * 8 == U64.v (Seq.head objs)) /\
  (forall (x: obj_addr). Seq.mem x objs ==> U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size) /\
  start % 8 == 0 /\ start <= heap_size /\
  (Seq.length objs > 0 ==> U64.v (Seq.head objs) == start + 8) /\
  (rw > 0 ==> U64.v fb - 8 + rw * 8 == start)

let walk_goal (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
    (start: nat) : prop =
  let rf = fused_aux g h_f objs fb rw fp in
  let rc = SpecCoalesce.coalesce_aux gs h_c objs fb rw fp in
  snd rf == snd rc /\
  wa (if rw > 0 && U64.v fb >= 8 then U64.v fb - 8 else start) (fst rf) (fst rc)

/// A pending run that is flushed: the walk from its header agrees provided
/// the flushed heaps agree along the walk from the run's end.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let flushed_run_step (h_f h_c f c: heap) (fb: U64.t) (rw: pos) (fp: U64.t) (start: nat)
  : Lemma (requires
             U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\ U64.v fb % U64.v mword == 0 /\
             rw - 1 < pow2 54 /\ U64.v fb - 8 + rw * 8 == start /\ start <= heap_size /\
             (let fbo : obj_addr = fb in
              read_word f (hd_address fbo) ==
                read_word (fst (SpecCoalesce.flush_blue h_f fb rw fp)) (hd_address fbo) /\
              read_word c (hd_address fbo) ==
                read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) (hd_address fbo) /\
              (rw >= 2 ==>
                read_word f fbo == read_word (fst (SpecCoalesce.flush_blue h_f fb rw fp)) fbo /\
                read_word c fbo == read_word (fst (SpecCoalesce.flush_blue h_c fb rw fp)) fbo)) /\
             wa start f c)
          (ensures wa (U64.v fb - 8) f c)
  = let fbo : obj_addr = fb in
    hd_address_spec fbo;
    SpecCoalesce.flush_blue_header_spec h_f fbo rw fp;
    SpecCoalesce.flush_blue_header_spec h_c fbo rw fp;
    if rw >= 2 then begin
      SpecCoalesce.flush_blue_field1_spec h_f fbo rw fp;
      SpecCoalesce.flush_blue_field1_spec h_c fbo rw fp
    end;
    wa_run_step f c fbo rw start
#pop-options

/// Base case: nothing left to walk.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let walk_base (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t)
    (start: nat)
  : Lemma (requires walk_hyps g gs h_f h_c objs fb rw start /\ Seq.length objs == 0)
          (ensures walk_goal g gs h_f h_c objs fb rw fp start)
  = SCH.flush_blue_snd_heap_independent h_f h_c fb rw fp;
    let f = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    let c = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
    assert (fused_aux g h_f objs fb rw fp == SpecCoalesce.flush_blue h_f fb rw fp);
    assert (SpecCoalesce.coalesce_aux gs h_c objs fb rw fp == SpecCoalesce.flush_blue h_c fb rw fp);
    let eq (a: hp_addr) : Lemma (U64.v a >= start ==> read_word f a == read_word c a)
      = if U64.v a >= start && rw > 0 then flush_pair_preserves_outside h_f h_c fb rw fp a
    in
    FStar.Classical.forall_intro eq;
    wa_of_equal_from start f c;
    if rw > 0 then flushed_run_step h_f h_c f c fb rw fp start
#pop-options

/// Black head: the hypotheses carry over to the rest of the walk.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let walk_black_hyps (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat)
    (fp: U64.t) (start: nat)
  : Lemma (requires walk_hyps g gs h_f h_c objs fb rw start /\
                    Seq.length objs > 0 /\ is_black (Seq.head objs) g)
          (ensures (let obj = Seq.head objs in
                    let h_f'' = makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp)) in
                    let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
                    walk_hyps g gs h_f'' h_c' (Seq.tail objs) 0UL 0
                      (U64.v obj + U64.v (wosize_of_object obj g) * 8)))
  = let obj = Seq.head objs in
    let rest = Seq.tail objs in
    let wz = U64.v (wosize_of_object obj g) in
    let next = U64.v obj + wz * 8 in
    let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
    let h_f'' = makeWhite obj h_f' in
    SpecCoalesce.flush_blue_preserves_length h_f fb rw fp;
    SpecCoalesce.flush_blue_preserves_length h_c fb rw fp;
    Seq.Properties.cons_head_tail objs;
    GC.Spec.Fields.mem_cons_lemma obj obj rest;
    let sub (x: obj_addr) : Lemma (Seq.mem x rest ==> Seq.mem x objs)
      = GC.Spec.Fields.mem_cons_lemma x obj rest
    in
    FStar.Classical.forall_intro sub;
    hd_address_spec obj;
    makeWhite_spec obj h_f';
    let hd_obj = hd_address obj in
    // above the head object nothing was written
    let high (a: hp_addr)
      : Lemma (requires U64.v a >= next)
              (ensures read_word h_f'' a == read_word h_f a /\ read_word h_c' a == read_word h_c a)
      = (if rw > 0 then flush_pair_preserves_outside h_f h_c fb rw fp a);
        read_write_different h_f' hd_obj a (colorHeader (read_word h_f' hd_obj) White)
    in
    let c5 (a: hp_addr)
      : Lemma (requires U64.v a >= next /\
                        (forall (x: obj_addr). Seq.mem x rest ==>
                           U64.v a >= U64.v x + U64.v (wosize_of_object x g) * 8))
              (ensures read_word h_f'' a == read_word h_c' a)
      = high a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires c5);
    let c6 (x: obj_addr)
      : Lemma (requires Seq.mem x rest /\ is_black x g)
              (ensures
                getWosize (read_word h_f'' (hd_address x)) == getWosize (read_word h_c' (hd_address x)) /\
                getTag (read_word h_f'' (hd_address x)) == getTag (read_word h_c' (hd_address x)) /\
                U64.v (getWosize (read_word h_c' (hd_address x))) == U64.v (wosize_of_object x g) /\
                is_white x h_c')
      = black_case_rest_headers g h_f h_c objs fb rw fp x;
        tail_beyond_head g objs x;
        hd_address_spec x;
        high (hd_address x)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires c6);
    let c7 (x: obj_addr)
      : Lemma (requires Seq.mem x rest /\ is_black x g)
              (ensures forall (a: hp_addr).
                 U64.v a >= U64.v x /\ U64.v a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                 read_word h_f'' a == read_word h_c' a)
      = black_case_body_agree g h_f h_c objs fb rw fp x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires c7);
    ML.lemma_mod_plus_distr_l (U64.v obj) (wz * 8) 8;
    ML.cancel_mul_mod wz 8;
    if Seq.length rest > 0 then begin
      contiguous_head g objs;
      ML.distributivity_add_left wz 1 8
    end
#pop-options

/// Black head: the conclusion for the whole walk from the rest's.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let walk_black_conclude (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat)
    (fp: U64.t) (start: nat)
  : Lemma (requires walk_hyps g gs h_f h_c objs fb rw start /\
                    Seq.length objs > 0 /\ is_black (Seq.head objs) g /\
                    (let obj = Seq.head objs in
                     let h_f'' = makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp)) in
                     let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
                     let fp' = snd (SpecCoalesce.flush_blue h_f fb rw fp) in
                     walk_goal g gs h_f'' h_c' (Seq.tail objs) 0UL 0 fp'
                       (U64.v obj + U64.v (wosize_of_object obj g) * 8)))
          (ensures walk_goal g gs h_f h_c objs fb rw fp start)
  = let obj = Seq.head objs in
    let rest = Seq.tail objs in
    let wz = U64.v (wosize_of_object obj g) in
    let next = U64.v obj + wz * 8 in
    let h_f' = fst (SpecCoalesce.flush_blue h_f fb rw fp) in
    let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
    let fp' = snd (SpecCoalesce.flush_blue h_f fb rw fp) in
    let h_f'' = makeWhite obj h_f' in
    SCH.flush_blue_snd_heap_independent h_f h_c fb rw fp;
    SpecCoalesce.flush_blue_preserves_length h_f fb rw fp;
    SpecCoalesce.flush_blue_preserves_length h_c fb rw fp;
    Seq.Properties.cons_head_tail objs;
    GC.Spec.Fields.mem_cons_lemma obj obj rest;
    assert (~(is_blue obj gs));
    // one step of each walk
    assert (fused_aux g h_f objs fb rw fp == fused_aux g h_f'' rest 0UL 0 fp');
    assert (SpecCoalesce.coalesce_aux gs h_c objs fb rw fp ==
            SpecCoalesce.coalesce_aux gs h_c' rest 0UL 0 fp');
    let f = fst (fused_aux g h_f'' rest 0UL 0 fp') in
    let c = fst (SpecCoalesce.coalesce_aux gs h_c' rest 0UL 0 fp') in
    hd_address_spec obj;
    let hd_obj = hd_address obj in
    makeWhite_spec obj h_f';
    // below `next`, the rest of the walk wrote nothing
    let low (a: hp_addr)
      : Lemma (requires U64.v a + 8 <= next)
              (ensures read_word f a == read_word h_f'' a /\ read_word c a == read_word h_c' a)
      = let beyond (x: obj_addr) : Lemma (Seq.mem x rest ==> U64.v a + 8 <= U64.v x - 8)
          = if Seq.mem x rest then tail_beyond_head g objs x
        in
        FStar.Classical.forall_intro beyond;
        fused_aux_preserves_low g h_f'' rest 0UL 0 fp' a;
        coalesce_aux_preserves_low gs h_c' rest 0UL 0 fp' a
    in
    // the survivor's own header and body
    low hd_obj;
    (if rw > 0 then flush_pair_preserves_outside h_f h_c fb rw fp hd_obj);
    read_write_same h_f' hd_obj (colorHeader (read_word h_f' hd_obj) White);
    SCH.colorHeader_same_wz_tag (read_word h_f hd_obj) (read_word h_c hd_obj) White;
    is_white_iff obj h_c;
    color_of_object_spec obj h_c;
    SCH.colorHeader_idempotent (read_word h_c hd_obj) White;
    assert (read_word f hd_obj == read_word c hd_obj);
    color_of_header_eq obj c h_c;
    GC.Spec.Fields.colors_exhaustive_and_exclusive obj h_c;
    let body (a: hp_addr)
      : Lemma (requires U64.v a >= U64.v obj /\ U64.v a + 8 <= next)
              (ensures read_word f a == read_word c a)
      = low a;
        (if rw > 0 then flush_pair_preserves_outside h_f h_c fb rw fp a);
        read_write_different h_f' hd_obj a (colorHeader (read_word h_f' hd_obj) White)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body);
    wa_survivor_step f c obj next;
    // and the run flushed in front of it
    if rw > 0 then begin
      let fbo : obj_addr = fb in
      hd_address_spec fbo;
      low (hd_address fbo);
      read_write_different h_f' hd_obj (hd_address fbo) (colorHeader (read_word h_f' hd_obj) White);
      if rw >= 2 then begin
        low fbo;
        read_write_different h_f' hd_obj fbo (colorHeader (read_word h_f' hd_obj) White)
      end;
      flushed_run_step h_f h_c f c fb rw fp start
    end
#pop-options

/// Dead head: it joins the pending run.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let walk_dead_hyps (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat)
    (start: nat)
  : Lemma (requires walk_hyps g gs h_f h_c objs fb rw start /\
                    Seq.length objs > 0 /\ ~(is_black (Seq.head objs) g))
          (ensures (let obj = Seq.head objs in
                    let ws = U64.v (wosize_of_object obj g) in
                    let new_fb : U64.t = if rw = 0 then obj else fb in
                    walk_hyps g gs h_f h_c (Seq.tail objs) new_fb (rw + ws + 1)
                      (U64.v obj + ws * 8)))
  = let obj = Seq.head objs in
    let rest = Seq.tail objs in
    let ws = U64.v (wosize_of_object obj g) in
    let new_fb : U64.t = if rw = 0 then obj else fb in
    let new_rw = rw + ws + 1 in
    let next = U64.v obj + ws * 8 in
    Seq.Properties.cons_head_tail objs;
    GC.Spec.Fields.mem_cons_lemma obj obj rest;
    let sub (x: obj_addr) : Lemma (Seq.mem x rest ==> Seq.mem x objs)
      = GC.Spec.Fields.mem_cons_lemma x obj rest
    in
    FStar.Classical.forall_intro sub;
    hd_address_spec obj;
    let geo (x: obj_addr) : Lemma (requires Seq.mem x rest)
                                  (ensures U64.v x >= U64.v new_fb + new_rw * 8)
      = tail_beyond_head g objs x;
        nonblack_case_geo_ok g objs fb rw x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires geo);
    ML.lemma_mod_plus_distr_l (U64.v obj) (ws * 8) 8;
    ML.cancel_mul_mod ws 8;
    (if rw = 0 then rw0_run_bound (U64.v obj) ws
     else rwpos_run_bound (U64.v fb) (U64.v obj) rw ws);
    // new_rw - 1 < pow2 54
    assert (new_rw * 8 <= heap_size);
    ML.lemma_div_le (new_rw * 8) heap_size 8;
    ML.cancel_mul_div new_rw 8;
    ML.lemma_div_lt_nat heap_size 57 3;
    assert_norm (pow2 3 == 8);
    if Seq.length rest > 0 then begin
      contiguous_head g objs;
      ML.distributivity_add_left ws 1 8;
      (if rw = 0 then begin
         ML.distributivity_add_left ws 1 8;
         rw0_run_bound (U64.v obj) ws
       end else rwpos_run_contig (U64.v fb) rw ws)
    end
#pop-options

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let walk_dead_conclude (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat)
    (fp: U64.t) (start: nat)
  : Lemma (requires walk_hyps g gs h_f h_c objs fb rw start /\
                    Seq.length objs > 0 /\ ~(is_black (Seq.head objs) g) /\
                    (let obj = Seq.head objs in
                     let ws = U64.v (wosize_of_object obj g) in
                     let new_fb : U64.t = if rw = 0 then obj else fb in
                     walk_goal g gs h_f h_c (Seq.tail objs) new_fb (rw + ws + 1) fp
                       (U64.v obj + ws * 8)))
          (ensures walk_goal g gs h_f h_c objs fb rw fp start)
  = let obj = Seq.head objs in
    Seq.Properties.cons_head_tail objs;
    GC.Spec.Fields.mem_cons_lemma obj obj (Seq.tail objs);
    assert (is_blue obj gs);
    hd_address_spec obj
#pop-options

/// ========================================================================
/// Main theorem
/// ========================================================================

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let rec walk_proof
  (g gs h_f h_c: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fp: U64.t) (start: nat)
  : Lemma (requires walk_hyps g gs h_f h_c objs fb rw start)
          (ensures walk_goal g gs h_f h_c objs fb rw fp start)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then walk_base g gs h_f h_c objs fb rw fp start
    else begin
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      tail_len_lt objs;
      let wz = U64.v (wosize_of_object obj g) in
      if is_black obj g then begin
        let h_f'' = makeWhite obj (fst (SpecCoalesce.flush_blue h_f fb rw fp)) in
        let h_c' = fst (SpecCoalesce.flush_blue h_c fb rw fp) in
        let fp' = snd (SpecCoalesce.flush_blue h_f fb rw fp) in
        walk_black_hyps g gs h_f h_c objs fb rw fp start;
        walk_proof g gs h_f'' h_c' rest 0UL 0 fp' (U64.v obj + wz * 8);
        walk_black_conclude g gs h_f h_c objs fb rw fp start
      end else begin
        let new_fb : U64.t = if rw = 0 then obj else fb in
        walk_dead_hyps g gs h_f h_c objs fb rw start;
        walk_proof g gs h_f h_c rest new_fb (rw + wz + 1) fp (U64.v obj + wz * 8);
        walk_dead_conclude g gs h_f h_c objs fb rw fp start
      end
    end
#pop-options
