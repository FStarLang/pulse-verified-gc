/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ByteFacts - the byte heap and the model heap it represents
/// ---------------------------------------------------------------------------
///
/// For a model heap `m` that a byte heap `g` represents (`brepr m g`: `m` is
/// `cabs g` word by word), the facts the page instance reads off:
///   - objects and model addresses (`obj_maddr`): an object `x` of the walk is
///     the block at model address `maddr x = (x - 8 - zero_addr) / 8`;
///   - blocks, headers and colours (`mblock`, `mhdr`);
///   - a word is recovered from the reading (`word_eq`): a header from its
///     decoded header, a field from its value;
///   - pointers (`ptr_resolve`): a pointer the model resolves, to a block or
///     through an infix header, is one `GC.Spec.Object.resolve_object`
///     resolves to the same object, and is infix-well-formed
///     (`infix_addr_wf`, which the byte heap's `well_formed_heap` asks of
///     every pointer field).

module GC.Spec.Top.ByteFacts

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Walk
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64
module Seq = FStar.Seq

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The model address of the block whose first field is at `x`.
let maddr (x: U64.t) : nat = if U64.v x >= 8 then mpos (U64.v x - 8) else 0

let obj_maddr (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g))
          (ensures pos (maddr x) + 8 == U64.v x /\ pos (maddr x) + 8 < heap_size /\
                   obj_of (maddr x) == x /\ M.is_block (abs g) (maddr x))
  = objects_mem_iff g zero_addr x;
    hd_address_spec x;
    walk_pos g (hd_address x);
    let y = maddr x in
    assert (pos y + 8 == U64.v x);
    U64.v_inj (obj_of y) x;
    abs_is_block g y

let maddr_obj (y: nat)
  : Lemma (requires pos y + 8 < heap_size) (ensures maddr (obj_of y) == y)
  = base_facts ();
    FStar.Math.Lemmas.lemma_div_plus 0 y 8

/// Blocks, headers and colours of a represented model heap.
let mblock (m: M.mheap) (g: heap) (y: nat)
  : Lemma (requires R.heq m (cabs g))
          (ensures M.is_block m y <==> (pos y + 8 < heap_size /\ Seq.mem (obj_of y) (objects zero_addr g)))
  = abs_is_block g y

let mhdr (m: M.mheap) (g: heap) (y: nat)
  : Lemma (requires R.heq m (cabs g) /\ M.is_block m y)
          (ensures pos y + 8 < heap_size /\
                   M.wz_of m y == U64.v (wosize_of_object (obj_of y) g) /\
                   M.tag_of m y == U64.v (tag_of_object (obj_of y) g) /\
                   M.col_of m y == abs_col (color_of_object (obj_of y) g) /\
                   (M.col_of m y == M.Blue <==> is_blue (obj_of y) g))
  = abs_header g y;
    abs_blue g y

/// ---------------------------------------------------------------------------
/// Words, from the reading
/// ---------------------------------------------------------------------------

/// A word of the model heap is a header or a field: the reading gives it.
let word_eq (g g': heap) (j: nat)
  : Lemma (requires j < msize /\ (exists (o: nat). M.covers (abs g) o j) /\ R.agree (abs g) (abs g'))
          (ensures word g j == word g' j)
  = if M.is_block (abs g) j then begin
      assert ((abs g).M.hd j == (abs g').M.hd j);
      abs_hdr_inj (word g j) (word g' j)
    end
    else begin
      assert (R.field_word (abs g) j);
      absv_inj (word g j) (word g' j)
    end

/// The byte word at an aligned address past `zero_addr`.
let word_at (g: heap) (a: hp_addr)
  : Lemma (requires U64.v a >= base)
          (ensures mpos (U64.v a) < msize /\ pos (mpos (U64.v a)) == U64.v a /\
                   word g (mpos (U64.v a)) == read_word g a)
  = base_facts ();
    FStar.Math.Lemmas.lemma_div_exact (U64.v a - base) 8;
    msize_pos (mpos (U64.v a));
    pos_aligned (mpos (U64.v a));
    U64.v_inj (hp (mpos (U64.v a))) a

/// ---------------------------------------------------------------------------
/// Pointers
/// ---------------------------------------------------------------------------

/// A pointer the model resolves resolves to the same object in the bytes,
/// and is infix-well-formed.
#push-options "--z3rlimit 40"
let ptr_resolve (g: heap) (b y: nat)
  : Lemma (requires M.resolve (abs g) b == Some y /\ b + 1 < msize /\ no_infix_block g)
          (ensures pos b + 8 < heap_size /\ pos y + 8 < heap_size /\
                   resolve_object (obj_of b) g == obj_of y /\
                   Seq.mem (obj_of y) (objects zero_addr g) /\
                   infix_addr_wf g (objects zero_addr g) (obj_of b))
  = base_facts ();
    msize_pos (b + 1);
    if M.is_block (abs g) b then begin
      resolve_block_bytes g b;
      abs_is_block g b;
      assert (~(is_infix (obj_of b) g));
      infix_addr_wf_non_infix g (objects zero_addr g) (obj_of b)
    end
    else begin
      resolve_infix_bytes g b y;
      abs_is_block g y;
      abs_header g y;
      let v = obj_of b in
      let k = b - y in
      let w = word g b in
      tag_low_byte w;
      wosize_high w;
      hd_of_obj b;
      wosize_of_object_spec v g;
      assert (U64.v (wosize_of_object v g) == k);
      parent_closure_addr_nat_spec v g;
      assert (parent_closure_addr_nat v g == pos y + 8);
      is_closure_spec (obj_of y) g;
      closure_tag_val ();
      assert (U64.v (U64.uint_to_t (pos y + 8)) == pos y + 8);
      U64.v_inj (U64.uint_to_t (pos y + 8)) (obj_of y);
      assert (infix_addr_conds g (objects zero_addr g) v);
      infix_addr_wf_intro g (objects zero_addr g) v
    end
#pop-options

/// The canonical reading has the blocks of `abs g`.
let wf_cabs (g: heap) : Lemma (requires M.well_formed (abs g)) (ensures M.well_formed (cabs g))
  = assert (forall (o: nat). M.is_block (cabs g) o == M.is_block (abs g) o);
    assert (forall (o: nat). M.hdr_of (cabs g) o == M.hdr_of (abs g) o);
    assert (forall (o w: nat). M.covers (cabs g) o w == M.covers (abs g) o w)

/// A pointer word is the pointer to the model block below it.
let ptr_b (v: U64.t) : nat = if U64.v v >= 8 + base then (U64.v v - 8 - base) / 8 else 0

let ptr_decode (v: U64.t)
  : Lemma (requires is_pointer v)
          (ensures (let b = ptr_b v in
                    absv v == M.VPtr (M.Major b) /\ pos b + 8 == U64.v v /\ b + 1 < msize /\
                    pos b + 8 < heap_size /\ obj_of b == v))
  = base_facts ();
    let b = ptr_b v in
    FStar.Math.Lemmas.lemma_div_exact (U64.v v - 8 - base) 8;
    msize_pos (b + 1);
    U64.v_inj (obj_of b) v

let obj_of_v (y: nat) : Lemma (requires pos y + 8 < heap_size) (ensures U64.v (obj_of y) == pos y + 8) = ()

let wf_abs (g: heap) : Lemma (requires M.well_formed (cabs g)) (ensures M.well_formed (abs g))
  = assert (forall (o: nat). M.is_block (cabs g) o == M.is_block (abs g) o);
    assert (forall (o: nat). M.hdr_of (cabs g) o == M.hdr_of (abs g) o);
    assert (forall (o w: nat). M.covers (cabs g) o w == M.covers (abs g) o w)

/// A field pointing to `t`: some field word is the pointer `t`.
#push-options "--fuel 1 --z3rlimit 40"
let rec efptu_elim (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (t: obj_addr)
  : Lemma (requires exists_field_pointing_to_unchecked g h wz t)
          (ensures exists (i: nat). i < U64.v wz /\ U64.v h + 8 * i < heap_size /\
                     (let a : hp_addr = U64.uint_to_t (U64.v h + 8 * i) in
                      is_pointer (read_word g a) /\ read_word g a == t))
          (decreases U64.v wz)
  = if wz = 0UL then assert (exists_field_pointing_to_unchecked g h wz t == false)
    else
    let idx = U64.sub wz 1UL in
    assert_norm (pow2 54 * 8 == pow2 57);
    assert_norm (pow2 57 + pow2 57 < pow2 64);
    let far = U64.add_mod h (U64.mul_mod idx mword) in
    FStar.Math.Lemmas.small_mod (U64.v idx * 8) (pow2 64);
    FStar.Math.Lemmas.small_mod (U64.v h + U64.v idx * 8) (pow2 64);
    assert (U64.v far == U64.v h + 8 * U64.v idx);
    if U64.v far >= heap_size || U64.v far % 8 <> 0 then
      assert (exists_field_pointing_to_unchecked g h wz t == false)
    else begin
      let fv = read_word g far in
      if is_pointer_to fv t then begin
        hd_address_spec fv; hd_address_spec t;
        U64.v_inj fv t;
        assert (U64.v h + 8 * U64.v idx < heap_size);
        assert (U64.uint_to_t (U64.v h + 8 * U64.v idx) == far)
      end
      else begin
        assert (exists_field_pointing_to_unchecked g h wz t == exists_field_pointing_to_unchecked g h idx t);
        efptu_elim g h idx t
      end
    end
#pop-options

/// A pointer the byte heap resolves, infix-well-formed, to an object: the
/// model resolves it to that object's block.
#push-options "--z3rlimit 40"
let ptr_resolve_back (g: heap) (v: U64.t)
  : Lemma (requires is_pointer v /\ no_infix_block g /\
                    Seq.mem (resolve_object v g) (objects zero_addr g) /\
                    infix_addr_wf g (objects zero_addr g) v)
          (ensures M.resolve (abs g) (ptr_b v) == Some (maddr (resolve_object v g)))
  = ptr_decode v;
    let b = ptr_b v in
    let r = resolve_object v g in
    obj_maddr g r;
    if is_infix v g then begin
      infix_addr_wf_elim g (objects zero_addr g) v;
      resolve_infix_spec v g;
      parent_closure_addr_nat_spec v g;
      let k = U64.v (wosize_of_object v g) in
      let w = word g b in
      hd_of_obj b;
      wosize_of_object_spec v g;
      tag_of_object_spec v g;
      is_infix_spec v g;
      infix_tag_val ();
      tag_low_byte w;
      wosize_high w;
      assert (U64.v w % 256 == 249);
      base_facts ();
      assert (~(is_pointer w) /\ ~(is_young_w w));
      assert (absv w == M.VInt (U64.v w));
      assert (M.infix_hdr (absv w) == Some k);
      if M.is_block (abs g) b then begin
        abs_is_block g b;
        assert (~(is_infix (obj_of b) g))
      end;
      let y = maddr r in
      assert (pos y + 8 == U64.v v - 8 * k);
      assert (y + k == b);
      abs_header g y;
      is_closure_spec r g;
      closure_tag_val ()
    end
    else begin
      resolve_non_infix v g;
      obj_maddr g v
    end
#pop-options
