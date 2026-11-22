/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ByteWrite - word writes on the byte heap, read as the model
/// ---------------------------------------------------------------------------
///
/// The canonical reading (`GC.Spec.Top.Abs.cabs`) of a byte heap after the
/// writes the collectors make, for any byte heap:
///   - `cabs_congr`: two heaps whose blocks along the first one's walk have
///     the same sizes have the same blocks and field words; the reading of
///     the second is its words, at the first one's blocks;
///   - `cabs_write_field`: writing a field word of a block is the model's
///     `set_field`;
///   - `cabs_recolour`: recolouring the header of a block (`makeGray`,
///     `makeBlack`, `set_object_color`) is the model's `set_col`.
/// Nothing here depends on an allocator.

module GC.Spec.Top.ByteWrite

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Walk
open GC.Lib.Header
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteFacts
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64
module Seq = FStar.Seq

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Words after a write
/// ---------------------------------------------------------------------------

let word_write (g: heap) (k: nat{pos k < heap_size}) (v: U64.t) (j: nat)
  : Lemma (word (write_word g (hp k) v) j == (if j = k then v else word g j))
  = if pos j < heap_size then begin
      pos_aligned j; pos_aligned k;
      if j = k then read_write_same g (hp k) v
      else read_write_different g (hp k) (hp j) v
    end

/// ---------------------------------------------------------------------------
/// Same sizes along the walk
/// ---------------------------------------------------------------------------

let same_sizes (g g': heap) : prop =
  forall (q: hp_addr). reaches g zero_addr (U64.v q) ==> getWosize (read_word g' q) == getWosize (read_word g q)

let on_walk_congr (g g': heap) (j: nat)
  : Lemma (requires same_sizes g g') (ensures on_walk g' j == on_walk g j)
  = walk_congr g g' zero_addr

#push-options "--fuel 1"
let rec fw_below_congr (g g': heap) (w n: nat)
  : Lemma (requires same_sizes g g') (ensures fw_below g' w n == fw_below g w n) (decreases n)
  = if n > 0 then begin
      on_walk_congr g g' (n - 1);
      fw_below_congr g g' w (n - 1)
    end
#pop-options

let is_fw_congr (g g': heap) (w: nat)
  : Lemma (requires same_sizes g g') (ensures is_fw g' w == is_fw g w)
  = fw_below_congr g g' w w

/// **The reading of `g'`**: its words, at `g`'s blocks and field words.
let cabs_congr (g g': heap)
  : Lemma (requires same_sizes g g')
          (ensures (forall (j: nat). (cabs g').M.hd j == (if on_walk g j then Some (abs_hdr (word g' j)) else None)) /\
                   (forall (w: nat). (cabs g').M.body w == (if is_fw g w then absv (word g' w) else M.VInt 0)) /\
                   (forall (w: nat). is_fw g' w == is_fw g w))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (on_walk_congr g g'));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (is_fw_congr g g'))

/// ---------------------------------------------------------------------------
/// Field words and headers
/// ---------------------------------------------------------------------------

/// The walk does not land inside a block.
let inside_not_reached (g: heap) (o k: nat)
  : Lemma (requires M.covers (abs g) o k /\ o < k) (ensures ~(reaches g zero_addr (pos k)))
  = abs_block_walk g o;
    if reaches g zero_addr (pos k) then reaches_block_before g zero_addr (hp o) (pos k)

/// A header is no field word.
let header_not_fw (g: heap) (o: nat)
  : Lemma (requires M.is_block (abs g) o) (ensures is_fw g o == false)
  = is_fw_iff g o;
    FStar.Classical.forall_intro (fun (o': nat) -> abs_uniq g o' o o)

let is_block_cabs (g: heap) (o: nat) : Lemma (M.is_block (cabs g) o == M.is_block (abs g) o) = ()

/// A write off the walk keeps the sizes.
let off_walk_sizes (g: heap) (k: nat{pos k < heap_size}) (v: U64.t)
  : Lemma (requires ~(reaches g zero_addr (pos k))) (ensures same_sizes g (write_word g (hp k) v))
  = let one (q: hp_addr)
      : Lemma (reaches g zero_addr (U64.v q) ==> read_word (write_word g (hp k) v) q == read_word g q)
      = if reaches g zero_addr (U64.v q) then begin
          pos_aligned k;
          read_write_different g (hp k) q v
        end in
    FStar.Classical.forall_intro one

/// **Writing a field word** is the model's `set_field`.
#push-options "--z3rlimit 40"
let cabs_write_field (g: heap) (o i: nat) (v: U64.t)
  : Lemma (requires M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o)
          (ensures pos (o + 1 + i) < heap_size /\
                   R.heq (cabs (write_word g (hp (o + 1 + i)) v)) (M.set_field (cabs g) o i (absv v)))
  = let k = o + 1 + i in
    let h = abs g in
    assert (M.covers h o k);
    abs_block_walk g o;
    msize_pos k;
    msize_pos (o + M.wz_of h o);
    inside_not_reached g o k;
    let g' = write_word g (hp k) v in
    off_walk_sizes g k v;
    cabs_congr g g';
    FStar.Classical.forall_intro (word_write g k v);
    is_fw_iff g k;
    assert (is_fw g k);
    let hd (j: nat) : Lemma ((cabs g').M.hd j == (cabs g).M.hd j)
      = if on_walk g j then assert (j <> k) in
    FStar.Classical.forall_intro hd
#pop-options

/// Recolouring a header word.
#push-options "--z3rlimit 40"
let colorHeader_abs (v: U64.t) (c: color)
  : Lemma (abs_hdr (colorHeader v c) ==
           ({ M.wz = (abs_hdr v).M.wz; M.tag = (abs_hdr v).M.tag; M.col = abs_col c }))
  = colorHeader_preserves_wosize v c;
    colorHeader_getColor v c;
    colorHeader_spec v c;
    let w = U64.v v in
    let pc = pack_color c in
    assert (pc < 4);
    setColor_preserves_tag w pc;
    tag_low_byte v;
    tag_low_byte (colorHeader v c);
    mask_tag_value ();
    FStar.UInt.logand_mask #64 w 8;
    FStar.UInt.logand_mask #64 (set_color w pc) 8;
    assert_norm (pow2 8 == 256)
#pop-options

let recolour_sizes (g: heap) (o: nat) (c: color)
  : Lemma (requires M.is_block (abs g) o)
          (ensures pos o < heap_size /\ same_sizes g (write_word g (hp o) (colorHeader (word g o) c)))
  = abs_block_walk g o;
    let w = colorHeader (word g o) c in
    colorHeader_preserves_wosize (word g o) c;
    let one (q: hp_addr)
      : Lemma (reaches g zero_addr (U64.v q) ==> getWosize (read_word (write_word g (hp o) w) q) == getWosize (read_word g q))
      = if reaches g zero_addr (U64.v q) then begin
          pos_aligned o;
          if q = hp o then read_write_same g (hp o) w
          else read_write_different g (hp o) q w
        end in
    FStar.Classical.forall_intro one

/// **Recolouring the header of a block** is the model's `set_col`.
#push-options "--z3rlimit 40"
let cabs_recolour_word (g: heap) (o: nat) (c: color)
  : Lemma (requires M.is_block (cabs g) o)
          (ensures pos o < heap_size /\
                   R.heq (cabs (write_word g (hp o) (colorHeader (word g o) c))) (M.set_col (cabs g) o (abs_col c)))
  = abs_block_walk g o;
    let g' = write_word g (hp o) (colorHeader (word g o) c) in
    recolour_sizes g o c;
    cabs_congr g g';
    FStar.Classical.forall_intro (word_write g o (colorHeader (word g o) c));
    header_not_fw g o;
    colorHeader_abs (word g o) c
#pop-options

let set_color_hp (g: heap) (o: nat) (c: color)
  : Lemma (requires pos o + 8 < heap_size /\ c <> Blue)
          (ensures set_object_color (obj_of o) g c == write_word g (hp o) (colorHeader (word g o) c))
  = hd_of_obj o;
    msize_pos o;
    match c with
    | Black -> makeBlack_spec (obj_of o) g; makeBlack_eq (obj_of o) g
    | Gray -> makeGray_spec (obj_of o) g; makeGray_eq (obj_of o) g
    | White -> makeWhite_spec (obj_of o) g; makeWhite_eq (obj_of o) g

/// **Recolouring an object**: `set_object_color` (so `makeGray`, `makeBlack`)
/// at the block's object is the model's `set_col`.
let cabs_recolour (g: heap) (o: nat) (c: color)
  : Lemma (requires M.is_block (cabs g) o /\ c <> Blue)
          (ensures pos o + 8 < heap_size /\
                   R.heq (cabs (set_object_color (obj_of o) g c)) (M.set_col (cabs g) o (abs_col c)))
  = abs_block_walk g o;
    abs_is_block g o;
    set_color_hp g o c;
    cabs_recolour_word g o c

/// ---------------------------------------------------------------------------
/// Pointer fields, read in the model
/// ---------------------------------------------------------------------------

/// The model resolves through the canonical reading as through `abs`.
let resolve_cabs (g: heap) (b y: nat)
  : Lemma (requires M.resolve (abs g) b == Some y) (ensures M.resolve (cabs g) b == Some y)
  = if not (M.is_block (abs g) b) then begin
      assert (M.covers (abs g) y b);
      is_fw_iff g b
    end

/// The field of an object that points to `child`.
let field_to (g: heap) (obj child: obj_addr) (i: nat) : prop =
  i < U64.v (wosize_of_object obj g) /\ U64.v obj + 8 * i < heap_size /\
  (let a : hp_addr = U64.uint_to_t (U64.v obj + 8 * i) in is_pointer (read_word g a) /\ read_word g a == child)

let field_to_exists (g: heap) (obj child: obj_addr)
  : Lemma (requires points_to g obj child) (ensures exists (i: nat). field_to g obj child i)
  = wosize_of_object_bound obj g;
    efptu_elim g obj (wosize_of_object obj g) child

/// That field, read in the model.
#push-options "--z3rlimit 40"
let field_model (g: heap) (obj child: obj_addr) (i: nat)
  : Lemma (requires Seq.mem obj (objects zero_addr g) /\ field_to g obj child i)
          (ensures (let o = maddr obj in
                    M.is_block (cabs g) o /\ i < M.wz_of (cabs g) o /\
                    M.field (cabs g) o i == M.VPtr (M.Major (ptr_b child))))
  = obj_maddr g obj;
    let o = maddr obj in
    abs_header g o;
    let w = o + 1 + i in
    assert (M.covers (abs g) o w);
    is_fw_iff g w;
    msize_pos w;
    abs_field g o i;
    U64.v_inj (hp w) (U64.uint_to_t (U64.v obj + 8 * i));
    ptr_decode child
#pop-options

/// The target of a pointer field of an object in use, read in the model.
let target_model (g: heap) (obj child: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g) /\
                    ~(is_no_scan obj g) /\ points_to g obj child)
          (ensures is_pointer child /\
                   M.resolve (cabs g) (ptr_b child) == Some (maddr (resolve_object child g)) /\
                   Seq.mem (resolve_object child g) (objects zero_addr g))
  = field_to_exists g obj child;
    wf_with_parts ();
    points_to_target_not_free free_stw g obj child;
    ptr_resolve_back g child;
    resolve_cabs g (ptr_b child) (maddr (resolve_object child g))

/// ---------------------------------------------------------------------------
/// Model facts on the bytes
/// ---------------------------------------------------------------------------

/// No block of the model is an infix block.
let no_infix_tags (m: M.mheap) : prop = forall (o: nat). M.is_block m o ==> M.tag_of m o <> M.infix_tag

let no_infix_of_model (g: heap)
  : Lemma (requires no_infix_tags (cabs g)) (ensures no_infix_block g)
  = let one (x: obj_addr) : Lemma (Seq.mem x (objects zero_addr g) ==> ~(is_infix x g))
      = if Seq.mem x (objects zero_addr g) then begin
          obj_maddr g x;
          let o = maddr x in
          U64.v_inj (obj_of o) x;
          abs_is_block g o;
          abs_header g o;
          is_infix_spec x g;
          infix_tag_val ()
        end in
    FStar.Classical.forall_intro one

/// The canonical reading resolves as `abs` does.
let resolve_abs_of_cabs (g: heap) (b y: nat)
  : Lemma (requires M.resolve (cabs g) b == Some y) (ensures M.resolve (abs g) b == Some y)
  = if not (M.is_block (cabs g) b) then assert (is_fw g b)

/// A pointer the model resolves is inside the heap.
let resolve_pos (g: heap) (a y: nat)
  : Lemma (requires M.resolve (cabs g) a == Some y)
          (ensures pos a + 8 < heap_size /\ a + 1 < msize /\ M.is_block (cabs g) y /\ y <= a)
  = abs_block_walk g y;
    msize_pos (a + 1)
