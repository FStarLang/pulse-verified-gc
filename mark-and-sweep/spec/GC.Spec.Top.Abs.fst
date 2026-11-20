/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Abs - the abstraction from the byte-level heap to the model
/// ---------------------------------------------------------------------------
///
/// `abs g` reads the byte-level heap `g` (GC.Spec.Base) as a heap of the
/// top-level specification (GC.Spec.Top.Heap):
///   - model word `m` is the byte word at `zero_addr + 8 m`; the model heap has
///     `(heap_size - zero_addr) / 8` words;
///   - a block starts at `m` exactly when the heap walk from `zero_addr`
///     (`GC.Spec.Walk.reaches`) lands on its header and can step: the blocks of
///     the model are the objects of `objects zero_addr g` (`abs_is_block`);
///   - its header is the decoded header (wosize, tag, colour; blue stays
///     blue);
///   - a word holding an 8-aligned in-heap address (`is_pointer`) is a major
///     pointer to the model address of that object's header; a word whose low
///     byte is the infix tag is an infix header (its wosize is its offset from
///     the closure, in words, as in OCaml); any other word is bytes.
///
/// Proved: blocks, headers, colours and fields correspond (`abs_is_block`,
/// `abs_header`, `abs_field`); when the walk reaches the end of the heap the
/// model is tiled, and with `no_infix_block` it is well formed (`abs_tiled`,
/// `abs_well_formed`).

module GC.Spec.Top.Abs

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Walk
open GC.Lib.Header
module M = GC.Spec.Top.Heap
module U64 = FStar.UInt64

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let base : nat = U64.v zero_addr

let msize : nat = (heap_size - base) / 8

/// The byte position of model word `m`.
let pos (m: nat) : nat = base + 8 * m

let pos_aligned (m: nat) : Lemma (pos m % 8 == 0) = ()

let hp (m: nat{pos m < heap_size}) : hp_addr = pos_aligned m; mk_hp_addr (pos m)

/// The model address of a byte header position.
let mpos (p: nat) : nat = if p >= base then (p - base) / 8 else 0

let abs_col (c: color_sem) : M.colour =
  match c with
  | White -> M.White
  | Gray -> M.Grey
  | Black -> M.Black
  | Blue -> M.Blue

/// The walk lands on the header at model word `m` and can step.
let on_walk (g: heap) (m: nat) : bool =
  if pos m < heap_size then reaches g zero_addr (pos m) && can_step g (hp m) else false

let word (g: heap) (m: nat) : U64.t =
  if pos m < heap_size then read_word g (hp m) else 0UL

let abs_hdr (v: U64.t) : M.header =
  { M.wz = U64.v (getWosize v); M.tag = U64.v (getTag v); M.col = abs_col (getColor v) }

let infix_byte : nat = 249

let absv (v: U64.t) : M.value =
  if is_pointer v then M.VPtr (M.Major (mpos (U64.v v - 8)))
  else if U64.v (getTag v) = infix_byte then M.VInfix (U64.v (getWosize v))
  else M.VInt (U64.v v)

let abs (g: heap) : M.mheap =
  { M.size = msize;
    M.hd = (fun (m: nat) -> if on_walk g m then Some (abs_hdr (word g m)) else None);
    M.body = (fun (m: nat) -> absv (word g m)) }

/// ---------------------------------------------------------------------------
/// Blocks, headers, fields
/// ---------------------------------------------------------------------------

let msize_pos (m: nat) : Lemma (m < msize <==> pos m < heap_size)
  = assert (base % 8 == 0 /\ base + 8 < heap_size /\ heap_size % 8 == 0)

/// The object (first-field address) of the block at model word `m`.
let obj_of (m: nat{pos m + 8 < heap_size}) : obj_addr =
  pos_aligned m; mk_hp_addr (pos m + 8)

let abs_is_block (g: heap) (m: nat)
  : Lemma (M.is_block (abs g) m <==>
           (pos m + 8 < heap_size /\ Seq.mem (obj_of m) (objects zero_addr g)))
  = msize_pos m;
    if pos m + 8 < heap_size then begin
      objects_mem_iff g zero_addr (obj_of m);
      hd_address_pos (obj_of m)
    end

let abs_header (g: heap) (m: nat)
  : Lemma (requires M.is_block (abs g) m)
          (ensures pos m + 8 < heap_size /\
                   M.wz_of (abs g) m == U64.v (wosize_of_object (obj_of m) g) /\
                   M.tag_of (abs g) m == U64.v (tag_of_object (obj_of m) g) /\
                   M.col_of (abs g) m == abs_col (color_of_object (obj_of m) g))
  = abs_is_block g m;
    hd_address_pos (obj_of m);
    wosize_of_object_spec (obj_of m) g;
    tag_of_object_spec (obj_of m) g;
    color_of_object_spec (obj_of m) g

let abs_blue (g: heap) (m: nat)
  : Lemma (requires M.is_block (abs g) m)
          (ensures pos m + 8 < heap_size /\ (M.col_of (abs g) m == M.Blue <==> is_blue (obj_of m) g))
  = abs_header g m;
    is_blue_iff (obj_of m) g

/// Field `i` of a block is the word `i` past its first-field address.
let abs_field (g: heap) (m i: nat)
  : Lemma (requires pos (m + 1 + i) < heap_size)
          (ensures M.field (abs g) m i == absv (read_word g (hp (m + 1 + i))))
  = ()

/// ---------------------------------------------------------------------------
/// The walk tiles the model
/// ---------------------------------------------------------------------------

/// The walk positions are model words.
let walk_pos (g: heap) (p: hp_addr)
  : Lemma (requires reaches g zero_addr (U64.v p))
          (ensures U64.v p >= base /\ pos (mpos (U64.v p)) == U64.v p)
  = reaches_bounds g zero_addr (U64.v p)

let block_of_walk (g: heap) (p: hp_addr)
  : Lemma (requires reaches g zero_addr (U64.v p) /\ can_step g p)
          (ensures (let m = mpos (U64.v p) in
                    M.is_block (abs g) m /\ pos m == U64.v p /\
                    pos m + 8 * (M.wz_of (abs g) m + 1) == bnext g p))
  = walk_pos g p;
    let m = mpos (U64.v p) in
    msize_pos m;
    assert (hp m == p)

/// A block of the model is a block of the walk.
let abs_block_walk (g: heap) (o: nat)
  : Lemma (requires M.is_block (abs g) o)
          (ensures pos o < heap_size /\ reaches g zero_addr (pos o) /\ can_step g (hp o) /\
                   U64.v (hp o) == pos o /\ bnext g (hp o) == pos o + 8 * (M.wz_of (abs g) o + 1))
  = msize_pos o

let abs_uniq (g: heap) (o1 o2 w: nat)
  : Lemma (M.covers (abs g) o1 w /\ M.covers (abs g) o2 w ==> o1 == o2)
  = let h = abs g in
    if M.covers h o1 w && M.covers h o2 w && o1 <> o2 then begin
      abs_block_walk g o1;
      abs_block_walk g o2;
      if o1 < o2 then reaches_block_before g zero_addr (hp o1) (pos o2)
      else reaches_block_before g zero_addr (hp o2) (pos o1)
    end

let abs_cover (g: heap) (w: nat)
  : Lemma (requires reaches g zero_addr heap_size /\ w < msize)
          (ensures exists (o: nat). M.covers (abs g) o w)
  = msize_pos w;
    let p = block_at g zero_addr heap_size (pos w) in
    block_of_walk g p;
    let o = mpos (U64.v p) in
    let k = M.wz_of (abs g) o in
    assert (pos o <= pos w /\ pos w < pos o + 8 * (k + 1));
    assert (o <= w /\ w <= o + k);
    assert (M.covers (abs g) o w)

let abs_tiled (g: heap)
  : Lemma (requires reaches g zero_addr heap_size)
          (ensures M.tiled (abs g))
  = let h = abs g in
    assert (base % 8 == 0 /\ base + 8 < heap_size /\ heap_size % 8 == 0);
    let bnd (o: nat) : Lemma (M.is_block h o ==> o + M.wz_of h o < h.M.size)
      = if M.is_block h o then begin
          msize_pos o;
          assert (can_step g (hp o));
          msize_pos (o + M.wz_of h o)
        end in
    FStar.Classical.forall_intro bnd;
    let cov (w: nat) : Lemma (w < h.M.size ==> (exists (o: nat). M.covers h o w))
      = if w < h.M.size then abs_cover g w in
    FStar.Classical.forall_intro cov;
    FStar.Classical.forall_intro_3 (abs_uniq g)

let abs_well_formed (g: heap)
  : Lemma (requires reaches g zero_addr heap_size /\ no_infix_block g)
          (ensures M.well_formed (abs g))
  = abs_tiled g;
    let nt (o: nat) : Lemma (M.is_block (abs g) o ==> M.tag_of (abs g) o <> M.infix_tag)
      = if M.is_block (abs g) o then begin
          abs_is_block g o;
          abs_header g o;
          is_infix_spec (obj_of o) g;
          infix_tag_val ()
        end in
    FStar.Classical.forall_intro nt
