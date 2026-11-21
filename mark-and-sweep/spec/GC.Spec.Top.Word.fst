/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Word - a machine word, read as a model value or header
/// ---------------------------------------------------------------------------
///
/// The byte-level heaps of this repository (the major heap of GC.Spec.Base,
/// the nursery of GC.Gen.MinorHeap) hold 64-bit words.  A word is read as:
///   - a major pointer when it is an 8-aligned address past `zero_addr` in
///     the major heap (`GC.Spec.Fields.is_pointer`): the model address of the
///     object's header, `(v - 8 - zero_addr) / 8`;
///   - a young pointer when it is an 8-aligned nursery offset of an object
///     (`8 <= v < minor_heap_size`, the reading of `GC.Gen.Base.to_minor_offset`
///     and `is_minor_addr`): the model address `(v - 8) / 8`;
///   - otherwise a word of bytes, `VInt v` (an infix header is one, whole,
///     colour bits included).
/// The reading loses nothing: on the words it can produce (`storable_w`) it
/// has an inverse (`concv`, `absv_concv`).  A header word is read as its
/// wosize, tag and colour (`abs_hdr`), with an inverse for every header of a
/// block that fits (`enc_hdr`, `abs_hdr_enc`).

module GC.Spec.Top.Word

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
module M = GC.Spec.Top.Heap
module U64 = FStar.UInt64
module GB = GC.Gen.Base

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let base : nat = U64.v zero_addr

/// The major heap's size, in words, from `zero_addr`.
let msize : nat = (heap_size - base) / 8

/// The nursery's size, in words.
let ywords : nat = GB.minor_heap_size / 8

let base_facts () : Lemma (base % 8 == 0 /\ base + 16 <= heap_size /\ heap_size % 8 == 0 /\
                           base + 8 * msize == heap_size /\ msize >= 2 /\ msize < pow2 54 /\
                           GB.minor_heap_size <= base /\ 8 * ywords == GB.minor_heap_size /\ ywords >= 2)
  = GB.zero_addr_above_minor ();
    assert_norm (pow2 57 == 8 * pow2 54)

/// A young pointer: an aligned nursery offset with room for a header below.
let is_young_w (v: U64.t) : bool =
  U64.v v % 8 = 0 && 8 <= U64.v v && U64.v v < GB.minor_heap_size

let absv (v: U64.t) : M.value =
  if is_pointer v then M.VPtr (M.Major ((U64.v v - 8 - base) / 8))
  else if is_young_w v then M.VPtr (M.Young ((U64.v v - 8) / 8))
  else M.VInt (U64.v v)

/// The values a word can hold.
let storable_w (v: M.value) : bool =
  match v with
  | M.VInt n -> 0 <= n && n < pow2 64 && not (is_pointer (U64.uint_to_t n)) && not (is_young_w (U64.uint_to_t n))
  | M.VPtr (M.Major a) -> base + 8 * a + 8 < heap_size
  | M.VPtr (M.Young a) -> 8 * a + 8 < GB.minor_heap_size

/// The word a storable value is.
let concv (v: M.value) : U64.t =
  match v with
  | M.VInt n -> if 0 <= n && n < pow2 64 then U64.uint_to_t n else 0UL
  | M.VPtr (M.Major a) -> if base + 8 * a + 8 < pow2 64 then U64.uint_to_t (base + 8 * a + 8) else 0UL
  | M.VPtr (M.Young a) -> if 8 * a + 8 < pow2 64 then U64.uint_to_t (8 * a + 8) else 0UL

let absv_concv (v: M.value)
  : Lemma (requires storable_w v) (ensures absv (concv v) == v)
  = base_facts ();
    match v with
    | M.VInt n -> ()
    | M.VPtr (M.Major a) -> ()
    | M.VPtr (M.Young a) -> ()

/// Every word the reading produces is storable.
let absv_storable (v: U64.t) : Lemma (storable_w (absv v))
  = base_facts ()

/// What OCaml puts in a field is storable: odd words, and pointers to every
/// block.
let odd_storable (n: nat) : Lemma (requires n < pow2 64 /\ n % 2 == 1) (ensures storable_w (M.VInt n)) = ()

let major_storable (a: nat) : Lemma (requires a + 1 < msize) (ensures storable_w (M.VPtr (M.Major a)))
  = base_facts ()

let young_storable (a: nat) : Lemma (requires a + 1 < ywords) (ensures storable_w (M.VPtr (M.Young a)))
  = base_facts ()

/// ---------------------------------------------------------------------------
/// Headers
/// ---------------------------------------------------------------------------

let abs_col (c: color_sem) : M.colour =
  match c with
  | White -> M.White
  | Gray -> M.Grey
  | Blue -> M.Blue
  | Black -> M.Black

let col_sem (c: M.colour) : color_sem =
  match c with
  | M.White -> White
  | M.Grey -> Gray
  | M.Blue -> Blue
  | M.Black -> Black

let abs_hdr (v: U64.t) : M.header =
  { M.wz = U64.v (getWosize v); M.tag = U64.v (getTag v); M.col = abs_col (getColor v) }

/// The header word of a header.
let enc_hdr (h: M.header) : U64.t =
  if h.M.wz < pow2 54 then begin
    assert_norm (pow2 54 < pow2 64);
    pack_header64 ({ wosize = h.M.wz; color = col_sem h.M.col; tag = h.M.tag })
  end
  else 0UL

#push-options "--z3rlimit 40"
let abs_hdr_enc (h: M.header)
  : Lemma (requires h.M.wz < pow2 54) (ensures abs_hdr (enc_hdr h) == h)
  = assert_norm (pow2 54 < pow2 64);
    let hs : header_sem = { wosize = h.M.wz; color = col_sem h.M.col; tag = h.M.tag } in
    let p = pack_header64 hs in
    assert_norm (pow2 54 < pow2 64);
    getWosize_spec p;
    get_wosize_pack_header hs;
    getTag_spec p;
    get_tag_pack_header hs;
    mask_tag_value ();
    getColor_spec p;
    get_color_pack_header hs;
    pack_unpack_color hs.color;
    assert (U64.v (getWosize p) == h.M.wz);
    assert (U64.v (getTag p) == h.M.tag);
    assert (getColor p == col_sem h.M.col)
#pop-options
