/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Heap - the heap model of the top-level GC specification
/// ---------------------------------------------------------------------------
///
/// The top-level specification (`GC.Spec.Top.Iface`, `GC.Spec.Top.Run`) is
/// stated over this model, not over the byte-level heap of `GC.Spec.Base`.
/// The model keeps exactly what the specification talks about:
///   - the major heap is a sequence of `size` words, tiled by blocks; a block
///     at `o` has a header (wosize, tag, colour) at word `o` and its fields at
///     words `o+1 .. o+wz`;
///   - a field holds a `value`: bytes, a pointer (into the major heap or the
///     nursery), or an infix header (only inside a closure);
///   - whether a block is free is not in the heap: it is the allocator's
///     (`allocator.free`), as the specification says ("allocation status").
///
/// An instance over the byte-level heap (pages, first-fit) is related to this
/// model by an abstraction function that reads the heap walk; see
/// docs/gc-interfaces-design.md, section 7.
///
/// Addresses are word indices.  A pointer to an object is its header's
/// address; a pointer to an infix object is the address of its infix header
/// inside the closure, and `resolve` maps it to the closure.

module GC.Spec.Top.Heap

module L = FStar.List.Tot
module Seq = FStar.Seq

/// Blue is OCaml's colour of a free block.  Whether a block is free is the
/// allocator's (`allocator.free`); the allocators of this repository mark
/// their free blocks blue, the toy marks them white.
type colour = | White | Grey | Black | Blue

/// Grey or black: what the mark makes.
let dark (c: colour) : bool = c = Grey || c = Black

let tag_t = n:nat{n < 256}
let closure_tag : tag_t = 247
let infix_tag : tag_t = 249
let no_scan_tag : tag_t = 251
let scannable (t: tag_t) : bool = t < no_scan_tag

type ptr =
  | Major : nat -> ptr
  | Young : nat -> ptr

type value =
  | VInt   : int -> value
  | VPtr   : ptr -> value
  | VInfix : nat -> value     (* an infix header at offset k of its closure *)

type header = { wz: nat; tag: tag_t; col: colour }

/// A heap: the major heap, or the nursery (same shape, its own addresses).
/// `hd o` is the header of the block at `o`, if one starts there; `body w`
/// is the content of word `w` (meaningful for the field words of a block).
noeq type mheap = {
  size : nat;
  hd   : nat -> option header;
  body : nat -> value;
}

let is_block (h: mheap) (o: nat) : bool = o < h.size && Some? (h.hd o)

let hdr_of (h: mheap) (o: nat) : header =
  match h.hd o with Some x -> x | None -> { wz = 0; tag = 0; col = White }

let wz_of  (h: mheap) (o: nat) : nat    = (hdr_of h o).wz
let tag_of (h: mheap) (o: nat) : tag_t  = (hdr_of h o).tag
let col_of (h: mheap) (o: nat) : colour = (hdr_of h o).col

/// Field `i` of the block at `o`.
let field (h: mheap) (o i: nat) : value = h.body (o + 1 + i)

/// The block at `o` covers word `w` (its header or one of its fields).
let covers (h: mheap) (o w: nat) : bool =
  is_block h o && o <= w && w <= o + wz_of h o

/// The heap walk: the blocks tile `[0, size)`, so the walk from 0 reaches
/// `size` exactly.
let tiled (h: mheap) : prop =
  (forall (o: nat). is_block h o ==> o + wz_of h o < h.size) /\
  (forall (w: nat). w < h.size ==> (exists (o: nat). covers h o w)) /\
  (forall (o1 o2 w: nat). covers h o1 w /\ covers h o2 w ==> o1 == o2)

let well_formed (h: mheap) : prop =
  tiled h /\ (forall (o: nat). is_block h o ==> tag_of h o <> infix_tag)

/// The nursery: blocks of wosize at least 1, inside it, not overlapping.
let young_ok (y: mheap) : prop =
  (forall (o: nat). is_block y o ==> wz_of y o >= 1 /\ o + wz_of y o < y.size /\ tag_of y o <> infix_tag) /\
  (forall (o1 o2 w: nat). covers y o1 w /\ covers y o2 w ==> o1 == o2)

/// resolve(p): the object `a` points into.  Either `a` is a block, or `a`
/// holds an infix header `VInfix k` at offset `k` of a closure.
let resolve (h: mheap) (a: nat) : option nat =
  if is_block h a then Some a
  else match h.body a with
    | VInfix k ->
      if k >= 1 && k <= a && is_block h (a - k) && tag_of h (a - k) = closure_tag
         && k <= wz_of h (a - k)
      then Some (a - k) else None
    | _ -> None

/// Field `i` of `o` is a pointer field: `o` is scannable, `i` in range.
/// fields(o) is empty for a no-scan block.
let ptr_field (h: mheap) (o i: nat) : bool =
  is_block h o && scannable (tag_of h o) && i < wz_of h o

/// An edge of the major heap: a pointer field of `o` resolves to `o'`.
let major_edge (h: mheap) (o o': nat) : prop =
  exists (i a: nat). ptr_field h o i /\ field h o i == VPtr (Major a) /\ resolve h a == Some o'

/// An edge of the nursery.
let young_edge (y: mheap) (o o': nat) : prop =
  exists (i a: nat). ptr_field y o i /\ field y o i == VPtr (Young a) /\ resolve y a == Some o'

/// A slot of the remembered set: field `i` of major block `o`.
type slot = nat & nat

/// The world the collector sees: the major heap, the nursery, the program's
/// roots and the remembered set.
noeq type world = {
  maj   : mheap;
  yng   : mheap;
  roots : list value;
  rem   : list slot;
}

/// outside_refs(i): major objects pointed to by a root or by a field of a
/// young object (any young object: the nursery is not traced by a major
/// collection).
let root_ref (w: world) (o: nat) : prop =
  exists (a: nat). L.memP (VPtr (Major a)) w.roots /\ resolve w.maj a == Some o

let young_ref (w: world) (o: nat) : prop =
  exists (y i a: nat). ptr_field w.yng y i /\ field w.yng y i == VPtr (Major a) /\
                       resolve w.maj a == Some o

let outside_ref (w: world) (o: nat) : prop = root_ref w o \/ young_ref w o

/// reachable(i): major objects reachable from outside_refs(i) through
/// fields and resolve.
noeq type reach (w: world) : nat -> Type0 =
  | RBase : o:nat -> squash (outside_ref w o) -> reach w o
  | RStep : o:nat -> o':nat -> reach w o -> squash (major_edge w.maj o o') -> reach w o'

let reachable (w: world) (o: nat) : prop = exists (_: reach w o). True

/// The young objects the program can reach: from a root, or from a field of
/// a reachable major object, then through young fields.
noeq type yreach (w: world) : nat -> Type0 =
  | YRoot : y:nat -> a:nat ->
            squash (L.memP (VPtr (Young a)) w.roots /\ resolve w.yng a == Some y) -> yreach w y
  | YOld  : y:nat -> o:nat -> i:nat -> a:nat -> reach w o ->
            squash (ptr_field w.maj o i /\ field w.maj o i == VPtr (Young a) /\
                    resolve w.yng a == Some y) -> yreach w y
  | YStep : y:nat -> y':nat -> yreach w y -> squash (young_edge w.yng y y') -> yreach w y'

let yreachable (w: world) (y: nat) : prop = exists (_: yreach w y). True

/// What a minor collection traces: young objects reachable from the roots
/// and the remembered slots, through young fields.
noeq type mlive (w: world) : nat -> Type0 =
  | LRoot : y:nat -> a:nat ->
            squash (L.memP (VPtr (Young a)) w.roots /\ resolve w.yng a == Some y) -> mlive w y
  | LRem  : y:nat -> o:nat -> i:nat -> a:nat ->
            squash (L.memP (o, i) w.rem /\ ptr_field w.maj o i /\
                    field w.maj o i == VPtr (Young a) /\ resolve w.yng a == Some y) -> mlive w y
  | LStep : y:nat -> y':nat -> mlive w y -> squash (young_edge w.yng y y') -> mlive w y'

let minor_live (w: world) (y: nat) : prop = exists (_: mlive w y). True

/// ---------------------------------------------------------------------------
/// Heap updates used by the semantics
/// ---------------------------------------------------------------------------

/// Fill: write the fields of the block at `o` with `vs`.
let fill (h: mheap) (o: nat) (vs: list value) : mheap =
  { h with body = (fun (w: nat) ->
      if o < w && w - o - 1 < L.length vs then L.index vs (w - o - 1) else h.body w) }

/// Store `v` in field `i` of `o`.
let set_field (h: mheap) (o i: nat) (v: value) : mheap =
  { h with body = (fun (w: nat) -> if w = o + 1 + i then v else h.body w) }

/// Recolour the block at `o` (no effect if there is none).
let set_col (h: mheap) (o: nat) (c: colour) : mheap =
  { h with hd = (fun (x: nat) ->
      if x = o then (match h.hd x with Some hx -> Some ({ hx with col = c }) | None -> None)
      else h.hd x) }

/// The empty nursery of a given capacity.
let empty_heap (n: nat) : mheap =
  { size = n; hd = (fun _ -> None); body = (fun _ -> VInt 0) }

/// The fields of a block, as a list.
let rec fields_from (h: mheap) (o i n: nat) : Tot (list value) (decreases n) =
  if n = 0 then [] else field h o i :: fields_from h o (i + 1) (n - 1)

let fields_of (h: mheap) (o: nat) : list value = fields_from h o 0 (wz_of h o)

let rec fields_from_spec (h: mheap) (o i n: nat)
  : Lemma (ensures L.length (fields_from h o i n) == n /\
                   (forall (j: nat). j < n ==> L.index (fields_from h o i n) j == field h o (i + j)))
          (decreases n)
  = if n = 0 then ()
    else begin
      fields_from_spec h o (i + 1) (n - 1);
      let aux (j: nat) : Lemma (j < n ==> L.index (fields_from h o i n) j == field h o (i + j))
        = if j > 0 && j < n then assert (L.index (fields_from h o i n) j == L.index (fields_from h o (i + 1) (n - 1)) (j - 1)) in
      FStar.Classical.forall_intro aux
    end

let fields_of_spec (h: mheap) (o: nat)
  : Lemma (L.length (fields_of h o) == wz_of h o /\
           (forall (j: nat). j < wz_of h o ==> L.index (fields_of h o) j == field h o j))
  = fields_from_spec h o 0 (wz_of h o)

/// Same block: header (colour included) and every field.
let same_block (h h': mheap) (o: nat) : prop =
  h'.hd o == h.hd o /\ (forall (i: nat). i < wz_of h o ==> field h' o i == field h o i)

/// Same contents: size, tag and every field; the colour may differ.
let same_contents (h h': mheap) (o: nat) : prop =
  wz_of h' o == wz_of h o /\ tag_of h' o == tag_of h o /\
  (forall (i: nat). i < wz_of h o ==> field h' o i == field h o i)

/// Only colours changed: same blocks, sizes, tags and words.
let colours_only (h h': mheap) : prop =
  h'.size == h.size /\
  (forall (o: nat). is_block h' o == is_block h o) /\
  (forall (o: nat). wz_of h' o == wz_of h o /\ tag_of h' o == tag_of h o) /\
  (forall (w: nat). h'.body w == h.body w)

/// Sums over `[0, n)`.
let rec sum (n: nat) (f: nat -> GTot nat) : GTot nat (decreases n) =
  if n = 0 then 0 else f (n - 1) + sum (n - 1) f
