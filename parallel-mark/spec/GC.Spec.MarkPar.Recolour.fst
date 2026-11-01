/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Recolour — heaps that differ from g only in colours
///
/// `recoloured g h` says h is g with some enumerated objects recoloured,
/// never to or from blue.  Both marks, sequential and parallel, only ever
/// apply `set_object_color` to a non-blue enumerated object with a non-blue
/// colour, and one such change keeps the relation (`recoloured_set`).
///
/// At the end (`recoloured_word`), every word of h is fixed by the colours
/// alone: an enumerated object's header is g's header recoloured, and every
/// other word is g's.  So two recoloured heaps with the same colours are the
/// same heap (`recoloured_ext`).
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Recolour

open FStar.Seq
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Lib.Header

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module Helpers = GC.Spec.SweepCoalesce.Helpers

/// ---------------------------------------------------------------------------
/// Words and headers
/// ---------------------------------------------------------------------------

/// Two heaps that agree on every aligned word are equal.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let heap_ext (h1 h2: heap)
  : Lemma (requires forall (a: hp_addr). read_word h1 a == read_word h2 a)
          (ensures h1 == h2)
  = let aux (b: nat{b < heap_size}) : Lemma (Seq.index h1 b == Seq.index h2 b) =
      let a : hp_addr = U64.uint_to_t (b - b % 8) in
      let v = read_word h1 a in
      Helpers.write_word_id h1 a;
      Helpers.write_word_id h2 a;
      write_word_spec h1 a v;
      write_word_spec h2 a v
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro h1 h2
#pop-options

let colorHeader_tag (hdr: U64.t) (c: color)
  : Lemma (getTag (colorHeader hdr c) == getTag hdr)
  = getTag_spec hdr;
    getTag_spec (colorHeader hdr c);
    colorHeader_spec hdr c;
    mask_tag_value ();
    setColor_preserves_tag (U64.v hdr) (pack_color c);
    assert (U64.v (U64.logand hdr 0xFFUL) == FStar.UInt.logand #64 (U64.v hdr) 255);
    assert (U64.v (U64.logand (colorHeader hdr c) 0xFFUL) ==
            FStar.UInt.logand #64 (U64.v (colorHeader hdr c)) 255)

/// A header is its wosize, tag and colour.
let header_eq (w1 w2: U64.t)
  : Lemma (requires getWosize w1 == getWosize w2 /\ getTag w1 == getTag w2 /\
                    getColor w1 == getColor w2)
          (ensures w1 == w2)
  = Helpers.colorHeader_idempotent w1 (getColor w1);
    Helpers.colorHeader_idempotent w2 (getColor w2);
    Helpers.colorHeader_same_wz_tag w1 w2 (getColor w1)

/// ---------------------------------------------------------------------------
/// The relation
/// ---------------------------------------------------------------------------

let is_obj_hdr (g: heap) (a: hp_addr) : prop =
  exists (x: obj_addr). Seq.mem x (objects zero_addr g) /\ a == hd_address x

let same_header (g h: heap) (x: obj_addr) : prop =
  getWosize (read_word h (hd_address x)) == getWosize (read_word g (hd_address x)) /\
  getTag (read_word h (hd_address x)) == getTag (read_word g (hd_address x))

let recoloured (g h: heap) : prop =
  objects zero_addr h == objects zero_addr g /\
  well_formed_heap h /\
  create_graph h == create_graph g /\
  Mark.no_pointer_to_blue h /\
  (forall (a: hp_addr). read_word h a <> read_word g a ==> is_obj_hdr g a) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> same_header g h x) /\
  (forall (x: obj_addr). is_blue x h <==> is_blue x g) /\
  (forall (v: obj_addr). resolve_object v h == resolve_object v g) /\
  (forall (x: obj_addr) (i: U64.t{U64.v i >= 1}).
     Seq.mem x (objects zero_addr g) /\ U64.v i <= U64.v (wosize_of_object x g) ==>
     HeapGraph.get_field h x i == HeapGraph.get_field g x i)

let recoloured_refl (g: heap)
  : Lemma (requires well_formed_heap g /\ Mark.no_pointer_to_blue g)
          (ensures recoloured g g)
  = ()

/// ---------------------------------------------------------------------------
/// What a recoloured heap keeps
/// ---------------------------------------------------------------------------

let recoloured_wosize (g h: heap) (x: obj_addr)
  : Lemma (requires recoloured g h /\ Seq.mem x (objects zero_addr g))
          (ensures wosize_of_object x h == wosize_of_object x g)
  = wosize_of_object_spec x h;
    wosize_of_object_spec x g

let recoloured_no_scan (g h: heap) (x: obj_addr)
  : Lemma (requires recoloured g h /\ Seq.mem x (objects zero_addr g))
          (ensures is_no_scan x h == is_no_scan x g)
  = is_no_scan_spec x h; is_no_scan_spec x g;
    tag_of_object_spec x h; tag_of_object_spec x g

/// ---------------------------------------------------------------------------
/// One colour change keeps the relation
/// ---------------------------------------------------------------------------

/// After a non-blue colour change, nothing new is blue.
let set_color_blue (y z: obj_addr) (h: heap) (c: color)
  : Lemma (requires c <> Blue /\ ~(is_blue y h))
          (ensures is_blue z (set_object_color y h c) <==> is_blue z h)
  = if z = y then begin
      is_blue_iff y (set_object_color y h c);
      set_color_preserves_not_blue y y h c
    end else begin
      color_change_preserves_other_color y z h c;
      is_blue_iff z h;
      is_blue_iff z (set_object_color y h c)
    end

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let set_color_no_pointer_to_blue (h: heap) (y: obj_addr) (c: color)
  : Lemma (requires well_formed_heap h /\ Mark.no_pointer_to_blue h /\
                    Seq.mem y (objects zero_addr h) /\ c <> Blue /\ ~(is_blue y h))
          (ensures Mark.no_pointer_to_blue (set_object_color y h c))
  = let h' = set_object_color y h c in
    color_change_preserves_objects h y c;
    let aux (src dst: obj_addr)
      : Lemma (requires Seq.mem src (objects zero_addr h') /\ ~(is_blue src h') /\
                        fields_constrained h' src /\ points_to h' src dst)
              (ensures ~(is_blue (resolve_object dst h') h'))
      = set_color_blue y src h c;
        if src = y then begin
          color_preserves_is_no_scan y h c;
          color_change_preserves_points_to_self h y c dst
        end else begin
          color_change_preserves_other_is_no_scan y src h c;
          color_change_preserves_points_to_other h y c src dst
        end;
        color_change_preserves_resolve y dst h c;
        set_color_blue y (resolve_object dst h) h c
    in
    FStar.Classical.forall_intro_2 (fun src dst -> FStar.Classical.move_requires (aux src) dst)
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let recoloured_set (g h: heap) (y: obj_addr) (c: color)
  : Lemma (requires recoloured g h /\ Seq.mem y (objects zero_addr g) /\
                    c <> Blue /\ ~(is_blue y h))
          (ensures recoloured g (set_object_color y h c))
  = let h' = set_object_color y h c in
    color_change_preserves_objects h y c;
    Mark.color_change_preserves_wf h y c;
    Mark.color_preserves_create_graph y h c;
    set_color_no_pointer_to_blue h y c;
    let words (a: hp_addr)
      : Lemma (read_word h' a <> read_word g a ==> is_obj_hdr g a)
      = if hd_address y <> a then color_change_preserves_other_read y a h c
    in
    FStar.Classical.forall_intro words;
    let hdrs (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g)) (ensures same_header g h' x)
      = if x = y then begin
          set_object_color_preserves_getWosize_at_hd y h c;
          color_preserves_tag y h c;
          tag_of_object_spec y h;
          tag_of_object_spec y h'
        end else begin
          hd_address_injective x y;
          color_change_preserves_other_read y (hd_address x) h c
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires hdrs);
    let blues (x: obj_addr) : Lemma (is_blue x h' <==> is_blue x g) = set_color_blue y x h c in
    FStar.Classical.forall_intro blues;
    let res (v: obj_addr) : Lemma (resolve_object v h' == resolve_object v g) =
      color_change_preserves_resolve y v h c in
    FStar.Classical.forall_intro res;
    let fld (x: obj_addr) (i: U64.t{U64.v i >= 1})
      : Lemma (requires Seq.mem x (objects zero_addr g) /\ U64.v i <= U64.v (wosize_of_object x g))
              (ensures HeapGraph.get_field h' x i == HeapGraph.get_field g x i)
      = recoloured_wosize g h x;
        Mark.color_preserves_get_field y x h c i
    in
    FStar.Classical.forall_intro_2 (fun x i -> FStar.Classical.move_requires (fld x) i)
#pop-options

let recoloured_makeGray (g h: heap) (y: obj_addr)
  : Lemma (requires recoloured g h /\ Seq.mem y (objects zero_addr g) /\ ~(is_blue y h))
          (ensures recoloured g (makeGray y h))
  = makeGray_eq y h; recoloured_set g h y Gray

let recoloured_makeBlack (g h: heap) (y: obj_addr)
  : Lemma (requires recoloured g h /\ Seq.mem y (objects zero_addr g) /\ ~(is_blue y h))
          (ensures recoloured g (makeBlack y h))
  = makeBlack_eq y h; recoloured_set g h y Black

/// ---------------------------------------------------------------------------
/// The words of a recoloured heap
/// ---------------------------------------------------------------------------

let recoloured_header (g h: heap) (x: obj_addr)
  : Lemma (requires recoloured g h /\ Seq.mem x (objects zero_addr g))
          (ensures read_word h (hd_address x) ==
                   colorHeader (read_word g (hd_address x)) (color_of_object x h))
  = let w = read_word h (hd_address x) in
    color_of_object_spec x h;
    Helpers.colorHeader_idempotent w (getColor w);
    Helpers.colorHeader_same_wz_tag w (read_word g (hd_address x)) (getColor w)

let makeBlack_header (g: heap) (x: obj_addr)
  : Lemma (read_word (makeBlack x g) (hd_address x) ==
           colorHeader (read_word g (hd_address x)) Black)
  = makeBlack_spec x g;
    read_write_same g (hd_address x) (colorHeader (read_word g (hd_address x)) Black)

/// A header recoloured with its own colour is unchanged.
let header_own_color (g: heap) (x: obj_addr)
  : Lemma (colorHeader (read_word g (hd_address x)) (color_of_object x g) == read_word g (hd_address x))
  = color_of_object_spec x g;
    Helpers.colorHeader_idempotent (read_word g (hd_address x)) (color_of_object x g)

/// The final shape both marks are shown to have: the objects satisfying p
/// are black and each is g's header made black; every other object keeps
/// g's colour; so every other word is g's.
let marked_as (g h: heap) (p: obj_addr -> prop) : prop =
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ p x ==>
     read_word h (hd_address x) == read_word (makeBlack x g) (hd_address x)) /\
  (forall (a: hp_addr).
     (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ p x ==> a <> hd_address x) ==>
     read_word h a == read_word g a)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let recoloured_marked_as (g h: heap) (p: obj_addr -> prop)
  : Lemma (requires recoloured g h /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       (p x ==> is_black x h) /\
                       (~(p x) ==> color_of_object x h == color_of_object x g)))
          (ensures marked_as g h p)
  = let blk (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g) /\ p x)
              (ensures read_word h (hd_address x) == read_word (makeBlack x g) (hd_address x))
      = recoloured_header g h x;
        is_black_iff x h;
        makeBlack_header g x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires blk);
    let other (a: hp_addr)
      : Lemma (requires forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ p x ==> a <> hd_address x)
              (ensures read_word h a == read_word g a)
      = if read_word h a <> read_word g a then begin
          let x = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                    (fun x -> Seq.mem x (objects zero_addr g) /\ a == hd_address x) in
          recoloured_header g h x;
          header_own_color g x
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires other)
#pop-options

/// Two heaps of the same shape are equal.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let marked_as_ext (g h1 h2: heap) (p: obj_addr -> prop)
  : Lemma (requires marked_as g h1 p /\ marked_as g h2 p)
          (ensures h1 == h2)
  = let aux (a: hp_addr) : Lemma (read_word h1 a == read_word h2 a) =
      FStar.Classical.excluded_middle
        (exists (x: obj_addr). Seq.mem x (objects zero_addr g) /\ p x /\ a == hd_address x)
    in
    FStar.Classical.forall_intro aux;
    heap_ext h1 h2
#pop-options

let recoloured_blue (g h: heap) (x: obj_addr)
  : Lemma (requires recoloured g h) (ensures is_blue x h <==> is_blue x g)
  = ()
