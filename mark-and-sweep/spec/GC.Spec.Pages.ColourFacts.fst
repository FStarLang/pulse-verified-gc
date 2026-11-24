/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ColourFacts - what does not depend on the colours of live objects
/// ---------------------------------------------------------------------------
///
/// Recolouring an object that is not free, to a colour that is not blue,
/// keeps the walk, which objects are free, every value a field may hold
/// (`field_ok`) and `well_formed_heap`, in both directions.  The same holds
/// of `GC.Spec.Pages.Recolour.whiten`, which recolours a list of such objects
/// white.  `GC.Spec.Pages.AllocPhase` uses these facts to carry the
/// allocator's guarantees between a heap and its whitened copy.

module GC.Spec.Pages.ColourFacts

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Blocks
open GC.Spec.Pages.Theorems
open GC.Spec.Pages.Recolour

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module HE = GC.Gen.HeapExtensional
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// One object
/// ---------------------------------------------------------------------------

/// A colour change is a write of the recoloured header.
let sc_eq (h: heap) (x: obj_addr) (c: color)
  : Lemma (requires c <> Blue)
          (ensures set_object_color x h c ==
                   write_word h (hd_address x) (colorHeader (read_word h (hd_address x)) c))
  = match c with
    | White -> makeWhite_eq x h; makeWhite_spec x h
    | Gray -> makeGray_eq x h; makeGray_spec x h
    | Black -> makeBlack_eq x h; makeBlack_spec x h

let write_twice (h: heap) (a: hp_addr) (v1 v2: U64.t)
  : Lemma (write_word (write_word h a v1) a v2 == write_word h a v2)
  = let l = write_word (write_word h a v1) a v2 in
    let r = write_word h a v2 in
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word l (U64.uint_to_t b) == read_word r (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then begin
          let ba : hp_addr = U64.uint_to_t b in
          if b = U64.v a then begin
            read_write_same (write_word h a v1) a v2;
            read_write_same h a v2
          end else begin
            read_write_different (write_word h a v1) a ba v2;
            read_write_different h a ba v1;
            read_write_different h a ba v2
          end
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext l r

let write_same (h: heap) (a: hp_addr)
  : Lemma (write_word h a (read_word h a) == h)
  = let l = write_word h a (read_word h a) in
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word l (U64.uint_to_t b) == read_word h (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then begin
          let ba : hp_addr = U64.uint_to_t b in
          if b = U64.v a then read_write_same h a (read_word h a)
          else read_write_different h a ba (read_word h a)
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext l h

/// Painting `x` back its old colour undoes a colour change.
let recolour_back (h: heap) (x: obj_addr) (c: color)
  : Lemma (requires c <> Blue /\ ~(is_blue x h))
          (ensures set_object_color x (set_object_color x h c) (color_of_object x h) == h)
  = let a = hd_address x in
    let c0 = color_of_object x h in
    is_blue_iff x h;
    color_of_object_spec x h;
    sc_eq h x c;
    let h1 = set_object_color x h c in
    read_write_same h a (colorHeader (read_word h a) c);
    sc_eq h1 x c0;
    write_twice h a (colorHeader (read_word h a) c) (colorHeader (colorHeader (read_word h a) c) c0);
    colorHeader_twice (read_word h a) c c0;
    colorHeader_same (read_word h a) c0;
    write_same h a

/// Free is unchanged: `x` is not free before or after, and no other header
/// moves.
let blue_same (h: heap) (x: obj_addr) (c: color) (y: obj_addr)
  : Lemma (requires c <> Blue /\ ~(is_blue x h))
          (ensures is_blue y (set_object_color x h c) <==> is_blue y h)
  = if y = x then set_color_preserves_not_blue x x h c
    else begin
      hd_address_spec x;
      hd_address_spec y;
      color_change_locality x y h c;
      is_blue_iff y h;
      is_blue_iff y (set_object_color x h c)
    end

let field_ok_one (h h': heap) (v: U64.t)
  : Lemma (requires objects zero_addr h' == objects zero_addr h /\
                    (forall (y: obj_addr). is_blue y h' <==> is_blue y h) /\
                    (forall (y: obj_addr). resolve_object y h' == resolve_object y h /\
                                           is_infix y h' == is_infix y h /\
                                           is_closure y h' == is_closure y h /\
                                           wosize_of_object y h' == wosize_of_object y h))
          (ensures field_ok h v ==> field_ok h' v)
  = if is_pointer v && FStar.IndefiniteDescription.strong_excluded_middle (field_ok h v) then
      infix_addr_wf_congr h h' (objects zero_addr h) (v <: obj_addr)

/// The facts about one colour change.
let step_facts (h: heap) (x: obj_addr) (c: color)
  : Lemma (requires c <> Blue /\ ~(is_blue x h) /\ Seq.mem x (objects zero_addr h))
          (ensures (let h' = set_object_color x h c in
                    objects zero_addr h' == objects zero_addr h /\
                    (forall (y: obj_addr). is_blue y h' <==> is_blue y h) /\
                    (forall (v: U64.t). field_ok h' v <==> field_ok h v) /\
                    (well_formed_heap h' <==> well_formed_heap h)))
  = let h' = set_object_color x h c in
    color_change_preserves_objects h x c;
    FStar.Classical.forall_intro (blue_same h x c);
    let same (y: obj_addr) : Lemma (resolve_object y h' == resolve_object y h /\
                                    is_infix y h' == is_infix y h /\
                                    is_closure y h' == is_closure y h /\
                                    wosize_of_object y h' == wosize_of_object y h)
      = color_change_preserves_resolve x y h c;
        color_change_preserves_is_infix x y h c;
        color_change_preserves_is_closure x y h c;
        color_change_preserves_wosize_any x y h c
    in
    FStar.Classical.forall_intro same;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (field_ok_one h h'));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (field_ok_one h' h));
    let c0 = color_of_object x h in
    is_blue_iff x h;
    set_color_preserves_not_blue x x h c;
    if FStar.IndefiniteDescription.strong_excluded_middle (well_formed_heap h) then
      Mark.color_change_preserves_wf h x c;
    if FStar.IndefiniteDescription.strong_excluded_middle (well_formed_heap h') then begin
      Mark.color_change_preserves_wf h' x c0;
      recolour_back h x c
    end

/// ---------------------------------------------------------------------------
/// A list of objects
/// ---------------------------------------------------------------------------

/// The objects `xs` are objects of `g` that are not free.
let live_list (g: heap) (xs: list obj_addr) : prop =
  forall (x: obj_addr). L.mem x xs ==> Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)

#push-options "--fuel 1"
let rec whiten_facts (g: heap) (xs: list obj_addr)
  : Lemma (requires live_list g xs)
          (ensures (let gw = whiten g xs in
                    objects zero_addr gw == objects zero_addr g /\
                    (forall (y: obj_addr). is_blue y gw <==> is_blue y g) /\
                    (forall (v: U64.t). field_ok gw v <==> field_ok g v) /\
                    (well_formed_heap gw <==> well_formed_heap g)))
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' ->
      whiten_facts g xs';
      let g' = whiten g xs' in
      whiten_step_eq g' x;
      step_facts g' x White
#pop-options
