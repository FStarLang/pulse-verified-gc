/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFBytes - one first-fit allocation on the byte heap, at any phase
/// ---------------------------------------------------------------------------
///
/// Design doc §13.  From the colour-blind facts of akhil's first-fit at a
/// phase (`GC.Spec.Allocator.Phase`: it is the idle allocator recoloured, and
/// it reads only the free list) and an ascending free list (whose cells are
/// exactly the blue blocks with a field, so the list avoids every other
/// block), what one allocation does to the byte heap at any phase:
///   - nothing, when it fails;
///   - otherwise a block `x` of the size and tag asked, in the colour the
///     phase gives its header, that was not a block in use before; the blocks
///     in use are those before and `x`; every other block in use keeps its
///     header and fields; and the heap stays `ready` (`alloc_bytes`).

module GC.Spec.Top.FFBytes

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
module U64 = FStar.UInt64
module Seq = FStar.Seq
module W = GC.Spec.Walk
module Ph = GC.Spec.Phase
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AC = GC.Spec.Allocator.Cursor
module FL = GC.Spec.FreeList
module FLA = GC.Spec.FreeList.Ascending
module AL = GC.Spec.Allocator.Lemmas
module I = GC.Spec.AllocIface
module MW = GC.Gen.MarkPhase.Walk

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// What an allocation needs of the heap, and keeps.
let ready (g: heap) (fp: U64.t) : prop =
  blocks_fit g /\ no_infix_block g /\ FLA.fl_ascending g fp /\ W.reaches g zero_addr heap_size /\
  heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0

/// The allocator's entry conditions.
let ready_ok (g: heap) (fp: U64.t) : Lemma (requires ready g fp) (ensures AP.alloc_ok g fp)
  = FLA.fl_ascending_valid g fp

/// A block that is not blue is no list cell, so the list avoids it.
let avoids (g: heap) (fp: U64.t) (y: obj_addr)
  : Lemma (requires FLA.fl_ascending g fp /\ ~(is_blue y g))
          (ensures AL.chain_avoids g fp y heap_words = true)
  = FLA.fl_ascending_avoids g fp y heap_words

/// The new block's facts, when there is one.
let new_ok (ph: Ph.gc_phase) (g: heap) (wz: nat) (tag: AP.tag_t) (g': heap) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr g') /\ U64.v x + wz * 8 <= heap_size /\
  U64.v (wosize_of_object x g') == wz /\ tag_of_object x g' == tag /\
  color_of_object x g' == Ph.allocation_color ph (hd_address x) /\
  ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
  (forall (y: obj_addr). in_use free_stw g' y == (in_use free_stw g y || y = x)) /\
  I.others_unchanged g g'

/// What one allocation does.
let alloc_post (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t) (r: SA.alloc_result) : prop =
  (r.SA.obj_out == 0UL ==> r.SA.heap_out == g /\ r.SA.fp_out == fp) /\
  (r.SA.obj_out <> 0UL ==>
     U64.v r.SA.obj_out >= 8 /\ U64.v r.SA.obj_out < heap_size /\ U64.v r.SA.obj_out % 8 == 0 /\
     new_ok ph g wz tag r.SA.heap_out (r.SA.obj_out <: obj_addr) /\
     ready r.SA.heap_out r.SA.fp_out)

/// ---------------------------------------------------------------------------
/// The pieces
/// ---------------------------------------------------------------------------

/// The colour the phase gives, read as the header's.
let colour_of_new (ph: Ph.gc_phase) (g': heap) (x: obj_addr)
  : Lemma (requires (is_black x g' <==> Ph.allocation_color ph (hd_address x) == Black) /\
                    (is_white x g' <==> Ph.allocation_color ph (hd_address x) == White))
          (ensures color_of_object x g' == Ph.allocation_color ph (hd_address x))
  = is_black_iff x g';
    is_white_iff x g'

/// A block in use before, other than the new one, keeps its header and
/// body, so it stays in use.
#push-options "--z3rlimit 40"
let kept_one (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t) (y: obj_addr)
  : Lemma (requires ready g fp /\ wz >= 1 /\ Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) /\
                    (AP.alloc_at ph g fp wz tag).SA.obj_out <> 0UL)
          (ensures (let r = AP.alloc_at ph g fp wz tag in
                    (y <: U64.t) <> r.SA.obj_out /\
                    Seq.mem y (objects zero_addr r.SA.heap_out) /\
                    read_word r.SA.heap_out (hd_address y) == read_word g (hd_address y) /\
                    (forall (b: hp_addr). U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                       read_word r.SA.heap_out b == read_word g b) /\
                    ~(is_blue y r.SA.heap_out)))
  = ready_ok g fp;
    avoids g fp y;
    AP.alloc_at_obj_ne_excl ph g fp wz y tag;
    AP.alloc_at_preserves_objects ph g fp wz tag;
    AP.alloc_at_read_header_other ph g fp wz y tag;
    let r = AP.alloc_at ph g fp wz tag in
    let body (b: hp_addr)
      : Lemma (requires U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8)
              (ensures read_word r.SA.heap_out b == read_word g b)
      = AP.alloc_at_read_other ph g fp wz y b tag
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body);
    color_of_object_spec y g;
    color_of_object_spec y r.SA.heap_out;
    hd_address_spec y;
    is_blue_iff y g;
    is_blue_iff y r.SA.heap_out
#pop-options

/// The blocks in use after: those before, and the new one.
#push-options "--z3rlimit 40"
let in_use_after (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t) (y: obj_addr)
  : Lemma (requires ready g fp /\ wz >= 1 /\ (AP.alloc_at ph g fp wz tag).SA.obj_out <> 0UL)
          (ensures (let r = AP.alloc_at ph g fp wz tag in
                    in_use free_stw r.SA.heap_out y == (in_use free_stw g y || (y <: U64.t) = r.SA.obj_out)))
  = ready_ok g fp;
    let r = AP.alloc_at ph g fp wz tag in
    AP.alloc_at_obj_not_blue ph g fp wz tag;
    AP.alloc_at_obj_in_objects ph g fp wz tag;
    AP.alloc_at_only_new_is_obj_out ph g fp wz tag;
    if Seq.mem y (objects zero_addr g) && not (is_blue y g) then kept_one ph g fp wz tag y
    else if (y <: U64.t) = r.SA.obj_out then ()
    else if Seq.mem y (objects zero_addr g) then AP.alloc_at_preserves_blue ph g fp wz y tag
#pop-options

/// The new block was no block in use.
let not_used_before (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t)
  : Lemma (requires ready g fp /\ wz >= 1 /\ (AP.alloc_at ph g fp wz tag).SA.obj_out <> 0UL)
          (ensures (let r = AP.alloc_at ph g fp wz tag in
                    forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) ==>
                      (y <: U64.t) <> r.SA.obj_out))
  = ready_ok g fp;
    AP.alloc_at_obj_valid ph g fp wz tag;
    let one (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) ==>
               (y <: U64.t) <> (AP.alloc_at ph g fp wz tag).SA.obj_out)
      = if Seq.mem y (objects zero_addr g) && not (is_blue y g) then begin
          avoids g fp y;
          AP.alloc_at_obj_ne_excl ph g fp wz y tag
        end in
    FStar.Classical.forall_intro one

/// The heap stays ready.
#push-options "--z3rlimit 40"
let ready_after (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t)
  : Lemma (requires ready g fp /\ U64.v tag <> 249)
          (ensures (let r = AP.alloc_at ph g fp wz tag in ready r.SA.heap_out r.SA.fp_out))
  = ready_ok g fp;
    let r = AP.alloc_at ph g fp wz tag in
    let r0 = SA.alloc_spec g fp wz tag in
    AP.alloc_at_alloc_ok ph g fp wz tag;
    infix_tag_val ();
    AP.alloc_at_preserves_no_infix ph g fp wz tag;
    AP.alloc_at_recoloured ph g fp wz tag;
    AP.alloc_at_fields ph g fp wz tag;
    GC.Spec.Allocator.Ascending.alloc_spec_preserves_fl_ascending g fp wz tag;
    AP.recoloured_fl r0.SA.heap_out r.SA.heap_out r0.SA.fp_out;
    GC.Spec.Allocator.Dense.alloc_spec_preserves_dense_part1 g fp wz tag;
    AP.recoloured_facts r0.SA.heap_out r.SA.heap_out;
    MW.alloc_reaches ph g fp wz tag heap_size;
    AP.alloc_at_preserves_objects ph g fp wz tag;
    let y = Seq.index (objects zero_addr g) 0 in
    FStar.Seq.Properties.lemma_index_is_nth (objects zero_addr g) 0;
    GC.Spec.Pages.Promote.Mark.mem_of_index (objects zero_addr g) 0;
    assert (Seq.mem y (objects zero_addr r.SA.heap_out));
    FStar.Seq.Properties.mem_index y (objects zero_addr r.SA.heap_out)
#pop-options

/// ---------------------------------------------------------------------------
/// The allocation
/// ---------------------------------------------------------------------------

/// **One first-fit allocation at any phase.**
#push-options "--z3rlimit 40"
let alloc_bytes (ph: Ph.gc_phase) (g: heap) (fp: U64.t) (wz: nat) (tag: AP.tag_t)
  : Lemma (requires ready g fp /\ wz >= 1 /\ U64.v tag <> 249)
          (ensures alloc_post ph g fp wz tag (AP.alloc_at ph g fp wz tag))
  = ready_ok g fp;
    let r = AP.alloc_at ph g fp wz tag in
    AP.alloc_at_fields ph g fp wz tag;
    ready_after ph g fp wz tag;
    if r.SA.obj_out <> 0UL then begin
      AP.alloc_at_obj_valid ph g fp wz tag;
      AP.alloc_at_obj_in_objects ph g fp wz tag;
      AP.alloc_at_obj_wosize ph g fp wz tag;
      AP.alloc_at_obj_body_within_heap ph g fp wz tag;
      AP.alloc_at_obj_not_blue ph g fp wz tag;
      AP.alloc_at_recoloured ph g fp wz tag;
      let x : obj_addr = r.SA.obj_out in
      colour_of_new ph r.SA.heap_out x;
      not_used_before ph g fp wz tag;
      FStar.Classical.forall_intro (in_use_after ph g fp wz tag);
      let ou (y: obj_addr)
        : Lemma (Seq.mem y (objects zero_addr g) /\ ~(is_blue y g) ==>
                 Seq.mem y (objects zero_addr r.SA.heap_out) /\
                 read_word r.SA.heap_out (hd_address y) == read_word g (hd_address y) /\
                 (forall (b: hp_addr). U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                    read_word r.SA.heap_out b == read_word g b))
        = if Seq.mem y (objects zero_addr g) && not (is_blue y g) then kept_one ph g fp wz tag y
      in
      FStar.Classical.forall_intro ou;
      assert (I.others_unchanged g r.SA.heap_out)
    end
#pop-options
