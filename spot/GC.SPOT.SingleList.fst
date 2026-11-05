/// ---------------------------------------------------------------------------
/// GC.SPOT.SingleList -- the shape invariant from one free block
/// ---------------------------------------------------------------------------
///
/// The concrete heaps below have one free block, whose link is null.  The
/// collector's state is the heads of the size-class free lists; with one free
/// block that is `fls_one k fp`, the block on the list `k` of its class and
/// every other list empty, and the shape invariant over it follows from the
/// single-list facts the concrete proofs establish.

module GC.SPOT.SingleList

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
module FreeListShape = GC.Gen.FreeListShape
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Mark = GC.Spec.Mark
module SweepInv = GC.Spec.SweepInv

/// No live object is on the one list.
let single_chain_objects_blue (g: heap) (fp: U64.t) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g) ==>
    AllocLemmas.chain_avoids g fp obj heap_words = true

/// Nothing is reachable from null.
#push-options "--fuel 1 --ifuel 1"
let null_meets_nothing (g: heap) (y: U64.t) (n: nat)
  : Lemma (FL.on_fl g 0UL y n == false)
  = ()
#pop-options

let unreachable_from_null (g: heap) (y: U64.t)
  : Lemma (~(FL.reachable_on_fl g 0UL y))
  = FStar.Classical.forall_intro (null_meets_nothing g y)

/// A block whose link is null is the whole list.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let single_cell (g: heap) (fp: U64.t) (y: U64.t)
  : Lemma (requires U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword == 0 /\ read_word g (fp <: hp_addr) == 0UL)
          (ensures (FL.reachable_on_fl g fp y ==> y == fp) /\
                   (y <> fp ==> AllocLemmas.chain_avoids g fp y heap_words = true))
  = (if y <> fp then begin
       let off (_: unit)
         : Lemma (requires FL.reachable_on_fl g fp y) (ensures False)
         = FL.reachable_uncons g fp y;
           unreachable_from_null g y
       in
       FStar.Classical.move_requires off ();
       hd_address_spec (fp <: obj_addr);
       if U64.v (hd_address (fp <: obj_addr)) + 16 > heap_size then
         AllocChain.chain_avoids_terminal g fp y heap_words
       else begin
         AllocChain.chain_avoids_unfold_step g fp y heap_words;
         AllocChain.chain_avoids_null g y (heap_words - 1)
       end
     end)
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let single_shape_intro (g: heap) (fp: U64.t) (k: nat)
  : Lemma (requires k < SC.n_lists /\
                    (fp <> 0UL ==>
                       U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                       U64.v fp % U64.v mword == 0 /\
                       k == SC.size_class (U64.v (wosize_of_object (fp <: obj_addr) g))) /\
                    well_formed_heap g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    FL.fl_exact g fp /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    (fp <> 0UL ==> read_word g (fp <: hp_addr) == 0UL) /\
                    FreeListShape.blue_link_fields_valid g /\
                    heap_objects_dense g /\
                    single_chain_objects_blue g fp /\
                    Seq.length (objects zero_addr g) > 0 /\
                    Mark.no_black_objects g /\
                    SweepInv.no_gray_objects g /\
                    Mark.no_pointer_to_blue g)
          (ensures GenInv.major_heap_shape g (FLs.fls_one k fp))
  = let fls = FLs.fls_one k fp in
    let head (i: nat) : Lemma (FLs.fls_head fls i == (if i = k then fp else 0UL))
      = FLs.fls_one_head k fp i
    in
    FStar.Classical.forall_intro head;
    FLs.fls_one_head k fp 0;
    // every list but k is empty
    let empty (i: nat)
      : Lemma (requires i < SC.n_lists /\ i <> k)
              (ensures AllocLemmas.fl_valid g (FLs.fls_head fls i) heap_words /\
                       FLs.chain_class g (FLs.fls_head fls i) i /\
                       AllocLemmas.fl_chain_terminates g (FLs.fls_head fls i) heap_words /\
                       FL.fl_sound g (FLs.fls_head fls i) /\
                       (forall (y: U64.t). AllocLemmas.chain_avoids g (FLs.fls_head fls i) y heap_words = true))
      = AllocLemmas.fl_valid_null g heap_words;
        AllocChain.fl_chain_terminates_terminal g 0UL heap_words;
        FStar.Classical.forall_intro (fun y -> AllocChain.chain_avoids_null g y heap_words);
        FStar.Classical.forall_intro (unreachable_from_null g)
    in
    // list k holds the block, of class k
    let one (_: unit)
      : Lemma (FLs.chain_class g fp k /\
               (forall (y: U64.t). FL.reachable_on_fl g fp y ==> y == fp))
      = if fp = 0UL then begin
          FStar.Classical.forall_intro (fun y -> AllocChain.chain_avoids_null g y heap_words);
          FStar.Classical.forall_intro (unreachable_from_null g)
        end
        else FStar.Classical.forall_intro (single_cell g fp)
    in
    one ();
    let per (i: nat)
      : Lemma (requires i < SC.n_lists)
              (ensures AllocLemmas.fl_valid g (FLs.fls_head fls i) heap_words /\
                       FLs.chain_class g (FLs.fls_head fls i) i /\
                       AllocLemmas.fl_chain_terminates g (FLs.fls_head fls i) heap_words /\
                       FL.fl_sound g (FLs.fls_head fls i))
      = if i = k then () else empty i
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires per);
    FLs.fls_valid_intro g fls;
    FLs.fls_terminates_intro g fls;
    // exact: a free block with a link is the block, on its class's list
    let complete (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g) /\ is_blue x g /\
               U64.v (wosize_of_object x g) >= 1 ==>
               FL.reachable_on_fl g (FLs.fls_head fls (SC.size_class (U64.v (wosize_of_object x g)))) x)
      = if Seq.mem x (objects zero_addr g) && is_blue x g &&
           U64.v (wosize_of_object x g) >= 1 then
          FL.fl_complete_elim g fp x
    in
    FStar.Classical.forall_intro complete;
    assert (FLs.fls_exact g fls);
    GenInv.free_list_exact_iff g fls;
    // the heads are null or pointers
    FreeListShape.fls_pointer_or_zero_iff fls;
    assert (FreeListShape.fls_pointer_or_zero fls);
    // no live object is on a list
    let live (obj: obj_addr)
      : Lemma (Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g) ==>
               FLs.fls_avoids g fls (obj <: U64.t))
      = FLs.fls_avoids_iff g fls (obj <: U64.t);
        let each (i: nat)
          : Lemma (i < SC.n_lists /\ Seq.mem obj (objects zero_addr g) /\ ~(is_blue obj g) ==>
                   AllocLemmas.chain_avoids g (FLs.fls_head fls i) (obj <: U64.t) heap_words = true)
          = if i < SC.n_lists && i <> k then empty i
        in
        FStar.Classical.forall_intro each
    in
    FStar.Classical.forall_intro live;
    reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue g fls);
    assert (Promote.chain_objects_blue g fls);
    FreeListShape.fls_pointer_or_zero_implies_fp_valid fls g;
    GenInv.major_heap_shape_intro g fls
#pop-options
