/// ---------------------------------------------------------------------------
/// GC.Spec.Partition.Lists - the free blocks, counted list by list
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Partition` counts the words of blue blocks that can carry a link
/// (`cell_whsize`) and those reachable from one free-list head
/// (`onchain_whsize`).  With the size lists, each such block is on exactly the
/// list of its class, so the words on the lists, summed list by list, are the
/// cell words.  A block on two lists would be counted twice, so the equation
/// also says the lists are disjoint.

module GC.Spec.Partition.Lists

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass
open GC.Spec.FreeLists

module U64 = FStar.UInt64
module Part = GC.Spec.Partition

/// The words of the blocks on lists `i ..`, list by list.
let rec onchain_whsize_lists (g: heap) (fls: fl_state) (objs: seq obj_addr) (i: nat)
  : GTot nat (decreases (n_lists - i))
  = if i >= n_lists then 0
    else Part.onchain_whsize g (fls_head fls i) objs + onchain_whsize_lists g fls objs (i + 1)

/// A cell is on exactly the list of its class.
let on_own_list (g: heap) (fls: fl_state) (x: obj_addr) : prop =
  Part.is_cellish g x ==>
  (forall (i: nat). i < n_lists ==>
     (Part.on_chain g (fls_head fls i) x <==> size_class (U64.v (wosize_of_object x g)) == i))

/// One block's words, over the lists `i ..`.
let rec one_block (g: heap) (fls: fl_state) (x: obj_addr) (i: nat)
  : GTot nat (decreases (n_lists - i))
  = if i >= n_lists then 0
    else (if Part.is_onchain g (fls_head fls i) x then whsize g x else 0) +
         one_block g fls x (i + 1)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec one_block_eq (g: heap) (fls: fl_state) (x: obj_addr) (i: nat)
  : Lemma (requires on_own_list g fls x)
          (ensures one_block g fls x i ==
                   (if Part.is_cellish g x &&
                       size_class (U64.v (wosize_of_object x g)) >= i
                    then whsize g x else 0))
          (decreases (n_lists - i))
  = size_class_lt (U64.v (wosize_of_object x g));
    if i >= n_lists then ()
    else one_block_eq g fls x (i + 1)

let rec lists_cons (g: heap) (fls: fl_state) (objs: seq obj_addr) (i: nat)
  : Lemma (requires Seq.length objs > 0)
          (ensures onchain_whsize_lists g fls objs i ==
                   one_block g fls (Seq.head objs) i +
                   onchain_whsize_lists g fls (Seq.tail objs) i)
          (decreases (n_lists - i))
  = if i >= n_lists then () else lists_cons g fls objs (i + 1)

let rec onchain_lists_cell (g: heap) (fls: fl_state) (objs: seq obj_addr)
  : Lemma (requires forall (x: obj_addr). Seq.mem x objs ==> on_own_list g fls x)
          (ensures onchain_whsize_lists g fls objs 0 == Part.cell_whsize g objs)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then begin
      let rec zero (i: nat)
        : Lemma (ensures onchain_whsize_lists g fls objs i == 0) (decreases (n_lists - i))
        = if i >= n_lists then () else zero (i + 1)
      in
      zero 0
    end
    else begin
      let x = Seq.head objs in
      let tl = Seq.tail objs in
      Seq.cons_head_tail objs;
      mem_cons_lemma x x tl;
      let sub (y: obj_addr) : Lemma (Seq.mem y tl ==> Seq.mem y objs)
        = mem_cons_lemma y x tl
      in
      FStar.Classical.forall_intro sub;
      lists_cons g fls objs 0;
      one_block_eq g fls x 0;
      onchain_lists_cell g fls tl
    end
#pop-options
