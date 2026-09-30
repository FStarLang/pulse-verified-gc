(*
   The heap, counted.

   Right-justified allocation can leave a one-word remainder that is free but
   cannot be linked: a block of wosize 0 has no field to hold a free-list
   pointer (`GC.Spec.Allocator.alloc_from_block`, the `leftover = 1` arm).
   `GC.Spec.FreeList.linkable_heap` used to assert that no such object exists.
   It has since been deleted: the `wosize >= 1` bound it really supplied now
   lives in `fl_sound`, where it is true, because it is a property of chain
   cells rather than of every object.

   This module states the true version. Every object of the walk falls into
   exactly one class, and the classes sum to the space the walk covers:

       total = allocated + linkable-free + fragments + in-flight

   so a fragment is not lost, it is *counted*. The word the allocator cannot
   link is still in the total; it has merely moved out of the free-list class.

   Counting is in whsize -- header plus fields, stock OCaml's Whsize_wosize
   (runtime/caml/mlvalues.h:165) -- and that is forced, not stylistic. Splitting
   one block into two preserves the whsize sum but *drops* the wosize sum by
   one, because a second header appears. A conservation law in wosize would be
   false of the very operation we want to reason about.
*)
module GC.Spec.Partition

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header

module U64 = FStar.UInt64
module WE  = GC.Spec.WalkEnd
module IndDesc = FStar.IndefiniteDescription
module FL  = GC.Spec.FreeList

/// Machine words an object occupies: its fields plus its header.
let whsize (g: heap) (x: obj_addr) : GTot nat = 1 + U64.v (wosize_of_object x g)

/// Blue with room for a link word, i.e. able to be a free-list cell.
/// `GC.Spec.FreeList.Descending.fl_cell` demands exactly this wosize bound.
let is_cellish (g: heap) (x: obj_addr) : GTot bool =
  is_blue x g && U64.v (wosize_of_object x g) >= 1

/// Blue with no field at all: free space that cannot carry a link.
let is_fragment (g: heap) (x: obj_addr) : GTot bool =
  is_blue x g && U64.v (wosize_of_object x g) = 0

/// Neither allocated nor free: gray or black, i.e. mid-collection.
let is_inflight (g: heap) (x: obj_addr) : GTot bool =
  not (is_white x g) && not (is_blue x g)

let rec total_whsize (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else whsize g (Seq.head objs) + total_whsize g (Seq.tail objs)

let rec white_whsize (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else (if is_white (Seq.head objs) g then whsize g (Seq.head objs) else 0)
         + white_whsize g (Seq.tail objs)

let rec cell_whsize (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else (if is_cellish g (Seq.head objs) then whsize g (Seq.head objs) else 0)
         + cell_whsize g (Seq.tail objs)

let rec frag_whsize (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else (if is_fragment g (Seq.head objs) then whsize g (Seq.head objs) else 0)
         + frag_whsize g (Seq.tail objs)

let rec inflight_whsize (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else (if is_inflight g (Seq.head objs) then whsize g (Seq.head objs) else 0)
         + inflight_whsize g (Seq.tail objs)

/// The four classes are mutually exclusive and exhaustive, so every object is
/// counted exactly once. Unconditional: it holds mid-collection too, when gray
/// and black objects are present.
/// `is_white`, `is_cellish`, `is_fragment` and `is_inflight` are mutually
/// exclusive and cover every object: the first splits on colour, the middle
/// two split the blue case on `wosize = 0`, and the last is everything that is
/// neither white nor blue.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec partition_exhaustive (g: heap) (objs: seq obj_addr)
  : Lemma
    (ensures total_whsize g objs ==
             white_whsize g objs + cell_whsize g objs
             + frag_whsize g objs + inflight_whsize g objs)
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let x = Seq.head objs in
      let tl = Seq.tail objs in
      // Unfold each sum one step, so the goal is about the head plus the tails.
      assert (total_whsize g objs == whsize g x + total_whsize g tl);
      assert (white_whsize g objs
              == (if is_white x g then whsize g x else 0) + white_whsize g tl);
      assert (cell_whsize g objs
              == (if is_cellish g x then whsize g x else 0) + cell_whsize g tl);
      assert (frag_whsize g objs
              == (if is_fragment g x then whsize g x else 0) + frag_whsize g tl);
      assert (inflight_whsize g objs
              == (if is_inflight g x then whsize g x else 0) + inflight_whsize g tl);
      // Exactly one of the four holds of x, so the head contributes its whsize
      // to exactly one of the four sums. At-least-one is not enough; the
      // solver also needs at-most-one, which is what this states numerically.
      // `is_white` and `is_blue` are abstract in GC.Spec.Object.fsti, so the
      // solver cannot see they are exclusive. Route through the colour, which
      // is a four-constructor datatype it can case-split.
      is_white_iff x g;
      is_blue_iff x g;
      assert (color_of_object x g = White \/ color_of_object x g = Gray
              \/ color_of_object x g = Blue \/ color_of_object x g = Black);
      assert ((if is_white x g then whsize g x else 0)
              + (if is_cellish g x then whsize g x else 0)
              + (if is_fragment g x then whsize g x else 0)
              + (if is_inflight g x then whsize g x else 0)
              == whsize g x);
      partition_exhaustive g tl
    end
#pop-options

/// Membership survives taking the tail, so an "all objects are ..." hypothesis
/// carries through the induction below.
let mem_tail_implies_mem (#a: eqtype) (objs: Seq.seq a) (x: a)
  : Lemma (requires Seq.length objs > 0 /\ Seq.mem x (Seq.tail objs))
          (ensures Seq.mem x objs)
  = Seq.cons_head_tail objs;
    mem_cons_lemma x (Seq.head objs) (Seq.tail objs)

/// After a sweep every object is allocated or free, so nothing is in flight.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec inflight_zero (g: heap) (objs: seq obj_addr)
  : Lemma
    (requires forall (x: obj_addr). Seq.mem x objs ==> (is_white x g \/ is_blue x g))
    (ensures inflight_whsize g objs == 0)
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let x = Seq.head objs in
      let tl = Seq.tail objs in
      Seq.cons_head_tail objs;
      mem_cons_lemma x x tl;
      assert (Seq.mem x objs);
      let aux (y: obj_addr)
        : Lemma (requires Seq.mem y tl) (ensures is_white y g \/ is_blue y g)
        = mem_tail_implies_mem objs y
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      inflight_zero g tl
    end
#pop-options

/// THE WEAK PARTITION, over the objects of a walk.
///
/// Every word the walk covers is allocated, on a free block big enough to be a
/// cell, or in a fragment -- and each is counted once. The fragment term is
/// what `linkable_heap` used to deny the existence of; here it is a summand.
let partition_swept (g: heap) (objs: seq obj_addr)
  : Lemma
    (requires forall (x: obj_addr). Seq.mem x objs ==> (is_white x g \/ is_blue x g))
    (ensures total_whsize g objs ==
             white_whsize g objs + cell_whsize g objs + frag_whsize g objs)
  = partition_exhaustive g objs;
    inflight_zero g objs

/// `total_whsize` on a cons, so the walk induction can step.
let total_whsize_cons (g: heap) (x: obj_addr) (s: seq obj_addr)
  : Lemma (total_whsize g (Seq.cons x s) == whsize g x + total_whsize g s)
  = Seq.head_cons x s; Seq.lemma_tl x s

/// THE TILING. The classes above sum to the space the walk actually covers:
/// stepping block by block from `start` lands exactly at `walk_end`, with no
/// gap and nothing counted twice. `objects` and `walk_end` share a recursion,
/// so this is that shared structure read as arithmetic.
///
/// A wosize-0 fragment is an ordinary step here -- `objects` bounds wosize
/// below by nothing and advances one word -- which is why the fragment is
/// inside the total rather than falling out of it.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let rec walk_is_tiled (g: heap) (start: hp_addr)
  : Lemma
    (requires Seq.length g == heap_size)
    (ensures U64.v start + total_whsize g (objects start g) * U64.v mword
             == WE.walk_end g start)
    (decreases (heap_size - U64.v start))
  = if U64.v start + 8 >= heap_size then begin
      assert (objects start g == Seq.empty);
      assert (WE.walk_end g start == U64.v start)
    end
    else begin
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size || next >= pow2 64 then begin
        assert (objects start g == Seq.empty);
        assert (WE.walk_end g start == U64.v start)
      end
      else begin
        f_address_spec start;
        hd_f_roundtrip start;
        let o : obj_addr = f_address start in
        wosize_of_object_spec o g;
        assert (whsize g o == U64.v wz + 1);
        if next >= heap_size then begin
          assert (objects start g == Seq.cons o Seq.empty);
          total_whsize_cons g o Seq.empty;
          assert (WE.walk_end g start == next)
        end
        else begin
          aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
          let nx : hp_addr = mk_hp_addr next in
          assert (U64.v nx == next);
          assert (objects start g == Seq.cons o (objects nx g));
          total_whsize_cons g o (objects nx g);
          assert (WE.walk_end g start == WE.walk_end g nx);
          walk_is_tiled g nx
        end
      end
    end
#pop-options

/// THE WEAK PARTITION THEOREM.
///
/// Walking the whole heap: allocated words, plus free words on blocks large
/// enough to be cells, plus fragment words, is exactly the span the walk
/// covers. Nothing is lost between the classes and nothing is counted twice.
///
/// This is the statement `GC.Spec.FreeList.linkable_heap` was reaching for and
/// got wrong. It said no object has wosize 0 -- which right-justified
/// allocation falsified -- where this says how many words are in such objects,
/// which is a number, and is correct whatever that number is.
let heap_partition_swept (g: heap)
  : Lemma
    (requires Seq.length g == heap_size /\
              (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                 (is_white x g \/ is_blue x g)))
    (ensures
      (let objs = objects zero_addr g in
       U64.v zero_addr
       + (white_whsize g objs + cell_whsize g objs + frag_whsize g objs)
         * U64.v mword
       == WE.walk_end g zero_addr))
  = partition_swept g (objects zero_addr g);
    walk_is_tiled g zero_addr

/// ---------------------------------------------------------------------------
/// The strong partition: is the free space actually reachable?
/// ---------------------------------------------------------------------------
///
/// `is_cellish` says a block is blue and big enough to hold a link. It does
/// not say the block is on the chain. Splitting it names the difference:
///
///   onchain -- blue, wosize >= 1, and reachable from `fp`; allocatable
///   orphan  -- blue, wosize >= 1, and NOT reachable; free but unreachable
///
/// `reachable_on_fl` is a `prop` (an existential over chain depth), so it
/// cannot drive a boolean sum directly. Classical decidability is sound here
/// and the file is ghost throughout; the repo already uses
/// `FStar.IndefiniteDescription` this way elsewhere.

let on_chain (g: heap) (fp: U64.t) (x: obj_addr) : GTot bool =
  IndDesc.strong_excluded_middle (FL.reachable_on_fl g fp x)

let is_onchain (g: heap) (fp: U64.t) (x: obj_addr) : GTot bool =
  is_cellish g x && on_chain g fp x

let is_orphan (g: heap) (fp: U64.t) (x: obj_addr) : GTot bool =
  is_cellish g x && not (on_chain g fp x)

let rec onchain_whsize (g: heap) (fp: U64.t) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else (if is_onchain g fp (Seq.head objs) then whsize g (Seq.head objs) else 0)
         + onchain_whsize g fp (Seq.tail objs)

let rec orphan_whsize (g: heap) (fp: U64.t) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else (if is_orphan g fp (Seq.head objs) then whsize g (Seq.head objs) else 0)
         + orphan_whsize g fp (Seq.tail objs)

/// The cellish class splits exactly in two.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec cell_splits (g: heap) (fp: U64.t) (objs: seq obj_addr)
  : Lemma
    (ensures cell_whsize g objs
             == onchain_whsize g fp objs + orphan_whsize g fp objs)
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else cell_splits g fp (Seq.tail objs)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec orphan_zero (g: heap) (fp: U64.t) (objs: seq obj_addr)
  : Lemma
    (requires forall (o: obj_addr). Seq.mem o objs /\ is_cellish g o ==>
                FL.reachable_on_fl g fp o)
    (ensures orphan_whsize g fp objs == 0)
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let x = Seq.head objs in
      let tl = Seq.tail objs in
      Seq.cons_head_tail objs;
      mem_cons_lemma x x tl;
      assert (Seq.mem x objs);
      let aux (y: obj_addr)
        : Lemma (requires Seq.mem y tl /\ is_cellish g y)
                (ensures FL.reachable_on_fl g fp y)
        = mem_tail_implies_mem objs y
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      orphan_zero g fp tl
    end
#pop-options

/// THE STRONG PARTITION THEOREM.
///
/// Allocated words, plus free words that are actually reachable on the free
/// list, plus fragment words, is exactly the heap the walk covers. There is no
/// fourth term: nothing is free-but-unreachable.
///
/// The fragment term is the price of right-justification, stated rather than
/// denied, and it is the only class that is free without being allocatable.
let heap_partition_strong (g: heap) (fp: U64.t)
  : Lemma
    (requires Seq.length g == heap_size /\
              (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                 (is_white x g \/ is_blue x g)) /\
              FL.fl_complete g fp)
    (ensures
      (let objs = objects zero_addr g in
       U64.v zero_addr
       + (white_whsize g objs + onchain_whsize g fp objs + frag_whsize g objs)
         * U64.v mword
       == WE.walk_end g zero_addr))
  = let objs = objects zero_addr g in
    partition_swept g objs;
    cell_splits g fp objs;
    orphan_zero g fp objs;
    walk_is_tiled g zero_addr
