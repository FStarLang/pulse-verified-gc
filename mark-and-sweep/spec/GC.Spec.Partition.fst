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
module Alloc = GC.Spec.Allocator
module ACore = GC.Spec.Allocator.Lemmas.Core

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

/// The same, for the allocated class.
let white_whsize_cons (g: heap) (x: obj_addr) (s: seq obj_addr)
  : Lemma (white_whsize g (Seq.cons x s)
           == (if is_white x g then whsize g x else 0) + white_whsize g s)
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
/// The completeness hypothesis is `GC.Spec.FreeList.fl_complete` itself,
/// which says every blue object that can hold a link is on the chain -- and
/// that is exactly the condition under which the orphan class is empty.
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

/// ---------------------------------------------------------------------------
/// Allocation accounting: the words the block loses are the words the object
/// gains
/// ---------------------------------------------------------------------------
///
/// The partition above is bookkeeping -- it is true of any heap, so on its own
/// it forbids nothing. This is the statement with teeth, and the reason it has
/// any is that the REQUESTED size appears in it.
///
/// Plain conservation would not do. "The total is unchanged" is satisfied by
/// the pre-fix allocator too: at a one-word leftover it handed the whole block
/// over, so a blue block of whsize `bwz + 1` became a white block of whsize
/// `bwz + 1` and nothing was lost. The defect is invisible to a law that only
/// counts words. It becomes visible the moment the law says how many words the
/// caller asked for.
///
/// So: the source block keeps its address and shrinks by exactly `wz + 1`
/// words, and exactly `wz + 1` words appear at the right-justified header.
/// The pre-fix allocator fails this -- it left `bwz` in the header at `hd` and
/// wrote nothing at `hd + leftover * 8` -- which is issue #19 stated as
/// arithmetic.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
let alloc_from_block_accounting
  (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma
    (requires (let hd = hd_address obj in
               let bwz = U64.v (getWosize (read_word g hd)) in
               bwz - wz >= 1 /\ wz < pow2 54 /\ bwz - wz - 1 < pow2 54 /\
               U64.v hd + (bwz - wz) * 8 < heap_size))
    (ensures (let hd = hd_address obj in
              let bwz = U64.v (getWosize (read_word g hd)) in
              let leftover = bwz - wz in
              let g' = fst (Alloc.alloc_from_block g obj wz next) in
              let ah : hp_addr = U64.uint_to_t (U64.v hd + leftover * 8) in
              // the block at `hd` is still a block, and it is exactly `wz + 1`
              // words smaller than it was
              (U64.v (getWosize (read_word g' hd)) + 1) + (wz + 1) == bwz + 1 /\
              // and exactly those `wz + 1` words are the allocated object
              U64.v (getWosize (read_word g' ah)) == wz /\
              // Sizes alone would be satisfied by an allocator that carved the
              // block correctly and coloured everything free, so the classes
              // have to be pinned too: the words leave the free class and
              // arrive in the allocated one.
              getColor (read_word g' ah) == White /\
              getColor (read_word g' hd) == Blue))
  = let hd = hd_address obj in
    let bwz = U64.v (getWosize (read_word g hd)) in
    let leftover = bwz - wz in
    Alloc.alloc_from_block_split_normal g obj wz next;
    let rhdr = Alloc.make_header (U64.uint_to_t (leftover - 1)) Alloc.blue_bits 0UL in
    let g1 = write_word g hd rhdr in
    let ahn = U64.v hd + leftover * 8 in
    let ah : hp_addr = U64.uint_to_t ahn in
    let ahdr = Alloc.make_header (U64.uint_to_t wz) Alloc.white_bits 0UL in
    let g2 = write_word g1 ah ahdr in
    // the allocated header: written last, so read it back directly
    read_write_same g1 ah ahdr;
    ACore.make_header_getWosize (U64.uint_to_t wz) Alloc.white_bits 0UL;
    // the remainder header: written first, and `ah <> hd` because leftover >= 1
    read_write_different g1 ah hd ahdr;
    read_write_same g hd rhdr;
    ACore.make_header_getWosize (U64.uint_to_t (leftover - 1)) Alloc.blue_bits 0UL;
    // colours: the header bits decode to the classes
    ACore.make_header_getColor (U64.uint_to_t wz) Alloc.white_bits 0UL;
    getColor_raw ahdr;
    ACore.make_header_getColor (U64.uint_to_t (leftover - 1)) Alloc.blue_bits 0UL;
    getColor_raw rhdr
#pop-options

/// The exact-fit arm. The block becomes the object outright: no remainder, no
/// fragment, and the object declares exactly what was asked for. Stated
/// separately because there is no leftover to account for -- the whole block
/// is the `wz + 1` words.
///
/// The pre-fix allocator happened to get this arm right, because at
/// `leftover = 0` the block size and the requested size coincide. It is the
/// `leftover = 1` arm above where the two part company.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let alloc_from_block_accounting_exact
  (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma
    (requires (let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
               bwz == wz /\ wz < pow2 54))
    (ensures (let hd = hd_address obj in
              let g' = fst (Alloc.alloc_from_block g obj wz next) in
              U64.v (getWosize (read_word g' hd)) == wz))
  = let hd = hd_address obj in
    Alloc.alloc_from_block_exact g obj wz next;
    let ahdr = Alloc.make_header (U64.uint_to_t wz) Alloc.white_bits 0UL in
    read_write_same g hd ahdr;
    ACore.make_header_getWosize (U64.uint_to_t wz) Alloc.white_bits 0UL
#pop-options

/// Both arms together: however the block is carved, the object the allocator
/// hands back declares exactly the number of fields that were requested.
///
/// This is the whole of issue #19 as a single statement. It is not a counting
/// law -- counting cannot see the defect, because the pre-fix allocator lost no
/// words -- it is a law relating what was asked for to what was produced.
let alloc_from_block_gives_requested_size
  (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma
    (requires (let hd = hd_address obj in
               let bwz = U64.v (getWosize (read_word g hd)) in
               bwz >= wz /\ wz >= 1 /\ wz < pow2 54 /\ bwz - wz - 1 < pow2 54 /\
               U64.v hd + (bwz - wz) * 8 < heap_size))
    (ensures (let hd = hd_address obj in
              let bwz = U64.v (getWosize (read_word g hd)) in
              let g' = fst (Alloc.alloc_from_block g obj wz next) in
              let ah : hp_addr = U64.uint_to_t (U64.v hd + (bwz - wz) * 8) in
              U64.v (getWosize (read_word g' ah)) == wz))
  = let hd = hd_address obj in
    let bwz = U64.v (getWosize (read_word g hd)) in
    if bwz = wz then alloc_from_block_accounting_exact g obj wz next
    else alloc_from_block_accounting g obj wz next

/// ---------------------------------------------------------------------------
/// The sum form: how much the allocated class grows
/// ---------------------------------------------------------------------------

/// Two heaps that agree on every word from `start` upward have the same walk
/// from `start`, and the same allocated total along it.
///
/// Walk-equality and sum-equality are proved together on purpose. Separating
/// them would mean two inductions over the same recursion, and the second
/// would still need the first at every step: a shared header gives the same
/// wosize (so the same next position) AND the same colour (so the same
/// contribution).
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let rec walk_white_agree (g g': heap) (start: hp_addr)
  : Lemma
    (requires Seq.length g == heap_size /\ Seq.length g' == heap_size /\
              (forall (a: hp_addr). U64.v a >= U64.v start ==>
                 read_word g a == read_word g' a))
    (ensures objects start g == objects start g' /\
             white_whsize g (objects start g) == white_whsize g' (objects start g'))
    (decreases (heap_size - U64.v start))
  = if U64.v start + 8 >= heap_size then begin
      assert (objects start g == Seq.empty);
      assert (objects start g' == Seq.empty)
    end
    else begin
      assert (read_word g start == read_word g' start);
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size || next >= pow2 64 then begin
        assert (objects start g == Seq.empty);
        assert (objects start g' == Seq.empty)
      end
      else begin
        f_address_spec start;
        hd_f_roundtrip start;
        let o : obj_addr = f_address start in
        // same header at `start`, so same size and same colour
        wosize_of_object_spec o g;
        wosize_of_object_spec o g';
        assert (whsize g o == whsize g' o);
        color_of_object_spec o g;
        color_of_object_spec o g';
        is_white_iff o g;
        is_white_iff o g';
        assert (is_white o g == is_white o g');
        if next >= heap_size then begin
          assert (objects start g == Seq.cons o Seq.empty);
          assert (objects start g' == Seq.cons o Seq.empty);
          white_whsize_cons g o Seq.empty;
          white_whsize_cons g' o Seq.empty
        end
        else begin
          aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
          let nx : hp_addr = mk_hp_addr next in
          walk_white_agree g g' nx;
          assert (objects start g == Seq.cons o (objects nx g));
          assert (objects start g' == Seq.cons o (objects nx g'));
          white_whsize_cons g o (objects nx g);
          white_whsize_cons g' o (objects nx g')
        end
      end
    end
#pop-options

/// **The allocated class grows by exactly the words requested.**
///
/// This is the sum form of `alloc_from_block_accounting`, over the walk that
/// starts at the block being carved. Everything below the block is untouched,
/// so the whole-heap statement differs from this one only by a prefix that
/// both sides share -- splitting the walk at an arbitrary address is the one
/// piece of machinery the repository does not have, and it is the only reason
/// this is stated from `hd` rather than from `zero_addr`.
///
/// `~(is_white obj g)` holds because the block comes off the free list, and it
/// is needed: if the source block were already allocated the arithmetic would
/// count it twice.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let alloc_from_block_white_grows
  (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t)
  : Lemma
    (requires (let hd = hd_address obj in
               let bwz = U64.v (getWosize (read_word g hd)) in
               Seq.length g == heap_size /\
               bwz - wz >= 1 /\ wz >= 1 /\ wz < pow2 54 /\ bwz - wz - 1 < pow2 54 /\
               ~(is_white obj g) /\
               U64.v hd + (bwz + 1) * 8 < heap_size))
    (ensures (let hd = hd_address obj in
              let g' = fst (Alloc.alloc_from_block g obj wz next) in
              white_whsize g' (objects hd g')
                == white_whsize g (objects hd g) + (wz + 1)))
  = let hd = hd_address obj in
    let bwz = U64.v (getWosize (read_word g hd)) in
    let leftover = bwz - wz in
    let g' = fst (Alloc.alloc_from_block g obj wz next) in
    let ahn = U64.v hd + leftover * 8 in
    let ah : hp_addr = U64.uint_to_t ahn in
    let aftn = U64.v hd + (bwz + 1) * 8 in
    let aft : hp_addr = mk_hp_addr aftn in
    // sizes and colours of the two rewritten headers
    alloc_from_block_accounting g obj wz next;
    // the walk above the block is untouched
    let frame (a: hp_addr) : Lemma
      (requires U64.v a >= aftn)
      (ensures read_word g' a == read_word g a)
      = Alloc.alloc_from_block_read_outside g obj wz next a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires frame);
    walk_white_agree g g' aft;
    // the block's own two steps in g', and its one step in g
    // `objects` emits `f_address hd`, and the goal is phrased with `obj`:
    // this is the direction that identifies them.
    f_hd_roundtrip obj;
    hd_address_spec obj;
    f_address_spec hd; hd_f_roundtrip hd;
    f_address_spec ah; hd_f_roundtrip ah;
    let ao : obj_addr = f_address ah in
    wosize_of_object_spec obj g; wosize_of_object_spec obj g';
    wosize_of_object_spec ao g';
    color_of_object_spec obj g'; color_of_object_spec ao g';
    is_white_iff obj g'; is_white_iff ao g';
    // the arithmetic that makes the two walks meet again at `aft`
    assert (ahn + (wz + 1) * 8 == aftn);
    // one step in g: the block spans to `aft`
    assert (objects hd g == Seq.cons obj (objects aft g));
    // two steps in g': the remainder at `hd`, then the object at `ah`
    assert (objects ah g' == Seq.cons ao (objects aft g'));
    assert (objects hd g' == Seq.cons obj (objects ah g'));
    white_whsize_cons g obj (objects aft g);
    white_whsize_cons g' ao (objects aft g');
    white_whsize_cons g' obj (objects ah g')
#pop-options
