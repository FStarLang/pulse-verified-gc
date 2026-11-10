/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Partition - no memory lost, as a word count
/// ---------------------------------------------------------------------------
///
/// The pages form of `GC.Impl.Correct.heap_partitioned`.  Every block of the
/// walk is given exactly one kind (`kind_of`): live, a listed free block (a
/// free slot, or a free block of a swept run of at least `lg_min` words),
/// or one of the bounded kinds of waste of `block_class`.  The words of the
/// blocks of each kind, summed over the walk, add up to the walk's end, and
/// the walk reaches the end of the heap up to a last word too short for a
/// header.
///
/// The proof is the old one (`GC.Spec.Partition.partition_exhaustive` and
/// `walk_is_tiled`) with more classes: the sums split the walk's total by
/// kind, and the leftover kind `KOther` sums to zero when every block is
/// classified (`block_class`, proved in `GC.Spec.Pages.GcCorrect`).

module GC.Spec.Pages.Partition

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module ST = GC.Spec.Pages.SweepTags
module WE = GC.Spec.WalkEnd
module ID = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The kinds of block
/// ---------------------------------------------------------------------------

let free_slot_at (g: heap) (st: pstate) (b: nat) : prop =
  exists (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat).
    (entry st.pm i).kind == Pool c /\ k < n_slots c /\ b == slot_base i c k /\ slot_free g i c k

let filler_kind (g: heap) (st: pstate) (b: nat) : prop =
  exists (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat).
    (entry st.pm i).kind == Pool c /\ k < n_slots c /\ ST.filler_at g i c k b

let pool_tail_at (st: pstate) (b: nat) : prop =
  exists (i: nat{i < n_pages}) (c: nat{c < n_cls}).
    (entry st.pm i).kind == Pool c /\ tail_words c > 0 /\ b == slots_end i c

let free_page_at (st: pstate) (b: nat) : prop =
  exists (i: nat{i < n_pages}). (entry st.pm i).kind == Free /\ b == page_base i

/// What a block of the swept heap is.  A free block is one of:
///   - a free slot of a pool page (listed, by (b));
///   - a filler: the rest of a used slot after its object, `cls c - w`
///     words for an object of `w` words;
///   - a pool page's tail, `tail_words c` words;
///   - a `Free` page;
///   - a free block of a swept run (listed when of at least `lg_min`
///     words, by (b));
///   - the heap's tail past the last page.
let block_class (g: heap) (st: pstate) (y: obj_addr) : prop =
  let b = U64.v y - 8 in
  is_white y g \/
  (is_blue y g /\
   (free_slot_at g st b \/ filler_kind g st b \/ pool_tail_at st b \/ free_page_at st b \/
    in_swept_run st.pm b \/ b == pages_end))

type kind =
  | KLive       (* white: allocated *)
  | KSlot       (* a free slot: on its page's list *)
  | KListed     (* a free block of a swept run of at least lg_min words: on the large lists *)
  | KFiller     (* the rest of a used slot *)
  | KTail       (* a pool page's tail *)
  | KFreePage   (* a Free page *)
  | KRunWaste   (* a free block of a swept run of fewer than lg_min words *)
  | KHeapTail   (* the heap's tail past the last page *)
  | KOther      (* none of these *)

let sem (p: prop) : GTot bool = ID.strong_excluded_middle p

/// The kind of a block, the first that applies.
let kind_of (g: heap) (st: pstate) (y: obj_addr) : GTot kind =
  let b = U64.v y - 8 in
  if is_white y g then KLive
  else if not (is_blue y g) then KOther
  else if sem (free_slot_at g st b) then KSlot
  else if sem (large_listable g st.pm y) then KListed
  else if sem (filler_kind g st b) then KFiller
  else if sem (pool_tail_at st b) then KTail
  else if sem (free_page_at st b) then KFreePage
  else if sem (in_swept_run st.pm b) then KRunWaste
  else if b = pages_end then KHeapTail
  else KOther

/// A classified block has a kind other than `KOther`.
let kind_of_classified (g: heap) (st: pstate) (y: obj_addr)
  : Lemma (requires block_class g st y) (ensures kind_of g st y <> KOther)
  = hd_address_spec y

/// ---------------------------------------------------------------------------
/// The sums
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec total_whsize (g: heap) (objs: Seq.seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else whsize g (Seq.head objs) + total_whsize g (Seq.tail objs)

/// The words of the blocks of kind `k`.
let rec kind_whsize (g: heap) (st: pstate) (k: kind) (objs: Seq.seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else (if kind_of g st (Seq.head objs) = k then whsize g (Seq.head objs) else 0)
         + kind_whsize g st k (Seq.tail objs)
#pop-options

let classes_whsize (g: heap) (st: pstate) (objs: Seq.seq obj_addr) : GTot nat =
  kind_whsize g st KLive objs + kind_whsize g st KSlot objs + kind_whsize g st KListed objs +
  kind_whsize g st KFiller objs + kind_whsize g st KTail objs + kind_whsize g st KFreePage objs +
  kind_whsize g st KRunWaste objs + kind_whsize g st KHeapTail objs

/// Every block is counted once, under its kind.
#push-options "--fuel 1"
let rec kinds_exhaustive (g: heap) (st: pstate) (objs: Seq.seq obj_addr)
  : Lemma (ensures total_whsize g objs == classes_whsize g st objs + kind_whsize g st KOther objs)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else kinds_exhaustive g st (Seq.tail objs)
#pop-options

let mem_tail (objs: Seq.seq obj_addr) (x: obj_addr)
  : Lemma (requires Seq.length objs > 0 /\ Seq.mem x (Seq.tail objs)) (ensures Seq.mem x objs)
  = Seq.cons_head_tail objs;
    mem_cons_lemma x (Seq.head objs) (Seq.tail objs)

/// No block is of no kind.
#push-options "--fuel 1"
let rec other_zero (g: heap) (st: pstate) (objs: Seq.seq obj_addr)
  : Lemma (requires forall (y: obj_addr). Seq.mem y objs ==> block_class g st y)
          (ensures kind_whsize g st KOther objs == 0)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let tl = Seq.tail objs in
      Seq.cons_head_tail objs;
      mem_cons_lemma (Seq.head objs) (Seq.head objs) tl;
      kind_of_classified g st (Seq.head objs);
      FStar.Classical.forall_intro (FStar.Classical.move_requires (mem_tail objs));
      other_zero g st tl
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The tiling
/// ---------------------------------------------------------------------------

let total_step (g: heap) (objs: Seq.seq obj_addr)
  : Lemma (requires Seq.length objs > 0)
          (ensures total_whsize g objs == whsize g (Seq.head objs) + total_whsize g (Seq.tail objs))
  = assert_norm (total_whsize g objs ==
      (if Seq.length objs = 0 then 0
       else whsize g (Seq.head objs) + total_whsize g (Seq.tail objs)))

/// `s + (w + t) * 8` split, in a context of its own.
let add_mul8 (s w t: nat) : Lemma (s + (w + t) * 8 == (s + w * 8) + t * 8) = ()

/// The blocks of the walk from `start` cover exactly up to its end
/// (`GC.Spec.Partition.walk_is_tiled`, through `WE.walk_end_step`).
#push-options "--fuel 1"
let rec walk_tiled (g: heap) (start: hp_addr)
  : Lemma (ensures U64.v start + total_whsize g (objects start g) * 8 == WE.walk_end g start)
          (decreases (heap_size - U64.v start))
  = if Seq.length (objects start g) = 0 then begin
      WE.walk_end_empty g start;
      assert (total_whsize g (objects start g) == 0)
    end
    else begin
      WE.walk_end_step g start;
      WE.walk_head g start;
      let o = f_address start in
      hd_f_roundtrip start;
      wosize_of_object_spec o g;
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      assert (whsize g o == U64.v wz + 1);
      if next >= heap_size then begin
        Seq.lemma_tl o (Seq.empty #obj_addr);
        assert (Seq.head (objects start g) == o);
        assert (total_whsize g (Seq.tail (objects start g)) == 0);
        assert (total_whsize g (objects start g) == whsize g o)
      end else begin
        let nx = mk_hp_addr next in
        let t = total_whsize g (objects nx g) in
        walk_tiled g nx;
        total_step g (objects start g);
        assert (total_whsize g (objects start g) == U64.v wz + 1 + t);
        add_mul8 (U64.v start) (U64.v wz + 1) t
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The equation
/// ---------------------------------------------------------------------------

/// (c2) as a word count: the live words, the listed free words and the
///      waste, by kind, sum to the end of the walk, and the walk reaches the
///      end of the heap up to a last word too short for a header.  The
///      kinds are exclusive, so nothing is counted twice; `heap_classified`
///      makes `KOther` empty, so nothing is left out.
let heap_partitioned (g: heap) (st: pstate) : prop =
  let objs = objects zero_addr g in
  U64.v zero_addr
  + (kind_whsize g st KLive objs
     + (kind_whsize g st KSlot objs + kind_whsize g st KListed objs)
     + (kind_whsize g st KFiller objs + kind_whsize g st KTail objs +
        kind_whsize g st KFreePage objs + kind_whsize g st KRunWaste objs +
        kind_whsize g st KHeapTail objs)) * U64.v mword
  == WE.walk_end g zero_addr /\
  WE.walk_end g zero_addr + 8 >= heap_size

/// The equation, from the classification and the walk reaching the end.
let partitioned (g: heap) (st: pstate)
  : Lemma (requires (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==> block_class g st y) /\
                    WE.walk_end g zero_addr + 8 >= heap_size)
          (ensures heap_partitioned g st)
  = let objs = objects zero_addr g in
    kinds_exhaustive g st objs;
    other_zero g st objs;
    walk_tiled g zero_addr

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
/// The equation does not hold of every heap: it needs the classification.
[@@expect_failure [19]]
let partitioned_needs_class (g: heap) (st: pstate)
  : Lemma (requires WE.walk_end g zero_addr + 8 >= heap_size) (ensures heap_partitioned g st)
  = walk_tiled g zero_addr

/// The hypotheses of `partitioned` are not refutable.
[@@expect_failure [19]]
let partitioned_hyps_not_false (g: heap) (st: pstate)
  : Lemma (requires (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==> block_class g st y) /\
                    WE.walk_end g zero_addr + 8 >= heap_size)
          (ensures False)
  = ()
#pop-options
