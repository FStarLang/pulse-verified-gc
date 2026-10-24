/// ---------------------------------------------------------------------------
/// GC.Spec.HeapAgree - Heaps that agree except inside free blocks
/// ---------------------------------------------------------------------------
///
/// The body of a free (blue) block beyond its free-list link is not part of
/// the heap model: `GC.Spec.Fields.fields_constrained` excludes blue sources
/// and `GC.Spec.HeapGraph.get_pointer_fields` gives them no edges.  Two heaps
/// that differ only there are interchangeable for every property the collector
/// proves.
///
/// `heaps_agree_mod_free h1 h2` says exactly that, block by block along the
/// object walk of `h2` (`walk_agree`): the two heaps have the same header at
/// every block on the walk; a non-blue block has the same fields; a blue block
/// has the same link word (field 0).  Words of a free block past its link,
/// including the stale headers of the dead objects that were merged into it,
/// are not compared.
///
/// It is what the collector's Pulse pass and its specification share:
/// `GC.Spec.SweepCoalesce.fused_agrees_sweep_coalesce` proves that the fused
/// sweep+coalesce pass the implementation runs agrees in this sense with
/// `coalesce (sweep ...)`, the heap the correctness theorems are stated about.
/// The lemmas below carry those theorems across.

module GC.Spec.HeapAgree

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module Mark = GC.Spec.Mark
module FL = GC.Spec.FreeList
module AllocCommon = GC.Spec.Allocator.Lemmas.Common
module AllocChain = GC.Spec.Allocator.Lemmas.Chain

/// What block `b` of `h2` must share with `h1`.
let block_agree (h1 h2: heap) (b: obj_addr) : prop =
  read_word h1 (hd_address b) == read_word h2 (hd_address b) /\
  (if is_blue b h2 then
     (U64.v (wosize_of_object b h2) >= 1 ==> read_word h1 b == read_word h2 b)
   else
     (forall (a: hp_addr).
        U64.v a >= U64.v b /\ U64.v a + 8 <= U64.v b + U64.v (wosize_of_object b h2) * 8 ==>
        read_word h1 a == read_word h2 a))

/// The walk's next position is word-aligned.
let walk_next_aligned (start: hp_addr) (wz: nat)
  : Lemma ((U64.v start + (wz + 1) * 8) % 8 == 0)
  = FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v start) ((wz + 1) * 8) 8;
    FStar.Math.Lemmas.cancel_mul_mod (wz + 1) 8

/// Agreement along the walk of `h2` from `start`, mirroring `objects`.
let rec walk_agree (start: hp_addr) (h1 h2: heap)
  : Tot prop (decreases (heap_size - U64.v start))
  = if U64.v start + 8 >= heap_size then True
    else
      read_word h1 start == read_word h2 start /\
      (let wz = getWosize (read_word h2 start) in
       let next = U64.v start + (U64.v wz + 1) * 8 in
       if next > heap_size then True
       else begin
         walk_next_aligned start (U64.v wz);
         block_agree h1 h2 (f_address start) /\
         (next < heap_size ==> walk_agree (U64.uint_to_t next) h1 h2)
       end)

let heaps_agree_mod_free (h1 h2: heap) : prop = walk_agree zero_addr h1 h2

/// ---------------------------------------------------------------------------
/// Building `walk_agree`
/// ---------------------------------------------------------------------------

/// Heaps that agree on every word from `start` on agree along the walk.
val walk_agree_of_equal_from (start: hp_addr) (h1 h2: heap)
  : Lemma (requires forall (a: hp_addr). U64.v a >= U64.v start ==> read_word h1 a == read_word h2 a)
          (ensures walk_agree start h1 h2)

/// One step of the walk.
val walk_agree_step (start: hp_addr) (h1 h2: heap)
  : Lemma (requires U64.v start + 8 < heap_size /\
                    read_word h1 start == read_word h2 start /\
                    (let next = U64.v start + (U64.v (getWosize (read_word h2 start)) + 1) * 8 in
                     next <= heap_size /\
                     block_agree h1 h2 (f_address start) /\
                     (next < heap_size ==> walk_agree (U64.uint_to_t next) h1 h2)))
          (ensures walk_agree start h1 h2)

/// ---------------------------------------------------------------------------
/// Using `heaps_agree_mod_free`
/// ---------------------------------------------------------------------------

val agree_objects (h1 h2: heap)
  : Lemma (requires heaps_agree_mod_free h1 h2)
          (ensures objects zero_addr h1 == objects zero_addr h2)

/// Everything about one block on the walk.
val agree_block (h1 h2: heap) (b: obj_addr)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ Seq.mem b (objects zero_addr h2))
          (ensures
            objects zero_addr h1 == objects zero_addr h2 /\
            read_word h1 (hd_address b) == read_word h2 (hd_address b) /\
            color_of_object b h1 == color_of_object b h2 /\
            is_white b h1 == is_white b h2 /\ is_blue b h1 == is_blue b h2 /\
            is_gray b h1 == is_gray b h2 /\ is_black b h1 == is_black b h2 /\
            wosize_of_object b h1 == wosize_of_object b h2 /\
            tag_of_object b h1 == tag_of_object b h2 /\
            is_no_scan b h1 == is_no_scan b h2 /\
            is_infix b h1 == is_infix b h2 /\
            is_closure b h1 == is_closure b h2 /\
            resolve_object b h1 == resolve_object b h2 /\
            fields_constrained h1 b == fields_constrained h2 b /\
            (is_blue b h2 /\ U64.v (wosize_of_object b h2) >= 1 ==>
              read_word h1 b == read_word h2 b) /\
            (~(is_blue b h2) ==>
              (forall (a: hp_addr).
                 U64.v a >= U64.v b /\ U64.v a + 8 <= U64.v b + U64.v (wosize_of_object b h2) * 8 ==>
                 read_word h1 a == read_word h2 a)))

/// Fields of a live block, as `get_field` sees them.
val agree_get_field (h1 h2: heap) (b: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ Seq.mem b (objects zero_addr h2) /\
                    ~(is_blue b h2) /\ U64.v i <= U64.v (wosize_of_object b h2))
          (ensures HeapGraph.get_field h1 b i == HeapGraph.get_field h2 b i)

/// The well-formedness facts of `h2` that make the targets of its live fields
/// stable: they resolve to live blocks, and for an interior pointer the infix
/// header sits inside a live closure.
let agree_target_pre (h2: heap) : prop =
  well_formed_heap h2 /\ Mark.no_pointer_to_blue h2

/// `points_to` from a live block is the same in both heaps.
val agree_points_to (h1 h2: heap) (src dst: obj_addr)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ Seq.mem src (objects zero_addr h2) /\
                    ~(is_blue src h2))
          (ensures points_to h1 src dst == points_to h2 src dst)

/// A target of a live field has the same header word, and so the same
/// resolution, in both heaps.
val agree_target (h1 h2: heap) (src dst: obj_addr)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ agree_target_pre h2 /\
                    Seq.mem src (objects zero_addr h2) /\ fields_constrained h2 src /\
                    points_to h2 src dst)
          (ensures read_word h1 (hd_address dst) == read_word h2 (hd_address dst) /\
                   resolve_object dst h1 == resolve_object dst h2 /\
                   is_infix dst h1 == is_infix dst h2 /\
                   wosize_of_object dst h1 == wosize_of_object dst h2 /\
                   Seq.mem (resolve_object dst h2) (objects zero_addr h2) /\
                   ~(is_blue (resolve_object dst h2) h2))

/// ---------------------------------------------------------------------------
/// Transferred properties
/// ---------------------------------------------------------------------------

val agree_wfh_part1 (h1 h2: heap)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ well_formed_heap_part1 h2)
          (ensures well_formed_heap_part1 h1)

/// Every object is white or blue in `h1` if it is in `h2`.
val agree_white_or_blue (h1 h2: heap)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr h2) ==>
                       is_white x h2 \/ is_blue x h2))
          (ensures forall (x: obj_addr). Seq.mem x (objects zero_addr h1) ==>
                     is_white x h1 \/ is_blue x h1)

val agree_well_formed_heap (h1 h2: heap)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ agree_target_pre h2)
          (ensures well_formed_heap h1)

val agree_no_pointer_to_blue (h1 h2: heap)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ agree_target_pre h2)
          (ensures Mark.no_pointer_to_blue h1)

val agree_create_graph (h1 h2: heap)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ agree_target_pre h2)
          (ensures HeapModel.create_graph h1 == HeapModel.create_graph h2)

/// ---------------------------------------------------------------------------
/// The free list
/// ---------------------------------------------------------------------------

/// Field 0 of every block -- the link of a free one -- is shared.
val agree_field0 (h1 h2: heap) (b: obj_addr)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ Seq.mem b (objects zero_addr h2) /\
                    U64.v (wosize_of_object b h2) >= 1)
          (ensures read_word h1 b == read_word h2 b)

val agree_fl_valid (h1 h2: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ AllocCommon.fl_valid h2 fp fuel)
          (ensures AllocCommon.fl_valid h1 fp fuel)

val agree_fl_chain_terminates (h1 h2: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ AllocCommon.fl_valid h2 fp steps /\
                    AllocChain.fl_chain_terminates h2 fp steps)
          (ensures AllocChain.fl_chain_terminates h1 fp steps)

val agree_chain_avoids (h1 h2: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ AllocCommon.fl_valid h2 fp fuel /\
                    AllocChain.chain_avoids h2 fp excl fuel = true)
          (ensures AllocChain.chain_avoids h1 fp excl fuel = true)

val agree_fl_exact (h1 h2: heap) (fp: U64.t)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ FL.fl_exact h2 fp)
          (ensures FL.fl_exact h1 fp)

val agree_dense (h1 h2: heap)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ heap_objects_dense h2)
          (ensures heap_objects_dense h1)
