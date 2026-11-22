/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PromoteUpdate - akhil's pointer update, read as the model
/// ---------------------------------------------------------------------------
///
/// After promotion the minor collection rewrites the nursery pointers held
/// by the blocks in use (`GC.Gen.Promote.update_pointers_with`).  On a heap
/// whose walk reaches its end: the blocks and headers stay (`upd_hd`), and a
/// field word of a block is rewritten through the forwarding map (`rw`)
/// exactly when the block is in use and scannable, else it stays
/// (`upd_field`).  Nothing here depends on an allocator.

module GC.Spec.Top.PromoteUpdate

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Walk
open GC.Gen.Base
open GC.Gen.Promote
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.ByteFacts
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64
module PUpd = GC.Gen.PromoteUpdate
module LV = GC.Spec.Top.PagesLive

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The rewrite of one word.
let rw (fwd: forwarding_map) (w: U64.t) : GTot U64.t =
  if is_minor_pointer w && fwd w <> 0UL then fwd w else w

/// Every position the walk reaches before the end is a block's header.
let reached_hdr (g: heap) (q: hp_addr)
  : Lemma (requires reaches g zero_addr heap_size /\ reaches g zero_addr (U64.v q))
          (ensures U64.v q + 8 < heap_size /\
                   (let x : obj_addr = U64.uint_to_t (U64.v q + 8) in
                    Seq.mem x (objects zero_addr g) /\ hd_address x == q))
  = reaches_block_before g zero_addr q heap_size;
    reaches_bounds g zero_addr (U64.v q);
    let x : obj_addr = U64.uint_to_t (U64.v q + 8) in
    hd_address_spec x;
    U64.v_inj (hd_address x) q;
    assert (reaches g zero_addr (U64.v (hd_address x)) /\ can_step g (hd_address x));
    objects_mem_iff g zero_addr x

/// **The blocks and headers stay.**
#push-options "--z3rlimit 40"
let upd_hd (free: free_def) (g: heap) (fwd: forwarding_map)
  : Lemma (requires blocks_fit g /\ reaches g zero_addr heap_size)
          (ensures (let g' = update_pointers_with free g fwd in
                    same_sizes g g' /\
                    (forall (j: nat). (cabs g').M.hd j == (cabs g).M.hd j) /\
                    (forall (w: nat). is_fw g' w == is_fw g w)))
  = let g' = update_pointers_with free g fwd in
    let hdr (q: hp_addr)
      : Lemma (reaches g zero_addr (U64.v q) ==> read_word g' q == read_word g q)
      = if reaches g zero_addr (U64.v q) then begin
          reached_hdr g q;
          PUpd.update_walk_preserves_header g (in_use free g) fwd (U64.uint_to_t (U64.v q + 8))
        end in
    FStar.Classical.forall_intro hdr;
    assert (same_sizes g g');
    cabs_congr g g';
    let hj (j: nat) : Lemma ((cabs g').M.hd j == (cabs g).M.hd j)
      = if on_walk g j then word_at g (hp j) in
    FStar.Classical.forall_intro hj
#pop-options

/// **A field word**: rewritten in a scannable block in use, else kept.
#push-options "--z3rlimit 40"
let upd_field (free: free_def) (g: heap) (fwd: forwarding_map) (x i: nat)
  : Lemma (requires blocks_fit g /\ reaches g zero_addr heap_size /\ M.is_block (cabs g) x /\ i < M.wz_of (cabs g) x)
          (ensures pos x + 8 < heap_size /\ pos (x + 1 + i) < heap_size /\
                   word (update_pointers_with free g fwd) (x + 1 + i) ==
                   (if in_use free g (obj_of x) && not (is_no_scan (obj_of x) g)
                    then rw fwd (word g (x + 1 + i)) else word g (x + 1 + i)))
  = abs_block_walk g x;
    abs_is_block g x;
    abs_header g x;
    msize_pos (x + 1 + i);
    msize_pos (x + M.wz_of (cabs g) x);
    let obj = obj_of x in
    let a = U64.uint_to_t (U64.v obj + i * 8) in
    assert (U64.v a == pos (x + 1 + i));
    U64.v_inj a (hp (x + 1 + i));
    pos_aligned (x + 1 + i);
    LV.tmo_id (read_word g a);
    if in_use free g obj && not (is_no_scan obj g)
    then PUpd.update_walk_field_effect g (in_use free g) fwd obj i
    else PUpd.update_walk_preserves_skipped_field g (in_use free g) fwd obj i
#pop-options
