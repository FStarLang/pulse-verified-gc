module GC.Gen.SweepPhase

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.FusedSweep.Inv
open GC.Spec.SweepPhase.Util
open GC.Spec.SweepPhase.Intrinsic
open GC.Spec.SweepPhase.Mutator
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module W = GC.Spec.Walk
module AC = GC.Spec.Allocator.Cursor
module SA = GC.Spec.Allocator
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Promotion
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let minor_fields_ok_of free minor obj g =
  let one (j: nat)
    : Lemma (requires j < minor_scan_wosize minor obj)
            (ensures storable free g (minor_read_field minor obj j))
    = let w = minor_read_field minor obj j in
      if is_pointer w then begin
        GC.Gen.HeapInvariant.minor_major_fields_not_free_elim free minor g obj j;
        let t : obj_addr = w in
        in_use_not_blue free g t;
        assert (~(is_infix t g));
        resolve_non_infix t g;
        infix_addr_wf_non_infix g (objects zero_addr g) t
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// The copy into a non-blue object keeps the shape, the walk and the
/// headers, and keeps a fresh object fresh.
#push-options "--z3rlimit 20"
let rec copy_shape (g: heap) (fp: U64.t) (c0: U64.t) (minor: minor_state)
                   (src: U64.t) (dst: obj_addr) (i n: nat)
  : Lemma (requires sweep_shape g fp c0 /\ Seq.mem dst (objects zero_addr g) /\ ~(is_blue dst g) /\
                    n <= U64.v (wosize_of_object dst g))
          (ensures (let g' = WB.copy_fields minor g src dst i n in
                    sweep_shape g' fp c0 /\ same_heads g g' /\
                    (forall (y: obj_addr). pending_free c0 g' y == pending_free c0 g y) /\
                    (fresh_ok g fp c0 dst ==> fresh_ok g' fp c0 dst)))
          (decreases (n - i))
  = if i >= n then begin
      WB.copy_fields_base minor g src dst i n;
      same_heads_refl g
    end else begin
      part1_holds g;
      wfh_part1_obj_bound g dst;
      hd_address_spec dst;
      let an = U64.v dst + i * 8 in
      let a : hp_addr = U64.uint_to_t an in
      let v = minor_read_field minor src i in
      WB.copy_fields_step minor g src dst i n;
      let g1 = write_word g a v in
      body_write_shape g fp c0 dst a v;
      same_heads_facts g g1;
      colour_of g dst; colour_of g1 dst;
      (if FStar.IndefiniteDescription.strong_excluded_middle (fresh_ok g fp c0 dst)
       then fresh_write g fp c0 dst a v);
      copy_shape g1 fp c0 minor src dst (i + 1) n;
      same_heads_trans g g1 (WB.copy_fields minor g1 src dst (i + 1) n)
    end
#pop-options

#push-options "--z3rlimit 30"
let promote_sweep_shape g fp c0 minor obj wosize =
  let tag = Promote.promoted_tag minor obj in
  alloc_sweep_shape g fp c0 wosize tag;
  let r = AC.alloc_phase g fp (SA.Sweeping c0) wosize tag in
  if r.SA.obj_out <> 0UL then begin
    let dst : obj_addr = r.SA.obj_out in
    obj_pos r.SA.heap_out dst; colour_of r.SA.heap_out dst;
    hd_address_spec dst;
    copy_shape r.SA.heap_out r.SA.fp_out c0 minor obj dst 0 wosize
  end
#pop-options

/// `same_block` composes.
let same_block_trans (g g' g'': heap) (q: hp_addr)
  : Lemma (requires same_block g g' q /\ same_block g' g'' q)
          (ensures same_block g g'' q)
  = W.bnext_facts g q; W.bnext_facts g' q

/// The copy into `dst` keeps every other object's block.
#push-options "--z3rlimit 20"
let copy_keeps (g1: heap) (minor: minor_state) (src: U64.t) (dst: obj_addr) (n: nat) (y: obj_addr)
  : Lemma (requires Seq.mem dst (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\ y <> dst /\
                    n <= U64.v (wosize_of_object dst g1))
          (ensures same_block g1 (WB.copy_fields minor g1 src dst 0 n) (hd_address y))
  = let g2 = WB.copy_fields minor g1 src dst 0 n in
    part1_holds g1;
    wfh_part1_obj_bound g1 dst;
    hd_address_spec dst;
    obj_pos g1 y;
    Promote.dst_fields_valid_from_bounds dst (if n = 0 then 1 else n);
    let body (b: hp_addr)
      : Lemma (requires U64.v (hd_address y) <= U64.v b /\ U64.v b < W.bnext g1 (hd_address y))
              (ensures read_word g2 b == read_word g1 b)
      = if n = 0 then WB.copy_fields_base minor g1 src dst 0 n
        else if U64.v b >= U64.v dst && U64.v b < U64.v dst + n * 8 then begin
          assert (in_body g1 dst b);
          (if U64.v b = U64.v (hd_address y) then begin
             in_body_block g1 dst b;
             no_pos_inside g1 (hd_address dst) (U64.v b)
           end else other_body g1 dst y b)
        end else Promote.copy_fields_frame minor g1 src dst 0 n b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires body);
    W.bnext_facts g1 (hd_address y)
#pop-options

/// The copied fields are storable.
#push-options "--z3rlimit 20"
let copy_storable_one (g g2: heap) (free free2: free_def) (minor: minor_state) (obj: U64.t) (dst: obj_addr)
                      (i: nat{U64.v dst + i * 8 + 8 <= heap_size})
  : Lemma (requires minor_fields_ok free minor obj g /\
                    no_infix_block g /\ no_infix_block g2 /\ free_def_ok free2 /\
                    heads_kept free g g2 /\ (forall (y: obj_addr). in_use free g y ==> in_use free2 g2 y) /\
                    i < minor_scan_wosize minor obj /\
                    field_val g2 dst i == minor_read_field minor obj i)
          (ensures storable free2 g2 (field_val g2 dst i))
  = storable_transfer g g2 free free2 (minor_read_field minor obj i)
#pop-options

#push-options "--z3rlimit 20"
let copy_storable (g g2: heap) (free free2: free_def) (minor: minor_state) (obj: U64.t) (dst: obj_addr)
                  (wosize: nat{wosize > 0})
  : Lemma (requires minor_fields_ok free minor obj g /\ wosize == minor_wosize minor obj /\
                    no_infix_block g /\ no_infix_block g2 /\ free_def_ok free2 /\
                    heads_kept free g g2 /\ (forall (y: obj_addr). in_use free g y ==> in_use free2 g2 y) /\
                    U64.v (wosize_of_object dst g2) == wosize /\
                    tag_of_object dst g2 == Promote.promoted_tag minor obj /\
                    (forall (j: nat). j < wosize /\ U64.v dst + j * 8 + 8 <= heap_size ==>
                       field_val g2 dst j == minor_read_field minor obj j))
          (ensures fields_storable free2 g2 dst)
  = is_no_scan_spec dst g2;
    no_scan_tag_val ();
    minor_scan_wosize_cases minor obj;
    minor_tag_bound minor obj;
    if not (is_no_scan dst g2) then begin
      assert (minor_scan_wosize minor obj == wosize);
      let sto (i: nat)
        : Lemma (i < U64.v (wosize_of_object dst g2) /\ U64.v dst + i * 8 + 8 <= heap_size ==>
                 storable free2 g2 (field_val g2 dst i))
        = if i < U64.v (wosize_of_object dst g2) && U64.v dst + i * 8 + 8 <= heap_size
          then copy_storable_one g g2 free free2 minor obj dst i
      in
      FStar.Classical.forall_intro sto
    end
#pop-options

#push-options "--z3rlimit 20"
let promote_sweep_phase g fp c0 minor obj wosize =
  let tag = Promote.promoted_tag minor obj in
  let free = free_incremental c0 in
  sweep_inv_incremental_iff g fp c0;
  alloc_sweep_phase g fp c0 wosize tag;
  let r = AC.alloc_phase g fp (SA.Sweeping c0) wosize tag in
  if r.SA.obj_out <> 0UL then begin
    let g1 = r.SA.heap_out in
    let dst : obj_addr = r.SA.obj_out in
    obj_pos g1 dst; colour_of g1 dst;
    hd_address_spec dst;
    copy_shape g1 r.SA.fp_out c0 minor obj dst 0 wosize;
    let g2 = WB.copy_fields minor g1 obj dst 0 wosize in
    same_heads_facts g1 g2;
    colour_of g2 dst;
    part1_holds g1;
    wfh_part1_obj_bound g1 dst;
    Promote.dst_fields_valid_from_obj g1 dst wosize;
    Promote.copy_fields_all_correct minor g1 obj dst wosize;
    assert (forall (j: nat). j < wosize /\ U64.v dst + j * 8 + 8 <= heap_size ==>
              field_val g2 dst j == minor_read_field minor obj j);
    let kept (y: obj_addr)
      : Lemma (requires in_use free g y)
              (ensures read_word g2 (hd_address y) == read_word g (hd_address y) /\
                       (is_closure y g ==> same_block g g2 (hd_address y)) /\
                       in_use (free_incremental c0) g2 y)
      = alloc_keeps g fp c0 wosize tag y;
        obj_pos g1 y;
        assert (read_word g2 (hd_address y) == read_word g1 (hd_address y));
        if is_closure y g then begin
          copy_keeps g1 minor obj dst wosize y;
          same_block_trans g g1 g2 (hd_address y)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
    wf_with_parts ();
    same_heads_part4 g1 g2;
    free_incremental_ok c0;
    copy_storable g g2 free (free_incremental c0) minor obj dst wosize;
    fresh_close g2 r.SA.fp_out c0 dst
  end
#pop-options
