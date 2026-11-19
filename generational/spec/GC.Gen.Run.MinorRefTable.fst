/// ---------------------------------------------------------------------------
/// GC.Gen.Run.MinorRefTable - after a minor collection the empty remembered
/// set covers the major heap
/// ---------------------------------------------------------------------------
///
/// The pointer update (`update_pointers_with`) rewrites every field of a
/// non-free scannable block holding a nursery pointer `v` with `fwd v`, a
/// major address, provided `fwd v <> 0`.  So it suffices that every such
/// `v` is forwarded.  A non-free block after promotion is
///   * an old block (`in_use free major`), whose field is unchanged by
///     promotion: coverage puts it at a remembered slot, so `v` is a
///     collector root, which resolves to a nursery object (`roots_valid_with`)
///     and is forwarded (`fwd_covers_roots` / `fwd_covers_infix_roots`); or
///   * the copy of a nursery object `m` (`fwd m`), whose field is `m`'s
///     field: it names a nursery object (`nursery_fields_valid`), a successor
///     of `m`, so it is forwarded (`fwd_closed` / `fwd_covers_infix_fields`).

module GC.Gen.Run.MinorRefTable

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney
open GC.Gen.Run.Step
open GC.Gen.Run.Invariant.Defs

module GI = GC.Gen.Incremental
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CV = GC.Gen.CheneyGeneric
module CS = GC.Gen.Cheney.Steps
module CPFr = GC.Gen.CheneyPreservation.Frame
module CPFi = GC.Gen.CheneyPreservation.Fields
module PU = GC.Gen.PromoteUpdate
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module CheneyBFS = GC.Gen.CheneyBFS
module Reach = GC.Gen.Reachability

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// The field `j` of `obj`, as an address.
let fa (obj: obj_addr) (j: nat{U64.v obj + j * 8 + 8 <= heap_size}) : hp_addr =
  U64.uint_to_t (U64.v obj + j * 8)

/// The nursery pointer held by an old block's field is a collector root, so it
/// is forwarded.
let old_field_forwarded (ph: gc_phase) (free: free_def) (ms: minor_state) (g: heap) (fp: U64.t)
  (rs slots: seq U64.t) (n: nat) (obj: obj_addr) (j: nat)
  : Lemma (requires CV.promote_pre ms g fp /\ free_def_ok free /\
                    RT.ref_table_covers_with free g slots n /\
                    MCFH.remembered_targets_in_roots g rs slots n /\
                    MCFH.roots_valid_with free ms g rs /\
                    CheneyBFS.cheney_no_oom ph ms g fp rs /\
                    in_use free g obj /\ is_no_scan obj g = false /\
                    j < U64.v (wosize_of_object obj g) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    is_minor_pointer (to_minor_offset
                      (read_word (cheney_promote ph ms g fp rs).major_final (fa obj j))))
          (ensures (cheney_promote ph ms g fp rs).fwd_map
                     (to_minor_offset (read_word (cheney_promote ph ms g fp rs).major_final (fa obj j))) <> 0UL)
  = free_def_ok_elim free;
    CPFr.cheney_promote_frame_old_fields ph ms g fp rs obj j;
    MCFH.major_field_target_in_roots g free rs slots n obj j;
    let v = to_minor_offset (read_word g (fa obj j)) in
    if is_infix_in_minor ms v then ()
    else resolve_minor_non_infix ms v

/// The nursery pointer held by a promoted copy's field is a field of the
/// nursery object, so it is forwarded with it.
let promoted_field_forwarded (ph: gc_phase) (free: free_def) (ms: minor_state) (g: heap) (fp: U64.t)
  (rs: seq U64.t) (m: U64.t) (obj: obj_addr) (j: nat)
  : Lemma (requires CV.promote_pre ms g fp /\ free_def_ok free /\ allocations_not_free ph free /\
                    nursery_fields_valid ms /\
                    CheneyBFS.cheney_no_oom ph ms g fp rs /\
                    Seq.mem m (minor_objects ms) /\
                    (let prom = cheney_promote ph ms g fp rs in
                     prom.fwd_map m == obj /\
                     is_no_scan obj prom.major_final = false /\
                     j < U64.v (wosize_of_object obj prom.major_final) /\
                     U64.v obj + j * 8 + 8 <= heap_size /\
                     is_minor_pointer (to_minor_offset (read_word prom.major_final (fa obj j)))))
          (ensures (cheney_promote ph ms g fp rs).fwd_map
                     (to_minor_offset (read_word (cheney_promote ph ms g fp rs).major_final (fa obj j))) <> 0UL)
  = let prom = cheney_promote ph ms g fp rs in
    CPFi.cheney_promote_fwd_target_not_free ph free ms g fp rs m;
    CS.cheney_promote_preserves_wfh_part4 ph ms g fp rs;
    assert (~(is_infix obj prom.major_final));
    CPFi.cheney_promote_fwd_target_no_scan_iff_minor_tag ph ms g fp rs m;
    CPFi.cheney_promote_fwd_target_fields_match ph ms g fp rs m j;
    minor_scan_wosize_cases ms m;
    let v = minor_read_field ms m j in
    let ov = to_minor_offset v in
    assert (read_word prom.major_final (fa obj j) == v);
    assert (is_young v);
    assert (Seq.mem (resolve_minor ms ov) (minor_objects ms));
    if is_infix_in_minor ms ov then ()
    else begin
      resolve_minor_non_infix ms ov;
      Reach.minor_successors_char ms m ov;
      minor_objects_body_bound ms ov;
      is_minor_addr_from_bounds ov;
      assert (resolve_minor ms (to_minor_offset (minor_read_field ms m j)) == ov);
      assert (Seq.mem ov (Reach.minor_successors ms m))
    end

/// What the field lemma needs of the collection's inputs.
let ctx (ph: gc_phase) (free: free_def) (ms: minor_state) (g: heap) (fp: U64.t)
  (rs slots: seq U64.t) (n: nat) : prop =
  CV.promote_pre ms g fp /\ free_def_ok free /\ allocations_not_free ph free /\
  nursery_fields_valid ms /\
  RT.ref_table_covers_with free g slots n /\
  MCFH.remembered_targets_in_roots g rs slots n /\
  MCFH.roots_valid_with free ms g rs /\
  CheneyBFS.cheney_no_oom ph ms g fp rs

/// Every forwarded nursery pointer read by the update was forwarded.
let promoted_heap_field_forwarded (ph: gc_phase) (free: free_def) (ms: minor_state) (g: heap) (fp: U64.t)
  (rs slots: seq U64.t) (n: nat) (obj: obj_addr) (j: nat)
  : Lemma (requires ctx ph free ms g fp rs slots n /\
                    (let gm = (cheney_promote ph ms g fp rs).major_final in
                     in_use free gm obj /\ is_no_scan obj gm = false /\
                     j < U64.v (wosize_of_object obj gm) /\
                     U64.v obj + j * 8 + 8 <= heap_size /\
                     is_minor_pointer (to_minor_offset (read_word gm (fa obj j)))))
          (ensures (cheney_promote ph ms g fp rs).fwd_map
                     (to_minor_offset (read_word (cheney_promote ph ms g fp rs).major_final (fa obj j))) <> 0UL)
  = let prom = cheney_promote ph ms g fp rs in
    let gm = prom.major_final in
    CV.cheney_promote_in_use_origin ph free ms g fp rs obj;
    if in_use free g obj then begin
      free_def_ok_elim free;
      CPFr.cheney_promote_frame_old_header ph ms g fp rs obj;
      MCFH.header_eq_preserves_wosize_no_scan g gm obj;
      old_field_forwarded ph free ms g fp rs slots n obj j
    end else begin
      let aux (m: U64.t)
        : Lemma (requires Seq.mem m (minor_objects ms) /\ prom.fwd_map m == obj)
                (ensures prom.fwd_map (to_minor_offset (read_word gm (fa obj j))) <> 0UL)
        = promoted_field_forwarded ph free ms g fp rs m obj j in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end

/// **No field of a non-free scannable block holds a nursery pointer after the
/// collection.**
let field_not_young (ph: gc_phase) (free: free_def) (ms: minor_state) (g: heap) (fp: U64.t)
  (rs slots: seq U64.t) (n: nat) (obj: obj_addr) (j: nat)
  : Lemma (requires ctx ph free ms g fp rs slots n /\
                    (let g' = (cheney_collect_spec_with ph free ms g fp rs).mc_major in
                     is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
                     j < U64.v (wosize_of_object obj g') /\
                     U64.v obj + j * 8 + 8 <= heap_size))
          (ensures (let g' = (cheney_collect_spec_with ph free ms g fp rs).mc_major in
                    ~(is_minor_pointer (to_minor_offset (read_word g' (fa obj j))))))
  = let prom = cheney_promote ph ms g fp rs in
    let gm = prom.major_final in
    let fwd = prom.fwd_map in
    let g' = (cheney_collect_spec_with ph free ms g fp rs).mc_major in
    assert (g' == update_walk gm (in_use free gm) fwd);
    CS.cheney_promote_preserves_wfh_part1 ph ms g fp rs;
    free_def_ok_elim free;
    CV.update_walk_keeps_in_use free gm (in_use free gm) fwd obj;
    assert (in_use free gm obj);
    PU.update_walk_preserves_header gm (in_use free gm) fwd obj;
    MCFH.header_eq_preserves_wosize_no_scan gm g' obj;
    PU.update_walk_field_effect gm (in_use free gm) fwd obj j;
    CS.cheney_promote_fwd_above_zero_addr ph ms g fp rs;
    zero_addr_above_minor ();
    let old_val = to_minor_offset (read_word gm (fa obj j)) in
    if is_minor_pointer old_val then begin
      promoted_heap_field_forwarded ph free ms g fp rs slots n obj j;
      CS.cheney_promote_fwd_bounded ph ms g fp rs;
      to_minor_offset_stable_above_minor (fwd old_val)
    end

/// The collector's roots include the remembered slots' targets.
let remembered_in_collector_roots (r: real_state) (roots: seq U64.t)
  : Lemma (MCFH.remembered_targets_in_roots r.memory.major (collector_roots r roots)
             r.ref_table (Seq.length r.ref_table))
  = let t = MCFH.remembered_slot_targets r.memory.major r.ref_table (Seq.length r.ref_table) in
    let aux (x: U64.t) : Lemma (Seq.mem x t ==> Seq.mem x (Seq.append roots t)) =
      FStar.Seq.Properties.lemma_mem_append roots t in
    FStar.Classical.forall_intro aux

/// The field lemma's context holds at a minor step.
let ctx_of_minor_step (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ minor_step r roots r')
          (ensures ctx r.phase (GI.phase_free r.phase) r.memory.nursery r.memory.major r.free_list
                     (collector_roots r roots) r.ref_table (Seq.length r.ref_table))
  = let ms = r.memory.nursery in
    let g = r.memory.major in
    let free = GI.phase_free r.phase in
    GI.phase_shape_collection ms g r.free_list r.phase r.scan_pos;
    GenInv.collection_shape_with_elim r.phase free ms g r.free_list;
    GenInv.major_shape_with_elim r.phase free g r.free_list;
    GenInv.minor_heap_shape_elim ms;
    remembered_in_collector_roots r roots

let minor_ref_table_empty r roots r' =
  let ms = r.memory.nursery in
  let g = r.memory.major in
  let free = GI.phase_free r.phase in
  let rs = collector_roots r roots in
  ctx_of_minor_step r roots r';
  let g' = (cheney_collect_spec_with r.phase free ms g r.free_list rs).mc_major in
  assert (r'.memory.major == g');
  let aux (obj: obj_addr) (j: nat)
    : Lemma (is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
             j < U64.v (wosize_of_object obj g') /\
             U64.v obj + j * 8 + 8 <= heap_size ==>
             ~(is_minor_pointer (to_minor_offset (read_word g' (U64.uint_to_t (U64.v obj + j * 8))))))
    = begin introduce (is_block g' obj /\ not (free g' obj) /\ scannable g' obj /\
                 j < U64.v (wosize_of_object obj g') /\
                 U64.v obj + j * 8 + 8 <= heap_size) ==>
                ~(is_minor_pointer (to_minor_offset (read_word g' (U64.uint_to_t (U64.v obj + j * 8)))))
      with field_not_young r.phase free ms g r.free_list rs r.ref_table (Seq.length r.ref_table) obj j end in
  FStar.Classical.forall_intro_2 aux
