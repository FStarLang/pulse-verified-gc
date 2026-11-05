/// ---------------------------------------------------------------------------
/// GC.Gen.ObjectTable - the object-start table across allocation and promotion
/// ---------------------------------------------------------------------------
///
/// An allocation from the free lists adds exactly one walk position, the
/// object it returns, and keeps every other (`GC.Gen.AllocLists`).  So the
/// table after it (`GC.Spec.ObjectTable.alloc_table`) is sound when the table
/// before it was, and exact when the table before it was.
///
/// Promotion is that allocation followed by writes to the new object's body
/// and a header rewrite that keeps its wosize: the walk is the allocation's.
/// The pointer rewrite of a minor collection writes fields only.  Both carry
/// soundness (`table_sound`), the invariant the generational heap keeps.

module GC.Gen.ObjectTable

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FreeLists
open GC.Spec.Allocator.Lists
open GC.Spec.ObjectTable
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Seq = FStar.Seq
module AL = GC.Gen.AllocLists
module PS = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module CD = GC.Gen.Cheney.Dense

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// A successful allocation was for fewer than `pow2 54` words: first fit
/// stops only at a block at least as large, and a wosize is below `pow2 54`.
#push-options "--z3rlimit 40"
let alloc_lists_wz_bound (g: heap) (fls: fl_state) (wz: nat)
  : Lemma (requires (alloc_lists_spec g fls wz).obj_out <> 0UL)
          (ensures req_wz wz < pow2 54)
  = alloc_lists_list_spec g fls wz;
    let j = alloc_lists_list g fls wz in
    let fp = fls_head fls j in
    GC.Spec.Allocator.Lists.first_fit_same_block g fp 0UL fp (req_wz wz) heap_words
#pop-options

/// **Exactness after an allocation.**
#push-options "--z3rlimit 40"
let alloc_lists_table (g: heap) (fls: fl_state) (wz: nat) (t: seq U64.t)
  : Lemma (requires AL.alloc_lists_pre g fls /\ wz >= 1 /\ table_ok g t)
          (ensures table_ok (alloc_lists_spec g fls wz).heap_out
                            (alloc_table t (alloc_lists_spec g fls wz).obj_out wz))
  = let r = alloc_lists_spec g fls wz in
    AL.alloc_lists_oom_unchanged g fls wz;
    if r.obj_out = 0UL then ()
    else begin
      alloc_lists_wz_bound g fls wz;
      table_ok_elim g t;
      AL.alloc_lists_preserves_dense_part1 g fls wz;
      AL.alloc_lists_obj_in_objects_part1 g fls wz;
      AL.alloc_lists_obj_wosize_exact_part1 g fls wz;
      AL.alloc_lists_preserves_objects_part1 g fls wz;
      AL.alloc_lists_only_new_is_obj_out_part1 g fls wz;
      let p : obj_addr = r.obj_out in
      objects_addresses_gt_start zero_addr r.heap_out p;
      table_add_block g r.heap_out t p wz
    end
#pop-options

/// The same, as the allocator's postcondition states it: conditional on the
/// facts it does not require.
let alloc_lists_table_imp (g: heap) (fls: fl_state) (wz: nat) (t: seq U64.t)
  : Lemma (ensures (AL.alloc_lists_pre g fls /\ wz >= 1 /\ table_ok g t) ==>
                   table_ok (alloc_lists_spec g fls wz).heap_out
                            (alloc_table t (alloc_lists_spec g fls wz).obj_out wz))
  = FStar.Classical.move_requires (alloc_lists_table g fls wz) t

/// What the allocator's table write needs to know about its result.
let alloc_lists_obj_for_table (g: heap) (fls: fl_state) (wz: nat)
  : Lemma (let r = alloc_lists_spec g fls wz in
           (r.obj_out == 0UL \/
            (U64.v r.obj_out >= 8 /\ U64.v r.obj_out < heap_size /\ U64.v r.obj_out % 8 == 0)) /\
           (U64.v r.obj_out >= 8 ==> req_wz wz < pow2 54))
  = AL.alloc_lists_obj_valid g fls wz;
    let r = alloc_lists_spec g fls wz in
    if r.obj_out <> 0UL then alloc_lists_wz_bound g fls wz

/// Promotion's writes after the allocation keep the walk.
#push-options "--z3rlimit 40"
let promote_object_objects (minor: minor_state) (major: heap) (obj: U64.t)
                           (fp: fl_state) (wz: nat{wz > 0})
  : Lemma (requires AL.alloc_lists_pre major fp /\ wz < pow2 54 /\
                    (alloc_lists_spec major fp wz).obj_out <> 0UL)
          (ensures objects zero_addr (PS.promote_object minor major obj fp wz).PS.major_out ==
                   objects zero_addr (alloc_lists_spec major fp wz).heap_out)
  = let a = alloc_lists_spec major fp wz in
    PS.promote_object_success minor major obj fp wz;
    AL.alloc_lists_obj_in_objects_part1 major fp wz;
    AL.alloc_lists_obj_wosize_exact_part1 major fp wz;
    let p : obj_addr = a.obj_out in
    let copied = WB.copy_fields minor a.heap_out obj p 0 wz in
    WB.copy_fields_preserves_objects_aux minor a.heap_out obj p 0 wz;
    minor_tag_bound minor obj;
    PS.set_promoted_tag_preserves_objects copied p (minor_tag minor obj)
#pop-options

/// **Soundness after an allocation.**  It needs only that the walk keeps
/// every position and gains the new object.
#push-options "--z3rlimit 40"
let alloc_lists_sound (g: heap) (fls: fl_state) (wz: nat) (t: seq U64.t)
  : Lemma (requires AL.alloc_lists_pre g fls /\ table_sound g t)
          (ensures table_sound (alloc_lists_spec g fls wz).heap_out
                               (alloc_table t (alloc_lists_spec g fls wz).obj_out wz))
  = let r = alloc_lists_spec g fls wz in
    AL.alloc_lists_oom_unchanged g fls wz;
    if r.obj_out = 0UL then ()
    else begin
      AL.alloc_lists_preserves_objects_part1 g fls wz;
      AL.alloc_lists_obj_in_objects_part1 g fls wz;
      let p : obj_addr = r.obj_out in
      table_sound_add_block g r.heap_out t p wz
    end
#pop-options

let alloc_lists_sound_imp (g: heap) (fls: fl_state) (wz: nat) (t: seq U64.t)
  : Lemma (ensures (AL.alloc_lists_pre g fls /\ table_sound g t) ==>
                   table_sound (alloc_lists_spec g fls wz).heap_out
                               (alloc_table t (alloc_lists_spec g fls wz).obj_out wz))
  = FStar.Classical.move_requires (alloc_lists_sound g fls wz) t

/// One promotion step, as `promote_one` states it: if the table was sound
/// for the heap before, it is sound after.  The allocator gives soundness
/// for its own heap (`t2`); promotion's later writes keep the walk.
#push-options "--z3rlimit 40"
let promote_object_sound_step (minor: minor_state) (major: heap) (obj: U64.t)
                              (fp: fl_state) (wz: nat{wz > 0}) (t t2: seq U64.t)
  : Lemma (requires AL.alloc_lists_pre major fp /\
                    (alloc_lists_spec major fp wz).obj_out <> 0UL /\
                    (table_sound major t ==> table_sound (alloc_lists_spec major fp wz).heap_out t2))
          (ensures table_sound major t ==>
                   table_sound (PS.promote_object minor major obj fp wz).PS.major_out t2)
  = alloc_lists_wz_bound major fp wz;
    promote_object_objects minor major obj fp wz;
    FStar.Classical.move_requires
      (table_sound_grow (alloc_lists_spec major fp wz).heap_out
                        (PS.promote_object minor major obj fp wz).PS.major_out) t2
#pop-options

/// **Soundness after a minor collection.**  The pointer rewrite after
/// promotion writes only fields, so the walk is promotion's.
let minor_collect_sound (minor: minor_state) (major: heap) (fp: fl_state)
                        (roots: seq U64.t) (t: seq U64.t)
  : Lemma (requires (let prom = GC.Gen.Cheney.cheney_promote minor major fp roots in
                     well_formed_heap_part1 prom.PS.major_final /\
                     table_sound prom.PS.major_final t))
          (ensures table_sound (GC.Gen.Cheney.cheney_collect_spec minor major fp roots).PS.mc_major t)
  = let prom = GC.Gen.Cheney.cheney_promote minor major fp roots in
    let res = GC.Gen.Cheney.cheney_collect_spec minor major fp roots in
    assert (res.PS.mc_major == PS.update_major_pointers prom.PS.major_final prom.PS.fwd_map);
    GC.Gen.PromoteUpdate.update_major_pointers_preserves_objects prom.PS.major_final prom.PS.fwd_map;
    table_sound_grow prom.PS.major_final res.PS.mc_major t
