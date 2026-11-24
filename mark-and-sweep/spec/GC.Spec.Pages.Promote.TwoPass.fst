/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.TwoPass - akhil's two-pass pointer update, for any
/// allocator
/// ---------------------------------------------------------------------------
///
/// Plan §30.  After promotion, akhil's Pulse collection rewrites nursery
/// pointers in two passes (`GC.Gen.Impl.UpdatePtrs`): in the promoted
/// objects, found through the forwarding array (`update_promoted_iter`), then
/// at the remembered slots (`rewrite_slots_iter`).  The model's collection
/// (`Spec.Pages.Promote.collect`) rewrites them in every block in use
/// (`update_pointers_with a.free`).  `two_pass`: they are the same, for any
/// allocator of the contract, given the write barrier's remembered set for
/// what counts as free for the allocator (`GC.Gen.RefTable`).
///
/// The proof is akhil's allocator-free `TwoPassEquiv.promoted_plus_slots_eq_walk`;
/// its hypotheses come from the loop invariant at the end of promotion
/// (`Promote.Sim`): the copies are blocks in use, distinct (injective
/// forwarding), so disjoint; an infix entry is an infix address of its
/// closure's copy; every block in use was in use before (with its fields)
/// or is a copy.  They mirror akhil's `TwoPassEquiv.Collect.derive_*`,
/// which take the same facts from his free list.

module GC.Spec.Pages.Promote.TwoPass

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.ForwardingArray
open GC.Gen.RefTable
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Promote
open GC.Spec.Pages.Promote.Loop

module U64 = FStar.UInt64
module Sim = GC.Spec.Pages.Promote.Sim
module C = GC.Spec.Pages.Promote.Collect
module CV = GC.Gen.CheneyGeneric
module TP = GC.Gen.TwoPassEquiv
module Aux = GC.Gen.PromoteUpdate.Aux
module ID = FStar.IndefiniteDescription
module ML = FStar.Math.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// What holds at the end of promotion.
let fin (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) : prop =
  ctx a minor g0 /\ linv a minor g0 cs /\ Sim.fwd_injective minor cs.fwd /\
  free_def_ok a.free /\ blocks_fit cs.major /\ no_infix_block cs.major /\
  CV.fwd_targets_not_free a.free cs.major cs.fwd

let fin_intro (a: tal pstate) (minor: minor_state) (g0: heap) (st0: pstate) (roots: seq U64.t)
  : Lemma (requires cpre a minor g0 st0)
          (ensures fin a minor g0 (promote a minor g0 st0 roots))
  = Sim.promote_sim a minor g0 st0 roots;
    Sim.sim_end a minor g0 (promote a minor g0 st0 roots);
    C.promoted a minor g0 st0 roots

/// ---------------------------------------------------------------------------
/// A forwarding entry
/// ---------------------------------------------------------------------------

/// A target that is not an infix address is the copy of a nursery object.
#push-options "--z3rlimit 30"
let target_copy (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (m: U64.t)
  : Lemma (requires fin a minor g0 cs /\ cs.fwd m <> 0UL /\
                    (U64.v (cs.fwd m) >= 8 /\ U64.v (cs.fwd m) < heap_size /\ U64.v (cs.fwd m) % 8 == 0) /\
                    ~(is_infix ((cs.fwd m) <: obj_addr) cs.major))
          (ensures ~(is_infix_in_minor minor m) /\ copy_of a minor g0 cs.major m (cs.fwd m))
  = assert (entry a minor g0 cs.major cs.fwd m);
    if is_infix_in_minor minor m then C.infix_target a minor g0 cs.major cs.fwd m
#pop-options

/// A copy is a block in use.
let copy_block (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (m: U64.t)
  : Lemma (requires fin a minor g0 cs /\ copy_of a minor g0 cs.major m (cs.fwd m))
          (ensures (let x : obj_addr = cs.fwd m in
                    in_use a.free cs.major x /\ Seq.mem x (objects zero_addr cs.major) /\
                    U64.v x + U64.v (wosize_of_object x cs.major) * 8 <= heap_size))
  = free_def_ok_elim a.free;
    wfh_part1_obj_bound cs.major (cs.fwd m)

/// The forwarding array at `i` is the entry of nursery word `i`.
let farr_at (farr: seq U64.t) (fwd: forwarding_map) (i: nat)
  : Lemma (requires represents_fwd farr fwd /\ i < fwd_array_size)
          (ensures Seq.index farr i == fwd (U64.uint_to_t (i * 8)))
  = ()

/// ---------------------------------------------------------------------------
/// The hypotheses of the two passes
/// ---------------------------------------------------------------------------

let body_words (x wz: nat)
  : Lemma (requires x % 8 == 0 /\ x + wz * 8 <= heap_size)
          (ensures forall (k: nat). k < wz ==> x + k * 8 + 8 <= heap_size /\ (x + k * 8) % 8 == 0)
  = let one (k: nat) : Lemma (k < wz ==> x + k * 8 + 8 <= heap_size /\ (x + k * 8) % 8 == 0)
      = if k < wz then begin
          ML.lemma_mult_le_right 8 (k + 1) wz;
          ML.modulo_addition_lemma x 8 k
        end
    in
    FStar.Classical.forall_intro one

#push-options "--z3rlimit 30"
let valid_from (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (farr: seq U64.t)
  : Lemma (requires fin a minor g0 cs /\ represents_fwd farr cs.fwd)
          (ensures promoted_entries_valid_from cs.major farr 0)
  = let one (i: nat{i < fwd_array_size})
      : Lemma (ensures (let obj = Seq.index farr i in
                        obj = 0UL \/
                        (U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
                         is_infix obj cs.major) \/
                        (U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
                         Seq.mem obj (objects zero_addr cs.major) /\
                         (let wz = U64.v (wosize_of_object obj cs.major) in
                          U64.v obj + wz * 8 <= heap_size /\
                          (forall (k: nat). k < wz ==>
                             (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0))))))
      = let m = U64.uint_to_t (i * 8) in
        farr_at farr cs.fwd i;
        let obj = Seq.index farr i in
        if obj <> 0UL && not (is_infix obj cs.major) then begin
          target_copy a minor g0 cs m;
          copy_block a minor g0 cs m;
          body_words (U64.v obj) (U64.v (wosize_of_object obj cs.major))
        end
    in
    FStar.Classical.forall_intro one
#pop-options

let inj_at (minor: minor_state) (fwd: forwarding_map) (m1 m2: U64.t)
  : Lemma (requires Sim.fwd_injective minor fwd /\ fwd m1 <> 0UL /\ fwd m1 == fwd m2 /\
                    ~(is_infix_in_minor minor m1) /\ ~(is_infix_in_minor minor m2))
          (ensures m1 == m2)
  = ()

#push-options "--z3rlimit 40"
let disjoint (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (farr: seq U64.t)
  : Lemma (requires fin a minor g0 cs /\ represents_fwd farr cs.fwd)
          (ensures promoted_entries_disjoint cs.major farr)
  = let one (i1: nat{i1 < fwd_array_size}) (i2: nat{i2 < fwd_array_size})
      : Lemma (requires i1 <> i2 /\
                        (let o1 = Seq.index farr i1 in
                         let o2 = Seq.index farr i2 in
                         o1 <> 0UL /\ o2 <> 0UL /\
                         U64.v o1 >= 8 /\ U64.v o2 >= 8 /\ U64.v o1 % 8 == 0 /\ U64.v o2 % 8 == 0 /\
                         U64.v o1 < heap_size /\ U64.v o2 < heap_size /\
                         is_infix o1 cs.major = false /\ is_infix o2 cs.major = false))
              (ensures (let o1 = Seq.index farr i1 in
                        let o2 = Seq.index farr i2 in
                        U64.v o1 + U64.v (wosize_of_object o1 cs.major) * 8 <= U64.v o2 \/
                        U64.v o2 + U64.v (wosize_of_object o2 cs.major) * 8 <= U64.v o1))
      = let m1 = U64.uint_to_t (i1 * 8) in
        let m2 = U64.uint_to_t (i2 * 8) in
        farr_at farr cs.fwd i1;
        farr_at farr cs.fwd i2;
        let o1 = Seq.index farr i1 in
        let o2 = Seq.index farr i2 in
        target_copy a minor g0 cs m1;
        target_copy a minor g0 cs m2;
        copy_block a minor g0 cs m1;
        copy_block a minor g0 cs m2;
        if U64.v o1 < U64.v o2 then objects_separated zero_addr cs.major o1 o2
        else if U64.v o2 < U64.v o1 then objects_separated zero_addr cs.major o2 o1
        else begin
          inj_at minor cs.fwd m1 m2;
          assert (i1 * 8 == i2 * 8)
        end
    in
    let two (i1 i2: nat)
      : Lemma (i1 < fwd_array_size /\ i2 < fwd_array_size /\ i1 <> i2 ==>
               (let o1 = Seq.index farr i1 in
                let o2 = Seq.index farr i2 in
                o1 <> 0UL /\ o2 <> 0UL /\
                U64.v o1 >= 8 /\ U64.v o2 >= 8 /\ U64.v o1 % 8 == 0 /\ U64.v o2 % 8 == 0 /\
                U64.v o1 < heap_size /\ U64.v o2 < heap_size /\
                is_infix o1 cs.major = false /\ is_infix o2 cs.major = false ==>
                U64.v o1 + U64.v (wosize_of_object o1 cs.major) * 8 <= U64.v o2 \/
                U64.v o2 + U64.v (wosize_of_object o2 cs.major) * 8 <= U64.v o1))
      = if i1 < fwd_array_size && i2 < fwd_array_size && i1 <> i2 then begin
          let o1 = Seq.index farr i1 in
          let o2 = Seq.index farr i2 in
          if o1 <> 0UL && o2 <> 0UL && U64.v o1 >= 8 && U64.v o2 >= 8 &&
             U64.v o1 % 8 = 0 && U64.v o2 % 8 = 0 && U64.v o1 < heap_size && U64.v o2 < heap_size &&
             is_infix o1 cs.major = false && is_infix o2 cs.major = false
          then one i1 i2
        end
    in
    FStar.Classical.forall_intro_2 two
#pop-options

#push-options "--z3rlimit 30"
let walked (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (farr: seq U64.t)
  : Lemma (requires fin a minor g0 cs /\ represents_fwd farr cs.fwd)
          (ensures TP.promoted_entries_walked cs.major (in_use a.free cs.major) farr)
  = let one (i: nat{i < fwd_array_size})
      : Lemma (requires (let obj = Seq.index farr i in
                         obj <> 0UL /\ U64.v obj >= U64.v mword /\ U64.v obj % U64.v mword == 0 /\
                         U64.v obj < heap_size /\ is_infix obj cs.major = false))
              (ensures in_use a.free cs.major ((Seq.index farr i) <: obj_addr))
      = farr_at farr cs.fwd i;
        target_copy a minor g0 cs (U64.uint_to_t (i * 8))
    in
    let two (i: nat)
      : Lemma (i < fwd_array_size ==>
               (let obj = Seq.index farr i in
                obj <> 0UL /\ U64.v obj >= U64.v mword /\ U64.v obj % U64.v mword == 0 /\
                U64.v obj < heap_size /\ is_infix obj cs.major = false ==>
                in_use a.free cs.major (obj <: obj_addr)))
      = if i < fwd_array_size then begin
          let obj = Seq.index farr i in
          if obj <> 0UL && U64.v obj >= U64.v mword && U64.v obj % U64.v mword = 0 &&
             U64.v obj < heap_size && is_infix obj cs.major = false
          then one i
        end
    in
    FStar.Classical.forall_intro two
#pop-options

/// A block in use before keeps its header, so its size and whether it is
/// scanned.
let old_block (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (obj: obj_addr)
  : Lemma (requires fin a minor g0 cs /\ in_use a.free g0 obj)
          (ensures in_use a.free cs.major obj /\ kept g0 cs.major obj /\
                   Seq.mem obj (objects zero_addr cs.major) /\
                   wosize_of_object obj cs.major == wosize_of_object obj g0 /\
                   is_no_scan obj cs.major == is_no_scan obj g0 /\
                   U64.v obj + U64.v (wosize_of_object obj cs.major) * 8 <= heap_size)
  = free_def_ok_elim a.free;
    Aux.header_eq_object_facts cs.major g0 obj;
    wfh_part1_obj_bound cs.major obj

#push-options "--z3rlimit 30"
let slots_walked (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
                 (slots: seq U64.t) (n: nat)
  : Lemma (requires fin a minor g0 cs /\ ref_table_sound_with a.free g0 slots n)
          (ensures TP.slots_rewrite_walked cs.major (in_use a.free cs.major) cs.fwd slots n)
  = let one (i: nat{i < n /\ n <= Seq.length slots})
      : Lemma (ensures (let ad = U64.v (Seq.index slots i) in
                        ad < heap_size /\ ad % 8 == 0 /\
                        TP.walked_field_addr cs.major (in_use a.free cs.major) ad))
      = let ad = U64.v (Seq.index slots i) in
        eliminate exists (obj: obj_addr) (j: nat).
          is_block g0 obj /\ not (a.free g0 obj) /\ scannable g0 obj /\
          j < U64.v (wosize_of_object obj g0) /\ ad == U64.v obj + j * 8
        with begin
          old_block a minor g0 cs obj;
          ML.lemma_mult_le_right 8 (j + 1) (U64.v (wosize_of_object obj g0));
          ML.modulo_addition_lemma (U64.v obj) 8 j
        end
    in
    FStar.Classical.forall_intro one
#pop-options

/// A nursery object's word index.
let word_index (m: U64.t)
  : Pure nat (requires U64.v m >= 8 /\ U64.v m < minor_heap_size /\ U64.v m % 8 == 0)
             (ensures fun i -> i < fwd_array_size /\ U64.uint_to_t (i * 8) == m)
  = ML.lemma_div_exact (U64.v m) 8;
    U64.v m / 8

#push-options "--z3rlimit 40"
let classified_one (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
                   (farr slots: seq U64.t) (n: nat) (obj: obj_addr) (j: nat)
  : Lemma (requires fin a minor g0 cs /\ represents_fwd farr cs.fwd /\ n <= Seq.length slots /\
                    ref_table_complete_with a.free g0 cs.fwd slots n /\
                    in_use a.free cs.major obj /\ is_no_scan obj cs.major = false /\
                    j < U64.v (wosize_of_object obj cs.major) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0 /\
                    (let fv = to_minor_offset (read_word cs.major (U64.uint_to_t (U64.v obj + j * 8))) in
                     is_minor_pointer fv /\ cs.fwd fv <> 0UL))
          (ensures (exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
                   (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8))
  = if in_use a.free g0 obj then begin
      old_block a minor g0 cs obj;
      let fa : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
      assert (read_word cs.major fa == read_word g0 fa)
    end else begin
      eliminate exists (m: U64.t). cs.fwd m == (obj <: U64.t) /\ copy_of a minor g0 cs.major m (obj <: U64.t)
      with begin
        minor_objects_valid minor m;
        let pi = word_index m in
        farr_at farr cs.fwd pi
      end
    end
#pop-options

let classified (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
               (farr slots: seq U64.t) (n: nat)
  : Lemma (requires fin a minor g0 cs /\ represents_fwd farr cs.fwd /\ n <= Seq.length slots /\
                    ref_table_complete_with a.free g0 cs.fwd slots n)
          (ensures TP.fwd_ptrs_classified_walked cs.major (in_use a.free cs.major) cs.fwd farr slots n)
  = let one (obj: obj_addr) (j: nat)
      : Lemma (Seq.mem obj (objects zero_addr cs.major) /\
               in_use a.free cs.major obj /\
               is_no_scan obj cs.major = false /\
               j < U64.v (wosize_of_object obj cs.major) /\
               U64.v obj + j * 8 + 8 <= heap_size /\
               (U64.v obj + j * 8) % 8 == 0 /\
               (let fv = to_minor_offset (read_word cs.major (U64.uint_to_t (U64.v obj + j * 8))) in
                is_minor_pointer fv /\ cs.fwd fv <> 0UL) ==>
               ((exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
                (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == U64.v obj + j * 8)))
      = FStar.Classical.move_requires (classified_one a minor g0 cs farr slots n obj) j
    in
    FStar.Classical.forall_intro_2 one

/// Every target is a major address, which no nursery pointer looks like.
#push-options "--z3rlimit 30"
let stable (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
  : Lemma (requires fin a minor g0 cs) (ensures fwd_targets_stable cs.fwd)
  = reveal_opaque (`%fwd_targets_stable) (fwd_targets_stable cs.fwd);
    zero_addr_above_minor ();
    free_def_ok_elim a.free;
    let one (x: U64.t)
      : Lemma (requires cs.fwd x <> 0UL)
              (ensures (let tg = cs.fwd x in
                        ~(is_minor_pointer (to_minor_offset tg) /\ cs.fwd (to_minor_offset tg) <> 0UL)))
      = let tg = cs.fwd x in
        assert (entry a minor g0 cs.major cs.fwd x);
        if is_infix_in_minor minor x then begin
          let p = infix_parent minor x in
          assert (copy_of a minor g0 cs.major p (cs.fwd p));
          copy_block a minor g0 cs p;
          objects_addresses_gt_start zero_addr cs.major (cs.fwd p)
        end else begin
          copy_block a minor g0 cs x;
          objects_addresses_gt_start zero_addr cs.major tg
        end;
        to_minor_offset_stable_above_minor tg
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

let valid_entries (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (farr: seq U64.t)
  : Lemma (requires fin a minor g0 cs /\ represents_fwd farr cs.fwd)
          (ensures valid_fwd_entries farr)
  = let one (i: nat{i < fwd_array_size})
      : Lemma (ensures (let ad = Seq.index farr i in
                                       ad == 0UL \/ (U64.v ad >= 8 /\ U64.v ad % 8 == 0 /\ U64.v ad <= heap_size)))
      = farr_at farr cs.fwd i
    in
    FStar.Classical.forall_intro one

/// **The two passes are the model's pointer update**: at the end of the
/// promotion `promote a`, with the forwarding array, and a remembered set
/// sound and covering for what the allocator counts as free.
#push-options "--z3rlimit 30"
let two_pass (a: tal pstate) (minor: minor_state) (g0: heap) (st0: pstate) (roots: seq U64.t)
             (farr slots: seq U64.t) (n: nat)
  : Lemma (requires cpre a minor g0 st0 /\
                    represents_fwd farr (promote a minor g0 st0 roots).fwd /\
                    ref_table_sound_with a.free g0 slots n /\ ref_table_covers_with a.free g0 slots n)
          (ensures (let cs = promote a minor g0 st0 roots in
                    Seq.length farr == fwd_array_size /\
                    valid_fwd_entries farr /\ valid_slot_addrs slots n /\
                    rewrite_slots_iter (update_promoted_iter cs.major farr cs.fwd 0) cs.fwd slots n 0 ==
                    update_pointers_with a.free cs.major cs.fwd))
  = let cs = promote a minor g0 st0 roots in
    fin_intro a minor g0 st0 roots;
    valid_entries a minor g0 cs farr;
    ref_table_sound_with_implies_valid_slot_addrs a.free g0 slots n;
    ref_table_covers_with_implies_complete a.free g0 cs.fwd slots n;
    valid_from a minor g0 cs farr;
    disjoint a minor g0 cs farr;
    walked a minor g0 cs farr;
    slots_walked a minor g0 cs slots n;
    classified a minor g0 cs farr slots n;
    stable a minor g0 cs;
    TP.promoted_plus_slots_eq_walk cs.major (in_use a.free cs.major) cs.fwd farr slots n
#pop-options
