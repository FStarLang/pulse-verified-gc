/// Helpers: promote_object read/chain preservation for OTHER objects — implementation
module GC.Gen.PromoteUpdate.PromoteFields.ReadOther

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// Numeric core of the "other object is untouched" argument.
///
/// `addr` lies inside `other`; `dst` is a different, non-overlapping object, so
/// none of `dst`'s header, fields or padding slot can alias `addr`.  Proved
/// from the raw offsets in an empty context: inside
/// `promote_object_read_other` these goals carry the whole well-formed-heap /
/// free-list context and time out.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let other_ranges_disjoint
  (other_v dst_v addr_v hd_dst_v wz_other wz wz_dst: nat)
  : Lemma
    (requires
      addr_v % 8 == 0 /\ other_v % 8 == 0 /\ dst_v % 8 == 0 /\
      hd_dst_v + 8 == dst_v /\ wz <= wz_dst /\
      addr_v >= other_v /\ addr_v + 8 <= other_v + wz_other * 8 /\
      (other_v < dst_v \/ dst_v < other_v) /\
      (other_v < dst_v ==> dst_v > other_v + wz_other * 8) /\
      (dst_v < other_v ==> other_v > dst_v + wz_dst * 8))
    (ensures
      (forall (k: nat). k < wz ==>
         (addr_v + 8 <= dst_v + k * 8 \/ dst_v + k * 8 + 8 <= addr_v)) /\
      addr_v <> dst_v + wz * 8 /\
      (addr_v + 8 <= hd_dst_v \/ hd_dst_v + 8 <= addr_v))
  = ()
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let promote_object_read_other
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (other: obj_addr) (addr: hp_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      Seq.mem other (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp other heap_words = true /\
      U64.v addr >= U64.v other /\
      U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8 /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures read_word (promote_object minor major obj fp wosize).major_out addr ==
             read_word major addr)
  = let fuel = heap_words in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let new_addr = alloc_res.obj_out in
    AllocLemmas.alloc_spec_read_other major fp wosize other addr;
    assert (read_word new_major addr == read_word major addr);
    GC.Gen.AllocProps.alloc_search_obj_in_objects_pre_part1 major fp zero_addr fp
      (if wosize = 0 then 1 else wosize) fuel;
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = new_addr in
    GC.Gen.AllocProps.alloc_spec_obj_ne_excl major fp wosize other;
    assert (new_addr <> other);
    GC.Gen.AllocProps.alloc_spec_obj_wosize_pre_part1 major fp wosize;
    assert (U64.v (wosize_of_object dst_obj major) >= wosize);
    hd_address_spec dst_obj;
    wfh_part1_obj_bound major dst_obj;
    let wz_other = U64.v (wosize_of_object other major) in
    let wz_dst = U64.v (wosize_of_object dst_obj major) in
    let disjoint () : Lemma
      (requires (U64.v other < U64.v dst_obj \/ U64.v dst_obj < U64.v other) /\
                (U64.v other < U64.v dst_obj ==>
                   U64.v dst_obj > U64.v other + wz_other * 8) /\
                (U64.v dst_obj < U64.v other ==>
                   U64.v other > U64.v dst_obj + wz_dst * 8))
      (ensures (forall (k: nat). k < wosize ==>
                  (U64.v addr + 8 <= U64.v dst_obj + k * 8 \/
                   U64.v dst_obj + k * 8 + 8 <= U64.v addr)) /\
               U64.v addr <> U64.v dst_obj + wosize * 8 /\
               (U64.v addr + U64.v mword <= U64.v (hd_address dst_obj) \/
                U64.v (hd_address dst_obj) + U64.v mword <= U64.v addr)) =
      other_ranges_disjoint (U64.v other) (U64.v dst_obj) (U64.v addr)
                            (U64.v (hd_address dst_obj)) wz_other wosize wz_dst
    in
    if U64.v other < U64.v new_addr then begin
      objects_separated zero_addr major other dst_obj;
      disjoint ();
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize addr
    end else begin
      objects_separated zero_addr major dst_obj other;
      disjoint ();
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize addr
    end;
    // Bridge: padding and set_promoted_tag preserve read at addr
    promote_object_success minor major obj fp wosize;
    let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    hd_address_injective other dst_obj;
    hd_address_spec dst_obj;
    zero_promote_padding_frame copied dst_obj wosize addr;
    let padded = zero_promote_padding copied dst_obj wosize in
    set_promoted_tag_read_frame padded dst_obj tag addr
#pop-options

/// Helper: read_word through copy_fields + zero_promote_padding + set_promoted_tag = read_word original
/// for objects other than dst_obj.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let promote_transfer_read
  (minor: minor_state) (new_major: heap) (obj: U64.t)
  (dst_obj: obj_addr) (wosize: nat{wosize > 0})
  (ao: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 new_major /\
      Seq.mem dst_obj (objects zero_addr new_major) /\
      Seq.mem ao (objects zero_addr new_major) /\
      ao <> dst_obj /\
      U64.v (wosize_of_object dst_obj new_major) >= wosize /\
      U64.v (wosize_of_object ao new_major) >= 1 /\
      dst_fields_valid dst_obj wosize /\
      minor_tag minor obj < 256)
    (ensures
      (let copied = copy_fields minor new_major obj dst_obj 0 wosize in
       let padded = zero_promote_padding copied dst_obj wosize in
       let tag = minor_tag minor obj in
       read_word (set_promoted_tag padded dst_obj tag) ao == read_word new_major ao))
  = let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    let padded = zero_promote_padding copied dst_obj wosize in
    let tag = minor_tag minor obj in
    hd_address_spec ao;
    hd_address_spec dst_obj;
    if U64.v ao < U64.v dst_obj then begin
      objects_separated zero_addr new_major ao dst_obj;
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize ao;
      zero_promote_padding_frame copied dst_obj wosize ao;
      set_promoted_tag_read_frame padded dst_obj tag ao
    end else begin
      objects_separated zero_addr new_major dst_obj ao;
      wosize_of_object_spec dst_obj new_major;
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize ao;
      zero_promote_padding_frame copied dst_obj wosize ao;
      set_promoted_tag_read_frame padded dst_obj tag ao
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let promote_object_preserves_chain_avoids
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (excl: U64.t)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      AllocLemmas.chain_avoids major fp excl heap_words = true /\
      U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
      U64.v excl % U64.v mword == 0 /\
      Seq.mem (excl <: obj_addr) (objects zero_addr major) /\
      U64.v (wosize_of_object (excl <: obj_addr) major) >= 1 /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wosize in
       AllocLemmas.chain_avoids res.major_out res.fp_out excl heap_words = true))
  = let fuel = heap_words in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let new_fp = alloc_res.fp_out in
    let dst = alloc_res.obj_out in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = dst in
    AllocLemmas.alloc_spec_preserves_chain_avoids_other major fp wosize excl;
    assert (AllocLemmas.chain_avoids new_major new_fp excl fuel = true);
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
    assert (AllocLemmas.chain_avoids new_major new_fp dst_obj fuel = true);
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
    assert (AllocLemmas.fl_valid new_major new_fp fuel);
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    assert (well_formed_heap_part1 new_major);
    promote_object_success minor major obj fp wosize;
    let copied = copy_fields minor new_major obj dst_obj 0 wosize in
    let padded = zero_promote_padding copied dst_obj wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    assert (Seq.mem dst_obj (objects zero_addr new_major));
    assert (U64.v (wosize_of_object dst_obj new_major) >= wosize);
    hd_address_spec dst_obj;
    assert (U64.v dst_obj + wosize * 8 <= heap_size);
    dst_fields_valid_from_bounds dst_obj wosize;
    let transfer_helper (a: hp_addr) : Lemma
      (requires U64.v a >= U64.v mword /\
               Seq.mem a (objects zero_addr new_major) /\ a <> excl /\ a <> dst_obj /\
               U64.v (wosize_of_object (a <: obj_addr) new_major) >= 1 /\
               U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size)
      (ensures read_word (set_promoted_tag padded dst_obj tag) a == read_word new_major a)
    = promote_transfer_read minor new_major obj dst_obj wosize (a <: obj_addr)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_helper);
    AllocLemmas.chain_avoids_transfer_excl2 new_major (set_promoted_tag padded dst_obj tag) new_fp excl dst_obj fuel
#pop-options

/// Build an `hp_addr` from a raw offset.  The bounds and alignment obligations
/// are trivial, but under the enclosing well-formed-heap context they are not
/// discharged in time; proving them here keeps the caller's goals small.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let mk_hp_addr (a: nat{a < heap_size /\ a % 8 == 0}) : (r: hp_addr{U64.v r == a}) =
  assert (a < pow2 64);
  U64.uint_to_t a
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let promote_object_preserves_one_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0})
  (prev_addr: obj_addr) (j: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      Seq.mem prev_addr (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp prev_addr heap_words = true /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      U64.v prev_addr + j * 8 + 8 <= heap_size /\
      U64.v prev_addr % 8 == 0 /\
      U64.v prev_addr + j * 8 < U64.v prev_addr + U64.v (wosize_of_object prev_addr major) * 8)
    (ensures read_word (promote_object minor major obj fp wz).major_out
                       (U64.uint_to_t (U64.v prev_addr + j * 8)) ==
             read_word major (U64.uint_to_t (U64.v prev_addr + j * 8)))
  = let field_addr : hp_addr = mk_hp_addr (U64.v prev_addr + j * 8) in
    promote_object_read_other minor major obj fp wz prev_addr field_addr
#pop-options
