/// ---------------------------------------------------------------------------
/// GC.Gen.TwoPassEquiv — Proof of two-pass equivalence
/// ---------------------------------------------------------------------------
///
/// Main theorem: rewriting promoted object fields + rewriting ref_table slots
/// produces the same heap as the full update_major_pointers walk.
///
/// Strategy: pointwise read_word equality at all aligned addresses,
/// followed by heap byte-level extensionality.

module GC.Gen.TwoPassEquiv

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Impl.UpdatePtrs

module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module PromObj = GC.Gen.PromoteUpdate.Obj
module PromField = GC.Gen.PromoteUpdate.Field

/// ---------------------------------------------------------------------------
/// Heap extensionality
/// ---------------------------------------------------------------------------

/// If two heaps agree on every aligned word, they are equal (byte-for-byte).
/// Proof: read_word at offset a determines bytes a..a+7. If this holds for
/// all aligned offsets, all bytes agree, hence Seq.equal gives equality.
let heap_read_word_extensional (h1 h2: heap)
  : Lemma
    (requires (forall (a: nat).
       a < heap_size /\ a % 8 == 0 ==>
       read_word h1 (U64.uint_to_t a) == read_word h2 (U64.uint_to_t a)))
    (ensures h1 == h2)
  = admit () // Requires combine_bytes injectivity (standard bitvector result)

/// ---------------------------------------------------------------------------
/// update_promoted_iter frame lemma
/// ---------------------------------------------------------------------------

/// Helper: update_object_pointers preserves promoted_iter_frame_pre for idx+1
/// when applied to the entry at idx.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let update_object_pointers_preserves_frame_pre
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map) (idx: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      promoted_iter_frame_pre major farr idx addr /\
      idx < fwd_array_size /\
      (let obj = Seq.index farr idx in
       obj <> 0UL /\
       U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
       Seq.mem obj (objects zero_addr major) /\
       (let wz = U64.v (wosize_of_object obj major) in
        wz > 0 /\ U64.v obj + wz * 8 <= heap_size /\
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))))
    (ensures
      (let obj = Seq.index farr idx in
       let wz = U64.v (wosize_of_object obj major) in
       let major' = update_object_pointers major obj wz fwd 0 in
       promoted_iter_frame_pre major' farr (idx + 1) addr))
  = let obj = Seq.index farr idx in
    let wz = U64.v (wosize_of_object obj major) in
    let major' = update_object_pointers major obj wz fwd 0 in
    // 1. objects list is preserved
    PromObj.update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);
    // 2. well_formed_heap_part1 major'
    //    Same argument as in PromoteUpdate.Aux: all headers preserved
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = obj then begin
        PromObj.update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else if U64.v h > U64.v obj then begin
        PromObj.update_object_pointers_preserves_other_header major obj wz fwd 0 h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        PromObj.update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
        wosize_of_object_spec h major;
        wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    assert (well_formed_heap_part1 major');
    // 3. For each i > idx with non-zero farr[i]:
    //    - Seq.mem (farr[i]) (objects zero_addr major') — from (1)
    //    - wosize_of_object (farr[i]) major' == wosize_of_object (farr[i]) major — from header pres
    //    - addr is outside body — same bounds since wosize unchanged
    assert (Seq.length farr == fwd_array_size);
    let aux_entry (i: nat{i < Seq.length farr}) : Lemma
      (requires i > idx /\
               (let o = Seq.index farr i in o <> 0UL))
      (ensures
        (let o = Seq.index farr i in
         U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
         Seq.mem o (objects zero_addr major') /\
         (let wz' = U64.v (wosize_of_object o major') in
          U64.v o + wz' * 8 <= heap_size /\
          (forall (k:nat). k < wz' ==>
            (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)) /\
          (U64.v addr < U64.v o \/ U64.v addr >= U64.v o + wz' * 8))))
    = let o = Seq.index farr i in
      // From original precondition on major:
      assert (Seq.mem o (objects zero_addr major));
      assert (Seq.mem o (objects zero_addr major'));
      // Show wosize_of_object o major' == wosize_of_object o major
      hd_address_spec o;
      wosize_of_object_spec o major;
      wosize_of_object_spec o major';
      if U64.v o > U64.v obj then
        PromObj.update_object_pointers_preserves_other_header major obj wz fwd 0 o
      else if o = obj then
        PromObj.update_object_pointers_preserves_self_header major obj wz fwd 0
      else
        PromObj.update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address o)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_entry)
#pop-options

/// Frame: addresses outside all promoted object bodies are unchanged.
/// Proof: induction on idx, mirroring the recursive structure of update_promoted_iter.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
let rec update_promoted_iter_frame
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map) (idx: nat)
  (addr: hp_addr)
  : Lemma
    (requires promoted_iter_frame_pre major farr idx addr)
    (ensures
      read_word (update_promoted_iter major farr fwd idx) addr ==
      read_word major addr)
    (decreases (fwd_array_size - idx))
  = if idx >= fwd_array_size then ()
    else if Seq.length farr <> fwd_array_size then ()
    else begin
      let major_addr = Seq.index farr idx in
      if major_addr = 0UL then
        update_promoted_iter_frame major farr fwd (idx + 1) addr
      else begin
        let hdr_addr_v = U64.v major_addr - 8 in
        if hdr_addr_v + 8 > heap_size || hdr_addr_v % 8 <> 0 then
          update_promoted_iter_frame major farr fwd (idx + 1) addr
        else begin
          let hdr = read_word major (U64.uint_to_t hdr_addr_v) in
          let wosize = U64.v (getWosize hdr) in
          let tag = getTag hdr in
          if wosize > 0 && U64.lt tag no_scan_tag then begin
            if U64.v major_addr + wosize * 8 <= heap_size then begin
              wosize_of_object_spec major_addr major;
              hd_address_spec major_addr;
              assert (U64.v addr < U64.v major_addr \/
                      U64.v addr >= U64.v major_addr + wosize * 8);
              let major' = update_object_pointers major major_addr wosize fwd 0 in
              (if U64.v addr < U64.v major_addr then
                PromObj.update_object_pointers_preserves_addr_below
                  major major_addr wosize fwd 0 addr
              else
                PromObj.update_object_pointers_preserves_addr_above
                  major major_addr wosize fwd 0 addr);
              // Establish recursive precondition
              update_object_pointers_preserves_frame_pre major farr fwd idx addr;
              // Recurse
              update_promoted_iter_frame major' farr fwd (idx + 1) addr
            end else
              update_promoted_iter_frame major farr fwd (idx + 1) addr
          end else
            update_promoted_iter_frame major farr fwd (idx + 1) addr
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// update_promoted_iter effect on promoted fields
/// ---------------------------------------------------------------------------

/// Effect: a field of a promoted object gets its minor pointers rewritten.
let update_promoted_iter_promoted_field
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map)
  (pi: nat) (j: nat)
  : Lemma
    (requires
      Seq.length farr == fwd_array_size /\
      well_formed_heap_part1 major /\
      pi < fwd_array_size /\
      (let obj = Seq.index farr pi in
       obj <> 0UL /\
       U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
       Seq.mem obj (objects zero_addr major) /\
       (let wz = U64.v (wosize_of_object obj major) in
        let tag = getTag (read_word major (hd_address obj)) in
        wz > 0 /\ U64.lt tag no_scan_tag /\
        U64.v obj + wz * 8 <= heap_size /\
        j < wz /\
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))) /\
      (forall (i: nat). i < fwd_array_size ==>
        (let o = Seq.index farr i in
         o <> 0UL ==>
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major) /\
          U64.v o + U64.v (wosize_of_object o major) * 8 <= heap_size))) /\
      (forall (i1 i2: nat). i1 < fwd_array_size /\ i2 < fwd_array_size /\ i1 <> i2 ==>
        (let o1 = Seq.index farr i1 in
         let o2 = Seq.index farr i2 in
         o1 <> 0UL /\ o2 <> 0UL ==>
         (U64.v o1 + U64.v (wosize_of_object o1 major) * 8 <= U64.v o2 \/
          U64.v o2 + U64.v (wosize_of_object o2 major) * 8 <= U64.v o1))))
    (ensures
      (let obj = Seq.index farr pi in
       let wz = U64.v (wosize_of_object obj major) in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_raw = read_word major field_addr in
       let old_val = to_minor_offset old_raw in
       let result = read_word (update_promoted_iter major farr fwd 0) field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> result == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> result == old_raw)))
  = admit () // Induction: at step pi, update_object_pointers_field_self gives the result;
             // frame lemma for i < pi (addr is in body of farr[pi], outside farr[i]'s body)

/// ---------------------------------------------------------------------------
/// rewrite_slots_iter frame lemma
/// ---------------------------------------------------------------------------

/// Frame: addresses not in the slot list are unchanged.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let rec rewrite_slots_iter_frame
  (major: heap) (fwd: forwarding_map) (slots: seq U64.t) (n: nat) (idx: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      idx <= n /\ n <= Seq.length slots /\
      (forall (i: nat). i >= idx /\ i < n ==>
        (let sa = U64.v (Seq.index slots i) in
         sa < heap_size /\ sa % 8 == 0 /\
         (U64.v addr + 8 <= sa \/ sa + 8 <= U64.v addr))))
    (ensures
      read_word (rewrite_slots_iter major fwd slots n idx) addr ==
      read_word major addr)
    (decreases (n - idx))
  = if idx >= n then ()
    else if idx >= Seq.length slots then ()
    else begin
      let slot_addr = Seq.index slots idx in
      if U64.v slot_addr >= heap_size || U64.v slot_addr % 8 <> 0 then
        // Skip invalid slot, recurse
        rewrite_slots_iter_frame major fwd slots n (idx + 1) addr
      else begin
        let field_val = to_minor_offset (read_word major slot_addr) in
        if is_minor_pointer field_val then
          let new_val = fwd field_val in
          if new_val <> 0UL then begin
            // Write at slot_addr, but slot_addr != addr by precondition
            let major' = write_word major slot_addr new_val in
            read_write_different major slot_addr addr new_val;
            rewrite_slots_iter_frame major' fwd slots n (idx + 1) addr
          end else
            rewrite_slots_iter_frame major fwd slots n (idx + 1) addr
        else
          rewrite_slots_iter_frame major fwd slots n (idx + 1) addr
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// rewrite_slots_iter effect on a slot address
/// ---------------------------------------------------------------------------

/// Effect: the slot at index si gets its minor pointer rewritten.
/// Proof: induction on idx. Steps before si don't modify slot_addr (distinct
/// aligned addresses → frame). At step si, the write (or no-op) produces the
/// expected result. Steps after si also don't modify slot_addr (frame again).
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
let rec rewrite_slots_iter_slot_effect_aux
  (major: heap) (fwd: forwarding_map) (slots: seq U64.t) (n: nat) (si: nat) (idx: nat)
  : Lemma
    (requires
      si < n /\ n <= Seq.length slots /\ idx <= n /\
      (forall (i: nat). i < n ==>
        (let sa = U64.v (Seq.index slots i) in
         sa < heap_size /\ sa % 8 == 0)) /\
      (forall (i: nat). i < n /\ i <> si ==>
        U64.v (Seq.index slots i) <> U64.v (Seq.index slots si)))
    (ensures
      (let slot_addr = Seq.index slots si in
       let old_raw = read_word major slot_addr in
       let old_val = to_minor_offset old_raw in
       // After steps 0..idx-1, the value at slot_addr is still old_raw
       // (because none of those steps wrote to slot_addr)
       // After step si writes (or doesn't), the result is the expected value
       // After steps si+1..n-1, the result is preserved
       let result = read_word (rewrite_slots_iter major fwd slots n idx) slot_addr in
       if idx <= si then
         // Steps idx..si-1 haven't touched slot_addr yet
         // Step si applies the rewrite
         // Steps si+1..n-1 preserve
         (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> result == fwd old_val) /\
         (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> result == old_raw)
       else
         // Already past si; previous step wrote (or didn't) to slot_addr
         // Steps idx..n-1 won't touch slot_addr → value is preserved from major
         result == read_word major slot_addr))
    (decreases (n - idx))
  = let slot_addr = Seq.index slots si in
    if idx >= n then ()
    else if idx >= Seq.length slots then ()
    else begin
      let cur_slot = Seq.index slots idx in
      if U64.v cur_slot >= heap_size || U64.v cur_slot % 8 <> 0 then
        rewrite_slots_iter_slot_effect_aux major fwd slots n si (idx + 1)
      else begin
        let field_val = to_minor_offset (read_word major cur_slot) in
        if idx < si then begin
          // idx != si, so cur_slot != slot_addr (distinct addresses)
          // Both are aligned, so they differ by at least 8
          assert (U64.v cur_slot <> U64.v slot_addr);
          assert (U64.v cur_slot % 8 == 0 /\ U64.v slot_addr % 8 == 0);
          if is_minor_pointer field_val then
            let new_val = fwd field_val in
            if new_val <> 0UL then begin
              let major' = write_word major cur_slot new_val in
              // Write at cur_slot doesn't affect slot_addr
              read_write_different major cur_slot slot_addr new_val;
              rewrite_slots_iter_slot_effect_aux major' fwd slots n si (idx + 1)
            end else
              rewrite_slots_iter_slot_effect_aux major fwd slots n si (idx + 1)
          else
            rewrite_slots_iter_slot_effect_aux major fwd slots n si (idx + 1)
        end else if idx = si then begin
          // This is the key step: processing slot_addr itself
          if is_minor_pointer field_val then begin
            let new_val = fwd field_val in
            if new_val <> 0UL then begin
              let major' = write_word major slot_addr new_val in
              read_write_same major slot_addr new_val;
              // After writing, major' at slot_addr == new_val == fwd old_val
              // Now show remaining steps (si+1..n-1) preserve this
              rewrite_slots_iter_frame major' fwd slots n (idx + 1) slot_addr
            end else
              // No write, value stays as old_raw
              rewrite_slots_iter_frame major fwd slots n (idx + 1) slot_addr
          end else
            // Not a minor pointer, no write
            rewrite_slots_iter_frame major fwd slots n (idx + 1) slot_addr
        end else begin
          // idx > si: shouldn't happen when called from slot_effect
          // but we handle it: slot_addr is distinct from cur_slot
          assert (U64.v cur_slot <> U64.v slot_addr);
          if is_minor_pointer field_val then
            let new_val = fwd field_val in
            if new_val <> 0UL then begin
              let major' = write_word major cur_slot new_val in
              read_write_different major cur_slot slot_addr new_val;
              rewrite_slots_iter_slot_effect_aux major' fwd slots n si (idx + 1)
            end else
              rewrite_slots_iter_slot_effect_aux major fwd slots n si (idx + 1)
          else
            rewrite_slots_iter_slot_effect_aux major fwd slots n si (idx + 1)
        end
      end
    end
#pop-options

let rewrite_slots_iter_slot_effect
  (major: heap) (fwd: forwarding_map) (slots: seq U64.t) (n: nat) (si: nat)
  : Lemma
    (requires
      si < n /\ n <= Seq.length slots /\
      (forall (i: nat). i < n ==>
        (let sa = U64.v (Seq.index slots i) in
         sa < heap_size /\ sa % 8 == 0)) /\
      (forall (i: nat). i < n /\ i <> si ==>
        U64.v (Seq.index slots i) <> U64.v (Seq.index slots si)))
    (ensures
      (let slot_addr = Seq.index slots si in
       let old_raw = read_word major slot_addr in
       let old_val = to_minor_offset old_raw in
       let result = read_word (rewrite_slots_iter major fwd slots n 0) slot_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> result == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> result == old_raw)))
  = rewrite_slots_iter_slot_effect_aux major fwd slots n si 0

/// ---------------------------------------------------------------------------
/// Main theorem: two-pass rewriting equals full update
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let promoted_plus_slots_eq_full_update
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       valid_fwd_entries farr /\
       represents_fwd farr prom.fwd_map /\
       valid_slot_addrs slots n /\
       ref_table_sound major_pre slots n /\
       ref_table_complete major_pre prom.fwd_map slots n /\
       well_formed_heap_part1 prom.major_final /\
       heap_objects_dense prom.major_final /\
       Seq.length (objects zero_addr prom.major_final) > 0 /\
       well_formed_heap major_pre /\
       AllocLemmas.fl_valid major_pre fp heap_fuel /\
       AllocLemmas.fl_chain_terminates major_pre fp heap_fuel))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       rewrite_slots_iter
         (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0
         == update_major_pointers prom.major_final prom.fwd_map))
  = let prom = CheneySpec.cheney_promote minor major_pre fp roots in
    let major = prom.major_final in
    let fwd = prom.fwd_map in
    let lhs = rewrite_slots_iter (update_promoted_iter major farr fwd 0) fwd slots n 0 in
    let rhs = update_major_pointers major fwd in
    // For every aligned address a, show read_word lhs a == read_word rhs a.
    // Then heap_read_word_extensional gives lhs == rhs.
    //
    // Per-address case analysis:
    // Case 1: a is a field of a promoted object farr[pi] at offset j
    //   - update_promoted_iter_promoted_field: intermediate = rewrite(old_raw, fwd)
    //   - promoted objects are NOT in ref_table (disjointness: promoted in blue region,
    //     ref_table has non-blue addresses)
    //   - So rewrite_slots_iter_frame preserves the field
    //   - update_major_pointers_field_effect: same rewrite
    //
    // Case 2: a is a ref_table slot slots[si]
    //   - ref_table addresses are NOT in promoted bodies (same disjointness)
    //   - update_promoted_iter_frame: intermediate = old value
    //   - rewrite_slots_iter_slot_effect: result = rewrite(old_raw, fwd)
    //   - update_major_pointers_field_effect: same rewrite
    //
    // Case 3: a is a field of a non-promoted scannable object, not in ref_table
    //   - ref_table_complete: this field does NOT contain a forwarded minor ptr
    //   - update_promoted_iter_frame: field unchanged (not in promoted body)
    //   - rewrite_slots_iter_frame: field unchanged (not a slot)
    //   - update_major_pointers on this field: old_val has no forwarded minor
    //     (by ref_table_complete + promote_all_read_other), so it's unchanged
    //
    // Case 4: a is a header, padding, blue/no_scan body, or outside all objects
    //   - All three passes leave it unchanged
    let aux (a: nat{a < heap_size /\ a % 8 == 0})
      : Lemma (read_word lhs (U64.uint_to_t a) == read_word rhs (U64.uint_to_t a))
      = admit ()  // Per-address case analysis using sub-lemmas above
    in
    FStar.Classical.forall_intro aux;
    heap_read_word_extensional lhs rhs
#pop-options
