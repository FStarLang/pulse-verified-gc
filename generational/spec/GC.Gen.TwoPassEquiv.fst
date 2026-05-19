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
module HeapExt = GC.Gen.HeapExtensional
module IndDesc = FStar.IndefiniteDescription

/// ---------------------------------------------------------------------------
/// Heap extensionality — delegates to GC.Gen.HeapExtensional
/// ---------------------------------------------------------------------------

let heap_read_word_extensional (h1 h2: heap)
  : Lemma
    (requires (forall (a: nat).
       a < heap_size /\ a % 8 == 0 ==>
       read_word h1 (U64.uint_to_t a) == read_word h2 (U64.uint_to_t a)))
    (ensures h1 == h2)
  = HeapExt.heap_read_word_ext h1 h2

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

/// Small helper: update_object_pointers on entry preserves a field_addr that is
/// outside entry's body (either below or above).
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let update_object_pointers_preserves_disjoint_field
  (major: heap) (entry: obj_addr) (wz_e: nat) (fwd: forwarding_map)
  (field_addr: hp_addr)
  : Lemma
    (requires
      Seq.mem entry (objects zero_addr major) /\
      U64.v entry % 8 == 0 /\
      wz_e == U64.v (wosize_of_object entry major) /\
      (U64.v field_addr < U64.v entry \/
       U64.v field_addr >= U64.v entry + wz_e * 8) /\
      (forall (k:nat). k < wz_e ==>
        (U64.v entry + k * 8 + 8 <= heap_size /\ (U64.v entry + k * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major entry wz_e fwd 0) field_addr ==
      read_word major field_addr)
  = if U64.v field_addr < U64.v entry then
      PromObj.update_object_pointers_preserves_addr_below major entry wz_e fwd 0 field_addr
    else
      PromObj.update_object_pointers_preserves_addr_above major entry wz_e fwd 0 field_addr
#pop-options

/// Small helper: update_object_pointers on entry preserves header of another
/// object that comes after it in the heap.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let update_object_pointers_preserves_other_obj_header
  (major: heap) (entry: obj_addr) (wz_e: nat) (fwd: forwarding_map)
  (other: obj_addr)
  : Lemma
    (requires
      Seq.mem entry (objects zero_addr major) /\
      Seq.mem other (objects zero_addr major) /\
      U64.v entry % 8 == 0 /\
      other <> entry /\
      wz_e == U64.v (wosize_of_object entry major) /\
      (forall (k:nat). k < wz_e ==>
        (U64.v entry + k * 8 + 8 <= heap_size /\ (U64.v entry + k * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major entry wz_e fwd 0) (hd_address other) ==
      read_word major (hd_address other))
  = if U64.v other > U64.v entry then
      PromObj.update_object_pointers_preserves_other_header major entry wz_e fwd 0 other
    else begin
      // other < entry => hd_address other < other < entry
      hd_address_spec other;
      PromObj.update_object_pointers_preserves_addr_below major entry wz_e fwd 0 (hd_address other)
    end
#pop-options

/// Helper: after processing entry idx (which is != pi), the promoted_field_aux
/// precondition holds for the updated heap at idx+1.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
private let update_object_pointers_preserves_promoted_field_pre
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map)
  (pi: nat) (j: nat) (idx: nat)
  : Lemma
    (requires
      Seq.length farr == fwd_array_size /\
      well_formed_heap_part1 major /\
      pi < fwd_array_size /\ idx < pi /\
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
      (let entry = Seq.index farr idx in
       entry <> 0UL /\
       U64.v entry >= U64.v mword /\ U64.v entry % 8 == 0 /\ U64.v entry < heap_size /\
       Seq.mem entry (objects zero_addr major) /\
       (let wz_e = U64.v (wosize_of_object entry major) in
        U64.v entry + wz_e * 8 <= heap_size /\
        (forall (k:nat). k < wz_e ==>
          (U64.v entry + k * 8 + 8 <= heap_size /\ (U64.v entry + k * 8) % 8 == 0)))) /\
      // All entries from idx onward are valid
      (forall (i: nat). i >= idx /\ i < fwd_array_size ==>
        (let o = Seq.index farr i in
         o = 0UL \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major) /\
          (let wz_o = U64.v (wosize_of_object o major) in
           U64.v o + wz_o * 8 <= heap_size /\
           (forall (k:nat). k < wz_o ==>
             (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)))))) /\
      // Disjointness
      (forall (i1 i2: nat). i1 >= idx /\ i1 < fwd_array_size /\ i2 >= idx /\ i2 < fwd_array_size /\ i1 <> i2 ==>
        (let o1 = Seq.index farr i1 in
         let o2 = Seq.index farr i2 in
         o1 <> 0UL /\ o2 <> 0UL ==>
         (U64.v o1 + U64.v (wosize_of_object o1 major) * 8 <= U64.v o2 \/
          U64.v o2 + U64.v (wosize_of_object o2 major) * 8 <= U64.v o1))))
    (ensures
      (let entry = Seq.index farr idx in
       let wz_e = U64.v (wosize_of_object entry major) in
       let major' = update_object_pointers major entry wz_e fwd 0 in
       let obj = Seq.index farr pi in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       // Field is preserved
       read_word major' field_addr == read_word major field_addr /\
       // Precondition transfers to major' at idx+1
       well_formed_heap_part1 major' /\
       Seq.mem obj (objects zero_addr major') /\
       wosize_of_object obj major' == wosize_of_object obj major /\
       read_word major' (hd_address obj) == read_word major (hd_address obj) /\
       (forall (i: nat). i >= (idx + 1) /\ i < fwd_array_size ==>
         (let o = Seq.index farr i in
          o = 0UL \/
          (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
           Seq.mem o (objects zero_addr major') /\
           (let wz_o = U64.v (wosize_of_object o major') in
            wz_o == U64.v (wosize_of_object o major) /\
            U64.v o + wz_o * 8 <= heap_size /\
            (forall (k:nat). k < wz_o ==>
              (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0))))))))
  = let entry = Seq.index farr idx in
    let obj = Seq.index farr pi in
    let wz_e = U64.v (wosize_of_object entry major) in
    let major' = update_object_pointers major entry wz_e fwd 0 in
    let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
    // Establish subtyping for entry : obj_addr and field_addr : hp_addr
    assert (U64.v entry >= U64.v mword /\ U64.v entry < heap_size /\ U64.v entry % 8 == 0);
    assert (U64.v field_addr < heap_size /\ U64.v field_addr % 8 == 0);
    let entry_o : obj_addr = entry in
    let field_hp : hp_addr = field_addr in
    // Objects list preserved
    PromObj.update_object_pointers_preserves_objects major entry_o wz_e fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);
    // field_addr is in obj's body, which is disjoint from entry's body
    let wz_obj = U64.v (wosize_of_object obj major) in
    assert (U64.v obj + wz_obj * 8 <= U64.v entry \/
            U64.v entry + wz_e * 8 <= U64.v obj);
    assert (U64.v field_addr >= U64.v obj);
    assert (U64.v field_addr < U64.v obj + wz_obj * 8);
    // Field is preserved (outside entry's body)
    assert (U64.v field_hp < U64.v entry_o \/
            U64.v field_hp >= U64.v entry_o + wz_e * 8);
    update_object_pointers_preserves_disjoint_field major entry_o wz_e fwd field_hp;
    // Header of obj is preserved (obj != entry, so header preserved)
    assert (U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0);
    let obj_o : obj_addr = obj in
    assert (obj_o <> entry_o);  // pi != idx so farr[pi] != farr[idx] ... hmm, not necessarily
    // Actually: we need obj != entry. This follows from disjointness + non-zero
    // Since pi != idx, and both farr[pi] != 0 and farr[idx] != 0, by the disjointness
    // condition with i1=idx, i2=pi: bodies don't overlap, hence addresses differ
    assert (U64.v entry_o + wz_e * 8 <= U64.v obj_o \/ U64.v obj_o + U64.v (wosize_of_object obj_o major) * 8 <= U64.v entry_o);
    assert (obj_o <> entry_o);
    update_object_pointers_preserves_other_obj_header major entry_o wz_e fwd obj_o;
    hd_address_spec obj_o;
    wosize_of_object_spec obj_o major;
    wosize_of_object_spec obj_o major';
    // well_formed_heap_part1 major' (same pattern as update_object_pointers_preserves_frame_pre)
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = entry_o then begin
        PromObj.update_object_pointers_preserves_self_header major entry_o wz_e fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        // h != entry, so header preserved by other_obj_header helper
        update_object_pointers_preserves_other_obj_header major entry_o wz_e fwd h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    // For each entry i > idx: wosize preserved in major'
    let aux_entry (i: nat{i < Seq.length farr}) : Lemma
      (requires i > idx /\
               (let o = Seq.index farr i in
                o <> 0UL /\
                U64.v o >= U64.v mword /\ U64.v o % U64.v mword == 0 /\ U64.v o < heap_size))
      (ensures
        (let o = Seq.index farr i in
         U64.v o >= U64.v mword /\ U64.v o % U64.v mword == 0 /\ U64.v o < heap_size /\
         Seq.mem o (objects zero_addr major') /\
         wosize_of_object o major' == wosize_of_object o major))
    = let o = Seq.index farr i in
      assert (Seq.mem o (objects zero_addr major));
      assert (Seq.mem o (objects zero_addr major'));
      // Two cases: either o == entry_o or o <> entry_o
      if o = entry_o then begin
        // o is the same object as entry; its header is preserved by self-preservation
        PromObj.update_object_pointers_preserves_self_header major entry_o wz_e fwd 0;
        hd_address_spec o;
        wosize_of_object_spec o major;
        wosize_of_object_spec o major'
      end else begin
        update_object_pointers_preserves_other_obj_header major entry_o wz_e fwd o;
        hd_address_spec o;
        wosize_of_object_spec o major;
        wosize_of_object_spec o major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_entry)
#pop-options

/// Effect: a field of a promoted object gets its minor pointers rewritten.
/// Proof: induction on idx. For entries before pi, the field is outside their
/// bodies (disjointness) so it's preserved. At entry pi, field_self gives the
/// rewrite. For entries after pi, frame preserves the result.
#push-options "--z3rlimit 150 --fuel 1 --ifuel 0 --split_queries always"
private let rec update_promoted_iter_promoted_field_aux
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map)
  (pi: nat) (j: nat) (idx: nat)
  : Lemma
    (requires
      Seq.length farr == fwd_array_size /\
      well_formed_heap_part1 major /\
      pi < fwd_array_size /\ idx <= pi /\
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
      // All entries are valid objects
      (forall (i: nat). i >= idx /\ i < fwd_array_size ==>
        (let o = Seq.index farr i in
         o = 0UL \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major) /\
          (let wz_o = U64.v (wosize_of_object o major) in
           U64.v o + wz_o * 8 <= heap_size /\
           (forall (k:nat). k < wz_o ==>
             (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)))))) /\
      // Disjointness of bodies
      (forall (i1 i2: nat). i1 >= idx /\ i1 < fwd_array_size /\ i2 >= idx /\ i2 < fwd_array_size /\ i1 <> i2 ==>
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
       let result = read_word (update_promoted_iter major farr fwd idx) field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> result == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> result == old_raw)))
    (decreases (pi - idx))
  = let obj = Seq.index farr pi in
    let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
    let entry = Seq.index farr idx in
    if idx = pi then begin
      // --- Base case: at the target entry ---
      // Unfold update_promoted_iter at pi (scan case)
      hd_address_spec obj;
      wosize_of_object_spec obj major;
      let wz = U64.v (wosize_of_object obj major) in
      update_promoted_iter_scan major farr fwd idx;
      let major' = update_object_pointers major obj wz fwd 0 in
      // field_self: the field at j gets rewritten as expected
      PromObj.update_object_pointers_field_self major obj wz fwd 0 j;
      // Suffix frame: entries pi+1..end don't touch field_addr
      // Need promoted_iter_frame_pre major' farr (pi+1) field_addr
      PromObj.update_object_pointers_preserves_objects major obj wz fwd 0;
      // For each i > pi: field_addr is outside farr[i]'s body (disjointness)
      // and farr[i] is valid in major' (header preserved)
      let aux_suffix (i: nat{i < Seq.length farr}) : Lemma
        (requires i > pi /\
                 (let o = Seq.index farr i in
                  o <> 0UL /\
                  U64.v o >= U64.v mword /\ U64.v o % U64.v mword == 0 /\ U64.v o < heap_size))
        (ensures
          (let o = Seq.index farr i in
           U64.v o >= U64.v mword /\ U64.v o % U64.v mword == 0 /\ U64.v o < heap_size /\
           Seq.mem o (objects zero_addr major') /\
           (let wz_o = U64.v (wosize_of_object o major') in
            U64.v o + wz_o * 8 <= heap_size /\
            (forall (k:nat). k < wz_o ==>
              (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)) /\
            (U64.v field_addr < U64.v o \/ U64.v field_addr >= U64.v o + wz_o * 8))))
      = let o = Seq.index farr i in
        hd_address_spec o;
        wosize_of_object_spec o major;
        wosize_of_object_spec o major';
        if U64.v o > U64.v obj then
          PromObj.update_object_pointers_preserves_other_header major obj wz fwd 0 o
        else if o = obj then
          PromObj.update_object_pointers_preserves_self_header major obj wz fwd 0
        else
          PromObj.update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address o);
        // Disjointness: field_addr in obj's body, outside o's body
        assert (U64.v obj + wz * 8 <= U64.v o \/ U64.v o + U64.v (wosize_of_object o major) * 8 <= U64.v obj);
        // field_addr = obj + j * 8, j < wz, so obj <= field_addr < obj + wz*8
        assert (U64.v field_addr >= U64.v obj /\ U64.v field_addr < U64.v obj + wz * 8)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_suffix);
      // Establish well_formed_heap_part1 for major'
      let aux_wfh (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr major'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
      = hd_address_spec h;
        if h = obj then begin
          PromObj.update_object_pointers_preserves_self_header major obj wz fwd 0;
          wosize_of_object_spec h major'; wosize_of_object_spec h major
        end else if U64.v h > U64.v obj then begin
          PromObj.update_object_pointers_preserves_other_header major obj wz fwd 0 h;
          wosize_of_object_spec h major'; wosize_of_object_spec h major
        end else begin
          PromObj.update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
          wosize_of_object_spec h major; wosize_of_object_spec h major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      // Now call update_promoted_iter_frame
      assert (promoted_iter_frame_pre major' farr (pi + 1) field_addr);
      update_promoted_iter_frame major' farr fwd (pi + 1) field_addr
    end else begin
      // --- Recursive case: idx < pi ---
      if entry = 0UL then begin
        // Zero entry: skip
        update_promoted_iter_zero major farr fwd idx;
        update_promoted_iter_promoted_field_aux major farr fwd pi j (idx + 1)
      end else begin
        // Non-zero scannable entry: update_object_pointers preserves field_addr
        hd_address_spec entry;
        wosize_of_object_spec entry major;
        let wz_e = U64.v (wosize_of_object entry major) in
        let tag_e = getTag (read_word major (hd_address entry)) in
        if wz_e > 0 && U64.lt tag_e no_scan_tag && U64.v entry + wz_e * 8 <= heap_size then begin
          update_promoted_iter_scan major farr fwd idx;
          // Establish recursive precondition via helper
          update_object_pointers_preserves_promoted_field_pre major farr fwd pi j idx;
          let major' = update_object_pointers major entry wz_e fwd 0 in
          // Recurse: precondition holds for major' at idx+1
          update_promoted_iter_promoted_field_aux major' farr fwd pi j (idx + 1)
        end else begin
          // Non-scannable entry: skip
          update_promoted_iter_skip major farr fwd idx;
          update_promoted_iter_promoted_field_aux major farr fwd pi j (idx + 1)
        end
      end
    end
#pop-options

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
  = update_promoted_iter_promoted_field_aux major farr fwd pi j 0

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
/// rewrite_slots_iter preservation for non-forwarded addresses
/// ---------------------------------------------------------------------------

/// If the value at addr does NOT have a forwarded minor pointer, then
/// rewrite_slots_iter preserves it — even if addr happens to be a slot address.
/// This is because the rewrite condition fails at addr, so no step writes there.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
let rec rewrite_slots_iter_preserves_non_fwd
  (major: heap) (fwd: forwarding_map) (slots: seq U64.t) (n: nat) (idx: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      idx <= n /\ n <= Seq.length slots /\
      (forall (i: nat). i >= idx /\ i < n ==>
        (let sa = U64.v (Seq.index slots i) in
         sa < heap_size /\ sa % 8 == 0)) /\
      (let old_val = to_minor_offset (read_word major addr) in
       ~(is_minor_pointer old_val /\ fwd old_val <> 0UL)))
    (ensures
      read_word (rewrite_slots_iter major fwd slots n idx) addr ==
      read_word major addr)
    (decreases (n - idx))
  = if idx >= n then ()
    else if idx >= Seq.length slots then ()
    else begin
      let slot_addr = Seq.index slots idx in
      if U64.v slot_addr >= heap_size || U64.v slot_addr % 8 <> 0 then
        rewrite_slots_iter_preserves_non_fwd major fwd slots n (idx + 1) addr
      else begin
        let slot_val = to_minor_offset (read_word major slot_addr) in
        if is_minor_pointer slot_val then
          let new_val = fwd slot_val in
          if new_val <> 0UL then begin
            // Write at slot_addr. Two sub-cases:
            if U64.v slot_addr = U64.v addr then begin
              // slot_addr == addr: but the value at addr doesn't satisfy the
              // rewrite condition (by precondition). Yet we're in a branch where
              // slot_val = to_minor_offset(read_word major slot_addr) IS a minor
              // pointer with fwd <> 0. Since slot_addr == addr, slot_val == old_val.
              // This contradicts the precondition ~(is_minor_pointer old_val /\ fwd old_val <> 0).
              // So this branch is unreachable.
              assert (to_minor_offset (read_word major addr) == slot_val);
              assert (is_minor_pointer slot_val /\ fwd slot_val <> 0UL);
              // Contradiction with precondition: ~(is_minor_pointer old_val /\ fwd old_val <> 0UL)
              assert false
            end else begin
              // slot_addr != addr: write doesn't affect addr
              let major' = write_word major slot_addr new_val in
              read_write_different major slot_addr addr new_val;
              // Value at addr unchanged in major', condition still false
              rewrite_slots_iter_preserves_non_fwd major' fwd slots n (idx + 1) addr
            end
          end else
            rewrite_slots_iter_preserves_non_fwd major fwd slots n (idx + 1) addr
        else
          rewrite_slots_iter_preserves_non_fwd major fwd slots n (idx + 1) addr
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
/// update_promoted_iter: preservation at non-forwarded addresses
/// ---------------------------------------------------------------------------

/// Helper: processing one entry preserves promoted_entries_valid_from for idx+1.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let update_obj_ptrs_preserves_entries_valid
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma
    (requires
      promoted_entries_valid_from major farr idx /\
      idx < fwd_array_size /\
      (let obj = Seq.index farr idx in
       obj <> 0UL /\
       U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
       Seq.mem obj (objects zero_addr major) /\
       (let wz = U64.v (wosize_of_object obj major) in
        let tag = getTag (read_word major (hd_address obj)) in
        wz > 0 /\ U64.lt tag no_scan_tag /\
        U64.v obj + wz * 8 <= heap_size /\
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))))
    (ensures
      (let obj = Seq.index farr idx in
       let wz = U64.v (wosize_of_object obj major) in
       let major' = update_object_pointers major obj wz fwd 0 in
       promoted_entries_valid_from major' farr (idx + 1)))
  = let obj = Seq.index farr idx in
    let wz = U64.v (wosize_of_object obj major) in
    let major' = update_object_pointers major obj wz fwd 0 in
    PromObj.update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);
    // Show well_formed_heap_part1 major'
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
    // Show each entry from idx+1 onward is still valid
    let aux_entry (i: nat{i < Seq.length farr}) : Lemma
      (requires i > idx /\ (let o = Seq.index farr i in o <> 0UL))
      (ensures
        (let o = Seq.index farr i in
         U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
         Seq.mem o (objects zero_addr major') /\
         (let wz' = U64.v (wosize_of_object o major') in
          U64.v o + wz' * 8 <= heap_size /\
          (forall (k:nat). k < wz' ==>
            (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)))))
    = let o = Seq.index farr i in
      assert (Seq.mem o (objects zero_addr major));
      assert (Seq.mem o (objects zero_addr major'));
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

/// Recursive preservation lemma: when the rewrite condition is false at addr,
/// update_promoted_iter preserves the value.
/// Proof: at each step, update_object_pointers either:
///   - doesn't touch addr (addr outside body): below/above preservation
///   - addr is inside body but condition false: field_self second conjunct
/// In both cases, value unchanged → condition still false → induction continues.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let rec update_promoted_iter_preserves_non_fwd
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map) (idx: nat) (addr: hp_addr)
  : Lemma
    (requires
      promoted_entries_valid_from major farr idx /\
      idx <= fwd_array_size /\
      (let old_val = to_minor_offset (read_word major addr) in
       ~(is_minor_pointer old_val /\ fwd old_val <> 0UL)))
    (ensures
      read_word (update_promoted_iter major farr fwd idx) addr == read_word major addr)
    (decreases (fwd_array_size - idx))
  = if idx >= fwd_array_size then ()
    else if Seq.length farr <> fwd_array_size then ()
    else begin
      let obj = Seq.index farr idx in
      if obj = 0UL then
        update_promoted_iter_preserves_non_fwd major farr fwd (idx + 1) addr
      else begin
        let hdr_addr_v = U64.v obj - 8 in
        if hdr_addr_v + 8 > heap_size || hdr_addr_v % 8 <> 0 then
          update_promoted_iter_preserves_non_fwd major farr fwd (idx + 1) addr
        else begin
          let hdr = read_word major (U64.uint_to_t hdr_addr_v) in
          let wosize = U64.v (getWosize hdr) in
          let tag = getTag hdr in
          if wosize > 0 && U64.lt tag no_scan_tag then begin
            if U64.v obj + wosize * 8 <= heap_size then begin
              wosize_of_object_spec obj major;
              hd_address_spec obj;
              let major' = update_object_pointers major obj wosize fwd 0 in
              // Show value at addr preserved by this step
              if U64.v addr < U64.v obj then
                PromObj.update_object_pointers_preserves_addr_below
                  major obj wosize fwd 0 addr
              else if U64.v addr >= U64.v obj + wosize * 8 then
                PromObj.update_object_pointers_preserves_addr_above
                  major obj wosize fwd 0 addr
              else begin
                // addr is inside body: addr = obj + j*8 for some j < wosize
                let j = (U64.v addr - U64.v obj) / 8 in
                assert (U64.v addr == U64.v obj + j * 8);
                assert (j < wosize);
                PromObj.update_object_pointers_field_self major obj wosize fwd 0 j
              end;
              assert (read_word major' addr == read_word major addr);
              // Establish recursive precondition
              update_obj_ptrs_preserves_entries_valid major farr fwd idx;
              update_promoted_iter_preserves_non_fwd major' farr fwd (idx + 1) addr
            end else
              update_promoted_iter_preserves_non_fwd major farr fwd (idx + 1) addr
          end else
            update_promoted_iter_preserves_non_fwd major farr fwd (idx + 1) addr
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: update_major_pointers characterization at non-forwarded addresses
/// ---------------------------------------------------------------------------
///
/// Key lemma: update_major_pointers preserves any address where the conditional
/// rewrite formula evaluates to "no change" (no forwarded minor pointer).
/// Proof: induction on update_all_objects_aux — at each step, the address is
/// either outside the current object (frame) or inside but not rewritten
/// (condition false → update_object_pointers skips it).
///
/// This is admittable because it follows structurally from:
/// - update_object_pointers only writes where is_minor_pointer /\ fwd <> 0
/// - different aligned addresses don't interfere
/// - no step creates a forwarded minor ptr where none existed

/// Helper: maintains well_formed_heap_part1 after update_object_pointers.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0 --split_queries always"
private let update_obj_ptrs_preserves_wfh
  (major: heap) (obj: obj_addr) (wz: nat) (fwd: forwarding_map)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wz == U64.v (wosize_of_object obj major) /\
      U64.v obj + wz * 8 <= heap_size /\
      (forall (k:nat). k < wz ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))
    (ensures
      (let major' = update_object_pointers major obj wz fwd 0 in
       well_formed_heap_part1 major' /\
       objects zero_addr major' == objects zero_addr major))
  = let major' = update_object_pointers major obj wz fwd 0 in
    PromObj.update_object_pointers_preserves_objects major obj wz fwd 0;
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
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh)
#pop-options

/// Recursive helper: update_all_objects_aux preserves non-fwd addresses.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let rec update_all_objects_aux_preserves_non_fwd
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      (let old_val = to_minor_offset (read_word major addr) in
       ~(is_minor_pointer old_val /\ fwd old_val <> 0UL)))
    (ensures
      read_word (update_all_objects_aux major objs fwd idx) addr == read_word major addr)
    (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      // Seq.mem obj (objects zero_addr major) from indexing
      assert (Seq.mem obj objs);
      if is_blue obj major then
        update_all_objects_aux_preserves_non_fwd major objs fwd (idx + 1) addr
      else if is_no_scan obj major then
        update_all_objects_aux_preserves_non_fwd major objs fwd (idx + 1) addr
      else begin
        // Scannable: process this object
        let wz = U64.v (wosize_of_object obj major) in
        let major' = update_object_pointers major obj wz fwd 0 in
        // Establish field bounds from well_formed_heap_part1
        wosize_of_object_spec obj major;
        hd_address_spec obj;
        assert (U64.v obj + wz * 8 <= heap_size);
        // Show read_word major' addr == read_word major addr
        if U64.v addr < U64.v obj then
          PromObj.update_object_pointers_preserves_addr_below major obj wz fwd 0 addr
        else if U64.v addr >= U64.v obj + wz * 8 then
          PromObj.update_object_pointers_preserves_addr_above major obj wz fwd 0 addr
        else begin
          // addr is in [obj, obj + wz*8) → it's field j
          let j = (U64.v addr - U64.v obj) / 8 in
          assert (U64.v addr == U64.v obj + j * 8);
          assert (j < wz);
          PromObj.update_object_pointers_field_self major obj wz fwd 0 j
        end;
        assert (read_word major' addr == read_word major addr);
        // Establish recursive preconditions
        update_obj_ptrs_preserves_wfh major obj wz fwd;
        assert (objects zero_addr major' == objects zero_addr major);
        // Recurse
        update_all_objects_aux_preserves_non_fwd major' objs fwd (idx + 1) addr
      end
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let update_major_pointers_preserves_non_fwd
  (major: heap) (fwd: forwarding_map) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      (let old_val = to_minor_offset (read_word major addr) in
       ~(is_minor_pointer old_val /\ fwd old_val <> 0UL)))
    (ensures
      read_word (update_major_pointers major fwd) addr == read_word major addr)
  = update_all_objects_aux_preserves_non_fwd major (objects zero_addr major) fwd 0 addr
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: update_major_pointers applies conditional rewrite at scannable fields
/// ---------------------------------------------------------------------------
///
/// For an address that IS a field of a scannable non-blue object with a forwarded
/// minor pointer, update_major_pointers rewrites it to the fwd target.
/// This is a direct corollary of update_major_pointers_field_effect.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let update_major_pointers_rewrites_fwd_field
  (major: heap) (fwd: forwarding_map) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      is_blue obj major = false /\
      is_no_scan obj major = false /\
      (let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = to_minor_offset (read_word major field_addr) in
       is_minor_pointer old_val /\ fwd old_val <> 0UL))
    (ensures
      (let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = to_minor_offset (read_word major field_addr) in
       read_word (update_major_pointers major fwd) field_addr == fwd old_val))
  = let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
    PromField.update_major_pointers_field_effect major fwd obj j
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: forwarding targets don't look like minor pointers
/// ---------------------------------------------------------------------------
///
/// After pass 1 rewrites a promoted field to fwd(offset), the resulting value
/// (a major heap address) should NOT trigger pass 2's rewrite condition.
/// This prevents double-application of the forwarding map.
///
/// Now trivially follows from fwd_targets_stable precondition.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let fwd_targets_not_minor_ptr
  (fwd: forwarding_map) (old_val: U64.t)
  : Lemma
    (requires
      fwd_targets_stable fwd /\
      is_minor_pointer old_val /\ fwd old_val <> 0UL)
    (ensures
      (let target = fwd old_val in
       let target_as_minor = to_minor_offset target in
       ~(is_minor_pointer target_as_minor /\ fwd target_as_minor <> 0UL)))
  = reveal_opaque (`%fwd_targets_stable) (fwd_targets_stable fwd)
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: non-promoted non-slot addresses have no forwarded minor pointer
/// ---------------------------------------------------------------------------
///
/// Now trivially follows from fwd_ptrs_classified by contrapositive:
/// if addr is NOT in any promoted body AND NOT a slot, the condition must be false.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let non_promoted_non_slot_no_fwd
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      Seq.length farr == fwd_array_size /\
      n <= Seq.length slots /\
      promoted_entries_valid_from major farr 0 /\
      fwd_ptrs_classified major fwd farr slots n /\
      // addr is not in any promoted body
      (forall (pi: nat). pi < fwd_array_size ==>
        (let obj = Seq.index farr pi in
         obj = 0UL \/
         U64.v addr < U64.v obj \/
         U64.v addr >= U64.v obj + U64.v (wosize_of_object obj major) * 8)) /\
      // addr is not any slot
      (forall (si: nat). si < n ==> U64.v (Seq.index slots si) <> U64.v addr))
    (ensures
      (let old_val = to_minor_offset (read_word major addr) in
       ~(is_minor_pointer old_val /\ fwd old_val <> 0UL)))
  = // Proof by contradiction: assume the condition holds and derive False.
    // fwd_ptrs_classified is non-opaque, so Z3 sees it directly.
    let a = U64.v addr in
    assert (a < heap_size /\ a % 8 == 0);
    assert (forall (pi:nat). pi < fwd_array_size ==>
      (let obj = Seq.index farr pi in
       obj = 0UL \/ a < U64.v obj \/
       a >= U64.v obj + U64.v (wosize_of_object obj major) * 8));
    assert (forall (si:nat). si < n ==> U64.v (Seq.index slots si) <> a)
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: RHS at a forwarded address (update_major_pointers applies fwd)
/// ---------------------------------------------------------------------------
///
/// Given witnesses obj, j from fwd_ptrs_classified part (1), the full-walk
/// update_major_pointers rewrites the field to fwd(to_minor_offset(old)).
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let if_branch_rhs
  (major: heap) (fwd: forwarding_map) (obj: obj_addr) (j: nat) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      is_blue obj major = false /\
      is_no_scan obj major = false /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v addr == U64.v obj + j * 8 /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      (let old_val = to_minor_offset (read_word major addr) in
       is_minor_pointer old_val /\ fwd old_val <> 0UL))
    (ensures
      (let old_val = to_minor_offset (read_word major addr) in
       read_word (update_major_pointers major fwd) addr == fwd old_val))
  = PromField.update_major_pointers_field_effect major fwd obj j
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: LHS promoted case (addr in a promoted body)
/// ---------------------------------------------------------------------------
///
/// When addr is in the body of a promoted object farr[pi], pass 1
/// (update_promoted_iter) rewrites it to fwd(old), and pass 2
/// (rewrite_slots_iter) preserves it (fwd_targets_stable prevents re-rewrite).
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let if_branch_lhs_promoted
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t)
  (n: nat) (pi: nat) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.length farr == fwd_array_size /\
      promoted_entries_valid_from major farr 0 /\
      promoted_entries_disjoint major farr /\
      valid_slot_addrs slots n /\
      fwd_targets_stable fwd /\
      pi < fwd_array_size /\
      (let obj_pi = Seq.index farr pi in
       obj_pi <> 0UL /\
       is_no_scan obj_pi major = false /\
       U64.v addr >= U64.v obj_pi /\
       U64.v addr < U64.v obj_pi + U64.v (wosize_of_object obj_pi major) * 8) /\
      (let old_val = to_minor_offset (read_word major addr) in
       is_minor_pointer old_val /\ fwd old_val <> 0UL))
    (ensures
      (let old_val = to_minor_offset (read_word major addr) in
       let intermediate = update_promoted_iter major farr fwd 0 in
       let lhs = rewrite_slots_iter intermediate fwd slots n 0 in
       read_word lhs addr == fwd old_val))
  = let old_val = to_minor_offset (read_word major addr) in
    let obj_pi = Seq.index farr pi in
    let wz = U64.v (wosize_of_object obj_pi major) in
    let j_pi = (U64.v addr - U64.v obj_pi) / 8 in
    // Derive wz > 0 from addr bounds
    assert (U64.v addr >= U64.v obj_pi);
    assert (U64.v addr < U64.v obj_pi + wz * 8);
    assert (wz * 8 > 0);
    assert (wz > 0);
    // Derive j_pi < wz from addr bounds
    assert (U64.v addr - U64.v obj_pi < wz * 8);
    assert (j_pi < wz);
    // Derive U64.lt tag no_scan_tag from is_no_scan = false
    is_no_scan_spec obj_pi major;
    tag_of_object_spec obj_pi major;
    let tag = getTag (read_word major (hd_address obj_pi)) in
    assert (tag == tag_of_object obj_pi major);
    assert (U64.gte tag no_scan_tag = false);
    assert (U64.lt tag no_scan_tag);
    // Assert field_addr matches addr
    assert (U64.v obj_pi + j_pi * 8 == U64.v addr);
    // Call the main lemma
    update_promoted_iter_promoted_field major farr fwd pi j_pi;
    let intermediate = update_promoted_iter major farr fwd 0 in
    assert (read_word intermediate addr == fwd old_val);
    // fwd old_val doesn't trigger rewrite condition (fwd_targets_stable)
    fwd_targets_not_minor_ptr fwd old_val;
    // So rewrite_slots_iter preserves it
    rewrite_slots_iter_preserves_non_fwd intermediate fwd slots n 0 addr
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: LHS slot case (addr is a slot, NOT in any promoted body)
/// ---------------------------------------------------------------------------
///
/// When addr is a remembered-set slot and not in any promoted body:
/// pass 1 preserves old_raw (via frame), pass 2 rewrites it (slot effect).
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let if_branch_lhs_slot
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t)
  (n: nat) (si: nat) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.length farr == fwd_array_size /\
      promoted_entries_valid_from major farr 0 /\
      valid_slot_addrs slots n /\
      si < n /\
      U64.v (Seq.index slots si) == U64.v addr /\
      // addr is NOT in any promoted body
      (forall (pi: nat). pi < fwd_array_size ==>
        (let obj_pi = Seq.index farr pi in
         obj_pi = 0UL \/
         U64.v addr < U64.v obj_pi \/
         U64.v addr >= U64.v obj_pi + U64.v (wosize_of_object obj_pi major) * 8)) /\
      // Slots are pairwise distinct
      (forall (i: nat). i < n /\ i <> si ==>
        U64.v (Seq.index slots i) <> U64.v addr) /\
      (let old_val = to_minor_offset (read_word major addr) in
       is_minor_pointer old_val /\ fwd old_val <> 0UL))
    (ensures
      (let old_val = to_minor_offset (read_word major addr) in
       let intermediate = update_promoted_iter major farr fwd 0 in
       let lhs = rewrite_slots_iter intermediate fwd slots n 0 in
       read_word lhs addr == fwd old_val))
  = // Pass 1 (update_promoted_iter) doesn't touch addr since it's not in any body
    update_promoted_iter_frame major farr fwd 0 addr;
    let intermediate = update_promoted_iter major farr fwd 0 in
    assert (read_word intermediate addr == read_word major addr);
    // Pass 2 (rewrite_slots_iter) rewrites it since it's a valid slot
    rewrite_slots_iter_slot_effect intermediate fwd slots n si
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: instantiate fwd_ptrs_classified at a specific address
/// ---------------------------------------------------------------------------
///
/// The reformulated fwd_ptrs_classified shares the obj variable between
/// field-membership and promoted/slot classification, avoiding Z3 matching
/// loops from wosize_of_object unfolding.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let fwd_ptrs_classified_at
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  (a: nat)
  : Lemma
    (requires
      a < heap_size /\ a % 8 == 0 /\
      fwd_ptrs_classified major fwd farr slots n /\
      (let field_val = to_minor_offset (read_word major (U64.uint_to_t a)) in
       is_minor_pointer field_val /\ fwd field_val <> 0UL))
    (ensures
      (exists (obj: obj_addr) (j: nat).
        Seq.mem obj (objects zero_addr major) /\
        is_blue obj major = false /\
        is_no_scan obj major = false /\
        j < U64.v (wosize_of_object obj major) /\
        a == U64.v obj + j * 8 /\
        U64.v obj + j * 8 + 8 <= heap_size /\
        ((exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
         (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == a))))
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: a field of obj cannot be in the body of a different object
/// ---------------------------------------------------------------------------
///
/// If addr is at offset j within obj, and obj_pi is a different object in
/// the heap, then addr is not in obj_pi's body (objects don't overlap).
#push-options "--z3rlimit 200 --fuel 3 --ifuel 1"
let field_not_in_other_obj
  (major: heap) (obj obj_pi: obj_addr) (j: nat) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      Seq.mem obj_pi (objects zero_addr major) /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v addr == U64.v obj + j * 8 /\
      obj_pi <> obj)
    (ensures
      U64.v addr < U64.v obj_pi \/
      U64.v addr >= U64.v obj_pi + U64.v (wosize_of_object obj_pi major) * 8)
  = if U64.v obj_pi < U64.v obj then begin
      // obj_pi < obj: objects_separated gives obj > obj_pi + wosize(obj_pi)*8
      objects_separated zero_addr major obj_pi obj;
      // So addr = obj + j*8 >= obj > obj_pi + wosize(obj_pi)*8
      assert (U64.v obj > U64.v obj_pi + U64.v (wosize_of_object_as_wosize obj_pi major) * 8);
      assert (U64.v addr >= U64.v obj_pi + U64.v (wosize_of_object_as_wosize obj_pi major) * 8)
    end else begin
      // obj_pi > obj: objects_separated gives obj_pi > obj + wosize(obj)*8
      objects_separated zero_addr major obj obj_pi;
      // Since j < wosize(obj): addr = obj + j*8 < obj + wosize(obj)*8 <= obj_pi
      assert (U64.v obj_pi > U64.v obj + U64.v (wosize_of_object_as_wosize obj major) * 8);
      assert (U64.v addr < U64.v obj_pi)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: if obj is not in farr, then addr (a field of obj) is not in any
/// promoted body.
/// ---------------------------------------------------------------------------
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let field_not_in_any_promoted_body
  (major: heap) (farr: seq U64.t) (obj: obj_addr) (j: nat) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.length farr == fwd_array_size /\
      promoted_entries_valid_from major farr 0 /\
      Seq.mem obj (objects zero_addr major) /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v addr == U64.v obj + j * 8 /\
      (forall (pi: nat). pi < fwd_array_size ==> Seq.index farr pi <> obj))
    (ensures
      (forall (pi: nat). pi < fwd_array_size ==>
        (let obj_pi = Seq.index farr pi in
         obj_pi = 0UL \/
         U64.v addr < U64.v obj_pi \/
         U64.v addr >= U64.v obj_pi + U64.v (wosize_of_object obj_pi major) * 8)))
  = let aux (pi: nat{pi < Seq.length farr}) : Lemma
      (ensures
        (let obj_pi = Seq.index farr pi in
         obj_pi = 0UL \/
         U64.v addr < U64.v obj_pi \/
         U64.v addr >= U64.v obj_pi + U64.v (wosize_of_object obj_pi major) * 8))
    = let obj_pi = Seq.index farr pi in
      if obj_pi = 0UL then ()
      else begin
        // obj_pi <> 0 and obj_pi <> obj (from precondition)
        // promoted_entries_valid_from gives obj_pi in objects
        assert (Seq.mem obj_pi (objects zero_addr major));
        field_not_in_other_obj major obj obj_pi j addr
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: if-branch point equality (addr has forwarded minor pointer)
/// ---------------------------------------------------------------------------
///
/// Given an address where the condition holds, proves lhs[addr] == rhs[addr].
/// Uses strong_excluded_middle for clean case split: promoted vs slot.
#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"
let if_branch_addr_eq
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  (a: nat{a < heap_size /\ a % 8 == 0})
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.length farr == fwd_array_size /\
      promoted_entries_valid_from major farr 0 /\
      promoted_entries_disjoint major farr /\
      valid_slot_addrs slots n /\
      slots_pairwise_distinct slots n /\
      fwd_targets_stable fwd /\
      fwd_ptrs_classified major fwd farr slots n /\
      (let old_val = to_minor_offset (read_word major (U64.uint_to_t a)) in
       is_minor_pointer old_val /\ fwd old_val <> 0UL))
    (ensures
      (let addr : hp_addr = U64.uint_to_t a in
       let intermediate = update_promoted_iter major farr fwd 0 in
       let lhs = rewrite_slots_iter intermediate fwd slots n 0 in
       let rhs = update_major_pointers major fwd in
       read_word lhs addr == read_word rhs addr))
  = let addr : hp_addr = U64.uint_to_t a in
    let old_val = to_minor_offset (read_word major addr) in
    let intermediate = update_promoted_iter major farr fwd 0 in
    let lhs = rewrite_slots_iter intermediate fwd slots n 0 in
    let rhs = update_major_pointers major fwd in
    // Step 1: instantiate fwd_ptrs_classified to get combined existential
    fwd_ptrs_classified_at major fwd farr slots n a;
    // Step 2: extract witnesses via two separate indefinite_description_ghost calls
    // to avoid the nested-to-pair existential conversion issue.
    let obj : obj_addr = IndDesc.indefinite_description_ghost obj_addr (fun obj ->
      exists (j: nat).
        Seq.mem obj (objects zero_addr major) /\
        is_blue obj major = false /\
        is_no_scan obj major = false /\
        j < U64.v (wosize_of_object obj major) /\
        a == U64.v obj + j * 8 /\
        U64.v obj + j * 8 + 8 <= heap_size /\
        ((exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
         (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == a))) in
    let j : nat = IndDesc.indefinite_description_ghost nat (fun j ->
        Seq.mem obj (objects zero_addr major) /\
        is_blue obj major = false /\
        is_no_scan obj major = false /\
        j < U64.v (wosize_of_object obj major) /\
        a == U64.v obj + j * 8 /\
        U64.v obj + j * 8 + 8 <= heap_size /\
        ((exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj) \/
         (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == a))) in
    // Step 3: RHS applies fwd at this field
    if_branch_rhs major fwd obj j addr;
    assert (read_word rhs addr == fwd old_val);
    // Step 4: LHS — use strong_excluded_middle for case split
    // Either obj is in farr (promoted) or it isn't (must be slot).
    if IndDesc.strong_excluded_middle
         (exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj)
    then begin
      // Promoted case: some farr[pi] == obj
      let pi = IndDesc.indefinite_description_ghost nat
        (fun pi -> pi < fwd_array_size /\ Seq.index farr pi == obj) in
      // farr[pi] == obj, so all preconditions of if_branch_lhs_promoted follow:
      // obj: obj_addr means U64.v obj >= 8, so farr[pi] <> 0UL
      // is_no_scan (farr[pi]) = is_no_scan obj = false (by equality)
      // U64.v addr = U64.v obj + j*8 >= U64.v obj = U64.v (farr[pi])
      // j < wosize(obj) = wosize(farr[pi]) so addr < farr[pi] + wosize*8
      if_branch_lhs_promoted major fwd farr slots n pi addr
    end else begin
      // Not promoted: forall pi. farr[pi] <> obj
      // From the disjunction + negation of promoted → slot case holds
      assert (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == a);
      let si = IndDesc.indefinite_description_ghost nat
        (fun si -> si < n /\ U64.v (Seq.index slots si) == a) in
      // Establish "not in any promoted body" via objects_separated
      field_not_in_any_promoted_body major farr obj j addr;
      if_branch_lhs_slot major fwd farr slots n si addr
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Main theorem: two-pass rewriting equals full update
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"
let promoted_plus_slots_eq_full_update
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       valid_fwd_entries farr /\
       represents_fwd farr prom.fwd_map /\
       promoted_entries_valid_from prom.major_final farr 0 /\
       promoted_entries_disjoint prom.major_final farr /\
       valid_slot_addrs slots n /\
       slots_pairwise_distinct slots n /\
       ref_table_sound major_pre slots n /\
       ref_table_complete major_pre prom.fwd_map slots n /\
       fwd_targets_stable prom.fwd_map /\
       fwd_ptrs_classified prom.major_final prom.fwd_map farr slots n /\
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
    let intermediate = update_promoted_iter major farr fwd 0 in
    let lhs = rewrite_slots_iter intermediate fwd slots n 0 in
    let rhs = update_major_pointers major fwd in
    // Strategy: show read_word lhs a == read_word rhs a for every aligned address.
    //
    // Key insight: at every address, the "conditional rewrite" formula gives:
    //   result = if is_minor_pointer(to_minor_offset(old)) /\ fwd(...) <> 0
    //            then fwd(to_minor_offset(old))
    //            else old
    //
    // Both LHS and RHS implement this same formula (under the theorem's invariants).
    // The proof splits on whether the condition is true or false at each address.
    let aux (a: nat{a < heap_size /\ a % 8 == 0})
      : Lemma (read_word lhs (U64.uint_to_t a) == read_word rhs (U64.uint_to_t a))
      = let addr : hp_addr = U64.uint_to_t a in
        let old_raw = read_word major addr in
        let old_val = to_minor_offset old_raw in
        if is_minor_pointer old_val && fwd old_val <> 0UL then begin
          // ---- CASE: addr has a forwarded minor pointer ----
          if_branch_addr_eq major fwd farr slots n a
        end else begin
          // ---- CASE: addr does NOT have a forwarded minor pointer ----
          // Both LHS and RHS preserve as old_raw.
          //
          // RHS direction: update_major_pointers_preserves_non_fwd.
          update_major_pointers_preserves_non_fwd major fwd addr;
          assert (read_word rhs addr == old_raw);
          //
          // LHS direction: neither pass changes addr.
          // Pass 1 (update_promoted_iter): ~cond means it doesn't write at addr.
          //   Whether addr is in a promoted body or not, intermediate preserves old_raw.
          update_promoted_iter_preserves_non_fwd major farr fwd 0 addr;
          assert (read_word intermediate addr == old_raw);
          // Pass 2 (rewrite_slots_iter): ~cond on intermediate[addr] = old_raw → no-op.
          rewrite_slots_iter_preserves_non_fwd intermediate fwd slots n 0 addr
        end
    in
    FStar.Classical.forall_intro aux;
    heap_read_word_extensional lhs rhs
#pop-options
