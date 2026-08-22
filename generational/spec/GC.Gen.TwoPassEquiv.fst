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
module Classif = GC.Gen.TwoPassEquiv.Classification
module IndDesc = FStar.IndefiniteDescription

/// ---------------------------------------------------------------------------
/// Heap extensionality — delegates to GC.Gen.HeapExtensional
/// ---------------------------------------------------------------------------

/// `k <= n` and `k <> n` give `k + 1 <= n`.  Proved in an empty context: this
/// step diverges inside the large recursive proofs below.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let lt_of_le_ne (k n: nat) : Lemma
  (requires k <= n /\ ~(k == n)) (ensures k + 1 <= n) = ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let heap_read_word_extensional_mk (h1 h2: heap)
  : Lemma
    (requires (forall (a: nat{a < heap_size /\ a % U64.v mword == 0}).
       read_word h1 (mk_hp_addr a) == read_word h2 (mk_hp_addr a)))
    (ensures h1 == h2)
  = let aux (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word h1 (U64.uint_to_t a) == read_word h2 (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          assert (read_word h1 (mk_hp_addr a) == read_word h2 (mk_hp_addr a));
          assert (mk_hp_addr a == U64.uint_to_t a)
        end
    in
    FStar.Classical.forall_intro aux;
    HeapExt.heap_read_word_ext h1 h2
#pop-options

/// Addresses that the full update_major_pointers walk may rewrite: fields of
/// non-blue, non-no_scan objects in the current major heap.
private let scannable_field_addr (major: heap) (a: nat) : prop =
  exists (obj: obj_addr) (j: nat).
    Seq.mem obj (objects zero_addr major) /\
    is_blue obj major = false /\
    is_no_scan obj major = false /\
    j < U64.v (wosize_of_object obj major) /\
    a == U64.v obj + j * 8 /\
    U64.v obj + j * 8 + 8 <= heap_size /\
    (U64.v obj + j * 8) % 8 == 0

/// ---------------------------------------------------------------------------
/// update_promoted_iter: preservation at non-forwarded addresses
/// ---------------------------------------------------------------------------

/// Infix header values are not word-aligned (mod 8 ≠ 0), hence never minor pointers.
/// Proof: getTag hdr == infix_tag (=249) → hdr mod 256 == 249 → hdr mod 8 == 1.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let infix_header_not_minor_pointer (hdr: U64.t)
  : Lemma (requires getTag hdr = infix_tag)
          (ensures U64.v hdr % 8 <> 0 /\
                   ~(is_minor_pointer (to_minor_offset hdr)))
  = getTag_spec hdr;
    infix_tag_val ();
    FStar.UInt.logand_mask #64 (U64.v hdr) 8;
    assert (U64.v hdr % 256 == 249);
    assert (U64.v hdr % 8 == (U64.v hdr % 256) % 8)
#pop-options

/// Helper: update_object_pointers preserves is_infix status because
/// infix header values are not minor pointers and thus are never rewritten.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
private let update_obj_ptrs_preserves_is_infix
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map)
  (other: obj_addr)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      wosize > 0 /\
      U64.v obj + wosize * 8 <= heap_size /\
      (forall (k:nat). k < wosize ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)) /\
      is_infix other major)
    (ensures
      is_infix other (update_object_pointers major obj wosize fwd 0))
  = let major' = update_object_pointers major obj wosize fwd 0 in
    let hdr_addr = hd_address other in
    hd_address_spec other;
    is_infix_spec other major;
    tag_of_object_spec other major;
    let old_hdr = read_word major hdr_addr in
    assert (getTag old_hdr = infix_tag);
    if U64.v hdr_addr < U64.v obj then begin
      PromObj.update_object_pointers_preserves_addr_below major obj wosize fwd 0 hdr_addr;
      assert (read_word major' hdr_addr == old_hdr);
      is_infix_spec other major';
      tag_of_object_spec other major'
    end else if U64.v hdr_addr >= U64.v obj + wosize * 8 then begin
      PromObj.update_object_pointers_preserves_addr_above major obj wosize fwd 0 hdr_addr;
      assert (read_word major' hdr_addr == old_hdr);
      is_infix_spec other major';
      tag_of_object_spec other major'
    end else begin
      // hdr_addr is inside obj's body at field index j
      let j = (U64.v hdr_addr - U64.v obj) / 8 in
      assert (U64.v hdr_addr == U64.v obj + j * 8);
      assert (j < wosize);
      PromObj.update_object_pointers_field_self major obj wosize fwd 0 j;
      let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
      assert (field_addr == hdr_addr);
      infix_header_not_minor_pointer old_hdr;
      assert (read_word major' hdr_addr == old_hdr);
      is_infix_spec other major';
      tag_of_object_spec other major'
    end
#pop-options

/// ---------------------------------------------------------------------------
/// update_promoted_iter frame lemma
/// ---------------------------------------------------------------------------

/// Helper: update_object_pointers preserves promoted_iter_frame_pre for idx+1
/// when applied to the entry at idx.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
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
    //    - Either is_infix (preserved by update_obj_ptrs_preserves_is_infix)
    //    - Or: Seq.mem (farr[i]) (objects zero_addr major') — from (1)
    //          wosize_of_object (farr[i]) major' == wosize_of_object (farr[i]) major
    //          addr is outside body — same bounds since wosize unchanged
    assert (Seq.length farr == fwd_array_size);
    let aux_entry (i: nat{i < Seq.length farr}) : Lemma
      (requires i > idx /\
               (let o = Seq.index farr i in o <> 0UL))
      (ensures
        (let o = Seq.index farr i in
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          is_infix o major') \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major') /\
          (let wz' = U64.v (wosize_of_object o major') in
           U64.v o + wz' * 8 <= heap_size /\
           (forall (k:nat). k < wz' ==>
             (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)) /\
           (U64.v addr < U64.v o \/ U64.v addr >= U64.v o + wz' * 8)))))
    = let o = Seq.index farr i in
      // From promoted_iter_frame_pre: o <> 0UL, so either bounds+infix or bounds+objects
      assert (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size);
      if is_infix o major then begin
        // Infix case: show is_infix preserved
        update_obj_ptrs_preserves_is_infix major obj wz fwd o
      end else begin
        // Non-infix case: from weakened frame_pre, it's in objects with addr outside body
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
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_entry)
#pop-options

/// Frame: addresses outside all promoted object bodies are unchanged.
/// Proof: induction on idx, mirroring the recursive structure of update_promoted_iter.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
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
          if wosize > 0 && U64.lt tag no_scan_tag && (tag <> infix_tag) then begin
            if U64.v major_addr + wosize * 8 <= heap_size then begin
              hd_address_spec major_addr;
              assert (U64.uint_to_t hdr_addr_v == hd_address major_addr);
              tag_of_object_spec major_addr major;
              is_infix_spec major_addr major;
              assert (is_infix major_addr major = false);
              assert (Seq.mem major_addr (objects zero_addr major));
              wosize_of_object_spec major_addr major;
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
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
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
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
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
#push-options "--z3rlimit 250 --fuel 1 --ifuel 0"
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
        wz > 0 /\ U64.lt tag no_scan_tag /\ tag <> infix_tag /\
        U64.v obj + wz * 8 <= heap_size /\
        j < wz /\
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))) /\
      (let entry = Seq.index farr idx in
       entry <> 0UL /\
       U64.v entry >= U64.v mword /\ U64.v entry % 8 == 0 /\ U64.v entry < heap_size /\
       Seq.mem entry (objects zero_addr major) /\
       is_infix entry major = false /\
       (let wz_e = U64.v (wosize_of_object entry major) in
        wz_e > 0 /\
        U64.v entry + wz_e * 8 <= heap_size /\
        (forall (k:nat). k < wz_e ==>
          (U64.v entry + k * 8 + 8 <= heap_size /\ (U64.v entry + k * 8) % 8 == 0)))) /\
      // All entries from idx onward are valid or infix
      (forall (i: nat). i >= idx /\ i < fwd_array_size ==>
        (let o = Seq.index farr i in
         o = 0UL \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          is_infix o major) \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major) /\
          (let wz_o = U64.v (wosize_of_object o major) in
           U64.v o + wz_o * 8 <= heap_size /\
           (forall (k:nat). k < wz_o ==>
             (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)))))) /\
      // Disjointness (only between non-infix entries)
      (forall (i1 i2: nat). i1 >= idx /\ i1 < fwd_array_size /\ i2 >= idx /\ i2 < fwd_array_size /\ i1 <> i2 ==>
        (let o1 = Seq.index farr i1 in
         let o2 = Seq.index farr i2 in
         o1 <> 0UL /\ o2 <> 0UL /\
         is_infix o1 major = false /\ is_infix o2 major = false ==>
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
            is_infix o major') \/
           (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
            is_infix o major' = false /\
            is_infix o major = false /\
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
    // Establish is_infix = false for both obj and entry (needed for disjointness)
    is_infix_spec obj major;
    tag_of_object_spec obj major;
    hd_address_spec obj;
    assert (is_infix obj major = false);
    assert (is_infix entry major = false);
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
    // For each entry i > idx: either infix (preserved) or wosize preserved in major'
    let aux_entry (i: nat{i < Seq.length farr}) : Lemma
      (requires i > idx)
      (ensures
        (let o = Seq.index farr i in
         o = 0UL \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          is_infix o major') \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          is_infix o major' = false /\
          is_infix o major = false /\
          Seq.mem o (objects zero_addr major') /\
          (let wz_o = U64.v (wosize_of_object o major') in
           wz_o == U64.v (wosize_of_object o major) /\
           U64.v o + wz_o * 8 <= heap_size /\
           (forall (k:nat). k < wz_o ==>
             (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0))))))
    = let o = Seq.index farr i in
      if o = 0UL then ()
      else begin
        // From validity: bounds hold
        assert (U64.v o >= U64.v mword /\ U64.v o % U64.v mword == 0 /\ U64.v o < heap_size);
        if is_infix o major then begin
          // Infix case: show is_infix preserved
          update_obj_ptrs_preserves_is_infix major entry_o wz_e fwd o
        end else begin
          // Non-infix case: it's in objects
          assert (Seq.mem o (objects zero_addr major));
          assert (Seq.mem o (objects zero_addr major'));
          hd_address_spec o;
          if o = entry_o then begin
            PromObj.update_object_pointers_preserves_self_header major entry_o wz_e fwd 0;
            wosize_of_object_spec o major;
            wosize_of_object_spec o major';
            is_infix_spec o major;
            is_infix_spec o major';
            tag_of_object_spec o major;
            tag_of_object_spec o major'
          end else begin
            update_object_pointers_preserves_other_obj_header major entry_o wz_e fwd o;
            wosize_of_object_spec o major;
            wosize_of_object_spec o major';
            is_infix_spec o major;
            is_infix_spec o major';
            tag_of_object_spec o major;
            tag_of_object_spec o major'
          end
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_entry)
#pop-options
#push-options "--z3rlimit 75 --fuel 1 --ifuel 0"
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
        wz > 0 /\ U64.lt tag no_scan_tag /\ tag <> infix_tag /\
        U64.v obj + wz * 8 <= heap_size /\
        j < wz /\
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))) /\
      // All entries are valid objects or infix
      (forall (i: nat). i >= idx /\ i < fwd_array_size ==>
        (let o = Seq.index farr i in
         o = 0UL \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          is_infix o major) \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major) /\
          (let wz_o = U64.v (wosize_of_object o major) in
           U64.v o + wz_o * 8 <= heap_size /\
           (forall (k:nat). k < wz_o ==>
             (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)))))) /\
      // Disjointness of bodies (only between non-infix entries)
      (forall (i1 i2: nat). i1 >= idx /\ i1 < fwd_array_size /\ i2 >= idx /\ i2 < fwd_array_size /\ i1 <> i2 ==>
        (let o1 = Seq.index farr i1 in
         let o2 = Seq.index farr i2 in
         o1 <> 0UL /\ o2 <> 0UL /\
         is_infix o1 major = false /\ is_infix o2 major = false ==>
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
      // and farr[i] is valid in major' (header preserved), or farr[i] is infix
      let aux_suffix (i: nat{i < Seq.length farr}) : Lemma
        (requires i > pi /\
                 (let o = Seq.index farr i in
                  o <> 0UL /\
                  U64.v o >= U64.v mword /\ U64.v o % U64.v mword == 0 /\ U64.v o < heap_size))
        (ensures
          (let o = Seq.index farr i in
           (U64.v o >= U64.v mword /\ U64.v o % U64.v mword == 0 /\ U64.v o < heap_size /\
            is_infix o major') \/
           (U64.v o >= U64.v mword /\ U64.v o % U64.v mword == 0 /\ U64.v o < heap_size /\
            Seq.mem o (objects zero_addr major') /\
            (let wz_o = U64.v (wosize_of_object o major') in
             U64.v o + wz_o * 8 <= heap_size /\
             (forall (k:nat). k < wz_o ==>
               (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0)) /\
             (U64.v field_addr < U64.v o \/ U64.v field_addr >= U64.v o + wz_o * 8)))))
      = let o = Seq.index farr i in
        if is_infix o major then begin
          update_obj_ptrs_preserves_is_infix major obj wz fwd o
        end else begin
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
          // Need is_infix obj major = false and is_infix o major = false for disjointness
          is_infix_spec obj major;
          tag_of_object_spec obj major;
          assert (is_infix obj major = false);
          assert (is_infix o major = false);
          assert (U64.v obj + wz * 8 <= U64.v o \/ U64.v o + U64.v (wosize_of_object o major) * 8 <= U64.v obj);
          // field_addr = obj + j * 8, j < wz, so obj <= field_addr < obj + wz*8
          assert (U64.v field_addr >= U64.v obj /\ U64.v field_addr < U64.v obj + wz * 8)
        end
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
      lt_of_le_ne idx pi;
      if entry = 0UL then begin
        // Zero entry: skip
        update_promoted_iter_zero major farr fwd idx;
        update_promoted_iter_promoted_field_aux major farr fwd pi j (idx + 1)
      end else begin
        // Non-zero entry: check if scannable
        hd_address_spec entry;
        let hdr_e = read_word major (hd_address entry) in
        let tag_e = getTag hdr_e in
        // If entry is infix, it's skipped
        tag_of_object_spec entry major;
        is_infix_spec entry major;
        if tag_e = infix_tag then begin
          // Infix entry: skipped by update_promoted_iter
          update_promoted_iter_skip major farr fwd idx;
          update_promoted_iter_promoted_field_aux major farr fwd pi j (idx + 1)
        end else begin
          // Non-infix entry: must be in objects
          assert (is_infix entry major = false);
          assert (Seq.mem entry (objects zero_addr major));
          wosize_of_object_spec entry major;
          let wz_e = U64.v (wosize_of_object entry major) in
          if wz_e > 0 && U64.lt tag_e no_scan_tag && U64.v entry + wz_e * 8 <= heap_size then begin
            update_promoted_iter_scan major farr fwd idx;
            // Establish recursive precondition via helper
            update_object_pointers_preserves_promoted_field_pre major farr fwd pi j idx;
            let major' = update_object_pointers major entry wz_e fwd 0 in
            // Recurse: precondition holds for major' at idx+1
            // Validity from helper postcondition; disjointness from:
            // helper gives is_infix o major' = false /\ wosize o major' == wosize o major
            // precondition gives: is_infix o major → is_infix o major' (via aux_entry 2nd case)
            // contrapositive: is_infix o major' = false → is_infix o major = false
            // then original disjointness + wosize preservation gives disjointness in major'
            update_promoted_iter_promoted_field_aux major' farr fwd pi j (idx + 1)
          end else begin
            // Non-scannable entry: skip
            update_promoted_iter_skip major farr fwd idx;
            update_promoted_iter_promoted_field_aux major farr fwd pi j (idx + 1)
          end
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
        wz > 0 /\ U64.lt tag no_scan_tag /\ tag <> infix_tag /\
        U64.v obj + wz * 8 <= heap_size /\
        j < wz /\
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))) /\
      (forall (i: nat). i < fwd_array_size ==>
        (let o = Seq.index farr i in
         o = 0UL \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          is_infix o major) \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major) /\
          U64.v o + U64.v (wosize_of_object o major) * 8 <= heap_size))) /\
      (forall (i1 i2: nat). i1 < fwd_array_size /\ i2 < fwd_array_size /\ i1 <> i2 ==>
        (let o1 = Seq.index farr i1 in
         let o2 = Seq.index farr i2 in
         o1 <> 0UL /\ o2 <> 0UL /\
         is_infix o1 major = false /\ is_infix o2 major = false ==>
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
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
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

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let slots_frame_from_non_field
  (major: heap) (slots: seq U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires
      valid_slot_addrs slots n /\
      slots_scannable_in_major major slots n /\
      ~(scannable_field_addr major (U64.v addr)))
    (ensures
      (forall (i: nat). i < n ==>
        (let sa = U64.v (Seq.index slots i) in
         sa < heap_size /\ sa % 8 == 0 /\
         (U64.v addr + 8 <= sa \/ sa + 8 <= U64.v addr))))
  =
    let aux (i: nat{i < n}) : Lemma
      (ensures
        (let sa = U64.v (Seq.index slots i) in
         sa < heap_size /\ sa % 8 == 0 /\
         (U64.v addr + 8 <= sa \/ sa + 8 <= U64.v addr)))
    = let sa = U64.v (Seq.index slots i) in
      assert (sa < heap_size /\ sa % 8 == 0);
      assert (scannable_field_addr major sa);
      if sa = U64.v addr then begin
        assert (scannable_field_addr major (U64.v addr));
        assert false
      end else if U64.v addr < sa then begin
        assert (U64.v addr % 8 == 0);
        assert (U64.v addr + 8 <= sa)
      end else begin
        assert (sa < U64.v addr);
        assert (sa + 8 <= U64.v addr)
      end
    in
    FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// rewrite_slots_iter preservation for non-forwarded addresses
/// ---------------------------------------------------------------------------

/// If the value at addr does NOT have a forwarded minor pointer, then
/// rewrite_slots_iter preserves it — even if addr happens to be a slot address.
/// This is because the rewrite condition fails at addr, so no step writes there.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
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
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
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


/// Helper: processing one entry preserves promoted_entries_valid_from for idx+1.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
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
        wz > 0 /\ U64.lt tag no_scan_tag /\ tag <> infix_tag /\
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
    // Show each entry from idx+1 onward is still valid (or infix)
    let aux_entry (i: nat{i < Seq.length farr}) : Lemma
      (requires i > idx /\ (let o = Seq.index farr i in o <> 0UL))
      (ensures
        (let o = Seq.index farr i in
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          is_infix o major') \/
         (U64.v o >= U64.v mword /\ U64.v o % 8 == 0 /\ U64.v o < heap_size /\
          Seq.mem o (objects zero_addr major') /\
          (let wz' = U64.v (wosize_of_object o major') in
           U64.v o + wz' * 8 <= heap_size /\
           (forall (k:nat). k < wz' ==>
             (U64.v o + k * 8 + 8 <= heap_size /\ (U64.v o + k * 8) % 8 == 0))))))
    = let o = Seq.index farr i in
      // From weakened valid_from: entry is either infix or valid object
      if is_infix o major then begin
        // Infix case: show is_infix preserved
        update_obj_ptrs_preserves_is_infix major obj wz fwd o
      end else begin
        // Non-infix case: original logic
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
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_entry)
#pop-options

/// Reflection lemma: update_object_pointers only mutates object fields, not
/// headers or the object list.  Thus any scannable-field witness after the
/// update was already a scannable-field witness before the update.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
private let update_obj_ptrs_reflects_scannable_field_addr
  (major: heap) (obj: obj_addr) (wz: nat) (fwd: forwarding_map) (addr: hp_addr)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wz == U64.v (wosize_of_object obj major) /\
      (forall (k:nat). k < wz ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)) /\
      scannable_field_addr (update_object_pointers major obj wz fwd 0) (U64.v addr))
    (ensures scannable_field_addr major (U64.v addr))
  = let major' = update_object_pointers major obj wz fwd 0 in
    let h : obj_addr = IndDesc.indefinite_description_ghost obj_addr (fun h ->
      exists (j: nat).
        Seq.mem h (objects zero_addr major') /\
        is_blue h major' = false /\
        is_no_scan h major' = false /\
        j < U64.v (wosize_of_object h major') /\
        U64.v addr == U64.v h + j * 8 /\
        U64.v h + j * 8 + 8 <= heap_size /\
        (U64.v h + j * 8) % 8 == 0) in
    let j : nat = IndDesc.indefinite_description_ghost nat (fun j ->
        Seq.mem h (objects zero_addr major') /\
        is_blue h major' = false /\
        is_no_scan h major' = false /\
        j < U64.v (wosize_of_object h major') /\
        U64.v addr == U64.v h + j * 8 /\
        U64.v h + j * 8 + 8 <= heap_size /\
        (U64.v h + j * 8) % 8 == 0) in
    PromObj.update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);
    assert (Seq.mem h (objects zero_addr major));
    if h = obj then
      PromObj.update_object_pointers_preserves_self_header major obj wz fwd 0
    else if U64.v h > U64.v obj then
      PromObj.update_object_pointers_preserves_other_header major obj wz fwd 0 h
    else begin
      hd_address_spec h;
      assert (U64.v (hd_address h) < U64.v obj);
      PromObj.update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h)
    end;
    assert (read_word major' (hd_address h) == read_word major (hd_address h));
    color_of_header_eq h major' major;
    tag_of_object_spec h major';
    tag_of_object_spec h major;
    is_no_scan_spec h major';
    is_no_scan_spec h major;
    wosize_of_object_spec h major';
    wosize_of_object_spec h major;
    assert (wosize_of_object h major' == wosize_of_object h major);
    assert (is_blue h major = false);
    assert (is_no_scan h major = false);
    assert (j < U64.v (wosize_of_object h major));
    assert (scannable_field_addr major (U64.v addr))

private let update_obj_ptrs_preserves_not_scannable_field_addr
  (major: heap) (obj: obj_addr) (wz: nat) (fwd: forwarding_map) (addr: hp_addr)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wz == U64.v (wosize_of_object obj major) /\
      (forall (k:nat). k < wz ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)) /\
      ~(scannable_field_addr major (U64.v addr)))
    (ensures
      ~(scannable_field_addr (update_object_pointers major obj wz fwd 0) (U64.v addr)))
  = let major' = update_object_pointers major obj wz fwd 0 in
    if IndDesc.strong_excluded_middle (scannable_field_addr major' (U64.v addr)) then begin
      update_obj_ptrs_reflects_scannable_field_addr major obj wz fwd addr;
      assert false
    end
#pop-options

private let promoted_entries_not_blue_from (major: heap) (farr: seq U64.t) (idx: nat) : prop =
  Seq.length farr == fwd_array_size /\
  (forall (i: nat). i >= idx /\ i < fwd_array_size ==>
    (let obj = Seq.index farr i in
     obj <> 0UL /\
     U64.v obj >= U64.v mword /\
     U64.v obj % U64.v mword == 0 /\
     U64.v obj < heap_size /\
     is_infix obj major = false ==>
     is_blue obj major = false))

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
private let update_obj_ptrs_preserves_entries_not_blue_from
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma
    (requires
      promoted_entries_valid_from major farr idx /\
      promoted_entries_not_blue_from major farr idx /\
      idx < fwd_array_size /\
      (let obj = Seq.index farr idx in
       obj <> 0UL /\
       U64.v obj >= U64.v mword /\ U64.v obj % 8 == 0 /\ U64.v obj < heap_size /\
       Seq.mem obj (objects zero_addr major) /\
       (let wz = U64.v (wosize_of_object obj major) in
        let tag = getTag (read_word major (hd_address obj)) in
        wz > 0 /\ U64.lt tag no_scan_tag /\ tag <> infix_tag /\
        U64.v obj + wz * 8 <= heap_size /\
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))))
    (ensures
      (let obj = Seq.index farr idx in
       let wz = U64.v (wosize_of_object obj major) in
       let major' = update_object_pointers major obj wz fwd 0 in
       promoted_entries_not_blue_from major' farr (idx + 1)))
  = let obj = Seq.index farr idx in
    let wz = U64.v (wosize_of_object obj major) in
    let major' = update_object_pointers major obj wz fwd 0 in
    PromObj.update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);
    let aux_entry (i: nat{i < Seq.length farr}) : Lemma
      (requires i > idx)
      (ensures
        (let o = Seq.index farr i in
         o <> 0UL /\
         U64.v o >= U64.v mword /\
         U64.v o % U64.v mword == 0 /\
         U64.v o < heap_size /\
         is_infix o major' = false ==>
         is_blue o major' = false))
    = let o = Seq.index farr i in
      if o <> 0UL &&
         U64.v o >= U64.v mword &&
         U64.v o % U64.v mword = 0 &&
         U64.v o < heap_size &&
         is_infix o major' = false
      then begin
        if is_infix o major then begin
          update_obj_ptrs_preserves_is_infix major obj wz fwd o;
          assert false
        end else begin
          assert (is_blue o major = false);
          assert (Seq.mem o (objects zero_addr major));
          if o = obj then
            PromObj.update_object_pointers_preserves_self_header major obj wz fwd 0
          else if U64.v o > U64.v obj then
            PromObj.update_object_pointers_preserves_other_header major obj wz fwd 0 o
          else begin
            hd_address_spec o;
            assert (U64.v (hd_address o) < U64.v obj);
            PromObj.update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address o)
          end;
          assert (read_word major' (hd_address o) == read_word major (hd_address o));
          color_of_header_eq o major major';
          assert (is_blue o major' = false)
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_entry)
#pop-options

/// Recursive preservation lemma: when the rewrite condition is false at addr,
/// update_promoted_iter preserves the value.
/// Proof: at each step, update_object_pointers either:
///   - doesn't touch addr (addr outside body): below/above preservation
///   - addr is inside body but condition false: field_self second conjunct
/// In both cases, value unchanged → condition still false → induction continues.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
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
          if wosize > 0 && U64.lt tag no_scan_tag && (tag <> infix_tag) then begin
            if U64.v obj + wosize * 8 <= heap_size then begin
              // tag <> infix_tag, so entry is not infix → by weakened valid_from, it's in objects
              hd_address_spec obj;
              assert (U64.uint_to_t hdr_addr_v == hd_address obj);
              tag_of_object_spec obj major;
              is_infix_spec obj major;
              assert (is_infix obj major = false);
              assert (Seq.mem obj (objects zero_addr major));
              wosize_of_object_spec obj major;
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

/// update_promoted_iter also preserves any address that is not a non-blue
/// scannable field.  The promoted_entries_not_blue_from invariant is what
/// excludes the otherwise-unsound case where farr names a blue object that
/// update_major_pointers would skip.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
let rec update_promoted_iter_preserves_non_field
  (major: heap) (farr: seq U64.t) (fwd: forwarding_map) (idx: nat) (addr: hp_addr)
  : Lemma
    (requires
      promoted_entries_valid_from major farr idx /\
      promoted_entries_not_blue_from major farr idx /\
      idx <= fwd_array_size /\
      ~(scannable_field_addr major (U64.v addr)))
    (ensures
      read_word (update_promoted_iter major farr fwd idx) addr == read_word major addr)
    (decreases (fwd_array_size - idx))
  = if idx >= fwd_array_size then ()
    else if Seq.length farr <> fwd_array_size then ()
    else begin
      let obj = Seq.index farr idx in
      if obj = 0UL then
        update_promoted_iter_preserves_non_field major farr fwd (idx + 1) addr
      else begin
        let hdr_addr_v = U64.v obj - 8 in
        if hdr_addr_v + 8 > heap_size || hdr_addr_v % 8 <> 0 then
          update_promoted_iter_preserves_non_field major farr fwd (idx + 1) addr
        else begin
          let hdr = read_word major (U64.uint_to_t hdr_addr_v) in
          let wosize = U64.v (getWosize hdr) in
          let tag = getTag hdr in
          if wosize > 0 && U64.lt tag no_scan_tag && (tag <> infix_tag) then begin
            if U64.v obj + wosize * 8 <= heap_size then begin
              hd_address_spec obj;
              assert (U64.uint_to_t hdr_addr_v == hd_address obj);
              tag_of_object_spec obj major;
              is_infix_spec obj major;
              is_no_scan_spec obj major;
              assert (is_infix obj major = false);
              assert (is_no_scan obj major = false);
              assert (Seq.mem obj (objects zero_addr major));
              assert (is_blue obj major = false);
              wosize_of_object_spec obj major;
              assert (wosize == U64.v (wosize_of_object obj major));
              assert (forall (k:nat). k < wosize ==>
                (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0));
              let major' = update_object_pointers major obj wosize fwd 0 in
              if U64.v addr < U64.v obj then begin
                PromObj.update_object_pointers_preserves_addr_below
                  major obj wosize fwd 0 addr;
                update_obj_ptrs_preserves_entries_valid major farr fwd idx;
                update_obj_ptrs_preserves_entries_not_blue_from major farr fwd idx;
                update_obj_ptrs_preserves_not_scannable_field_addr major obj wosize fwd addr;
                update_promoted_iter_preserves_non_field major' farr fwd (idx + 1) addr
              end else if U64.v addr >= U64.v obj + wosize * 8 then begin
                PromObj.update_object_pointers_preserves_addr_above
                  major obj wosize fwd 0 addr;
                update_obj_ptrs_preserves_entries_valid major farr fwd idx;
                update_obj_ptrs_preserves_entries_not_blue_from major farr fwd idx;
                update_obj_ptrs_preserves_not_scannable_field_addr major obj wosize fwd addr;
                update_promoted_iter_preserves_non_field major' farr fwd (idx + 1) addr
              end else begin
                let j = (U64.v addr - U64.v obj) / 8 in
                assert (U64.v addr == U64.v obj + j * 8);
                assert (j < wosize);
                assert (U64.v obj + j * 8 + 8 <= heap_size);
                assert ((U64.v obj + j * 8) % 8 == 0);
                assert (scannable_field_addr major (U64.v addr));
                assert false
              end
            end else
              update_promoted_iter_preserves_non_field major farr fwd (idx + 1) addr
          end else
            update_promoted_iter_preserves_non_field major farr fwd (idx + 1) addr
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
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
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
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
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

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
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

/// Recursive helper: update_all_objects_aux preserves addresses that are not
/// fields of any non-blue scannable object, irrespective of the word stored at
/// that address.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec update_all_objects_aux_preserves_non_field
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      ~(scannable_field_addr major (U64.v addr)))
    (ensures
      read_word (update_all_objects_aux major objs fwd idx) addr == read_word major addr)
    (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      assert (Seq.mem obj objs);
      if is_blue obj major then
        update_all_objects_aux_preserves_non_field major objs fwd (idx + 1) addr
      else if is_no_scan obj major then
        update_all_objects_aux_preserves_non_field major objs fwd (idx + 1) addr
      else begin
        let wz = U64.v (wosize_of_object obj major) in
        let major' = update_object_pointers major obj wz fwd 0 in
        wosize_of_object_spec obj major;
        hd_address_spec obj;
        assert (U64.v obj + wz * 8 <= heap_size);
        assert (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0));
        if U64.v addr < U64.v obj then begin
          PromObj.update_object_pointers_preserves_addr_below major obj wz fwd 0 addr;
          update_obj_ptrs_preserves_wfh major obj wz fwd;
          assert (objects zero_addr major' == objects zero_addr major);
          update_obj_ptrs_preserves_not_scannable_field_addr major obj wz fwd addr;
          update_all_objects_aux_preserves_non_field major' objs fwd (idx + 1) addr
        end else if U64.v addr >= U64.v obj + wz * 8 then begin
          PromObj.update_object_pointers_preserves_addr_above major obj wz fwd 0 addr;
          update_obj_ptrs_preserves_wfh major obj wz fwd;
          assert (objects zero_addr major' == objects zero_addr major);
          update_obj_ptrs_preserves_not_scannable_field_addr major obj wz fwd addr;
          update_all_objects_aux_preserves_non_field major' objs fwd (idx + 1) addr
        end else begin
          let j = (U64.v addr - U64.v obj) / 8 in
          assert (U64.v addr == U64.v obj + j * 8);
          assert (j < wz);
          assert (U64.v obj + j * 8 + 8 <= heap_size);
          assert ((U64.v obj + j * 8) % 8 == 0);
          assert (scannable_field_addr major (U64.v addr));
          assert false
        end
      end
    end

let update_major_pointers_preserves_non_field
  (major: heap) (fwd: forwarding_map) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      ~(scannable_field_addr major (U64.v addr)))
    (ensures
      read_word (update_major_pointers major fwd) addr == read_word major addr)
  = update_all_objects_aux_preserves_non_field major (objects zero_addr major) fwd 0 addr
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: update_major_pointers applies conditional rewrite at scannable fields
/// ---------------------------------------------------------------------------
///
/// For an address that IS a field of a scannable non-blue object with a forwarded
/// minor pointer, update_major_pointers rewrites it to the fwd target.
/// This is a direct corollary of update_major_pointers_field_effect.
/// ---------------------------------------------------------------------------
/// Helper: forwarding targets don't look like minor pointers
/// ---------------------------------------------------------------------------
///
/// After pass 1 rewrites a promoted field to fwd(offset), the resulting value
/// (a major heap address) should NOT trigger pass 2's rewrite condition.
/// This prevents double-application of the forwarding map.
///
/// Now trivially follows from fwd_targets_stable precondition.
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
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
/// Helper: RHS at a forwarded address (update_major_pointers applies fwd)
/// ---------------------------------------------------------------------------
///
/// Given witnesses obj, j from fwd_ptrs_classified part (1), the full-walk
/// update_major_pointers rewrites the field to fwd(to_minor_offset(old)).
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
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
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
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
       is_infix obj_pi major = false /\
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
    is_infix_spec obj_pi major;
    let tag = getTag (read_word major (hd_address obj_pi)) in
    assert (tag == tag_of_object obj_pi major);
    assert (U64.gte tag no_scan_tag = false);
    assert (U64.lt tag no_scan_tag);
    assert (tag <> infix_tag);
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
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
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
      // addr is NOT in any promoted body (infix entries also excluded)
      (forall (pi: nat). pi < fwd_array_size ==>
        (let obj_pi = Seq.index farr pi in
         obj_pi = 0UL \/
         is_infix obj_pi major \/
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
/// Helper: a field of obj cannot be in the body of a different object
/// ---------------------------------------------------------------------------
///
/// If addr is at offset j within obj, and obj_pi is a different object in
/// the heap, then addr is not in obj_pi's body (objects don't overlap).
#push-options "--z3rlimit 100 --fuel 3 --ifuel 1"
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
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
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
         is_infix obj_pi major \/
         U64.v addr < U64.v obj_pi \/
         U64.v addr >= U64.v obj_pi + U64.v (wosize_of_object obj_pi major) * 8)))
  = let aux (pi: nat{pi < Seq.length farr}) : Lemma
      (ensures
        (let obj_pi = Seq.index farr pi in
         obj_pi = 0UL \/
         is_infix obj_pi major \/
         U64.v addr < U64.v obj_pi \/
         U64.v addr >= U64.v obj_pi + U64.v (wosize_of_object obj_pi major) * 8))
    = let obj_pi = Seq.index farr pi in
      if obj_pi = 0UL then ()
      else if is_infix obj_pi major then ()  // Infix entries are skipped, don't affect addr
      else begin
        // obj_pi <> 0 and obj_pi <> obj (from precondition) and not infix
        // weakened promoted_entries_valid_from gives obj_pi in objects
        assert (Seq.mem obj_pi (objects zero_addr major));
        field_not_in_other_obj major obj obj_pi j addr
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: if-branch equality at a known scannable field
/// ---------------------------------------------------------------------------
///
/// The old address-only helper was intentionally removed: after
/// fwd_ptrs_classified was reformulated over (obj,j) field positions, an
/// arbitrary aligned address is not enough to recover a field witness.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let if_branch_field_eq
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  (obj: obj_addr) (j: nat) (addr: hp_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.length farr == fwd_array_size /\
      promoted_entries_valid_from major farr 0 /\
      promoted_entries_disjoint major farr /\
      well_formed_heap_part4 major /\
      valid_slot_addrs slots n /\
      slots_pairwise_distinct slots n /\
      fwd_targets_stable fwd /\
      fwd_ptrs_classified major fwd farr slots n /\
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
      (let intermediate = update_promoted_iter major farr fwd 0 in
       let lhs = rewrite_slots_iter intermediate fwd slots n 0 in
       let rhs = update_major_pointers major fwd in
       read_word lhs addr == read_word rhs addr))
  = let a = U64.v addr in
    let old_val = to_minor_offset (read_word major addr) in
    let intermediate = update_promoted_iter major farr fwd 0 in
    let lhs = rewrite_slots_iter intermediate fwd slots n 0 in
    let rhs = update_major_pointers major fwd in
    assert (a == U64.v obj + j * 8);
    Classif.fwd_ptrs_classified_field major fwd farr slots n obj j;
    if_branch_rhs major fwd obj j addr;
    assert (read_word rhs addr == fwd old_val);
    if IndDesc.strong_excluded_middle
         (exists (pi: nat). pi < fwd_array_size /\ Seq.index farr pi == obj)
    then begin
      let pi = IndDesc.indefinite_description_ghost nat
        (fun pi -> pi < fwd_array_size /\ Seq.index farr pi == obj) in
      assert (Seq.index farr pi == obj);
      assert (~(is_infix obj major));
      assert (U64.v addr >= U64.v obj);
      assert (U64.v addr < U64.v obj + U64.v (wosize_of_object obj major) * 8);
      if_branch_lhs_promoted major fwd farr slots n pi addr
    end else begin
      assert (exists (si: nat). si < n /\ U64.v (Seq.index slots si) == a);
      let si = IndDesc.indefinite_description_ghost nat
        (fun si -> si < n /\ U64.v (Seq.index slots si) == a) in
      assert (forall (pi: nat). pi < fwd_array_size ==> Seq.index farr pi <> obj);
      field_not_in_any_promoted_body major farr obj j addr;
      if_branch_lhs_slot major fwd farr slots n si addr
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Pointwise core of the main theorem, hoisted to top level.
///
/// This used to be a local `aux` inside `promoted_plus_slots_eq_full_update`.
/// As a local function its verification condition carried the whole ambient
/// context of the main theorem -- in particular every hypothesis phrased over
/// `(cheney_promote minor major_pre fp roots).major_final` -- and the resulting
/// single query is large enough that Z3 4.15.3 gives up on it ("Overflow
/// encountered when expanding vector").  Stating it over an abstract `major`
/// and `fwd` keeps the query small.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let two_pass_pointwise
  (major: heap) (fwd: forwarding_map) (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  (a: nat{a < heap_size /\ a % U64.v mword == 0})
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      well_formed_heap_part4 major /\
      Seq.length farr == fwd_array_size /\
      promoted_entries_valid_from major farr 0 /\
      promoted_entries_not_blue_from major farr 0 /\
      promoted_entries_disjoint major farr /\
      valid_slot_addrs slots n /\
      slots_pairwise_distinct slots n /\
      slots_scannable_in_major major slots n /\
      fwd_targets_stable fwd /\
      fwd_ptrs_classified major fwd farr slots n)
    (ensures
      (let intermediate = update_promoted_iter major farr fwd 0 in
       let lhs = rewrite_slots_iter intermediate fwd slots n 0 in
       let rhs = update_major_pointers major fwd in
       read_word lhs (mk_hp_addr a) == read_word rhs (mk_hp_addr a)))
  = let intermediate = update_promoted_iter major farr fwd 0 in
    let addr : hp_addr = mk_hp_addr a in
    let old_raw = read_word major addr in
    let old_val = to_minor_offset old_raw in
    if is_minor_pointer old_val && fwd old_val <> 0UL
    then begin
      if IndDesc.strong_excluded_middle (scannable_field_addr major a)
      then begin
        let obj : obj_addr = IndDesc.indefinite_description_ghost obj_addr (fun obj ->
          exists (j: nat).
            Seq.mem obj (objects zero_addr major) /\
            is_blue obj major = false /\
            is_no_scan obj major = false /\
            j < U64.v (wosize_of_object obj major) /\
            a == U64.v obj + j * 8 /\
            U64.v obj + j * 8 + 8 <= heap_size /\
            (U64.v obj + j * 8) % 8 == 0) in
        let j : nat = IndDesc.indefinite_description_ghost nat (fun j ->
            Seq.mem obj (objects zero_addr major) /\
            is_blue obj major = false /\
            is_no_scan obj major = false /\
            j < U64.v (wosize_of_object obj major) /\
            a == U64.v obj + j * 8 /\
            U64.v obj + j * 8 + 8 <= heap_size /\
            (U64.v obj + j * 8) % 8 == 0) in
        if_branch_field_eq major fwd farr slots n obj j addr
      end else begin
        update_major_pointers_preserves_non_field major fwd addr;
        update_promoted_iter_preserves_non_field major farr fwd 0 addr;
        slots_frame_from_non_field major slots n addr;
        rewrite_slots_iter_frame intermediate fwd slots n 0 addr
      end
    end else begin
      update_major_pointers_preserves_non_fwd major fwd addr;
      update_promoted_iter_preserves_non_fwd major farr fwd 0 addr;
      rewrite_slots_iter_preserves_non_fwd intermediate fwd slots n 0 addr
    end
#pop-options

/// Main theorem: two-pass rewriting equals full update
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 150 --fuel 0 --ifuel 0"
let promoted_plus_slots_eq_full_update
  (minor: minor_state) (major_pre: heap) (fp: U64.t) (roots: seq U64.t)
  (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       promoted_entries_valid_from prom.major_final farr 0 /\
       promoted_entries_disjoint prom.major_final farr /\
       promoted_entries_not_blue prom.major_final farr /\
       well_formed_heap_part4 prom.major_final /\
       valid_slot_addrs slots n /\
       slots_pairwise_distinct slots n /\
       ref_table_sound major_pre slots n /\
       slots_scannable_in_major prom.major_final slots n /\
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
    assert (promoted_entries_not_blue_from major farr 0);
    // Strategy: show read_word lhs a == read_word rhs a for every aligned
    // address.  The forwarded-pointer case is handled only after extracting an
    // explicit non-blue scannable field witness; headers and other non-fields
    // need separate frame lemmas and must not use fwd_ptrs_classified.
    let aux (a: nat{a < heap_size /\ a % U64.v mword == 0})
      : Lemma (read_word lhs (mk_hp_addr a) == read_word rhs (mk_hp_addr a))
      = two_pass_pointwise major fwd farr slots n a
    in
    FStar.Classical.forall_intro aux;
    heap_read_word_extensional_mk lhs rhs
#pop-options
