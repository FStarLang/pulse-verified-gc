/// ---------------------------------------------------------------------------
/// GC.Gen.Promote — Specification of minor→major object promotion (copying)
/// ---------------------------------------------------------------------------
///
/// When the minor heap is full, all live minor-heap objects are promoted
/// (copied) to the major heap. This module defines:
///
/// 1. promote_object: copy a single minor object to the major heap
/// 2. promote_all: promote all reachable objects from a set of roots
/// 3. update_pointers: rewrite minor-heap pointers to their new major addresses
///
/// After promotion, the minor heap is reset (bump pointer → 0).
///
/// Key correctness property: every object reachable from roots in the
/// pre-promotion state is present in the post-promotion major heap with
/// identical field data (modulo pointer updates).

module GC.Gen.Promote

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Forwarding Map
/// ---------------------------------------------------------------------------

/// A forwarding map records where each minor object was placed in the major heap.
/// It maps minor_obj_addr → major_obj_addr (or 0 if not promoted).
let forwarding_map = U64.t -> GTot U64.t

/// Empty forwarding: nothing promoted yet
let empty_forwarding : forwarding_map = fun _ -> 0UL

/// Extend forwarding with a new mapping
let extend_forwarding (fwd: forwarding_map) (minor_addr: U64.t) (major_addr: U64.t) : forwarding_map =
  fun a -> if a = minor_addr then major_addr else fwd a

/// ---------------------------------------------------------------------------
/// Promote a Single Object
/// ---------------------------------------------------------------------------

/// Result of promoting one object
noeq
type promote_one_result = {
  major_out : heap;         // updated major heap
  fp_out    : U64.t;        // updated major free-list pointer
  new_addr  : U64.t;        // address of object in major heap (0 if failed)
}

/// Set the tag in a promoted object's header.
/// Reads the current header, builds a new one with same wosize + white color + new tag.
/// When obj is not a valid obj_addr or tag >= 256, returns the heap unchanged.
let set_promoted_tag (major: heap) (obj: U64.t) (tag: nat) : GTot heap =
  if tag >= 256 then major
  else if U64.v obj >= U64.v mword && U64.v obj < heap_size && U64.v obj % U64.v mword = 0 then
    let hd = hd_address (obj <: obj_addr) in
    let hdr = read_word major hd in
    let wz = getWosize hdr in
    let new_hdr = makeHeader wz White (U64.uint_to_t tag) in
    write_word major hd new_hdr
  else major

/// Zero the padding field after copy_fields, if the allocator gave a block
/// larger than requested (leftover=1 case: block_wz = requested_wz + 1).
/// This ensures the padding slot is provably non-pointer.
/// When actual_wz == copied_wz (exact-fit or split), this is a no-op.
let zero_promote_padding (g: heap) (dst: U64.t) (copied_wz: nat)
  : GTot heap
  = if U64.v dst >= U64.v mword && U64.v dst < heap_size && U64.v dst % U64.v mword = 0 then
      let obj : obj_addr = dst in
      let actual_wz = U64.v (wosize_of_object obj g) in
      if actual_wz > copied_wz then
        let pad_nat = U64.v dst + copied_wz * U64.v mword in
        if pad_nat < heap_size && pad_nat % U64.v mword = 0 then
          write_word g (U64.uint_to_t pad_nat <: hp_addr) 0UL
        else g
      else g
    else g

/// Promote a single object from minor heap to major heap.
///
/// 1. Read wosize and tag from minor object header
/// 2. Allocate in major heap via the major allocator
/// 3. Copy field data from minor to major
/// 4. Zero any padding field (leftover=1 allocator case)
/// 5. Set the correct tag from the minor header
///
/// If major allocation fails (OOM), returns new_addr = 0.
let promote_object (minor: minor_state) (major: heap) (obj: U64.t)
                   (fp: U64.t) (wosize: nat{wosize > 0})
  : GTot promote_one_result =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  let new_major = alloc_res.heap_out in
  let new_fp = alloc_res.fp_out in
  let new_addr = alloc_res.obj_out in
  if new_addr = 0UL then
    { major_out = major; fp_out = fp; new_addr = 0UL }
  else
    let copied_major = copy_fields minor new_major obj new_addr 0 wosize in
    let padded_major = zero_promote_padding copied_major new_addr wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    let final_major = set_promoted_tag padded_major new_addr tag in
    { major_out = final_major; fp_out = new_fp; new_addr = new_addr }

/// Unfold: when alloc fails (OOM), promote_object returns original heap/fp unchanged.
val promote_object_oom (minor: minor_state) (major: heap) (obj: U64.t)
                       (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out == 0UL)
          (ensures (let res = promote_object minor major obj fp wosize in
                    res.major_out == major /\ res.fp_out == fp /\ res.new_addr == 0UL))

/// Unfold: when alloc succeeds, promote_object = alloc + copy_fields + zero_padding + set_tag.
val promote_object_success (minor: minor_state) (major: heap) (obj: U64.t)
                           (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out <> 0UL)
          (ensures (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
                    let res = promote_object minor major obj fp wosize in
                    let copied = copy_fields minor alloc_res.heap_out obj alloc_res.obj_out 0 wosize in
                    let padded = zero_promote_padding copied alloc_res.obj_out wosize in
                    let tag = minor_tag minor obj in
                    res.major_out == set_promoted_tag padded alloc_res.obj_out tag /\
                    res.fp_out == alloc_res.fp_out /\
                    res.new_addr == alloc_res.obj_out))

/// Unfold set_promoted_tag: when tag < 256 and obj is a valid obj_addr,
/// set_promoted_tag is just a header write.
val set_promoted_tag_unfold
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (set_promoted_tag major obj tag ==
           write_word major (hd_address obj)
             (makeHeader (getWosize (read_word major (hd_address obj)))
                         White (U64.uint_to_t tag)))

/// zero_promote_padding frame: reads at addresses != padding slot are unchanged.
val zero_promote_padding_frame
  (g: heap) (dst: obj_addr) (wz: nat) (addr: hp_addr)
  : Lemma (requires U64.v addr <> U64.v dst + wz * U64.v mword)
          (ensures read_word (zero_promote_padding g dst wz) addr == read_word g addr)

/// zero_promote_padding preserves wosize (only writes to a field, not a header).
val zero_promote_padding_preserves_wosize
  (g: heap) (dst: obj_addr) (wz: nat)
  : Lemma (wosize_of_object dst (zero_promote_padding g dst wz) == wosize_of_object dst g)

/// zero_promote_padding is identity when actual_wz == wz (exact fit / split case).
val zero_promote_padding_noop
  (g: heap) (dst: obj_addr) (wz: nat)
  : Lemma (requires U64.v (wosize_of_object dst g) <= wz)
          (ensures zero_promote_padding g dst wz == g)

/// zero_promote_padding writes 0UL at padding position when actual_wz > wz.
val zero_promote_padding_write
  (g: heap) (dst: obj_addr) (wz: nat)
  : Lemma (requires U64.v (wosize_of_object dst g) > wz /\
                    U64.v dst + wz * U64.v mword < heap_size)
          (ensures zero_promote_padding g dst wz ==
                   write_word g (U64.uint_to_t (U64.v dst + wz * U64.v mword) <: hp_addr) 0UL)

/// zero_promote_padding preserves objects enumeration (field write, not header).
val zero_promote_padding_preserves_objects
  (g: heap) (dst: obj_addr) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem dst (objects zero_addr g))
          (ensures objects zero_addr (zero_promote_padding g dst wz) == objects zero_addr g)
/// Header-specific frame: for any distinct object, its header is unchanged.
val zero_promote_padding_frame_obj_header
  (g: heap) (dst src: obj_addr) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem dst (objects zero_addr g) /\
                    Seq.mem src (objects zero_addr g) /\
                    src <> dst)
          (ensures read_word (zero_promote_padding g dst wz) (hd_address src)
                == read_word g (hd_address src))

/// zero_promote_padding preserves well_formed_heap_part1.
val zero_promote_padding_preserves_wfh_part1
  (g: heap) (dst: obj_addr) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem dst (objects zero_addr g))
          (ensures well_formed_heap_part1 (zero_promote_padding g dst wz))

/// set_promoted_tag preserves the objects enumeration (same wosize → same objects list)
val set_promoted_tag_preserves_objects
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires Seq.mem obj (objects zero_addr major))
          (ensures objects zero_addr (set_promoted_tag major obj tag) ==
                   objects zero_addr major)

/// set_promoted_tag preserves reads at addresses disjoint from the header of obj
val set_promoted_tag_read_frame
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256}) (addr: hp_addr)
  : Lemma (requires (U64.v addr + U64.v mword <= U64.v (hd_address obj) \/
                     U64.v (hd_address obj) + U64.v mword <= U64.v addr))
          (ensures read_word (set_promoted_tag major obj tag) addr == read_word major addr)

/// set_promoted_tag preserves allocator invariants (wfh_part1, fl_valid, fl_chain_terminates)
/// because it writes to a header position that is not in the free-list chain,
/// and the new header has the same wosize as the old one.
val set_promoted_tag_preserves_alloc_invariants
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256}) (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem obj (objects zero_addr major) /\
             AllocLemmas.fl_valid major fp heap_words /\
             AllocLemmas.fl_chain_terminates major fp heap_words /\
             AllocLemmas.chain_avoids major fp obj heap_words = true)
          (ensures (let g' = set_promoted_tag major obj tag in
                    well_formed_heap_part1 g' /\
                    AllocLemmas.fl_valid g' fp heap_words /\
                    AllocLemmas.fl_chain_terminates g' fp heap_words))

/// zero_promote_padding preserves allocator invariants.
/// In the noop case (exact fit), everything trivially holds.
/// In the write case, uses write_body_preserves_* helpers since the padding
/// position is a field of dst, which is excluded from the free-list chain.
val zero_promote_padding_preserves_alloc_invariants
  (g: heap) (dst: obj_addr) (wz: nat) (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 g /\
             Seq.mem dst (objects zero_addr g) /\
             AllocLemmas.fl_valid g fp heap_words /\
             AllocLemmas.fl_chain_terminates g fp heap_words /\
             AllocLemmas.chain_avoids g fp dst heap_words = true)
          (ensures (let g' = zero_promote_padding g dst wz in
                    well_formed_heap_part1 g' /\
                    Seq.mem dst (objects zero_addr g') /\
                    AllocLemmas.fl_valid g' fp heap_words /\
                    AllocLemmas.fl_chain_terminates g' fp heap_words /\
                    AllocLemmas.chain_avoids g' fp dst heap_words = true))

/// zero_promote_padding preserves well_formed_heap_part4 (no infix objects).
val zero_promote_padding_preserves_wfh_part4
  (g: heap) (dst: obj_addr) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    well_formed_heap_part4 g /\
                    Seq.mem dst (objects zero_addr g))
          (ensures well_formed_heap_part4 (zero_promote_padding g dst wz))

/// promote_object preserves allocator invariants (wfh_part1, fl_valid, fl_chain_terminates).
/// Combines alloc_spec, copy_fields, and set_promoted_tag preservation in one lemma.
val promote_object_preserves_alloc_invariants
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp heap_words /\
             AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = promote_object minor major obj fp wosize in
                    well_formed_heap_part1 res.major_out /\
                    AllocLemmas.fl_valid res.major_out res.fp_out heap_words /\
                    AllocLemmas.fl_chain_terminates res.major_out res.fp_out heap_words))

/// The promoted copy has room for the whole object, not merely its header.
///
/// `alloc_spec_obj_valid` bounds only the object address.  A caller that has to
/// address a byte *inside* the copy --- forwarding an interior pointer lands at
/// `new_addr + delta` for some `delta` below `wosize * 8` --- needs the body to
/// fit as well.  It does: the block is an object of the resulting heap, and
/// part 1 of well-formedness is exactly the statement that an object's body
/// lies within the heap.
val promote_object_new_addr_body_bound
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp heap_words /\
             AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = promote_object minor major obj fp wosize in
                    res.new_addr <> 0UL ==>
                    U64.v res.new_addr + wosize * 8 <= heap_size))

/// ---------------------------------------------------------------------------
/// Promote All Live Objects
/// ---------------------------------------------------------------------------

/// The set of roots for minor collection includes:
/// - Program stack roots (mutator roots pointing into minor heap)
/// - Remembered set (major-heap objects pointing into minor heap)
///
/// "Live" minor objects = objects reachable from these roots via
/// pointer fields within the minor heap.

/// Result of promoting all live objects
noeq
type promote_all_result = {
  major_final : heap;            // final major heap state
  fp_final    : U64.t;           // final free-list pointer
  fwd_map     : forwarding_map;  // maps old minor addrs to new major addrs
}
/// ---------------------------------------------------------------------------
/// Pointer Update
/// ---------------------------------------------------------------------------

/// After all objects are promoted, update pointers:
/// - In the major heap: any field that pointed to a minor address
///   gets rewritten to the forwarded major address.
/// - In the roots: update root pointers similarly.
///
/// This ensures no dangling references to the (about to be reset) minor heap.

/// Check if a value looks like a minor-heap pointer
let is_minor_pointer (v: U64.t) : bool =
  U64.v v >= 8 && U64.v v < minor_heap_size && U64.v v % 8 = 0

/// Update pointers in one object's fields: iterate fields [i, wosize) and rewrite
/// minor-heap pointers via the forwarding map.
let rec update_object_pointers (major: heap) (obj: U64.t) (wosize: nat)
                               (fwd: forwarding_map) (i: nat)
  : GTot heap (decreases (wosize - i)) =
  if i >= wosize then major
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then major
    else
      let field_val = to_minor_offset (read_word major (U64.uint_to_t field_offset)) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then
          let major' = write_word major (U64.uint_to_t field_offset) new_val in
          update_object_pointers major' obj wosize fwd (i + 1)
        else
          update_object_pointers major obj wosize fwd (i + 1)
      else
        update_object_pointers major obj wosize fwd (i + 1)

/// Unfold lemma: one step of update_object_pointers when i < wosize
val update_object_pointers_step (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
  : Lemma (requires i < wosize /\
                    U64.v obj + i * 8 + 8 <= heap_size /\
                    (U64.v obj + i * 8) % 8 = 0)
          (ensures (let field_offset = U64.v obj + i * 8 in
                    let field_val = to_minor_offset (read_word major (U64.uint_to_t field_offset)) in
                    update_object_pointers major obj wosize fwd i ==
                    (if is_minor_pointer field_val then
                       let new_val = fwd field_val in
                       if new_val <> 0UL then
                         update_object_pointers (write_word major (U64.uint_to_t field_offset) new_val) obj wosize fwd (i + 1)
                       else
                         update_object_pointers major obj wosize fwd (i + 1)
                     else
                       update_object_pointers major obj wosize fwd (i + 1))))

/// Base case: update_object_pointers at i >= wosize is identity
val update_object_pointers_done (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
  : Lemma (requires i >= wosize)
          (ensures update_object_pointers major obj wosize fwd i == major)

/// ---------------------------------------------------------------------------
/// update_all_objects_aux — exposed for Pulse implementation
/// ---------------------------------------------------------------------------

/// Exposed recursive worker: processes objects in `objs` starting at index `idx`
let rec update_all_objects_aux (major: heap) (objs: seq obj_addr)
                               (fwd: forwarding_map) (idx: nat)
  : GTot heap (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then major
  else
    let obj = Seq.index objs idx in
    if is_blue obj major then
      update_all_objects_aux major objs fwd (idx + 1)
    else if is_no_scan obj major then
      update_all_objects_aux major objs fwd (idx + 1)
    else
      let wz = U64.v (wosize_of_object obj major) in
      let major' = update_object_pointers major obj wz fwd 0 in
      update_all_objects_aux major' objs fwd (idx + 1)

/// Update all pointers in the major heap that refer to minor addresses
let update_major_pointers (major: heap) (fwd: forwarding_map) : GTot heap =
  update_all_objects_aux major (objects zero_addr major) fwd 0

/// ---------------------------------------------------------------------------
/// Live Set and Root Rewriting
/// ---------------------------------------------------------------------------

/// Compute the live set: minor objects reachable from program roots combined
/// with the remembered set (major-heap objects pointing into the minor heap).
let live_set_of (minor: minor_state) (major: heap) (roots: seq U64.t) : GTot (seq U64.t) =
  let remembered = minor_roots_from_major major in
  minor_reachable minor (Seq.append roots remembered)

/// Rewrite a single root: if it's a minor pointer that was forwarded, use the new address
let rewrite_root (r: U64.t) (fwd: forwarding_map) : GTot U64.t =
  if is_minor_pointer r && fwd r <> 0UL then fwd r else r

/// Rewrite all roots using the forwarding map
let rec rewrite_roots (roots: seq U64.t) (fwd: forwarding_map)
  : GTot (seq U64.t) (decreases (Seq.length roots)) =
  if Seq.length roots = 0 then Seq.empty
  else
    let r = Seq.index roots 0 in
    let new_r = rewrite_root r fwd in
    let rest = Seq.slice roots 1 (Seq.length roots) in
    Seq.cons new_r (rewrite_roots rest fwd)

/// rewrite_roots has the same length as roots
val rewrite_roots_length (roots: seq U64.t) (fwd: forwarding_map)
  : Lemma (ensures Seq.length (rewrite_roots roots fwd) == Seq.length roots)
    [SMTPat (rewrite_roots roots fwd)]

/// rewrite_roots applies rewrite_root pointwise
val rewrite_roots_index (roots: seq U64.t) (fwd: forwarding_map) (i: nat)
  : Lemma (requires i < Seq.length roots)
          (ensures Seq.index (rewrite_roots roots fwd) i == rewrite_root (Seq.index roots i) fwd)

/// If a sequence has rewrite_root applied pointwise, it equals rewrite_roots
val rewrite_roots_pointwise (roots: seq U64.t) (fwd: forwarding_map) (rs2: seq U64.t)
  : Lemma (requires Seq.length rs2 == Seq.length roots /\
                    (forall (j: nat). j < Seq.length roots ==>
                      Seq.index rs2 j == rewrite_root (Seq.index roots j) fwd))
          (ensures rs2 == rewrite_roots roots fwd)

/// ---------------------------------------------------------------------------
/// Minor Collection (Full Spec)
/// ---------------------------------------------------------------------------

/// Result of a complete minor collection
noeq
type minor_collect_result = {
  mc_major  : heap;            // post-collection major heap
  mc_fp     : U64.t;           // post-collection free-list pointer
  mc_minor  : minor_state;     // reset minor heap (bump = 0)
  mc_roots  : seq U64.t;       // rewritten roots (minor pointers → major addresses)
  mc_fwd    : forwarding_map;  // forwarding map (for spec-level reasoning)
}
/// ---------------------------------------------------------------------------
/// Correctness Properties
/// ---------------------------------------------------------------------------

/// Helper: all destination addresses in copy_fields are valid hp_addr
let dst_fields_valid (dst_obj: U64.t) (n: nat) : prop =
  (forall (j:nat). j < n ==>
    (U64.v dst_obj + j * 8 + 8 <= heap_size /\
     (U64.v dst_obj + j * 8) % 8 == 0))
/// Derive dst_fields_valid from scalar upper bound + alignment
val dst_fields_valid_from_bounds (addr: U64.t) (wz: pos)
  : Lemma (requires U64.v addr % 8 == 0 /\ U64.v addr + (wz - 1) * 8 + 8 <= heap_size)
          (ensures dst_fields_valid addr wz)

/// copy_fields doesn't modify addresses outside the dst region
val copy_fields_frame
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      dst_fields_valid dst_obj n /\
      U64.v dst_obj % 8 == 0 /\
      (U64.v addr + 8 <= U64.v dst_obj \/
       U64.v addr >= U64.v dst_obj + n * 8))
    (ensures
      read_word (copy_fields minor major src_obj dst_obj i n) addr ==
      read_word major addr)

/// Key lemma: copy_fields correctly copies all fields
val copy_fields_all_correct
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (n: nat)
  : Lemma
    (requires
      dst_fields_valid dst_obj n /\
      U64.v dst_obj % 8 == 0)
    (ensures
      (let result = copy_fields minor major src_obj dst_obj 0 n in
       (forall (j:nat). j < n ==>
         read_word result (U64.uint_to_t (U64.v dst_obj + j * 8)) ==
         minor_read_field minor src_obj j)))

/// After promotion, field data is preserved: every field of the promoted
/// object in the major heap equals the corresponding minor-heap field.
val promote_preserves_fields
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             U64.v obj >= 8 /\ U64.v obj < minor_heap_size)
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              dst_fields_valid res.new_addr wosize ==>
              U64.v res.new_addr % 8 == 0 ==>
              (forall (j:nat). j < wosize ==>
                read_word res.major_out (U64.uint_to_t (U64.v res.new_addr + j * 8)) ==
                minor_read_field minor obj j)))

/// If allocation rounded a promoted block up by one word, the extra field is
/// zeroed by `zero_promote_padding`, hence cannot be a pointer.
val promote_object_extra_field_not_pointer
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wz: nat{wz > 0}) (field_idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL /\
       U64.v res.new_addr >= U64.v mword /\
       U64.v res.new_addr < heap_size /\
       U64.v res.new_addr % U64.v mword == 0 /\
       field_idx >= wz /\
       field_idx < U64.v (wosize_of_object (res.new_addr <: obj_addr) res.major_out) /\
       U64.v res.new_addr + field_idx * 8 < heap_size /\
       (U64.v res.new_addr + field_idx * 8) % U64.v mword == 0))
     (ensures
       (let res = promote_object minor major obj fp wz in
        let field_addr : hp_addr =
          U64.uint_to_t (U64.v res.new_addr + field_idx * 8) in
        read_word res.major_out field_addr == 0UL /\
        ~(is_pointer_field (read_word res.major_out field_addr))))
/// promote_object preserves objects (part1 version — no full well_formed_heap needed)
val promote_object_preserves_objects_part1
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             GC.Spec.Allocator.Lemmas.fl_valid major fp heap_words /\
             GC.Spec.Allocator.Lemmas.fl_chain_terminates major fp heap_words)
          (ensures
             (let res = promote_object minor major obj fp wosize in
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.major_out))))
/// promote_object preserves well_formed_heap_part4 (no infix objects) when the
/// promoted minor object has a non-infix tag (tag <> 249).
val promote_object_preserves_wfh_part4
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             well_formed_heap_part4 major /\
             AllocLemmas.fl_valid major fp heap_words /\
             AllocLemmas.fl_chain_terminates major fp heap_words /\
             minor_tag minor obj <> U64.v GC.Spec.Object.infix_tag)
           (ensures (let res = promote_object minor major obj fp wosize in
                     well_formed_heap_part4 res.major_out))

/// ---------------------------------------------------------------------------
/// Heap objects density definition (used by PromoteUpdate)
/// ---------------------------------------------------------------------------

/// Heap objects density: all objects reachable from the linear scan are valid.
let heap_objects_dense (g: heap) : prop =
  forall (start: hp_addr).
    U64.v start + 8 < heap_size ==>
    Seq.mem (f_address start) (objects zero_addr g) ==>
    Seq.length (objects start g) > 0 ==>
    (let wz = getWosize (read_word g start) in
     let next = U64.v start + ((U64.v wz + 1) * 8) in
     next + 8 < heap_size ==>
     Seq.length (objects (U64.uint_to_t next) g) > 0 /\
     Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g))

/// Blue fields closed: for blue (free-list) objects, all pointer fields
/// target valid objects in the heap.
[@@"opaque_to_smt"]
let blue_fields_closed (major: heap) : prop =
  forall (src: obj_addr) (j: nat).
    Seq.mem src (objects zero_addr major) /\ is_blue src major /\
    j < U64.v (wosize_of_object src major) /\
    U64.v src + j * 8 + 8 <= heap_size ==>
    (let v = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
     is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr major))
/// All free-chain objects are blue (standard allocator invariant).
[@@"opaque_to_smt"]
let chain_objects_blue (major: heap) (fp: U64.t) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr major) /\ ~(is_blue obj major) ==>
    AllocLemmas.chain_avoids major fp obj heap_words = true
