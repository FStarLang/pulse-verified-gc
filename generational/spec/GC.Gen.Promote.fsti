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
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids major fp obj (heap_size / U64.v mword) = true)
          (ensures (let g' = set_promoted_tag major obj tag in
                    well_formed_heap_part1 g' /\
                    AllocLemmas.fl_valid g' fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g' fp (heap_size / U64.v mword)))

/// zero_promote_padding preserves allocator invariants.
/// In the noop case (exact fit), everything trivially holds.
/// In the write case, uses write_body_preserves_* helpers since the padding
/// position is a field of dst, which is excluded from the free-list chain.
val zero_promote_padding_preserves_alloc_invariants
  (g: heap) (dst: obj_addr) (wz: nat) (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 g /\
             Seq.mem dst (objects zero_addr g) /\
             AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids g fp dst (heap_size / U64.v mword) = true)
          (ensures (let g' = zero_promote_padding g dst wz in
                    well_formed_heap_part1 g' /\
                    Seq.mem dst (objects zero_addr g') /\
                    AllocLemmas.fl_valid g' fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g' fp (heap_size / U64.v mword) /\
                    AllocLemmas.chain_avoids g' fp dst (heap_size / U64.v mword) = true))

/// promote_object preserves allocator invariants (wfh_part1, fl_valid, fl_chain_terminates).
/// Combines alloc_spec, copy_fields, and set_promoted_tag preservation in one lemma.
val promote_object_preserves_alloc_invariants
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_object minor major obj fp wosize in
                    well_formed_heap_part1 res.major_out /\
                    AllocLemmas.fl_valid res.major_out res.fp_out (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.major_out res.fp_out (heap_size / U64.v mword)))

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

/// Promote objects from `live_set[idx..]` using accumulated forwarding map.
/// Continuation form: "what remains to do from the current state."
let rec promote_all_aux (minor: minor_state) (major: heap)
                    (fp: U64.t) (live_set: seq U64.t)
                    (fwd: forwarding_map) (idx: nat)
  : GTot promote_all_result (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then
    { major_final = major; fp_final = fp; fwd_map = fwd }
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      promote_all_aux minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then
        { major_final = major; fp_final = fp; fwd_map = fwd }
      else
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux minor res.major_out res.fp_out live_set fwd' (idx + 1)

/// Promote all objects listed in `live_set` (in order).
/// Each promotion allocates in the major heap and records the forwarding.
let promote_all_spec (minor: minor_state) (major: heap)
                     (fp: U64.t) (live_set: seq U64.t)
  : GTot promote_all_result =
  promote_all_aux minor major fp live_set empty_forwarding 0

/// Unfold: promote_all_aux when idx >= length
val promote_all_aux_base (minor: minor_state) (major: heap)
                         (fp: U64.t) (live_set: seq U64.t)
                         (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx >= Seq.length live_set)
          (ensures promote_all_aux minor major fp live_set fwd idx ==
                   { major_final = major; fp_final = fp; fwd_map = fwd })

/// Unfold: promote_all_aux when wz > 0 and allocation succeeds
val promote_all_aux_step (minor: minor_state) (major: heap)
                         (fp: U64.t) (live_set: seq U64.t)
                         (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length live_set /\
                    (let obj = Seq.index live_set idx in
                     let wz = minor_wosize minor obj in
                     wz > 0 /\
                     (let res = promote_object minor major obj fp wz in
                      res.new_addr <> 0UL)))
          (ensures (let obj = Seq.index live_set idx in
                    let wz = minor_wosize minor obj in
                    let res = promote_object minor major obj fp wz in
                    let fwd' = extend_forwarding fwd obj res.new_addr in
                    promote_all_aux minor major fp live_set fwd idx ==
                    promote_all_aux minor res.major_out res.fp_out live_set fwd' (idx + 1)))

/// Unfold: promote_all_aux when wz = 0 (skip)
val promote_all_aux_skip (minor: minor_state) (major: heap)
                         (fp: U64.t) (live_set: seq U64.t)
                         (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length live_set /\
                    minor_wosize minor (Seq.index live_set idx) = 0)
          (ensures promote_all_aux minor major fp live_set fwd idx ==
                   promote_all_aux minor major fp live_set fwd (idx + 1))

/// Unfold: promote_all_aux when allocation fails (OOM)
val promote_all_aux_oom (minor: minor_state) (major: heap)
                        (fp: U64.t) (live_set: seq U64.t)
                        (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length live_set /\
                    (let obj = Seq.index live_set idx in
                     let wz = minor_wosize minor obj in
                     wz > 0 /\
                     (promote_object minor major obj fp wz).new_addr = 0UL))
          (ensures promote_all_aux minor major fp live_set fwd idx ==
                   { major_final = major; fp_final = fp; fwd_map = fwd })

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
      let field_val = read_word major (U64.uint_to_t field_offset) in
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
                    let field_val = read_word major (U64.uint_to_t field_offset) in
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

/// Full minor collection specification:
/// 1. Determine live set (reachable from roots + remembered set)
/// 2. Promote all live objects to major heap
/// 3. Update pointers in major heap
/// 4. Rewrite roots to point to new major addresses
/// 5. Reset minor heap
///
/// Parameters:
///   minor: current minor heap state
///   major: current major heap state
///   fp: current major-heap free-list pointer
///   roots: addresses of root pointers (program stack)
let minor_collect_spec (minor: minor_state) (major: heap)
                       (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result =
  let live_set = live_set_of minor major roots in
  let prom_res = promote_all_spec minor major fp live_set in
  let updated_major = update_major_pointers prom_res.major_final prom_res.fwd_map in
  let new_roots = rewrite_roots roots prom_res.fwd_map in
  { mc_major = updated_major;
    mc_fp = prom_res.fp_final;
    mc_minor = minor_reset minor;
    mc_roots = new_roots;
    mc_fwd = prom_res.fwd_map }

/// Unfold lemma: mc_major is update_major_pointers applied to promote_all result
val minor_collect_spec_unfold (minor: minor_state) (major: heap)
                              (fp: U64.t) (roots: seq U64.t)
  : Lemma (let live_set = live_set_of minor major roots in
           let prom_res = promote_all_spec minor major fp live_set in
           (minor_collect_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_spec minor major fp roots).mc_fp == prom_res.fp_final)

/// Unfold lemma: mc_minor is minor_reset minor (well-formed, bump = 0)
val minor_collect_resets_minor (minor: minor_state) (major: heap)
                               (fp: U64.t) (roots: seq U64.t)
  : Lemma (let res = minor_collect_spec minor major fp roots in
           minor_wf res.mc_minor /\ U64.v res.mc_minor.bump == 0)

/// Unfold lemma: mc_roots is rewrite_roots applied to roots
val minor_collect_rewrites_roots (minor: minor_state) (major: heap)
                                  (fp: U64.t) (roots: seq U64.t)
  : Lemma (let res = minor_collect_spec minor major fp roots in
           res.mc_roots == rewrite_roots roots res.mc_fwd)

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

/// copy_fields preserves the objects walk (writes only within object bodies, never headers)
val copy_fields_preserves_objects
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             well_formed_heap major /\
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n)
          (ensures
             objects zero_addr (copy_fields minor major src_obj dst_obj 0 n) == objects zero_addr major)

/// promote_object preserves existing object membership
val promote_object_preserves_objects
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap major /\
             GC.Spec.Allocator.Lemmas.fl_valid major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.major_out))))

/// copy_fields preserves the allocator invariants (wfh_part1, fl_valid, fl_chain_terminates)
/// when dst_obj is not in the free-list chain.
/// This is the key lemma enabling Pulse promote_one to maintain loop invariants.
val copy_fields_preserves_alloc_invariants
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat{n > 0})
  (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids major fp dst_obj (heap_size / U64.v mword) = true)
           (ensures (let g' = copy_fields minor major src_obj dst_obj 0 n in
                     well_formed_heap_part1 g' /\
                     AllocLemmas.fl_valid g' fp (heap_size / U64.v mword) /\
                     AllocLemmas.fl_chain_terminates g' fp (heap_size / U64.v mword)))

/// promote_object preserves objects (part1 version — no full well_formed_heap needed)
val promote_object_preserves_objects_part1
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             GC.Spec.Allocator.Lemmas.fl_valid major fp (heap_size / U64.v mword) /\
             GC.Spec.Allocator.Lemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.major_out))))

/// promote_all_spec preserves existing object membership
val promote_all_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires
             well_formed_heap major /\
             GC.Spec.Allocator.Lemmas.fl_valid major fp (heap_size / U64.v mword) /\
             GC.Spec.Allocator.Lemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_all_spec minor major fp live_set in
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.major_final))))

/// promote_all_spec preserves well_formed_heap_part1
val promote_all_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (promote_all_spec minor major fp live_set).major_final)

/// promote_all_spec preserves well_formed_heap_part4 (no infix objects)
/// Requires that no promoted object has infix_tag (249), since setting an
/// infix tag on a major-heap object would violate the no-infix invariant.
/// In practice, minor objects in the live set are independently allocated
/// (not infix headers embedded within closures), so this always holds.
let live_set_no_infix (minor: minor_state) (live_set: seq U64.t) : prop =
  forall (i: nat). i < Seq.length live_set ==>
    minor_tag minor (Seq.index live_set i) <> U64.v GC.Spec.Object.infix_tag

val promote_all_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    live_set_no_infix minor live_set)
          (ensures well_formed_heap_part4 (promote_all_spec minor major fp live_set).major_final)

/// ---------------------------------------------------------------------------
/// Minor No-Scan Invariant
/// ---------------------------------------------------------------------------

/// No-scan objects in the minor heap (tag >= 251) contain only raw data:
/// no field looks like a valid heap pointer. This mirrors the major-heap
/// no_scan_invariant and ensures that after promotion, the major-heap
/// no_scan_invariant is maintained for promoted no-scan objects.
let minor_no_scan_invariant (minor: minor_state) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    minor_tag minor obj >= 251 /\
    j < minor_wosize minor obj ==>
    ~(is_pointer_field (minor_read_field minor obj j))

/// Allocated (non-blue) objects avoid the free-list chain.
/// (Defined here for use in the no-scan preservation proof.)
let allocated_avoid_chain (major: heap) (fp: U64.t) : prop =
  forall (x: obj_addr).
    Seq.mem x (objects zero_addr major) /\ ~(is_blue x major) ==>
    AllocLemmas.chain_avoids major fp x (heap_size / U64.v mword) = true

/// promote_all_spec preserves no_scan_invariant: after promoting all live
/// minor objects, no-scan objects in the post-promote major heap still have
/// non-pointer field values.
val promote_all_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    no_scan_invariant major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    allocated_avoid_chain major fp /\
                    (forall (k:nat). k < Seq.length live_set ==>
                      Seq.mem (Seq.index live_set k) (minor_objects minor)))
          (ensures no_scan_invariant (promote_all_spec minor major fp live_set).major_final)

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


/// Predicate: every forwarded object's address is in the objects of heap g
let fwd_targets_in_objects (fwd: forwarding_map) (live_set: seq U64.t) (idx: nat) (g: heap) : prop =
  forall (k:nat). k < idx /\ k < Seq.length live_set ==>
    (let obj = Seq.index live_set k in
     fwd obj <> 0UL ==>
     (U64.v (fwd obj) >= U64.v mword /\
      U64.v (fwd obj) < heap_size /\
      U64.v (fwd obj) % U64.v mword == 0 /\
      Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr g)))

/// Stronger invariant: for ANY address x, if fwd(x) ≠ 0, then fwd(x) is valid object in g.
let fwd_all_targets_valid (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL ==>
    (U64.v (fwd x) >= U64.v mword /\
     U64.v (fwd x) < heap_size /\
     U64.v (fwd x) % U64.v mword == 0 /\
     Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g))

/// Pointer closure modulo forwarding
let pointer_closure_modulo_fwd (major: heap) (fwd: forwarding_map) : prop =
  forall (src: obj_addr) (j: nat).
    Seq.mem src (objects zero_addr major) /\
    j < U64.v (wosize_of_object src major) /\
    U64.v src + j * 8 + 8 <= heap_size ==>
    (let v = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
     is_pointer v /\ ~(is_minor_pointer v /\ fwd v <> 0UL) ==>
     Seq.mem (v <: obj_addr) (objects zero_addr major))

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

/// Predicate: all promoted objects in the major heap have field data matching
/// the original minor-heap values (pre-pointer-update).
/// Defined recursively so reveal_opaque unfolds only one step at a time.
[@@"opaque_to_smt"]
let rec fields_match_minor (minor: minor_state) (major: heap) (fwd: forwarding_map)
                           (live_set: seq U64.t) (idx: nat) : Tot prop (decreases idx) =
  if idx = 0 then True
  else
    fields_match_minor minor major fwd live_set (idx - 1) /\
    (idx - 1 < Seq.length live_set ==>
      (let obj = Seq.index live_set (idx - 1) in
       let wz = minor_wosize minor obj in
       fwd obj <> 0UL /\ wz > 0 ==>
       (let new_addr = fwd obj in
        dst_fields_valid new_addr wz /\
        U64.v new_addr % 8 == 0 ==>
        (forall (j:nat). j < wz ==>
          read_word major (U64.uint_to_t (U64.v new_addr + j * 8)) ==
          minor_read_field minor obj j))))

/// Introduce fields_match_minor at idx=0 (trivially true).
val fields_match_minor_empty
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t)
  : Lemma (fields_match_minor minor major fwd live_set 0)

/// Extend fields_match_minor from idx to idx+1 given:
/// - the predicate holds up to idx
/// - the new field at idx is correct (or fwd obj = 0 / wz = 0)
val fields_match_minor_extend
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  : Lemma (requires
      fields_match_minor minor major fwd live_set idx /\
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       fwd obj = 0UL \/ wz = 0 \/
       (fwd obj <> 0UL /\ wz > 0 /\
        (dst_fields_valid (fwd obj) wz /\ U64.v (fwd obj) % 8 == 0 ==>
         (forall (j:nat). j < wz ==>
           read_word major (U64.uint_to_t (U64.v (fwd obj) + j * 8)) ==
           minor_read_field minor obj j)))))
    (ensures fields_match_minor minor major fwd live_set (idx + 1))

/// Eliminate fields_match_minor: extract the field match for a given k and j.
val fields_match_minor_elim_lemma
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat) (k: nat) (j: nat) (field_addr: hp_addr)
  : Lemma (requires
      fields_match_minor minor major fwd live_set idx /\
      k < idx /\ k < Seq.length live_set /\
      (let obj = Seq.index live_set k in
       let wz = minor_wosize minor obj in
       fwd obj <> 0UL /\ wz > 0 /\ j < wz /\
       U64.v (fwd obj) % 8 == 0 /\
       U64.v (fwd obj) + (wz - 1) * 8 + 8 <= heap_size /\
       field_addr == U64.uint_to_t (U64.v (fwd obj) + j * 8)))
    (ensures (let obj = Seq.index live_set k in
              read_word major field_addr == minor_read_field minor obj j))

/// Weaken: if fields_match_minor holds for idx, it holds for any idx' <= idx.
val fields_match_minor_weaken
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx idx': nat)
  : Lemma (requires fields_match_minor minor major fwd live_set idx /\ idx' <= idx)
          (ensures fields_match_minor minor major fwd live_set idx')

/// Introduce fields_match_minor from a pointwise proof for each k.
/// This is the inverse of the forall definition — takes individual k-level proofs
/// and assembles them into the recursive predicate.
val fields_match_minor_intro
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  : Lemma (requires
      (forall (k:nat). k < idx /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz > 0 ==>
         (let new_addr = fwd obj in
          dst_fields_valid new_addr wz /\
          U64.v new_addr % 8 == 0 ==>
          (forall (j:nat). j < wz ==>
            read_word major (U64.uint_to_t (U64.v new_addr + j * 8)) ==
            minor_read_field minor obj j)))))
    (ensures fields_match_minor minor major fwd live_set idx)

/// Flat intro: introduce fields_match_minor from a single flat forall over (k, j).
/// Avoids nested closures in callers — only needs forall k j. precond ==> read == minor_read.
val fields_match_minor_intro_flat
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  : Lemma (requires
      (forall (k:nat) (j:nat).
        (k < idx /\ k < Seq.length live_set /\
         (let obj = Seq.index live_set k in
          let wz = minor_wosize minor obj in
          fwd obj <> 0UL /\ wz > 0 /\ j < wz /\
          dst_fields_valid (fwd obj) wz /\ U64.v (fwd obj) % 8 == 0)) ==>
        (let obj = Seq.index live_set k in
         read_word major (U64.uint_to_t (U64.v (fwd obj) + j * 8)) ==
         minor_read_field minor obj j)))
    (ensures fields_match_minor minor major fwd live_set idx)

/// Frame lemma: if fields_match_minor holds and all relevant field reads are
/// preserved from major to major', then fields_match_minor holds on major'.
/// Requires fwd' to agree with fwd on all relevant entries.
val fields_match_minor_frame
  (minor: minor_state) (major major': heap) (fwd fwd': forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  : Lemma (requires
      fields_match_minor minor major fwd live_set idx /\
      (forall (k:nat). k < idx /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         fwd' obj == fwd obj /\
         (let wz = minor_wosize minor obj in
          fwd obj <> 0UL /\ wz > 0 ==>
          (let addr = fwd obj in
           dst_fields_valid addr wz /\ U64.v addr % 8 == 0 ==>
           (forall (j:nat). j < wz ==>
             read_word major' (U64.uint_to_t (U64.v addr + j * 8)) ==
             read_word major (U64.uint_to_t (U64.v addr + j * 8))))))))
    (ensures fields_match_minor minor major' fwd' live_set idx)

/// Higher-order intro: introduce fields_match_minor by calling a proof function
/// at each (k, j). Avoids E-matching issues with universals in _intro_flat.
val fields_match_minor_intro_by_proof
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  (proof: (k:nat -> j:nat -> Lemma
    (requires k < idx /\ k < Seq.length live_set /\
      (let obj = Seq.index live_set k in
       let wz = minor_wosize minor obj in
       fwd obj <> 0UL /\ wz > 0 /\ j < wz /\
       dst_fields_valid (fwd obj) wz /\ U64.v (fwd obj) % 8 == 0))
    (ensures (let obj = Seq.index live_set k in
       read_word major (U64.uint_to_t (U64.v (fwd obj) + j * 8)) ==
       minor_read_field minor obj j))))
  : Lemma (ensures fields_match_minor minor major fwd live_set idx)

/// All free-chain objects are blue (standard allocator invariant).
[@@"opaque_to_smt"]
let chain_objects_blue (major: heap) (fp: U64.t) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr major) /\ ~(is_blue obj major) ==>
    AllocLemmas.chain_avoids major fp obj (heap_size / U64.v mword) = true

/// Minor collection that promotes ALL minor objects.
let minor_collect_all_spec (minor: minor_state) (major: heap)
                            (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result =
  let all_objs = minor_objects minor in
  let prom_res = promote_all_spec minor major fp all_objs in
  let updated = update_major_pointers prom_res.major_final prom_res.fwd_map in
  { mc_major = updated;
    mc_fp    = prom_res.fp_final;
    mc_minor = minor_reset minor;
    mc_roots = rewrite_roots roots prom_res.fwd_map;
    mc_fwd   = prom_res.fwd_map }
