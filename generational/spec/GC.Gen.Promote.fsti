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

/// The tag a promoted copy is allocated with: the minor object's own.
let promoted_tag (minor: minor_state) (obj: U64.t) : GTot (t:U64.t{U64.v t < 256}) =
  minor_tag_bound minor obj;
  U64.uint_to_t (minor_tag minor obj)

/// Promote a single object from minor heap to major heap.
///
/// 1. Allocate in the major heap with the minor object's wosize and tag, as
///    OCaml's `caml_alloc_shr (wosize, tag)` does: the header is written once,
///    white, carrying the tag
/// 2. Copy field data from minor to major
///
/// If major allocation fails (OOM), returns new_addr = 0.
let promote_object (minor: minor_state) (major: heap) (obj: U64.t)
                   (fp: U64.t) (wosize: nat{wosize > 0})
  : GTot promote_one_result =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
  let new_major = alloc_res.heap_out in
  let new_fp = alloc_res.fp_out in
  let new_addr = alloc_res.obj_out in
  if new_addr = 0UL then
    { major_out = major; fp_out = fp; new_addr = 0UL }
  else
    let copied_major = copy_fields minor new_major obj new_addr 0 wosize in
    { major_out = copied_major; fp_out = new_fp; new_addr = new_addr }

/// Unfold: when alloc fails (OOM), promote_object returns original heap/fp unchanged.
val promote_object_oom (minor: minor_state) (major: heap) (obj: U64.t)
                       (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj)).obj_out == 0UL)
          (ensures (let res = promote_object minor major obj fp wosize in
                    res.major_out == major /\ res.fp_out == fp /\ res.new_addr == 0UL))

/// Unfold: when alloc succeeds, promote_object = tagged alloc + copy_fields.
val promote_object_success (minor: minor_state) (major: heap) (obj: U64.t)
                           (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj)).obj_out <> 0UL)
          (ensures (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
                    let res = promote_object minor major obj fp wosize in
                    res.major_out == copy_fields minor alloc_res.heap_out obj alloc_res.obj_out 0 wosize /\
                    res.fp_out == alloc_res.fp_out /\
                    res.new_addr == alloc_res.obj_out))

/// promote_object preserves allocator invariants (wfh_part1, fl_valid, fl_chain_terminates).
/// Combines alloc_spec and copy_fields preservation in one lemma.
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
/// The pointer update over a live set
/// ---------------------------------------------------------------------------

/// The same walk, over a live set fixed for the whole walk: it rewrites the
/// fields of the objects `x` with `live x` (and scannable, as above) and skips
/// every other object without reading its fields.  It reads every header, so it
/// needs only the walk facts of the heap (parts 1 and 4).
///
/// `live` is a proposition (as in `GC.Spec.Fields.live_ok`), so the test goes
/// through `strong_excluded_middle`; this is a ghost specification function.
/// At `idle_live major` it is today's `update_major_pointers`
/// (`GC.Gen.PromoteUpdate.Aux.update_live_pointers_idle`).
let rec update_live_aux (major: heap) (objs: seq obj_addr) (live: obj_addr -> prop)
                        (fwd: forwarding_map) (idx: nat)
  : GTot heap (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then major
  else
    let obj = Seq.index objs idx in
    if not (FStar.IndefiniteDescription.strong_excluded_middle (live obj)) then
      update_live_aux major objs live fwd (idx + 1)
    else if is_no_scan obj major then
      update_live_aux major objs live fwd (idx + 1)
    else
      let wz = U64.v (wosize_of_object obj major) in
      let major' = update_object_pointers major obj wz fwd 0 in
      update_live_aux major' objs live fwd (idx + 1)

/// Rewrite the nursery pointers held by the live objects of the major heap.
let update_live_pointers (major: heap) (live: obj_addr -> prop) (fwd: forwarding_map)
  : GTot heap =
  update_live_aux major (objects zero_addr major) live fwd 0

/// The live set after promotion: the live set before it, plus the images of
/// the promoted nursery objects.  It is an explicit set, not recomputed from
/// the heap's colours.  (An unpromoted nursery object maps to `0UL`, which is
/// not an `obj_addr`; interior nursery pointers are not `minor_objects`, so
/// their interior images are not members.)
let promoted_live (minor: minor_state) (live: obj_addr -> prop) (fwd: forwarding_map)
  : obj_addr -> prop =
  fun x -> live x \/ (exists (v: U64.t). Seq.mem v (minor_objects minor) /\ fwd v == x)

/// ---------------------------------------------------------------------------
/// Live Set and Root Rewriting
/// ---------------------------------------------------------------------------

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

/// Same, from the object bound of `wfh_part1_obj_bound` and a lower bound on
/// the object's wosize.  Callers used to derive the scalar bound inline, which
/// Z3 5.x fails to do inside their large contexts.
val dst_fields_valid_from_obj (g: heap) (addr: obj_addr) (wz: pos)
  : Lemma (requires U64.v addr + U64.v (wosize_of_object addr g) * 8 <= Seq.length g /\
                    U64.v (wosize_of_object addr g) >= wz)
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
/// (`--fuel 0`: the statement's well-formedness needs no unfolding, and with
/// fuel Z3 5.1.0 unrolls `promote_object` instead of using `dst_fields_valid`.)
#push-options "--fuel 0 --ifuel 0"
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
#pop-options

/// The walk facts of a well-formed heap: parts 1 and 4, which are all of
/// well-formedness that promotion reads.  The promotion lemmas ask for these
/// alone, so they also apply to a heap that is well formed only over a live
/// set (`GC.Spec.Fields.well_formed_heap_over`).
val wfh_walk_facts (g: heap)
  : Lemma (requires well_formed_heap g)
          (ensures well_formed_heap_part1 g /\ well_formed_heap_part4 g)

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

/// `heap_objects_dense` is `GC.Spec.Fields.heap_objects_dense`.

/// All free-chain objects are blue (standard allocator invariant).
[@@"opaque_to_smt"]
let chain_objects_blue (major: heap) (fp: U64.t) : prop =
  forall (obj: obj_addr).
    Seq.mem obj (objects zero_addr major) /\ ~(is_blue obj major) ==>
    AllocLemmas.chain_avoids major fp obj heap_words = true
