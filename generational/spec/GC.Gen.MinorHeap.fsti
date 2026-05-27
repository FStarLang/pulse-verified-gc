/// ---------------------------------------------------------------------------
/// GC.Gen.MinorHeap — Specification of the bump-pointer minor heap
/// ---------------------------------------------------------------------------
///
/// The minor heap is a contiguous region of memory with a simple bump allocator.
/// Objects are allocated sequentially from the start. The bump pointer tracks
/// the next free position. No free list, no deallocation — the entire minor
/// heap is reset after each minor collection.
///
/// Layout:
///   [obj1_hdr][obj1_fields...][obj2_hdr][obj2_fields...]...[free space...]
///    ^                                                       ^
///    0 (start)                                               bump_ptr
///
/// Each object has the same header format as major heap objects:
///   | wosize (54 bits) | color (2 bits) | tag (8 bits) |

module GC.Gen.MinorHeap

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Gen.Base

/// ---------------------------------------------------------------------------
/// Minor Heap Word Operations (independent of major heap's read_word)
/// ---------------------------------------------------------------------------

/// Combine 8 bytes into a U64 (little-endian, same as GC.Spec.Heap.combine_bytes)
let minor_combine_bytes (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) : U64.t =
  let open U64 in
  FStar.Int.Cast.uint8_to_uint64 b0 |^
  (FStar.Int.Cast.uint8_to_uint64 b1 <<^ 8ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b2 <<^ 16ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b3 <<^ 24ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b4 <<^ 32ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b5 <<^ 40ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b6 <<^ 48ul) |^
  (FStar.Int.Cast.uint8_to_uint64 b7 <<^ 56ul)

/// Read a 64-bit word from the minor heap at a word-aligned offset
noextract
let minor_read_word (h: minor_heap) (addr: U64.t{U64.v addr + 8 <= minor_heap_size /\ U64.v addr % 8 == 0}) : U64.t =
  minor_combine_bytes
    (Seq.index h (U64.v addr))
    (Seq.index h (U64.v addr + 1))
    (Seq.index h (U64.v addr + 2))
    (Seq.index h (U64.v addr + 3))
    (Seq.index h (U64.v addr + 4))
    (Seq.index h (U64.v addr + 5))
    (Seq.index h (U64.v addr + 6))
    (Seq.index h (U64.v addr + 7))

/// Total version of minor_read_word (no argument refinement) for use in Pulse specs
noextract
let minor_read_word_t (h: minor_heap) (addr: U64.t) : U64.t =
  if U64.v addr + 8 <= minor_heap_size && U64.v addr % 8 = 0
  then minor_read_word h addr
  else 0UL

/// Decompose a U64 into its low byte
noextract
let minor_byte_of (x: U64.t) : U8.t =
  FStar.Int.Cast.uint64_to_uint8 x

/// Write a 64-bit word to the minor heap at a word-aligned offset
noextract
let minor_write_word (h: minor_heap) (addr: U64.t{U64.v addr + 8 <= minor_heap_size /\ U64.v addr % 8 == 0}) (v: U64.t)
  : minor_heap =
  let a = U64.v addr in
  let h = Seq.upd h a       (minor_byte_of v) in
  let h = Seq.upd h (a + 1) (minor_byte_of (U64.shift_right v 8ul)) in
  let h = Seq.upd h (a + 2) (minor_byte_of (U64.shift_right v 16ul)) in
  let h = Seq.upd h (a + 3) (minor_byte_of (U64.shift_right v 24ul)) in
  let h = Seq.upd h (a + 4) (minor_byte_of (U64.shift_right v 32ul)) in
  let h = Seq.upd h (a + 5) (minor_byte_of (U64.shift_right v 40ul)) in
  let h = Seq.upd h (a + 6) (minor_byte_of (U64.shift_right v 48ul)) in
  let h = Seq.upd h (a + 7) (minor_byte_of (U64.shift_right v 56ul)) in
  h

/// Total version of minor_write_word (no argument refinement)
noextract
let minor_write_word_t (h: minor_heap) (addr: U64.t) (v: U64.t) : minor_heap =
  if U64.v addr + 8 <= minor_heap_size && U64.v addr % 8 = 0
  then minor_write_word h addr v
  else h

/// ---------------------------------------------------------------------------
/// Minor Heap State
/// ---------------------------------------------------------------------------

/// A minor heap state is the byte array plus the current bump pointer.
/// bump_ptr points to the next free byte (always word-aligned, within bounds).
noeq
type minor_state = {
  data : minor_heap;
  bump : U64.t;  // next free byte offset (0 <= bump <= minor_heap_size, word-aligned)
}

/// Chain validity: the walk from pos to bump never encounters a zero-wosize
/// header or jumps past bump. This guarantees the object enumeration reaches
/// all allocated objects.
val minor_chain_valid (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : GTot bool

/// Chain no-infix: walking the same chain, no header has tag = 249 (Infix_tag).
/// This is a separate invariant from structural validity to minimize proof impact.
val minor_chain_no_infix (data: minor_heap) (pos: nat{pos % 8 == 0}) (bump: nat{bump <= minor_heap_size /\ bump % 8 == 0})
  : GTot bool

/// Well-formed minor state: bump pointer is word-aligned, in bounds,
/// the chain from 0 to bump is valid, and no chain position has Infix_tag.
let minor_wf (ms: minor_state) : prop =
  U64.v ms.bump % 8 == 0 /\
  U64.v ms.bump <= minor_heap_size /\
  minor_chain_valid ms.data 0 (U64.v ms.bump) == true /\
  minor_chain_no_infix ms.data 0 (U64.v ms.bump) == true

/// Initial (empty) minor heap state
val minor_init (data: minor_heap) : Tot (ms:minor_state{minor_wf ms /\ U64.v ms.bump == 0})

/// ---------------------------------------------------------------------------
/// Bump Allocation Spec
/// ---------------------------------------------------------------------------

/// Result of a minor allocation attempt
noeq
type minor_alloc_result = {
  ms_out   : minor_state;    // updated minor state
  obj_addr : U64.t;          // allocated object address, or 0 if OOM
}

/// Can we fit an object of `wosize` words in the minor heap?
let minor_can_alloc (ms: minor_state) (wosize: nat) : bool =
  U64.v ms.bump + (wosize + 1) * 8 <= minor_heap_size

/// Bump-allocate an object in the minor heap.
///
/// If there's room: writes header at bump, returns obj_addr = bump + 8,
/// advances bump by (wosize+1)*8.
/// If no room: returns obj_addr = 0, state unchanged.
///
/// The header is written as: wosize in bits 10-63, white color (0), tag.
val minor_alloc_spec (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                     (tag: nat{tag < 256 /\ tag <> 249})
  : Tot minor_alloc_result

/// ---------------------------------------------------------------------------
/// Minor Heap Object Enumeration
/// ---------------------------------------------------------------------------

/// Walk the minor heap from offset 0 to bump, collecting object addresses.
/// Similar to `objects` for the major heap but bounded by bump pointer.
val minor_objects (ms: minor_state) : GTot (seq U64.t)

/// Every address in minor_objects is a valid minor_obj_addr
val minor_objects_valid (ms: minor_state) (x: U64.t)
  : Lemma (requires Seq.mem x (minor_objects ms))
          (ensures U64.v x >= 8 /\ U64.v x < minor_heap_size /\ U64.v x % 8 == 0)

/// ---------------------------------------------------------------------------
/// Minor Heap Liveness
/// ---------------------------------------------------------------------------

/// An object in the minor heap is "live" if it's reachable from:
/// 1. Program roots (stack), OR
/// 2. A major-heap object that points into the minor heap (remembered set)
///
/// We model this abstractly here; the remembered set module provides the scan.

/// Establish pow2 bounds needed for U64.uint_to_t below
let minor_heap_size_bound : squash (minor_heap_size < pow2 64) =
  assert_norm (pow2 57 < pow2 64)

/// Read a field from a minor heap object
let minor_read_field (ms: minor_state) (obj: U64.t) (field_idx: nat) : GTot U64.t =
  let byte_offset = U64.v obj + field_idx * 8 in
  if byte_offset + 8 <= minor_heap_size && byte_offset % 8 = 0
  then minor_read_word ms.data (U64.uint_to_t byte_offset)
  else 0UL

/// Read the wosize of a minor heap object (from its header)
let minor_wosize (ms: minor_state) (obj: U64.t) : GTot nat =
  if U64.v obj >= 8 && U64.v obj < minor_heap_size then
    let hdr_addr = U64.v obj - 8 in
    if hdr_addr + 8 <= minor_heap_size && hdr_addr % 8 = 0 then
      let hdr = minor_read_word ms.data (U64.uint_to_t hdr_addr) in
      U64.v (U64.shift_right hdr 10ul)
    else 0
  else 0

/// Read the tag of a minor heap object (from its header, bits 0-7)
let minor_tag (ms: minor_state) (obj: U64.t) : GTot nat =
  if U64.v obj >= 8 && U64.v obj < minor_heap_size then
    let hdr_addr = U64.v obj - 8 in
    if hdr_addr + 8 <= minor_heap_size && hdr_addr % 8 = 0 then
      let hdr = minor_read_word ms.data (U64.uint_to_t hdr_addr) in
      U64.v (U64.logand hdr 0xFFUL)
    else 0
  else 0

/// The tag value is always < 256
val minor_tag_bound (ms: minor_state) (obj: U64.t)
  : Lemma (minor_tag ms obj < 256)

/// ---------------------------------------------------------------------------
/// Infix Object Detection
/// ---------------------------------------------------------------------------

/// An address in the minor heap points to an infix sub-object if its
/// header tag is Infix_tag (249). Infix headers reside WITHIN the body of
/// a parent closure (tag=247) and encode the byte offset back to the parent
/// in the wosize field.
let is_infix_in_minor (ms: minor_state) (addr: U64.t) : GTot bool =
  U64.v addr >= 8 && U64.v addr < minor_heap_size && U64.v addr % 8 = 0 &&
  minor_tag ms addr = 249

/// Compute the parent closure's val-address from an infix val-address.
/// The infix header's wosize field encodes the word offset from infix val
/// to parent val: parent = infix_val - wosize * 8.
/// Returns 0 if the offset would underflow (defensive; minor_infix_wf prevents this).
let infix_parent (ms: minor_state) (addr: U64.t) : GTot U64.t =
  let off = minor_wosize ms addr * 8 in
  if off <= U64.v addr
  then U64.uint_to_t (U64.v addr - off)
  else 0UL

/// ---------------------------------------------------------------------------
/// Guard Completeness (trust assumption on the mutator)
/// ---------------------------------------------------------------------------

/// Guard completeness: runtime guards suffice to identify minor objects.
///
/// TRUST ASSUMPTION on the mutator:
/// The allocator zeros newly allocated object bodies (so body positions have
/// wosize = 0 and cannot masquerade as object starts). The mutator is trusted
/// not to store values in body fields whose upper 54 bits happen to form a
/// plausible wosize that, combined with alignment and bounds, would be
/// mistaken for an object header. In practice OCaml tagged values (odd integers,
/// aligned pointers) do not produce such confusion.
///
/// Note: addresses with tag = 249 (Infix_tag) are excluded — they are
/// infix sub-objects within closures, not standalone objects.
///
/// This predicate is expected at GC entry and preserved by the collector
/// (which only reads the minor heap) and by minor_reset (which clears the
/// nursery and resets bump → 0).
[@@"opaque_to_smt"]
let minor_guards_complete (ms: minor_state) : prop =
  forall (addr: U64.t).
    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0 /\
    minor_wosize ms addr > 0 /\
    U64.v addr + minor_wosize ms addr * 8 <= minor_heap_size /\
    minor_tag ms addr <> 249 ==>
    Seq.mem addr (minor_objects ms)

/// ---------------------------------------------------------------------------
/// Infix Well-Formedness (trust assumption on the mutator)
/// ---------------------------------------------------------------------------

/// When an infix sub-object exists in the minor heap, its encoded parent
/// must be a valid minor object (a closure). This guarantees that the
/// infix-aware BFS can safely forward the parent and derive infix forwarding.
[@@"opaque_to_smt"]
let minor_infix_wf (ms: minor_state) : prop =
  forall (addr: U64.t).
    is_infix_in_minor ms addr ==>
    (let wz = minor_wosize ms addr in
     let parent = infix_parent ms addr in
     wz > 0 /\
     wz * 8 <= U64.v addr - 8 /\
     U64.v parent >= 8 /\
     U64.v parent % 8 == 0 /\
     Seq.mem parent (minor_objects ms) /\
     // The infix lies within the parent's body:
     U64.v addr - U64.v parent < minor_wosize ms parent * 8)

/// ---------------------------------------------------------------------------
/// Properties
/// ---------------------------------------------------------------------------

/// Infix sub-objects (tag=249) are never in minor_objects
/// When addr is an infix sub-object and minor_infix_wf holds,
/// the parent's value is addr minus the encoded offset (wosize*8).
val infix_parent_value (ms: minor_state) (addr: U64.t)
  : Lemma (requires is_infix_in_minor ms addr /\ minor_infix_wf ms)
          (ensures U64.v (infix_parent ms addr) == U64.v addr - minor_wosize ms addr * 8)

/// When addr is an infix sub-object and minor_infix_wf holds,
/// the parent is a valid minor object with expected bounds.
val infix_parent_in_minor_objects (ms: minor_state) (addr: U64.t)
  : Lemma (requires is_infix_in_minor ms addr /\ minor_infix_wf ms)
          (ensures (let parent = infix_parent ms addr in
                    Seq.mem parent (minor_objects ms) /\
                    U64.v parent >= 8 /\
                    U64.v parent % 8 == 0 /\
                    U64.v addr - U64.v parent < minor_wosize ms parent * 8))

val minor_objects_not_infix (ms: minor_state) (addr: U64.t)
  : Lemma (requires minor_wf ms /\ Seq.mem addr (minor_objects ms))
          (ensures minor_tag ms addr <> 249)

/// Every object in minor_objects has wosize that fits in the heap
val minor_objects_wosize_bound (ms: minor_state) (obj: U64.t)
  : Lemma (requires Seq.mem obj (minor_objects ms))
          (ensures (minor_wosize ms obj + 1) * 8 <= minor_heap_size)

/// The body of a minor object fits within the heap:
/// obj + wosize*8 <= minor_heap_size (and wosize > 0)
val minor_objects_body_bound (ms: minor_state) (obj: U64.t)
  : Lemma (requires minor_wf ms /\ Seq.mem obj (minor_objects ms))
          (ensures minor_wosize ms obj > 0 /\
                   U64.v obj + minor_wosize ms obj * 8 <= minor_heap_size /\
                   minor_wosize ms obj < minor_heap_size)

/// After allocation, the new object appears in minor_objects
val minor_alloc_adds_object (ms: minor_state) (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                            (tag: nat{tag < 256 /\ tag <> 249})
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize)
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    minor_wf res.ms_out /\
                    res.obj_addr <> 0UL /\
                    Seq.mem res.obj_addr (minor_objects res.ms_out)))

/// Allocation preserves existing objects' data
val minor_alloc_preserves_existing (ms: minor_state) 
                                    (wosize: nat{wosize > 0 /\ wosize <= max_young_wosize})
                                    (tag: nat{tag < 256 /\ tag <> 249})
                                    (x: U64.t)
  : Lemma (requires minor_wf ms /\ minor_can_alloc ms wosize /\
                    Seq.mem x (minor_objects ms))
          (ensures (let res = minor_alloc_spec ms wosize tag in
                    Seq.mem x (minor_objects res.ms_out) /\
                    minor_wosize res.ms_out x == minor_wosize ms x /\
                    (forall (i:nat). i < minor_wosize ms x ==>
                      minor_read_field res.ms_out x i == minor_read_field ms x i)))

/// Resetting the minor heap (after collection) clears stale object headers and
/// bodies before making the heap empty again.
val minor_reset (ms: minor_state)
  : Tot (ms':minor_state{
      minor_wf ms' /\
      U64.v ms'.bump == 0 /\
      ms'.data == Seq.create minor_heap_size 0uy
    })

val minor_reset_wosize_zero (ms: minor_state) (addr: U64.t)
  : Lemma (ensures minor_wosize (minor_reset ms) addr == 0)

val minor_reset_objects_empty (ms: minor_state)
  : Lemma (ensures minor_objects (minor_reset ms) == Seq.empty)

val minor_reset_objects_not_mem (ms: minor_state) (addr: U64.t)
  : Lemma (ensures ~(Seq.mem addr (minor_objects (minor_reset ms))))

val minor_reset_no_infix (ms: minor_state) (addr: U64.t)
  : Lemma (ensures ~(is_infix_in_minor (minor_reset ms) addr))

/// The number of minor objects is bounded by minor_heap_size / 16.
/// Each object uses at least 16 bytes (8 for header + 8 for body with wosize >= 1).
/// Since queue_size = minor_heap_size / 8, we get |minor_objects| < queue_size.
val minor_objects_count_bound (ms: minor_state)
  : Lemma (requires minor_wf ms)
          (ensures Seq.length (minor_objects ms) <= minor_heap_size / 16 /\
                   Seq.length (minor_objects ms) < minor_heap_size / 8)

/// When bump is 0, there are no objects (for SPOT)
val minor_objects_zero_bump (ms: minor_state)
  : Lemma (requires U64.v ms.bump == 0)
          (ensures minor_objects ms == Seq.empty)
