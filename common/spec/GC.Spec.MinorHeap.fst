/// ---------------------------------------------------------------------------
/// GC.Spec.MinorHeap - Spec for the minor (young) heap
/// ---------------------------------------------------------------------------
///
/// Stage 1 of the generational extension. Mirrors the major-heap byte model
/// in GC.Spec.{Base,Heap} but with its own size constant (minor_size) and
/// address types. The minor heap is a separate `seq U8.t` from the major
/// heap and never overlaps with it.
///
/// Minor allocations follow OCaml 4 conventions: a bump pointer
/// `young_ptr` decrements from `minor_size` toward 0. Each allocation
/// reserves (wosize+1) words: one header word followed by `wosize` field
/// words. The new object's header address is `young_ptr - (wosize+1)*8`,
/// and the field address (the `obj_addr` clients see) is `header + 8`.

module GC.Spec.MinorHeap

open FStar.Seq

module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap         // combine_bytes, uint64_to_uint8

/// ---------------------------------------------------------------------------
/// Size constants
/// ---------------------------------------------------------------------------

/// Minor heap size in bytes. Same shape constraints as `heap_size`. A
/// concrete default of 256 bytes (32 words) is chosen here; the
/// extraction-time runtime can override this just like `heap_size` is
/// overridden via `GC.Spec.Base.heap_size` (see `GC.Spec.Base.fst`).
let minor_size : n:pos{n % U64.v mword == 0 /\ n >= 16 /\ n < pow2 57 /\ n < pow2 64} = 256

/// Minor heap size as U64.
let minor_size_u64 : n:U64.t{U64.v n == minor_size} = 256UL

/// ---------------------------------------------------------------------------
/// Minor heap type and address types
/// ---------------------------------------------------------------------------

/// Byte-addressable minor heap of exactly `minor_size` bytes.
let minor_heap = h:seq U8.t{Seq.length h == minor_size}

/// Word-aligned address within the minor heap.
let m_hp_addr = a:U64.t{
  U64.v a < minor_size /\
  U64.v a % U64.v mword == 0
}

/// Object address: header is at `addr - 8`, fields at `addr`.
let m_obj_addr = a:m_hp_addr{U64.v a >= U64.v mword}

/// Young pointer: word-aligned, can point one past the end.
let young_ptr_t = p:U64.t{
  U64.v p <= minor_size /\
  U64.v p % U64.v mword == 0
}

/// ---------------------------------------------------------------------------
/// Byte-level read/write on the minor heap
/// ---------------------------------------------------------------------------
///
/// These mirror `GC.Spec.Heap.{read_word,write_word}` but operate on a
/// `minor_heap` (length minor_size) instead of the major `heap`. The
/// underlying `combine_bytes` and `uint64_to_uint8` are shared.

/// Alignment + size constraint imply addr + 8 <= minor_size.
let m_hp_addr_plus_8 (addr: m_hp_addr)
  : Lemma (U64.v addr + 8 <= minor_size)
  = assert (U64.v addr < minor_size);
    assert (U64.v addr % 8 == 0);
    assert (minor_size % 8 == 0)

/// Read a 64-bit little-endian word at `addr`.
let m_read_word (g: minor_heap) (addr: m_hp_addr) : U64.t =
  m_hp_addr_plus_8 addr;
  combine_bytes
    (Seq.index g (U64.v addr))
    (Seq.index g (U64.v addr + 1))
    (Seq.index g (U64.v addr + 2))
    (Seq.index g (U64.v addr + 3))
    (Seq.index g (U64.v addr + 4))
    (Seq.index g (U64.v addr + 5))
    (Seq.index g (U64.v addr + 6))
    (Seq.index g (U64.v addr + 7))

/// Write a 64-bit little-endian word at `addr`.
let m_write_word (g: minor_heap) (addr: m_hp_addr) (v: U64.t) : minor_heap =
  m_hp_addr_plus_8 addr;
  let b0 = uint64_to_uint8 v in
  let b1 = uint64_to_uint8 (U64.shift_right v 8ul) in
  let b2 = uint64_to_uint8 (U64.shift_right v 16ul) in
  let b3 = uint64_to_uint8 (U64.shift_right v 24ul) in
  let b4 = uint64_to_uint8 (U64.shift_right v 32ul) in
  let b5 = uint64_to_uint8 (U64.shift_right v 40ul) in
  let b6 = uint64_to_uint8 (U64.shift_right v 48ul) in
  let b7 = uint64_to_uint8 (U64.shift_right v 56ul) in
  let g1 = Seq.upd g  (U64.v addr)     b0 in
  let g2 = Seq.upd g1 (U64.v addr + 1) b1 in
  let g3 = Seq.upd g2 (U64.v addr + 2) b2 in
  let g4 = Seq.upd g3 (U64.v addr + 3) b3 in
  let g5 = Seq.upd g4 (U64.v addr + 4) b4 in
  let g6 = Seq.upd g5 (U64.v addr + 5) b5 in
  let g7 = Seq.upd g6 (U64.v addr + 6) b6 in
              Seq.upd g7 (U64.v addr + 7) b7

/// ---------------------------------------------------------------------------
/// Minor heap state and well-formedness
/// ---------------------------------------------------------------------------

/// The minor heap state: byte array + current bump pointer.
type minor_state = {
  m_data    : minor_heap;
  young_ptr : young_ptr_t;
}

/// An empty minor: young_ptr at the top, no live objects.
let empty_minor (g: minor_heap) : minor_state =
  { m_data = g; young_ptr = minor_size_u64 }

/// Stage 1 well-formedness. The minor is essentially typed: the only real
/// constraint is the bump pointer remains aligned and in range, which the
/// types already enforce. Later stages will add invariants about
/// promoted/forwarded objects.
let well_formed_minor (m: minor_state) : prop =
  True

/// ---------------------------------------------------------------------------
/// Bump allocator spec
/// ---------------------------------------------------------------------------

/// Result of a minor allocation attempt.
noeq
type minor_alloc_result = {
  m_state_out : minor_state;
  obj_out     : U64.t;        // 0UL on OOM; otherwise an m_obj_addr
}

/// Bytes needed to satisfy a request of `wosize` field words (rounded up to
/// 1 if the client asked for 0). Header word + wosize field words.
let alloc_bytes (wosize: nat) : nat =
  let wz = if wosize = 0 then 1 else wosize in
  (wz + 1) * U64.v mword

/// Does the current bump pointer have room for `wosize` fields?
let has_room (m: minor_state) (wosize: nat) : bool =
  alloc_bytes wosize <= U64.v m.young_ptr

/// Auxiliary: build a header word (wz, White, tag) without depending on
/// the major-heap `make_header` (which lives in `GC.Spec.Allocator`).
let m_make_header (wz: U64.t{U64.v wz < pow2 54}) (tag: U64.t{U64.v tag < 256}) : U64.t =
  let wz_shifted = U64.shift_left wz 10ul in
  U64.logor wz_shifted tag    // color = 0 = White

/// Pure bump allocator. On success: decrements young_ptr, writes a White
/// header at the new header slot, returns the object address.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let minor_alloc_spec (m: minor_state) (wosize: nat{wosize < pow2 54}) (tag: U64.t{U64.v tag < 256})
  : minor_alloc_result
  = let wz : pos = if wosize = 0 then 1 else wosize in
    let need_bytes : pos = (wz + 1) * U64.v mword in
    let yp_v : nat = U64.v m.young_ptr in
    if need_bytes > yp_v then
      { m_state_out = m; obj_out = 0UL }
    else begin
      let new_yp_v : nat = yp_v - need_bytes in
      // Modular arithmetic: yp_v % 8 == 0 (young_ptr_t refinement);
      // need_bytes = (wz+1)*8 hence -need_bytes = (-(wz+1)) * 8.
      // lemma_mod_plus: (a + b*n) % n == a % n.
      FStar.Math.Lemmas.lemma_mod_plus yp_v (- (wz + 1)) (U64.v mword);
      assert (new_yp_v % U64.v mword == yp_v % U64.v mword);
      assert (yp_v % U64.v mword == 0);
      let new_yp : young_ptr_t = U64.uint_to_t new_yp_v in
      // obj_v = new_yp + 8. wz >= 1 ⟹ need_bytes >= 16 ⟹ obj_v + 8 <= yp_v.
      let obj_v : nat = new_yp_v + U64.v mword in
      FStar.Math.Lemmas.lemma_mod_plus new_yp_v 1 (U64.v mword);
      assert (obj_v % U64.v mword == new_yp_v % U64.v mword);
      assert (obj_v >= U64.v mword);
      assert (obj_v + U64.v mword <= yp_v);     // since need_bytes >= 16
      assert (obj_v < minor_size);              // since yp_v <= minor_size
      let obj : m_obj_addr = U64.uint_to_t obj_v in
      let wz_u64 : U64.t = U64.uint_to_t wz in
      let hdr = m_make_header wz_u64 tag in
      let g' = m_write_word m.m_data new_yp hdr in
      let m_state_out = { m_data = g'; young_ptr = new_yp } in
      { m_state_out; obj_out = obj }
    end
#pop-options

/// Reset the minor heap to empty (used after a minor collection).
let reset_minor (m: minor_state) : minor_state =
  { m with young_ptr = minor_size_u64 }
