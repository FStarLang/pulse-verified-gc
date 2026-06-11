(*
   GC.Impl.ArrayWord — Word-level read/write primitives for byte arrays.

   These are assumed (extern) operations that read/write 8 bytes at once
   as a little-endian U64.  Extracted to C as simple word load/store,
   replacing 8 individual byte operations.

   The specs are expressed in terms of combine_bytes / uint64_to_uint8
   from GC.Spec.Heap so that callers can bridge to existing heap specs.
*)
module GC.Impl.ArrayWord

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module U8  = FStar.UInt8
module U64 = FStar.UInt64
module SZ  = FStar.SizeT
module Seq = FStar.Seq
module SpecHeap = GC.Spec.Heap

/// ---------------------------------------------------------------------------
/// Pure specifications (thin wrappers around GC.Spec.Heap)
/// ---------------------------------------------------------------------------

/// Read 8 bytes starting at [off] as a little-endian U64
noextract
let read_u64_spec (s: Seq.seq U8.t) (off: nat{off + 8 <= Seq.length s}) : U64.t =
  SpecHeap.combine_bytes
    (Seq.index s off)
    (Seq.index s (off + 1))
    (Seq.index s (off + 2))
    (Seq.index s (off + 3))
    (Seq.index s (off + 4))
    (Seq.index s (off + 5))
    (Seq.index s (off + 6))
    (Seq.index s (off + 7))

/// Write a U64 as 8 little-endian bytes starting at [off]
noextract
let write_u64_spec (s: Seq.seq U8.t) (off: nat{off + 8 <= Seq.length s}) (v: U64.t)
  : (r: Seq.seq U8.t{Seq.length r == Seq.length s}) =
  let b0 = SpecHeap.uint64_to_uint8 v in
  let b1 = SpecHeap.uint64_to_uint8 (U64.shift_right v 8ul) in
  let b2 = SpecHeap.uint64_to_uint8 (U64.shift_right v 16ul) in
  let b3 = SpecHeap.uint64_to_uint8 (U64.shift_right v 24ul) in
  let b4 = SpecHeap.uint64_to_uint8 (U64.shift_right v 32ul) in
  let b5 = SpecHeap.uint64_to_uint8 (U64.shift_right v 40ul) in
  let b6 = SpecHeap.uint64_to_uint8 (U64.shift_right v 48ul) in
  let b7 = SpecHeap.uint64_to_uint8 (U64.shift_right v 56ul) in
  let s = Seq.upd s off       b0 in
  let s = Seq.upd s (off + 1) b1 in
  let s = Seq.upd s (off + 2) b2 in
  let s = Seq.upd s (off + 3) b3 in
  let s = Seq.upd s (off + 4) b4 in
  let s = Seq.upd s (off + 5) b5 in
  let s = Seq.upd s (off + 6) b6 in
  Seq.upd s (off + 7) b7

/// ---------------------------------------------------------------------------
/// Assumed Pulse primitives (extracted as extern C functions)
/// ---------------------------------------------------------------------------

/// Read 8 bytes from a byte array at [offset] as a little-endian U64.
/// C implementation: *(uint64_t*)(arr + offset)
val read_u64_le
  (#s: Ghost.erased (Seq.seq U8.t))
  (arr: array U8.t)
  (offset: SZ.t{SZ.v offset + 8 <= Seq.length s})
  : stt U64.t
    (pts_to arr s)
    (fun v -> pts_to arr s ** pure (v == read_u64_spec s (SZ.v offset)))

/// Write a U64 as 8 little-endian bytes to a byte array at [offset].
/// C implementation: *(uint64_t*)(arr + offset) = v
val write_u64_le
  (#s: Ghost.erased (Seq.seq U8.t))
  (arr: array U8.t)
  (offset: SZ.t{SZ.v offset + 8 <= Seq.length s})
  (v: U64.t)
  : stt unit
    (pts_to arr s)
    (fun _ -> pts_to arr (write_u64_spec s (SZ.v offset) v))
