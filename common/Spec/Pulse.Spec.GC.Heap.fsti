/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Heap - Heap memory operations
/// ---------------------------------------------------------------------------
///
/// This module provides pure heap read/write operations:
/// - Read/write 64-bit words
/// - Memory preservation lemmas

module Pulse.Spec.GC.Heap

#set-options "--z3rlimit 10"

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64
module U8 = FStar.UInt8

open Pulse.Spec.GC.Base

/// ---------------------------------------------------------------------------
/// Byte ↔ U64 Helpers (shared with Pulse.Lib.GC.Heap)
/// ---------------------------------------------------------------------------

let uint8_to_uint64 (x: U8.t) : U64.t = U64.uint_to_t (U8.v x)
let uint64_to_uint8 (x: U64.t) : U8.t = U8.uint_to_t (U64.v x % 256)

let combine_bytes (b0 b1 b2 b3 b4 b5 b6 b7: U8.t) : U64.t =
  let open U64 in
  let v0 = uint8_to_uint64 b0 in
  let v1 = uint8_to_uint64 b1 <<^ 8ul in
  let v2 = uint8_to_uint64 b2 <<^ 16ul in
  let v3 = uint8_to_uint64 b3 <<^ 24ul in
  let v4 = uint8_to_uint64 b4 <<^ 32ul in
  let v5 = uint8_to_uint64 b5 <<^ 40ul in
  let v6 = uint8_to_uint64 b6 <<^ 48ul in
  let v7 = uint8_to_uint64 b7 <<^ 56ul in
  v0 |^ v1 |^ v2 |^ v3 |^ v4 |^ v5 |^ v6 |^ v7

/// ---------------------------------------------------------------------------
/// Word Read Operations
/// ---------------------------------------------------------------------------

/// Read a 64-bit word from heap at byte index (little-endian)
val read_word (g: heap) (addr: hp_addr) : U64.t

/// Read word characterization: read_word returns combine_bytes of individual bytes
val read_word_spec : (g: heap) -> (addr: hp_addr) ->
  Lemma (read_word g addr == combine_bytes
    (Seq.index g (U64.v addr))
    (Seq.index g (U64.v addr + 1))
    (Seq.index g (U64.v addr + 2))
    (Seq.index g (U64.v addr + 3))
    (Seq.index g (U64.v addr + 4))
    (Seq.index g (U64.v addr + 5))
    (Seq.index g (U64.v addr + 6))
    (Seq.index g (U64.v addr + 7)))

/// Roundtrip: combine_bytes(decompose(v)) == v
val combine_decompose_identity (v: U64.t) : Lemma (combine_bytes
    (uint64_to_uint8 v)
    (uint64_to_uint8 (U64.shift_right v 8ul))
    (uint64_to_uint8 (U64.shift_right v 16ul))
    (uint64_to_uint8 (U64.shift_right v 24ul))
    (uint64_to_uint8 (U64.shift_right v 32ul))
    (uint64_to_uint8 (U64.shift_right v 40ul))
    (uint64_to_uint8 (U64.shift_right v 48ul))
    (uint64_to_uint8 (U64.shift_right v 56ul))
    == v)

/// ---------------------------------------------------------------------------
/// Range Replacement (for writes)
/// ---------------------------------------------------------------------------

/// Replace 8 bytes starting at addr with new bytes
val replace_range (g: heap) 
                  (addr: hp_addr) 
                  (bytes: seq U8.t{Seq.length bytes == U64.v mword})
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           (forall i. i >= U64.v addr /\ i < U64.v addr + U64.v mword ==>
             Seq.index result i == Seq.index bytes (i - U64.v addr)) /\
           (forall i. (i < U64.v addr \/ i >= U64.v addr + U64.v mword) /\ i < Seq.length g ==>
             Seq.index result i == Seq.index g i))

/// ---------------------------------------------------------------------------
/// Word Write Operations
/// ---------------------------------------------------------------------------

/// Write a 64-bit word to heap at byte index (little-endian)
val write_word (g: heap) (addr: hp_addr) (value: U64.t) 
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           read_word result addr == value)

/// Write word characterization: write_word produces per-byte updates
val write_word_spec : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (write_word g addr v ==
    (let a = U64.v addr in
     let s = Seq.upd g a (uint64_to_uint8 v) in
     let s = Seq.upd s (a+1) (uint64_to_uint8 (U64.shift_right v 8ul)) in
     let s = Seq.upd s (a+2) (uint64_to_uint8 (U64.shift_right v 16ul)) in
     let s = Seq.upd s (a+3) (uint64_to_uint8 (U64.shift_right v 24ul)) in
     let s = Seq.upd s (a+4) (uint64_to_uint8 (U64.shift_right v 32ul)) in
     let s = Seq.upd s (a+5) (uint64_to_uint8 (U64.shift_right v 40ul)) in
     let s = Seq.upd s (a+6) (uint64_to_uint8 (U64.shift_right v 48ul)) in
     Seq.upd s (a+7) (uint64_to_uint8 (U64.shift_right v 56ul))))

/// ---------------------------------------------------------------------------
/// Read/Write Lemmas
/// ---------------------------------------------------------------------------

/// Reading after writing to same address returns written value
val read_write_same : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (read_word (write_word g addr v) addr == v)

/// Reading after writing to different address returns original value
val read_write_different : (g: heap) -> (addr1: hp_addr) -> (addr2: hp_addr) -> (v: U64.t) ->
  Lemma (requires addr1 <> addr2 /\ 
                  (U64.v addr1 + U64.v mword <= U64.v addr2 \/
                   U64.v addr2 + U64.v mword <= U64.v addr1))
        (ensures read_word (write_word g addr1 v) addr2 == read_word g addr2)

/// Write to one address preserves reads before that address
val write_preserves_before : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). U64.v a + U64.v mword <= U64.v addr ==>
           read_word (write_word g addr v) a == read_word g a)

/// Write to one address preserves reads after that address
val write_preserves_after : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). U64.v a >= U64.v addr + U64.v mword ==>
           read_word (write_word g addr v) a == read_word g a)

/// Combined: write only affects the target address
val write_word_locality : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). 
           (U64.v a + U64.v mword <= U64.v addr \/ U64.v a >= U64.v addr + U64.v mword) ==>
           read_word (write_word g addr v) a == read_word g a)

/// ---------------------------------------------------------------------------
/// Address Conversion Helpers
/// ---------------------------------------------------------------------------

/// Header address from object address (header = object - mword)
val hd_address (obj: obj_addr) : hp_addr

/// Helper: hd_address result satisfies f_address precondition
val hd_address_bounds : (obj: obj_addr) ->
  Lemma (U64.v (hd_address obj) + U64.v mword < heap_size)

/// Field/object address from header address  
val f_address (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : obj_addr

/// f_address arithmetic: f_address h = h + 8
val f_address_spec : (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) ->
  Lemma (U64.v (f_address h_addr) = U64.v h_addr + 8)

/// Round-trip lemmas
val hd_f_roundtrip : (h: hp_addr{U64.v h + U64.v mword < heap_size}) ->
  Lemma (hd_address (f_address h) == h)

val f_hd_roundtrip : (f: obj_addr) ->
  Lemma (ensures (hd_address_bounds f; f_address (hd_address f) == f))

/// hd_address arithmetic: hd_address obj = obj - 8
val hd_address_spec : (obj: obj_addr) ->
  Lemma (U64.v (hd_address obj) = U64.v obj - 8)

/// hd_address is injective: different addresses give different headers
val hd_address_injective : (f1: obj_addr) -> (f2: obj_addr) ->
  Lemma (requires f1 <> f2)
        (ensures hd_address f1 <> hd_address f2)

/// ---------------------------------------------------------------------------
/// Logical Heap Types and Pack/Unpack
/// ---------------------------------------------------------------------------

module Header = Pulse.Lib.Header

/// Wosize: number of fields (< pow2 54)
type wosize = w:U64.t{U64.v w < pow2 54}

/// Logical object: parsed header fields + field values
type object_l = {
  tag    : t:U64.t{U64.v t < 256};
  color  : Header.color_sem;
  wz     : wosize;
  fields : s:seq U64.t{Seq.length s == U64.v wz};
}

/// Total color extraction (maps 3→White; color 3 never occurs in OCaml)
val unpack_color_total (c: FStar.UInt.uint_t 64) : Header.color_sem

/// Parse one object at header address
val unpack_object (g: heap) (h_addr: hp_addr) : GTot (option (obj_addr & object_l))

/// unpack_object succeeds when object walk position is valid and object fits
val unpack_object_succeeds (g: heap) (h_addr: hp_addr) : Lemma
  (requires U64.v h_addr + 8 < heap_size /\  
            (let hdr = read_word g h_addr in
             let wz = Header.get_wosize (U64.v hdr) in
             U64.v h_addr + (wz + 1) * 8 <= heap_size))
  (ensures Some? (unpack_object g h_addr))

/// When unpack_object succeeds, the object address is h_addr + 8
val unpack_object_addr (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures fst (Some?.v (unpack_object g h_addr)) == U64.uint_to_t (U64.v h_addr + 8))

/// When unpack_object succeeds, parsed wosize matches raw header
val unpack_object_wz (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures U64.v (snd (Some?.v (unpack_object g h_addr))).wz == 
           Header.get_wosize (U64.v (read_word g h_addr)))

/// When unpack_object succeeds, parsed tag matches raw header
val unpack_object_tag (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures U64.v (snd (Some?.v (unpack_object g h_addr))).tag == 
           Header.get_tag (U64.v (read_word g h_addr)))

/// When unpack_object succeeds, parsed color matches raw header  
val unpack_object_color (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures (snd (Some?.v (unpack_object g h_addr))).color == 
           unpack_color_total (Header.get_color (U64.v (read_word g h_addr))))

/// Recursive walk: parse all objects from h_addr (always succeeds)
val unpack_objects (g: heap) (h_addr: hp_addr) 
  : GTot (list (obj_addr & object_l))

/// Check pointer closure
val pointer_closed (entries: list (obj_addr & object_l)) : GTot bool

/// Logical heap: well-formed list of objects with pointer closure
type heap_l = entries:list (obj_addr & object_l){pointer_closed entries}

/// Top-level unpack: parse raw heap into logical form
val unpack (g: heap) : GTot (option heap_l)

/// Lookup an object by address
val lookup (l: heap_l) (obj: obj_addr) : GTot (option object_l)

/// Domain: all object addresses
val heap_l_domain (l: heap_l) : GTot (list obj_addr)

/// Construct header word from object_l components
val make_header_word (ol: object_l) : U64.t

/// Pack: reconstruct raw heap from logical form
val pack (l: heap_l) 
  : Ghost heap
    (requires (forall (e: (obj_addr & object_l)). List.Tot.mem e l ==>
                U64.v (hd_address (fst e)) + (U64.v (snd e).wz + 1) * 8 <= heap_size))
    (ensures fun r -> Seq.length r == heap_size)

/// ---------------------------------------------------------------------------
/// Logical Heap Operations (L1–L3)
/// ---------------------------------------------------------------------------

/// Replace the object_l at a given address, preserving list structure
val update_entry (entries: list (obj_addr & object_l)) (addr: obj_addr) (ol': object_l)
  : GTot (list (obj_addr & object_l))

/// update_entry preserves the address list
val update_entry_preserves_addrs 
  (entries: list (obj_addr & object_l)) (addr: obj_addr) (ol': object_l)
  : Lemma (ensures List.Tot.map fst (update_entry entries addr ol') == 
                   List.Tot.map fst entries)

/// L1: Update color of an object in heap_l (pointer_closed preserved)
val update_color_l (hl: heap_l) (addr: obj_addr) (c: Header.color_sem) : GTot heap_l

/// L2: Update a field of an object in heap_l
val update_field_l (hl: heap_l) (addr: obj_addr) (i: nat) (v: U64.t)
  : Ghost heap_l
    (requires (match lookup hl addr with
              | Some ol -> i < U64.v ol.wz /\
                (U64.v v >= 8 && U64.v v < heap_size && U64.v v % 8 = 0 ==> 
                 List.Tot.mem v (heap_l_domain hl))
              | None -> True))
    (ensures fun _ -> True)

/// L3: Pointer children of a single object
val children_of (ol: object_l) : GTot (list obj_addr)

/// L3: Pointer children of an object address in the heap
val children (hl: heap_l) (addr: obj_addr) : GTot (list obj_addr)
