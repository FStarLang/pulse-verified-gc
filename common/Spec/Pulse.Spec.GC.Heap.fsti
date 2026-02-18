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

/// Write word characterization: byte-level expansion available as
/// write_word_spec in the .fst (internal lemma, proof is () by definitional equality)

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

/// Read field values from object starting at obj address
val read_fields (g: heap) (obj: obj_addr) (wz: nat) (i: nat)
  : Ghost (option (seq U64.t))
          (requires i <= wz)
          (ensures fun r -> match r with
                         | Some s -> Seq.length s == wz - i
                         | None -> True)

/// Total color extraction (maps 3→White; color 3 never occurs in OCaml)
val unpack_color_total (c: FStar.UInt.uint_t 64) : Header.color_sem

/// read_fields succeeds when object fits in heap
val read_fields_succeeds (g: heap) (obj: obj_addr) (wz: nat) (i: nat)
  : Lemma 
    (requires i <= wz /\ U64.v obj + wz * 8 <= heap_size /\ U64.v obj % 8 == 0)
    (ensures Some? (read_fields g obj wz i))

/// read_fields_index: the j-th element equals read_word at the right address
val read_fields_index (g: heap) (obj: obj_addr) (wz: nat) (start: nat) (j: nat)
  : Lemma
    (requires start <= wz /\ j >= start /\ j < wz /\
             U64.v obj + wz * 8 <= heap_size /\ U64.v obj % 8 == 0 /\
             Some? (read_fields g obj wz start))
    (ensures (let addr_nat = U64.v obj + j * 8 in
              addr_nat < heap_size /\ addr_nat % 8 == 0 /\
              addr_nat < pow2 64 /\
              Seq.index (Some?.v (read_fields g obj wz start)) (j - start) ==
              read_word g (U64.uint_to_t addr_nat <: hp_addr)))

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

/// When unpack_object succeeds, fields match read_fields output
val unpack_object_fields (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures (let (obj, ol) = Some?.v (unpack_object g h_addr) in
            Some? (read_fields g obj (U64.v ol.wz) 0) /\
            ol.fields == Some?.v (read_fields g obj (U64.v ol.wz) 0)))

/// Recursive walk: parse all objects from h_addr (always succeeds)
val unpack_objects (g: heap) (h_addr: hp_addr) 
  : GTot (list (obj_addr & object_l))

/// Unfolding: unpack_objects returns [] when start is past heap end
val unpack_objects_empty_start (g: heap) (h_addr: hp_addr) : Lemma
  (requires U64.v h_addr + 8 >= heap_size)
  (ensures unpack_objects g h_addr == [])

/// Unfolding: unpack_objects returns [] when object overflows heap
val unpack_objects_empty_overflow (g: heap) (h_addr: hp_addr) : Lemma
  (requires U64.v h_addr + 8 < heap_size /\
            (None? (unpack_object g h_addr) \/
             (Some? (unpack_object g h_addr) /\
              (let (_, ol) = Some?.v (unpack_object g h_addr) in
               let next_nat = U64.v h_addr + (U64.v ol.wz + 1) * 8 in
               next_nat > heap_size \/ next_nat >= pow2 64))))
  (ensures unpack_objects g h_addr == [])

/// Unfolding: when unpack_object succeeds and next is within heap, unpack_objects returns cons
val unpack_objects_cons (g: heap) (h_addr: hp_addr) : Lemma
  (requires U64.v h_addr + 8 < heap_size /\
            Some? (unpack_object g h_addr) /\
            (let (_, ol) = Some?.v (unpack_object g h_addr) in
             let next_nat = U64.v h_addr + (U64.v ol.wz + 1) * 8 in
             next_nat <= heap_size /\ next_nat < pow2 64 /\
             next_nat < heap_size /\ next_nat % 8 == 0))
  (ensures (let (obj, ol) = Some?.v (unpack_object g h_addr) in
            let next_nat = U64.v h_addr + (U64.v ol.wz + 1) * 8 in
            let next : hp_addr = U64.uint_to_t next_nat in
            unpack_objects g h_addr == (obj, ol) :: unpack_objects g next))

/// Unfolding: terminal object (next >= heap_size)
val unpack_objects_singleton (g: heap) (h_addr: hp_addr) : Lemma
  (requires U64.v h_addr + 8 < heap_size /\
            Some? (unpack_object g h_addr) /\
            (let (_, ol) = Some?.v (unpack_object g h_addr) in
             let next_nat = U64.v h_addr + (U64.v ol.wz + 1) * 8 in
             next_nat <= heap_size /\ next_nat < pow2 64 /\
             next_nat >= heap_size))
  (ensures (let (obj, ol) = Some?.v (unpack_object g h_addr) in
            unpack_objects g h_addr == [(obj, ol)]))

/// Head element is in unpack_objects addresses
val unpack_objects_head (g: heap) (h_addr: hp_addr) : Lemma
  (requires U64.v h_addr + 8 < heap_size /\
            Some? (unpack_object g h_addr) /\
            (let (_, ol) = Some?.v (unpack_object g h_addr) in
             let next_nat = U64.v h_addr + (U64.v ol.wz + 1) * 8 in
             next_nat <= heap_size /\ next_nat < pow2 64))
  (ensures (let (obj, _) = Some?.v (unpack_object g h_addr) in
            List.Tot.mem obj (List.Tot.map fst (unpack_objects g h_addr))))

/// Tail membership monotonicity
val unpack_objects_mem_tail (g: heap) (h_addr: hp_addr) (x: obj_addr) : Lemma
  (requires U64.v h_addr + 8 < heap_size /\
            Some? (unpack_object g h_addr) /\
            (let (_, ol) = Some?.v (unpack_object g h_addr) in
             let next_nat = U64.v h_addr + (U64.v ol.wz + 1) * 8 in
             next_nat <= heap_size /\ next_nat < pow2 64 /\
             next_nat < heap_size /\ next_nat % 8 == 0 /\
             List.Tot.mem x (List.Tot.map fst (unpack_objects g (U64.uint_to_t next_nat)))))
  (ensures List.Tot.mem x (List.Tot.map fst (unpack_objects g h_addr)))

/// Per-entry pointer check
let entry_check (ol: object_l) (addrs: list obj_addr) : Tot bool =
  if U64.v ol.wz = 0 then true
  else
    List.Tot.for_all (fun (fv: U64.t) ->
      if U64.v fv >= 8 && U64.v fv < heap_size && U64.v fv % 8 = 0
      then List.Tot.mem fv addrs
      else true
    ) (Seq.seq_to_list ol.fields)

/// Safe per-entry pointer check at a heap address (total, handles None)
let entry_check_at (g: heap) (h: hp_addr) (addrs: list obj_addr) : GTot bool =
  match unpack_object g h with
  | None -> true
  | Some (_, ol) -> entry_check ol addrs

/// Check pointer closure against an external address list
val pointer_closed_ext (entries: list (obj_addr & object_l)) (addrs: list obj_addr) : GTot bool

/// Check pointer closure (defined as pointer_closed_ext with map fst)
val pointer_closed (entries: list (obj_addr & object_l)) : GTot bool

/// pointer_closed == pointer_closed_ext with map fst
val pointer_closed_ext_eq (entries: list (obj_addr & object_l))
  : Lemma (pointer_closed entries == pointer_closed_ext entries (List.Tot.map fst entries))

/// pointer_closed_ext unfolds on cons
val pointer_closed_ext_cons (entry: (obj_addr & object_l)) (rest: list (obj_addr & object_l)) (addrs: list obj_addr)
  : Lemma (pointer_closed_ext (entry :: rest) addrs ==
           (entry_check (snd entry) addrs && pointer_closed_ext rest addrs))

/// pointer_closed_ext on empty list
val pointer_closed_ext_nil (addrs: list obj_addr)
  : Lemma (pointer_closed_ext [] addrs = true)

/// pointer_closed from universal entry_check_at at position 0UL
/// Uses entry_check_at (total/safe) instead of entry_check+Some?.v to avoid subtyping issues
val pointer_closed_from_universal_0 (g: heap) (addrs: list obj_addr) : Lemma
  (requires addrs == List.Tot.map fst (unpack_objects g zero_addr) /\
    (forall (h: hp_addr). 
      (U64.v h + 8 < heap_size /\
       (match unpack_object g h with
        | None -> True
        | Some (_, ol) ->
          let next_nat = U64.v h + (U64.v ol.wz + 1) * 8 in
          next_nat <= heap_size /\ next_nat < pow2 64 /\
          List.Tot.mem (U64.uint_to_t (U64.v h + 8)) addrs)) ==>
      entry_check_at g h addrs = true))
  (ensures pointer_closed (unpack_objects g zero_addr) = true)

/// Logical heap: well-formed list of objects with pointer closure
type heap_l = entries:list (obj_addr & object_l){pointer_closed entries}

/// Top-level unpack: parse raw heap into logical form
val unpack (g: heap) : GTot (option heap_l)

/// Bridge: pointer_closed implies unpack succeeds
val pointer_closed_implies_unpack (g: heap) : Lemma
  (requires pointer_closed (unpack_objects g 0UL) = true)
  (ensures Some? (unpack g))

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

/// L1: Color update preserves domain
val update_color_l_preserves_domain (hl: heap_l) (addr: obj_addr) (c: Header.color_sem)
  : Lemma (heap_l_domain (update_color_l hl addr c) == heap_l_domain hl)

/// Check if a field value is valid w.r.t. an address list (computational, avoids subtyping)
let valid_field_value (v: U64.t) (addrs: list obj_addr) : Tot bool =
  if U64.v v >= 8 && U64.v v < heap_size && U64.v v % 8 = 0
  then List.Tot.mem v addrs
  else true

/// L2: Update a field of an object in heap_l
val update_field_l (hl: heap_l) (addr: obj_addr) (i: nat) (v: U64.t)
  : Ghost heap_l
    (requires (match lookup hl addr with
              | Some ol -> i < U64.v ol.wz /\
                valid_field_value v (heap_l_domain hl) = true
              | None -> True))
    (ensures fun _ -> True)

/// L2: Field update preserves domain
val update_field_l_preserves_domain (hl: heap_l) (addr: obj_addr) (i: nat) (v: U64.t)
  : Lemma (requires (match lookup hl addr with
              | Some ol -> i < U64.v ol.wz /\
                valid_field_value v (heap_l_domain hl) = true
              | None -> True))
          (ensures heap_l_domain (update_field_l hl addr i v) == heap_l_domain hl)

/// L3: Pointer children of a single object
val children_of (ol: object_l) : GTot (list obj_addr)

/// L3: Pointer children of an object address in the heap
val children (hl: heap_l) (addr: obj_addr) : GTot (list obj_addr)
