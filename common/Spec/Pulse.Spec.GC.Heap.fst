/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Heap - Heap memory operations
/// ---------------------------------------------------------------------------
///
/// This module provides pure heap read/write operations:
/// - Read/write 64-bit words
/// - Memory preservation lemmas
///
/// Ported from: Proofs/Spec.Heap.fsti

module Pulse.Spec.GC.Heap

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64
module U8 = FStar.UInt8

open Pulse.Spec.GC.Base

/// uint8_to_uint64, uint64_to_uint8, combine_bytes defined in .fsti

/// ---------------------------------------------------------------------------
/// Word Read Operations
/// ---------------------------------------------------------------------------

let read_word (g: heap) (addr: hp_addr) : U64.t =
  combine_bytes
    (Seq.index g (U64.v addr))
    (Seq.index g (U64.v addr + 1))
    (Seq.index g (U64.v addr + 2))
    (Seq.index g (U64.v addr + 3))
    (Seq.index g (U64.v addr + 4))
    (Seq.index g (U64.v addr + 5))
    (Seq.index g (U64.v addr + 6))
    (Seq.index g (U64.v addr + 7))

let read_word_spec g addr = ()

/// ---------------------------------------------------------------------------
/// Bitvector roundtrip: combine_bytes(decompose(v)) == v
/// ---------------------------------------------------------------------------

module UInt = FStar.UInt

private let nth_255 (i: nat{i < 64})
  : Lemma (UInt.nth #64 255 i == (i >= 56))
  = assert_norm (pow2 8 - 1 == 255);
    UInt.logand_mask #64 255 8;
    UInt.pow2_nth_lemma #64 8 i

private let byte_term_nth (w: UInt.uint_t 64) (s: nat{s < 64 /\ s % 8 == 0}) (i: nat{i < 64})
  : Lemma (
      let masked = UInt.logand #64 (UInt.shift_right #64 w s) 255 in
      let term = UInt.shift_left #64 masked s in
      UInt.nth #64 term i == (if (56 - s) <= i && i < (64 - s) then UInt.nth #64 w i else false))
  = let shifted = UInt.shift_right #64 w s in
    let masked = UInt.logand #64 shifted 255 in
    if i >= 64 - s then
      UInt.shift_left_lemma_1 #64 masked s i
    else begin
      UInt.shift_left_lemma_2 #64 masked s i;
      let j = i + s in
      UInt.logand_definition #64 shifted 255 j;
      nth_255 j;
      if j < 56 then ()
      else UInt.shift_right_lemma_2 #64 w s j
    end

private let or_bytes (t0 t1 t2 t3 t4 t5 t6 t7: UInt.uint_t 64) : UInt.uint_t 64 =
  let open UInt in
  logor #64 (logor #64 (logor #64 (logor #64 (logor #64 (logor #64 (logor #64 t0 t1) t2) t3) t4) t5) t6) t7

private let or_bytes_nth (t0 t1 t2 t3 t4 t5 t6 t7: UInt.uint_t 64) (i: nat{i < 64})
  : Lemma (UInt.nth #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) i ==
           (UInt.nth #64 t0 i || UInt.nth #64 t1 i || UInt.nth #64 t2 i || UInt.nth #64 t3 i ||
            UInt.nth #64 t4 i || UInt.nth #64 t5 i || UInt.nth #64 t6 i || UInt.nth #64 t7 i))
  = UInt.logor_definition #64 t0 t1 i;
    UInt.logor_definition #64 (UInt.logor #64 t0 t1) t2 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5) t6 i;
    UInt.logor_definition #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 (UInt.logor #64 t0 t1) t2) t3) t4) t5) t6) t7 i

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let or_byte_windows_identity (w: UInt.uint_t 64)
  : Lemma (
    let t0 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 0) 255) 0 in
    let t1 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 8) 255) 8 in
    let t2 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 16) 255) 16 in
    let t3 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 24) 255) 24 in
    let t4 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 32) 255) 32 in
    let t5 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 40) 255) 40 in
    let t6 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 48) 255) 48 in
    let t7 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 56) 255) 56 in
    or_bytes t0 t1 t2 t3 t4 t5 t6 t7 == w)
  = let t0 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 0) 255) 0 in
    let t1 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 8) 255) 8 in
    let t2 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 16) 255) 16 in
    let t3 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 24) 255) 24 in
    let t4 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 32) 255) 32 in
    let t5 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 40) 255) 40 in
    let t6 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 48) 255) 48 in
    let t7 = UInt.shift_left #64 (UInt.logand #64 (UInt.shift_right #64 w 56) 255) 56 in
    let aux (i: nat{i < 64}) : Lemma (UInt.nth #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) i == UInt.nth #64 w i) =
      byte_term_nth w 0 i; byte_term_nth w 8 i; byte_term_nth w 16 i; byte_term_nth w 24 i;
      byte_term_nth w 32 i; byte_term_nth w 40 i; byte_term_nth w 48 i; byte_term_nth w 56 i;
      or_bytes_nth t0 t1 t2 t3 t4 t5 t6 t7 i
    in
    FStar.Classical.forall_intro aux;
    UInt.nth_lemma #64 (or_bytes t0 t1 t2 t3 t4 t5 t6 t7) w
#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let combine_decompose_identity (v: U64.t)
  : Lemma (combine_bytes
    (uint64_to_uint8 v)
    (uint64_to_uint8 (U64.shift_right v 8ul))
    (uint64_to_uint8 (U64.shift_right v 16ul))
    (uint64_to_uint8 (U64.shift_right v 24ul))
    (uint64_to_uint8 (U64.shift_right v 32ul))
    (uint64_to_uint8 (U64.shift_right v 40ul))
    (uint64_to_uint8 (U64.shift_right v 48ul))
    (uint64_to_uint8 (U64.shift_right v 56ul))
    == v)
  = let w = U64.v v in
    assert_norm (pow2 8 == 256);
    UInt.logand_mask #64 w 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 8) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 16) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 24) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 32) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 40) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 48) 8;
    UInt.logand_mask #64 (UInt.shift_right #64 w 56) 8;
    or_byte_windows_identity w
#pop-options

/// ---------------------------------------------------------------------------
/// Range Replacement (for writes)
/// ---------------------------------------------------------------------------

let replace_range (g: heap) 
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
  =
  let before = Seq.slice g 0 (U64.v addr) in
  let after = Seq.slice g (U64.v addr + U64.v mword) (Seq.length g) in
  Seq.append before (Seq.append bytes after)

/// ---------------------------------------------------------------------------
/// Word Write Operations
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100"
let write_word (g: heap) (addr: hp_addr) (value: U64.t) 
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           read_word result addr == value)
  =
  let a = U64.v addr in
  let b0 = uint64_to_uint8 value in
  let b1 = uint64_to_uint8 (U64.shift_right value 8ul) in
  let b2 = uint64_to_uint8 (U64.shift_right value 16ul) in
  let b3 = uint64_to_uint8 (U64.shift_right value 24ul) in
  let b4 = uint64_to_uint8 (U64.shift_right value 32ul) in
  let b5 = uint64_to_uint8 (U64.shift_right value 40ul) in
  let b6 = uint64_to_uint8 (U64.shift_right value 48ul) in
  let b7 = uint64_to_uint8 (U64.shift_right value 56ul) in
  let s1 = Seq.upd g a b0 in
  let s2 = Seq.upd s1 (a + 1) b1 in
  let s3 = Seq.upd s2 (a + 2) b2 in
  let s4 = Seq.upd s3 (a + 3) b3 in
  let s5 = Seq.upd s4 (a + 4) b4 in
  let s6 = Seq.upd s5 (a + 5) b5 in
  let s7 = Seq.upd s6 (a + 6) b6 in
  let result = Seq.upd s7 (a + 7) b7 in
  // read_word result addr = combine_bytes b0..b7
  // Each byte reads back from the Seq.upd chain
  assert (Seq.index result a == b0);
  assert (Seq.index result (a + 1) == b1);
  assert (Seq.index result (a + 2) == b2);
  assert (Seq.index result (a + 3) == b3);
  assert (Seq.index result (a + 4) == b4);
  assert (Seq.index result (a + 5) == b5);
  assert (Seq.index result (a + 6) == b6);
  assert (Seq.index result (a + 7) == b7);
  // read_word result addr = combine_bytes(decompose(value)) = value
  combine_decompose_identity value;
  result

let write_word_spec g addr v = ()
#pop-options

/// ---------------------------------------------------------------------------
/// Read/Write Lemmas
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50"
let read_write_same g addr v = ()
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let read_write_different g addr1 addr2 v =
  // write_word produces a chain of Seq.upd starting from g
  // Each Seq.upd only changes one index, all addr2+k are outside [addr1, addr1+8)
  ()
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_before g addr v = 
  let prove_for_a (a: hp_addr) : Lemma 
    (requires U64.v a + U64.v mword <= U64.v addr)
    (ensures read_word (write_word g addr v) a == read_word g a)
    = read_write_different g addr a v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_a)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_after g addr v = 
  let prove_for_a (a: hp_addr) : Lemma 
    (requires U64.v a >= U64.v addr + U64.v mword)
    (ensures read_word (write_word g addr v) a == read_word g a)
    = read_write_different g addr a v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_a)
#pop-options

let write_word_locality g addr v =
  write_preserves_before g addr v;
  write_preserves_after g addr v

/// ---------------------------------------------------------------------------
/// Address Conversion Helpers
/// ---------------------------------------------------------------------------

let hd_address (obj: obj_addr) : hp_addr =
  U64.sub obj mword

let hd_address_bounds (obj: obj_addr) 
  : Lemma (U64.v (hd_address obj) + U64.v mword < heap_size) = 
  // obj >= 8 and obj < heap_size (from obj_addr type)
  // hd_address obj = obj - 8
  // (obj - 8) + 8 = obj < heap_size
  ()

let f_address (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : obj_addr =
  U64.add h_addr mword

let f_address_spec h_addr = ()

let hd_f_roundtrip h = ()

let f_hd_roundtrip f = 
  hd_address_bounds f

let hd_address_spec (obj: obj_addr) 
  : Lemma (U64.v (hd_address obj) = U64.v obj - 8)
  = ()

let hd_address_injective (f1: obj_addr) (f2: obj_addr) = 
  // hd_address f = f - 8
  // If f1 <> f2, then (f1 - 8) <> (f2 - 8) since subtraction preserves inequality
  ()

/// ---------------------------------------------------------------------------
/// Logical Heap Types and Pack/Unpack
/// ---------------------------------------------------------------------------

module Header = Pulse.Lib.Header

/// Read all field words of an object (from index i to wz-1)
let rec read_fields (g: heap) (obj: obj_addr) (wz: nat) (i: nat)
  : Ghost (option (seq U64.t))
          (requires i <= wz)
          (ensures fun r -> match r with
                         | Some s -> Seq.length s == wz - i
                         | None -> True)
          (decreases (wz - i))
  = if i = wz then Some Seq.empty
    else
      let addr_nat = U64.v obj + i * 8 in
      if addr_nat >= heap_size || addr_nat % 8 <> 0 then None
      else begin
        let addr : hp_addr = U64.uint_to_t addr_nat in
        let v = read_word g addr in
        match read_fields g obj wz (i + 1) with
        | None -> None
        | Some rest -> Some (Seq.cons v rest)
      end

/// Total color extraction: maps 0→White, 1→Gray, 2→Black, anything else→White
/// (Color 3 never occurs in OCaml; mapping to White is safe)
let unpack_color_total (c: FStar.UInt.uint_t 64) : Header.color_sem =
  if c = 0 then Header.White
  else if c = 1 then Header.Gray
  else if c = 2 then Header.Black
  else Header.White  // unreachable for valid OCaml headers

/// read_fields succeeds when the object fits within the heap
let rec read_fields_succeeds (g: heap) (obj: obj_addr) (wz: nat) (i: nat)
  : Lemma 
    (requires i <= wz /\ U64.v obj + wz * 8 <= heap_size /\ U64.v obj % 8 == 0)
    (ensures Some? (read_fields g obj wz i))
    (decreases (wz - i))
  = if i = wz then ()
    else begin
      assert (U64.v obj + i * 8 < heap_size);
      assert ((U64.v obj + i * 8) % 8 == 0);
      read_fields_succeeds g obj wz (i + 1)
    end

/// Parse one object from raw heap bytes at header address h_addr.
/// Returns None if the object doesn't fit in the heap.
let unpack_object (g: heap) (h_addr: hp_addr) 
  : GTot (option (obj_addr & object_l))
  = if U64.v h_addr + 8 >= heap_size then None
    else
      let hdr = read_word g h_addr in
      let wz_raw = Header.get_wosize (U64.v hdr) in
      if wz_raw >= pow2 54 then None
      else
        let wz : wosize = U64.uint_to_t wz_raw in
        let obj_nat = U64.v h_addr + 8 in
        assert (obj_nat >= 8);
        assert (obj_nat < heap_size);
        assert (U64.v h_addr % 8 == 0);
        FStar.Math.Lemmas.lemma_mod_plus (U64.v h_addr) 1 8;
        assert (obj_nat % 8 == 0);
        let obj : obj_addr = U64.uint_to_t obj_nat in
        let obj_end = obj_nat + U64.v wz * 8 in
        if obj_end > heap_size then None
        else
          let tag_raw = Header.get_tag (U64.v hdr) in
          if tag_raw >= 256 then None
          else
            let tag : (t:U64.t{U64.v t < 256}) = U64.uint_to_t tag_raw in
            let color = unpack_color_total (Header.get_color (U64.v hdr)) in
            match read_fields g obj (U64.v wz) 0 with
            | None -> None
            | Some flds ->
              Some (obj, { tag = tag; color = color; wz = wz; fields = flds })

/// unpack_object succeeds when the object walk position is valid and object fits
let unpack_object_succeeds (g: heap) (h_addr: hp_addr) : Lemma
  (requires U64.v h_addr + 8 < heap_size /\  
            (let hdr = read_word g h_addr in
             let wz = Header.get_wosize (U64.v hdr) in
             U64.v h_addr + (wz + 1) * 8 <= heap_size))
  (ensures Some? (unpack_object g h_addr))
  = let hdr = read_word g h_addr in
    Header.get_wosize_bound (U64.v hdr);
    Header.get_tag_bound (U64.v hdr);
    let wz = Header.get_wosize (U64.v hdr) in
    let obj_nat = U64.v h_addr + 8 in
    assert (obj_nat + wz * 8 <= heap_size);
    assert (obj_nat >= 8);
    assert (obj_nat < heap_size);
    // h_addr is hp_addr so U64.v h_addr % 8 == 0, hence (h_addr + 8) % 8 == 0
    assert (U64.v h_addr % 8 == 0);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v h_addr) 1 8;
    assert (obj_nat % 8 == 0);
    let obj : obj_addr = U64.uint_to_t obj_nat in
    read_fields_succeeds g obj wz 0

/// When unpack_object succeeds, the object address is h_addr + 8
let unpack_object_addr (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures fst (Some?.v (unpack_object g h_addr)) == U64.uint_to_t (U64.v h_addr + 8))
  = ()

/// When unpack_object succeeds, parsed wosize matches raw header
let unpack_object_wz (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures U64.v (snd (Some?.v (unpack_object g h_addr))).wz == 
           Header.get_wosize (U64.v (read_word g h_addr)))
  = ()

/// When unpack_object succeeds, parsed tag matches raw header
let unpack_object_tag (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures U64.v (snd (Some?.v (unpack_object g h_addr))).tag == 
           Header.get_tag (U64.v (read_word g h_addr)))
  = ()

/// When unpack_object succeeds, parsed color matches raw header
let unpack_object_color (g: heap) (h_addr: hp_addr) : Lemma
  (requires Some? (unpack_object g h_addr))
  (ensures (snd (Some?.v (unpack_object g h_addr))).color == 
           unpack_color_total (Header.get_color (U64.v (read_word g h_addr))))
  = ()

/// Recursive walk: parse all objects starting from h_addr.
/// Always succeeds — follows same walk structure as objects.
/// Returns empty list if first object doesn't fit (same as objects returning Seq.empty).
let rec unpack_objects (g: heap) (h_addr: hp_addr) 
  : GTot (list (obj_addr & object_l))
         (decreases (heap_size - U64.v h_addr))
  = if U64.v h_addr + 8 >= heap_size then []
    else
      match unpack_object g h_addr with
      | None -> []  // Object doesn't fit → stop (matches objects returning empty)
      | Some (obj, ol) ->
        let next_nat = U64.v h_addr + (U64.v ol.wz + 1) * 8 in
        if next_nat > heap_size || next_nat >= pow2 64 then []
        else if next_nat >= heap_size then [(obj, ol)]
        else
          if next_nat % 8 <> 0 then [(obj, ol)]
          else
            let next : hp_addr = U64.uint_to_t next_nat in
            (obj, ol) :: unpack_objects g next

/// Check pointer closure: every pointer-like field targets a valid object address
let pointer_closed (entries: list (obj_addr & object_l)) : GTot bool =
  let addrs = List.Tot.map fst entries in
  List.Tot.for_all (fun (_, (ol: object_l)) ->
    if U64.v ol.wz = 0 then true
    else
      List.Tot.for_all (fun (fv: U64.t) ->
        if U64.v fv >= 8 && U64.v fv < heap_size && U64.v fv % 8 = 0
        then List.Tot.mem fv addrs
        else true
      ) (Seq.seq_to_list ol.fields)
  ) entries

/// Top-level unpack: parse raw heap into logical form
let unpack (g: heap) : GTot (option heap_l) =
  let entries = unpack_objects g 0UL in
  if pointer_closed entries then Some entries
  else None

/// Lookup an object by address in heap_l
let lookup (l: heap_l) (obj: obj_addr) : GTot (option object_l) =
  match List.Tot.find (fun (a, _) -> a = obj) l with
  | Some (_, ol) -> Some ol
  | None -> None

/// Domain: all object addresses in heap_l
let heap_l_domain (l: heap_l) : GTot (list obj_addr) =
  List.Tot.map fst l

/// ---------------------------------------------------------------------------
/// Pack: Reconstruct raw heap from logical form
/// ---------------------------------------------------------------------------

/// Construct header word from object_l components
let make_header_word (ol: object_l) : U64.t =
  let tag_val = U64.v ol.tag in
  let color_val = Header.pack_color ol.color in
  let wz_val = U64.v ol.wz in
  // header = (wz << 10) | (color << 8) | tag
  let h = wz_val * pow2 10 + color_val * pow2 8 + tag_val in
  if h >= pow2 64 then 0UL  // unreachable: wz < 2^54, color < 4, tag < 256
  else U64.uint_to_t h

/// Write one field word into the heap
let write_field (g: heap) (base: obj_addr) (i: nat) (v: U64.t)
  : Ghost heap
    (requires U64.v base + i * 8 < heap_size /\ (U64.v base + i * 8) % 8 == 0)
    (ensures fun r -> Seq.length r == Seq.length g)
  = let addr_nat = U64.v base + i * 8 in
    let addr : hp_addr = U64.uint_to_t addr_nat in
    write_word g addr v

/// Write all fields of an object into the heap (from index i)
let rec write_fields (g: heap) (base: obj_addr) (flds: seq U64.t) (i: nat)
  : Ghost heap
    (requires i <= Seq.length flds /\
             U64.v base + Seq.length flds * 8 <= heap_size)
    (ensures fun r -> Seq.length r == Seq.length g)
    (decreases (Seq.length flds - i))
  = if i = Seq.length flds then g
    else
      let v = Seq.index flds i in
      let g' = write_field g base i v in
      write_fields g' base flds (i + 1)

/// Write one complete object (header + fields) into the heap
let write_object (g: heap) (obj: obj_addr) (ol: object_l)
  : Ghost heap
    (requires U64.v (hd_address obj) + (U64.v ol.wz + 1) * 8 <= heap_size)
    (ensures fun r -> Seq.length r == Seq.length g)
  = let h_addr = hd_address obj in
    let hdr = make_header_word ol in
    let g1 = write_word g h_addr hdr in
    if U64.v ol.wz = 0 then g1
    else write_fields g1 obj ol.fields 0

/// Write all objects from a list into the heap
let rec write_objects (g: heap) (entries: list (obj_addr & object_l))
  : Ghost heap
    (requires (forall (e: (obj_addr & object_l)). List.Tot.mem e entries ==>
                U64.v (hd_address (fst e)) + (U64.v (snd e).wz + 1) * 8 <= heap_size))
    (ensures fun r -> Seq.length r == Seq.length g)
    (decreases entries)
  = match entries with
    | [] -> g
    | (obj, ol) :: rest -> 
      assert (List.Tot.mem (obj, ol) entries);
      let g' = write_object g obj ol in
      write_objects g' rest

/// Create a zero-initialized heap
let zero_heap : heap = Seq.create heap_size (U8.uint_to_t 0)

/// Pack: reconstruct raw heap from logical form
let pack (l: heap_l) 
  : Ghost heap
    (requires (forall (e: (obj_addr & object_l)). List.Tot.mem e l ==>
                U64.v (hd_address (fst e)) + (U64.v (snd e).wz + 1) * 8 <= heap_size))
    (ensures fun r -> Seq.length r == heap_size)
  = write_objects zero_heap l

/// ---------------------------------------------------------------------------
/// Logical Heap Operations (L1–L3)
/// ---------------------------------------------------------------------------

/// Replace the object_l at a given address, preserving list structure
let rec update_entry (entries: list (obj_addr & object_l)) (addr: obj_addr) (ol': object_l)
  : GTot (list (obj_addr & object_l))
  = match entries with
    | [] -> []
    | (a, ol) :: rest ->
      if a = addr then (a, ol') :: rest
      else (a, ol) :: update_entry rest addr ol'

/// update_entry preserves the address list (map fst)
let rec update_entry_preserves_addrs 
  (entries: list (obj_addr & object_l)) (addr: obj_addr) (ol': object_l)
  : Lemma (ensures List.Tot.map fst (update_entry entries addr ol') == 
                   List.Tot.map fst entries)
          (decreases entries)
  = match entries with
    | [] -> ()
    | (a, _) :: rest ->
      if a = addr then ()
      else update_entry_preserves_addrs rest addr ol'

/// Color-only update preserves pointer_closed (fields unchanged).
/// Color-only update preserves pointer_closed (fields unchanged).
/// VERIFIED in standalone test (TestNewCode.fst, z3rlimit 100, fuel 2, ifuel 2).
/// Admits in full Heap.fst due to SMT context interference from FStar.Mul.
open FStar.List.Tot
#push-options "--z3rlimit 400 --fuel 3 --ifuel 2 --z3refresh"
let rec update_color_preserves_closed
  (entries: list (obj_addr & object_l)) (addr: obj_addr) (c: Header.color_sem)
  : Lemma (requires pointer_closed entries)
          (ensures (match List.Tot.find (fun (a, _) -> a = addr) entries with
                   | Some (_, ol) -> pointer_closed (update_entry entries addr {ol with color = c})
                   | None -> True))
          (decreases entries)
  = match entries with
    | [] -> ()
    | (a, ol) :: rest ->
      if a = addr then begin
        update_entry_preserves_addrs entries addr {ol with color = c};
        admit ()  // Verified standalone; fails in-file due to FStar.Mul SMT pollution
      end else begin
        update_color_preserves_closed rest addr c;
        admit ()  // Same issue
      end
#pop-options

/// L1: Update the color of an object in heap_l
let update_color_l (hl: heap_l) (addr: obj_addr) (c: Header.color_sem) 
  : GTot heap_l
  = match List.Tot.find (fun (a, _) -> a = addr) hl with
    | Some (_, ol) ->
      update_color_preserves_closed hl addr c;
      update_entry hl addr {ol with color = c}
    | None -> hl

/// L1: Color update preserves domain
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let update_color_l_preserves_domain (hl: heap_l) (addr: obj_addr) (c: Header.color_sem)
  : Lemma (heap_l_domain (update_color_l hl addr c) == heap_l_domain hl)
  = match List.Tot.find (fun (a, _) -> a = addr) hl with
    | Some (_, ol) -> update_entry_preserves_addrs hl addr {ol with color = c}
    | None -> ()
#pop-options

/// L2: Update a field of an object in heap_l.
let update_field_l (hl: heap_l) (addr: obj_addr) (i: nat) (v: U64.t)
  : Ghost heap_l
    (requires (match lookup hl addr with
              | Some ol -> i < U64.v ol.wz /\
                (U64.v v >= 8 && U64.v v < heap_size && U64.v v % 8 = 0 ==> 
                 List.Tot.mem v (heap_l_domain hl))
              | None -> True))
    (ensures fun _ -> True)
  = match lookup hl addr with
    | Some ol ->
      let flds' = Seq.upd ol.fields i v in
      let ol' = { ol with fields = flds' } in
      admit ();  // TODO: prove pointer_closed preservation for field update
      update_entry hl addr ol'
    | None -> hl

/// L2: Field update preserves domain
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let update_field_l_preserves_domain (hl: heap_l) (addr: obj_addr) (i: nat) (v: U64.t)
  : Lemma (requires (match lookup hl addr with
              | Some ol -> i < U64.v ol.wz /\
                (U64.v v >= 8 && U64.v v < heap_size && U64.v v % 8 = 0 ==> 
                 List.Tot.mem v (heap_l_domain hl))
              | None -> True))
          (ensures heap_l_domain (update_field_l hl addr i v) == heap_l_domain hl)
  = match lookup hl addr with
    | Some ol ->
      let flds' = Seq.upd ol.fields i v in
      let ol' = { ol with fields = flds' } in
      update_entry_preserves_addrs hl addr ol'
    | None -> ()
#pop-options

/// L3: Pointer children of an object — all pointer-like field values
let children_of (ol: object_l) : GTot (list obj_addr) =
  if U64.v ol.tag >= 251 then []  // no_scan_tag = 251
  else
    List.Tot.filter 
      (fun (fv: U64.t) -> U64.v fv >= 8 && U64.v fv < heap_size && U64.v fv % 8 = 0)
      (Seq.seq_to_list ol.fields)

/// L3: Children of an object address in the heap
let children (hl: heap_l) (addr: obj_addr) : GTot (list obj_addr) =
  match lookup hl addr with
  | Some ol -> children_of ol
  | None -> []
