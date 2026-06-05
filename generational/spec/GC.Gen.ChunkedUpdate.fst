/// ---------------------------------------------------------------------------
/// GC.Gen.ChunkedUpdate -- pointer rewriting over chunked major heaps
/// ---------------------------------------------------------------------------

module GC.Gen.ChunkedUpdate

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Gen.Base
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator

let obj_in_single_chunk_range (obj: obj_addr) : Tot prop =
  U64.v obj >= U64.v zero_addr + U64.v mword

let rec objects_in_single_chunk_range (objs: seq obj_addr) (idx: nat)
  : Tot prop (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then True
    else
      obj_in_single_chunk_range (Seq.index objs idx) /\
      objects_in_single_chunk_range objs (idx + 1)

let chunked_update_field_slot (src: obj_addr) (i: nat)
  : GTot (option hp_addr)
  = let field_offset = U64.v src + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then
      None
    else
      Some (U64.uint_to_t field_offset <: hp_addr)

let chunked_header_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option U64.t)
  = MH.read_word_in_major mh (hd_address obj)

let chunked_wosize_nat_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot nat
  = match chunked_header_of_object mh obj with
    | Some hdr -> U64.v (getWosize hdr)
    | None -> 0

let chunked_is_blue (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_header_of_object mh obj with
    | Some hdr -> getColor hdr = Blue
    | None -> false

let chunked_is_no_scan (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_header_of_object mh obj with
    | Some hdr -> U64.v (getTag hdr) >= U64.v no_scan_tag
    | None -> false

let chunked_update_field (mh: MH.major_heap) (field_addr: hp_addr)
                         (fwd: forwarding_map)
  : GTot MH.major_heap
  = match MH.read_word_in_major mh field_addr with
    | None -> mh
    | Some raw ->
      let field_val = to_minor_offset raw in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then
          SpecMajorAlloc.major_write_word_or_same mh field_addr new_val
        else
          mh
      else
        mh

let rec chunked_update_object_pointers (mh: MH.major_heap) (obj: obj_addr)
                                       (wosize: nat) (fwd: forwarding_map)
                                       (i: nat)
  : GTot MH.major_heap (decreases (wosize - i))
  = if i >= wosize then mh
    else
      match chunked_update_field_slot obj i with
      | None -> mh
      | Some field_addr ->
        let mh' = chunked_update_field mh field_addr fwd in
        chunked_update_object_pointers mh' obj wosize fwd (i + 1)

let chunked_update_object_pointers_done
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat)
  : Lemma
      (requires i >= wosize)
      (ensures chunked_update_object_pointers mh obj wosize fwd i == mh)
  = ()

let chunked_update_object_pointers_step
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat) (field_addr: hp_addr)
  : Lemma
      (requires i < wosize /\
                chunked_update_field_slot obj i == Some field_addr)
      (ensures
        chunked_update_object_pointers mh obj wosize fwd i ==
        chunked_update_object_pointers
          (chunked_update_field mh field_addr fwd) obj wosize fwd (i + 1))
  = ()

let chunked_update_object_pointers_invalid_slot
  (mh: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat)
  : Lemma
      (requires i < wosize /\
                chunked_update_field_slot obj i == None)
      (ensures chunked_update_object_pointers mh obj wosize fwd i == mh)
  = ()

let rec chunked_update_all_objects_aux (mh: MH.major_heap) (objs: seq obj_addr)
                                       (fwd: forwarding_map) (idx: nat)
  : GTot MH.major_heap (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then mh
    else
      let obj = Seq.index objs idx in
      if chunked_is_blue mh obj then
        chunked_update_all_objects_aux mh objs fwd (idx + 1)
      else if chunked_is_no_scan mh obj then
        chunked_update_all_objects_aux mh objs fwd (idx + 1)
      else
        let wz = chunked_wosize_nat_of_object mh obj in
        let mh' = chunked_update_object_pointers mh obj wz fwd 0 in
        chunked_update_all_objects_aux mh' objs fwd (idx + 1)

let chunked_update_major_pointers (mh: MH.major_heap) (fwd: forwarding_map)
  : GTot MH.major_heap
  = chunked_update_all_objects_aux mh (MH.major_objects mh) fwd 0

let chunked_is_blue_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_is_blue (MH.single_chunk_major_heap g) obj ==
        is_blue obj g)
  = hd_address_bounds obj;
    hd_address_spec obj;
    assert (U64.v mword == 8);
    assert (U64.v (hd_address obj) >= U64.v zero_addr);
    MH.single_chunk_read_word_compat g (hd_address obj);
    color_of_object_spec obj g;
    is_blue_iff obj g

let chunked_is_no_scan_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_is_no_scan (MH.single_chunk_major_heap g) obj ==
        is_no_scan obj g)
  = hd_address_bounds obj;
    hd_address_spec obj;
    assert (U64.v mword == 8);
    assert (U64.v (hd_address obj) >= U64.v zero_addr);
    MH.single_chunk_read_word_compat g (hd_address obj);
    tag_of_object_spec obj g;
    is_no_scan_spec obj g

let chunked_wosize_nat_single_chunk_compat (g: heap) (obj: obj_addr)
  : Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_wosize_nat_of_object (MH.single_chunk_major_heap g) obj ==
        U64.v (wosize_of_object obj g))
  = hd_address_bounds obj;
    hd_address_spec obj;
    assert (U64.v mword == 8);
    assert (U64.v (hd_address obj) >= U64.v zero_addr);
    MH.single_chunk_read_word_compat g (hd_address obj);
    wosize_of_object_spec obj g

let chunked_update_field_single_chunk_compat
  (g: heap)
  (field_addr: hp_addr)
  (fwd: forwarding_map)
  : Lemma
      (requires U64.v field_addr >= U64.v zero_addr /\
                U64.v field_addr + U64.v mword <= heap_size)
      (ensures
        chunked_update_field (MH.single_chunk_major_heap g) field_addr fwd ==
        MH.single_chunk_major_heap
          (let field_val = to_minor_offset (read_word g field_addr) in
           if is_minor_pointer field_val then
             let new_val = fwd field_val in
             if new_val <> 0UL then write_word g field_addr new_val else g
           else g))
  = MH.single_chunk_read_word_compat g field_addr;
    let field_val = to_minor_offset (read_word g field_addr) in
    if is_minor_pointer field_val then begin
      let new_val = fwd field_val in
      if new_val <> 0UL then
        SpecMajorAlloc.major_write_word_or_same_single_chunk_compat
          g field_addr new_val
    end

let rec chunked_update_object_pointers_single_chunk_compat
  (g: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma
      (requires obj_in_single_chunk_range obj)
      (ensures
        chunked_update_object_pointers
          (MH.single_chunk_major_heap g) obj wosize fwd i ==
        MH.single_chunk_major_heap
          (update_object_pointers g obj wosize fwd i))
      (decreases (wosize - i))
  = if i >= wosize then ()
    else begin
      let field_offset = U64.v obj + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then begin
        assert (chunked_update_field_slot obj i == None)
      end else begin
        let field_addr : hp_addr = U64.uint_to_t field_offset in
        assert (U64.v field_addr == field_offset);
        assert (U64.v field_addr >= U64.v zero_addr);
        assert (chunked_update_field_slot obj i == Some field_addr);
        chunked_update_field_single_chunk_compat g field_addr fwd;
        let field_val = to_minor_offset (read_word g field_addr) in
        if is_minor_pointer field_val then begin
          let new_val = fwd field_val in
          if new_val <> 0UL then
            chunked_update_object_pointers_single_chunk_compat
              (write_word g field_addr new_val) obj wosize fwd (i + 1)
          else
            chunked_update_object_pointers_single_chunk_compat
              g obj wosize fwd (i + 1)
        end else
          chunked_update_object_pointers_single_chunk_compat
            g obj wosize fwd (i + 1)
      end
    end

let rec chunked_update_all_objects_aux_single_chunk_compat
  (g: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma
      (requires objects_in_single_chunk_range objs idx)
      (ensures
        chunked_update_all_objects_aux
          (MH.single_chunk_major_heap g) objs fwd idx ==
        MH.single_chunk_major_heap
          (update_all_objects_aux g objs fwd idx))
      (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      assert (obj_in_single_chunk_range obj);
      assert (objects_in_single_chunk_range objs (idx + 1));
      chunked_is_blue_single_chunk_compat g obj;
      if is_blue obj g then
        chunked_update_all_objects_aux_single_chunk_compat
          g objs fwd (idx + 1)
      else begin
        chunked_is_no_scan_single_chunk_compat g obj;
        if is_no_scan obj g then
          chunked_update_all_objects_aux_single_chunk_compat
            g objs fwd (idx + 1)
        else begin
          chunked_wosize_nat_single_chunk_compat g obj;
          let wz = U64.v (wosize_of_object obj g) in
          chunked_update_object_pointers_single_chunk_compat
            g obj wz fwd 0;
          let g' = update_object_pointers g obj wz fwd 0 in
          chunked_update_all_objects_aux_single_chunk_compat
            g' objs fwd (idx + 1)
        end
      end
    end

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let objects_zero_addr_index_in_single_chunk_range (g: heap)
                                                    (k: nat{k < Seq.length (objects zero_addr g)})
  : Lemma
      (ensures obj_in_single_chunk_range (Seq.index (objects zero_addr g) k))
  =
    let obj = Seq.index (objects zero_addr g) k in
    FStar.Seq.Properties.lemma_index_is_nth (objects zero_addr g) k;
    assert (Seq.mem obj (objects zero_addr g));
    objects_addresses_gt_start zero_addr g obj;
    assert (U64.v obj > U64.v zero_addr);
    assert (U64.v obj % U64.v mword == 0);
    assert (U64.v zero_addr % U64.v mword == 0);
    MH.word_aligned_gt_at_least_mword (U64.v obj) (U64.v zero_addr);
    assert (U64.v obj >= U64.v zero_addr + U64.v mword)
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let rec objects_zero_addr_in_single_chunk_range_from (g: heap) (idx: nat)
  : Lemma
      (requires idx <= Seq.length (objects zero_addr g))
      (ensures objects_in_single_chunk_range (objects zero_addr g) idx)
      (decreases (Seq.length (objects zero_addr g) - idx))
  = if idx >= Seq.length (objects zero_addr g) then ()
    else begin
      let kk : k':nat{k' < Seq.length (objects zero_addr g)} = idx in
      objects_zero_addr_index_in_single_chunk_range g kk;
      objects_zero_addr_in_single_chunk_range_from g (idx + 1)
    end
#pop-options

let objects_zero_addr_in_single_chunk_range (g: heap)
  : Lemma
      (ensures objects_in_single_chunk_range (objects zero_addr g) 0)
  = objects_zero_addr_in_single_chunk_range_from g 0

let chunked_update_major_pointers_single_chunk_compat
  (g: heap) (fwd: forwarding_map)
  : Lemma
      (ensures
        chunked_update_major_pointers (MH.single_chunk_major_heap g) fwd ==
        MH.single_chunk_major_heap (update_major_pointers g fwd))
  = MH.single_chunk_major_objects_compat g;
    objects_zero_addr_in_single_chunk_range g;
    chunked_update_all_objects_aux_single_chunk_compat
      g (objects zero_addr g) fwd 0
