(*
   GC.Spec.Allocator.Lemmas.SearchBase — shared allocator-search helpers.

   Split out of Core to provide reusable boundaries for search proofs.
*)
module GC.Spec.Allocator.Lemmas.SearchBase

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Allocator.Lemmas.Header
open GC.Spec.Allocator.Lemmas.Split
open GC.Spec.Allocator.Lemmas.Part1

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

/// next_fp (link to next free block) is in objects if it's a valid pointer
let next_fp_in_objects (g: heap) (obj: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v (wosize_of_object obj g) >= 1 /\
                    (let hd = hd_address obj in
                     U64.v hd + 16 <= heap_size))
          (ensures (let next = read_word g obj in
                    is_pointer_field next ==>
                    Seq.mem next (objects zero_addr g)))
  = let hd = hd_address obj in
    let next = read_word g obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    if is_pointer_field next then begin
      // next = read_word g obj, obj is field 0 of obj
      // obj has wosize >= 1 (since hd + 16 <= heap_size means hd + 8 + 8 <= heap_size,
      // i.e., obj + 8 <= heap_size, which means wosize >= 1)
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      wf_object_size_bound g obj;
      // read_word g obj is the value at field index 0 of obj
      // is_pointer_to next target means hd_address next = hd_address target
      // We need: next ∈ objects(0, g)
      // Use: field 0 of obj is at obj, and read_word g obj = next.
      // is_pointer_field next means next is a valid obj_addr.
      // By wf_field_target_in_objects: if efptu(g, obj, wosize, next), then next ∈ objects.
      // Need to show efptu(g, obj, wosize, next).
      // field_read_implies_exists_pointing: if read_word at field k is a pointer to target,
      // then efptu finds it.
      // Field 0 at address obj + 0*8 = obj. read_word g obj = next.
      // is_pointer_to next next = (is_pointer_field next && hd_address next = hd_address next) = true
      field_read_implies_exists_pointing g obj (wosize_of_object obj g) 0UL next;
      wf_field_target_in_objects g obj next
    end

/// alloc_from_block preserves objects membership and returns rem_fp in objects
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let alloc_from_block_objects_facts
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz) /\
                    (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)))
          (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                    // Old objects are preserved
                    (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g')) /\
                    // rem_fp, if a valid pointer, is in objects(0, g')
                    (is_pointer_field rem_fp ==> Seq.mem rem_fp (objects zero_addr g'))))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let (g', rem_fp) = alloc_from_block g obj wz next_fp in
    if block_wz - wz >= 2 then begin
      // Split case
      alloc_split_facts g obj wz next_fp;
      // Old objects preserved
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g))
        (ensures Seq.mem h (objects zero_addr g'))
      = alloc_split_old_in_new g obj wz next_fp h
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      // rem_fp is in objects(0, g')
      alloc_split_rem_in_objects g obj wz next_fp
    end else begin
      // Exact fit case: objects are the same, rem_fp = next_fp
      alloc_exact_preserves_wf g obj wz next_fp;
      alloc_from_block_exact g obj wz next_fp;
      // In exact fit: alloc_from_block returns (write_word g hd new_hdr, next_fp)
      // objects are preserved (header_write_same_wosize_preserves_objects)
      let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
      make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj alloc_hdr;
      // rem_fp = next_fp. If pointer, in objects(0,g) = objects(0,g').
      ()
    end
#pop-options

/// Helper: for the split case, establish the fl_valid_transfer quantifier.
/// For all objects a in objects(0,g) with wosize >= 1:
///   - a ∈ objects(0,g')
///   - wosize(a,g') >= 1
///   - link preserved: read_word g' a == read_word g a
#restart-solver
#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"
let alloc_split_fl_transfer_pre
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (a: obj_addr)
  : Lemma (requires alloc_split_pre g obj wz next_fp /\
                    wz >= 1 /\
                    Seq.mem a (objects zero_addr g) /\
                    U64.v a >= U64.v mword /\
                    U64.v a < heap_size /\
                    U64.v a % U64.v mword = 0)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    Seq.mem a (objects zero_addr g') /\
                    (U64.v (wosize_of_object a g) >= 1 ==>
                      U64.v (wosize_of_object a g') >= 1) /\
                    (U64.v (wosize_of_object a g) >= 1 /\
                     U64.v (hd_address a) + 16 <= heap_size ==>
                      read_word g' a == read_word g a)))
  = alloc_split_facts g obj wz next_fp;
    alloc_from_block_objects_facts g obj wz next_fp;
    let (g', _) = alloc_from_block g obj wz next_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
    let rem_obj_nat = rem_hd_nat + 8 in
    hd_address_spec obj;
    hd_address_bounds obj;
    wf_object_size_bound g obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    if U64.v (wosize_of_object a g) >= 1 then begin
      hd_address_spec a;
      wosize_of_object_spec a g;
      wosize_of_object_bound a g;
      wf_object_size_bound g a;
      if a = obj then begin
        // Header changed to alloc_hdr with wosize = wz >= 1.
        // Link at a (= obj): obj ∉ {hd, rem_hd, rem_obj} since
        //   hd = obj - 8 ≠ obj; rem_hd > obj; rem_obj > obj
        assert (U64.v obj <> U64.v hd);  // hd = obj - 8 < obj
        assert (wz >= 1);
        assert (rem_hd_nat == U64.v hd + (1 + wz) * 8);
        assert ((1 + wz) * 8 >= 16);
        assert (rem_hd_nat >= U64.v hd + 16);
        assert (rem_hd_nat >= U64.v obj + 8);
        assert (U64.v obj <> rem_hd_nat);
        assert (rem_obj_nat > rem_hd_nat);
        assert (U64.v obj <> rem_obj_nat);
        // Link preservation: read_word g' obj == read_word g obj
        alloc_split_g3_agrees g obj wz next_fp (obj <: hp_addr);
        // Prove wosize(obj, g') = wz >= 1
        // Reconstruct intermediate heaps to trace read_word g' hd
        alloc_from_block_split_normal g obj wz next_fp;
        let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
        let g1 = write_word g hd alloc_hdr in
        let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
        let rem_wz = block_wz - wz - 1 in
        let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
        let g2 = write_word g1 rem_hd rem_hdr in
        let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
        let g3 = write_word g2 rem_obj next_fp in
        // read_word g' hd = alloc_hdr (tracing through writes)
        read_write_different g2 rem_obj hd next_fp;
        read_write_different g1 rem_hd hd rem_hdr;
        read_write_same g hd alloc_hdr;
        make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
        wosize_of_object_spec obj g3
      end else begin
        // a ≠ obj: objects_separated ensures a's header & body are outside obj's span
        if U64.v a < U64.v obj then begin
          objects_separated zero_addr g a obj;
          // a + wosize(a)*8 < obj, so a ≤ obj - 16 (since wosize >= 1, aligned)
          // hd_address(a) = a - 8 ≤ obj - 24 < hd = obj - 8 < rem_hd < rem_obj
          // a ≤ obj - 16 < obj - 8 = hd < rem_hd < rem_obj
          alloc_split_g3_agrees g obj wz next_fp (hd_address a);
          alloc_split_g3_agrees g obj wz next_fp (a <: hp_addr);
          wosize_of_object_spec a g;
          wosize_of_object_spec a g'
        end else begin
          objects_separated zero_addr g obj a;
          // a > obj + block_wz*8, so a >= obj + block_wz*8 + 8 (aligned)
          // hd_address(a) = a - 8 >= obj + block_wz*8 = hd + (block_wz+1)*8
          // All writes at hd, rem_hd, rem_obj are below hd + (block_wz+1)*8
          alloc_split_g3_agrees g obj wz next_fp (hd_address a);
          alloc_split_g3_agrees g obj wz next_fp (a <: hp_addr);
          wosize_of_object_spec a g;
          wosize_of_object_spec a g'
        end
      end
    end else ()
#pop-options

/// Helper: for the exact-fit case, establish the fl_valid_transfer quantifier.
#restart-solver
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let alloc_exact_fl_transfer_pre
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz < 2) /\
                    Seq.mem a (objects zero_addr g) /\
                    U64.v a >= U64.v mword /\
                    U64.v a < heap_size /\
                    U64.v a % U64.v mword = 0)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    Seq.mem a (objects zero_addr g') /\
                    (U64.v (wosize_of_object a g) >= 1 ==>
                      U64.v (wosize_of_object a g') >= 1) /\
                    (U64.v (wosize_of_object a g) >= 1 /\
                     U64.v (hd_address a) + 16 <= heap_size ==>
                      read_word g' a == read_word g a)))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
    alloc_from_block_exact g obj wz next_fp;
    let g' = write_word g hd alloc_hdr in
    hd_address_spec obj;
    hd_address_bounds obj;
    getWosize_bound hdr;
    make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;
    header_write_same_wosize_preserves_objects g obj alloc_hdr;
    alloc_exact_preserves_wf g obj wz next_fp;
    if U64.v (wosize_of_object a g) >= 1 then begin
      hd_address_spec a;
      wosize_of_object_spec a g;
      wosize_of_object_bound a g;
      wf_object_size_bound g a;
      if a = obj then begin
        // Header changed but wosize preserved (block_wz = block_wz)
        read_write_same g hd alloc_hdr;
        read_write_different g hd (a <: hp_addr) alloc_hdr;
        wosize_of_object_spec a g'
      end else begin
        // a ≠ obj: header at hd_address(a) ≠ hd, and a ≠ hd
        if U64.v a < U64.v obj then
          objects_separated zero_addr g a obj
        else
          objects_separated zero_addr g obj a;
        read_write_different g hd (hd_address a) alloc_hdr;
        read_write_different g hd (a <: hp_addr) alloc_hdr;
        wosize_of_object_spec a g;
        wosize_of_object_spec a g'
      end
    end else ()
#pop-options
