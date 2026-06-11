/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.BlueAlloc — alloc preserves blue_fields_closed
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.BlueAlloc

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Gen.PromoteUpdate.Aux
open GC.Gen.PromoteUpdate.Header

module AllocLemmas = GC.Spec.Allocator.Lemmas
module FreeListShape = GC.Gen.FreeListShape
module WriteBody = GC.Gen.WriteBodyLemmas

/// ---------------------------------------------------------------------------
/// promote_all preserves blue_fields_closed
/// ---------------------------------------------------------------------------

/// Base case: well_formed_heap_part2 implies blue_fields_closed
/// (blue_fields_closed is a weakening of part2 — restricted to blue objects)
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always"
let wfh_part2_implies_blue_fields_closed (g: heap)
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part2 g)
          (ensures blue_fields_closed g)
  = reveal_opaque (`%blue_fields_closed) blue_fields_closed;
    let aux (src: obj_addr) (j: nat)
      : Lemma (Seq.mem src (objects zero_addr g) /\ is_blue src g /\
               j < U64.v (wosize_of_object src g) /\
               U64.v src + j * 8 + 8 <= heap_size ==>
               (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g)))
      = if Seq.mem src (objects zero_addr g) && is_blue src g &&
           j < U64.v (wosize_of_object src g) &&
           U64.v src + j * 8 + 8 <= heap_size
        then begin
          let wz = wosize_of_object src g in
          let far : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
          let v = read_word g far in
          if is_pointer v then begin
            hd_address_spec src;
            assert (well_formed_object g src);
            wosize_of_object_bound src g;
            assert (U64.v wz < pow2 54);
            let k : U64.t = U64.uint_to_t j in
            FStar.Math.Lemmas.pow2_lt_compat 61 54;
            assert (U64.v k < U64.v wz);
            assert (U64.v k < pow2 61);
            assert (U64.v wz <= U64.v (wosize_of_object src g));
            FStar.Math.Lemmas.small_mod (j * U64.v mword) (pow2 64);
            assert (U64.v (U64.mul_mod k mword) == j * 8);
            FStar.Math.Lemmas.small_mod (U64.v src + j * 8) (pow2 64);
            assert (U64.v (U64.add_mod src (U64.mul_mod k mword)) == U64.v src + j * 8);
            assert (U64.v (U64.add_mod src (U64.mul_mod k mword)) < heap_size);
            assert (U64.v (U64.add_mod src (U64.mul_mod k mword)) % 8 == 0);
            assert (is_pointer_to v (v <: obj_addr));
            field_read_implies_exists_pointing g src wz k (v <: obj_addr);
            assert (exists_field_pointing_to_unchecked g src wz (v <: obj_addr))
          end else ()
        end else ()
    in
    FStar.Classical.forall_intro_2 aux
#pop-options

/// Helper: alloc_spec preserves blue_fields_closed.
/// After allocation, blue objects' pointer fields still target valid objects.
///
/// Proof argument (documented for future discharge):
/// After alloc_spec, blue objects in heap_out are:
/// 1. Original blue objects from major (minus dst_obj which became white), headers unchanged
/// 2. The remainder (if split), which is new and blue
///
/// For category 1 (src in objects(major), src != dst_obj, src is blue):
///   alloc only modifies: hd(dst_obj), rem_hd, rem_obj (field 0 of remainder), prev_fp (field 0).
///   - hd(dst_obj), rem_hd, rem_obj are all >= hd(dst_obj). For src < dst_obj: field < hd(dst_obj).
///   - For src > dst_obj and src != remainder: src's body above all writes. prev_fp < dst_obj < src.
///   - prev_fp write: if src = prev_fp and j = 0, written value is remainder_fp or next_fp, both in objects(new).
///   - All other fields: read unchanged from major -> by bfc(major) -> in objects(major) <= objects(new).
///
/// For category 2 (remainder):
///   - Field 0 = next_fp (original next in chain). If is_pointer: in objects by fl_valid.
///   - Fields j > 0: addresses were in body of original dst_obj block (which was blue).
///     By bfc(major) for original block: pointer targets in objects(major) <= objects(new_major).
#push-options "--z3rlimit 150 --fuel 1 --ifuel 0 --z3refresh --split_queries always"
private let rec alloc_search_preserves_bfc
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap_part1 g /\
      AllocLemmas.fl_valid g cur_fp fuel /\
      AllocLemmas.fl_chain_terminates g cur_fp fuel /\
      blue_fields_closed g /\
      wz >= 1 /\
      (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out <> 0UL /\
      (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false ==>
        AllocLemmas.chain_avoids g cur_fp obj fuel = true) /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
        Seq.mem x (objects zero_addr (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)) /\
      (prev_fp <> 0UL ==>
        (prev_fp <> cur_fp /\
         U64.v prev_fp >= U64.v mword /\ U64.v prev_fp < heap_size /\
         U64.v prev_fp % U64.v mword = 0 /\
         Seq.mem prev_fp (objects zero_addr g) /\
         U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
         is_blue (prev_fp <: obj_addr) g)))
    (ensures
      blue_fields_closed (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)
    (decreases fuel)
  =
  let open GC.Spec.Allocator in
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    assert (U64.v cur_fp >= U64.v mword /\ U64.v cur_fp < heap_size /\ U64.v cur_fp % U64.v mword == 0);
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
    AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;

    if not (is_blue obj g) then
      AllocLemmas.chain_avoids_head_ne g cur_fp (obj <: U64.t) fuel
    else

    if bwz >= wz then begin
      // *** FOUND CASE ***
      let (g', new_rem_fp) = alloc_from_block g obj wz next_fp in
      let heap_out =
        if prev_fp = 0UL then g'
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0
        then write_word g' (prev_fp <: hp_addr) new_rem_fp
        else g'
      in
      assert (heap_out == (alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out);

      let bfc_proof (src: obj_addr) (j: nat)
        : Lemma (Seq.mem src (objects zero_addr heap_out) /\ is_blue src heap_out /\
                 j < U64.v (wosize_of_object src heap_out) /\
                 U64.v src + j * 8 + 8 <= heap_size ==>
                 (let v = read_word heap_out (U64.uint_to_t (U64.v src + j * 8)) in
                  is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr heap_out)))
        = if not (Seq.mem src (objects zero_addr heap_out) && is_blue src heap_out &&
                  j < U64.v (wosize_of_object src heap_out) &&
                  U64.v src + j * 8 + 8 <= heap_size)
          then ()
          else begin
            let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
            let v = read_word heap_out field_addr in
            if not (is_pointer v) then ()
            else if Seq.mem src (objects zero_addr g) then begin
              // Case A: src in objects(g) — frame reasoning
              // Step 1: obj is not blue in heap_out → src ≠ obj
              GC.Gen.AllocProps.alloc_from_block_obj_not_blue g obj wz next_fp;
              hd_address_spec obj;
              if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
                hd_address_spec obj;
                if U64.v prev_fp < U64.v obj then
                  objects_separated zero_addr g (prev_fp <: obj_addr) obj
                else
                  objects_separated zero_addr g obj (prev_fp <: obj_addr);
                // prev_fp and hd(obj) are word-separated (from objects_separated)
                read_write_different g' (prev_fp <: hp_addr) (hd_address obj) new_rem_fp;
                color_of_header_eq obj (write_word g' (prev_fp <: hp_addr) new_rem_fp) g'
              end else ();
              assert (is_blue obj heap_out = false);
              assert (src <> obj);

              // Step 2: Header of src preserved → color/wosize preserved
              hd_address_spec src;
              hd_address_bounds src;
              wosize_of_object_spec src g;
              wosize_of_object_spec obj g;
              if U64.v src < U64.v obj then
                objects_separated zero_addr g src obj
              else
                objects_separated zero_addr g obj src;
              GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp (hd_address src);
              if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
                if U64.v src < U64.v prev_fp then
                  objects_separated zero_addr g src (prev_fp <: obj_addr)
                else if U64.v src > U64.v prev_fp then
                  objects_separated zero_addr g (prev_fp <: obj_addr) src
                else ();  // src = prev_fp: hd(src) = src - 8 ≠ src = prev_fp (write addr)
                read_write_different g' (prev_fp <: hp_addr) (hd_address src) new_rem_fp
              end else ();
              color_of_header_eq src heap_out g;
              assert (is_blue src g);
              wosize_of_object_spec src heap_out;
              assert (j < U64.v (wosize_of_object src g));

              // Step 3: Field value preservation
              if j > 0 || src <> prev_fp ||
                 prev_fp = 0UL ||
                 not (U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                      U64.v prev_fp % U64.v mword = 0) then begin
                // Field NOT overwritten by prev_fp write
                GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp field_addr;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
                  if src <> prev_fp then begin
                    if U64.v src < U64.v prev_fp then
                      objects_separated zero_addr g src (prev_fp <: obj_addr)
                    else
                      objects_separated zero_addr g (prev_fp <: obj_addr) src
                  end else ();
                  read_write_different g' (prev_fp <: hp_addr) field_addr new_rem_fp
                end else ();
                blue_fields_closed_inst g src j;
                assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                ()
              end
              else begin
                // j = 0 and src = prev_fp: field_addr = src = prev_fp, overwritten
                // v = new_rem_fp (the overwritten value)
                // Need: is_pointer new_rem_fp ==> new_rem_fp ∈ objects(heap_out)
                wfh_part1_obj_bound g obj;
                assert (U64.v obj + bwz * 8 <= heap_size);
                if bwz - wz < 2 then begin
                  // Exact fit: new_rem_fp = next_fp
                  GC.Spec.Allocator.alloc_from_block_exact g obj wz next_fp;
                  // next_fp = read_word g obj (field 0 of obj)
                  // obj is blue, in objects(g), wosize >= 1
                  blue_fields_closed_inst g obj 0;
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                  ()
                end
                else begin
                  // Split: bwz - wz >= 2
                  let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                  if rem_hd_nat >= heap_size then begin
                    // rem_hd OOB: new_rem_fp = next_fp (same as exact)
                    GC.Spec.Allocator.alloc_from_block_split_rem_hd_oob g obj wz next_fp;
                    blue_fields_closed_inst g obj 0;
                    assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                    assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                    ()
                  end
                  else begin
                    let rem_obj_nat = rem_hd_nat + 8 in
                    if rem_obj_nat >= heap_size then begin
                      // rem_obj OOB: new_rem_fp has address >= heap_size → not a pointer
                      GC.Spec.Allocator.alloc_from_block_split_rem_obj_oob g obj wz next_fp;
                      // is_pointer requires U64.v v < heap_size, contradiction
                      assert (U64.v new_rem_fp >= heap_size);
                      ()
                    end
                    else begin
                      // Normal split: new_rem_fp = remainder object address
                      GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
                      // new_rem_fp ∈ objects(g')
                      AllocLemmas.alloc_from_block_rem_in_objects_part1 g obj wz next_fp;
                      // objects(heap_out) == objects(g') via write_body_preserves_objects
                      AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                      wosize_of_object_spec (prev_fp <: obj_addr) g';
                      write_body_preserves_objects g' (prev_fp <: obj_addr)
                        (prev_fp <: hp_addr) new_rem_fp;
                      ()
                    end
                  end
                end
              end
            end
            else begin
              // Case B: src not in objects(g) — must be the remainder from a normal split.
              assert (~(Seq.mem src (objects zero_addr g)));

              // bwz - wz must be >= 2 (otherwise objects unchanged → contradiction)
              if bwz - wz < 2 then begin
                // Exact fit: objects(g') == objects(g), so objects(heap_out) == objects(g)
                // But src ∈ objects(heap_out) and src ∉ objects(g) — contradiction!
                GC.Gen.AllocProps.alloc_from_block_exact_objects_eq_part1 g obj wz next_fp;
                wosize_of_object_spec obj g;
                wfh_part1_obj_bound g obj;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g));
                  AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g'));
                  assert (prev_fp <> obj);
                  objects_separated zero_addr g (prev_fp <: obj_addr) obj;
                  objects_separated zero_addr g obj (prev_fp <: obj_addr);
                  hd_address_spec (prev_fp <: obj_addr);
                  wosize_of_object_spec (prev_fp <: obj_addr) g;
                  GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp
                    (hd_address (prev_fp <: obj_addr));
                  wosize_of_object_spec (prev_fp <: obj_addr) g';
                  write_body_preserves_objects g' (prev_fp <: obj_addr)
                    (prev_fp <: hp_addr) new_rem_fp
                end else ();
                // objects(heap_out) == objects(g) in all cases → src ∈ objects(g)
                assert (Seq.mem src (objects zero_addr g))
              end
              else begin
                // Split case: bwz - wz >= 2
                // Establish normal split bounds first (needed by alloc_from_block_split_normal)
                wosize_of_object_spec obj g;
                wfh_part1_obj_bound g obj;
                assert (U64.v obj + bwz * 8 <= heap_size);

                // Establish objects(heap_out) = objects(g') via write_body_preserves_objects
                GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
                AllocLemmas.alloc_from_block_rem_in_objects_part1 g obj wz next_fp;
                AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g));
                  AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g'));
                  // Establish wosize(prev_fp, g') == wosize(prev_fp, g) via frame
                  assert (prev_fp <> obj);
                  objects_separated zero_addr g (prev_fp <: obj_addr) obj;
                  objects_separated zero_addr g obj (prev_fp <: obj_addr);
                  hd_address_spec (prev_fp <: obj_addr);
                  wosize_of_object_spec (prev_fp <: obj_addr) g;
                  GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp
                    (hd_address (prev_fp <: obj_addr));
                  wosize_of_object_spec (prev_fp <: obj_addr) g';
                  write_body_preserves_objects g' (prev_fp <: obj_addr)
                    (prev_fp <: hp_addr) new_rem_fp
                end else ();

                // src ∈ objects(g') (from objects(heap_out) = objects(g') and hypothesis)
                AllocLemmas.alloc_from_block_objects_backward_part1 g obj wz next_fp src;
                assert (src == new_rem_fp);
                let rem_hd_nat2 = U64.v hd + (1 + wz) * 8 in
                let rem_obj_nat2 = rem_hd_nat2 + 8 in
                assert (rem_hd_nat2 < heap_size);
                assert (rem_obj_nat2 < heap_size);

                let rem_hd2 : hp_addr = U64.uint_to_t rem_hd_nat2 in

                hd_address_spec (src <: obj_addr);
                assert (hd_address (src <: obj_addr) == rem_hd2);

                // Establish wosize of src in heap_out
                GC.Spec.Allocator.alloc_split_normal_read_rem_hd g obj wz next_fp;
                let rem_wz = bwz - wz - 1 in
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then
                  read_write_different g' (prev_fp <: hp_addr) rem_hd2 new_rem_fp
                else ();
                wosize_of_object_spec (src <: obj_addr) heap_out;
                AllocLemmas.make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
                assert (U64.v (wosize_of_object (src <: obj_addr) heap_out) = rem_wz);
                assert (j < rem_wz);

                // Handle field j
                if j = 0 then begin
                  GC.Spec.Allocator.alloc_split_normal_read_rem_field g obj wz next_fp;
                  if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                     U64.v prev_fp % U64.v mword = 0 then
                    read_write_different g' (prev_fp <: hp_addr) (src <: hp_addr) new_rem_fp
                  else ();
                  blue_fields_closed_inst g obj 0;
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                  ()
                end
                else begin
                  GC.Spec.Allocator.alloc_split_normal_read_other g obj wz next_fp field_addr;
                  if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                     U64.v prev_fp % U64.v mword = 0 then
                    read_write_different g' (prev_fp <: hp_addr) field_addr new_rem_fp
                  else ();
                  assert (wz + 1 + j < bwz);
                  blue_fields_closed_inst g obj (wz + 1 + j);
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                  ()
                end
              end
            end
          end
      in
      reveal_opaque (`%blue_fields_closed) blue_fields_closed;
      FStar.Classical.forall_intro_2 bfc_proof
    end
    else begin
      // *** NOT FOUND: advance to next ***
      if U64.v hd + 16 <= heap_size then begin
        AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
        let chain_blue_next (nobj: obj_addr)
          : Lemma (requires Seq.mem nobj (objects zero_addr g) /\ is_blue nobj g = false)
                  (ensures AllocLemmas.chain_avoids g next_fp nobj (fuel - 1) = true)
          = AllocLemmas.chain_avoids_tail g cur_fp nobj fuel
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires chain_blue_next);
        alloc_search_preserves_bfc g head_fp cur_fp next_fp wz (fuel - 1)
      end else ()
    end
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
let alloc_spec_preserves_blue_fields_closed
  (major: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed major /\
      wz >= 1 /\
      (GC.Spec.Allocator.alloc_spec major fp wz).obj_out <> 0UL /\
      chain_objects_blue major fp)
    (ensures
      blue_fields_closed (GC.Spec.Allocator.alloc_spec major fp wz).heap_out)
  =
    let fuel = heap_size / U64.v mword in
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
    let chain_avoids_non_blue (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr major) /\ is_blue obj major = false)
              (ensures AllocLemmas.chain_avoids major fp obj fuel = true)
      = reveal_opaque (`%chain_objects_blue) chain_objects_blue
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires chain_avoids_non_blue);
    alloc_search_preserves_bfc major fp 0UL fp wz fuel
#pop-options

/// The allocator's output free-list head is null or a syntactically valid heap
/// pointer when all blue free-list link fields have that same value shape.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let alloc_from_block_fp_pointer_or_zero
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires
      well_formed_heap_part1 g /\
      Seq.mem obj (objects zero_addr g) /\
      is_blue obj g /\
      FreeListShape.blue_link_fields_valid g /\
      FreeListShape.fp_pointer_or_zero next_fp /\
      wz >= 1 /\
      U64.v (getWosize (read_word g (hd_address obj))) >= wz /\
      U64.v (wosize_of_object obj g) >= 1 /\
      U64.v (hd_address obj) + 16 <= heap_size)
    (ensures
      FreeListShape.fp_pointer_or_zero
        (snd (GC.Spec.Allocator.alloc_from_block g obj wz next_fp)))
  = let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec obj g;
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    assert (bwz >= wz);
    if bwz - wz < 2 then begin
      assert (FreeListShape.fp_pointer_or_zero next_fp);
      assert ((let hdr = read_word g (hd_address obj) in
               let bwz = U64.v (getWosize hdr) in
               bwz >= wz /\ bwz - wz < 2));
      GC.Spec.Allocator.alloc_from_block_exact g obj wz next_fp
    end
    else begin
      let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
      if rem_hd_nat >= heap_size then begin
        assert (FreeListShape.fp_pointer_or_zero next_fp);
        GC.Spec.Allocator.alloc_from_block_split_rem_hd_oob g obj wz next_fp
      end
      else begin
        let rem_obj_nat = rem_hd_nat + 8 in
        if rem_obj_nat >= heap_size then begin
          wfh_part1_obj_bound g obj;
          assert (U64.v obj + bwz * 8 <= heap_size);
          assert (wz + 1 < bwz);
          assert (rem_obj_nat == U64.v obj + (wz + 1) * 8);
          assert False
        end else begin
          GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
          objects_addresses_gt_start zero_addr g obj;
          assert (rem_obj_nat > U64.v obj);
          assert (rem_obj_nat > U64.v zero_addr);
          assert (rem_obj_nat % U64.v mword == 0);
          assert (rem_obj_nat >= U64.v zero_addr + U64.v mword);
          assert (FreeListShape.fp_pointer_or_zero (U64.uint_to_t rem_obj_nat))
        end
      end
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let rec alloc_search_fp_pointer_or_zero
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires
      well_formed_heap_part1 g /\
      AllocLemmas.fl_valid g cur_fp fuel /\
      AllocLemmas.fl_chain_terminates g cur_fp fuel /\
      FreeListShape.blue_link_fields_valid g /\
      FreeListShape.fp_pointer_or_zero head_fp /\
      wz >= 1 /\
      (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out <> 0UL /\
      (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false ==>
        AllocLemmas.chain_avoids g cur_fp obj fuel = true) /\
      (prev_fp <> 0UL ==>
        (prev_fp <> cur_fp /\
         U64.v prev_fp >= U64.v mword /\ U64.v prev_fp < heap_size /\
         U64.v prev_fp % U64.v mword = 0 /\
         Seq.mem prev_fp (objects zero_addr g) /\
         U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
         is_blue (prev_fp <: obj_addr) g)))
    (ensures
      FreeListShape.fp_pointer_or_zero
        (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).fp_out)
    (decreases fuel)
  =
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      assert (U64.v cur_fp >= U64.v mword /\
              U64.v cur_fp < heap_size /\
              U64.v cur_fp % U64.v mword == 0);
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      hd_address_spec obj;
      hd_address_bounds obj;
      let hdr = read_word g hd in
      let bwz = U64.v (getWosize hdr) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
      wosize_of_object_spec obj g;
      wfh_part1_obj_bound g obj;
      assert (U64.v (hd_address obj) + 16 <= heap_size);

      if not (is_blue obj g) then
        AllocLemmas.chain_avoids_head_ne g cur_fp (obj <: U64.t) fuel
      else if bwz >= wz then begin
        if prev_fp = 0UL then begin
          FreeListShape.blue_link_fields_valid_elim g obj;
          assert (FreeListShape.fp_pointer_or_zero next_fp);
          alloc_from_block_fp_pointer_or_zero g obj wz next_fp
        end
        else ()
      end else begin
        AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
        let chain_blue_next (nobj: obj_addr)
          : Lemma (requires Seq.mem nobj (objects zero_addr g) /\ is_blue nobj g = false)
                  (ensures AllocLemmas.chain_avoids g next_fp nobj (fuel - 1) = true)
          = AllocLemmas.chain_avoids_tail g cur_fp nobj fuel
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires chain_blue_next);
        alloc_search_fp_pointer_or_zero g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let alloc_spec_preserves_fp_pointer_or_zero
  (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    FreeListShape.blue_link_fields_valid g /\
                    FreeListShape.fp_pointer_or_zero fp /\
                    wz >= 1 /\
                    (GC.Spec.Allocator.alloc_spec g fp wz).obj_out <> 0UL /\
                    chain_objects_blue g fp)
          (ensures FreeListShape.fp_pointer_or_zero
                     (GC.Spec.Allocator.alloc_spec g fp wz).fp_out)
  =
    let fuel = heap_size / U64.v mword in
    let chain_avoids_non_blue (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false)
              (ensures AllocLemmas.chain_avoids g fp obj fuel = true)
      = reveal_opaque (`%chain_objects_blue) chain_objects_blue
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires chain_avoids_non_blue);
    alloc_search_fp_pointer_or_zero g fp 0UL fp wz fuel
#pop-options

#push-options "--z3rlimit 120 --fuel 1 --ifuel 0 --split_queries always"
private let rec alloc_search_preserves_blfv
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap_part1 g /\
      AllocLemmas.fl_valid g cur_fp fuel /\
      AllocLemmas.fl_chain_terminates g cur_fp fuel /\
      FreeListShape.blue_link_fields_valid g /\
      wz >= 1 /\
      (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out <> 0UL /\
      (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false ==>
        AllocLemmas.chain_avoids g cur_fp obj fuel = true) /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
        Seq.mem x (objects zero_addr (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)) /\
      (prev_fp <> 0UL ==>
        (prev_fp <> cur_fp /\
         U64.v prev_fp >= U64.v mword /\ U64.v prev_fp < heap_size /\
         U64.v prev_fp % U64.v mword = 0 /\
         Seq.mem prev_fp (objects zero_addr g) /\
         U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
         is_blue (prev_fp <: obj_addr) g)))
    (ensures
      FreeListShape.blue_link_fields_valid
        (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)
    (decreases fuel)
  =
    let open GC.Spec.Allocator in
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      assert (U64.v cur_fp >= U64.v mword /\ U64.v cur_fp < heap_size /\ U64.v cur_fp % U64.v mword == 0);
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      hd_address_spec obj;
      hd_address_bounds obj;
      let hdr = read_word g hd in
      let bwz = U64.v (getWosize hdr) in
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
      wosize_of_object_spec obj g;
      wfh_part1_obj_bound g obj;
      assert (U64.v (hd_address obj) + 16 <= heap_size);

      if not (is_blue obj g) then
        AllocLemmas.chain_avoids_head_ne g cur_fp (obj <: U64.t) fuel
      else if bwz >= wz then begin
        let (g', new_rem_fp) = alloc_from_block g obj wz next_fp in
        let heap_out =
          if prev_fp = 0UL then g'
          else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                  U64.v prev_fp % U64.v mword = 0
          then write_word g' (prev_fp <: hp_addr) new_rem_fp
          else g'
        in
        assert (heap_out == (alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out);
        FreeListShape.blue_link_fields_valid_elim g obj;
        assert (FreeListShape.fp_pointer_or_zero next_fp);
        alloc_from_block_fp_pointer_or_zero g obj wz next_fp;

        let blfv_proof (src: obj_addr)
          : Lemma (requires Seq.mem src (objects zero_addr heap_out) /\
                            is_blue src heap_out /\
                            U64.v (wosize_of_object src heap_out) >= 1 /\
                            U64.v (hd_address src) + 16 <= heap_size)
                  (ensures (let v = read_word heap_out src in
                            FreeListShape.fp_pointer_or_zero v))
          = if Seq.mem src (objects zero_addr g) then begin
              GC.Gen.AllocProps.alloc_from_block_obj_not_blue g obj wz next_fp;
              if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
                if U64.v prev_fp < U64.v obj then
                  objects_separated zero_addr g (prev_fp <: obj_addr) obj
                else
                  objects_separated zero_addr g obj (prev_fp <: obj_addr);
                read_write_different g' (prev_fp <: hp_addr) (hd_address obj) new_rem_fp;
                color_of_header_eq obj (write_word g' (prev_fp <: hp_addr) new_rem_fp) g'
              end else ();
              assert (is_blue obj heap_out = false);
              assert (src <> obj);

              hd_address_spec src;
              hd_address_bounds src;
              wosize_of_object_spec src g;
              wosize_of_object_spec obj g;
              if U64.v src < U64.v obj then
                objects_separated zero_addr g src obj
              else
                objects_separated zero_addr g obj src;
              GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp (hd_address src);
              if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
                if U64.v src < U64.v prev_fp then
                  objects_separated zero_addr g src (prev_fp <: obj_addr)
                else if U64.v src > U64.v prev_fp then
                  objects_separated zero_addr g (prev_fp <: obj_addr) src
                else ();
                read_write_different g' (prev_fp <: hp_addr) (hd_address src) new_rem_fp
              end else ();
              color_of_header_eq src heap_out g;
              assert (is_blue src g);
              wosize_of_object_spec src heap_out;
              assert (U64.v (wosize_of_object src g) >= 1);

              if src = prev_fp &&
                 prev_fp <> 0UL &&
                 U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
                assert (read_word heap_out src == new_rem_fp);
                assert (FreeListShape.fp_pointer_or_zero new_rem_fp)
              end else begin
                GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp (src <: hp_addr);
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then
                  read_write_different g' (prev_fp <: hp_addr) (src <: hp_addr) new_rem_fp
                else ();
                assert (read_word heap_out src == read_word g src);
                FreeListShape.blue_link_fields_valid_elim g src
              end
            end else begin
              assert (~(Seq.mem src (objects zero_addr g)));
              if bwz - wz < 2 then begin
                GC.Gen.AllocProps.alloc_from_block_exact_objects_eq_part1 g obj wz next_fp;
                wosize_of_object_spec obj g;
                wfh_part1_obj_bound g obj;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g));
                  AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g'));
                  assert (prev_fp <> obj);
                  objects_separated zero_addr g (prev_fp <: obj_addr) obj;
                  objects_separated zero_addr g obj (prev_fp <: obj_addr);
                  hd_address_spec (prev_fp <: obj_addr);
                  wosize_of_object_spec (prev_fp <: obj_addr) g;
                  GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp
                    (hd_address (prev_fp <: obj_addr));
                  wosize_of_object_spec (prev_fp <: obj_addr) g';
                  write_body_preserves_objects g' (prev_fp <: obj_addr)
                    (prev_fp <: hp_addr) new_rem_fp
                end else ();
                assert (Seq.mem src (objects zero_addr g))
              end else begin
                wosize_of_object_spec obj g;
                wfh_part1_obj_bound g obj;
                assert (U64.v obj + bwz * 8 <= heap_size);
                GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
                AllocLemmas.alloc_from_block_rem_in_objects_part1 g obj wz next_fp;
                AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g));
                  AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g'));
                  assert (prev_fp <> obj);
                  objects_separated zero_addr g (prev_fp <: obj_addr) obj;
                  objects_separated zero_addr g obj (prev_fp <: obj_addr);
                  hd_address_spec (prev_fp <: obj_addr);
                  wosize_of_object_spec (prev_fp <: obj_addr) g;
                  GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp
                    (hd_address (prev_fp <: obj_addr));
                  wosize_of_object_spec (prev_fp <: obj_addr) g';
                  write_body_preserves_objects g' (prev_fp <: obj_addr)
                    (prev_fp <: hp_addr) new_rem_fp
                end else ();
                AllocLemmas.alloc_from_block_objects_backward_part1 g obj wz next_fp src;
                assert (src == new_rem_fp);
                let rem_hd_nat2 = U64.v hd + (1 + wz) * 8 in
                let rem_obj_nat2 = rem_hd_nat2 + 8 in
                assert (rem_hd_nat2 < heap_size);
                assert (rem_obj_nat2 < heap_size);
                let rem_hd2 : hp_addr = U64.uint_to_t rem_hd_nat2 in
                hd_address_spec src;
                assert (hd_address src == rem_hd2);
                GC.Spec.Allocator.alloc_split_normal_read_rem_field g obj wz next_fp;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then
                  read_write_different g' (prev_fp <: hp_addr) (src <: hp_addr) new_rem_fp
                else ();
                assert (read_word heap_out src == next_fp);
                assert (FreeListShape.fp_pointer_or_zero next_fp)
              end
            end
        in
        FreeListShape.blue_link_fields_valid_intro heap_out blfv_proof
      end else begin
        AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
        let chain_blue_next (nobj: obj_addr)
          : Lemma (requires Seq.mem nobj (objects zero_addr g) /\ is_blue nobj g = false)
                  (ensures AllocLemmas.chain_avoids g next_fp nobj (fuel - 1) = true)
          = AllocLemmas.chain_avoids_tail g cur_fp nobj fuel
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires chain_blue_next);
        alloc_search_preserves_blfv g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --split_queries always"
let alloc_spec_preserves_blue_link_fields_valid
  (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword) /\
                    FreeListShape.blue_link_fields_valid g /\
                    wz >= 1 /\
                    (GC.Spec.Allocator.alloc_spec g fp wz).obj_out <> 0UL /\
                    chain_objects_blue g fp)
          (ensures FreeListShape.blue_link_fields_valid
                     (GC.Spec.Allocator.alloc_spec g fp wz).heap_out)
  =
    let fuel = heap_size / U64.v mword in
    AllocLemmas.alloc_spec_preserves_objects_part1 g fp wz;
    let chain_avoids_non_blue (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false)
              (ensures AllocLemmas.chain_avoids g fp obj fuel = true)
      = reveal_opaque (`%chain_objects_blue) chain_objects_blue
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires chain_avoids_non_blue);
    alloc_search_preserves_blfv g fp 0UL fp wz fuel
#pop-options

/// Helper: promote_object preserves blue_fields_closed.
/// 1. alloc_spec_preserves_blue_fields_closed -> bfc(new_major)
