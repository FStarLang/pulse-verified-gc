/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney.Dense — Density preservation through allocation + copy_fields
/// ---------------------------------------------------------------------------
///
/// Strategy:
/// - OOM case: heap unchanged, trivial.
/// - Non-OOM: prove density at alloc_from_block level with exact/split case split.
/// - copy_fields: objects unchanged, all headers preserved, transfer.
/// - Compose: alloc_spec = alloc_search (finds block) + alloc_from_block.

module GC.Gen.Cheney.Dense

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Lib.Header
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module SA = GC.Spec.Allocator
module Part1 = GC.Spec.Allocator.Lemmas.Part1
module Part2 = GC.Spec.Allocator.Lemmas.Part2

/// ---------------------------------------------------------------------------
/// Z3 4.15.3 arithmetic helpers
/// ---------------------------------------------------------------------------
///
/// `base + k * mword` stays word-aligned, and two distinct word-aligned
/// addresses are at least a word apart.  Both are trivial, and both are goals
/// that Z3 4.15.3 fails to discharge inside the density proofs below, where the
/// context carries the whole well-formed-heap and free-list invariant.  The
/// first carries an `SMTPat` because it is needed at every `U64.uint_to_t`
/// coercion to `hp_addr` in this module.

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let aligned_step (base k: nat)
  : Lemma (requires base % U64.v mword == 0)
          (ensures (base + k * 8) % U64.v mword == 0)
          [SMTPat ((base + k * 8) % U64.v mword)]
  = aligned_plus_mul8 base k

private let aligned_step8 (base: nat)
  : Lemma (requires base % U64.v mword == 0)
          (ensures (base + 8) % U64.v mword == 0)
          [SMTPat ((base + 8) % U64.v mword)]
  = aligned_plus_mul8 base 1

/// The remainder block's successor offset: splitting a block of `bwz` words into
/// `wz` + remainder lands exactly at the original block's end.
private let split_next_offset (hd wz bwz: nat)
  : Lemma (requires bwz >= wz + 1)
          (ensures hd + (1 + wz) * 8 + (bwz - wz - 1 + 1) * 8 == hd + (1 + bwz) * 8)
  = ()

private let aligned_apart (a b: U64.t)
  : Lemma (requires a <> b /\ U64.v a % U64.v mword == 0 /\ U64.v b % U64.v mword == 0)
          (ensures U64.v a + U64.v mword <= U64.v b \/
                   U64.v b + U64.v mword <= U64.v a)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: objects_nonempty_from_header
/// ---------------------------------------------------------------------------

private let objects_nonempty_from_header (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    read_word g1 start == read_word g2 start /\
                    Seq.length (objects start g1) > 0)
          (ensures Seq.length (objects start g2) > 0)
  = ()

/// If two heaps have the same length and the same wosize at start, and one has
/// nonempty objects at start, so does the other.
/// Nonemptiness depends on (1) start + 8 < length, and (2) next_start <= length,
/// where next_start = start + (wosize+1)*8. Both conditions transfer when length
/// and wosize match.
#push-options "--fuel 1"
private let objects_nonempty_from_wosize (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    getWosize (read_word g1 start) == getWosize (read_word g2 start) /\
                    Seq.length (objects start g1) > 0)
          (ensures Seq.length (objects start g2) > 0)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: explicit density instantiation at a given header
/// ---------------------------------------------------------------------------

private let density_at (g: heap) (start: hp_addr)
  : Lemma (requires heap_objects_dense g /\
                    U64.v start + 8 < heap_size /\
                    Seq.mem (f_address start) (objects zero_addr g) /\
                    Seq.length (objects start g) > 0)
          (ensures (let wz = getWosize (read_word g start) in
                    let next = U64.v start + ((U64.v wz + 1) * 8) in
                    next + 8 < heap_size ==>
                    (Seq.length (objects (U64.uint_to_t next) g) > 0 /\
                     Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g))))
  = ()

/// ---------------------------------------------------------------------------
/// Helper: header address separated from field positions of dst_obj
/// ---------------------------------------------------------------------------
///
/// A header address `hd` (where f_address hd is in objects) is disjoint from
/// all field positions of dst_obj. This lets us invoke copy_fields_preserves_other.

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"

private let header_separated_from_fields
  (major: heap) (dst_obj: obj_addr) (hd: hp_addr) (n: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr major) /\
      U64.v hd + U64.v mword < heap_size /\
      Seq.mem (f_address hd) (objects zero_addr major) /\
      U64.v dst_obj % 8 == 0 /\
      n > 0 /\
      U64.v (wosize_of_object dst_obj major) >= n /\
      U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size)
    (ensures
      (forall (k:nat). 0 <= k /\ k < n ==>
        (U64.v hd + 8 <= U64.v dst_obj + k * 8 \/
         U64.v dst_obj + k * 8 + 8 <= U64.v hd)))
  = f_address_spec hd;
    hd_address_spec dst_obj;
    let obj_hd = f_address hd in
    if U64.v obj_hd <= U64.v dst_obj then begin
      // obj_hd <= dst_obj means hd + 8 <= dst_obj <= dst_obj + k*8 for all k >= 0
      // First disjunct: hd + 8 <= dst_obj + k*8
      assert (U64.v hd + 8 = U64.v obj_hd);
      assert (U64.v obj_hd <= U64.v dst_obj);
      ()
    end else begin
      // obj_hd > dst_obj: use objects_separated
      objects_separated zero_addr major dst_obj obj_hd;
      wosize_of_object_spec dst_obj major;
      let wz_dst = U64.v (wosize_of_object dst_obj major) in
      assert (U64.v obj_hd > U64.v dst_obj + wz_dst * 8);
      assert (wz_dst >= n);
      // obj_hd > dst_obj + n*8
      assert (U64.v obj_hd > U64.v dst_obj + n * 8);
      // hd = obj_hd - 8, so hd >= dst_obj + n*8
      // (because obj_hd is word-aligned and > dst_obj + n*8 which is word-aligned,
      //  so obj_hd >= dst_obj + n*8 + 8, hence hd = obj_hd - 8 >= dst_obj + n*8)
      assert (U64.v hd = U64.v obj_hd - 8);
      assert (U64.v obj_hd % 8 == 0);
      assert ((U64.v dst_obj + n * 8) % 8 == 0);
      assert (U64.v obj_hd >= U64.v dst_obj + n * 8 + 8);
      assert (U64.v hd >= U64.v dst_obj + n * 8);
      // For all k < n: dst_obj + k*8 + 8 <= dst_obj + n*8 <= hd
      ()
    end

#pop-options

/// ---------------------------------------------------------------------------
/// copy_fields preserves density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"

private let copy_fields_preserves_dense
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    Seq.mem dst_obj (objects zero_addr major) /\
                    U64.v dst_obj % 8 == 0 /\
                    U64.v (wosize_of_object dst_obj major) >= n /\
                    n > 0)
          (ensures heap_objects_dense (copy_fields minor major src_obj dst_obj 0 n))
  = let major' = copy_fields minor major src_obj dst_obj 0 n in
    copy_fields_preserves_objects_aux minor major src_obj dst_obj 0 n;
    assert (objects zero_addr major' == objects zero_addr major);
    let aux (start: hp_addr)
      : Lemma
        (requires U64.v start + 8 < heap_size /\
                 Seq.mem (f_address start) (objects zero_addr major') /\
                 Seq.length (objects start major') > 0)
        (ensures (let wz = getWosize (read_word major' start) in
                  let next = U64.v start + ((U64.v wz + 1) * 8) in
                  next + 8 < heap_size ==>
                  Seq.length (objects (U64.uint_to_t next) major') > 0 /\
                  Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr major')))
      = f_address_spec start;
        wosize_of_object_spec dst_obj major;
        hd_address_spec dst_obj;
        assert (Seq.mem (f_address start) (objects zero_addr major));
        // Derive bound: dst_obj + n*8 <= heap_size from wfh_part1
        assert (U64.v (hd_address dst_obj) + 8 + U64.v (wosize_of_object dst_obj major) * 8 <= heap_size);
        assert (U64.v dst_obj + U64.v (wosize_of_object dst_obj major) * 8 <= heap_size);
        assert (U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size);
        // Prove start is separated from all field positions of dst_obj
        header_separated_from_fields major dst_obj start n;
        copy_fields_preserves_other minor major src_obj dst_obj 0 n start;
        assert (read_word major' start == read_word major start);
        objects_nonempty_from_header major' major start;
        let wz = getWosize (read_word major start) in
        let next = U64.v start + ((U64.v wz + 1) * 8) in
        if next + 8 < heap_size then begin
          let next_hp : hp_addr = U64.uint_to_t next in
          f_address_spec next_hp;
          // next_hp is also a header (from density of major)
          assert (Seq.mem (f_address next_hp) (objects zero_addr major));
          header_separated_from_fields major dst_obj next_hp n;
          copy_fields_preserves_other minor major src_obj dst_obj 0 n next_hp;
          assert (read_word major' next_hp == read_word major next_hp);
          objects_nonempty_from_header major major' next_hp
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// zero_promote_padding preserves density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"

private let zero_promote_padding_preserves_dense
  (major: heap) (dst_obj: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    Seq.mem dst_obj (objects zero_addr major))
          (ensures heap_objects_dense (zero_promote_padding major dst_obj wz))
  = let actual_wz = U64.v (wosize_of_object dst_obj major) in
    if actual_wz <= wz then
      // Noop case: identity
      zero_promote_padding_noop major dst_obj wz
    else begin
      // Write case: actual_wz > wz, so actual_wz >= wz + 1
      let major' = zero_promote_padding major dst_obj wz in
      zero_promote_padding_preserves_objects major dst_obj wz;
      assert (objects zero_addr major' == objects zero_addr major);
      let aux (start: hp_addr)
        : Lemma
          (requires U64.v start + 8 < heap_size /\
                   Seq.mem (f_address start) (objects zero_addr major') /\
                   Seq.length (objects start major') > 0)
          (ensures (let wz_s = getWosize (read_word major' start) in
                    let next = U64.v start + ((U64.v wz_s + 1) * 8) in
                    next + 8 < heap_size ==>
                    Seq.length (objects (U64.uint_to_t next) major') > 0 /\
                    Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr major')))
        = f_address_spec start;
          wosize_of_object_spec dst_obj major;
          hd_address_spec dst_obj;
          assert (Seq.mem (f_address start) (objects zero_addr major));
          wfh_part1_obj_bound major dst_obj;
          // actual_wz >= wz + 1, so header_separated_from_fields with n = wz + 1 works
          header_separated_from_fields major dst_obj start (wz + 1);
          zero_promote_padding_frame major dst_obj wz start;
          assert (read_word major' start == read_word major start);
          objects_nonempty_from_header major' major start;
          let wz_s = getWosize (read_word major start) in
          let next = U64.v start + ((U64.v wz_s + 1) * 8) in
          if next + 8 < heap_size then begin
            let next_hp : hp_addr = U64.uint_to_t next in
            f_address_spec next_hp;
            assert (Seq.mem (f_address next_hp) (objects zero_addr major));
            header_separated_from_fields major dst_obj next_hp (wz + 1);
            zero_promote_padding_frame major dst_obj wz next_hp;
            assert (read_word major' next_hp == read_word major next_hp);
            objects_nonempty_from_header major major' next_hp
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end

#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block split case density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"

private let alloc_from_block_split_dense
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    wz >= 1 /\
                    (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ bwz - wz >= 2))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    heap_objects_dense g'))
  = let hd_obj = hd_address obj in
    let hdr = read_word g hd_obj in
    let bwz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec obj g;
    assert (U64.v hd_obj + 8 + bwz * 8 <= heap_size);

    let rhn = U64.v hd_obj + (1 + wz) * 8 in
    assert (rhn + 16 <= heap_size);

    SA.alloc_from_block_split_normal g obj wz next_fp;
    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd_obj ahdr in
    let rh : hp_addr = U64.uint_to_t rhn in
    let rw = bwz - wz - 1 in
    let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
    let g2 = write_word g1 rh rhdr in
    let ron = rhn + 8 in
    let ro : hp_addr = U64.uint_to_t ron in
    let g3 = write_word g2 ro next_fp in
    assert (alloc_from_block g obj wz next_fp == (g3, U64.uint_to_t ron));
    let g' = g3 in

    AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
    AllocLemmas.make_header_getWosize (U64.uint_to_t rw) blue_bits 0UL;

    Part1.alloc_from_block_rem_in_objects_part1 g obj wz next_fp;
    let rem_obj : obj_addr = U64.uint_to_t ron in

    let aux (start: hp_addr) : Lemma
      (requires U64.v start + 8 < heap_size /\
               Seq.mem (f_address start) (objects zero_addr g') /\
               Seq.length (objects start g') > 0)
      (ensures (let wz' = getWosize (read_word g' start) in
                let next = U64.v start + ((U64.v wz' + 1) * 8) in
                next + 8 < heap_size ==>
                Seq.length (objects (U64.uint_to_t next) g') > 0 /\
                Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g')))
      = f_address_spec start;
        if start = hd_obj then begin
          // Allocated block header: wosize = wz, next = rhn = rh
          aligned_apart ro start;
          read_write_different g2 ro start next_fp;
          aligned_apart rh start;
          read_write_different g1 rh start rhdr;
          read_write_same g hd_obj ahdr;
          assert (read_word g' start == ahdr);
          if rhn + 8 < heap_size then begin
            f_address_spec rh;
            assert (f_address rh == rem_obj);
            aligned_apart ro rh;
            read_write_different g2 ro rh next_fp;
            read_write_same g1 rh rhdr;
            ()
          end
        end
        else if start = rh then begin
          // Remainder header: wosize = rw, next = hd_obj + (1+bwz)*8
          aligned_apart ro rh;
          read_write_different g2 ro rh next_fp;
          read_write_same g1 rh rhdr;
          assert (read_word g' rh == rhdr);
          let next = rhn + (rw + 1) * 8 in
          split_next_offset (U64.v hd_obj) wz bwz;
          assert (next == U64.v hd_obj + (1 + bwz) * 8);
          if next + 8 < heap_size then begin
            let next_hp : hp_addr = U64.uint_to_t next in
            let fa_next = f_address next_hp in
            f_address_spec next_hp;
            // Explicitly instantiate density of g at hd_obj
            f_address_spec hd_obj;
            assert (Seq.mem (f_address hd_obj) (objects zero_addr g));
            density_at g hd_obj;
            // density_at gives: f_address(next_hp) in objects(0, g)
            assert (Seq.mem fa_next (objects zero_addr g));
            Part1.alloc_split_old_in_new_part1 g obj wz next_fp (fa_next <: obj_addr);
            // Header at next_hp unchanged (beyond all writes)
            aligned_apart ro next_hp;
            read_write_different g2 ro next_hp next_fp;
            aligned_apart rh next_hp;
            read_write_different g1 rh next_hp rhdr;
            aligned_apart hd_obj next_hp;
            read_write_different g hd_obj next_hp ahdr;
            objects_nonempty_from_header g g' next_hp
          end
        end
        else begin
          // Other start: show header unchanged and use old density
          let fa = f_address start in
          // First handle start = ro (impossible case)
          if U64.v start = U64.v ro then begin
            // f_address(ro) = ron + 8. Show this is NOT in objects(0, g').
            assert (U64.v fa == ron + 8);
            // If fa in objects(g), objects_separated gives fa > obj + bwz*8.
            // But fa = obj + (2+wz)*8 and obj + bwz*8 >= obj + (wz+2)*8 = fa. Contradiction.
            if Seq.mem fa (objects zero_addr g) then begin
              objects_separated zero_addr g obj (fa <: obj_addr);
              wosize_of_object_spec obj g;
              assert false
            end else begin
              // fa not in objects(g). Backward: fa = rem_obj? No, ron+8 != ron.
              AllocLemmas.alloc_from_block_objects_backward_part1 g obj wz next_fp fa;
              assert false
            end
          end else begin
            // start != hd_obj, start != rh, start != ro → header unchanged
            aligned_apart ro start;
            aligned_apart ro start;
            read_write_different g2 ro start next_fp;
            aligned_apart rh start;
            read_write_different g1 rh start rhdr;
            aligned_apart hd_obj start;
            read_write_different g hd_obj start ahdr;
            assert (read_word g' start == read_word g start);
            // fa must be in objects(0, g)
            if not (Seq.mem fa (objects zero_addr g)) then begin
              AllocLemmas.alloc_from_block_objects_backward_part1 g obj wz next_fp fa;
              f_address_spec rh;
              // backward says fa = rem_obj = f_address rh, so U64.v fa = ron
              // f_address start = start + 8 = U64.v fa, so start = U64.v fa - 8 = ron - 8 = rhn = rh
              // But start != rh. Contradiction.
              assert false
            end else ();
            objects_nonempty_from_header g' g start;
            let wz' = getWosize (read_word g start) in
            let next = U64.v start + ((U64.v wz' + 1) * 8) in
            if next + 8 < heap_size then begin
              let next_hp : hp_addr = U64.uint_to_t next in
              let fa_next = f_address next_hp in
              f_address_spec next_hp;
              // fa_next in objects(g) from density
              assert (Seq.mem fa_next (objects zero_addr g));
              Part1.alloc_split_old_in_new_part1 g obj wz next_fp (fa_next <: obj_addr);
              // Header at next_hp
              if next_hp = hd_obj then begin
                aligned_apart ro next_hp;
                aligned_apart ro next_hp;
                read_write_different g2 ro next_hp next_fp;
                aligned_apart rh next_hp;
                read_write_different g1 rh next_hp rhdr;
                read_write_same g hd_obj ahdr;
                ()
              end else if next_hp = rh then begin
                aligned_apart ro next_hp;
                aligned_apart ro next_hp;
                read_write_different g2 ro next_hp next_fp;
                read_write_same g1 rh rhdr;
                ()
              end else if U64.v next_hp = U64.v ro then begin
                // next_hp = ro. f_address(ro) = ron + 8. This should be in objects(g).
                // But objects_separated obj (f_address ro) gives contradiction.
                f_address_spec next_hp;
                assert (U64.v fa_next == ron + 8);
                objects_separated zero_addr g obj (fa_next <: obj_addr);
                wosize_of_object_spec obj g;
                assert false
              end else begin
                aligned_apart ro next_hp;
                aligned_apart ro next_hp;
                read_write_different g2 ro next_hp next_fp;
                aligned_apart rh next_hp;
                read_write_different g1 rh next_hp rhdr;
                aligned_apart hd_obj next_hp;
                read_write_different g hd_obj next_hp ahdr;
                objects_nonempty_from_header g g' next_hp
              end
            end
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block exact case density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"

private let alloc_from_block_exact_dense
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    wz >= 1 /\
                    (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ bwz - wz < 2))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    heap_objects_dense g'))
  = let (g', _) = alloc_from_block g obj wz next_fp in
    AllocProps.alloc_from_block_exact_objects_eq_part1 g obj wz next_fp;
    let hdr = read_word g (hd_address obj) in
    let bwz = U64.v (getWosize hdr) in
    SA.alloc_from_block_exact g obj wz next_fp;
    hd_address_spec obj;
    hd_address_bounds obj;
    let ahdr = make_header (U64.uint_to_t bwz) white_bits 0UL in
    AllocLemmas.make_header_getWosize (U64.uint_to_t bwz) white_bits 0UL;
    // All wosizes preserved (only hd_address(obj) written, same wosize)
    let hd_obj = hd_address obj in
    let aux_wz (p: hp_addr) : Lemma (getWosize (read_word g' p) == getWosize (read_word g p))
      = if p = hd_obj then begin
          read_write_same g hd_obj ahdr
        end else begin
          aligned_apart hd_obj p;
          read_write_different g hd_obj p ahdr
        end
    in
    FStar.Classical.forall_intro aux_wz;
    // Transfer density directly
    let aux (start: hp_addr)
      : Lemma
        (requires U64.v start + 8 < heap_size /\
                 Seq.mem (f_address start) (objects zero_addr g') /\
                 Seq.length (objects start g') > 0)
        (ensures (let wz' = getWosize (read_word g' start) in
                  let next = U64.v start + ((U64.v wz' + 1) * 8) in
                  next + 8 < heap_size ==>
                  Seq.length (objects (U64.uint_to_t next) g') > 0 /\
                  Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g')))
      = aux_wz start;
        // objects are equal, so membership in g' = membership in g
        assert (Seq.mem (f_address start) (objects zero_addr g));
        if start = hd_obj then begin
          // getWosize preserved, use density_at on g
          density_at g hd_obj;
          let wz' = getWosize (read_word g start) in
          let next = U64.v start + ((U64.v wz' + 1) * 8) in
          if next + 8 < heap_size then begin
            let next_hp : hp_addr = U64.uint_to_t next in
            aligned_apart hd_obj next_hp;
            read_write_different g hd_obj next_hp ahdr;
            objects_nonempty_from_header g g' next_hp
          end
        end else begin
          aligned_apart hd_obj start;
          read_write_different g hd_obj start ahdr;
          objects_nonempty_from_header g' g start;
          let wz' = getWosize (read_word g start) in
          let next = U64.v start + ((U64.v wz' + 1) * 8) in
          if next + 8 < heap_size then begin
            let next_hp : hp_addr = U64.uint_to_t next in
            aux_wz next_hp;
            if next_hp = hd_obj then
              density_at g hd_obj
            else begin
              aligned_apart hd_obj next_hp;
              read_write_different g hd_obj next_hp ahdr;
              objects_nonempty_from_header g g' next_hp
            end
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block preserves density (combine exact + split)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

private let alloc_from_block_preserves_dense
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    wz >= 1 /\
                    U64.v (getWosize (read_word g (hd_address obj))) >= wz)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    heap_objects_dense g'))
  = let hdr = read_word g (hd_address obj) in
    let bwz = U64.v (getWosize hdr) in
    if bwz - wz < 2 then
      alloc_from_block_exact_dense g obj wz next_fp
    else
      alloc_from_block_split_dense g obj wz next_fp

#pop-options

/// ---------------------------------------------------------------------------
/// Write at a field position preserves density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"

private let write_field_preserves_dense
  (g: heap) (obj: obj_addr) (v: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v (wosize_of_object obj g) >= 1)
          (ensures heap_objects_dense (write_word g obj v))
  = let g' = write_word g obj v in
    // Writing at obj (first field) preserves objects
    wosize_of_object_spec obj g;
    write_word_preserves_objects_part1 g obj obj v;
    assert (objects zero_addr g' == objects zero_addr g);
    // For any header start: show header unchanged
    let aux (start: hp_addr) : Lemma
      (requires U64.v start + 8 < heap_size /\
               Seq.mem (f_address start) (objects zero_addr g') /\
               Seq.length (objects start g') > 0)
      (ensures (let wz' = getWosize (read_word g' start) in
                let next = U64.v start + ((U64.v wz' + 1) * 8) in
                next + 8 < heap_size ==>
                Seq.length (objects (U64.uint_to_t next) g') > 0 /\
                Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g')))
      = f_address_spec start;
        assert (Seq.mem (f_address start) (objects zero_addr g));
        // start is a header. obj is an object with wosize >= 1.
        // f_address(start) in objects means start+8 is an obj_addr in objects.
        // If start = obj: then f_address(start) = obj + 8. But obj is in objects
        // with wosize >= 1, so objects_separated gives obj+8 > obj + wosize(obj)*8
        // which means 8 > wosize(obj)*8 >= 8. Contradiction. So start ≠ obj.
        if start = obj then begin
          // f_address(obj) = obj + 8. Both obj and obj+8 would be in objects.
          objects_separated zero_addr g obj (f_address start);
          wosize_of_object_spec obj g;
          // This gives obj+8 > obj + wosize(obj)*8 >= obj + 8. False.
          assert false
        end else begin
          read_write_different g obj start v;
          assert (read_word g' start == read_word g start);
          objects_nonempty_from_header g' g start;
          let wz' = getWosize (read_word g start) in
          let next = U64.v start + ((U64.v wz' + 1) * 8) in
          if next + 8 < heap_size then begin
            let next_hp : hp_addr = U64.uint_to_t next in
            if next_hp = obj then begin
              // next_hp = obj → f_address(obj) = obj+8 in objects.
              // Same contradiction as above.
              f_address_spec next_hp;
              objects_separated zero_addr g obj (f_address next_hp);
              wosize_of_object_spec obj g;
              assert false
            end else begin
              read_write_different g obj next_hp v;
              objects_nonempty_from_header g g' next_hp
            end
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// Helper: prev≠0 found case density proof (low fuel)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// Factored helper: in the split case, prev_fp stays in objects after alloc_from_block.
/// Separated into its own function to keep the VC context small.
private let alloc_split_prev_mem
  (g: heap) (obj: obj_addr) (prev_fp: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    Seq.mem prev_fp (objects zero_addr g) /\
                    (let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
                     bwz >= wz /\ bwz - wz >= 2))
          (ensures (let (g_alloc, _) = alloc_from_block g obj wz next_fp in
                    Seq.mem prev_fp (objects zero_addr g_alloc)))
  = Part1.alloc_split_old_in_new_part1 g obj wz next_fp prev_fp

#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"

/// When alloc_search finds a block (bwz >= wz) and prev ≠ 0, the result is
/// write_word (alloc_from_block g obj wz next) prev new_fp. Prove density.
private let alloc_search_found_prev_dense
  (g: heap) (obj: obj_addr) (prev_fp: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    Seq.mem prev_fp (objects zero_addr g) /\
                    prev_fp <> obj /\
                    wz >= 1 /\
                    U64.v (wosize_of_object prev_fp g) >= 1 /\
                    (let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
                     bwz >= wz))
          (ensures (let (g_alloc, new_fp_out) = alloc_from_block g obj wz next_fp in
                    heap_objects_dense (write_word g_alloc prev_fp new_fp_out)))
  = let (g_alloc, new_fp_out) = alloc_from_block g obj wz next_fp in
    alloc_from_block_preserves_dense g obj wz next_fp;
    Part2.alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
    // Prove prev_fp membership in g_alloc (exact vs split)
    let bwz_obj = U64.v (getWosize (read_word g (hd_address obj))) in
    (if bwz_obj - wz < 2 then
      AllocProps.alloc_from_block_exact_objects_eq_part1 g obj wz next_fp
    else begin
      assert (bwz_obj >= wz);
      assert (bwz_obj - wz >= 2);
      assert ((let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
               bwz >= wz /\ bwz - wz >= 2));
      alloc_split_prev_mem g obj prev_fp wz next_fp
    end);
    assert (Seq.mem prev_fp (objects zero_addr g_alloc));
    // prev ≠ obj, so hd_prev ≠ hd_obj
    hd_address_spec prev_fp;
    hd_address_spec obj;
    hd_address_bounds obj;
    let hd_prev : hp_addr = hd_address prev_fp in
    let hd_obj : hp_addr = hd_address obj in
    assert (hd_prev <> hd_obj);
    let hdr_obj = read_word g hd_obj in
    let bwz_obj = U64.v (getWosize hdr_obj) in
    if bwz_obj - wz < 2 then begin
      // Exact case: only hd_obj written
      SA.alloc_from_block_exact g obj wz next_fp;
      read_write_different g hd_obj hd_prev
        (make_header (U64.uint_to_t bwz_obj) white_bits 0UL);
      wosize_of_object_spec prev_fp g;
      wosize_of_object_spec prev_fp g_alloc;
      write_field_preserves_dense g_alloc prev_fp new_fp_out
    end else begin
      // Split case: 3 writes within obj's span
      wosize_of_object_spec obj g;
      assert (U64.v hd_obj + 8 + bwz_obj * 8 <= heap_size);
      // bwz_obj >= wz + 2, so hd_obj + (1+wz)*8 + 16 <= heap_size
      assert (U64.v hd_obj + (1 + wz) * 8 < heap_size);
      assert (U64.v hd_obj + (1 + wz) * 8 + 8 < heap_size);
      SA.alloc_from_block_split_normal g obj wz next_fp;
      let rhn = U64.v hd_obj + (1 + wz) * 8 in
      let rh : hp_addr = U64.uint_to_t rhn in
      let ron = rhn + 8 in
      let ro : hp_addr = U64.uint_to_t ron in
      // prev's header outside obj's entire span
      if U64.v prev_fp < U64.v obj then begin
        objects_separated zero_addr g prev_fp obj;
        assert (U64.v hd_prev < U64.v hd_obj)
      end else begin
        objects_separated zero_addr g obj prev_fp;
        assert (U64.v (prev_fp <: obj_addr) > U64.v obj + bwz_obj * 8);
        assert (U64.v hd_prev > U64.v obj + bwz_obj * 8 - 8);
        assert (rhn <= U64.v obj + bwz_obj * 8 - 8)
      end;
      let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
      let g1 = write_word g hd_obj ahdr in
      let rw = bwz_obj - wz - 1 in
      let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
      let g2 = write_word g1 rh rhdr in
      aligned_apart hd_obj hd_prev;
      read_write_different g hd_obj hd_prev ahdr;
      aligned_apart rh hd_prev;
      read_write_different g1 rh hd_prev rhdr;
      aligned_apart ro hd_prev;
      read_write_different g2 ro hd_prev next_fp;
      assert (read_word g_alloc hd_prev == read_word g hd_prev);
      wosize_of_object_spec prev_fp g;
      wosize_of_object_spec prev_fp g_alloc;
      write_field_preserves_dense g_alloc prev_fp new_fp_out
    end

#pop-options

/// ---------------------------------------------------------------------------
/// alloc_spec preserves density (induction on alloc_search)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 600 --fuel 4 --ifuel 1"

private let rec alloc_search_preserves_dense
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
             heap_objects_dense g /\
             AllocLemmas.fl_valid g cur_fp fuel /\
             AllocLemmas.fl_chain_terminates g cur_fp fuel /\
             wz >= 1 /\
             (prev_fp <> 0UL ==>
               (prev_fp <> cur_fp /\
                U64.v prev_fp >= U64.v mword /\
                U64.v prev_fp < heap_size /\
                U64.v prev_fp % U64.v mword == 0 /\
                Seq.mem (prev_fp <: obj_addr) (objects zero_addr g) /\
                U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
    (ensures heap_objects_dense (alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)
    (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      hd_address_spec obj;
      hd_address_bounds obj;
      let hdr = read_word g hd in
      let bwz = U64.v (getWosize hdr) in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      if bwz >= wz then begin
        // Found a block that fits. alloc_from_block preserves density.
        // Case: prev = 0 (head of list)
        if prev_fp = 0UL then begin
          SA.alloc_search_found_head g head_fp prev_fp cur_fp wz fuel;
          alloc_from_block_preserves_dense g obj wz next_fp
        end else begin
          // prev != 0: use helper
          SA.alloc_search_found_prev g head_fp prev_fp cur_fp wz fuel;
          alloc_search_found_prev_dense g obj (prev_fp <: obj_addr) wz next_fp
        end
      end else begin
        // Block too small, advance to next
        if U64.v hd + 16 <= heap_size then begin
          AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
          AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
          AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
          assert (Seq.mem (cur_fp <: obj_addr) (objects zero_addr g));
          assert (U64.v (wosize_of_object (cur_fp <: obj_addr) g) >= 1);
          assert (AllocLemmas.fl_valid g next_fp (fuel - 1));
          assert (AllocLemmas.fl_chain_terminates g next_fp (fuel - 1) = true);
          // fl_valid_elim gives read_word g obj ≠ obj, i.e. next_fp ≠ cur_fp
          assert (next_fp <> cur_fp);
          alloc_search_preserves_dense g head_fp cur_fp next_fp wz (fuel - 1)
        end else ()
      end
    end

#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let alloc_spec_preserves_dense_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words)
          (ensures (let r = alloc_spec g fp requested_wz in
                    heap_objects_dense r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_dense g fp 0UL fp wz heap_words

#pop-options

/// ---------------------------------------------------------------------------
/// set_promoted_tag preserves density
/// ---------------------------------------------------------------------------
///
/// set_promoted_tag writes one header word with the same wosize.
/// Density depends only on wosize at each header position, so is preserved.

#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"

private let set_promoted_tag_preserves_dense
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    Seq.mem obj (objects zero_addr major))
          (ensures heap_objects_dense (set_promoted_tag major obj tag))
  = let g' = set_promoted_tag major obj tag in
    set_promoted_tag_preserves_objects major obj tag;
    assert (objects zero_addr g' == objects zero_addr major);
    set_promoted_tag_unfold major obj tag;
    let hd_obj = hd_address obj in
    hd_address_spec obj;
    let hdr = read_word major hd_obj in
    let wz = getWosize hdr in
    getWosize_bound hdr;
    let new_hdr = makeHeader wz White (U64.uint_to_t tag) in
    makeHeader_getWosize wz White (U64.uint_to_t tag);
    // Key fact: g' has same length as major (write_word preserves length)
    assert (Seq.length g' == Seq.length major);
    // For every header position, wosize is unchanged, so density transfers
    let aux (start: hp_addr)
      : Lemma
        (requires U64.v start + 8 < heap_size /\
                 Seq.mem (f_address start) (objects zero_addr g') /\
                 Seq.length (objects start g') > 0)
        (ensures (let wz' = getWosize (read_word g' start) in
                  let next = U64.v start + ((U64.v wz' + 1) * 8) in
                  next + 8 < heap_size ==>
                  Seq.length (objects (U64.uint_to_t next) g') > 0 /\
                  Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr g')))
      = assert (Seq.mem (f_address start) (objects zero_addr major));
        // Show wosize at start is the same in both heaps
        if start = hd_obj then begin
          read_write_same major hd_obj new_hdr;
          assert (getWosize (read_word g' start) == wz);
          assert (getWosize (read_word g' start) == getWosize (read_word major start));
          // objects at start has same structure → nonempty in major too
          objects_nonempty_from_wosize g' major start
        end else begin
          read_write_different major hd_obj start new_hdr;
          assert (read_word g' start == read_word major start);
          objects_nonempty_from_header g' major start
        end;
        assert (Seq.length (objects start major) > 0);
        // Now getWosize is the same, so next is the same in both heaps
        let wz_major = getWosize (read_word major start) in
        assert (getWosize (read_word g' start) == wz_major);
        let next = U64.v start + ((U64.v wz_major + 1) * 8) in
        if next + 8 < heap_size then begin
          let next_hp : hp_addr = U64.uint_to_t next in
          // From density of major: objects at next_hp is nonempty and in objects zero_addr major
          assert (Seq.mem (f_address next_hp) (objects zero_addr major));
          assert (Seq.length (objects next_hp major) > 0);
          // Since objects zero_addr g' == objects zero_addr major, membership transfers
          // For nonempty: transfer via header/wosize equality
          if next_hp = hd_obj then begin
            read_write_same major hd_obj new_hdr;
            objects_nonempty_from_wosize major g' next_hp
          end else begin
            read_write_different major hd_obj next_hp new_hdr;
            objects_nonempty_from_header major g' next_hp
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// promote_object preserves density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"

let promote_object_preserves_dense
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = promote_object minor major obj fp wz in
                    heap_objects_dense res.major_out))
  = let alloc_res = alloc_spec major fp wz in
    if alloc_res.obj_out = 0UL then
      promote_object_oom minor major obj fp wz
    else begin
      alloc_spec_preserves_dense_part1 major fp wz;
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
      AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
      AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
      promote_object_success minor major obj fp wz;
      let dst_obj : obj_addr = alloc_res.obj_out in
      // Step 1: copy_fields preserves density
      copy_fields_preserves_dense minor alloc_res.heap_out obj dst_obj wz;
      // Step 2: zero_promote_padding preserves density
      let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
      let padded = zero_promote_padding copied dst_obj wz in
      let tag = minor_tag minor obj in
      minor_tag_bound minor obj;
      copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
      copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
      assert (Seq.mem dst_obj (objects zero_addr copied));
      wfh_part1_obj_bound copied dst_obj;
      AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
      zero_promote_padding_preserves_dense copied dst_obj wz;
      zero_promote_padding_preserves_wfh_part1 copied dst_obj wz;
      zero_promote_padding_preserves_objects copied dst_obj wz;
      assert (Seq.mem dst_obj (objects zero_addr padded));
      // Step 3: set_promoted_tag preserves density
      set_promoted_tag_preserves_dense padded dst_obj tag
    end

#pop-options
