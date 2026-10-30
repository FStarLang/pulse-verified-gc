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
module AD = GC.Spec.Allocator.Dense
module SA = GC.Spec.Allocator
module Part1 = GC.Spec.Allocator.Lemmas.Part1
module Part2 = GC.Spec.Allocator.Lemmas.Part2


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
/// Helper: header address separated from field positions of dst_obj
/// ---------------------------------------------------------------------------
///
/// A header address `hd` (where f_address hd is in objects) is disjoint from
/// all field positions of dst_obj. This lets us invoke copy_fields_preserves_other.

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

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

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

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
  = reveal_opaque (`%heap_objects_dense) heap_objects_dense;
    let major' = copy_fields minor major src_obj dst_obj 0 n in
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
        AD.objects_nonempty_from_header major' major start;
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
          AD.objects_nonempty_from_header major major' next_hp
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// set_promoted_tag preserves density
/// ---------------------------------------------------------------------------
///
/// set_promoted_tag writes one header word with the same wosize.
/// Density depends only on wosize at each header position, so is preserved.

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let set_promoted_tag_preserves_dense
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    Seq.mem obj (objects zero_addr major))
          (ensures heap_objects_dense (set_promoted_tag major obj tag))
  = reveal_opaque (`%heap_objects_dense) heap_objects_dense;
    let g' = set_promoted_tag major obj tag in
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
          AD.objects_nonempty_from_header g' major start
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
            AD.objects_nonempty_from_header major g' next_hp
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// promote_object preserves density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"

let promote_object_preserves_dense
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  = let alloc_res = alloc_spec major fp wz 0UL in
    if alloc_res.obj_out = 0UL then
      promote_object_oom minor major obj fp wz
    else begin
      AD.alloc_spec_preserves_dense_part1 major fp wz 0UL;
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz 0UL;
      AllocProps.alloc_spec_obj_in_objects_part1 major fp wz 0UL;
      AllocProps.alloc_spec_obj_wosize_part1 major fp wz 0UL;
      promote_object_success minor major obj fp wz;
      let dst_obj : obj_addr = alloc_res.obj_out in
      // Step 1: copy_fields preserves density
      copy_fields_preserves_dense minor alloc_res.heap_out obj dst_obj wz;
      let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
      let tag = minor_tag minor obj in
      minor_tag_bound minor obj;
      copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
      copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
      assert (Seq.mem dst_obj (objects zero_addr copied));
      // Step 2: set_promoted_tag preserves density
      set_promoted_tag_preserves_dense copied dst_obj tag
    end

#pop-options
