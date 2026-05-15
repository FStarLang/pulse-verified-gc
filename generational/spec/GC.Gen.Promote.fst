/// ---------------------------------------------------------------------------
/// GC.Gen.Promote — Implementation of minor→major promotion spec
/// ---------------------------------------------------------------------------

module GC.Gen.Promote

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

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas
module AllocHeaderLemmas = GC.Spec.Allocator.Lemmas.Header
module AllocProps = GC.Gen.AllocProps

open GC.Lib.Header

/// ---------------------------------------------------------------------------
/// Promote a single object: copy fields from minor to major
/// ---------------------------------------------------------------------------

/// copy_fields, copy_fields_base, copy_fields_step are provided by
/// GC.Gen.WriteBodyLemmas (opened via the .fsti).

/// ---------------------------------------------------------------------------
/// copy_fields correctness lemmas
/// ---------------------------------------------------------------------------

/// copy_fields_preserves_other is provided by GC.Gen.WriteBodyLemmas (opened via .fsti).

/// After copy_fields from index i to n, reading field j (with i <= j < n) at
/// address dst + j*8 returns minor_read_field minor src j.
#push-options "--z3rlimit 20 --fuel 2"
let rec copy_fields_preserves
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat) (j: nat)
  : Lemma
    (requires
      i <= j /\ j < n /\
      U64.v dst_obj % 8 == 0 /\
      U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size)
    (ensures
      (let result = copy_fields minor major src_obj dst_obj i n in
       let addr_nat = U64.v dst_obj + j * 8 in
       addr_nat + 8 <= heap_size /\
       addr_nat % 8 == 0 /\
       read_word result (U64.uint_to_t addr_nat) == minor_read_field minor src_obj j))
    (decreases (n - i))
  = let field_val = minor_read_field minor src_obj i in
    let dst_offset = U64.v dst_obj + i * 8 in
    assert (dst_offset + 8 <= heap_size);
    assert (dst_offset % 8 == 0);
    let dst_addr : hp_addr = U64.uint_to_t dst_offset in
    let major' = write_word major dst_addr field_val in
    if j = i then begin
      // Field j was just written at dst_addr
      read_write_same major dst_addr field_val;
      // The recursive call writes at dst + k*8 for k = i+1,...,n-1
      // None of these overlap with dst_addr (they are all strictly greater)
      copy_fields_preserves_other minor major' src_obj dst_obj (i + 1) n dst_addr
    end else begin
      // j > i, so field j is written by the recursive call; apply IH
      copy_fields_preserves minor major' src_obj dst_obj (i + 1) n j
    end
#pop-options

let promote_object_oom (minor: minor_state) (major: heap) (obj: U64.t)
                       (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out == 0UL)
          (ensures (let res = promote_object minor major obj fp wosize in
                    res.major_out == major /\ res.fp_out == fp /\ res.new_addr == 0UL)) = ()

let promote_object_success (minor: minor_state) (major: heap) (obj: U64.t)
                           (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out <> 0UL)
          (ensures (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
                    let res = promote_object minor major obj fp wosize in
                    let copied = copy_fields minor alloc_res.heap_out obj alloc_res.obj_out 0 wosize in
                    let cleaned = clean_promote_leftover copied alloc_res.obj_out wosize in
                    let tag = minor_tag minor obj in
                    res.major_out == set_promoted_tag cleaned alloc_res.obj_out tag /\
                    res.fp_out == alloc_res.fp_out /\
                    res.new_addr == alloc_res.obj_out)) = ()

let set_promoted_tag_unfold
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (set_promoted_tag major obj tag ==
           write_word major (hd_address obj)
             (makeHeader (getWosize (read_word major (hd_address obj)))
                         White (U64.uint_to_t tag))) = ()

/// ---------------------------------------------------------------------------
/// clean_promote_leftover lemma proofs
/// ---------------------------------------------------------------------------

/// Helper: unfold clean_promote_leftover for a valid obj_addr
private let clean_promote_leftover_unfold (g: heap) (obj: obj_addr) (wz: nat)
  : Lemma (let hdr = read_word g (hd_address obj) in
           let block_wz = U64.v (getWosize hdr) in
           let extra_off = U64.v obj + wz * U64.v mword in
           if block_wz > wz && extra_off + U64.v mword <= heap_size then
             (FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
              clean_promote_leftover g obj wz ==
                write_word g (U64.uint_to_t extra_off <: hp_addr) 0UL)
           else
             clean_promote_leftover g obj wz == g)
  = ()

let clean_promote_leftover_read_frame
  (g: heap) (obj: obj_addr) (wz: nat) (addr: hp_addr)
  : Lemma (requires U64.v addr <> U64.v obj + wz * U64.v mword \/
                    U64.v (getWosize (read_word g (hd_address obj))) <= wz)
          (ensures read_word (clean_promote_leftover g obj wz) addr == read_word g addr)
  = clean_promote_leftover_unfold g obj wz;
    let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let extra_off = U64.v obj + wz * U64.v mword in
    if block_wz > wz && extra_off + U64.v mword <= heap_size then begin
      FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
      let eaddr : hp_addr = U64.uint_to_t extra_off in
      read_write_different g eaddr addr 0UL
    end

let clean_promote_leftover_preserves_header
  (g: heap) (obj: obj_addr) (wz: nat{wz > 0})
  : Lemma (read_word (clean_promote_leftover g obj wz) (hd_address obj) ==
           read_word g (hd_address obj))
  = hd_address_spec obj;
    // hd_address obj = obj - 8, extra field at obj + wz*8 with wz >= 1
    // so extra_off >= obj + 8 > obj - 8 = hd_address obj
    clean_promote_leftover_read_frame g obj wz (hd_address obj)

let clean_promote_leftover_preserves_objects
  (g: heap) (obj: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 g /\ Seq.mem obj (objects zero_addr g))
          (ensures objects zero_addr (clean_promote_leftover g obj wz) == objects zero_addr g)
  = clean_promote_leftover_unfold g obj wz;
    let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let extra_off = U64.v obj + wz * U64.v mword in
    if block_wz > wz && extra_off + U64.v mword <= heap_size then begin
      FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
      let eaddr : hp_addr = U64.uint_to_t extra_off in
      // extra field is within obj's body: obj <= eaddr < obj + wosize*8
      assert (U64.v eaddr >= U64.v obj);
      wfh_part1_obj_bound g obj;
      wosize_of_object_spec obj g;
      // wz < block_wz = wosize_of_object obj g, so eaddr < obj + wosize*8
      FStar.Math.Lemmas.lemma_mult_lt_right (U64.v mword) wz (U64.v (wosize_of_object obj g));
      write_word_preserves_objects_part1 g obj eaddr 0UL
    end

/// ---------------------------------------------------------------------------
/// clean_promote_leftover preserves allocator invariants
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let clean_promote_leftover_preserves_alloc_invariants
  (g: heap) (obj: obj_addr) (wz: nat{wz > 0}) (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 g /\
             Seq.mem obj (objects zero_addr g) /\
             AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates g fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids g fp obj (heap_size / U64.v mword) = true)
          (ensures (let g' = clean_promote_leftover g obj wz in
                    well_formed_heap_part1 g' /\
                    AllocLemmas.fl_valid g' fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g' fp (heap_size / U64.v mword)))
  = clean_promote_leftover_unfold g obj wz;
    let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let extra_off = U64.v obj + wz * U64.v mword in
    let fuel = heap_size / U64.v mword in
    if block_wz > wz && extra_off + U64.v mword <= heap_size then begin
      FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
      let eaddr : hp_addr = U64.uint_to_t extra_off in
      // The extra field is a body word of obj: obj <= eaddr < obj + wosize*8
      wfh_part1_obj_bound g obj;
      wosize_of_object_spec obj g;
      FStar.Math.Lemmas.lemma_mult_lt_right (U64.v mword) wz (U64.v (wosize_of_object obj g));
      assert (U64.v eaddr >= U64.v obj);
      assert (U64.v eaddr < U64.v obj + (U64.v (wosize_of_object obj g) * 8));
      // chain_avoids implies not_in_fl_chain
      WriteBody.chain_avoids_implies_not_in_fl_chain g fp obj fuel;
      // Use write_body lemmas for fl_valid and fl_chain_terminates
      WriteBody.write_body_preserves_fl_valid_aux g obj eaddr 0UL fp fuel;
      WriteBody.write_body_preserves_fl_chain_terminates g obj eaddr 0UL fp fuel;
      // wfh_part1 is preserved since objects are unchanged and headers are unchanged
      write_word_preserves_objects_part1 g obj eaddr 0UL;
      let g' = write_word g eaddr 0UL in
      // All headers unchanged → wfh_part1 preserved
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects 0UL g'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h g') * 8) <= Seq.length g')
      = assert (Seq.mem h (objects 0UL g));
        hd_address_spec h;
        if h = obj then begin
          // eaddr is in obj's body, not at header → header unchanged
          read_write_different g eaddr (hd_address h) 0UL;
          wosize_of_object_spec h g';
          wosize_of_object_spec h g
        end else begin
          // h != obj: show eaddr and hd_address h are separated
          // eaddr is in obj's body: obj <= eaddr < obj + block_wz*8
          // hd_address h = h - 8, and h is a different object
          if U64.v h > U64.v obj then begin
            objects_separated 0UL g obj h;
            // obj + (wosize obj)*8 + 8 <= h, so obj + (wosize obj)*8 <= h - 8 = hd_address h
            // eaddr = obj + wz*8 < obj + block_wz*8 = obj + (wosize obj)*8 <= hd_address h
            assert (U64.v eaddr + U64.v mword <= U64.v (hd_address h))
          end else begin
            // h < obj: hd_address h = h - 8 < h <= obj - (wosize_prev)*8 - 8
            // so hd_address h + 8 <= h < obj <= eaddr
            assert (U64.v (hd_address h) + U64.v mword <= U64.v eaddr)
          end;
          read_write_different g eaddr (hd_address h) 0UL;
          wosize_of_object_spec h g';
          wosize_of_object_spec h g
        end
      in
      Classical.forall_intro (Classical.move_requires aux)
    end
#pop-options

/// clean_promote_leftover preserves chain_avoids for dst_obj
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let clean_promote_leftover_preserves_chain_avoids
  (g: heap) (obj: obj_addr) (wz: nat{wz > 0}) (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 g /\
             Seq.mem obj (objects zero_addr g) /\
             AllocLemmas.fl_valid g fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids g fp obj (heap_size / U64.v mword) = true)
          (ensures AllocLemmas.chain_avoids (clean_promote_leftover g obj wz)
                     fp obj (heap_size / U64.v mword) = true)
  = clean_promote_leftover_unfold g obj wz;
    let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let extra_off = U64.v obj + wz * U64.v mword in
    let fuel = heap_size / U64.v mword in
    if block_wz > wz && extra_off + U64.v mword <= heap_size then begin
      FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
      let eaddr : hp_addr = U64.uint_to_t extra_off in
      wfh_part1_obj_bound g obj;
      wosize_of_object_spec obj g;
      FStar.Math.Lemmas.lemma_mult_lt_right (U64.v mword) wz (U64.v (wosize_of_object obj g));
      WriteBody.write_body_preserves_chain_avoids_self g obj eaddr 0UL fp fuel
    end
#pop-options

let clean_promote_leftover_zeroes_extra
  (g: heap) (obj: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires
             U64.v (getWosize (read_word g (hd_address obj))) > wz /\
             U64.v obj + wz * U64.v mword + U64.v mword <= heap_size)
          (ensures (let extra_addr : hp_addr =
                      (FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
                       U64.uint_to_t (U64.v obj + wz * U64.v mword)) in
                    read_word (clean_promote_leftover g obj wz) extra_addr == 0UL))
  = clean_promote_leftover_unfold g obj wz;
    FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
    let eaddr : hp_addr = U64.uint_to_t (U64.v obj + wz * U64.v mword) in
    read_write_same g eaddr 0UL

let clean_promote_leftover_is_write
  (g: heap) (obj: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires
             U64.v (getWosize (read_word g (hd_address obj))) > wz /\
             U64.v obj + wz * U64.v mword + U64.v mword <= heap_size)
          (ensures (let extra_addr : hp_addr =
                      (FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
                       U64.uint_to_t (U64.v obj + wz * U64.v mword)) in
                    clean_promote_leftover g obj wz == write_word g extra_addr 0UL))
  = clean_promote_leftover_unfold g obj wz;
    FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword)

let clean_promote_leftover_noop
  (g: heap) (obj: obj_addr) (wz: nat)
  : Lemma (requires U64.v (getWosize (read_word g (hd_address obj))) <= wz)
          (ensures clean_promote_leftover g obj wz == g)
  = ()

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let clean_promote_leftover_preserves_wfh_part4
  (g: heap) (obj: obj_addr) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part4 g /\
                     Seq.mem obj (objects zero_addr g))
          (ensures well_formed_heap_part4 (clean_promote_leftover g obj wz))
  = clean_promote_leftover_unfold g obj wz;
    let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let extra_off = U64.v obj + wz * U64.v mword in
    if block_wz > wz && extra_off + U64.v mword <= heap_size then begin
      FStar.Math.Lemmas.lemma_mod_plus (U64.v obj) wz (U64.v mword);
      let eaddr : hp_addr = U64.uint_to_t extra_off in
      let g' = write_word g eaddr 0UL in
      wfh_part1_obj_bound g obj;
      wosize_of_object_spec obj g;
      FStar.Math.Lemmas.lemma_mult_lt_right (U64.v mword) wz block_wz;
      write_word_preserves_objects_part1 g obj eaddr 0UL;
      assert (objects zero_addr g' == objects zero_addr g);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(GC.Spec.Object.is_infix h g'))
      = assert (Seq.mem h (objects zero_addr g));
        GC.Spec.Object.is_infix_spec h g';
        GC.Spec.Object.is_infix_spec h g;
        GC.Spec.Object.tag_of_object_spec h g';
        GC.Spec.Object.tag_of_object_spec h g;
        hd_address_spec h;
        if h = obj then begin
          // hd_address h = obj - 8. eaddr = obj + wz*8 >= obj + 8.
          // So hd_address h + 8 <= obj <= eaddr.
          FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) 1 wz;
          read_write_different g eaddr (hd_address h) 0UL
        end else begin
          if U64.v h > U64.v obj then begin
            objects_separated 0UL g obj h;
            // h > obj + block_wz*8, hd_address h = h - 8 >= obj + block_wz*8
            // eaddr = obj + wz*8 < obj + block_wz*8 (wz < block_wz)
            // So eaddr + 8 <= obj + block_wz*8 + 8 <= h, 
            // and eaddr < obj + block_wz*8 <= hd_address h
            assert (U64.v eaddr + U64.v mword <= U64.v (hd_address h))
          end else begin
            // h < obj: hd_address h = h - 8 < h < obj <= eaddr
            assert (U64.v (hd_address h) + U64.v mword <= U64.v eaddr)
          end;
          read_write_different g eaddr (hd_address h) 0UL
        end
      in
      Classical.forall_intro (Classical.move_requires aux)
    end
#pop-options

/// Helper: set_promoted_tag preserves objects (header rewrite with same wosize)
let set_promoted_tag_preserves_objects
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires Seq.mem obj (objects zero_addr major))
          (ensures objects zero_addr (set_promoted_tag major obj tag) == objects zero_addr major)
  = let hd = hd_address obj in
    let hdr = read_word major hd in
    let wz = getWosize hdr in
    getWosize_bound hdr;
    hd_address_spec obj;
    makeHeader_getWosize wz White (U64.uint_to_t tag);
    let new_hdr = makeHeader wz White (U64.uint_to_t tag) in
    assert (getWosize new_hdr == getWosize (read_word major hd));
    AllocHeaderLemmas.header_write_same_wosize_preserves_objects major obj new_hdr

/// Helper: set_promoted_tag preserves reads at addresses disjoint from the header
let set_promoted_tag_read_frame
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256}) (addr: hp_addr)
  : Lemma (requires (U64.v addr + U64.v mword <= U64.v (hd_address obj) \/
                     U64.v (hd_address obj) + U64.v mword <= U64.v addr))
          (ensures read_word (set_promoted_tag major obj tag) addr == read_word major addr)
  = let hd = hd_address obj in
    let hdr = read_word major hd in
    let wz = getWosize hdr in
    getWosize_bound hdr;
    let new_hdr = makeHeader wz White (U64.uint_to_t tag) in
    read_write_different major hd addr new_hdr

/// Helper: set_promoted_tag preserves fl_valid
/// Key insight: writing to hd_address obj doesn't change any free-list link reads
/// because all field addresses (>= obj) are above hd_address obj (= obj - 8).
#push-options "--z3rlimit 40 --fuel 1"
private let rec set_promoted_tag_preserves_fl_valid
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256}) (fp: U64.t) (fuel: nat)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem obj (objects zero_addr major) /\
             AllocLemmas.fl_valid major fp fuel /\
             AllocLemmas.chain_avoids major fp obj fuel = true)
          (ensures AllocLemmas.fl_valid (set_promoted_tag major obj tag) fp fuel)
          (decreases fuel)
  = let g' = set_promoted_tag major obj tag in
    set_promoted_tag_preserves_objects major obj tag;
    if fuel = 0 then
      AllocLemmas.fl_valid_zero g' fp
    else if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size || U64.v fp % U64.v mword <> 0 then
      AllocLemmas.fl_valid_terminal g' fp fuel
    else begin
      // fp is a valid obj_addr with fuel > 0
      AllocLemmas.fl_valid_elim major fp fuel;
      // fp <> obj since chain_avoids
      AllocLemmas.chain_avoids_head_ne major fp obj fuel;
      assert (fp <> obj);
      let fp_obj : obj_addr = fp in
      hd_address_spec obj;
      hd_address_spec fp_obj;
      let hd_obj = hd_address obj in
      let hdr_obj = read_word major hd_obj in
      let wz_obj = getWosize hdr_obj in
      getWosize_bound hdr_obj;
      let new_hdr = makeHeader wz_obj White (U64.uint_to_t tag) in
      // Show hd_fp is disjoint from hd_obj
      hd_address_injective fp_obj obj;
      // Show field[0] at fp is disjoint from hd_obj
      if U64.v fp < U64.v obj then begin
        objects_separated 0UL major fp_obj obj;
        wosize_of_object_spec fp_obj major;
        assert (U64.v fp + U64.v mword <= U64.v hd_obj)
      end else begin
        assert (U64.v hd_obj + U64.v mword <= U64.v fp)
      end;
      // Now we can frame the header read at fp and the field read at fp
      read_write_different major hd_obj (hd_address fp_obj) new_hdr;
      read_write_different major hd_obj (fp <: hp_addr) new_hdr;
      let next = read_word major fp_obj in
      // Decompose chain_avoids for tail
      if U64.v (hd_address fp_obj) + 16 <= heap_size then begin
        AllocLemmas.chain_avoids_tail major fp obj fuel;
        set_promoted_tag_preserves_fl_valid major obj tag next (fuel - 1)
      end else ();
      // Reconstruct fl_valid for g': need mem, wosize, and conditional tail
      assert (objects zero_addr g' == objects zero_addr major);
      assert (Seq.mem fp (objects 0UL g'));
      wosize_of_object_spec fp_obj g';
      wosize_of_object_spec fp_obj major;
      assert (wosize_of_object fp_obj g' == wosize_of_object fp_obj major);
      AllocLemmas.fl_valid_step g' fp fuel
    end
#pop-options

/// Helper: set_promoted_tag preserves fl_chain_terminates
#push-options "--z3rlimit 40 --fuel 1"
private let rec set_promoted_tag_preserves_fl_chain_terminates
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256}) (fp: U64.t) (fuel: nat)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem obj (objects zero_addr major) /\
             AllocLemmas.fl_valid major fp fuel /\
             AllocLemmas.fl_chain_terminates major fp fuel /\
             AllocLemmas.chain_avoids major fp obj fuel = true)
          (ensures AllocLemmas.fl_chain_terminates (set_promoted_tag major obj tag) fp fuel)
          (decreases fuel)
  = let g' = set_promoted_tag major obj tag in
    if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size || U64.v fp % U64.v mword <> 0 then
      AllocLemmas.fl_chain_terminates_terminal g' fp fuel
    else if fuel = 0 then begin
      AllocLemmas.fl_chain_terminates_valid_zero major fp
      // fl_chain_terminates major fp 0 = false contradicts requires
    end
    else begin
      // fp is valid, fuel > 0
      AllocLemmas.chain_avoids_head_ne major fp obj fuel;
      AllocLemmas.fl_valid_gives_mem major fp fuel;
      AllocLemmas.fl_valid_gives_wosize major fp fuel;
      hd_address_spec fp;
      hd_address_spec obj;
      let hd_obj = hd_address obj in
      let hdr_obj = read_word major hd_obj in
      let wz_obj = getWosize hdr_obj in
      getWosize_bound hdr_obj;
      let new_hdr = makeHeader wz_obj White (U64.uint_to_t tag) in
      // field[0] of fp: show disjointness from hd_obj
      if U64.v fp < U64.v obj then begin
        objects_separated 0UL major (fp <: obj_addr) obj;
        wosize_of_object_spec (fp <: obj_addr) major;
        assert (U64.v fp + U64.v mword <= U64.v hd_obj)
      end else
        assert (U64.v hd_obj + U64.v mword <= U64.v fp);
      assert (g' == write_word major hd_obj new_hdr);
      read_write_different major hd_obj (fp <: hp_addr) new_hdr;
      assert (read_word g' (fp <: obj_addr) == read_word major (fp <: obj_addr));
      if U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size then begin
        AllocLemmas.fl_chain_terminates_elim major fp fuel;
        AllocLemmas.fl_valid_elim major fp fuel;
        AllocLemmas.chain_avoids_tail major fp obj fuel;
        let next = read_word major (fp <: obj_addr) in
        set_promoted_tag_preserves_fl_chain_terminates major obj tag next (fuel - 1);
        assert (AllocLemmas.fl_chain_terminates g' next (fuel - 1));
        assert (next == read_word g' (fp <: obj_addr))
      end;
      AllocLemmas.fl_chain_terminates_step g' fp fuel
    end
#pop-options

/// Helper: set_promoted_tag preserves well_formed_heap_part1
/// wfh_part1: forall h in objects, hd_address h + 8 + wosize(h)*8 <= Seq.length g
/// objects is preserved (same wosize header write), and wosize of each object is preserved.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let set_promoted_tag_preserves_wfh_part1
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem obj (objects zero_addr major))
          (ensures well_formed_heap_part1 (set_promoted_tag major obj tag))
  = let g' = set_promoted_tag major obj tag in
    set_promoted_tag_preserves_objects major obj tag;
    assert (objects zero_addr g' == objects zero_addr major);
    let hd_obj = hd_address obj in
    hd_address_spec obj;
    let hdr = read_word major hd_obj in
    let wz = getWosize hdr in
    getWosize_bound hdr;
    let new_hdr = makeHeader wz White (U64.uint_to_t tag) in
    makeHeader_getWosize wz White (U64.uint_to_t tag);
    // For each h in objects, wosize_of_object h g' == wosize_of_object h major
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures (let wz_h = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + (U64.v wz_h * 8) <= Seq.length g'))
    = assert (Seq.mem h (objects zero_addr major));
      hd_address_spec h;
      let hd_h = hd_address h in
      if hd_h = hd_obj then begin
        // h must equal obj (if h <> obj, hd_address_injective gives hd_h <> hd_obj, contradiction)
        if h <> obj then hd_address_injective h obj else ();
        // h = obj
        read_write_same major hd_obj new_hdr;
        wosize_of_object_spec h g';
        wosize_of_object_spec h major;
        makeHeader_getWosize wz White (U64.uint_to_t tag)
      end else begin
        read_write_different major hd_obj hd_h new_hdr;
        wosize_of_object_spec h g';
        wosize_of_object_spec h major
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// set_promoted_tag_preserves_alloc_invariants: combines the above helpers
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let set_promoted_tag_preserves_alloc_invariants
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256}) (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem obj (objects zero_addr major) /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids major fp obj (heap_size / U64.v mword) = true)
          (ensures (let g' = set_promoted_tag major obj tag in
                    well_formed_heap_part1 g' /\
                    AllocLemmas.fl_valid g' fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates g' fp (heap_size / U64.v mword)))
  = let fuel = heap_size / U64.v mword in
    set_promoted_tag_preserves_wfh_part1 major obj tag;
    set_promoted_tag_preserves_fl_valid major obj tag fp fuel;
    set_promoted_tag_preserves_fl_chain_terminates major obj tag fp fuel
#pop-options

/// promote_object preserves allocator invariants
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let promote_object_preserves_alloc_invariants
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_object minor major obj fp wosize in
                    well_formed_heap_part1 res.major_out /\
                    AllocLemmas.fl_valid res.major_out res.fp_out (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.major_out res.fp_out (heap_size / U64.v mword)))
  = let fuel = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    if alloc_res.obj_out = 0UL then begin
      // OOM: promote_object returns original heap unchanged
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize
    end else begin
      // Success path: alloc → copy_fields → set_promoted_tag
      GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
      let dst_obj : obj_addr = alloc_res.obj_out in
      // Alloc preserves invariants
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize;
      GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
      GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
      AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
      // Copy fields preserves invariants
      WriteBody.chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
      copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
      copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wosize alloc_res.fp_out fuel;
      copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wosize alloc_res.fp_out fuel;
      // clean_promote_leftover preserves invariants
      let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize in
      let tag = minor_tag minor obj in
      minor_tag_bound minor obj;
      copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
      copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wosize alloc_res.fp_out fuel;
      clean_promote_leftover_preserves_alloc_invariants copied dst_obj wosize alloc_res.fp_out;
      clean_promote_leftover_preserves_objects copied dst_obj wosize;
      clean_promote_leftover_preserves_chain_avoids copied dst_obj wosize alloc_res.fp_out;
      // set_promoted_tag preserves invariants
      let cleaned = clean_promote_leftover copied dst_obj wosize in
      set_promoted_tag_preserves_alloc_invariants cleaned dst_obj tag alloc_res.fp_out
    end
#pop-options

/// set_promoted_tag preserves well_formed_heap_part4 (no infix objects)
/// when the promoted tag is not infix_tag.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let set_promoted_tag_preserves_wfh_part4
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
  : Lemma (requires
             well_formed_heap_part1 major /\
             well_formed_heap_part4 major /\
             Seq.mem obj (objects zero_addr major) /\
             tag <> U64.v GC.Spec.Object.infix_tag)
          (ensures well_formed_heap_part4 (set_promoted_tag major obj tag))
  = let g' = set_promoted_tag major obj tag in
    set_promoted_tag_preserves_objects major obj tag;
    assert (objects zero_addr g' == objects zero_addr major);
    let hd_obj = hd_address obj in
    hd_address_spec obj;
    let hdr = read_word major hd_obj in
    let wz = getWosize hdr in
    getWosize_bound hdr;
    let new_hdr = makeHeader wz White (U64.uint_to_t tag) in
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures ~(GC.Spec.Object.is_infix h g'))
    = assert (Seq.mem h (objects zero_addr major));
      GC.Spec.Object.is_infix_spec h g';
      GC.Spec.Object.is_infix_spec h major;
      GC.Spec.Object.tag_of_object_spec h g';
      GC.Spec.Object.tag_of_object_spec h major;
      hd_address_spec h;
      if hd_address h = hd_obj then begin
        if h <> obj then hd_address_injective h obj else ();
        read_write_same major hd_obj new_hdr;
        makeHeader_getTag wz White (U64.uint_to_t tag)
      end else
        read_write_different major hd_obj (hd_address h) new_hdr
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Promote all live objects
/// ---------------------------------------------------------------------------

/// Unfold lemmas for promote_all_aux — trivial from the recursive definition
let promote_all_aux_base (minor: minor_state) (major: heap)
                         (fp: U64.t) (live_set: seq U64.t)
                         (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx >= Seq.length live_set)
          (ensures promote_all_aux minor major fp live_set fwd idx ==
                   { major_final = major; fp_final = fp; fwd_map = fwd })
  = ()

let promote_all_aux_step (minor: minor_state) (major: heap)
                         (fp: U64.t) (live_set: seq U64.t)
                         (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length live_set /\
                    (let obj = Seq.index live_set idx in
                     let wz = minor_wosize minor obj in
                     wz > 0 /\
                     (let res = promote_object minor major obj fp wz in
                      res.new_addr <> 0UL)))
          (ensures (let obj = Seq.index live_set idx in
                    let wz = minor_wosize minor obj in
                    let res = promote_object minor major obj fp wz in
                    let fwd' = extend_forwarding fwd obj res.new_addr in
                    promote_all_aux minor major fp live_set fwd idx ==
                    promote_all_aux minor res.major_out res.fp_out live_set fwd' (idx + 1)))
  = ()

let promote_all_aux_skip (minor: minor_state) (major: heap)
                         (fp: U64.t) (live_set: seq U64.t)
                         (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length live_set /\
                    minor_wosize minor (Seq.index live_set idx) = 0)
          (ensures promote_all_aux minor major fp live_set fwd idx ==
                   promote_all_aux minor major fp live_set fwd (idx + 1))
  = ()

let promote_all_aux_oom (minor: minor_state) (major: heap)
                        (fp: U64.t) (live_set: seq U64.t)
                        (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length live_set /\
                    (let obj = Seq.index live_set idx in
                     let wz = minor_wosize minor obj in
                     wz > 0 /\
                     (promote_object minor major obj fp wz).new_addr = 0UL))
          (ensures promote_all_aux minor major fp live_set fwd idx ==
                   { major_final = major; fp_final = fp; fwd_map = fwd })
  = ()

/// ---------------------------------------------------------------------------
/// Pointer update: rewrite minor-heap pointers in major heap
/// ---------------------------------------------------------------------------

/// Unfold lemma: one step of update_object_pointers
let update_object_pointers_step (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
  : Lemma (requires i < wosize /\
                    U64.v obj + i * 8 + 8 <= heap_size /\
                    (U64.v obj + i * 8) % 8 = 0)
          (ensures (let field_offset = U64.v obj + i * 8 in
                    let field_val = read_word major (U64.uint_to_t field_offset) in
                    update_object_pointers major obj wosize fwd i ==
                    (if is_minor_pointer field_val then
                       let new_val = fwd field_val in
                       if new_val <> 0UL then
                         update_object_pointers (write_word major (U64.uint_to_t field_offset) new_val) obj wosize fwd (i + 1)
                       else
                         update_object_pointers major obj wosize fwd (i + 1)
                     else
                       update_object_pointers major obj wosize fwd (i + 1)))) = ()

/// Base case: identity at i >= wosize
let update_object_pointers_done (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
  : Lemma (requires i >= wosize)
          (ensures update_object_pointers major obj wosize fwd i == major) = ()

/// ---------------------------------------------------------------------------
/// Root rewriting
/// ---------------------------------------------------------------------------

let rec rewrite_roots_length (roots: seq U64.t) (fwd: forwarding_map)
  : Lemma (ensures Seq.length (rewrite_roots roots fwd) == Seq.length roots)
          (decreases (Seq.length roots)) =
  if Seq.length roots = 0 then ()
  else rewrite_roots_length (Seq.slice roots 1 (Seq.length roots)) fwd

let rec rewrite_roots_index (roots: seq U64.t) (fwd: forwarding_map) (i: nat)
  : Lemma (requires i < Seq.length roots)
          (ensures Seq.index (rewrite_roots roots fwd) i == rewrite_root (Seq.index roots i) fwd)
          (decreases i) =
  if i = 0 then ()
  else rewrite_roots_index (Seq.slice roots 1 (Seq.length roots)) fwd (i - 1)

#push-options "--z3rlimit 50"
let rewrite_roots_pointwise (roots: seq U64.t) (fwd: forwarding_map) (rs2: seq U64.t)
  : Lemma (requires Seq.length rs2 == Seq.length roots /\
                    (forall (j: nat). j < Seq.length roots ==>
                      Seq.index rs2 j == rewrite_root (Seq.index roots j) fwd))
          (ensures rs2 == rewrite_roots roots fwd) =
  rewrite_roots_length roots fwd;
  let rr = rewrite_roots roots fwd in
  assert (Seq.length rr == Seq.length rs2);
  let aux (i: nat{i < Seq.length rs2})
    : Lemma (Seq.index rs2 i == Seq.index rr i) =
    rewrite_roots_index roots fwd i
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro rs2 rr
#pop-options

/// ---------------------------------------------------------------------------
/// Full minor collection
/// ---------------------------------------------------------------------------

let minor_collect_spec_unfold (minor: minor_state) (major: heap)
                              (fp: U64.t) (roots: seq U64.t)
  : Lemma (let live_set = live_set_of minor major roots in
           let prom_res = promote_all_spec minor major fp live_set in
           (minor_collect_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_spec minor major fp roots).mc_fp == prom_res.fp_final) = ()

let minor_collect_resets_minor (minor: minor_state) (major: heap)
                               (fp: U64.t) (roots: seq U64.t)
  : Lemma (let res = minor_collect_spec minor major fp roots in
           minor_wf res.mc_minor /\ U64.v res.mc_minor.bump == 0) = ()

let minor_collect_rewrites_roots (minor: minor_state) (major: heap)
                                  (fp: U64.t) (roots: seq U64.t)
  : Lemma (let res = minor_collect_spec minor major fp roots in
           res.mc_roots == rewrite_roots roots res.mc_fwd) = ()

/// ---------------------------------------------------------------------------
/// Correctness lemmas (matching .fsti declaration order)
/// ---------------------------------------------------------------------------

/// Helper: derive dst_fields_valid from scalar upper bound + alignment
#push-options "--z3rlimit 20"
let dst_fields_valid_from_bounds (addr: U64.t) (wz: pos)
  : Lemma (requires U64.v addr % 8 == 0 /\ U64.v addr + (wz - 1) * 8 + 8 <= heap_size)
          (ensures dst_fields_valid addr wz)
  = let aux (j': nat)
      : Lemma (requires j' < wz)
              (ensures U64.v addr + j' * 8 + 8 <= heap_size /\ (U64.v addr + j' * 8) % 8 == 0)
    = assert (j' <= wz - 1);
      FStar.Math.Lemmas.lemma_mult_le_right 8 j' (wz - 1)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// copy_fields doesn't modify addresses outside the dst region [dst, dst+(n-1)*8+8).
/// Proved by delegating to the internal copy_fields_preserves_other.
#push-options "--z3rlimit 20 --fuel 2"
let copy_fields_frame
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      dst_fields_valid dst_obj n /\
      U64.v dst_obj % 8 == 0 /\
      (U64.v addr + 8 <= U64.v dst_obj \/
       U64.v addr >= U64.v dst_obj + n * 8))
    (ensures
      read_word (copy_fields minor major src_obj dst_obj i n) addr ==
      read_word major addr) =
  copy_fields_preserves_other minor major src_obj dst_obj i n addr
#pop-options

/// Key lemma: copy_fields correctly copies all fields (starting from index 0).
/// Proved by instantiating the internal copy_fields_preserves for each j.
#push-options "--z3rlimit 20 --fuel 2"
let copy_fields_all_correct
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (n: nat)
  : Lemma
    (requires
      dst_fields_valid dst_obj n /\
      U64.v dst_obj % 8 == 0)
    (ensures
      (let result = copy_fields minor major src_obj dst_obj 0 n in
       (forall (j:nat). j < n ==>
         read_word result (U64.uint_to_t (U64.v dst_obj + j * 8)) ==
         minor_read_field minor src_obj j))) =
  if n = 0 then ()
  else begin
    assert (U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size);
    let aux (j: nat{j < n}) : Lemma
      (let result = copy_fields minor major src_obj dst_obj 0 n in
       read_word result (U64.uint_to_t (U64.v dst_obj + j * 8)) ==
       minor_read_field minor src_obj j)
    = FStar.Math.Lemmas.lemma_mult_le_right 8 j (n - 1);
      copy_fields_preserves minor major src_obj dst_obj 0 n j
    in
    FStar.Classical.forall_intro aux
  end
#pop-options

/// After promote_object, if allocation succeeds AND the destination
/// has valid bounds, all field data is preserved.
#push-options "--z3rlimit 160 --fuel 2 --split_queries always"
let promote_preserves_fields
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             U64.v obj >= 8 /\ U64.v obj < minor_heap_size)
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              dst_fields_valid res.new_addr wosize ==>
              U64.v res.new_addr % 8 == 0 ==>
              (forall (j:nat). j < wosize ==>
                read_word res.major_out (U64.uint_to_t (U64.v res.new_addr + j * 8)) ==
                minor_read_field minor obj j))) =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    if U64.v alloc_res.obj_out % 8 = 0 &&
       U64.v alloc_res.obj_out + (wosize - 1) * 8 + 8 <= heap_size then begin
      // Establish dst_fields_valid
      let dfv_aux (j: nat) : Lemma
        (requires j < wosize)
        (ensures U64.v alloc_res.obj_out + j * 8 + 8 <= heap_size /\
                (U64.v alloc_res.obj_out + j * 8) % 8 == 0)
      = assert (j <= wosize - 1);
        FStar.Math.Lemmas.lemma_mult_le_right 8 j (wosize - 1);
        assert (j * 8 <= (wosize - 1) * 8);
        FStar.Math.Lemmas.modulo_lemma 0 8;
        FStar.Math.Lemmas.lemma_mod_plus (U64.v alloc_res.obj_out) j 8
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires dfv_aux);
      assert (dst_fields_valid alloc_res.obj_out wosize);
      copy_fields_all_correct minor alloc_res.heap_out obj alloc_res.obj_out wosize;
      // set_promoted_tag only modifies the header; field reads are preserved
      let copied = copy_fields minor alloc_res.heap_out obj alloc_res.obj_out 0 wosize in
      let tag = minor_tag minor obj in
      minor_tag_bound minor obj;
      // alloc_res.obj_out is a valid obj_addr: >= mword, < heap_size, % mword == 0
      // obj_out <> 0UL, obj_out % 8 == 0, so obj_out >= 8 = mword
      assert (alloc_res.obj_out <> 0UL);
      assert (U64.v alloc_res.obj_out % U64.v mword == 0);
      // obj_out <> 0 and obj_out % 8 == 0 means obj_out >= 8
      // Proof by contradiction: if obj_out < 8, then small_mod gives obj_out % 8 = obj_out = 0
      (if U64.v alloc_res.obj_out < U64.v mword then
        FStar.Math.Lemmas.small_mod (U64.v alloc_res.obj_out) (U64.v mword)
       else ());
      assert (U64.v alloc_res.obj_out >= U64.v mword);
      assert (U64.v alloc_res.obj_out + 8 <= heap_size);
      assert (U64.v alloc_res.obj_out < heap_size);
      let dst_obj : obj_addr = alloc_res.obj_out in
      let cleaned = clean_promote_leftover copied dst_obj wosize in
      let field_frame (j: nat{j < wosize}) : Lemma
        (read_word (set_promoted_tag cleaned dst_obj tag) (U64.uint_to_t (U64.v dst_obj + j * 8))
              == minor_read_field minor obj j)
      = FStar.Math.Lemmas.lemma_mult_le_right 8 j (wosize - 1);
        assert (U64.v dst_obj + j * 8 + 8 <= heap_size);
        let addr : hp_addr = U64.uint_to_t (U64.v dst_obj + j * 8) in
        hd_address_spec dst_obj;
        // j < wosize so j*8 < wosize*8, meaning addr <> extra field addr
        FStar.Math.Lemmas.lemma_mult_lt_right 8 j wosize;
        assert (U64.v addr <> U64.v dst_obj + wosize * U64.v mword);
        clean_promote_leftover_read_frame copied dst_obj wosize addr;
        assert (read_word cleaned addr == read_word copied addr);
        set_promoted_tag_read_frame cleaned dst_obj tag addr;
        assert (read_word (set_promoted_tag cleaned dst_obj tag) addr == read_word cleaned addr)
      in
      FStar.Classical.forall_intro field_frame
    end else ()
  end
#pop-options

/// ---------------------------------------------------------------------------
/// copy_fields preserves heap structure — delegated to WriteBodyLemmas module
/// ---------------------------------------------------------------------------

/// Predicate: dst_obj is not reachable from fp via the free-list chain.
let not_in_fl_chain = WriteBody.not_in_fl_chain

/// Bridge: chain_avoids (bool) implies not_in_fl_chain (prop).
let chain_avoids_implies_not_in_fl_chain = WriteBody.chain_avoids_implies_not_in_fl_chain

/// write_body aliases
private let write_body_preserves_objects = WriteBody.write_body_preserves_objects
private let write_body_preserves_fl_valid_aux = WriteBody.write_body_preserves_fl_valid_aux
private let write_body_preserves_not_in_fl_chain = WriteBody.write_body_preserves_not_in_fl_chain
private let write_body_preserves_fl_chain_terminates = WriteBody.write_body_preserves_fl_chain_terminates
private let write_body_preserves_chain_avoids_self = WriteBody.write_body_preserves_chain_avoids_self

/// copy_fields_preserves_* aliases
private let copy_fields_preserves_objects_aux = WriteBody.copy_fields_preserves_objects_aux
private let copy_fields_preserves_fl_valid_aux = WriteBody.copy_fields_preserves_fl_valid_aux
private let copy_fields_preserves_fl_chain_terminates = WriteBody.copy_fields_preserves_fl_chain_terminates
private let copy_fields_preserves_chain_avoids_self = WriteBody.copy_fields_preserves_chain_avoids_self
private let copy_fields_preserves_wfh_part1 = WriteBody.copy_fields_preserves_wfh_part1

/// copy_fields_preserves_objects: exported in .fsti (wrapper over _aux)
let copy_fields_preserves_objects
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n)
          (ensures
             objects zero_addr (copy_fields minor major src_obj dst_obj 0 n) == objects zero_addr major) =
  copy_fields_preserves_objects_aux minor major src_obj dst_obj 0 n

/// promote_object preserves existing object membership.
#push-options "--z3rlimit 80 --fuel 1"
let promote_object_preserves_objects
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.major_out)))) =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    AllocLemmas.alloc_spec_preserves_objects major fp wosize;
    AllocLemmas.alloc_spec_preserves_wf major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    // Reveal well_formed_heap to extract well_formed_heap_part1
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    copy_fields_preserves_objects minor alloc_res.heap_out obj dst_obj wosize;
    assert (objects zero_addr (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects zero_addr alloc_res.heap_out);
    let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    // Establish preconditions for copy_fields_preserves_wfh_part1
    assert (well_formed_heap_part1 alloc_res.heap_out);
    assert (Seq.mem dst_obj (objects zero_addr alloc_res.heap_out));
    assert (U64.v dst_obj % 8 == 0);
    assert (U64.v (wosize_of_object dst_obj alloc_res.heap_out) >= wosize);
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
    assert (well_formed_heap_part1 copied);
    assert (Seq.mem dst_obj (objects zero_addr copied));
    clean_promote_leftover_preserves_objects copied dst_obj wosize;
    assert (objects zero_addr (clean_promote_leftover copied dst_obj wosize) ==
            objects zero_addr copied);
    let cleaned = clean_promote_leftover copied dst_obj wosize in
    assert (Seq.mem dst_obj (objects zero_addr cleaned));
    set_promoted_tag_preserves_objects cleaned dst_obj tag
  end
#pop-options

/// Composite lemma: copy_fields preserves all allocator invariants together.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let copy_fields_preserves_alloc_invariants
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat{n > 0})
  (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids major fp dst_obj (heap_size / U64.v mword) = true)
           (ensures (let g' = copy_fields minor major src_obj dst_obj 0 n in
                     well_formed_heap_part1 g' /\
                     AllocLemmas.fl_valid g' fp (heap_size / U64.v mword) /\
                     AllocLemmas.fl_chain_terminates g' fp (heap_size / U64.v mword)))
  = let fuel = heap_size / U64.v mword in
    chain_avoids_implies_not_in_fl_chain major fp dst_obj fuel;
    copy_fields_preserves_wfh_part1 minor major src_obj dst_obj n;
    copy_fields_preserves_fl_valid_aux minor major src_obj dst_obj 0 n fp fuel;
    copy_fields_preserves_fl_chain_terminates minor major src_obj dst_obj 0 n fp fuel
#pop-options

/// promote_object preserves objects (part1 version — no full well_formed_heap needed)
#push-options "--z3rlimit 40 --fuel 1"
let promote_object_preserves_objects_part1
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                Seq.mem x (objects zero_addr res.major_out)))) =
  let fuel = heap_size / U64.v mword in
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    // After alloc: old objects are preserved (part1 version)
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize;
    // obj_out is a valid obj_addr
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    // obj_out is in objects of the output heap (part1 version)
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    // wosize of obj_out >= requested (no wfh needed)
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
    assert (objects zero_addr (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects zero_addr alloc_res.heap_out);
    // set_promoted_tag preserves objects too (same wosize header write)
    let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
    clean_promote_leftover_preserves_objects copied dst_obj wosize;
    let cleaned = clean_promote_leftover copied dst_obj wosize in
    set_promoted_tag_preserves_objects cleaned dst_obj tag;
    assert (objects zero_addr (set_promoted_tag cleaned dst_obj tag) ==
            objects zero_addr cleaned)
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --split_queries always"
let rec promote_all_aux_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_aux minor major fp live_set fwd idx in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.major_final))))
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      promote_all_aux_preserves_objects minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then ()
      else begin
        let fuel = heap_size / U64.v mword in
        promote_object_preserves_objects_part1 minor major obj fp wz;
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        // alloc_res.obj_out is a valid obj_addr (from allocator guards)
        GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        // After alloc: fl_valid for the post-alloc heap
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        // After alloc: obj_out is in objects and has sufficient wosize (part1)
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        // Key allocator property: alloc removes obj_out from the chain.
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        // fl_chain_terminates after alloc
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        // copy_fields preserves fl_valid
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        // copy_fields preserves fl_chain_terminates
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        // copy_fields preserves well_formed_heap_part1
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        // set_promoted_tag preserves all invariants (via clean_promote_leftover)
        let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
        let tag = minor_tag minor obj in
        minor_tag_bound minor obj;
        copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
        copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        clean_promote_leftover_preserves_objects copied dst_obj wz;
        clean_promote_leftover_preserves_alloc_invariants copied dst_obj wz alloc_res.fp_out;
        clean_promote_leftover_preserves_chain_avoids copied dst_obj wz alloc_res.fp_out;
        let cleaned = clean_promote_leftover copied dst_obj wz in
        set_promoted_tag_preserves_alloc_invariants cleaned dst_obj tag alloc_res.fp_out;
        assert (AllocLemmas.fl_valid res.major_out res.fp_out fuel);
        assert (AllocLemmas.fl_chain_terminates res.major_out res.fp_out fuel);
        assert (well_formed_heap_part1 res.major_out);
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux_preserves_objects minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
#pop-options

let promote_all_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.major_final)))) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_aux_preserves_objects minor major fp live_set empty_forwarding 0

/// promote_all preserves well_formed_heap_part1
#push-options "--z3rlimit 50 --fuel 1 --split_queries always"
let rec promote_all_aux_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (promote_all_aux minor major fp live_set fwd idx).major_final)
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      promote_all_aux_preserves_wfh_part1 minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then ()
      else begin
        let fuel = heap_size / U64.v mword in
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        // set_promoted_tag preserves wfh_part1, fl_valid, fl_chain_terminates
        let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
        let tag = minor_tag minor obj in
        minor_tag_bound minor obj;
        copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
        copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        clean_promote_leftover_preserves_objects copied dst_obj wz;
        clean_promote_leftover_preserves_alloc_invariants copied dst_obj wz alloc_res.fp_out;
        clean_promote_leftover_preserves_chain_avoids copied dst_obj wz alloc_res.fp_out;
        let cleaned = clean_promote_leftover copied dst_obj wz in
        set_promoted_tag_preserves_alloc_invariants cleaned dst_obj tag alloc_res.fp_out;
        assert (well_formed_heap_part1 res.major_out);
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux_preserves_wfh_part1 minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
#pop-options

/// Top-level: promote_all_spec preserves well_formed_heap_part1
let promote_all_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (promote_all_spec minor major fp live_set).major_final) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_aux_preserves_wfh_part1 minor major fp live_set empty_forwarding 0

/// copy_fields preserves well_formed_heap_part4 (no infix objects).
/// Since copy_fields only writes to field addresses (>= dst_obj), no headers change.
#push-options "--z3rlimit 40 --fuel 0 --split_queries always"
private let copy_fields_preserves_wfh_part4
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             well_formed_heap_part1 major /\
             well_formed_heap_part4 major /\
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             n > 0)
          (ensures
             well_formed_heap_part4 (copy_fields minor major src_obj dst_obj 0 n)) =
  let g' = copy_fields minor major src_obj dst_obj 0 n in
  copy_fields_preserves_objects_aux minor major src_obj dst_obj 0 n;
  assert (objects zero_addr g' == objects zero_addr major);
  let wz_dst = U64.v (wosize_of_object dst_obj major) in
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr major))
    (ensures ~(GC.Spec.Object.is_infix h g'))
  = let hdr_addr = hd_address h in
    hd_address_spec h;
    hd_address_spec dst_obj;
    if U64.v h > U64.v dst_obj then begin
      objects_separated 0UL major dst_obj h;
      wosize_of_object_spec dst_obj major
    end else ();
    assert (forall (k:nat). 0 <= k /\ k < n ==>
      (U64.v hdr_addr + 8 <= U64.v dst_obj + k * 8 \/ U64.v dst_obj + k * 8 + 8 <= U64.v hdr_addr));
    assert (U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size);
    copy_fields_preserves_other minor major src_obj dst_obj 0 n hdr_addr;
    GC.Spec.Object.tag_of_object_spec h g';
    GC.Spec.Object.tag_of_object_spec h major;
    GC.Spec.Object.is_infix_spec h g';
    GC.Spec.Object.is_infix_spec h major
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// promote_all_aux preserves well_formed_heap_part4 (no infix objects).
#push-options "--z3rlimit 100 --fuel 1 --split_queries always"
let rec promote_all_aux_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    well_formed_heap_part4 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    live_set_no_infix minor live_set)
          (ensures well_formed_heap_part4 (promote_all_aux minor major fp live_set fwd idx).major_final)
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      promote_all_aux_preserves_wfh_part4 minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then ()
      else begin
        let fuel = heap_size / U64.v mword in
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        // alloc preserves part1 and part4
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        AllocLemmas.alloc_spec_preserves_wfh_part4 major fp wz;
        // copy_fields preserves part1 and part4
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        copy_fields_preserves_wfh_part4 minor alloc_res.heap_out obj dst_obj wz;
        // set_promoted_tag preserves part1 and part4
        let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
        let tag = minor_tag minor obj in
        minor_tag_bound minor obj;
        copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
        copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        clean_promote_leftover_preserves_objects copied dst_obj wz;
        clean_promote_leftover_preserves_alloc_invariants copied dst_obj wz alloc_res.fp_out;
        clean_promote_leftover_preserves_chain_avoids copied dst_obj wz alloc_res.fp_out;
        clean_promote_leftover_preserves_wfh_part4 copied dst_obj wz;
        let cleaned = clean_promote_leftover copied dst_obj wz in
        set_promoted_tag_preserves_alloc_invariants cleaned dst_obj tag alloc_res.fp_out;
        assert (minor_tag minor obj <> U64.v GC.Spec.Object.infix_tag);
        set_promoted_tag_preserves_wfh_part4 cleaned dst_obj tag;
        assert (well_formed_heap_part1 res.major_out);
        assert (well_formed_heap_part4 res.major_out);
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux_preserves_wfh_part4 minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
#pop-options

/// Top-level: promote_all_spec preserves well_formed_heap_part4
#push-options "--z3rlimit 20"
let promote_all_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    live_set_no_infix minor live_set)
          (ensures well_formed_heap_part4 (promote_all_spec minor major fp live_set).major_final) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_aux_preserves_wfh_part4 minor major fp live_set empty_forwarding 0
#pop-options



/// ---------------------------------------------------------------------------
/// promote_all_spec preserves no_scan_invariant
/// ---------------------------------------------------------------------------

/// Helper: for a non-blue, no-scan object src != dst_obj in the post-promote
/// heap, its field reads are unchanged from the original heap.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0 --split_queries always"
private let promote_object_frame_old_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects 0UL major) /\
      AllocLemmas.chain_avoids major fp src (heap_size / U64.v mword) = true /\
      (src <> (GC.Spec.Allocator.alloc_spec major fp wz).obj_out) /\
      idx < U64.v (wosize_of_object src major) /\
      U64.v src + idx * 8 + 8 <= heap_size)
    (ensures
      (let res = promote_object minor major obj fp wz in
       let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
       read_word res.major_out field_addr == read_word major field_addr))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
  // 1. alloc preserves body reads of src
  AllocLemmas.alloc_spec_read_other major fp wz src field_addr;
  assert (read_word alloc_res.heap_out field_addr == read_word major field_addr);
  // 2. copy_fields preserves reads outside dst_obj body
  AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  FStar.Math.Lemmas.lemma_mult_le_right 8 wz (U64.v (wosize_of_object dst_obj alloc_res.heap_out));
  // Establish that src's header (and hence wosize) is unchanged by alloc
  AllocProps.alloc_spec_read_header_other_part1 major fp wz src;
  wosize_of_object_spec src alloc_res.heap_out;
  wosize_of_object_spec src major;
  // Case split and assert key scalar bound to help Z3 with the forall
  if U64.v src < U64.v dst_obj then begin
    objects_separated 0UL alloc_res.heap_out src dst_obj;
    // src + wosize*8 < dst_obj, and field_addr + 8 <= src + wosize*8, so field_addr + 8 <= dst_obj
    FStar.Math.Lemmas.lemma_mult_le_right 8 (idx + 1) (U64.v (wosize_of_object src alloc_res.heap_out));
    assert (U64.v field_addr + 8 <= U64.v dst_obj)
  end else begin
    objects_separated 0UL alloc_res.heap_out dst_obj src;
    // dst_obj + wosize_dst*8 < src <= field_addr, and wz <= wosize_dst
    assert (U64.v dst_obj + wz * 8 <= U64.v field_addr)
  end;
  copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz field_addr;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  assert (read_word copied field_addr == read_word alloc_res.heap_out field_addr);
  // 2b. clean_promote_leftover preserves reads outside extra field
  // extra field is at dst_obj + wz*8, which is within dst_obj's body
  // field_addr is within src's body, and src != dst_obj, so they're disjoint
  clean_promote_leftover_read_frame copied dst_obj wz field_addr;
  let cleaned = clean_promote_leftover copied dst_obj wz in
  assert (read_word cleaned field_addr == read_word copied field_addr);
  // 3. set_promoted_tag only writes at hd_address dst_obj
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  hd_address_spec dst_obj;
  hd_address_spec src;
  set_promoted_tag_read_frame cleaned dst_obj tag field_addr
#pop-options

/// Helper: for a non-blue, no-scan object src != dst_obj, its header is
/// unchanged from the original heap (so is_no_scan, is_blue, wosize are same).
/// Helper: for a non-blue, no-scan object src != dst_obj, its header is
/// unchanged from the original heap (so is_no_scan, is_blue, wosize are same).
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0 --split_queries no"
private let promote_object_frame_old_header
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects 0UL major) /\
      (src <> (GC.Spec.Allocator.alloc_spec major fp wz).obj_out))
    (ensures
      (let res = promote_object minor major obj fp wz in
       read_word res.major_out (hd_address src) == read_word major (hd_address src)))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  // 1. alloc preserves header of src
  AllocProps.alloc_spec_read_header_other_part1 major fp wz src;
  assert (read_word alloc_res.heap_out (hd_address src) == read_word major (hd_address src));
  // 2. copy_fields doesn't change header of src
  AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  FStar.Math.Lemmas.lemma_mult_le_right 8 wz (U64.v (wosize_of_object dst_obj alloc_res.heap_out));
  hd_address_spec src;
  hd_address_spec dst_obj;
  // Case split to establish disjointness of hd_address src from dst_obj body
  if U64.v src < U64.v dst_obj then begin
    objects_separated 0UL alloc_res.heap_out src dst_obj;
    // hd_address src < src < dst_obj, so hd_address src + 8 <= dst_obj
    assert (U64.v (hd_address src) + 8 <= U64.v dst_obj)
  end else begin
    objects_separated 0UL alloc_res.heap_out dst_obj src;
    // objects_separated: src > dst_obj + wosize_of_object_as_wosize(dst_obj)*8
    wosize_of_object_spec dst_obj alloc_res.heap_out;
    let wosize_dst = U64.v (wosize_of_object dst_obj alloc_res.heap_out) in
    // wosize_dst >= wz (from alloc_spec_obj_wosize_part1)
    assert (wosize_dst >= wz);
    // wz * 8 <= wosize_dst * 8 (from lemma_mult_le_right)
    FStar.Math.Lemmas.lemma_mult_le_right 8 wz wosize_dst;
    // hd_address src >= dst_obj + wosize_dst * 8 >= dst_obj + wz * 8
    assert (U64.v (hd_address src) >= U64.v dst_obj + wosize_dst * 8);
    assert (U64.v dst_obj + wz * 8 <= U64.v dst_obj + wosize_dst * 8)
  end;
  copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (hd_address src);
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  assert (read_word copied (hd_address src) == read_word alloc_res.heap_out (hd_address src));
  // 2b. clean_promote_leftover preserves header of src
  // Establish that copy_fields preserves the header of dst_obj
  // (needed for read_frame's disjunction: when wosize_dst = wz, clean is a no-op)
  copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (hd_address dst_obj);
  assert (read_word copied (hd_address dst_obj) == read_word alloc_res.heap_out (hd_address dst_obj));
  clean_promote_leftover_read_frame copied dst_obj wz (hd_address src);
  let cleaned = clean_promote_leftover copied dst_obj wz in
  // 3. set_promoted_tag writes at hd_address dst_obj, not at hd_address src
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_read_frame cleaned dst_obj tag (hd_address src)
#pop-options

/// Top-level: chain_avoids for excl == dst_obj case
#restart-solver
#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
private let promote_chain_avoids_dst_obj
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures (let res = promote_object minor major obj fp wz in
              let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
              AllocLemmas.chain_avoids res.major_out res.fp_out alloc_res.obj_out
                (heap_size / U64.v mword) = true))
  =
  let fuel = heap_size / U64.v mword in
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  promote_object_success minor major obj fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
  AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
  copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
  copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  clean_promote_leftover_preserves_objects copied dst_obj wz;
  clean_promote_leftover_preserves_alloc_invariants copied dst_obj wz alloc_res.fp_out;
  clean_promote_leftover_preserves_chain_avoids copied dst_obj wz alloc_res.fp_out;
  let cleaned = clean_promote_leftover copied dst_obj wz in
  set_promoted_tag_preserves_objects cleaned dst_obj tag;
  set_promoted_tag_preserves_alloc_invariants cleaned dst_obj tag alloc_res.fp_out;
  // chain_avoids_transfer through set_promoted_tag
  let set_tag_read_frame_at_obj (a: obj_addr)
    : Lemma (requires Seq.mem a (objects 0UL cleaned) /\
                      U64.v (wosize_of_object a cleaned) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      (a <: U64.t) <> (dst_obj <: U64.t))
            (ensures read_word (set_promoted_tag cleaned dst_obj tag) a ==
                     read_word cleaned a)
    = hd_address_spec a;
      hd_address_spec dst_obj;
      if U64.v a < U64.v dst_obj then
        objects_separated 0UL cleaned a dst_obj
      else ();
      set_promoted_tag_read_frame cleaned dst_obj tag (a <: hp_addr)
  in
  Classical.forall_intro (Classical.move_requires set_tag_read_frame_at_obj);
  AllocLemmas.chain_avoids_transfer cleaned (set_promoted_tag cleaned dst_obj tag)
    alloc_res.fp_out dst_obj fuel
#pop-options

/// Top-level: chain_avoids for excl ≠ dst_obj case
/// Takes backward membership as precondition to avoid axiom pollution.
#restart-solver
#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
private let promote_chain_avoids_other
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (excl: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      allocated_avoid_chain major fp /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem excl (objects 0UL major) /\
      ~(is_blue excl major) /\
      (excl <: U64.t) <> ((GC.Spec.Allocator.alloc_spec major fp wz).obj_out <: U64.t))
    (ensures
      AllocLemmas.chain_avoids (promote_object minor major obj fp wz).major_out
                               (promote_object minor major obj fp wz).fp_out
                               excl (heap_size / U64.v mword) = true)
  =
  let fuel = heap_size / U64.v mword in
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  promote_object_success minor major obj fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
  chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
  // Through alloc
  AllocLemmas.alloc_spec_preserves_chain_avoids_other major fp wz (excl <: U64.t);
  // Build forall for chain_avoids_transfer_excl2_obj (quantified over obj_addr)
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  clean_promote_leftover_preserves_objects copied dst_obj wz;
  let cleaned = clean_promote_leftover copied dst_obj wz in
  let cf_read_frame_at_obj (a: obj_addr)
    : Lemma (requires Seq.mem a (objects 0UL alloc_res.heap_out) /\
                      U64.v (wosize_of_object a alloc_res.heap_out) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      (a <: U64.t) <> (excl <: U64.t) /\
                      (a <: U64.t) <> (dst_obj <: U64.t))
            (ensures read_word cleaned a == read_word alloc_res.heap_out a)
    = hd_address_spec a;
      hd_address_spec dst_obj;
      if U64.v a < U64.v dst_obj then
        objects_separated 0UL alloc_res.heap_out a dst_obj
      else
        objects_separated 0UL alloc_res.heap_out dst_obj a;
      copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (a <: hp_addr);
      clean_promote_leftover_read_frame copied dst_obj wz (a <: hp_addr)
  in
  Classical.forall_intro (Classical.move_requires cf_read_frame_at_obj);
  copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
  copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
  copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
  clean_promote_leftover_preserves_alloc_invariants copied dst_obj wz alloc_res.fp_out;
  clean_promote_leftover_preserves_chain_avoids copied dst_obj wz alloc_res.fp_out;
  AllocLemmas.chain_avoids_transfer_excl2_obj alloc_res.heap_out cleaned
    alloc_res.fp_out (excl <: U64.t) (dst_obj <: U64.t) fuel;
  // Through set_promoted_tag
  set_promoted_tag_preserves_objects cleaned dst_obj tag;
  set_promoted_tag_preserves_alloc_invariants cleaned dst_obj tag alloc_res.fp_out;
  let set_tag_read_frame (a: obj_addr)
    : Lemma (requires Seq.mem a (objects 0UL cleaned) /\
                      U64.v (wosize_of_object a cleaned) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      (a <: U64.t) <> (excl <: U64.t))
            (ensures read_word (set_promoted_tag cleaned dst_obj tag) a ==
                     read_word cleaned a)
    = hd_address_spec a;
      hd_address_spec dst_obj;
      if U64.v a < U64.v dst_obj then
        objects_separated 0UL cleaned a dst_obj
      else ();
      set_promoted_tag_read_frame cleaned dst_obj tag (a <: hp_addr)
  in
  Classical.forall_intro (Classical.move_requires set_tag_read_frame);
  AllocLemmas.chain_avoids_transfer cleaned (set_promoted_tag cleaned dst_obj tag)
    alloc_res.fp_out (excl <: U64.t) fuel
#pop-options



/// Helper: no_scan_invariant for the newly promoted object's fields.
/// Extracted to reduce Z3 context size per query.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0 --split_queries always"
private let promote_no_scan_new_object_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (field_idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      minor_no_scan_invariant minor /\
      Seq.mem obj (minor_objects minor) /\
      wz <= minor_wosize minor obj /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
       let dst_obj = alloc_res.obj_out in
       U64.v dst_obj >= U64.v mword /\
       U64.v dst_obj < heap_size /\
       U64.v dst_obj % U64.v mword == 0 /\
       (let dst_obj : obj_addr = dst_obj in
        let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
        let tag = minor_tag minor obj in
        let cleaned = clean_promote_leftover copied dst_obj wz in
        let g' = set_promoted_tag cleaned dst_obj tag in
        is_no_scan dst_obj g' /\
        field_idx < U64.v (wosize_of_object dst_obj g') /\
        U64.v dst_obj + field_idx * 8 < heap_size)))
    (ensures
      (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
       let dst_obj = alloc_res.obj_out in
       let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
       let tag = minor_tag minor obj in
       let cleaned = clean_promote_leftover copied dst_obj wz in
       let g' = set_promoted_tag cleaned dst_obj tag in
       let field_addr : hp_addr = U64.uint_to_t (U64.v dst_obj + field_idx * 8) in
       ~(is_pointer_field (read_word g' field_addr))))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  let dst_obj : obj_addr = alloc_res.obj_out in
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  let cleaned = clean_promote_leftover copied dst_obj wz in
  let g' = set_promoted_tag cleaned dst_obj tag in
  let field_addr : hp_addr = U64.uint_to_t (U64.v dst_obj + field_idx * 8) in
  // Establish allocator facts
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  AllocProps.alloc_spec_obj_valid major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  // set_promoted_tag only writes the header — field reads preserved
  hd_address_spec dst_obj;
  set_promoted_tag_read_frame cleaned dst_obj tag field_addr;
  // Establish wosize chain: g' → cleaned → copied → alloc_res.heap_out
  // copy_fields_frame needs dst_fields_valid
  dst_fields_valid_from_bounds dst_obj wz;
  copy_fields_frame minor alloc_res.heap_out obj dst_obj 0 wz (hd_address dst_obj);
  clean_promote_leftover_preserves_header copied dst_obj wz;
  wosize_of_object_spec dst_obj alloc_res.heap_out;
  wosize_of_object_spec dst_obj copied;
  wosize_of_object_spec dst_obj cleaned;
  set_promoted_tag_unfold cleaned dst_obj tag;
  wosize_of_object_spec dst_obj g';
  read_write_same cleaned (hd_address dst_obj)
    (makeHeader (getWosize (read_word cleaned (hd_address dst_obj))) White (U64.uint_to_t tag));
  makeHeader_getWosize
    (getWosize (read_word cleaned (hd_address dst_obj))) White (U64.uint_to_t tag);
  // Establish heap bounds for dst_obj fields
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  FStar.Math.Lemmas.lemma_mult_le_right 8 wz (U64.v (wosize_of_object dst_obj alloc_res.heap_out));
  // Case split: field_idx < wz (copied from minor) vs field_idx >= wz (zeroed extra)
  if field_idx < wz then begin
    // Field was copied from minor → use minor_no_scan_invariant
    clean_promote_leftover_read_frame copied dst_obj wz field_addr;
    dst_fields_valid_from_bounds dst_obj wz;
    copy_fields_all_correct minor alloc_res.heap_out obj dst_obj wz;
    // Establish that read_word g' (hd_address dst_obj) = makeHeader ... White (uint_to_t tag)
    set_promoted_tag_unfold cleaned dst_obj tag;
    read_write_same cleaned (hd_address dst_obj)
      (makeHeader (getWosize (read_word cleaned (hd_address dst_obj))) White (U64.uint_to_t tag));
    assert (read_word g' (hd_address dst_obj) ==
            makeHeader (getWosize (read_word cleaned (hd_address dst_obj))) White (U64.uint_to_t tag));
    // getTag of the makeHeader == uint_to_t tag
    makeHeader_getTag
      (getWosize (read_word cleaned (hd_address dst_obj))) White (U64.uint_to_t tag);
    assert (getTag (read_word g' (hd_address dst_obj)) == U64.uint_to_t tag);
    // tag_of_object == getTag (read_word g' (hd_address dst_obj))
    tag_of_object_spec dst_obj g';
    assert (tag_of_object dst_obj g' == U64.uint_to_t tag);
    // is_no_scan means tag_of_object >= no_scan_tag (251)
    is_no_scan_spec dst_obj g';
    no_scan_tag_val();
    assert (U64.v (tag_of_object dst_obj g') >= 251);
    assert (minor_tag minor obj >= 251);
    assert (field_idx < minor_wosize minor obj)
  end else begin
    // field_idx >= wz: extra leftover field zeroed by clean_promote_leftover
    // Establish tight upper bound: wosize <= wz + 1 (allocator invariant)
    AllocProps.alloc_spec_obj_wosize_upper_part1 major fp wz;
    // wosize chain: wosize_of_object dst_obj g' == wosize_of_object dst_obj alloc_res.heap_out
    // Therefore: wz <= field_idx < wosize_of_object dst_obj g' <= wz + 1
    // This forces field_idx = wz
    assert (field_idx = wz);
    // clean_promote_leftover zeroes the field at offset wz * 8 when block_wz > wz
    clean_promote_leftover_zeroes_extra copied dst_obj wz
  end
#pop-options

/// Helper: no_scan_invariant for OLD objects (src <> dst_obj) in post-promote heap.
/// Extracted to reduce Z3 context for the forall_intro_2 call in the main lemma.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0 --split_queries no"
private let promote_no_scan_old_object_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (field_idx: nat)
  : Lemma
    (requires
      no_scan_invariant major /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      allocated_avoid_chain major fp /\
      minor_no_scan_invariant minor /\
      Seq.mem obj (minor_objects minor) /\
      wz <= minor_wosize minor obj /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
       let dst_obj = alloc_res.obj_out in
       U64.v dst_obj >= U64.v mword /\
       U64.v dst_obj < heap_size /\
       U64.v dst_obj % U64.v mword == 0 /\
       src <> dst_obj /\
       (let dst_obj : obj_addr = dst_obj in
        let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
        let tag = minor_tag minor obj in
        let cleaned = clean_promote_leftover copied dst_obj wz in
        let g' = set_promoted_tag cleaned dst_obj tag in
        Seq.mem src (objects 0UL g') /\
        is_no_scan src g' /\
        ~(is_blue src g') /\
        field_idx < U64.v (wosize_of_object src g') /\
        U64.v src + field_idx * 8 < heap_size)))
    (ensures
      (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
       let dst_obj : obj_addr = alloc_res.obj_out in
       let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
       let tag = minor_tag minor obj in
       let cleaned = clean_promote_leftover copied dst_obj wz in
       let g' = set_promoted_tag cleaned dst_obj tag in
       let field_addr : hp_addr = U64.uint_to_t (U64.v src + field_idx * 8) in
       ~(is_pointer_field (read_word g' field_addr))))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_valid major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  let cleaned = clean_promote_leftover copied dst_obj wz in
  let g' = set_promoted_tag cleaned dst_obj tag in
  // Objects equality chain
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  clean_promote_leftover_preserves_objects copied dst_obj wz;
  set_promoted_tag_preserves_objects cleaned dst_obj tag;
  // Header disjointness from dst_obj body
  hd_address_spec src;
  hd_address_spec dst_obj;
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  wosize_of_object_spec dst_obj alloc_res.heap_out;
  FStar.Math.Lemmas.lemma_mult_le_right 8 wz
    (U64.v (wosize_of_object dst_obj alloc_res.heap_out));
  if U64.v src < U64.v dst_obj then
    objects_separated 0UL alloc_res.heap_out src dst_obj
  else
    objects_separated 0UL alloc_res.heap_out dst_obj src;
  // Header frame chain: g' → cleaned → copied → alloc_res.heap_out
  copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (hd_address src);
  copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (hd_address dst_obj);
  wosize_of_object_spec dst_obj copied;
  clean_promote_leftover_read_frame copied dst_obj wz (hd_address src);
  set_promoted_tag_read_frame cleaned dst_obj tag (hd_address src);
  // Blue/color specs for src in both heaps
  is_blue_iff src g';
  is_blue_iff src alloc_res.heap_out;
  color_of_object_spec src g';
  color_of_object_spec src alloc_res.heap_out;
  // Frame helpers for old object
  promote_object_frame_old_header minor major obj fp wz src;
  is_no_scan_spec src g';
  is_no_scan_spec src major;
  tag_of_object_spec src g';
  tag_of_object_spec src major;
  is_blue_iff src major;
  color_of_object_spec src major;
  wosize_of_object_spec src g';
  wosize_of_object_spec src major;
  promote_object_frame_old_field minor major obj fp wz src field_idx;
  no_scan_invariant_elim major src field_idx
#pop-options

/// Unified helper: proves no_scan_invariant field condition for ANY src in post-promote heap.
/// Uses FLAT preconditions (no nested lets) so Z3 can match at the forall_intro_2 call site.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0 --split_queries always"
private let promote_no_scan_any_object_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (field_idx: nat)
  : Lemma
    (requires
      no_scan_invariant major /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      allocated_avoid_chain major fp /\
      minor_no_scan_invariant minor /\
      Seq.mem obj (minor_objects minor) /\
      wz <= minor_wosize minor obj /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem src (objects 0UL (promote_object minor major obj fp wz).major_out) /\
      is_no_scan src (promote_object minor major obj fp wz).major_out /\
      ~(is_blue src (promote_object minor major obj fp wz).major_out) /\
      field_idx < U64.v (wosize_of_object src (promote_object minor major obj fp wz).major_out) /\
      U64.v src + field_idx * 8 < heap_size)
    (ensures
      (let field_addr : hp_addr = U64.uint_to_t (U64.v src + field_idx * 8) in
       ~(is_pointer_field (read_word (promote_object minor major obj fp wz).major_out field_addr))))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  if src = dst_obj then
    promote_no_scan_new_object_field minor major obj fp wz field_idx
  else
    promote_no_scan_old_object_field minor major obj fp wz src field_idx
#pop-options

/// Per-step: promote_object preserves no_scan_invariant
#restart-solver
#push-options "--z3rlimit 600 --fuel 0 --ifuel 0 --split_queries always"
let promote_object_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma
    (requires
      no_scan_invariant major /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      allocated_avoid_chain major fp /\
      minor_no_scan_invariant minor /\
      Seq.mem obj (minor_objects minor) /\
      wz <= minor_wosize minor obj)
    (ensures no_scan_invariant (promote_object minor major obj fp wz).major_out)
  =
  let res = promote_object minor major obj fp wz in
  if res.new_addr = 0UL then begin
    promote_object_oom minor major obj fp wz;
    assert (res.major_out == major)
  end else begin
    let g' = res.major_out in
    // Help Z3 with the hp_addr well-formedness for the forall body
    assert (forall (src: obj_addr) (field_idx: nat).
      U64.v src + field_idx * 8 < heap_size ==>
      U64.v src + field_idx * 8 >= 0 /\
      U64.v src + field_idx * 8 < pow2 64 /\
      (U64.v src + field_idx * 8) % U64.v mword == 0);
    // Prove the universal quantifier for no_scan_invariant_intro.
    // We put the full implication in ensures (matching no_scan_invariant's structure)
    // to avoid a type well-formedness issue with move_requires_2 where the ensures
    // expression isn't well-typed for all argument values.
    let aux (src: obj_addr) (field_idx: nat) : Lemma
      (ensures
        (Seq.mem src (objects 0UL g') /\ is_no_scan src g' /\ ~(is_blue src g') /\
         field_idx < U64.v (wosize_of_object src g') /\ U64.v src + field_idx * 8 < heap_size) ==>
        (let field_addr : hp_addr = U64.uint_to_t (U64.v src + field_idx * 8) in
         ~(is_pointer_field (read_word g' field_addr))))
    = if Seq.mem src (objects 0UL g') && is_no_scan src g' &&
         not (is_blue src g') &&
         field_idx < U64.v (wosize_of_object src g') && U64.v src + field_idx * 8 < heap_size
      then
        promote_no_scan_any_object_field minor major obj fp wz src field_idx
    in
    Classical.forall_intro_2 aux;
    no_scan_invariant_intro g'
  end
#pop-options

/// Helper: Prove that a non-blue object in the post-promote heap was already
/// in the original heap's objects list. Uses the "new objects are blue" property
/// of alloc_spec as a backward membership argument.
#restart-solver
#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
private let prove_excl_in_original_objects
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (excl: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem excl (objects 0UL (promote_object minor major obj fp wz).major_out) /\
      ~(is_blue excl (promote_object minor major obj fp wz).major_out) /\
      (excl <: U64.t) <> ((GC.Spec.Allocator.alloc_spec major fp wz).obj_out <: U64.t))
    (ensures Seq.mem excl (objects 0UL major))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  let res = promote_object minor major obj fp wz in
  promote_object_success minor major obj fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  // Objects equality chain: objects(res.major_out) == objects(alloc_out)
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  clean_promote_leftover_preserves_objects copied dst_obj wz;
  let cleaned = clean_promote_leftover copied dst_obj wz in
  set_promoted_tag_preserves_objects cleaned dst_obj tag;
  // From equality chain: excl ∈ objects(alloc_out)
  assert (Seq.mem excl (objects 0UL alloc_res.heap_out));
  // Show header of excl is unchanged from alloc_out through to res.major_out.
  hd_address_spec excl;
  hd_address_spec dst_obj;
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  assert (U64.v (wosize_of_object dst_obj alloc_res.heap_out) >= wz);
  (if U64.v excl < U64.v dst_obj then
     objects_separated 0UL alloc_res.heap_out excl dst_obj
   else begin
     objects_separated 0UL alloc_res.heap_out dst_obj excl;
     FStar.Math.Lemmas.lemma_mult_le_right 8 wz
       (U64.v (wosize_of_object dst_obj alloc_res.heap_out))
   end);
  copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (hd_address excl);
  copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (hd_address dst_obj);
  wosize_of_object_spec dst_obj copied;
  wosize_of_object_spec dst_obj alloc_res.heap_out;
  assert (read_word copied (hd_address dst_obj) == read_word alloc_res.heap_out (hd_address dst_obj));
  assert (U64.v (getWosize (read_word copied (hd_address dst_obj))) >= wz);
  if U64.v (hd_address excl) = U64.v dst_obj + wz * U64.v mword then begin
    assert (U64.v (getWosize (read_word copied (hd_address dst_obj))) <= wz)
  end;
  clean_promote_leftover_read_frame copied dst_obj wz (hd_address excl);
  set_promoted_tag_read_frame cleaned dst_obj tag (hd_address excl);
  is_blue_iff excl alloc_res.heap_out;
  is_blue_iff excl res.major_out;
  color_of_object_spec excl alloc_res.heap_out;
  color_of_object_spec excl res.major_out;
  assert (~(is_blue excl alloc_res.heap_out));
  AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wz
#pop-options

/// Dispatcher: promote_object preserves chain_avoids for any excl.
#restart-solver
#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
private let promote_object_chain_avoids_excl
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (excl: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      allocated_avoid_chain major fp /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      Seq.mem excl (objects 0UL (promote_object minor major obj fp wz).major_out) /\
      ~(is_blue excl (promote_object minor major obj fp wz).major_out))
    (ensures
      AllocLemmas.chain_avoids (promote_object minor major obj fp wz).major_out
                               (promote_object minor major obj fp wz).fp_out
                               excl (heap_size / U64.v mword) = true)
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  if (excl <: U64.t) = (dst_obj <: U64.t) then
    promote_chain_avoids_dst_obj minor major obj fp wz
  else begin
    prove_excl_in_original_objects minor major obj fp wz excl;
    promote_object_frame_old_header minor major obj fp wz excl;
    is_blue_iff excl major;
    is_blue_iff excl (promote_object minor major obj fp wz).major_out;
    color_of_object_spec excl major;
    color_of_object_spec excl (promote_object minor major obj fp wz).major_out;
    assert (~(is_blue excl major));
    promote_chain_avoids_other minor major obj fp wz excl
  end
#pop-options

/// Helper: promote_object preserves allocated_avoid_chain.
/// Every non-blue object in the post-promote heap avoids the new free-list chain.
#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let promote_object_preserves_allocated_avoid_chain
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      allocated_avoid_chain major fp /\
      (promote_object minor major obj fp wz).new_addr <> 0UL)
    (ensures
      allocated_avoid_chain (promote_object minor major obj fp wz).major_out
                           (promote_object minor major obj fp wz).fp_out)
  = Classical.forall_intro
      (Classical.move_requires (promote_object_chain_avoids_excl minor major obj fp wz))
#pop-options


/// Inductive: promote_all_aux preserves no_scan_invariant
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"
private let rec promote_all_aux_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma
    (requires
      no_scan_invariant major /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      allocated_avoid_chain major fp /\
      minor_no_scan_invariant minor /\
      (forall (k:nat). k < Seq.length live_set ==>
        Seq.mem (Seq.index live_set k) (minor_objects minor)))
    (ensures no_scan_invariant (promote_all_aux minor major fp live_set fwd idx).major_final)
    (decreases (Seq.length live_set - idx))
  =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      promote_all_aux_preserves_no_scan_invariant minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then ()
      else begin
        let fuel = heap_size / U64.v mword in
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        // Establish that promote_object preserves no_scan_invariant
        promote_object_preserves_no_scan_invariant minor major obj fp wz;
        assert (no_scan_invariant res.major_out);
        // Re-establish allocator invariants for recursive call
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        // set_promoted_tag preserves allocator invariants
        let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
        let tag = minor_tag minor obj in
        minor_tag_bound minor obj;
        copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
        copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        clean_promote_leftover_preserves_objects copied dst_obj wz;
        clean_promote_leftover_preserves_alloc_invariants copied dst_obj wz alloc_res.fp_out;
        clean_promote_leftover_preserves_chain_avoids copied dst_obj wz alloc_res.fp_out;
        let cleaned = clean_promote_leftover copied dst_obj wz in
        set_promoted_tag_preserves_alloc_invariants cleaned dst_obj tag alloc_res.fp_out;
        // Establish allocated_avoid_chain for res.major_out
        promote_object_preserves_allocated_avoid_chain minor major obj fp wz;
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux_preserves_no_scan_invariant minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
#pop-options

/// Top-level: promote_all_spec preserves no_scan_invariant
let promote_all_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    no_scan_invariant major /\
                    minor_no_scan_invariant minor /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    allocated_avoid_chain major fp /\
                    (forall (k:nat). k < Seq.length live_set ==>
                      Seq.mem (Seq.index live_set k) (minor_objects minor)))
          (ensures no_scan_invariant (promote_all_spec minor major fp live_set).major_final) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_aux_preserves_no_scan_invariant minor major fp live_set empty_forwarding 0
/// ---------------------------------------------------------------------------
/// fields_match_minor intro/elim lemmas (predicate is opaque_to_smt, recursive)
/// ---------------------------------------------------------------------------

let fields_match_minor_empty
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t)
  : Lemma (fields_match_minor minor major fwd live_set 0)
  = reveal_opaque (`%fields_match_minor) (fields_match_minor minor major fwd live_set 0)

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let fields_match_minor_extend
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  : Lemma (requires
      fields_match_minor minor major fwd live_set idx /\
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       fwd obj = 0UL \/ wz = 0 \/
       (fwd obj <> 0UL /\ wz > 0 /\
        (dst_fields_valid (fwd obj) wz /\ U64.v (fwd obj) % 8 == 0 ==>
         (forall (j:nat). j < wz ==>
           read_word major (U64.uint_to_t (U64.v (fwd obj) + j * 8)) ==
           minor_read_field minor obj j)))))
    (ensures fields_match_minor minor major fwd live_set (idx + 1))
  = // Unfold one step: fields_match_minor ... (idx+1) = fields_match_minor ... idx /\ body(idx)
    reveal_opaque (`%fields_match_minor) (fields_match_minor minor major fwd live_set (idx + 1))
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let rec fields_match_minor_elim_helper
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat) (k: nat)
  : Lemma (requires fields_match_minor minor major fwd live_set idx /\
                    k < idx /\ k < Seq.length live_set)
          (ensures (let obj = Seq.index live_set k in
                    let wz = minor_wosize minor obj in
                    fwd obj <> 0UL /\ wz > 0 ==>
                    (dst_fields_valid (fwd obj) wz /\ U64.v (fwd obj) % 8 == 0 ==>
                     (forall (j:nat). j < wz ==>
                       read_word major (U64.uint_to_t (U64.v (fwd obj) + j * 8)) ==
                       minor_read_field minor obj j))))
          (decreases (idx - k))
  = // Unfold one step: fields_match_minor ... idx = fields_match_minor ... (idx-1) /\ body(idx-1)
    reveal_opaque (`%fields_match_minor) (fields_match_minor minor major fwd live_set idx);
    if k = idx - 1 then ()
    else fields_match_minor_elim_helper minor major fwd live_set (idx - 1) k
#pop-options

#push-options "--z3rlimit 40"
let fields_match_minor_elim_lemma
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat) (k: nat) (j: nat) (field_addr: hp_addr)
  : Lemma (requires
      fields_match_minor minor major fwd live_set idx /\
      k < idx /\ k < Seq.length live_set /\
      (let obj = Seq.index live_set k in
       let wz = minor_wosize minor obj in
       fwd obj <> 0UL /\ wz > 0 /\ j < wz /\
       U64.v (fwd obj) % 8 == 0 /\
       U64.v (fwd obj) + (wz - 1) * 8 + 8 <= heap_size /\
       field_addr == U64.uint_to_t (U64.v (fwd obj) + j * 8)))
    (ensures (let obj = Seq.index live_set k in
              read_word major field_addr == minor_read_field minor obj j))
  = let obj = Seq.index live_set k in
    let wz = minor_wosize minor obj in
    fields_match_minor_elim_helper minor major fwd live_set idx k;
    dst_fields_valid_from_bounds (fwd obj) wz
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let rec fields_match_minor_weaken
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx idx': nat)
  : Lemma (requires fields_match_minor minor major fwd live_set idx /\ idx' <= idx)
          (ensures fields_match_minor minor major fwd live_set idx')
          (decreases (idx - idx'))
  = if idx = idx' then ()
    else begin
      reveal_opaque (`%fields_match_minor) (fields_match_minor minor major fwd live_set idx);
      fields_match_minor_weaken minor major fwd live_set (idx - 1) idx'
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let rec fields_match_minor_intro
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  : Lemma (requires
      (forall (k:nat). k < idx /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz > 0 ==>
         (let new_addr = fwd obj in
          dst_fields_valid new_addr wz /\
          U64.v new_addr % 8 == 0 ==>
          (forall (j:nat). j < wz ==>
            read_word major (U64.uint_to_t (U64.v new_addr + j * 8)) ==
            minor_read_field minor obj j)))))
    (ensures fields_match_minor minor major fwd live_set idx)
    (decreases idx)
  = reveal_opaque (`%fields_match_minor) (fields_match_minor minor major fwd live_set idx);
    if idx = 0 then ()
    else fields_match_minor_intro minor major fwd live_set (idx - 1)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let rec fields_match_minor_intro_flat
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  : Lemma (requires
      (forall (k:nat) (j:nat).
        (k < idx /\ k < Seq.length live_set /\
         (let obj = Seq.index live_set k in
          let wz = minor_wosize minor obj in
          fwd obj <> 0UL /\ wz > 0 /\ j < wz /\
          dst_fields_valid (fwd obj) wz /\ U64.v (fwd obj) % 8 == 0)) ==>
        (let obj = Seq.index live_set k in
         read_word major (U64.uint_to_t (U64.v (fwd obj) + j * 8)) ==
         minor_read_field minor obj j)))
    (ensures fields_match_minor minor major fwd live_set idx)
    (decreases idx)
  = reveal_opaque (`%fields_match_minor) (fields_match_minor minor major fwd live_set idx);
    if idx = 0 then ()
    else fields_match_minor_intro_flat minor major fwd live_set (idx - 1)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let rec fields_match_minor_frame
  (minor: minor_state) (major major': heap) (fwd fwd': forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  : Lemma (requires
      fields_match_minor minor major fwd live_set idx /\
      (forall (k:nat). k < idx /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         fwd' obj == fwd obj /\
         (let wz = minor_wosize minor obj in
          fwd obj <> 0UL /\ wz > 0 ==>
          (let addr = fwd obj in
           dst_fields_valid addr wz /\ U64.v addr % 8 == 0 ==>
           (forall (j:nat). j < wz ==>
             read_word major' (U64.uint_to_t (U64.v addr + j * 8)) ==
             read_word major (U64.uint_to_t (U64.v addr + j * 8))))))))
    (ensures fields_match_minor minor major' fwd' live_set idx)
    (decreases idx)
  = reveal_opaque (`%fields_match_minor) (fields_match_minor minor major fwd live_set idx);
    reveal_opaque (`%fields_match_minor) (fields_match_minor minor major' fwd' live_set idx);
    if idx = 0 then ()
    else fields_match_minor_frame minor major major' fwd fwd' live_set (idx - 1)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let rec fields_match_minor_intro_by_proof
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat)
  (proof: (k:nat -> j:nat -> Lemma
    (requires k < idx /\ k < Seq.length live_set /\
      (let obj = Seq.index live_set k in
       let wz = minor_wosize minor obj in
       fwd obj <> 0UL /\ wz > 0 /\ j < wz /\
       dst_fields_valid (fwd obj) wz /\ U64.v (fwd obj) % 8 == 0))
    (ensures (let obj = Seq.index live_set k in
       read_word major (U64.uint_to_t (U64.v (fwd obj) + j * 8)) ==
       minor_read_field minor obj j))))
  : Lemma (ensures fields_match_minor minor major fwd live_set idx)
          (decreases idx)
  = if idx = 0 then fields_match_minor_empty minor major fwd live_set
    else begin
      fields_match_minor_intro_by_proof minor major fwd live_set (idx - 1)
        (fun k j -> proof k j);
      if idx - 1 < Seq.length live_set then begin
        let k = idx - 1 in
        let obj = Seq.index live_set k in
        let wz = minor_wosize minor obj in
        let new_addr = fwd obj in
        // Use fields_match_minor_extend to go from (idx-1) to idx.
        // Its requires needs a disjunction about the object at k=idx-1.
        // We establish the third disjunct using impl_intro_gen for the
        // inner implication where forall j's well-formedness depends on
        // dst_fields_valid.
        if fwd obj = 0UL || wz = 0 then
          fields_match_minor_extend minor major fwd live_set k
        else begin
          // fwd obj <> 0UL /\ wz > 0
          // Need: dst_fields_valid new_addr wz /\ align ==> forall j. ...
          // Use impl_intro_gen: q's well-formedness depends on p
          Classical.impl_intro_gen
            #(dst_fields_valid new_addr wz /\ U64.v new_addr % 8 == 0)
            #(fun (_: squash (dst_fields_valid new_addr wz /\ U64.v new_addr % 8 == 0)) ->
                forall (j:nat). j < wz ==>
                  read_word major (U64.uint_to_t (U64.v new_addr + j * 8)) ==
                  minor_read_field minor obj j)
            (fun (_: squash (dst_fields_valid new_addr wz /\ U64.v new_addr % 8 == 0)) ->
              // Can't use (move_requires step) where step has (requires j < wz),
              // because move_requires extracts #q as a standalone nat -> Type,
              // which fails well-formedness for U64.uint_to_t without bounds.
              // Solution: put j < wz as ==> in ensures (well-formed because
              // U64.uint_to_t is checked under the ==> antecedent j < wz).
              let step (j:nat) : Lemma
                (ensures (j < wz ==>
                  read_word major (U64.uint_to_t (U64.v new_addr + j * 8)) ==
                  minor_read_field minor obj j))
                = if j < wz then proof k j else ()
              in
              Classical.forall_intro step);
          fields_match_minor_extend minor major fwd live_set k
        end
      end else
        // idx - 1 >= Seq.length live_set, so the implication in
        // fields_match_minor's definition is vacuously true.
        reveal_opaque (`%fields_match_minor) (fields_match_minor minor major fwd live_set idx)
    end
#pop-options

