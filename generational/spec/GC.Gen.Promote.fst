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
open GC.Gen.WriteBodyLemmas
/// Headers of two distinct 8-aligned objects are 8 bytes apart.
///
/// Proved in an empty context: under the enclosing well-formed-heap and
/// free-list hypotheses, combining `U64.v` injectivity with the alignment
/// facts sends Z3 into a matching loop.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let hdr_pair_disjoint (s d: U64.t) (hs hd_v: nat) : Lemma
  (requires U64.v s % 8 == 0 /\ U64.v d % 8 == 0 /\ ~(s == d) /\
            hs == U64.v s - 8 /\ hd_v == U64.v d - 8)
  (ensures hs + U64.v mword <= hd_v \/ hd_v + U64.v mword <= hs)
  = ()
#pop-options

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
#push-options "--z3rlimit 10 --fuel 2"
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
                    = ()

let promote_object_success (minor: minor_state) (major: heap) (obj: U64.t)
                           (fp: U64.t) (wosize: nat{wosize > 0})
                    = ()

let set_promoted_tag_unfold
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
                         = ()

/// zero_promote_padding lemmas
let zero_promote_padding_frame
  (g: heap) (dst: obj_addr) (wz: nat) (addr: hp_addr)
  = let actual_wz = U64.v (wosize_of_object dst g) in
    if actual_wz > wz then
      let pad_nat = U64.v dst + wz * U64.v mword in
      if pad_nat < heap_size && pad_nat % U64.v mword = 0 then
        read_write_different g (U64.uint_to_t pad_nat <: hp_addr) addr 0UL
      else ()
    else ()

let zero_promote_padding_preserves_wosize
  (g: heap) (dst: obj_addr) (wz: nat)
  = let actual_wz = U64.v (wosize_of_object dst g) in
    if actual_wz > wz then
      let pad_nat = U64.v dst + wz * U64.v mword in
      if pad_nat < heap_size && pad_nat % U64.v mword = 0 then begin
        let pad_addr : hp_addr = U64.uint_to_t pad_nat in
        let hd = hd_address dst in
        hd_address_spec dst;
        // hd_address dst = dst - 8, padding is at dst + wz*8 (wz >= 1)
        // so hd < dst <= pad, meaning hd != pad
        assert (U64.v hd <> U64.v pad_addr);
        read_write_different g pad_addr hd 0UL;
        wosize_of_object_spec dst g;
        wosize_of_object_spec dst (write_word g pad_addr 0UL)
      end else ()
    else ()

let zero_promote_padding_noop
  (g: heap) (dst: obj_addr) (wz: nat)
  = ()

let zero_promote_padding_write
  (g: heap) (dst: obj_addr) (wz: nat)
  = wosize_of_object_spec dst g

let zero_promote_padding_preserves_objects
  (g: heap) (dst: obj_addr) (wz: nat)
  = let actual_wz = U64.v (wosize_of_object dst g) in
    if actual_wz > wz then begin
      // actual_wz > wz implies actual_wz >= wz + 1
      // wfh_part1_obj_bound: dst + actual_wz * 8 <= heap_size
      // so dst + wz * 8 + 8 <= heap_size, hence dst + wz * 8 < heap_size
      wfh_part1_obj_bound g dst;
      zero_promote_padding_write g dst wz;
      let pad_addr : hp_addr = U64.uint_to_t (U64.v dst + wz * U64.v mword) in
      assert (U64.v pad_addr >= U64.v dst);
      assert (U64.v pad_addr < U64.v dst + actual_wz * U64.v mword);
      write_word_preserves_objects_part1 g dst pad_addr 0UL
    end else
      zero_promote_padding_noop g dst wz

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let zero_promote_padding_frame_obj_header
  (g: heap) (dst src: obj_addr) (wz: nat)
  = let actual_wz = U64.v (wosize_of_object dst g) in
    if actual_wz <= wz then
      zero_promote_padding_noop g dst wz
    else begin
      hd_address_spec src;
      hd_address_spec dst;
      wfh_part1_obj_bound g dst;
      if U64.v src < U64.v dst then
        objects_separated zero_addr g src dst
      else begin
        objects_separated zero_addr g dst src;
        wosize_of_object_spec dst g;
        FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) (wz + 1) actual_wz
      end;
      assert (U64.v (hd_address src) <> U64.v dst + wz * U64.v mword);
      zero_promote_padding_frame g dst wz (hd_address src)
    end
#pop-options
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let zero_promote_padding_preserves_wfh_part1
  (g: heap) (dst: obj_addr) (wz: nat)
  = let g' = zero_promote_padding g dst wz in
    zero_promote_padding_preserves_objects g dst wz;
    zero_promote_padding_preserves_wosize g dst wz;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures (let wz_h = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + U64.v wz_h * 8 <= Seq.length g'))
    = assert (Seq.mem h (objects zero_addr g));
      if h = dst then begin
        assert (wosize_of_object h g' == wosize_of_object h g);
        wfh_part1_obj_bound g h
      end else begin
        hd_address_spec h;
        hd_address_spec dst;
        // Need addr <> pad_pos. Padding is at dst + wz*8.
        // hd_address h = h - 8. We need h - 8 <> dst + wz*8.
        // objects_separated gives h >= dst + wosize_of_object(dst)*8 + 8 (if h > dst)
        // or h + wosize_of_object(h)*8 + 8 <= dst (if h < dst).
        if U64.v h < U64.v dst then begin
          objects_separated zero_addr g h dst;
          // h + wosize(h)*8 + 8 <= dst, so h - 8 < h <= dst - 8 - wosize(h)*8 < dst <= dst + wz*8
          zero_promote_padding_frame g dst wz (hd_address h)
        end else begin
          objects_separated zero_addr g dst h;
          wosize_of_object_spec dst g;
          // h >= dst + wosize_of_object(dst)*8 + 8
          // hd_address h = h - 8 >= dst + wosize_of_object(dst)*8
          // padding at dst + wz*8, wosize_of_object(dst) >= wz, so pad <= dst + wosize_of_object(dst)*8
          // If wosize_of_object(dst) > wz, then pad = dst + wz*8 < dst + wosize_of_object(dst)*8 <= hd_address h
          // If wosize_of_object(dst) == wz, zero_promote_padding is identity
          let actual_wz = U64.v (wosize_of_object dst g) in
          if actual_wz <= wz then
            zero_promote_padding_noop g dst wz
          else
            zero_promote_padding_frame g dst wz (hd_address h)
        end;
        wosize_of_object_spec h g;
        wosize_of_object_spec h g';
        wfh_part1_obj_bound g h
      end
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// set_promoted_tag preserves allocator invariants
/// ---------------------------------------------------------------------------

/// Helper: set_promoted_tag preserves objects (header rewrite with same wosize)
let set_promoted_tag_preserves_objects
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256})
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
  = let hd = hd_address obj in
    let hdr = read_word major hd in
    let wz = getWosize hdr in
    getWosize_bound hdr;
    let new_hdr = makeHeader wz White (U64.uint_to_t tag) in
    read_write_different major hd addr new_hdr

/// Helper: set_promoted_tag preserves fl_valid
/// Key insight: writing to hd_address obj doesn't change any free-list link reads
/// because all field addresses (>= obj) are above hd_address obj (= obj - 8).
#push-options "--z3rlimit 10 --fuel 1"
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
        objects_separated zero_addr major fp_obj obj;
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
      assert (Seq.mem fp (objects zero_addr g'));
      wosize_of_object_spec fp_obj g';
      wosize_of_object_spec fp_obj major;
      assert (wosize_of_object fp_obj g' == wosize_of_object fp_obj major);
      AllocLemmas.fl_valid_step g' fp fuel
    end
#pop-options

/// Helper: set_promoted_tag preserves fl_chain_terminates
#push-options "--z3rlimit 10 --fuel 1"
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
        objects_separated zero_addr major (fp <: obj_addr) obj;
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
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
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
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let set_promoted_tag_preserves_alloc_invariants
  (major: heap) (obj: obj_addr) (tag: nat{tag < 256}) (fp: U64.t)
  = let fuel : nat = heap_words in
    set_promoted_tag_preserves_wfh_part1 major obj tag;
    set_promoted_tag_preserves_fl_valid major obj tag fp fuel;
    set_promoted_tag_preserves_fl_chain_terminates major obj tag fp fuel
#pop-options

/// zero_promote_padding preserves allocator invariants
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let zero_promote_padding_preserves_alloc_invariants
  (g: heap) (dst: obj_addr) (wz: nat) (fp: U64.t)
  = let fuel : nat = heap_words in
    let actual_wz = U64.v (wosize_of_object dst g) in
    zero_promote_padding_preserves_wfh_part1 g dst wz;
    zero_promote_padding_preserves_objects g dst wz;
    if actual_wz > wz then begin
      // Write case: pad_addr = dst + wz * 8
      wfh_part1_obj_bound g dst;
      zero_promote_padding_write g dst wz;
      let pad_addr : hp_addr = U64.uint_to_t (U64.v dst + wz * U64.v mword) in
      assert (U64.v pad_addr >= U64.v dst);
      assert (U64.v pad_addr < U64.v dst + actual_wz * U64.v mword);
      WriteBody.chain_avoids_implies_not_in_fl_chain g fp dst fuel;
      WriteBody.write_body_preserves_fl_valid_aux g dst pad_addr 0UL fp fuel;
      WriteBody.write_body_preserves_fl_chain_terminates g dst pad_addr 0UL fp fuel;
      WriteBody.write_body_preserves_chain_avoids_self g dst pad_addr 0UL fp fuel
    end else
      zero_promote_padding_noop g dst wz
#pop-options

/// zero_promote_padding preserves wfh_part4 (no infix objects).
/// Proof: padding writes to a field slot, never a header, so is_infix is unchanged.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let zero_promote_padding_preserves_wfh_part4
  (g: heap) (dst: obj_addr) (wz: nat)
  = let actual_wz = U64.v (wosize_of_object dst g) in
    if actual_wz > wz then begin
      wfh_part1_obj_bound g dst;
      let g' = zero_promote_padding g dst wz in
      zero_promote_padding_preserves_objects g dst wz;
      assert (objects zero_addr g' == objects zero_addr g);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(GC.Spec.Object.is_infix h g'))
      = assert (Seq.mem h (objects zero_addr g));
        hd_address_spec h;
        hd_address_spec dst;
        // pad_addr = dst + wz * 8.  hd_address h = h - 8.
        // We need: hd_address h <> pad_addr to use zero_promote_padding_frame.
        // h's header address is at h - mword.
        // pad_addr = dst + wz * mword where wz < actual_wz.
        // For h = dst: hd_address dst = dst - 8, pad_addr = dst + wz*8 >= dst > dst - 8.
        // For h <> dst: objects_separated guarantees headers don't overlap fields.
        if U64.v h > U64.v dst then begin
          objects_separated zero_addr g dst h;
          wosize_of_object_spec dst g
        end else ();
        assert (U64.v (hd_address h) <> U64.v dst + wz * U64.v mword);
        zero_promote_padding_frame g dst wz (hd_address h);
        GC.Spec.Object.tag_of_object_spec h g';
        GC.Spec.Object.tag_of_object_spec h g;
        GC.Spec.Object.is_infix_spec h g';
        GC.Spec.Object.is_infix_spec h g
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else
      zero_promote_padding_noop g dst wz
#pop-options

/// promote_object preserves allocator invariants
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let promote_object_preserves_alloc_invariants
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  = let fuel : nat = heap_words in
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
      chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
      copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
      copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wosize alloc_res.fp_out fuel;
      copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wosize alloc_res.fp_out fuel;
      // set_promoted_tag preserves invariants
      let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize in
      let tag = minor_tag minor obj in
      minor_tag_bound minor obj;
      copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
      copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wosize alloc_res.fp_out fuel;
      // zero_promote_padding preserves invariants
      zero_promote_padding_preserves_alloc_invariants copied dst_obj wosize alloc_res.fp_out;
      let padded = zero_promote_padding copied dst_obj wosize in
      set_promoted_tag_preserves_alloc_invariants padded dst_obj tag alloc_res.fp_out
    end
#pop-options

/// set_promoted_tag preserves well_formed_heap_part4 (no infix objects)
/// when the promoted tag is not infix_tag.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
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


#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let promote_object_new_addr_body_bound
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  = AllocProps.alloc_spec_obj_body_within_heap major fp wosize;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wosize
#pop-options

/// ---------------------------------------------------------------------------
/// Promote all live objects
/// ---------------------------------------------------------------------------
/// ---------------------------------------------------------------------------
/// Pointer update: rewrite minor-heap pointers in major heap
/// ---------------------------------------------------------------------------

/// Unfold lemma: one step of update_object_pointers
let update_object_pointers_step (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
                       = ()

/// Base case: identity at i >= wosize
let update_object_pointers_done (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
          = ()

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

#push-options "--z3rlimit 12"
let rewrite_roots_pointwise (roots: seq U64.t) (fwd: forwarding_map) (rs2: seq U64.t)
          =
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

/// ---------------------------------------------------------------------------
/// Correctness lemmas (matching .fsti declaration order)
/// ---------------------------------------------------------------------------

/// Helper: derive dst_fields_valid from scalar upper bound + alignment
#push-options "--z3rlimit 10"
let dst_fields_valid_from_bounds (addr: U64.t) (wz: pos)
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
#push-options "--z3rlimit 10 --fuel 2"
let copy_fields_frame
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (addr: hp_addr)
      =
  copy_fields_preserves_other minor major src_obj dst_obj i n addr
#pop-options

/// Key lemma: copy_fields correctly copies all fields (starting from index 0).
/// Proved by instantiating the internal copy_fields_preserves for each j.
#push-options "--z3rlimit 10 --fuel 2"
let copy_fields_all_correct
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (n: nat)
         =
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

/// Pointwise lemma: for a specific field j, promote_object preserves the value.
/// Takes addr as pre-computed hp_addr to avoid uint_to_t subtyping cascade in ensures.
#restart-solver
#push-options "--z3rlimit 10 --fuel 2"
let promote_preserves_field_at
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (j: nat)
  (dst_addr: U64.t) (addr: hp_addr)
  : Lemma
    (requires
      U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\
      j < wosize /\
      U64.v dst_addr % 8 == 0 /\
      U64.v dst_addr + (wosize - 1) * 8 + 8 <= heap_size /\
      U64.v addr == U64.v dst_addr + j * 8 /\
      (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
       alloc_res.obj_out == dst_addr /\
       alloc_res.obj_out <> 0UL))
    (ensures
      (let res = promote_object minor major obj fp wosize in
       read_word res.major_out addr == minor_read_field minor obj j))
  = let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    assert (alloc_res.obj_out == dst_addr);
    promote_object_success minor major obj fp wosize;
    dst_fields_valid_from_bounds dst_addr wosize;
    copy_fields_all_correct minor alloc_res.heap_out obj dst_addr wosize;
    let copied = copy_fields minor alloc_res.heap_out obj dst_addr 0 wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    (if U64.v dst_addr < U64.v mword then
      FStar.Math.Lemmas.small_mod (U64.v dst_addr) (U64.v mword)
     else ());
    let dst_obj : obj_addr = dst_addr in
    let padded = zero_promote_padding copied dst_obj wosize in
    FStar.Math.Lemmas.lemma_mult_le_right 8 j (wosize - 1);
    assert (U64.v dst_obj + j * 8 + 8 <= heap_size);
    hd_address_spec dst_obj;
    assert (j * 8 < wosize * 8);
    assert (U64.v addr <> U64.v dst_obj + wosize * U64.v mword);
    zero_promote_padding_frame copied dst_obj wosize addr;
    set_promoted_tag_read_frame padded dst_obj tag addr
#pop-options

/// After promote_object, if allocation succeeds AND the destination
/// has valid bounds, all field data is preserved.
#push-options "--z3rlimit 10 --fuel 0"
let promote_preserves_fields
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
                =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    promote_object_success minor major obj fp wosize;
    if U64.v alloc_res.obj_out % 8 = 0 &&
       U64.v alloc_res.obj_out + (wosize - 1) * 8 + 8 <= heap_size then begin
      dst_fields_valid_from_bounds alloc_res.obj_out wosize;
      // step: postcondition as implication (guards U64.uint_to_t well-formedness)
      let step (j: nat) : Lemma
        (j < wosize ==>
         (let res = promote_object minor major obj fp wosize in
          read_word res.major_out (U64.uint_to_t (U64.v res.new_addr + j * 8))
          == minor_read_field minor obj j))
      = if j < wosize then begin
          FStar.Math.Lemmas.lemma_mult_le_right 8 j (wosize - 1);
          let addr : hp_addr = U64.uint_to_t (U64.v alloc_res.obj_out + j * 8) in
          promote_preserves_field_at minor major obj fp wosize j alloc_res.obj_out addr
        end
      in
      FStar.Classical.forall_intro step
    end else ()
  end
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let promote_object_extra_field_not_pointer
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wz: nat{wz > 0}) (field_idx: nat)
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  let res = promote_object minor major obj fp wz in
  promote_object_success minor major obj fp wz;
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let padded = zero_promote_padding copied dst_obj wz in
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  let field_addr : hp_addr =
    U64.uint_to_t (U64.v dst_obj + field_idx * U64.v mword) in
  hd_address_spec dst_obj;
  set_promoted_tag_read_frame padded dst_obj tag field_addr;
  AllocProps.alloc_spec_obj_wosize_upper_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  let hd_dst = hd_address dst_obj in
  copy_fields_frame minor alloc_res.heap_out obj dst_obj 0 wz hd_dst;
  wosize_of_object_spec dst_obj copied;
  wosize_of_object_spec dst_obj alloc_res.heap_out;
  assert (wosize_of_object dst_obj copied ==
          wosize_of_object dst_obj alloc_res.heap_out);
  assert (U64.v (wosize_of_object dst_obj copied) <= wz + 1);
  zero_promote_padding_preserves_wosize copied dst_obj wz;
  assert (U64.v (wosize_of_object dst_obj padded) <= wz + 1);
  set_promoted_tag_unfold padded dst_obj tag;
  assert (U64.v hd_dst <> U64.v dst_obj + wz * U64.v mword);
  zero_promote_padding_frame copied dst_obj wz hd_dst;
  let new_hdr =
    makeHeader (getWosize (read_word padded hd_dst)) White (U64.uint_to_t tag) in
  read_write_same padded hd_dst new_hdr;
  wosize_of_object_spec dst_obj res.major_out;
  makeHeader_getWosize (getWosize (read_word padded hd_dst)) White (U64.uint_to_t tag);
  wosize_of_object_spec dst_obj padded;
  assert (wosize_of_object dst_obj res.major_out == wosize_of_object dst_obj padded);
  assert (U64.v (wosize_of_object dst_obj res.major_out) <= wz + 1);
  assert (field_idx == wz);
  let pad_nat = U64.v dst_obj + wz * U64.v mword in
  assert (pad_nat == U64.v field_addr);
  assert (pad_nat < heap_size);
  assert (pad_nat % U64.v mword == 0);
  assert (U64.v (wosize_of_object dst_obj copied) > wz);
  zero_promote_padding_write copied dst_obj wz;
  let pad_hp : hp_addr = U64.uint_to_t pad_nat in
  assert (pad_hp == field_addr);
  assert (padded == write_word copied pad_hp 0UL);
  read_write_same copied pad_hp 0UL;
  assert (read_word padded field_addr == 0UL);
  assert (read_word res.major_out field_addr == read_word padded field_addr);
  assert (read_word res.major_out field_addr == 0UL)
#pop-options

/// ---------------------------------------------------------------------------
/// copy_fields preserves heap structure — delegated to WriteBodyLemmas module
/// ---------------------------------------------------------------------------
/// Bridge: chain_avoids (bool) implies not_in_fl_chain (prop).
let chain_avoids_implies_not_in_fl_chain = WriteBody.chain_avoids_implies_not_in_fl_chain
/// copy_fields_preserves_* aliases
private let copy_fields_preserves_objects_aux = WriteBody.copy_fields_preserves_objects_aux
private let copy_fields_preserves_wfh_part1 = WriteBody.copy_fields_preserves_wfh_part1
/// promote_object preserves existing object membership.
/// Composite lemma: copy_fields preserves all allocator invariants together.
/// promote_object preserves objects (part1 version — no full well_formed_heap needed)
#push-options "--z3rlimit 10 --fuel 1"
let promote_object_preserves_objects_part1
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
                =
  let fuel : nat = heap_words in
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
    // zero_promote_padding and set_promoted_tag preserve objects
    let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
    zero_promote_padding_preserves_objects copied dst_obj wosize;
    let padded = zero_promote_padding copied dst_obj wosize in
    set_promoted_tag_preserves_objects padded dst_obj tag;
    assert (objects zero_addr (set_promoted_tag padded dst_obj tag) ==
            objects zero_addr copied)
  end
#pop-options

/// promote_all preserves well_formed_heap_part1
/// copy_fields preserves well_formed_heap_part4 (no infix objects).
/// Since copy_fields only writes to field addresses (>= dst_obj), no headers change.
#push-options "--z3rlimit 10 --fuel 0"
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
      objects_separated zero_addr major dst_obj h;
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

/// promote_object preserves well_formed_heap_part4 when tag is not infix_tag.
/// Combines alloc_spec, copy_fields, zero_promote_padding, set_promoted_tag part4 preservation.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let promote_object_preserves_wfh_part4
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  = let fuel : nat = heap_words in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    if alloc_res.obj_out = 0UL then begin
      promote_object_oom minor major obj fp wosize
    end else begin
      GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
      let dst_obj : obj_addr = alloc_res.obj_out in
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
      AllocLemmas.alloc_spec_preserves_wfh_part4 major fp wosize;
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize;
      GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
      GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
      AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
      chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
      copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
      copy_fields_preserves_wfh_part4 minor alloc_res.heap_out obj dst_obj wosize;
      let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize in
      let tag = minor_tag minor obj in
      minor_tag_bound minor obj;
      copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
      assert (Seq.mem dst_obj (objects zero_addr copied));
      zero_promote_padding_preserves_objects copied dst_obj wosize;
      zero_promote_padding_preserves_wfh_part1 copied dst_obj wosize;
      zero_promote_padding_preserves_wfh_part4 copied dst_obj wosize;
      let padded = zero_promote_padding copied dst_obj wosize in
      assert (Seq.mem dst_obj (objects zero_addr padded));
      set_promoted_tag_preserves_wfh_part4 padded dst_obj tag
    end
#pop-options

/// promote_all_aux preserves well_formed_heap_part4 (no infix objects).
/// Top-level: promote_all_spec preserves well_formed_heap_part4
/// ---------------------------------------------------------------------------
/// promote_all_spec preserves no_scan_invariant
/// ---------------------------------------------------------------------------

/// Helper: for a non-blue, no-scan object src != dst_obj in the post-promote
/// heap, its field reads are unchanged from the original heap.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let promote_object_frame_old_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (idx: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp src heap_words = true /\
      (src <> (GC.Spec.Allocator.alloc_spec major fp wz).obj_out) /\
      idx < U64.v (wosize_of_object src major) /\
      U64.v src + idx * 8 + 8 <= heap_size)
    (ensures
      (let res = promote_object minor major obj fp wz in
       let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
       read_word res.major_out field_addr == read_word major field_addr))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  // Derive alloc_res.obj_out <> 0UL from promote_object.new_addr <> 0UL (contrapositive of oom)
  (if alloc_res.obj_out = 0UL then promote_object_oom minor major obj fp wz else ());
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  let fuel : nat = heap_words in
  let field_addr : hp_addr = U64.uint_to_t (U64.v src + idx * 8) in
  // 1. alloc preserves body reads of src (chain_avoids ensures src not in free list)
  AllocLemmas.alloc_spec_read_other major fp wz src field_addr;
  assert (read_word alloc_res.heap_out field_addr == read_word major field_addr);
  // 2. copy_fields preserves reads outside [dst_obj, dst_obj + (wz-1)*8]
  // src != dst_obj, so by objects_separated, their bodies are disjoint
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  objects_separated zero_addr alloc_res.heap_out src dst_obj;
  objects_separated zero_addr alloc_res.heap_out dst_obj src;
  wosize_of_object_spec src alloc_res.heap_out;
  wosize_of_object_spec src major;
  AllocProps.alloc_spec_read_header_other_part1 major fp wz src;
  assert (read_word alloc_res.heap_out (hd_address src) == read_word major (hd_address src));
  assert (wosize_of_object src alloc_res.heap_out == wosize_of_object src major);
  hd_address_spec dst_obj;
  hd_address_spec src;
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  // Bridge for copy_fields_preserves_other: prove separation of field_addr from dst body
  assert (U64.v field_addr = U64.v src + idx * 8);
  assert (U64.v (wosize_of_object dst_obj alloc_res.heap_out) >= wz);
  assert (U64.v dst_obj + wz * 8 <= heap_size);
  if U64.v src < U64.v dst_obj then begin
    // field_addr < src + wosize*8 <= dst_obj, so field_addr + 8 <= dst_obj
    assert (U64.v dst_obj > U64.v src + U64.v (wosize_of_object_as_wosize src alloc_res.heap_out) * 8);
    // wosize_of_object_as_wosize = wosize_of_object (by definition)
    assert (U64.v (wosize_of_object src alloc_res.heap_out) = U64.v (wosize_of_object_as_wosize src alloc_res.heap_out));
    // idx < wosize(src, major) = wosize(src, heap_out), so field_addr < src + wosize*8 < dst_obj
    assert (U64.v field_addr < U64.v dst_obj);
    // Both 8-aligned, so field_addr + 8 <= dst_obj
    assert (U64.v field_addr % 8 == 0);
    assert (U64.v dst_obj % 8 == 0);
    assert (U64.v field_addr + 8 <= U64.v dst_obj);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz field_addr
  end else begin
    // src > dst_obj + wosize(dst_obj)*8 >= dst_obj + wz*8, so field_addr >= src > dst_obj + wz*8
    assert (U64.v src > U64.v dst_obj + U64.v (wosize_of_object_as_wosize dst_obj alloc_res.heap_out) * 8);
    assert (U64.v field_addr >= U64.v src);
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz field_addr
  end;
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  assert (read_word copied field_addr == read_word alloc_res.heap_out field_addr);
  // 3. zero_promote_padding only writes at dst_obj + wz*8, disjoint from field_addr
  //    (field_addr is in src's body, which is disjoint from dst_obj's body by objects_separated)
  let pad_nat = U64.v dst_obj + wz * U64.v mword in
  assert (U64.v field_addr <> pad_nat);
  zero_promote_padding_frame copied dst_obj wz field_addr;
  let padded = zero_promote_padding copied dst_obj wz in
  // 4. set_promoted_tag only writes at hd_address dst_obj
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_read_frame padded dst_obj tag field_addr
#pop-options

/// Helper: for a non-blue, no-scan object src != dst_obj, its header is
/// unchanged from the original heap (so is_no_scan, is_blue, wosize are same).
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let promote_object_frame_old_header
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      (let res = promote_object minor major obj fp wz in
       res.new_addr <> 0UL) /\
      Seq.mem src (objects zero_addr major) /\
      (src <> (GC.Spec.Allocator.alloc_spec major fp wz).obj_out))
    (ensures
      (let res = promote_object minor major obj fp wz in
       read_word res.major_out (hd_address src) == read_word major (hd_address src)))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  (if alloc_res.obj_out = 0UL then promote_object_oom minor major obj fp wz else ());
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  // 1. alloc preserves header of src
  AllocProps.alloc_spec_read_header_other_part1 major fp wz src;
  assert (read_word alloc_res.heap_out (hd_address src) == read_word major (hd_address src));
  // 2. copy_fields doesn't change headers (writes only at dst body positions)
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  hd_address_spec src;
  hd_address_spec dst_obj;
  wfh_part1_obj_bound alloc_res.heap_out dst_obj;
  objects_separated zero_addr alloc_res.heap_out src dst_obj;
  objects_separated zero_addr alloc_res.heap_out dst_obj src;
  copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz (hd_address src);
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  assert (read_word copied (hd_address src) == read_word alloc_res.heap_out (hd_address src));
  // 3. zero_promote_padding preserves header of src (src <> dst_obj)
  copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  zero_promote_padding_frame_obj_header copied dst_obj src wz;
  let padded = zero_promote_padding copied dst_obj wz in
  // 4. set_promoted_tag writes at hd_address dst_obj, not at hd_address src
  let tag = minor_tag minor obj in
  minor_tag_bound minor obj;
  set_promoted_tag_read_frame padded dst_obj tag (hd_address src)
#pop-options

/// Per-step: promote_object preserves no_scan_invariant
///
/// Proof outline:
/// - OOM case: promote_object returns original heap, invariant preserved trivially
/// - Success case (new_addr ≠ 0): use no_scan_invariant_intro.  For each (src, idx):
///     * src ≠ dst: header/field reads unchanged (frame lemmas) → original invariant
///     * src = dst, idx < wz: copy_fields_all_correct + minor_no_scan_invariant
///     * src = dst, idx ≥ wz: leftover=1 allocator padding (see assume below)
///
/// The alloc_from_block non-split case can give wosize = wz+1, leaving one
/// uninitialized padding field.  This assume discharges the padding obligation;
/// it can be eliminated by either (a) zeroing the padding word in promote_object
/// or (b) restricting the allocator to exact-fit only.

/// Helper for new-object case: fields of the promoted object are non-pointer
/// when the object is no_scan.
#push-options "--z3rlimit 75 --fuel 0 --ifuel 0"
private let promote_no_scan_new_object
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (field_idx: nat)
  : Lemma
    (requires (
      let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
      alloc_res.obj_out <> 0UL /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp heap_words /\
      AllocLemmas.fl_chain_terminates major fp heap_words /\
      minor_no_scan_invariant minor /\
      Seq.mem obj (minor_objects minor) /\
      wz == minor_wosize minor obj /\
      minor_tag minor obj < 256 /\
      (U64.v alloc_res.obj_out >= U64.v mword /\
       U64.v alloc_res.obj_out < heap_size /\
       U64.v alloc_res.obj_out % U64.v mword == 0) /\
      (let dst_obj : obj_addr = alloc_res.obj_out in
       let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
       let padded = zero_promote_padding copied dst_obj wz in
       let tag = minor_tag minor obj in
       let g' = set_promoted_tag padded dst_obj tag in
       is_no_scan dst_obj g' /\
       field_idx < U64.v (wosize_of_object dst_obj g') /\
       U64.v dst_obj + field_idx * 8 < heap_size)))
    (ensures (
      let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
      let dst_obj : obj_addr = alloc_res.obj_out in
      let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
      let padded = zero_promote_padding copied dst_obj wz in
      let tag = minor_tag minor obj in
      let g' = set_promoted_tag padded dst_obj tag in
      let field_addr : hp_addr = U64.uint_to_t (U64.v dst_obj + field_idx * 8) in
      ~(is_pointer_field (read_word g' field_addr))))
  =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let padded = zero_promote_padding copied dst_obj wz in
  let tag = minor_tag minor obj in
  let g' = set_promoted_tag padded dst_obj tag in
  let field_addr : hp_addr = U64.uint_to_t (U64.v dst_obj + field_idx * 8) in
  // set_promoted_tag only writes the header; field reads are unchanged
  hd_address_spec dst_obj;
  set_promoted_tag_read_frame padded dst_obj tag field_addr;
  // So read_word g' field_addr == read_word padded field_addr
  if field_idx < wz then begin
    // zero_promote_padding frame: padding is at dst + wz*8, field is at dst + field_idx*8
    // field_idx < wz, so these are different
    assert (U64.v field_addr <> U64.v dst_obj + wz * U64.v mword);
    zero_promote_padding_frame copied dst_obj wz field_addr;
    // So read_word padded field_addr == read_word copied field_addr
    // Now the original proof for field_idx < wz applies to copied
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    wfh_part1_obj_bound alloc_res.heap_out dst_obj;
    dst_fields_valid_from_bounds (dst_obj <: U64.t) wz;
    copy_fields_all_correct minor alloc_res.heap_out obj dst_obj wz;
    assert (read_word copied field_addr == minor_read_field minor obj field_idx);
    // Derive minor_tag minor obj >= 251 from is_no_scan dst_obj g'
    set_promoted_tag_unfold padded dst_obj tag;
    let hdr_addr = hd_address dst_obj in
    zero_promote_padding_preserves_wosize copied dst_obj wz;
    assert (U64.v hdr_addr <> U64.v dst_obj + wz * U64.v mword);
    zero_promote_padding_frame copied dst_obj wz hdr_addr;
    let new_hdr = makeHeader (getWosize (read_word padded hdr_addr)) White (U64.uint_to_t tag) in
    read_write_same padded hdr_addr new_hdr;
    assert (read_word g' hdr_addr == new_hdr);
    tag_of_object_spec dst_obj g';
    makeHeader_getTag (getWosize (read_word padded hdr_addr)) White (U64.uint_to_t tag);
    assert (tag_of_object dst_obj g' == U64.uint_to_t tag);
    is_no_scan_spec dst_obj g';
    no_scan_tag_val ();
    assert (minor_tag minor obj >= 251);
    // Now use minor_no_scan_invariant
    assert (field_idx < minor_wosize minor obj);
    ()
  end else begin
    // field_idx >= wz: the padding field was zeroed by zero_promote_padding
    // read_word g' field_addr == read_word padded field_addr (from set_promoted_tag_read_frame above)
    // The padding position is dst_obj + wz * 8
    // Since field_idx >= wz and field_idx < actual_wz, and actual_wz <= wz+1 from allocator,
    // field_idx == wz. So field_addr is exactly the padding position.
    assert (field_idx >= wz);
    // Prove field_idx == wz using allocator upper bound on wosize
    AllocProps.alloc_spec_obj_wosize_upper_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    // wosize_of_object dst_obj alloc_res.heap_out <= wz + 1
    // Now show wosize is preserved through copy_fields
    let hd_dst = hd_address dst_obj in
    hd_address_spec dst_obj;
    copy_fields_preserves_other minor alloc_res.heap_out obj dst_obj 0 wz hd_dst;
    // read_word copied hd_dst == read_word alloc_res.heap_out hd_dst
    wosize_of_object_spec dst_obj copied;
    wosize_of_object_spec dst_obj alloc_res.heap_out;
    assert (wosize_of_object dst_obj copied == wosize_of_object dst_obj alloc_res.heap_out);
    assert (U64.v (wosize_of_object dst_obj copied) <= wz + 1);
    // Through zero_promote_padding
    zero_promote_padding_preserves_wosize copied dst_obj wz;
    assert (U64.v (wosize_of_object dst_obj padded) <= wz + 1);
    // Through set_promoted_tag
    set_promoted_tag_unfold padded dst_obj tag;
    let hdr_addr2 = hd_address dst_obj in
    assert (U64.v hdr_addr2 <> U64.v dst_obj + wz * U64.v mword);
    zero_promote_padding_frame copied dst_obj wz hdr_addr2;
    // set_promoted_tag preserves wosize
    let new_hdr = makeHeader (getWosize (read_word padded hdr_addr2)) White (U64.uint_to_t tag) in
    read_write_same padded hdr_addr2 new_hdr;
    wosize_of_object_spec dst_obj g';
    makeHeader_getWosize (getWosize (read_word padded hdr_addr2)) White (U64.uint_to_t tag);
    wosize_of_object_spec dst_obj padded;
    assert (wosize_of_object dst_obj g' == wosize_of_object dst_obj padded);
    assert (U64.v (wosize_of_object dst_obj g') <= wz + 1);
    // Combined with field_idx >= wz and field_idx < wosize_of_object dst_obj g':
    assert (field_idx == wz);
    // Now field_addr == dst_obj + wz * 8 = padding address
    let pad_nat = U64.v dst_obj + wz * U64.v mword in
    assert (pad_nat == U64.v field_addr);
    assert (pad_nat < heap_size);
    assert (pad_nat % U64.v mword == 0);
    // zero_promote_padding wrote 0UL at pad_nat (since actual_wz > wz)
    assert (U64.v (wosize_of_object dst_obj copied) > wz);
    zero_promote_padding_write copied dst_obj wz;
    let pad_hp : hp_addr = U64.uint_to_t pad_nat in
    assert (pad_hp == field_addr);
    assert (padded == write_word copied pad_hp 0UL);
    read_write_same copied pad_hp 0UL;
    assert (read_word padded field_addr == 0UL);
    assert (~(is_pointer_field (read_word padded field_addr)));
    ()
  end
#pop-options

/// Helper for old-object case: fields of pre-existing objects are non-pointer
/// when the object is no_scan (frame lemma through promote_object).
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let promote_no_scan_old_object
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  (src: obj_addr) (field_idx: nat)
  : Lemma
    (requires (
      let fuel : nat = heap_words in
      let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
      alloc_res.obj_out <> 0UL /\
      no_scan_invariant major /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp fuel /\
      AllocLemmas.fl_chain_terminates major fp fuel /\
      allocated_avoid_chain major fp /\
      minor_tag minor obj < 256 /\
      (U64.v alloc_res.obj_out >= U64.v mword /\
       U64.v alloc_res.obj_out < heap_size /\
       U64.v alloc_res.obj_out % U64.v mword == 0) /\
      (let dst_obj : obj_addr = alloc_res.obj_out in
       let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
       let padded = zero_promote_padding copied dst_obj wz in
       let tag = minor_tag minor obj in
       let g' = set_promoted_tag padded dst_obj tag in
       (src <: U64.t) <> (dst_obj <: U64.t) /\
       Seq.mem src (objects zero_addr g') /\
       is_no_scan src g' /\
       ~(is_blue src g') /\
       field_idx < U64.v (wosize_of_object src g') /\
       U64.v src + field_idx * 8 < heap_size /\
       objects zero_addr g' == objects zero_addr alloc_res.heap_out /\
       dst_fields_valid dst_obj wz /\
       well_formed_heap_part1 alloc_res.heap_out /\
       Seq.mem dst_obj (objects zero_addr alloc_res.heap_out))))
    (ensures (
      let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
      let dst_obj : obj_addr = alloc_res.obj_out in
      let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
      let padded = zero_promote_padding copied dst_obj wz in
      let tag = minor_tag minor obj in
      let g' = set_promoted_tag padded dst_obj tag in
      let field_addr : hp_addr = U64.uint_to_t (U64.v src + field_idx * 8) in
      ~(is_pointer_field (read_word g' field_addr))))
  =
  let fuel : nat = heap_words in
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
  AllocProps.alloc_spec_obj_valid major fp wz;
  let dst_obj : obj_addr = alloc_res.obj_out in
  let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
  let padded = zero_promote_padding copied dst_obj wz in
  let tag = minor_tag minor obj in
  let g' = set_promoted_tag padded dst_obj tag in
  let field_addr : hp_addr = U64.uint_to_t (U64.v src + field_idx * 8) in
  // Frame through set_promoted_tag: hd_address(src) ≠ hd_address(dst_obj)
  hd_address_spec src;
  hd_address_spec dst_obj;
  hd_address_injective src dst_obj;
  hdr_pair_disjoint src dst_obj (U64.v (hd_address src)) (U64.v (hd_address dst_obj));
  set_promoted_tag_read_frame padded dst_obj tag (hd_address src);
  // Frame through zero_promote_padding: use frame_obj_header since src ≠ dst_obj
  AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
  assert (well_formed_heap_part1 alloc_res.heap_out);
  AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
  AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
  WriteBody.copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
  WriteBody.copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
  // Now: well_formed_heap_part1 copied, objects zero_addr copied == objects zero_addr alloc_res.heap_out
  zero_promote_padding_frame_obj_header copied dst_obj src wz;
  // Frame through copy_fields: hd_address(src) outside [dst_obj, dst_obj + wz*8)
  if U64.v src < U64.v dst_obj then
    copy_fields_frame minor alloc_res.heap_out obj dst_obj 0 wz (hd_address src)
  else begin
    objects_separated zero_addr alloc_res.heap_out dst_obj src;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    copy_fields_frame minor alloc_res.heap_out obj dst_obj 0 wz (hd_address src)
  end;
  // header(src) same in g' and alloc_res.heap_out → same in g' and major
  color_of_object_spec src g';
  color_of_object_spec src alloc_res.heap_out;
  is_blue_iff src g';
  is_blue_iff src alloc_res.heap_out;
  // src ∈ objects(major) by contrapositive of alloc_spec_new_objects_blue_part1
  AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wz;
  assert (Seq.mem src (objects zero_addr major));
  // Use promote_object_frame_old_header
  promote_object_frame_old_header minor major obj fp wz src;
  is_no_scan_spec src g';
  is_no_scan_spec src major;
  tag_of_object_spec src g';
  tag_of_object_spec src major;
  is_blue_iff src major;
  color_of_object_spec src major;
  wosize_of_object_spec src g';
  wosize_of_object_spec src major;
  // Bounds
  wfh_part1_obj_bound major src;
  FStar.Math.Lemmas.lemma_mult_le_right 8 (field_idx + 1) (U64.v (wosize_of_object src major));
  // Field reads unchanged
  promote_object_frame_old_field minor major obj fp wz src field_idx;
  // Original invariant
  no_scan_invariant_elim major src field_idx
#pop-options

/// Main proof: promote_object preserves no_scan_invariant
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let promote_object_preserves_no_scan_invariant
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  =
  let fuel : nat = heap_words in
  let res = promote_object minor major obj fp wz in
  if res.new_addr = 0UL then begin
    promote_object_oom minor major obj fp wz;
    assert (res.major_out == major)
  end else begin
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
    (if alloc_res.obj_out = 0UL then promote_object_oom minor major obj fp wz else ());
    AllocProps.alloc_spec_obj_valid major fp wz;
    let dst_obj : obj_addr = alloc_res.obj_out in
    promote_object_success minor major obj fp wz;
    let copied = copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
    let padded = zero_promote_padding copied dst_obj wz in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    let g' = res.major_out in
    assert (g' == set_promoted_tag padded dst_obj tag);
    // Shared facts
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    wfh_part1_obj_bound alloc_res.heap_out dst_obj;
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
    // zero_promote_padding preserves objects (only writes a field, not a header)
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
    zero_promote_padding_preserves_objects copied dst_obj wz;
    zero_promote_padding_preserves_wosize copied dst_obj wz;
    set_promoted_tag_preserves_objects padded dst_obj tag;
    assert (objects zero_addr g' == objects zero_addr alloc_res.heap_out);
    dst_fields_valid_from_bounds (dst_obj <: U64.t) wz;
    // Prove the universal for no_scan_invariant_intro
    let aux (src: obj_addr) (field_idx: nat) : Lemma
      (ensures (
        Seq.mem src (objects zero_addr g') /\
        is_no_scan src g' /\
        ~(is_blue src g') /\
        field_idx < U64.v (wosize_of_object src g') /\
        U64.v src + field_idx * 8 < heap_size ==>
        (let field_addr : hp_addr = U64.uint_to_t (U64.v src + field_idx * 8) in
         ~(is_pointer_field (read_word g' field_addr)))))
    = if Seq.mem src (objects zero_addr g') &&
         is_no_scan src g' &&
         not (is_blue src g') &&
         field_idx < U64.v (wosize_of_object src g') &&
         U64.v src + field_idx * 8 < heap_size then
        if (src <: U64.t) = (dst_obj <: U64.t) then
          promote_no_scan_new_object minor major obj fp wz field_idx
        else
          promote_no_scan_old_object minor major obj fp wz src field_idx
      else ()
    in
    Classical.forall_intro_2 aux;
    no_scan_invariant_intro g'
  end
#pop-options

/// Helper: promote_object preserves allocated_avoid_chain.
/// Every non-blue object in the post-promote heap avoids the new free-list chain.
/// Inductive: promote_all_aux preserves no_scan_invariant
/// ---------------------------------------------------------------------------
/// fields_match_minor intro/elim lemmas (predicate is opaque_to_smt, recursive)
/// ---------------------------------------------------------------------------
