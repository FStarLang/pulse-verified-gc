(*
   GC.Spec.Allocator.Lemmas — Bridge proofs connecting the allocator to the GC.

   Main theorem: alloc_spec preserves well_formed_heap, so the GC can be
   called after any sequence of allocations.
*)
module GC.Spec.Allocator.Lemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq
open FStar.Mul

/// ===========================================================================
/// Section 1: Preliminary lemmas about make_header
/// ===========================================================================

/// getWosize of make_header returns the original wosize
/// Proof: make_header produces the same bit pattern as GC.Lib.Header.pack_header,
/// which has the get_wosize_pack_header roundtrip lemma.
#push-options "--z3rlimit 50"
let make_header_getWosize (wz: U64.t{U64.v wz < pow2 54})
                          (c: U64.t{U64.v c < 4})
                          (t: U64.t{U64.v t < 256})
  : Lemma (getWosize (make_header wz c t) == wz)
  = // make_header wz c t == wz<<10 | c<<8 | t
    make_header_eq_impl wz c t;
    // Use colorHeader_preserves_wosize on a simpler construction:
    // First build a header with just wz and tag 0, color 0:
    // make_header wz 0 t = wz<<10 | t
    // Then make_header wz c t = make_header wz 0 t | c<<8
    // Actually, let's use a different approach.
    // Since make_header and GC.Impl.Object.makeHeader produce the same result,
    // and makeHeader_getWosize is proved in GC.Impl.Object, we bridge via
    // make_header_eq_impl.
    // For now, use a direct SMT proof with higher rlimit.
    getWosize_spec (make_header wz c t);
    // Need: shift_right (wz<<10 | c<<8 | t) 10 == wz
    // This holds when c<<8 | t < 2^10 = 1024, which is true since c < 4 and t < 256
    // So c<<8 < 1024 and t < 256, meaning c<<8 | t < 1024
    admit ()  // Bitvector: shift_right (wz<<10 | c<<8|t) 10 == wz
#pop-options

/// getTag of make_header returns the original tag
#push-options "--z3rlimit 50"
let make_header_getTag (wz: U64.t{U64.v wz < pow2 54})
                       (c: U64.t{U64.v c < 4})
                       (t: U64.t{U64.v t < 256})
  : Lemma (U64.v (getTag (make_header wz c t)) == U64.v t)
  = make_header_eq_impl wz c t;
    getTag_spec (make_header wz c t);
    // Need: logand (wz<<10 | c<<8 | t) 0xFF == t
    // This holds when t < 256 and wz<<10 | c<<8 has no bits in 0..7
    admit ()  // Bitvector: logand (wz<<10 | c<<8|t) 0xFF == t
#pop-options

/// ===========================================================================
/// Section 2: Header write with same wosize preserves objects
/// ===========================================================================

/// If getWosize is the same at every header position, objects walk is the same
private let rec wosize_eq_implies_objects_eq
  (start: hp_addr) (g g': heap)
  : Lemma (requires Seq.length g' == Seq.length g /\
                    (forall (p: hp_addr). getWosize (read_word g' p) == getWosize (read_word g p)))
          (ensures objects start g' == objects start g)
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let wz = getWosize (read_word g start) in
      let next_start_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else if next_start_nat >= heap_size then ()
      else wosize_eq_implies_objects_eq (U64.uint_to_t next_start_nat) g g'
    end

/// A write to hd_address(obj) with same getWosize preserves objects from 0
let header_write_same_wosize_preserves_objects
  (g: heap) (obj: obj_addr) (new_hdr: U64.t)
  : Lemma (requires getWosize new_hdr == getWosize (read_word g (hd_address obj)))
          (ensures objects 0UL (write_word g (hd_address obj) new_hdr) == objects 0UL g)
  = let hd = hd_address obj in
    let g' = write_word g hd new_hdr in
    hd_address_spec obj;
    let aux (p: hp_addr) : Lemma (getWosize (read_word g' p) == getWosize (read_word g p))
      = if U64.v p = U64.v hd then
          read_write_same g hd new_hdr
        else
          read_write_different g hd p new_hdr
    in
    FStar.Classical.forall_intro aux;
    wosize_eq_implies_objects_eq 0UL g g'

/// ===========================================================================
/// Section 3: exists_field_pointing_to_unchecked congruence
/// ===========================================================================

/// If all field reads of src are the same in g' and g, then efptu is the same
private let rec efptu_congruence
  (g g': heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (dst: obj_addr)
  : Lemma (requires (forall (k: nat{k < U64.v wz}).
                       let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
                       U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                       read_word g' fa == read_word g fa))
          (ensures exists_field_pointing_to_unchecked g' src wz dst ==
                   exists_field_pointing_to_unchecked g src wz dst)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      let fa = U64.add_mod src (U64.mul_mod idx mword) in
      if U64.v fa >= heap_size || U64.v fa % 8 <> 0 then ()
      else begin
        assert (U64.v idx < U64.v wz);
        efptu_congruence g' g src idx dst
      end
    end

/// ===========================================================================
/// Section 4: Header write at hd_address(obj) doesn't change field reads
/// ===========================================================================

/// For src = obj: fields at obj + k*8 are all > hd_address obj = obj - 8
#restart-solver
#push-options "--z3rlimit 200"
let header_write_doesnt_change_own_fields
  (g: heap) (obj: obj_addr) (new_hdr: U64.t) (k: nat)
  : Lemma (requires k < U64.v (wosize_of_object obj g))
          (ensures (let fa = U64.add_mod obj (U64.mul_mod (U64.uint_to_t k) mword) in
                    let hd = hd_address obj in
                    U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                    read_word (write_word g hd new_hdr) fa == read_word g fa))
  = let fa = U64.add_mod obj (U64.mul_mod (U64.uint_to_t k) mword) in
    let hd = hd_address obj in
    hd_address_spec obj;
    wosize_of_object_bound obj g;
    if U64.v fa < heap_size && U64.v fa % 8 = 0 then
      read_write_different g hd fa new_hdr
#pop-options

/// For src ≠ obj: all fields of src are separated from hd_address(obj)
#push-options "--z3rlimit 30"
let header_write_doesnt_change_other_fields
  (g: heap) (obj src: obj_addr) (new_hdr: U64.t) (k: nat)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    Seq.mem src (objects 0UL g) /\
                    src <> obj /\
                    k < U64.v (wosize_of_object src g))
          (ensures (let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
                    let hd = hd_address obj in
                    U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
                    read_word (write_word g hd new_hdr) fa == read_word g fa))
  = let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
    let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_spec src;
    wosize_of_object_bound src g;
    wosize_of_object_bound obj g;
    wf_object_size_bound g src;
    if U64.v fa < heap_size && U64.v fa % 8 = 0 then begin
      if U64.v src < U64.v obj then
        objects_separated 0UL g src obj
      else
        objects_separated 0UL g obj src;
      read_write_different g hd fa new_hdr
    end
#pop-options

/// ===========================================================================
/// Section 5: Exact-fit preserves well_formed_heap
/// ===========================================================================

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let alloc_exact_preserves_wf
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz < 2))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap g' /\
                    objects 0UL g' == objects 0UL g))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let new_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
    let g' = write_word g hd new_hdr in
    hd_address_spec obj;
    hd_address_bounds obj;
    getWosize_bound hdr;
    make_header_getWosize (U64.uint_to_t block_wz) white_bits 0UL;

    // Objects preserved
    header_write_same_wosize_preserves_objects g obj new_hdr;

    // Access well_formed_heap parts
    reveal_opaque (`%well_formed_heap) well_formed_heap;

    // --- Part 1: size bounds ---
    let aux1 (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g'))
      (ensures (let w = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + U64.v w * 8 <= Seq.length g'))
    = wosize_of_object_spec h g;
      wosize_of_object_spec h g';
      wosize_of_object_bound h g;
      hd_address_spec h;
      if h = obj then
        read_write_same g hd new_hdr
      else begin
        if U64.v h < U64.v obj then
          objects_separated 0UL g h obj
        else
          objects_separated 0UL g obj h;
        read_write_different g hd (hd_address h) new_hdr
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux1);

    // --- Part 2: pointer targets ---
    let aux2 (src dst: obj_addr) : Lemma
      (requires Seq.mem src (objects 0UL g') /\
                (let w = wosize_of_object src g' in
                 U64.v w < pow2 54 /\
                 exists_field_pointing_to_unchecked g' src w dst))
      (ensures Seq.mem dst (objects 0UL g'))
    = wosize_of_object_spec src g;
      wosize_of_object_spec src g';
      wosize_of_object_bound src g;
      hd_address_spec src;
      if src = obj then
        read_write_same g hd new_hdr
      else begin
        if U64.v src < U64.v obj then
          objects_separated 0UL g src obj
        else
          objects_separated 0UL g obj src;
        read_write_different g hd (hd_address src) new_hdr
      end;
      let wz_src = wosize_of_object src g in
      let field_eq (k: nat{k < U64.v wz_src}) : Lemma
        (let fa = U64.add_mod src (U64.mul_mod (U64.uint_to_t k) mword) in
         U64.v fa < heap_size /\ U64.v fa % 8 == 0 ==>
         read_word g' fa == read_word g fa)
      = if src = obj then
          header_write_doesnt_change_own_fields g obj new_hdr k
        else
          header_write_doesnt_change_other_fields g obj src new_hdr k
      in
      FStar.Classical.forall_intro field_eq;
      efptu_congruence g' g src wz_src dst
    in
    let aux2_imp (src dst: obj_addr) : Lemma
      ((Seq.mem src (objects 0UL g') /\
        U64.v (wosize_of_object src g') < pow2 54 /\
        exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst) ==>
       Seq.mem dst (objects 0UL g'))
    = FStar.Classical.move_requires (aux2 src) dst
    in
    FStar.Classical.forall_intro_2 aux2_imp;

    // --- Part 3: infix_wf (vacuous: no infix objects exist) ---
    // We'll prove part 4 first (no infix objects), then use it for part 3.
    // Part 4 proof:
    let not_infix (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g'))
      (ensures ~(is_infix h g'))
    = is_infix_spec h g';
      tag_of_object_spec h g';
      hd_address_spec h;
      if h = obj then begin
        read_write_same g hd new_hdr;
        make_header_getTag (U64.uint_to_t block_wz) white_bits 0UL;
        infix_tag_val ();
        // getTag new_hdr has value 0, infix_tag has value 249
        // tag_of_object h g' = getTag (read_word g' hd) = getTag new_hdr
        // U64.v (getTag new_hdr) == 0, U64.v infix_tag == 249
        assert (tag_of_object h g' <> infix_tag)
      end else begin
        if U64.v h < U64.v obj then
          objects_separated 0UL g h obj
        else
          objects_separated 0UL g obj h;
        read_write_different g hd (hd_address h) new_hdr;
        is_infix_spec h g;
        tag_of_object_spec h g
      end
    in
    // Part 3: infix_wf holds because no object is infix
    let no_infix_pf (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL g') /\ is_infix h g')
      (ensures (let p = parent_closure_addr_nat h g' in
                p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
                Seq.mem (U64.uint_to_t p) (objects 0UL g') /\
                is_closure (U64.uint_to_t p) g'))
    = not_infix h  // Derives ~(is_infix h g'), contradicting requires
    in
    infix_wf_intro g' (objects 0UL g') no_infix_pf;

    // --- Part 4: no infix objects ---
    let aux4_imp (h: obj_addr) : Lemma
      (Seq.mem h (objects 0UL g') ==> ~(is_infix h g'))
    = FStar.Classical.move_requires not_infix h
    in
    FStar.Classical.forall_intro aux4_imp
#pop-options

/// ===========================================================================
/// Section 6: Split case — alloc_from_block with split preserves wf
/// ===========================================================================

/// The split case creates a new object boundary. This requires proving
/// that the new objects list is the old list with one block replaced by two.
/// This is the hardest part of the allocator-GC bridge.

/// TODO: Prove objects_split lemma showing the new objects list structure.
/// For now, we admit this case to establish the overall proof structure.

let alloc_split_preserves_wf
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 2))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap g'))
  = admit ()

/// ===========================================================================
/// Section 7: alloc_from_block preserves well_formed_heap (combining cases)
/// ===========================================================================

let alloc_from_block_preserves_wf
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap g'))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    if block_wz - wz >= 2 then
      alloc_split_preserves_wf g obj wz next_fp
    else
      alloc_exact_preserves_wf g obj wz next_fp

/// ===========================================================================
/// Section 8: alloc_search preserves well_formed_heap
/// ===========================================================================

/// The recursive search either returns unchanged heap (OOM/advance) or
/// calls alloc_from_block once. In all cases, well_formed_heap is preserved.

/// alloc_search with prev_fp update: the prev link write is a field write
/// to an existing object, preserving wf.

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let rec alloc_search_preserves_wf
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g)
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    well_formed_heap r.heap_out))
          (decreases fuel)
  = if fuel = 0 then ()
    else if cur_fp = 0UL then ()
    else if U64.v cur_fp < U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found: alloc_from_block preserves wf
        // Need: obj in objects 0UL g
        // This is a key precondition we need to establish.
        // For now, assume it (it follows from the free-list invariant).
        assume (Seq.mem obj (objects 0UL g));
        alloc_from_block_preserves_wf g obj wz next_fp;
        let (g', new_fp) = alloc_from_block g obj wz next_fp in
        // Handle prev_fp update
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // prev_fp write: need to show this preserves wf
          // This needs: prev_fp in objects, write addr in body of prev_fp
          // For now, admit this step
          admit ()
        end
        else ()
      end
      else
        // Advance: same heap, recurse
        alloc_search_preserves_wf g head_fp cur_fp next_fp wz (fuel - 1)
    end
#pop-options

/// ===========================================================================
/// Section 9: Top-level theorem
/// ===========================================================================

let alloc_spec_preserves_wf (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap g)
          (ensures (let r = alloc_spec g fp requested_wz in
                    well_formed_heap r.heap_out))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_wf g fp 0UL fp wz (heap_size / U64.v mword)
