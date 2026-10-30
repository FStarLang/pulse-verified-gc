/// ---------------------------------------------------------------------------
/// GC.Spec.Allocator.Dense — allocation preserves heap_objects_dense
/// ---------------------------------------------------------------------------
///
/// Strategy:
/// - OOM case: heap unchanged, trivial.
/// - Non-OOM: prove density at alloc_from_block level with exact/split case split.
/// - Compose: alloc_spec = alloc_search (finds block) + alloc_from_block.
///
/// Moved from GC.Gen.Cheney.Dense: it is about `alloc_spec` only, so the
/// mark-and-sweep tree can use it without importing a generational module.

module GC.Spec.Allocator.Dense

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Lib.Header

module AllocLemmas = GC.Spec.Allocator.Lemmas
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

let objects_nonempty_from_header (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    read_word g1 start == read_word g2 start /\
                    Seq.length (objects start g1) > 0)
          (ensures Seq.length (objects start g2) > 0)
  = ()

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
  = reveal_opaque (`%heap_objects_dense) heap_objects_dense

/// Helper: writing a value with the same getWosize at an aligned address preserves objects.
/// By induction on objects: at each header position, either the read is unchanged
/// (read_write_different) or the wosize is preserved (read_write_same + hypothesis).
#push-options "--z3rlimit 12 --fuel 1 --ifuel 1"
private let rec write_header_same_wosize_preserves_objects_aux
  (start: hp_addr) (g: heap) (addr: hp_addr) (v: U64.t)
  : Lemma (requires getWosize v == getWosize (read_word g addr))
          (ensures objects start (write_word g addr v) == objects start g)
          (decreases (Seq.length g - U64.v start))
  = let g' = write_word g addr v in
    if U64.v start + 8 >= Seq.length g then ()
    else begin
      // Show: getWosize (read_word g' start) == getWosize (read_word g start)
      if start = addr then
        read_write_same g addr v
        // read_word g' start == v, and getWosize v == getWosize (read_word g start)
      else
        read_write_different g addr start v;
        // read_word g' start == read_word g start

      let wz = getWosize (read_word g start) in
      let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        if next_start_nat >= heap_size then ()
        else
          write_header_same_wosize_preserves_objects_aux
            (U64.uint_to_t next_start_nat) g addr v
      end
    end
#pop-options

/// In the EXACT-fit case (bwz == wz) the objects list is unchanged: the only
/// write is the header, and it carries the same wosize.
///
/// Narrowed from `bwz - wz < 2`.  At leftover = 1 the statement is now false:
/// right-justification splits the block into the empty fragment and the
/// allocated object, so `objects` gains an entry.  Callers must dispatch on
/// leftover = 0 versus leftover = 1 rather than lumping them together.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
private let alloc_from_block_exact_objects_eq_part1 (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
                     bwz == wz) /\
                    wz >= 1)
          (ensures (let (g', _) = alloc_from_block g obj wz tag next_fp in
                    objects zero_addr g' == objects zero_addr g))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    SA.alloc_from_block_exact g obj wz next_fp tag;
    let ahdr = make_header (U64.uint_to_t wz) white_bits tag in
    let g1 = write_word g hd ahdr in
    assert (alloc_from_block g obj wz tag next_fp == (g1, next_fp));
    getWosize_bound hdr;
    AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits tag;
    assert (getWosize ahdr == getWosize hdr);
    write_header_same_wosize_preserves_objects_aux zero_addr g hd ahdr
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block split case density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

/// Right-justified split (and the one-word leftover, which writes the same
/// two headers): the remainder keeps `hd` and shrinks to `leftover - 1`, and
/// the allocated header sits `leftover` words above it.  The two blocks tile
/// exactly the span the original block covered --
///
///     hd .. hd + leftover*8   the remainder, wosize leftover - 1
///     ah .. ah + (wz+1)*8     the allocated block, wosize wz
///
/// and `ah + (wz+1)*8 = hd + (bwz+1)*8` is where the next block always
/// started -- so density is preserved by construction.
private let alloc_from_block_split_dense
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    wz >= 1 /\
                    (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz >= wz /\ bwz - wz >= 1))
          (ensures (let (g', _) = alloc_from_block g obj wz tag next_fp in
                    heap_objects_dense g'))
  = reveal_opaque (`%heap_objects_dense) heap_objects_dense;
    let hd_obj = hd_address obj in
    let hdr = read_word g hd_obj in
    let bwz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec obj g;
    assert (U64.v hd_obj + 8 + bwz * 8 <= heap_size);

    let leftover = bwz - wz in
    let rw = leftover - 1 in
    let ahn = U64.v hd_obj + leftover * 8 in
    // wz >= 1 keeps the allocated header a full block below the end
    assert (ahn + 8 + wz * 8 == U64.v hd_obj + 8 + bwz * 8);
    assert (ahn + 8 < heap_size);

    SA.alloc_from_block_split_normal g obj wz next_fp tag;
    let rhdr = make_header (U64.uint_to_t rw) blue_bits 0UL in
    let g1 = write_word g hd_obj rhdr in
    let ah : hp_addr = U64.uint_to_t ahn in
    let ahdr = make_header (U64.uint_to_t wz) white_bits tag in
    let g2 = write_word g1 ah ahdr in
    let g' = g2 in

    AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits tag;
    AllocLemmas.make_header_getWosize (U64.uint_to_t rw) blue_bits 0UL;

    // the allocated block is an object of g'
    Part1.alloc_from_block_alloc_in_objects_part1 g obj wz next_fp tag;
    f_address_spec ah;
    let alloc_obj : obj_addr = f_address ah in
    assert (Seq.mem (alloc_obj <: U64.t) (objects zero_addr g'));

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
          // the remainder: wosize rw, so the next header is exactly `ah`
          aligned_apart ah start;
          read_write_different g1 ah start ahdr;
          read_write_same g hd_obj rhdr;
          assert (read_word g' start == rhdr);
          assert (U64.v start + (rw + 1) * 8 == ahn);
          objects_nonempty_from_header g' g' ah
        end
        else if start = ah then begin
          // the allocated block: its end is where the old block ended
          read_write_same g1 ah ahdr;
          assert (read_word g' ah == ahdr);
          let next = ahn + (wz + 1) * 8 in
          assert (next == U64.v hd_obj + (1 + bwz) * 8);
          if next + 8 < heap_size then begin
            let next_hp : hp_addr = U64.uint_to_t next in
            let fa_next = f_address next_hp in
            f_address_spec next_hp;
            f_address_spec hd_obj;
            assert (Seq.mem (f_address hd_obj) (objects zero_addr g));
            density_at g hd_obj;
            assert (Seq.mem fa_next (objects zero_addr g));
            Part1.alloc_split_old_in_new_part1 g obj wz next_fp (fa_next <: obj_addr) tag;
            // the next header is beyond both writes
            aligned_apart ah next_hp;
            read_write_different g1 ah next_hp ahdr;
            aligned_apart hd_obj next_hp;
            read_write_different g hd_obj next_hp rhdr;
            objects_nonempty_from_header g g' next_hp
          end
        end
        else begin
          // every other header is untouched, so the old density carries over
          let fa = f_address start in
          aligned_apart ah start;
          read_write_different g1 ah start ahdr;
          aligned_apart hd_obj start;
          read_write_different g hd_obj start rhdr;
          assert (read_word g' start == read_word g start);
          // `fa` must be an old object: the only new one is the allocated block
          if not (Seq.mem fa (objects zero_addr g)) then begin
            AllocLemmas.alloc_from_block_objects_backward_part1 g obj wz next_fp fa tag;
            assert false
          end else ();
          objects_nonempty_from_header g' g start;
          density_at g start;
          let wz' = getWosize (read_word g start) in
          let next = U64.v start + ((U64.v wz' + 1) * 8) in
          if next + 8 < heap_size then begin
            let next_hp : hp_addr = U64.uint_to_t next in
            let fa_next = f_address next_hp in
            f_address_spec next_hp;
            assert (Seq.mem fa_next (objects zero_addr g));
            Part1.alloc_split_old_in_new_part1 g obj wz next_fp (fa_next <: obj_addr) tag;
            if next_hp = hd_obj then begin
              aligned_apart ah next_hp;
              read_write_different g1 ah next_hp ahdr;
              read_write_same g hd_obj rhdr;
              ()
            end else if next_hp = ah then begin
              read_write_same g1 ah ahdr;
              ()
            end else begin
              aligned_apart ah next_hp;
              read_write_different g1 ah next_hp ahdr;
              aligned_apart hd_obj next_hp;
              read_write_different g hd_obj next_hp rhdr;
              objects_nonempty_from_header g g' next_hp
            end
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block exact case density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"

private let alloc_from_block_exact_dense
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    wz >= 1 /\
                    (let hdr = read_word g (hd_address obj) in
                     let bwz = U64.v (getWosize hdr) in
                     bwz == wz))
          (ensures (let (g', _) = alloc_from_block g obj wz tag next_fp in
                    heap_objects_dense g'))
  = reveal_opaque (`%heap_objects_dense) heap_objects_dense;
    let (g', _) = alloc_from_block g obj wz tag next_fp in
    alloc_from_block_exact_objects_eq_part1 g obj wz next_fp tag;
    let hdr = read_word g (hd_address obj) in
    let bwz = U64.v (getWosize hdr) in
    SA.alloc_from_block_exact g obj wz next_fp tag;
    hd_address_spec obj;
    hd_address_bounds obj;
    let ahdr = make_header (U64.uint_to_t wz) white_bits tag in
    AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits tag;
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

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"

private let alloc_from_block_preserves_dense
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    wz >= 1 /\
                    U64.v (getWosize (read_word g (hd_address obj))) >= wz)
          (ensures (let (g', _) = alloc_from_block g obj wz tag next_fp in
                    heap_objects_dense g'))
  = let hdr = read_word g (hd_address obj) in
    let bwz = U64.v (getWosize hdr) in
    if bwz - wz >= 1 then
      alloc_from_block_split_dense g obj wz next_fp tag
    else
      alloc_from_block_exact_dense g obj wz next_fp tag

#pop-options

/// ---------------------------------------------------------------------------
/// Write at a field position preserves density
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

private let write_field_preserves_dense
  (g: heap) (obj: obj_addr) (v: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v (wosize_of_object obj g) >= 1)
          (ensures heap_objects_dense (write_word g obj v))
  = reveal_opaque (`%heap_objects_dense) heap_objects_dense;
    let g' = write_word g obj v in
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


#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

/// When alloc_search finds a block and prev <> 0, the result is
/// `alloc_from_block (write_word g prev new_fp) obj wz next`.  In the
/// reordered search the link write comes first, and that makes this proof two
/// independent steps instead of a case analysis over the block writes: a
/// field write preserves density, and then the block writes preserve it.
private let alloc_search_found_prev_dense
  (g: heap) (obj: obj_addr) (prev_fp: obj_addr) (wz: nat) (next_fp: U64.t)
  (new_fp: U64.t) (tag: U64.t{U64.v tag < 256})
  : Lemma (requires well_formed_heap_part1 g /\
                    heap_objects_dense g /\
                    Seq.mem obj (objects zero_addr g) /\
                    Seq.mem prev_fp (objects zero_addr g) /\
                    prev_fp <> obj /\
                    U64.v (prev_fp <: U64.t) <> U64.v (hd_address obj) /\
                    wz >= 1 /\
                    U64.v (wosize_of_object prev_fp g) >= 1 /\
                    (let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
                     bwz >= wz))
          (ensures (let gw = write_word g (prev_fp <: hp_addr) new_fp in
                    heap_objects_dense (fst (alloc_from_block gw obj wz tag next_fp))))
  = let gw = write_word g (prev_fp <: hp_addr) new_fp in
    hd_address_spec prev_fp;
    hd_address_bounds prev_fp;
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec prev_fp g;
    wosize_of_object_bound prev_fp g;
    // Step 1: the link write is a field write, which preserves density,
    // well-formedness and the enumeration.
    write_field_preserves_dense g prev_fp new_fp;
    AllocLemmas.write_body_preserves_wfh_part1 g prev_fp (prev_fp <: hp_addr) new_fp;
    AllocLemmas.write_body_preserves_objects_local
      zero_addr g prev_fp (prev_fp <: hp_addr) new_fp;
    // Step 2: obj's header survives it, so the block writes see the same block
    aligned_apart (prev_fp <: hp_addr) (hd_address obj);
    read_write_different g (prev_fp <: hp_addr) (hd_address obj) new_fp;
    alloc_from_block_preserves_dense gw obj wz next_fp tag

#pop-options

/// ---------------------------------------------------------------------------
/// alloc_spec preserves density (induction on alloc_search)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 150 --fuel 4 --ifuel 1"

private let rec alloc_search_preserves_dense
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat) (tag: U64.t{U64.v tag < 256})
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
    (ensures heap_objects_dense (alloc_search g head_fp prev_fp cur_fp wz tag fuel).heap_out)
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
        let leftover = bwz - wz in
        let ahn = U64.v hd + leftover * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then
          // the right-justified object would leave the heap; the search bails
          // and the heap is untouched
          SA.alloc_search_found_oob g head_fp prev_fp cur_fp wz fuel tag
        else if prev_fp = 0UL then begin
          SA.alloc_search_found_head g head_fp prev_fp cur_fp wz fuel tag;
          alloc_from_block_preserves_dense g obj wz next_fp tag
        end else if U64.v prev_fp <> U64.v hd then begin
          // prev usable: the search relinks it, then allocates
          SA.alloc_search_found_prev g head_fp prev_fp cur_fp wz fuel tag;
          alloc_search_found_prev_dense g obj (prev_fp <: obj_addr) wz next_fp
            (SA.alloc_replacement_fp g obj wz next_fp) tag
        end else begin
          // prev is the degenerate wosize-0 shape; the search treats it as
          // absent and allocates without touching any link
          SA.alloc_search_found_head g head_fp prev_fp cur_fp wz fuel tag;
          alloc_from_block_preserves_dense g obj wz next_fp tag
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
          alloc_search_preserves_dense g head_fp cur_fp next_fp wz (fuel - 1) tag
        end else ()
      end
    end

#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"

let alloc_spec_preserves_dense_part1 (g: heap) (fp: U64.t) (requested_wz: nat) (tag: U64.t{U64.v tag < 256})
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_dense g fp 0UL fp wz heap_words tag

#pop-options
