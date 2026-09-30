(*
   GC.Spec.Allocator.Lemmas.Part2 — Section P2-P5 proofs.

   alloc_spec preserves well_formed_heap_part1, fl_valid, fl_chain_terminates,
   and various framing properties under the weaker part1 precondition.
*)
module GC.Spec.Allocator.Lemmas.Part2


open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Header
open GC.Spec.Allocator.Lemmas.Split
open GC.Spec.Allocator.Lemmas.Part1
open GC.Spec.Allocator.Lemmas.Common
open GC.Spec.Allocator.Lemmas.Chain
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Header = GC.Lib.Header

/// Module-level default: all functions get z3rlimit 10 unless overridden
#push-options "--z3rlimit 10 --z3refresh"

/// At leftover = 0 the right-justified address IS the block's own address.
/// Trivial, but the enclosing contexts are large enough that Z3 will not
/// bother; discharged here where the context is empty.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let add_zero_offset (a: U64.t) (k: nat)
  : Lemma (requires k == 0)
          (ensures U64.add a (U64.uint_to_t (k * 8)) == a)
  = ()
#pop-options

/// Two distinct word-aligned addresses are at least one word apart.
///
/// Trivial, but query splitting makes each goal carry the whole context of the
/// enclosing recursive proof, so it is discharged here where the context is
/// empty and applied as a lemma.
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let aligned_distinct (a b: U64.t)
  : Lemma (requires a <> b /\ U64.v a % U64.v mword == 0 /\ U64.v b % U64.v mword == 0)
          (ensures U64.v a + U64.v mword <= U64.v b \/
                   U64.v a >= U64.v b + U64.v mword)
  = ()
#pop-options

/// An address strictly inside the block owned by `blk` is distinct from every other
/// object of the heap.  `objects_separated` places any other object either strictly
/// below `blk` or strictly beyond `blk`'s last field, and `inner` sits between the
/// two.  Proved here, in an empty context, because the free-list proofs that need it
/// carry enormous hypothesis sets in which Z3 4.15.3 no longer finds this argument.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let addr_inside_block_ne (g: heap) (blk other: obj_addr) (inner: U64.t) (block_wz: nat)
  : Lemma
    (requires Seq.mem blk (objects zero_addr g) /\
              Seq.mem other (objects zero_addr g) /\
              U64.v (wosize_of_object_as_wosize blk g) == block_wz /\
              U64.v blk < U64.v inner /\
              U64.v inner < U64.v blk + block_wz * 8)
    (ensures other =!= inner)
  = objects_separated zero_addr g blk other;
    objects_separated zero_addr g other blk
#pop-options

/// Specialisation of `addr_inside_block_ne` to the remainder object produced by a
/// split allocation: `rem = hd + (1 + wz) * mword + mword`, which lies strictly
/// between `obj = hd + mword` and the end of `obj`'s block whenever
/// `wz + 1 < block_wz`.  Hence it differs from every other object in the heap.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let rem_obj_ne (g: heap) (obj other: obj_addr) (rem: U64.t) (hd: hp_addr) (wz block_wz: nat)
  : Lemma
    (requires Seq.mem obj (objects zero_addr g) /\
              Seq.mem other (objects zero_addr g) /\
              U64.v (wosize_of_object_as_wosize obj g) == block_wz /\
              U64.v obj == U64.v hd + U64.v mword /\
              U64.v rem == U64.v hd + (1 + wz) * 8 + 8 /\
              wz >= 1 /\ wz + 1 < block_wz)
    (ensures other =!= rem)
  = addr_inside_block_ne g obj other rem block_wz
#pop-options

/// Companion of `rem_obj_ne` for the remainder *header* address,
/// `rem_hd = hd + (1 + wz) * mword`, which also lies strictly inside `obj`'s block
/// whenever `wz < block_wz`.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let rem_hd_ne (g: heap) (obj other: obj_addr) (rem_hd: U64.t) (hd: hp_addr) (wz block_wz: nat)
  : Lemma
    (requires Seq.mem obj (objects zero_addr g) /\
              Seq.mem other (objects zero_addr g) /\
              U64.v (wosize_of_object_as_wosize obj g) == block_wz /\
              U64.v obj == U64.v hd + U64.v mword /\
              U64.v rem_hd == U64.v hd + (1 + wz) * 8 /\
              wz >= 1 /\ wz < block_wz)
    (ensures other =!= rem_hd)
  = addr_inside_block_ne g obj other rem_hd block_wz
#pop-options

/// The header of the object one word above `h` is `h` itself.  Phrased over the
/// raw nat so that the `UInt.size` side condition of `U64.uint_to_t` is discharged
/// here rather than inside the free-list proofs.
/// The right-justified allocated address is INTERIOR to the free block, so it
/// is not an object of the pre-allocation heap: `objects_separated` says the
/// next object starts strictly past `obj + block_wz * 8`, and `wz >= 1` keeps
/// the allocated address a word below that.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let alloc_obj_interior (g: heap) (obj a: obj_addr) (block_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem (obj <: U64.t) (objects zero_addr g) /\
                    U64.v (getWosize (read_word g (hd_address obj))) == block_wz /\
                    U64.v a > U64.v obj /\
                    U64.v a <= U64.v obj + (block_wz - 1) * 8)
          (ensures ~(Seq.mem (a <: U64.t) (objects zero_addr g)))
  = hd_address_spec obj;
    wosize_of_object_spec obj g;
    objects_separated zero_addr g obj a
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let hd_address_of_succ (h o: hp_addr)
  : Lemma (requires U64.v o == U64.v h + U64.v mword /\ U64.v o >= U64.v mword)
          (ensures hd_address (o <: obj_addr) == h)
  = hd_address_spec (o <: obj_addr)
#pop-options

/// The header of the object at `rem_hd_nat + 8` is at `rem_hd_nat`.  At the call
/// site in `alloc_search_new_objects_blue_part1` the hypothesis holds by
/// equational reasoning alone, whereas the conclusion needs integer arithmetic,
/// which F*'s one-query-per-goal encoding asks Z3 to find under the full
/// hypothesis load of that proof (where it runs out of rlimit).
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let hd_address_below (x: obj_addr) (rem_hd_nat: int)
  : Lemma (requires U64.v x == rem_hd_nat + 8)
          (ensures U64.v (hd_address x) == rem_hd_nat)
  = hd_address_spec x
#pop-options

/// `objects_separated` for the free block `obj` and a later object `y`, stated
/// over `obj`'s raw header.  In `alloc_search_preserves_fl_valid_part1` the
/// arithmetic consequence was left to Z3 under the full hypothesis load of that
/// proof, which F*'s one-query-per-goal encoding made exhaust its rlimit on the
/// first attempt (succeeding only on `--retry`).
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let objects_separated_from_block (g: heap) (obj y: obj_addr)
  : Lemma (requires Seq.mem obj (objects zero_addr g) /\
                    Seq.mem y (objects zero_addr g) /\
                    U64.v y >= U64.v obj /\ y <> obj)
          (ensures U64.v y > U64.v obj + U64.v (getWosize (read_word g (hd_address obj))) * 8)
  = objects_separated zero_addr g obj y;
    wosize_of_object_spec obj g
#pop-options

/// Compose an object-level frame (`g` to `g'`) with the address-level frame of a
/// single `write_word` at `excl` (`g'` to `g2`), yielding the frame condition in
/// the exact shape that `GC.Spec.Allocator.Lemmas.Chain` requires.
///
/// Both ingredients are already available at every call site; what Z3 4.15.3 can
/// no longer do is chain them under the hypothesis load of the enclosing
/// recursive proof.  Doing it here, over abstract heaps, keeps the query small.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let frame_excl_compose (g g' g2: heap) (excl: hp_addr)
  : Lemma
    (requires
      U64.v excl % U64.v mword == 0 /\
      (forall (a: obj_addr).
         (Seq.mem a (objects zero_addr g) /\
          U64.v (wosize_of_object a g) >= 1 /\
          U64.v (hd_address a) + 16 <= heap_size) ==>
            read_word g' a == read_word g a) /\
      (forall (a: hp_addr).
         (U64.v a + U64.v mword <= U64.v excl \/ U64.v a >= U64.v excl + U64.v mword) ==>
            read_word g2 a == read_word g' a))
    (ensures
      forall (a: U64.t).
        (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
         Seq.mem a (objects zero_addr g) /\ a <> excl) ==>
        (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
         U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
           read_word g2 (a <: obj_addr) == read_word g (a <: obj_addr)))
  = introduce forall (a: U64.t).
        (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
         Seq.mem a (objects zero_addr g) /\ a <> excl) ==>
        (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
         U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
           read_word g2 (a <: obj_addr) == read_word g (a <: obj_addr))
    with introduce _ ==> _
    with introduce _ ==> _
    with aligned_distinct a excl
#pop-options

#restart-solver
#push-options "--z3rlimit 12 --fuel 2 --ifuel 1"
private let chain_avoids_shrink (g: heap) (fp excl: U64.t) (s_small s_big: nat)
  : Lemma (requires chain_avoids g fp excl s_big = true /\ s_small <= s_big)
          (ensures chain_avoids g fp excl s_small = true)
  = chain_avoids_weaken g fp excl s_big s_small
#pop-options

#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let make_header_getColor (wz: U64.t{U64.v wz < pow2 54})
                                 (c: U64.t{U64.v c < 4})
                                 (t: U64.t{U64.v t < 256})
  : Lemma (Header.get_color (U64.v (make_header wz c t)) == U64.v c)
  = let hdr = make_header wz c t in
    make_header_value wz c t;
    Header.get_color_val (U64.v hdr);
    FStar.UInt.shift_right_value_lemma #64 (U64.v hdr) 8;
    assert_norm (pow2 8 = 256);
    FStar.Math.Lemmas.lemma_div_plus (U64.v c * 256 + U64.v t) (U64.v wz * 4) 256;
    FStar.Math.Lemmas.lemma_div_plus (U64.v t) (U64.v c) 256;
    FStar.Math.Lemmas.small_div (U64.v t) 256;
    FStar.UInt.logand_mask #64 (U64.v wz * 4 + U64.v c) 2;
    assert_norm (pow2 2 - 1 = 3);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v c) (U64.v wz) 4;
    FStar.Math.Lemmas.small_mod (U64.v c) 4
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
private let make_header_color_blue (wz: U64.t{U64.v wz < pow2 54})
  : Lemma (getColor (make_header wz blue_bits 0UL) == Header.Blue)
  = let hdr = make_header wz blue_bits 0UL in
    getColor_raw hdr;
    make_header_getColor wz blue_bits 0UL
#pop-options

/// ===========================================================================
/// Section P2: alloc_spec preserves well_formed_heap_part1
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// P2-pre: split_new_mem_in_old_or_rem_part1
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 3 --ifuel 1"
private let rec split_new_mem_in_old_or_rem_part1
  (start: hp_addr) (g g3: heap)
  (obj: obj_addr) (wz block_wz: nat)
  (h: obj_addr)
  : Lemma (requires
      Seq.length g3 == Seq.length g /\
      well_formed_heap_part1 g /\
      Seq.mem obj (objects zero_addr g) /\
      (let hd = hd_address obj in
       let hdr = read_word g hd in
       U64.v (getWosize hdr) == block_wz /\
       // a one-word leftover builds the same two-block tiling as a split
       block_wz >= wz /\ block_wz - wz >= 1 /\
       // Right-justified: the block at hd is the REMAINDER and the ALLOCATED
       // object sits `leftover` words above it, so the new object is the
       // allocated one rather than the remainder.
       (let ahn = U64.v hd + (block_wz - wz) * 8 in
        let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
        ahn < heap_size /\
        ahn + 8 < heap_size /\
        next_hd_nat <= heap_size /\
        (forall (p: hp_addr). U64.v p < U64.v hd ==> read_word g3 p == read_word g p) /\
        getWosize (read_word g3 hd) == U64.uint_to_t (block_wz - wz - 1) /\
        (ahn < heap_size ==>
          getWosize (read_word g3 (U64.uint_to_t ahn <: hp_addr)) == U64.uint_to_t wz) /\
        (next_hd_nat < heap_size ==>
          objects (U64.uint_to_t next_hd_nat <: hp_addr) g3 == objects (U64.uint_to_t next_hd_nat <: hp_addr) g) /\
        U64.v start <= U64.v hd)) /\
      Seq.mem h (objects start g3) /\
      (U64.v start = U64.v zero_addr \/ Seq.mem (f_address start) (objects zero_addr g)) /\
      Seq.mem obj (objects start g))
    (ensures (let ahn = U64.v (hd_address obj) + (block_wz - wz) * 8 in
              Seq.mem h (objects start g) \/ U64.v h == ahn + 8))
    (decreases (Seq.length g3 - U64.v start))
  = let hd = hd_address obj in
    hd_address_spec obj;
    if U64.v start + 8 >= Seq.length g3 then ()
    else begin
      let header_g3 = read_word g3 start in
      let wz_g3 = getWosize header_g3 in
      let next_nat_g3 = U64.v start + (U64.v wz_g3 + 1) * 8 in
      if next_nat_g3 > Seq.length g3 || next_nat_g3 >= pow2 64 then ()
      else begin
        f_address_spec start;
        let first : obj_addr = f_address start in
        mem_cons_lemma h first
          (if next_nat_g3 >= heap_size then Seq.empty
           else objects (U64.uint_to_t next_nat_g3 <: hp_addr) g3);
        if U64.v start = U64.v hd then begin
          // g3 has the REMAINDER at hd, so the walk's next stop is the
          // allocated header at ahn, not a remainder above the object.
          let ahn = U64.v hd + (block_wz - wz) * 8 in
          let alloc_obj_nat = ahn + 8 in
          let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
          assert (first == obj);
          assert (next_nat_g3 == ahn);
          if h = first then begin
            let header_g = read_word g start in
            let wz_g = getWosize header_g in
            let next_nat_g = U64.v start + (U64.v wz_g + 1) * 8 in
            assert (next_nat_g == next_hd_nat);
            if next_hd_nat >= heap_size then
              mem_cons_lemma h obj (Seq.empty #obj_addr)
            else
              mem_cons_lemma h obj (objects (U64.uint_to_t next_hd_nat <: hp_addr) g)
          end else begin
            if ahn >= heap_size then ()
            else begin
              let ah_hp : hp_addr = U64.uint_to_t ahn in
              assert (Seq.mem h (objects ah_hp g3));
              f_address_spec ah_hp;
              let alloc_obj_addr : obj_addr = f_address ah_hp in
              assert (U64.v alloc_obj_addr == alloc_obj_nat);
              let next_from_alloc = ahn + (wz + 1) * 8 in
              assert (next_from_alloc == next_hd_nat);
              mem_cons_lemma h alloc_obj_addr
                (if next_hd_nat >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_hd_nat <: hp_addr) g3);
              if h = alloc_obj_addr then begin
                assert (U64.v h == alloc_obj_nat)
              end else begin
                if next_hd_nat >= heap_size then ()
                else begin
                  let next_hd : hp_addr = U64.uint_to_t next_hd_nat in
                  assert (Seq.mem h (objects next_hd g3));
                  assert (objects next_hd g3 == objects next_hd g);
                  assert (Seq.mem h (objects next_hd g));
                  let header_g = read_word g start in
                  let next_nat_g = U64.v start + (U64.v (getWosize header_g) + 1) * 8 in
                  assert (next_nat_g == next_hd_nat);
                  mem_cons_lemma h obj (objects next_hd g)
                end
              end
            end
          end
        end else begin
          assert (read_word g3 start == read_word g start);
          if h = first then begin
            let header_g = read_word g start in
            let next_nat_g = U64.v start + (U64.v (getWosize header_g) + 1) * 8 in
            if next_nat_g >= heap_size then
              mem_cons_lemma h first (Seq.empty #obj_addr)
            else
              mem_cons_lemma h first (objects (U64.uint_to_t next_nat_g <: hp_addr) g)
          end else begin
            if next_nat_g3 >= heap_size then ()
            else begin
              let next_hp : hp_addr = U64.uint_to_t next_nat_g3 in
              let header_g_here = read_word g start in
              assert (header_g3 == header_g_here);
              let wz_g_here = getWosize header_g_here in
              assert (wz_g3 == wz_g_here);
              mem_cons_lemma first first
                (if next_nat_g3 >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_nat_g3 <: hp_addr) g);
              assert (Seq.mem first (objects start g));
              // Need U64.v zero_addr <= U64.v start for objects_later_in_earlier
              (if U64.v start = U64.v zero_addr then ()
               else begin
                 f_address_spec start;
                 objects_addresses_gt_start zero_addr g (f_address start)
               end);
              assert (U64.v zero_addr <= U64.v start);
              objects_later_in_earlier zero_addr g start first;
              hd_address_spec first;
              wosize_of_object_spec first g;
              objects_separated zero_addr g first obj;
              assert (U64.v hd % 8 == 0);
              assert (U64.v start % 8 == 0);
              FStar.Math.Lemmas.cancel_mul_mod (U64.v wz_g_here) 8;
              assert ((U64.v start + U64.v wz_g_here * 8) % 8 == 0);
              assert (U64.v hd > U64.v start + U64.v wz_g_here * 8);
              assert (next_nat_g3 <= U64.v hd);
              let next_nat_g = U64.v start + (U64.v wz_g_here + 1) * 8 in
              assert (next_nat_g == next_nat_g3);
              mem_cons_lemma obj first
                (if next_nat_g >= heap_size then Seq.empty
                 else objects (U64.uint_to_t next_nat_g <: hp_addr) g);
              assert (obj <> first);
              objects_nonempty_first_mem next_hp g obj;
              mem_cons_lemma (f_address next_hp) first (objects next_hp g);
              if U64.v start = U64.v zero_addr then ()
              else objects_addresses_gt_start zero_addr g (f_address start);
              objects_later_in_earlier zero_addr g start (f_address next_hp);
              split_new_mem_in_old_or_rem_part1 next_hp g g3 obj wz block_wz h;
              // the new object is the ALLOCATED one, at ahn + 8
              let alloc_obj_nat = U64.v hd + (block_wz - wz) * 8 + 8 in
              if U64.v h = alloc_obj_nat then ()
              else begin
                let next_nat_g2 = U64.v start + (U64.v wz_g_here + 1) * 8 in
                assert (next_nat_g2 == next_nat_g3);
                mem_cons_lemma h first (objects next_hp g)
              end
            end
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2a: alloc_split preserves wfh_part1 (under just part1)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
private let alloc_split_wf_part1_v2
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    // wz >= 1 is what makes the allocated OBJECT address
                    // (hd + leftover*8 + 8) land strictly inside the heap
                    wz >= 1 /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 1))
          (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part1 g3))
  = alloc_split_facts_part1 g obj wz next_fp;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    // Right-justified: the remainder keeps hd (so `obj` is the remainder now),
    // and the allocated object sits `leftover` words above it.
    let leftover = block_wz - wz in
    let rem_wz = leftover - 1 in
    let ahn = U64.v hd + leftover * 8 in
    let alloc_obj_nat = ahn + 8 in
    let alloc_obj_addr : obj_addr = U64.uint_to_t alloc_obj_nat in
    let (g3, _) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g3))
      (ensures (let w = wosize_of_object h g3 in
                U64.v (hd_address h) + 8 + U64.v w * 8 <= Seq.length g3))
    = wosize_of_object_spec h g3;
      hd_address_spec h;
      if h = obj then begin
        // obj is the REMAINDER: wosize rem_wz, and hd + 8 + rem_wz*8 = ahn
        assert (Seq.length g3 == heap_size);
        assert (U64.v (hd_address h) == U64.v hd);
        assert (U64.v (wosize_of_object h g3) == rem_wz);
        assert (U64.v hd + 8 + rem_wz * 8 == ahn);
        assert (ahn <= heap_size)
      end else if h = alloc_obj_addr then begin
        // the allocated object: wosize wz, ending exactly at the block's end
        assert (Seq.length g3 == heap_size);
        assert (U64.v (hd_address h) == ahn);
        assert (U64.v (wosize_of_object h g3) == wz);
        assert (ahn + 8 + wz * 8 == U64.v hd + (block_wz + 1) * 8);
        assert (U64.v hd + (block_wz + 1) * 8 <= heap_size)
      end else begin
        // h is from old objects. Use split_new_mem_in_old_or_rem_part1 to show h ∈ objects(0, g)
        let aux_before (p: hp_addr) : Lemma
          (requires U64.v p < U64.v hd)
          (ensures read_word g3 p == read_word g p)
        = alloc_split_g3_agrees_part1 g obj wz next_fp p
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
        objects_addresses_gt_start zero_addr g obj;
        split_new_mem_in_old_or_rem_part1 zero_addr g g3 obj wz block_wz h;
        assert (Seq.mem h (objects zero_addr g));
        // Header of h is unchanged
        hd_address_spec h;
        wosize_of_object_spec h g;
        wosize_of_object_spec obj g;
        if U64.v h < U64.v obj then begin
          objects_separated zero_addr g h obj;
          alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
        end else begin
          objects_separated zero_addr g obj h;
          assert (U64.v (hd_address h) > U64.v hd + block_wz * 8 - 8);
          assert (U64.v (hd_address h) <> U64.v hd);
          // only two words are written now: hd and the object header at ahn
          assert (U64.v (hd_address h) <> ahn);
          alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// P2b: alloc_exact preserves wfh_part1 (under just part1)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
private let alloc_exact_preserves_wfh_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     // exact fit only: at leftover = 1 the heap gains a block,
                     // so the split lemma covers that case instead
                     block_wz == wz))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part1 g'))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let new_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    alloc_from_block_exact g obj wz next_fp;
    hd_address_spec obj;
    hd_address_bounds obj;
    getWosize_bound hdr;
    make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
    header_write_same_wosize_preserves_objects g obj new_hdr;
    let g' = write_word g hd new_hdr in
    // objects(0, g') == objects(0, g), and for each h: wosize(h, g') == wosize(h, g)
    // since the only modified header is at hd with same wosize.
    // So part1 transfers trivially.
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures (let w = wosize_of_object h g' in
                U64.v (hd_address h) + 8 + U64.v w * 8 <= Seq.length g'))
    = hd_address_spec h;
      wosize_of_object_spec h g';
      wosize_of_object_spec h g;
      if h = obj then
        read_write_same g hd new_hdr
      else begin
        if U64.v h < U64.v obj then
          objects_separated zero_addr g h obj
        else
          objects_separated zero_addr g obj h;
        read_write_different g hd (hd_address h) new_hdr
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// P2c: alloc_from_block preserves wfh_part1 (under just part1)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let alloc_from_block_preserves_wfh_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    // leftover >= 1 all goes through the split lemma now: a one-word leftover
    // builds the same two-block tiling as a real split.
    if block_wz - wz >= 1 then
      alloc_split_wf_part1_v2 g obj wz next_fp
    else
      alloc_exact_preserves_wfh_part1 g obj wz next_fp
#pop-options

/// ---------------------------------------------------------------------------
/// P2d: write within object body preserves wfh_part1
/// ---------------------------------------------------------------------------


/// ---------------------------------------------------------------------------
/// P2e: alloc_search_preserves_wfh_part1 — recursive proof
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_wfh_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    // the right-justified object address needs it
                    wz >= 1 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    well_formed_heap_part1 r.heap_out))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      assert (Seq.mem obj (objects zero_addr g));
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        if prev_fp = 0UL then ()
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          let prev : obj_addr = prev_fp in
          // Reordered: the prev-link write happens FIRST, on `g`, and the
          // block writes then run on `gw`.  Both steps are easier this way --
          // the field write is a plain body write on a heap nobody has touched
          // yet, and `alloc_from_block` is applied to a heap where `obj` is
          // still exactly the object it was.
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          hd_address_spec prev;
          hd_address_bounds prev;
          wosize_of_object_spec obj g;
          // prev's block is disjoint from obj's, in particular prev <> hd.
          if U64.v prev < U64.v obj then begin
            objects_separated zero_addr g prev obj;
            assert (U64.v (hd_address prev) + 8 <= U64.v hd)
          end else begin
            objects_separated zero_addr g obj prev;
            assert (U64.v prev > U64.v obj + block_wz * 8);
            assert (U64.v (hd_address prev) >= U64.v hd + (block_wz + 1) * 8)
          end;
          assert (U64.v prev <> U64.v hd);
          // Step 1: the field write preserves wfh and the objects tiling.
          write_body_preserves_wfh_part1 g prev (prev <: hp_addr) new_fp;
          write_body_preserves_objects_local zero_addr g prev (prev <: hp_addr) new_fp;
          let gw = write_word g (prev <: hp_addr) new_fp in
          assert (objects zero_addr gw == objects zero_addr g);
          assert (Seq.mem obj (objects zero_addr gw));
          // Step 2: obj's header is untouched, so the block is the same size.
          read_write_different g (prev <: hp_addr) hd new_fp;
          assert (read_word gw hd == hdr);
          assert (U64.v (getWosize (read_word gw hd)) == block_wz);
          getWosize_bound hdr;
          alloc_from_block_preserves_wfh_part1 gw obj wz next_fp
        end
        else ()
      end
      else begin
        fl_valid_next g cur_fp fuel;
        assert (cur_fp <> next_fp);
        assert (U64.v hd + 16 <= heap_size);
        assert (fl_valid g next_fp (fuel - 1));
        fl_chain_terminates_elim g cur_fp fuel;
        assert (fl_chain_terminates g next_fp (fuel - 1));
        alloc_search_preserves_wfh_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2f: Top-level alloc_spec_preserves_wfh_part1
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_wfh_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_wfh_part1 g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// P2g: alloc_split_fl_transfer_pre_part1 — split case fl_valid_transfer
///      under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let alloc_split_fl_transfer_pre_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz >= 1 /\
                     // At leftover = 1 the remainder at `hd` is the empty
                     // block, so `obj` -- its object address -- has wosize 0
                     // in the output heap and is the one object for which the
                     // conclusion below is false.  It is also no longer a
                     // free-list cell, so callers exclude it instead.
                     (block_wz - wz >= 2 \/ a <> obj)) /\
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
  = alloc_split_facts_part1 g obj wz next_fp;
    alloc_from_block_objects_facts_part1 g obj wz next_fp;
    let (g', _) = alloc_from_block g obj wz next_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let leftover = block_wz - wz in
    let ahn = U64.v hd + leftover * 8 in
    hd_address_spec obj;
    hd_address_bounds obj;
    wosize_of_object_spec obj g;
    getWosize_bound hdr;
    if U64.v (wosize_of_object a g) >= 1 then begin
      hd_address_spec a;
      wosize_of_object_spec a g;
      wosize_of_object_bound a g;
      if a = obj then begin
        // Right-justified: the remainder keeps `hd`, so `obj` is still its
        // object address and its wosize is leftover - 1 >= 1.  `obj` itself
        // (the link word) is not written at all.
        assert (U64.v obj == U64.v hd + 8);
        assert (leftover >= 2);
        assert (ahn == U64.v hd + leftover * 8);
        assert (ahn >= U64.v hd + 16);
        assert (U64.v obj <> U64.v hd);
        assert (U64.v obj <> ahn);
        alloc_split_g3_agrees_part1 g obj wz next_fp (obj <: hp_addr);
        wosize_of_object_spec obj g'
      end else begin
        if U64.v a < U64.v obj then begin
          objects_separated zero_addr g a obj;
          // a + wosize(a)*8 <= obj - 8 = hd, so hd_address(a) = a - 8 < a <= hd,
          // and both writes are at hd and ahn = hd + leftover*8 >= hd.
          alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address a);
          alloc_split_g3_agrees_part1 g obj wz next_fp (a <: hp_addr);
          wosize_of_object_spec a g;
          wosize_of_object_spec a g'
        end else begin
          objects_separated zero_addr g obj a;
          // a >= hd + (block_wz+1)*8 + 8, so hd_address(a) = a - 8 >=
          // hd + (block_wz+1)*8 > ahn = hd + leftover*8 > hd.
          alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address a);
          alloc_split_g3_agrees_part1 g obj wz next_fp (a <: hp_addr);
          wosize_of_object_spec a g;
          wosize_of_object_spec a g'
        end
      end
    end else ()
#pop-options

/// ---------------------------------------------------------------------------
/// P2h: alloc_exact_fl_transfer_pre_part1 — exact-fit case fl_valid_transfer
///      under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let alloc_exact_fl_transfer_pre_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz == wz) /\
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
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    alloc_from_block_exact g obj wz next_fp;
    let g' = write_word g hd alloc_hdr in
    hd_address_spec obj;
    hd_address_bounds obj;
    getWosize_bound hdr;
    make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
    header_write_same_wosize_preserves_objects g obj alloc_hdr;
    if U64.v (wosize_of_object a g) >= 1 then begin
      hd_address_spec a;
      wosize_of_object_spec a g;
      wosize_of_object_bound a g;
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

/// ---------------------------------------------------------------------------
/// P2h2: fl_valid_field_write_part1 — like fl_valid_field_write but only needs
///       well_formed_heap_part1 (not full well_formed_heap)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
private let rec fl_valid_field_write_part1
  (g: heap) (p: obj_addr) (v: U64.t) (fp: U64.t) (fuel tail_fuel: nat)
  : Lemma
    (requires fl_valid g fp fuel /\
              well_formed_heap_part1 g /\
              Seq.mem p (objects zero_addr g) /\
              U64.v (wosize_of_object p g) >= 1 /\
              v <> p /\
              fl_valid (write_word g (p <: hp_addr) v) v tail_fuel /\
              tail_fuel >= fuel)
    (ensures fl_valid (write_word g (p <: hp_addr) v) fp fuel)
    (decreases fuel)
  = let g' = write_word g (p <: hp_addr) v in
    if fuel = 0 then
      fl_valid_zero g' fp
    else if fp = 0UL then
      fl_valid_null g' fuel
    else if U64.v fp < U64.v mword then
      fl_valid_terminal g' fp fuel
    else if U64.v fp >= heap_size then
      fl_valid_terminal g' fp fuel
    else if U64.v fp % U64.v mword <> 0 then
      fl_valid_terminal g' fp fuel
    else begin
      let obj_fp : obj_addr = fp in
      let hd_fp = hd_address obj_fp in
      fl_valid_gives_mem g fp fuel;
      fl_valid_gives_wosize g fp fuel;
      // objects preserved by field write
      wfh_part1_obj_bound g p;
      wosize_of_object_bound p g;
      write_word_preserves_objects_part1 g p (p <: hp_addr) v;
      assert (objects zero_addr g' == objects zero_addr g);
      assert (Seq.mem fp (objects zero_addr g'));
      // wosize preserved: hd_fp ≠ p (the write position)
      hd_address_spec obj_fp;
      if U64.v fp <> U64.v p then begin
        if U64.v fp > U64.v p then
          objects_separated zero_addr g p obj_fp
        else
          objects_separated zero_addr g obj_fp p
      end;
      read_write_different g (p <: hp_addr) (hd_fp <: hp_addr) v;
      wosize_of_object_spec obj_fp g;
      wosize_of_object_spec obj_fp g';
      assert (U64.v (wosize_of_object obj_fp g') >= 1);
      if U64.v hd_fp + 16 <= heap_size then begin
        fl_valid_next g fp fuel;
        assert (read_word g obj_fp <> fp);
        assert (fl_valid g (read_word g obj_fp) (fuel - 1));
        if fp = p then begin
          read_write_same g (p <: hp_addr) v;
          assert (read_word g' obj_fp == v);
          fl_valid_weaken g' v tail_fuel (fuel - 1)
        end else begin
          read_write_different g (p <: hp_addr) (obj_fp <: hp_addr) v;
          assert (read_word g' obj_fp == read_word g obj_fp);
          fl_valid_field_write_part1 g p v (read_word g obj_fp) (fuel - 1) tail_fuel
        end
      end;
      assert (Seq.mem fp (objects zero_addr g'));
      assert (U64.v (wosize_of_object (fp <: obj_addr) g') >= 1);
      assert (U64.v hd_fp + 16 <= heap_size ==>
                read_word g' obj_fp <> fp /\
                fl_valid g' (read_word g' obj_fp) (fuel - 1));
      fl_valid_step g' fp fuel;
      assert (fl_valid g' fp fuel)
    end
#pop-options

/// fl_valid_field_write_tail_part1: establishes fl_valid g' v fuel
/// where g' = write_word g p v, using only well_formed_heap_part1.
#restart-solver
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
private let rec fl_valid_field_write_tail_part1
  (g: heap) (p: obj_addr) (v: U64.t) (fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
              Seq.mem p (objects zero_addr g) /\
              U64.v (wosize_of_object p g) >= 1 /\
              v <> p /\
              fl_valid g v fuel)
    (ensures fl_valid (write_word g (p <: hp_addr) v) v fuel)
    (decreases fuel)
  = let g' = write_word g (p <: hp_addr) v in
    if fuel = 0 then
      fl_valid_zero g' v
    else if v = 0UL then
      fl_valid_null g' fuel
    else if U64.v v < U64.v mword then
      fl_valid_terminal g' v fuel
    else if U64.v v >= heap_size then
      fl_valid_terminal g' v fuel
    else if U64.v v % U64.v mword <> 0 then
      fl_valid_terminal g' v fuel
    else begin
      let obj_v : obj_addr = v in
      let hd_v = hd_address obj_v in
      fl_valid_gives_mem g v fuel;
      fl_valid_gives_wosize g v fuel;
      // objects preserved
      wfh_part1_obj_bound g p;
      wosize_of_object_bound p g;
      write_word_preserves_objects_part1 g p (p <: hp_addr) v;
      assert (objects zero_addr g' == objects zero_addr g);
      // wosize preserved at v: hd_v ≠ p
      hd_address_spec obj_v;
      if U64.v v <> U64.v p then begin
        if U64.v v > U64.v p then
          objects_separated zero_addr g p obj_v
        else
          objects_separated zero_addr g obj_v p
      end;
      read_write_different g (p <: hp_addr) (hd_v <: hp_addr) v;
      wosize_of_object_spec obj_v g;
      wosize_of_object_spec obj_v g';
      assert (Seq.mem v (objects zero_addr g'));
      assert (U64.v (wosize_of_object (v <: obj_addr) g') >= 1);
      if U64.v hd_v + 16 <= heap_size then begin
        fl_valid_next g v fuel;
        // v ≠ p, so link at v unchanged
        read_write_different g (p <: hp_addr) (obj_v <: hp_addr) v;
        let link = read_word g obj_v in
        assert (read_word g' obj_v == link);
        assert (link <> v);
        assert (fl_valid g link (fuel - 1));
        // IH: fl_valid g' v (fuel-1)
        fl_valid_weaken g v fuel (fuel - 1);
        fl_valid_field_write_tail_part1 g p v (fuel - 1);
        // fl_valid g' link (fuel-1) via fl_valid_field_write_part1
        fl_valid_field_write_part1 g p v link (fuel - 1) (fuel - 1)
      end;
      assert (U64.v hd_v + 16 <= heap_size ==>
                read_word g' obj_v <> v /\
                fl_valid g' (read_word g' obj_v) (fuel - 1));
      fl_valid_step g' v fuel;
      assert (fl_valid g' v fuel)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// chain_avoids_after_relink -- the relinked chain skips the allocated block
/// ---------------------------------------------------------------------------
///
/// In `gw = write_word g prev next_fp` -- prev's link repaired, block writes
/// NOT yet applied -- the chain from `head_fp` no longer visits `cur_fp`.
///
/// This is the fact the reordered `alloc_search` makes available and the old
/// order could not: here the list has already been repaired while the block at
/// `cur_fp` is still untouched, so `fl_valid` and `chain_avoids` both hold of
/// the same heap.  Splices two halves --
///
///   head..prev   avoids cur_fp   by acyclicity: cur_fp sits at depth d + 1,
///                                so it cannot also appear at depth <= d
///   next_fp..    avoids cur_fp   by fl_chain_predecessor_not_in_suffix_b
///
/// -- and transfers each across the single write at prev.  Modelled on the
/// corresponding block in `alloc_search_obj_not_in_chain_part1`.

#restart-solver
#push-options "--z3rlimit 150 --fuel 1 --ifuel 0"
private let chain_avoids_after_relink
  (g: heap) (prev_obj: obj_addr) (cur_fp next_fp head_fp: U64.t) (fuel big_fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
              fl_valid g cur_fp fuel /\
              fl_chain_terminates g cur_fp fuel /\
              fl_valid g head_fp big_fuel /\
              fl_chain_terminates g head_fp big_fuel /\
              fuel > 0 /\ fuel < big_fuel /\
              U64.v cur_fp >= U64.v mword /\ U64.v cur_fp < heap_size /\
              U64.v cur_fp % U64.v mword = 0 /\
              U64.v (hd_address (cur_fp <: obj_addr)) + 16 <= heap_size /\
              read_word g (cur_fp <: obj_addr) == next_fp /\
              Seq.mem cur_fp (objects zero_addr g) /\
              U64.v (wosize_of_object (cur_fp <: obj_addr) g) >= 1 /\
              (prev_obj <: U64.t) <> cur_fp /\
              Seq.mem (prev_obj <: U64.t) (objects zero_addr g) /\
              U64.v (wosize_of_object prev_obj g) >= 1 /\
              U64.v (hd_address prev_obj) + 16 <= heap_size /\
              read_word g (prev_obj <: obj_addr) == cur_fp /\
              walk_chain g head_fp (big_fuel - fuel) = cur_fp /\
              walk_chain_valid g head_fp (big_fuel - fuel) /\
              walk_chain g head_fp (big_fuel - fuel - 1) = (prev_obj <: U64.t))
    (ensures (let gw = write_word g (prev_obj <: hp_addr) next_fp in
              chain_avoids gw head_fp cur_fp big_fuel = true))
  = let gw = write_word g (prev_obj <: hp_addr) next_fp in
    let d = big_fuel - fuel - 1 in
    hd_address_spec prev_obj;
    hd_address_spec (cur_fp <: obj_addr);
    // `gw` differs from `g` at exactly one word, so every OTHER object address
    // reads the same.  This is the frame both chain_avoids_transfer_excl2
    // calls below need, and it is the only thing they need.
    let frame_aux (a: obj_addr) : Lemma
      (requires (a <: U64.t) <> (prev_obj <: U64.t))
      (ensures read_word gw a == read_word g a)
    = aligned_distinct (prev_obj <: U64.t) (a <: U64.t);
      read_write_different g (prev_obj <: hp_addr) (a <: hp_addr) next_fp
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires frame_aux);
    // ---- suffix: next_fp .. avoids cur_fp, and survives the prev write ----
    fl_chain_predecessor_not_in_suffix_b g cur_fp fuel;
    not_in_fl_chain_b_is_chain_avoids g next_fp cur_fp (fuel - 1);
    assert (chain_avoids g next_fp cur_fp (fuel - 1) = true);
    fl_valid_next g cur_fp fuel;
    assert (fl_valid g next_fp (fuel - 1));
    fl_chain_terminates_elim g cur_fp fuel;
    // the suffix never revisits prev either, so the single write is invisible
    chain_avoids_prev g (prev_obj <: U64.t) cur_fp next_fp (fuel - 1);
    chain_avoids_transfer_excl2 g gw next_fp cur_fp (prev_obj <: U64.t) (fuel - 1);
    fl_chain_terminates_transfer_excl g gw next_fp (prev_obj <: U64.t) (fuel - 1);
    chain_avoids_strengthen gw next_fp cur_fp (fuel - 1) (big_fuel - 1);
    assert (chain_avoids gw next_fp cur_fp (big_fuel - 1) = true);
    // ---- step back over prev, whose link in gw is next_fp ----
    read_write_same g (prev_obj <: hp_addr) next_fp;
    assert (read_word gw (prev_obj <: obj_addr) == next_fp);
    assert ((prev_obj <: U64.t) <> cur_fp);
    chain_avoids_unfold_step gw (prev_obj <: U64.t) cur_fp big_fuel;
    assert (chain_avoids gw (prev_obj <: U64.t) cur_fp big_fuel = true);
    // ---- prefix: head .. prev, unchanged by the write, avoids cur_fp ----
    if d = 0 then begin
      // head IS prev; nothing to splice.
      walk_chain_zero g head_fp;
      assert (head_fp == (prev_obj <: U64.t));
      assert (chain_avoids gw head_fp cur_fp big_fuel = true)
    end else begin
      walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
      // cur_fp sits at depth d + 1, prev at depth d; acyclicity says neither
      // appears earlier than its own position.
      fl_chain_no_early_repeat g head_fp (d + 1) big_fuel;
      chain_avoids_shrink g head_fp cur_fp d (d + 1);
      fl_chain_no_early_repeat g head_fp d big_fuel;
      assert (chain_avoids g head_fp (prev_obj <: U64.t) d = true);
      fl_valid_weaken g head_fp big_fuel d;
      walk_chain_valid_preserved g gw head_fp (prev_obj <: U64.t) d big_fuel;
      chain_avoids_transfer_excl2 g gw head_fp cur_fp (prev_obj <: U64.t) d;
      // unfold_steps gives an EQUATION between the full walk and the walk from
      // depth d; supply the right-hand side at the shifted fuel.
      assert (walk_chain gw head_fp d == (prev_obj <: U64.t));
      chain_avoids_shrink gw (prev_obj <: U64.t) cur_fp (big_fuel - d) big_fuel;
      chain_avoids_unfold_steps gw head_fp cur_fp d big_fuel;
      assert (chain_avoids gw head_fp cur_fp big_fuel = true)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2i: alloc_search_preserves_fl_valid_part1 — recursive proof that alloc_search
///      preserves fl_valid under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_fl_valid_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    fl_valid g head_fp heap_words /\
                    fl_chain_terminates g head_fp heap_words /\
                    wz >= 1 /\
                    fuel <= heap_words /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
                       U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
                       read_word g (prev_fp <: obj_addr) = cur_fp)) /\
                    // Walk-chain invariants, carried so the prev <> 0 arm can
                    // splice `head..prev` onto the suffix when proving that the
                    // relinked chain skips cur_fp.  Same shape as
                    // `alloc_search_obj_not_in_chain_part1`, discharged at
                    // depth 0 by the wrapper.
                    walk_chain g head_fp (heap_words - fuel) = cur_fp /\
                    walk_chain_valid g head_fp (heap_words - fuel) /\
                    (prev_fp <> 0UL ==> fuel < heap_words /\
                                        walk_chain g head_fp (heap_words - fuel - 1) = prev_fp))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    fl_valid r.heap_out r.fp_out heap_words))
          (decreases fuel)
  = let big_fuel = heap_words in
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      fl_valid_next g cur_fp fuel;
      assert (Seq.mem obj (objects zero_addr g));
      assert (U64.v (wosize_of_object obj g) >= 1);
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      // Use well_formed_heap_part1 to get the size bound (replaces wf_object_size_bound)
      assert (U64.v hd + 8 + block_wz * 8 <= heap_size);
      getWosize_bound hdr;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      assert (U64.v hd + 16 <= heap_size);
      assert (fl_valid g next_fp (fuel - 1));
      fl_chain_terminates_elim g cur_fp fuel;
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        // Establish: is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)
        // Using FL-based reasoning instead of next_fp_in_objects
        (if next_fp = 0UL then ()
         else if U64.v next_fp < U64.v mword then ()
         else if U64.v next_fp >= heap_size then ()
         else if U64.v next_fp % U64.v mword <> 0 then ()
         else if fuel - 1 = 0 then begin
           fl_chain_terminates_valid_zero g next_fp;
           assert false
         end
         else fl_valid_elim g next_fp (fuel - 1));
        assert (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g));
        alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
        let g' = fst (alloc_from_block g obj wz next_fp) in
        // The free-list replacement, read off transparently: `alloc_search`
        // builds `gw` from this exact term, so use the same one here.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        // Upgrade fl_valid g next_fp (fuel-1) to fl_valid g next_fp big_fuel
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        assert (fl_valid g next_fp big_fuel);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0UL: fp_out = new_fp =====
          if block_wz - wz >= 2 then begin
            // ===== Split: right-justified, so new_fp = obj = cur_fp =====
            // The remainder keeps `hd`, keeps its address and keeps the link
            // word already stored at hd + 8, so the free list is bit-identical
            // and fp_out is the very cell we started from.
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            let leftover = block_wz - wz in
            let rem_wz = leftover - 1 in
            let ahn = U64.v hd + leftover * 8 in
            assert (new_fp == cur_fp);
            assert (U64.v obj == U64.v hd + 8);
            assert (ahn >= U64.v hd + 16);
            // Transfer fl_valid g next_fp big_fuel to g'
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer g g' next_fp big_fuel;
            fl_valid_weaken g' next_fp big_fuel (big_fuel - 1);
            // 1. the link word at obj is one of the two words NOT written
            alloc_split_g3_agrees_part1 g obj wz next_fp (obj <: hp_addr);
            assert (read_word g' new_fp == next_fp);
            // 2. the remainder header at hd now declares leftover - 1 >= 1
            wosize_of_object_spec (new_fp <: obj_addr) g';
            assert (U64.v (wosize_of_object (new_fp <: obj_addr) g') == rem_wz);
            assert (rem_wz >= 1);
            // 3-5. address, bounds and absence of a self-loop are inherited
            //      unchanged from cur_fp
            assert (U64.v (hd_address (new_fp <: obj_addr)) + 16 <= heap_size);
            assert (next_fp <> new_fp);
            fl_valid_step g' new_fp big_fuel
          end else if block_wz - wz = 1 then begin
            // ===== One-word leftover: the whole block leaves the list =====
            // The remainder at `hd` is the empty block (header only), so `obj`
            // has wosize 0 in g' and is no longer a free-list cell.  It is the
            // one object the transfer cannot cover; `fl_chain_terminates` says
            // the suffix from next_fp never visits it, so it can be excluded.
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            assert (new_fp == next_fp);
            fl_chain_predecessor_not_in_suffix_b g cur_fp fuel;
            not_in_fl_chain_b_is_chain_avoids g next_fp cur_fp (fuel - 1);
            assert (chain_avoids g next_fp cur_fp (fuel - 1) = true);
            (if big_fuel >= fuel - 1 then
               chain_avoids_strengthen g next_fp cur_fp (fuel - 1) big_fuel
             else
               chain_avoids_weaken g next_fp cur_fp (fuel - 1) big_fuel);
            let transfer_aux_f (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g) /\ a <> obj)
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_f);
            fl_valid_transfer_excl g g' next_fp obj big_fuel
          end else begin
            // ===== Exact-fit case: new_fp = next_fp =====
            assert (block_wz == wz);
            alloc_exact_preserves_wfh_part1 g obj wz next_fp;
            alloc_from_block_exact g obj wz next_fp;
            // Transfer fl_valid g next_fp big_fuel to g'
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer g g' next_fp big_fuel;
            ()
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp <> 0: fp_out = head_fp =====
          //
          // Reordered: `alloc_search` writes prev's link FIRST, on `g`, and
          // runs the block writes on the result.  So the heap out is
          //
          //     gw = write_word g prev new_fp
          //     g2 = fst (alloc_from_block gw obj wz next_fp)
          //
          // and the two steps below follow that order.  Doing it this way is
          // what makes the leftover = 1 case provable at all: the link write
          // happens while `obj` is still a well-formed cell of wosize >= 1,
          // rather than after it has become the wosize-0 empty block.
          let prev_obj : obj_addr = prev_fp in
          let gw = write_word g (prev_obj <: hp_addr) new_fp in
          let g2 = fst (alloc_from_block gw obj wz next_fp) in

          // --- separation: prev's block is disjoint from obj's ---
          hd_address_spec prev_obj;
          hd_address_bounds prev_obj;
          wosize_of_object_spec prev_obj g;
          wosize_of_object_bound prev_obj g;
          wosize_of_object_spec obj g;
          if U64.v prev_fp < U64.v obj then begin
            objects_separated zero_addr g prev_obj obj;
            assert (U64.v (hd_address prev_obj) + 8 <= U64.v hd)
          end else begin
            objects_separated zero_addr g obj prev_obj;
            assert (U64.v prev_fp > U64.v obj + block_wz * 8);
            assert (U64.v (hd_address prev_obj) >= U64.v hd + (block_wz + 1) * 8)
          end;
          assert (U64.v prev_fp <> U64.v hd);

          // --- Step 1: fl_valid gw head_fp, entirely on `g` ---
          // new_fp is either obj itself (split: the cell keeps its address, so
          // this stores the value already there) or next_fp (the block leaves
          // the list).  Either way fl_valid g new_fp is already in hand.
          // Unfold just the free-pointer component.
          (if block_wz - wz >= 1 then alloc_split_facts_part1 g obj wz next_fp
           else alloc_from_block_exact g obj wz next_fp);
          assert (new_fp == (if block_wz - wz >= 2 then (obj <: U64.t) else next_fp));
          // fl_valid of whichever it is:
          //   split -> new_fp is cur_fp itself; the cell keeps its address
          //   otherwise -> new_fp is next_fp, the tail of the chain
          fl_valid_any_fuel g cur_fp fuel big_fuel;
          fl_valid_next g cur_fp fuel;
          fl_chain_terminates_elim g cur_fp fuel;
          fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
          assert (fl_valid g new_fp big_fuel);
          // new_fp <> prev_fp.  On a split new_fp IS cur_fp, which the
          // precondition separates from prev.  Otherwise new_fp is next_fp,
          // and next = prev would close a two-cycle prev -> cur -> prev, which
          // cannot terminate.
          (if block_wz - wz >= 2 then ()
           else if new_fp = prev_fp then begin
             assert (read_word g (prev_fp <: obj_addr) == cur_fp);
             assert (read_word g (cur_fp <: obj_addr) == next_fp);
             assert (next_fp == prev_fp);
             fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
             assert (fl_chain_terminates g prev_fp (fuel - 1) = false);
             assert false
           end else ());
          assert (new_fp <> prev_fp);

          // `gw` differs from `g` at exactly one word, so every OTHER object
          // address reads the same.  Every transfer out of `g` below needs
          // this frame, and it is the only thing they need.
          let frame_aux (a: obj_addr) : Lemma
            (requires (a <: U64.t) <> (prev_obj <: U64.t))
            (ensures read_word gw a == read_word g a)
          = aligned_distinct (prev_obj <: U64.t) (a <: U64.t);
            read_write_different g (prev_obj <: hp_addr) (a <: hp_addr) new_fp
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires frame_aux);
          fl_valid_field_write_tail_part1 g prev_obj new_fp big_fuel;
          fl_valid_field_write_part1 g prev_obj new_fp head_fp big_fuel big_fuel;
          assert (fl_valid gw head_fp big_fuel);

          // --- Step 2: obj is untouched by the link write ---
          write_body_preserves_wfh_part1 g prev_obj (prev_obj <: hp_addr) new_fp;
          write_body_preserves_objects_local zero_addr g prev_obj (prev_obj <: hp_addr) new_fp;
          read_write_different g (prev_obj <: hp_addr) hd new_fp;
          assert (objects zero_addr gw == objects zero_addr g);
          assert (read_word gw hd == hdr);
          // Pin the block size through `gw` once, for all three arms below --
          // each transfer lemma's precondition is stated over `read_word gw hd`
          // and Z3 does not chase it back to `hdr` on its own.
          assert (U64.v (getWosize (read_word gw hd)) == block_wz);
          getWosize_bound hdr;
          assert (Seq.mem obj (objects zero_addr gw));

          // --- Step 3: carry fl_valid across the block writes, gw -> g2 ---
          if block_wz - wz >= 2 then begin
            // The remainder keeps `hd` with wosize leftover - 1 >= 1, so every
            // object still has a wosize >= 1 and a plain transfer suffices.
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw))
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_split_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_valid_transfer gw g2 head_fp big_fuel
          end
          else if block_wz - wz = 1 then begin
            // The whole block leaves the list and `obj` becomes the wosize-0
            // empty block, so it is the one object the transfer cannot cover.
            // In `gw` the chain from head_fp already skips it -- that is the
            // whole point of having rewired prev first -- so exclude it.
            fl_chain_predecessor_not_in_suffix_b g cur_fp fuel;
            not_in_fl_chain_b_is_chain_avoids g next_fp cur_fp (fuel - 1);
            assert (chain_avoids g next_fp cur_fp (fuel - 1) = true);
            chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
            chain_avoids_after_relink g prev_obj cur_fp next_fp head_fp fuel big_fuel;
            let transfer_aux_f (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw) /\ a <> obj)
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_split_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_f);
            fl_valid_transfer_excl gw g2 head_fp obj big_fuel
          end
          else begin
            // Exact fit: only the header at hd is rewritten, same wosize.
            assert (block_wz == wz);
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw))
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_exact_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            fl_valid_transfer gw g2 head_fp big_fuel
          end
        end
        else ()
      end
      else begin
        // ===== Advance: block too small, continue search =====
        assert (cur_fp <> next_fp);
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        walk_chain_append g head_fp (big_fuel - fuel) 1;
        walk_chain_one_step g cur_fp;
        walk_chain_valid_snoc g head_fp (big_fuel - fuel);
        alloc_search_preserves_fl_valid_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2j: Top-level alloc_spec_preserves_fl_valid_part1
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_fl_valid_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    // The walk-chain invariants hold trivially at depth 0, where head = cur.
    walk_chain_zero g fp;
    walk_chain_valid_zero g fp;
    alloc_search_preserves_fl_valid_part1 g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// P2k: alloc_search_preserves_fl_chain_terminates_part1 — recursive proof that
///      alloc_search preserves fl_chain_terminates under well_formed_heap_part1 only
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_fl_chain_terminates_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    fl_valid g head_fp heap_words /\
                    fl_chain_terminates g head_fp heap_words /\
                    wz >= 1 /\
                    fuel <= heap_words /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
                       U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
                       read_word g (prev_fp <: obj_addr) = cur_fp)) /\
                    // Walk-chain invariants
                    fuel <= heap_words /\
                    walk_chain g head_fp (heap_words - fuel) = cur_fp /\
                    walk_chain_valid g head_fp (heap_words - fuel) /\
                    (prev_fp <> 0UL ==> fuel < heap_words /\
                                        walk_chain g head_fp (heap_words - fuel - 1) = prev_fp))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    fl_chain_terminates r.heap_out r.fp_out heap_words))
          (decreases fuel)
  = let big_fuel = heap_words in
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      fl_valid_next g cur_fp fuel;
      assert (Seq.mem obj (objects zero_addr g));
      assert (U64.v (wosize_of_object obj g) >= 1);
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      // Use well_formed_heap_part1 to get the size bound (replaces wf_object_size_bound)
      assert (U64.v hd + 8 + block_wz * 8 <= heap_size);
      getWosize_bound hdr;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      assert (U64.v hd + 16 <= heap_size);
      assert (fl_valid g next_fp (fuel - 1));
      fl_chain_terminates_elim g cur_fp fuel;
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        // Establish: is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)
        // Using FL-based reasoning instead of next_fp_in_objects
        (if next_fp = 0UL then ()
         else if U64.v next_fp < U64.v mword then ()
         else if U64.v next_fp >= heap_size then ()
         else if U64.v next_fp % U64.v mword <> 0 then ()
         else if fuel - 1 = 0 then begin
           fl_chain_terminates_valid_zero g next_fp;
           assert false
         end
         else fl_valid_elim g next_fp (fuel - 1));
        assert (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g));
        alloc_from_block_preserves_wfh_part1 g obj wz next_fp;
        let g' = fst (alloc_from_block g obj wz next_fp) in
        // The free-list replacement, read off transparently: `alloc_search`
        // builds `gw` from this exact term, so use the same one here.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        // Upgrade fl_valid/terminates g next_fp (fuel-1) to big_fuel
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        assert (fl_valid g next_fp big_fuel);
        fl_chain_terminates_weaken g next_fp (fuel - 1) big_fuel;
        assert (fl_chain_terminates g next_fp big_fuel);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0UL: fp_out = new_fp, heap_out = g' =====
          if block_wz - wz >= 2 then begin
            // ===== Split: right-justified, so new_fp = obj = cur_fp =====
            // The remainder keeps `hd` and keeps the link word at hd + 8, so
            // the chain out of new_fp is the old chain out of cur_fp.
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            assert (new_fp == cur_fp);
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_chain_terminates_weaken g next_fp (fuel - 1) (big_fuel - 1);
            fl_valid_any_fuel g next_fp (fuel - 1) (big_fuel - 1);
            fl_chain_terminates_transfer g g' next_fp (big_fuel - 1);
            // the link word at obj is one of the two words NOT written
            alloc_split_g3_agrees_part1 g obj wz next_fp (obj <: hp_addr);
            assert (read_word g' new_fp == next_fp);
            fl_chain_terminates_step g' new_fp big_fuel
          end else if block_wz - wz = 1 then begin
            // ===== One-word leftover: the whole block leaves the list =====
            // `obj` becomes the wosize-0 empty block, so it is the one object
            // the transfer cannot cover; the suffix never visits it.
            alloc_split_facts_part1 g obj wz next_fp;
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            assert (new_fp == next_fp);
            fl_chain_predecessor_not_in_suffix_b g cur_fp fuel;
            not_in_fl_chain_b_is_chain_avoids g next_fp cur_fp (fuel - 1);
            assert (chain_avoids g next_fp cur_fp (fuel - 1) = true);
            (if big_fuel >= fuel - 1 then
               chain_avoids_strengthen g next_fp cur_fp (fuel - 1) big_fuel
             else
               chain_avoids_weaken g next_fp cur_fp (fuel - 1) big_fuel);
            let transfer_aux_f (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g) /\ a <> obj)
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_f);
            fl_chain_terminates_transfer_excl g g' next_fp obj big_fuel
          end else begin
            // ===== Exact fit: new_fp = next_fp =====
            alloc_exact_preserves_wfh_part1 g obj wz next_fp;
            alloc_from_block_exact g obj wz next_fp;
            assert (block_wz == wz);
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            fl_chain_terminates_transfer g g' next_fp big_fuel
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp <> 0: fp_out = head_fp =====
          //
          // Reordered: the prev-link write runs FIRST, on `g`, and the block
          // writes on the result:
          //
          //     gw = write_word g prev new_fp
          //     g2 = fst (alloc_from_block gw obj wz next_fp)
          //
          // Step 1 rebuilds termination of the head chain in `gw`, using only
          // facts about `g`; step 3 carries it across the block writes.
          let prev_obj : obj_addr = prev_fp in
          let gw = write_word g (prev_obj <: hp_addr) new_fp in
          let g2 = fst (alloc_from_block gw obj wz next_fp) in
          let d = big_fuel - fuel - 1 in

          // --- separation: prev's block is disjoint from obj's ---
          hd_address_spec prev_obj;
          hd_address_bounds prev_obj;
          wosize_of_object_spec prev_obj g;
          wosize_of_object_bound prev_obj g;
          wosize_of_object_spec obj g;
          if U64.v prev_fp < U64.v obj then begin
            objects_separated zero_addr g prev_obj obj;
            assert (U64.v (hd_address prev_obj) + 8 <= U64.v hd)
          end else begin
            objects_separated zero_addr g obj prev_obj;
            assert (U64.v prev_fp > U64.v obj + block_wz * 8);
            assert (U64.v (hd_address prev_obj) >= U64.v hd + (block_wz + 1) * 8)
          end;
          assert (U64.v prev_fp <> U64.v hd);

          // --- new_fp is either cur_fp (split) or next_fp, and is never prev ---
          (if block_wz - wz >= 1 then alloc_split_facts_part1 g obj wz next_fp
           else alloc_from_block_exact g obj wz next_fp);
          assert (new_fp == (if block_wz - wz >= 2 then (obj <: U64.t) else next_fp));
          fl_valid_any_fuel g cur_fp fuel big_fuel;
          fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
          (if block_wz - wz >= 2 then ()
           else if new_fp = prev_fp then begin
             assert (read_word g (prev_fp <: obj_addr) == cur_fp);
             assert (read_word g (cur_fp <: obj_addr) == next_fp);
             fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
             assert false
           end else ());
          assert (new_fp <> prev_fp);

          // `gw` differs from `g` at exactly one word, so every OTHER object
          // address reads the same.  Every transfer out of `g` below needs
          // this frame, and it is the only thing they need.
          let frame_aux (a: obj_addr) : Lemma
            (requires (a <: U64.t) <> (prev_obj <: U64.t))
            (ensures read_word gw a == read_word g a)
          = aligned_distinct (prev_obj <: U64.t) (a <: U64.t);
            read_write_different g (prev_obj <: hp_addr) (a <: hp_addr) new_fp
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires frame_aux);

          // --- Step 1a: fl_valid gw head_fp, needed by every transfer below ---
          fl_valid_field_write_tail_part1 g prev_obj new_fp big_fuel;
          fl_valid_field_write_part1 g prev_obj new_fp head_fp big_fuel big_fuel;
          assert (fl_valid gw head_fp big_fuel);

          // --- Step 1b: fl_chain_terminates gw head_fp big_fuel ---
          // The suffix from next_fp never revisits prev, so the single write
          // is invisible to it.
          chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
          fl_chain_terminates_transfer_excl g gw next_fp prev_fp (fuel - 1);
          assert (fl_chain_terminates gw next_fp (fuel - 1));
          // The chain out of new_fp terminates within `fuel` steps: on a split
          // new_fp is cur_fp, whose link in `gw` is still next_fp.
          (if block_wz - wz >= 2 then begin
             read_write_different g (prev_obj <: hp_addr) (cur_fp <: hp_addr) new_fp;
             assert (read_word gw (cur_fp <: obj_addr) == next_fp);
             fl_chain_terminates_step gw cur_fp fuel
           end else
             fl_chain_terminates_weaken gw next_fp (fuel - 1) fuel);
          assert (fl_chain_terminates gw new_fp fuel);
          read_write_same g (prev_obj <: hp_addr) new_fp;
          assert (read_word gw (prev_obj <: obj_addr) == new_fp);
          fl_chain_terminates_step gw prev_fp (fuel + 1);
          if d = 0 then begin
            walk_chain_zero g head_fp;
            assert (head_fp == prev_fp);
            fl_chain_terminates_weaken gw head_fp (fuel + 1) big_fuel
          end else begin
            walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
            fl_chain_no_early_repeat g head_fp d big_fuel;
            walk_chain_valid_preserved g gw head_fp prev_fp d big_fuel;
            fl_chain_terminates_unfold_steps gw head_fp d big_fuel
          end;
          assert (fl_chain_terminates gw head_fp big_fuel);

          // --- Step 2: obj is untouched by the link write ---
          write_body_preserves_wfh_part1 g prev_obj (prev_obj <: hp_addr) new_fp;
          write_body_preserves_objects_local zero_addr g prev_obj (prev_obj <: hp_addr) new_fp;
          read_write_different g (prev_obj <: hp_addr) hd new_fp;
          assert (objects zero_addr gw == objects zero_addr g);
          assert (read_word gw hd == hdr);
          assert (U64.v (getWosize (read_word gw hd)) == block_wz);
          getWosize_bound hdr;
          assert (Seq.mem obj (objects zero_addr gw));

          // --- Step 3: carry termination across the block writes, gw -> g2 ---
          if block_wz - wz >= 2 then begin
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw))
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_split_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            fl_chain_terminates_transfer gw g2 head_fp big_fuel
          end
          else if block_wz - wz = 1 then begin
            chain_avoids_after_relink g prev_obj cur_fp next_fp head_fp fuel big_fuel;
            assert (chain_avoids gw head_fp cur_fp big_fuel = true);
            let transfer_aux_f (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw) /\ a <> obj)
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_split_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_f);
            fl_chain_terminates_transfer_excl gw g2 head_fp obj big_fuel
          end
          else begin
            assert (block_wz == wz);
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw))
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_exact_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            fl_chain_terminates_transfer gw g2 head_fp big_fuel
          end
        end
        else ()
      end
      else begin
        // ===== Advance: block too small, continue search =====
        assert (cur_fp <> next_fp);
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        // Maintain walk_chain invariants for the recursive call
        walk_chain_append g head_fp (big_fuel - fuel) 1;
        walk_chain_one_step g cur_fp;
        walk_chain_valid_snoc g head_fp (big_fuel - fuel);
        alloc_search_preserves_fl_chain_terminates_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P2l: Top-level alloc_spec_preserves_fl_chain_terminates_part1
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_fl_chain_terminates_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    walk_chain_zero g fp;
    walk_chain_valid_zero g fp;
    alloc_search_preserves_fl_chain_terminates_part1 g fp 0UL fp wz heap_words

/// ===========================================================================
/// Section P3: alloc_spec_obj_not_in_chain under well_formed_heap_part1
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// P3a: alloc_search_obj_not_in_chain_part1 — recursive proof that alloc_search
///      removes obj_out from the chain, under well_formed_heap_part1 only.
///      Mirrors alloc_search_obj_not_in_chain but uses part1 helpers.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 150 --fuel 1 --ifuel 0"
private let rec alloc_search_obj_not_in_chain_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    fl_valid g head_fp heap_words /\
                    fl_chain_terminates g head_fp heap_words /\
                    wz >= 1 /\
                    fuel <= heap_words /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
                       U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
                       read_word g (prev_fp <: obj_addr) = cur_fp)) /\
                    // Walk-chain invariants
                    walk_chain g head_fp (heap_words - fuel) = cur_fp /\
                    walk_chain_valid g head_fp (heap_words - fuel) /\
                    (prev_fp <> 0UL ==> fuel < heap_words /\
                                        walk_chain g head_fp (heap_words - fuel - 1) = prev_fp))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL ==>
                    chain_avoids r.heap_out r.fp_out r.obj_out heap_words = true))
          (decreases fuel)
  = let big_fuel = heap_words in
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      fl_valid_next g cur_fp fuel;
      assert (Seq.mem obj (objects zero_addr g));
      assert (U64.v (wosize_of_object obj g) >= 1);
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      // Use well_formed_heap_part1 to get size bound (replaces wf_object_size_bound)
      assert (U64.v hd + 8 + block_wz * 8 <= heap_size);
      getWosize_bound hdr;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      assert (U64.v hd + 16 <= heap_size);
      assert (fl_valid g next_fp (fuel - 1));
      fl_chain_terminates_elim g cur_fp fuel;
      assert (fl_chain_terminates g next_fp (fuel - 1));
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        //
        // `obj_out` is the RIGHT-JUSTIFIED allocated block, `leftover` words
        // above cur_fp.  That makes the statement easy in two different ways:
        //
        //   leftover >= 1  the address is interior to the block in `g`, so it
        //                  is not an object of `g` at all and no chain can
        //                  visit it -- `chain_avoids_non_object`;
        //   leftover  = 0  it IS cur_fp, and the content is that the relinked
        //                  chain skips the block that just left the list.
        let g' = fst (alloc_from_block g obj wz next_fp) in
        // The free-list replacement, read off transparently: `alloc_search`
        // builds `gw` from this exact term, so use the same one here.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        fl_chain_terminates_weaken g next_fp (fuel - 1) big_fuel;
        fl_valid_any_fuel g cur_fp fuel big_fuel;
        fl_chain_predecessor_not_in_suffix_b g cur_fp fuel;
        not_in_fl_chain_b_is_chain_avoids g next_fp cur_fp (fuel - 1);
        assert (chain_avoids g next_fp cur_fp (fuel - 1) = true);
        chain_avoids_strengthen g next_fp cur_fp (fuel - 1) big_fuel;
        let leftover = block_wz - wz in
        let ahn = U64.v hd + leftover * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then
          // `alloc_search` bails here with obj_out = 0; nothing to prove.
          ()
        else begin
          let alloc_obj : obj_addr = U64.add cur_fp (U64.uint_to_t (leftover * 8)) in
          assert (U64.v alloc_obj == U64.v obj + leftover * 8);
          (if leftover >= 1 then
             alloc_obj_interior g obj alloc_obj block_wz
           else
             add_zero_offset cur_fp leftover);
          if prev_fp = 0UL then begin
            // ===== prev_fp = 0: fp_out = new_fp, heap_out = g' =====
            (if leftover >= 1 then alloc_split_facts_part1 g obj wz next_fp
             else alloc_from_block_exact g obj wz next_fp);
            alloc_from_block_objects_facts_part1 g obj wz next_fp;
            assert (new_fp == (if leftover >= 2 then (obj <: U64.t) else next_fp));
            assert (fl_valid g new_fp big_fuel);
            if leftover >= 2 then begin
              let transfer_aux (a: obj_addr) : Lemma
                (requires Seq.mem a (objects zero_addr g))
                (ensures Seq.mem a (objects zero_addr g') /\
                         (U64.v (wosize_of_object a g) >= 1 ==>
                           U64.v (wosize_of_object a g') >= 1) /\
                         (U64.v (wosize_of_object a g) >= 1 /\
                          U64.v (hd_address a) + 16 <= heap_size ==>
                           read_word g' a == read_word g a))
              = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
              chain_avoids_non_object g new_fp alloc_obj big_fuel;
              chain_avoids_transfer_excl g g' new_fp (alloc_obj <: U64.t) big_fuel
            end else if leftover = 1 then begin
              // `obj` becomes the wosize-0 empty block, so it is the one
              // object the transfer cannot cover; the chain skips it already.
              let transfer_aux_f (a: obj_addr) : Lemma
                (requires Seq.mem a (objects zero_addr g) /\ a <> obj)
                (ensures Seq.mem a (objects zero_addr g') /\
                         (U64.v (wosize_of_object a g) >= 1 ==>
                           U64.v (wosize_of_object a g') >= 1) /\
                         (U64.v (wosize_of_object a g) >= 1 /\
                          U64.v (hd_address a) + 16 <= heap_size ==>
                           read_word g' a == read_word g a))
              = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_f);
              chain_avoids_non_object g new_fp alloc_obj big_fuel;
              chain_avoids_transfer_excl2 g g' new_fp (alloc_obj <: U64.t) cur_fp big_fuel
            end else begin
              // Exact fit: alloc_obj IS cur_fp, and new_fp is next_fp.
              assert (leftover == 0);
              assert (block_wz == wz);
              alloc_exact_preserves_wfh_part1 g obj wz next_fp;
              let transfer_aux_e (a: obj_addr) : Lemma
                (requires Seq.mem a (objects zero_addr g))
                (ensures Seq.mem a (objects zero_addr g') /\
                         (U64.v (wosize_of_object a g) >= 1 ==>
                           U64.v (wosize_of_object a g') >= 1) /\
                         (U64.v (wosize_of_object a g) >= 1 /\
                          U64.v (hd_address a) + 16 <= heap_size ==>
                           read_word g' a == read_word g a))
              = alloc_exact_fl_transfer_pre_part1 g obj wz next_fp a
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
              assert ((alloc_obj <: U64.t) == cur_fp);
              chain_avoids_transfer_excl g g' next_fp cur_fp big_fuel
            end
          end
          else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                  U64.v prev_fp % U64.v mword = 0 then begin
            // ===== prev_fp <> 0: fp_out = head_fp, heap_out = g2 =====
            let prev_obj : obj_addr = prev_fp in
            let gw = write_word g (prev_obj <: hp_addr) new_fp in
            let g2 = fst (alloc_from_block gw obj wz next_fp) in

            // --- separation: prev's block is disjoint from obj's ---
            hd_address_spec prev_obj;
            hd_address_bounds prev_obj;
            wosize_of_object_spec prev_obj g;
            wosize_of_object_bound prev_obj g;
            if U64.v prev_fp < U64.v obj then begin
              objects_separated zero_addr g prev_obj obj;
              assert (U64.v (hd_address prev_obj) + 8 <= U64.v hd)
            end else begin
              objects_separated zero_addr g obj prev_obj;
              assert (U64.v prev_fp > U64.v obj + block_wz * 8);
              assert (U64.v (hd_address prev_obj) >= U64.v hd + (block_wz + 1) * 8)
            end;
            assert (U64.v prev_fp <> U64.v hd);

            (if leftover >= 1 then alloc_split_facts_part1 g obj wz next_fp
             else alloc_from_block_exact g obj wz next_fp);
            assert (new_fp == (if leftover >= 2 then (obj <: U64.t) else next_fp));
            (if leftover >= 2 then ()
             else if new_fp = prev_fp then begin
               assert (read_word g (prev_fp <: obj_addr) == cur_fp);
               assert (read_word g (cur_fp <: obj_addr) == next_fp);
               fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
               assert false
             end else ());
            assert (new_fp <> prev_fp);

          // `gw` differs from `g` at exactly one word, so every OTHER object
          // address reads the same.  Every transfer out of `g` below needs
          // this frame, and it is the only thing they need.
          let frame_aux (a: obj_addr) : Lemma
            (requires (a <: U64.t) <> (prev_obj <: U64.t))
            (ensures read_word gw a == read_word g a)
          = aligned_distinct (prev_obj <: U64.t) (a <: U64.t);
            read_write_different g (prev_obj <: hp_addr) (a <: hp_addr) new_fp
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires frame_aux);

            // --- Step 1: the relinked head chain, on `gw` ---
            fl_valid_field_write_tail_part1 g prev_obj new_fp big_fuel;
            fl_valid_field_write_part1 g prev_obj new_fp head_fp big_fuel big_fuel;
            assert (fl_valid gw head_fp big_fuel);

            // --- Step 2: obj is untouched by the link write ---
            write_body_preserves_wfh_part1 g prev_obj (prev_obj <: hp_addr) new_fp;
            write_body_preserves_objects_local zero_addr g prev_obj (prev_obj <: hp_addr) new_fp;
            read_write_different g (prev_obj <: hp_addr) hd new_fp;
            assert (objects zero_addr gw == objects zero_addr g);
            assert (read_word gw hd == hdr);
            assert (U64.v (getWosize (read_word gw hd)) == block_wz);
            getWosize_bound hdr;
            assert (Seq.mem obj (objects zero_addr gw));

            // --- Step 3: carry the avoidance across the block writes ---
            if leftover >= 2 then begin
              chain_avoids_non_object gw head_fp alloc_obj big_fuel;
              let transfer_aux (a: obj_addr) : Lemma
                (requires Seq.mem a (objects zero_addr gw))
                (ensures Seq.mem a (objects zero_addr g2) /\
                         (U64.v (wosize_of_object a gw) >= 1 ==>
                           U64.v (wosize_of_object a g2) >= 1) /\
                         (U64.v (wosize_of_object a gw) >= 1 /\
                          U64.v (hd_address a) + 16 <= heap_size ==>
                           read_word g2 a == read_word gw a))
              = alloc_split_fl_transfer_pre_part1 gw obj wz next_fp a
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
              chain_avoids_transfer_excl gw g2 head_fp (alloc_obj <: U64.t) big_fuel
            end
            else if leftover = 1 then begin
              chain_avoids_non_object gw head_fp alloc_obj big_fuel;
              chain_avoids_after_relink g prev_obj cur_fp next_fp head_fp fuel big_fuel;
              assert (chain_avoids gw head_fp cur_fp big_fuel = true);
              let transfer_aux_f (a: obj_addr) : Lemma
                (requires Seq.mem a (objects zero_addr gw) /\ a <> obj)
                (ensures Seq.mem a (objects zero_addr g2) /\
                         (U64.v (wosize_of_object a gw) >= 1 ==>
                           U64.v (wosize_of_object a g2) >= 1) /\
                         (U64.v (wosize_of_object a gw) >= 1 /\
                          U64.v (hd_address a) + 16 <= heap_size ==>
                           read_word g2 a == read_word gw a))
              = alloc_split_fl_transfer_pre_part1 gw obj wz next_fp a
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_f);
              chain_avoids_transfer_excl2 gw g2 head_fp (alloc_obj <: U64.t) cur_fp big_fuel
            end
            else begin
              // Exact fit: alloc_obj IS cur_fp, which left the list when prev
              // was rewired.
              chain_avoids_after_relink g prev_obj cur_fp next_fp head_fp fuel big_fuel;
              assert (chain_avoids gw head_fp cur_fp big_fuel = true);
              assert ((alloc_obj <: U64.t) == cur_fp);
              assert (leftover == 0);
              assert (block_wz == wz);
              let transfer_aux_e (a: obj_addr) : Lemma
                (requires Seq.mem a (objects zero_addr gw))
                (ensures Seq.mem a (objects zero_addr g2) /\
                         (U64.v (wosize_of_object a gw) >= 1 ==>
                           U64.v (wosize_of_object a g2) >= 1) /\
                         (U64.v (wosize_of_object a gw) >= 1 /\
                          U64.v (hd_address a) + 16 <= heap_size ==>
                           read_word g2 a == read_word gw a))
              = alloc_exact_fl_transfer_pre_part1 gw obj wz next_fp a
              in
              FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
              chain_avoids_transfer_excl gw g2 head_fp cur_fp big_fuel
            end
          end
          else ()
        end
      end
      else begin
        // ===== Advance: block too small, continue search =====
        assert (cur_fp <> next_fp);
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        walk_chain_append g head_fp (big_fuel - fuel) 1;
        walk_chain_one_step g cur_fp;
        walk_chain_valid_snoc g head_fp (big_fuel - fuel);
        alloc_search_obj_not_in_chain_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P3b: Top-level alloc_spec_obj_not_in_chain_part1
/// ---------------------------------------------------------------------------

let alloc_spec_obj_not_in_chain_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    walk_chain_zero g fp;
    walk_chain_valid_zero g fp;
    alloc_search_obj_not_in_chain_part1 g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// Section P4: alloc_spec body/other framing
///
/// alloc_from_block only writes to the header, remainder header, and remainder
/// link field. It does NOT write to the body [obj, obj + wz*8).
/// alloc_search additionally writes to prev_fp (a link in a different block).
/// ---------------------------------------------------------------------------


/// Inductive: alloc_search preserves reads in the body of the allocated object.
/// Inductive: alloc_search preserves reads in the body of a different object
/// that is not in the free-list chain.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
private let rec alloc_search_read_other
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    wz >= 1 /\
                    Seq.mem other (objects zero_addr g) /\
                    chain_avoids g cur_fp other fuel = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other g) * 8 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> other /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    read_word r.heap_out addr == read_word g addr))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      // chain_avoids gives cur_fp ≠ other
      chain_avoids_head_ne g cur_fp other fuel;
      assert (cur_fp <> other);
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found a suitable block (cur_fp <> other).
        wosize_of_object_spec other g;
        wosize_of_object_spec obj g;
        let other_wz = U64.v (wosize_of_object other g) in
        // `addr` lies wholly outside obj's block -- pure arithmetic, and the
        // prev-link write below changes no header, so it stays true of `gw`.
        (if U64.v other < U64.v obj then begin
           objects_separated zero_addr g other obj;
           assert (U64.v obj > U64.v other + other_wz * 8);
           assert (U64.v addr + 8 <= U64.v other + other_wz * 8);
           assert (U64.v addr + 8 <= U64.v hd)
         end else begin
           objects_separated zero_addr g obj other;
           assert (U64.v other > U64.v obj + block_wz * 8);
           assert (U64.v addr >= U64.v hd + (block_wz + 1) * 8)
         end);
        // The free-list replacement, read off transparently: `alloc_search`
        // builds `gw` from this exact term, so use the same one here.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        if prev_fp = 0UL then
          alloc_from_block_read_outside g obj wz next_fp addr
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // Reordered: the link write runs first, on `g`.
          let prev : obj_addr = prev_fp in
          let gw = write_word g (prev <: hp_addr) new_fp in
          hd_address_spec prev;
          hd_address_bounds prev;
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          // 1. the link write misses `addr`, which sits in other's body
          (if U64.v prev_fp < U64.v other then begin
             objects_separated zero_addr g prev other;
             assert (U64.v prev_fp + 8 <= U64.v other);
             assert (U64.v prev_fp + 8 <= U64.v addr)
           end else begin
             objects_separated zero_addr g other prev;
             assert (U64.v prev_fp > U64.v other + other_wz * 8);
             assert (U64.v addr + 8 <= U64.v prev_fp)
           end);
          read_write_different g (prev <: hp_addr) addr new_fp;
          assert (read_word gw addr == read_word g addr);
          // 2. and it leaves obj's block exactly as it was
          write_body_preserves_wfh_part1 g prev (prev <: hp_addr) new_fp;
          write_body_preserves_objects_local zero_addr g prev (prev <: hp_addr) new_fp;
          (if U64.v prev < U64.v obj then begin
             objects_separated zero_addr g prev obj;
             assert (U64.v prev + 8 <= U64.v hd)
           end else begin
             objects_separated zero_addr g obj prev;
             assert (U64.v hd + 8 <= U64.v prev)
           end);
          read_write_different g (prev <: hp_addr) hd new_fp;
          assert (read_word gw hd == hdr);
          assert (U64.v (getWosize (read_word gw hd)) == block_wz);
          getWosize_bound hdr;
          alloc_from_block_read_outside gw obj wz next_fp addr
        end
        else
          alloc_from_block_read_outside g obj wz next_fp addr
      end
      else begin
        // Block too small, continue search
        if U64.v hd + 16 <= heap_size then begin
          fl_valid_elim g cur_fp fuel;
          chain_avoids_tail g cur_fp other fuel
        end else ();
        alloc_search_read_other g head_fp cur_fp next_fp wz (fuel - 1) other addr
      end
    end
#pop-options

/// Top-level: alloc_spec preserves reads in the body of a different object
/// not in the free-list chain.
let alloc_spec_read_other (g: heap) (fp: U64.t) (requested_wz: nat)
                          (other: obj_addr) (addr: hp_addr)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_read_other g fp 0UL fp wz heap_words other addr

/// ---------------------------------------------------------------------------
/// Section P5: alloc_spec_preserves_chain_avoids_other
///
/// If excl was not in the free-list chain before alloc, it's not in the chain after.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 400 --fuel 1 --ifuel 0 --z3refresh"
private let rec alloc_search_preserves_chain_avoids_other
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  (excl: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    fl_valid g head_fp heap_words /\
                    fl_chain_terminates g head_fp heap_words /\
                    wz >= 1 /\
                    fuel <= heap_words /\
                    // excl avoids the chain from cur_fp
                    chain_avoids g cur_fp excl fuel = true /\
                    // excl avoids the entire chain from head_fp
                    chain_avoids g head_fp excl heap_words = true /\
                    // excl is a valid object
                    U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                    U64.v excl % U64.v mword == 0 /\
                    Seq.mem (excl <: obj_addr) (objects zero_addr g) /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
                       U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
                       read_word g (prev_fp <: obj_addr) = cur_fp)) /\
                    // Walk-chain invariants
                    walk_chain g head_fp (heap_words - fuel) = cur_fp /\
                    walk_chain_valid g head_fp (heap_words - fuel) /\
                    (prev_fp <> 0UL ==> fuel < heap_words /\
                                        walk_chain g head_fp (heap_words - fuel - 1) = prev_fp))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL ==>
                    chain_avoids r.heap_out r.fp_out excl heap_words = true))
          (decreases fuel)
  = let big_fuel = heap_words in
    if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      fl_valid_next g cur_fp fuel;
      wosize_of_object_spec obj g;
      wosize_of_object_bound obj g;
      getWosize_bound hdr;
      // excl ≠ cur_fp (from chain_avoids)
      chain_avoids_head_ne g cur_fp excl fuel;
      assert (cur_fp <> excl);
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      assert (U64.v hd + 16 <= heap_size);
      assert (fl_valid g next_fp (fuel - 1));
      fl_chain_terminates_elim g cur_fp fuel;
      assert (fl_chain_terminates g next_fp (fuel - 1));
      // chain_avoids g next_fp excl (fuel-1) from tail
      chain_avoids_tail g cur_fp excl fuel;
      assert (chain_avoids g next_fp excl (fuel - 1) = true);
      if block_wz >= wz then begin
        // ===== Found a suitable block =====
        let g' = fst (alloc_from_block g obj wz next_fp) in
        // The free-list replacement, read off transparently: `alloc_search`
        // builds `gw` from this exact term, so use the same one here.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        fl_valid_any_fuel g next_fp (fuel - 1) big_fuel;
        fl_chain_terminates_weaken g next_fp (fuel - 1) big_fuel;
        // cur_fp not in suffix
        fl_chain_predecessor_not_in_suffix_b g cur_fp fuel;
        not_in_fl_chain_b_is_chain_avoids g next_fp cur_fp (fuel - 1);
        assert (chain_avoids g next_fp cur_fp (fuel - 1) = true);
        if prev_fp = 0UL then begin
          // ===== prev_fp = 0: fp_out = new_fp, heap_out = g' =====
          (if block_wz - wz >= 1 then alloc_split_facts_part1 g obj wz next_fp
           else alloc_from_block_exact g obj wz next_fp);
          alloc_from_block_objects_facts_part1 g obj wz next_fp;
          fl_valid_any_fuel g cur_fp fuel big_fuel;
          if block_wz - wz >= 2 then begin
            // Split: the remainder keeps cur_fp, so the chain out of fp_out is
            // literally the old chain out of cur_fp, and no read on it moves.
            assert (new_fp == cur_fp);
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            chain_avoids_strengthen g cur_fp excl fuel big_fuel;
            chain_avoids_transfer g g' cur_fp excl big_fuel
          end else if block_wz - wz = 1 then begin
            // The block leaves the list; `obj` is the one object the transfer
            // cannot cover, and the suffix never visits it.
            assert (new_fp == next_fp);
            chain_avoids_strengthen g next_fp excl (fuel - 1) big_fuel;
            chain_avoids_strengthen g next_fp cur_fp (fuel - 1) big_fuel;
            let transfer_aux_f (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g) /\ a <> obj)
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_split_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_f);
            chain_avoids_transfer_excl2 g g' next_fp excl cur_fp big_fuel
          end else begin
            // ----- Exact fit: new_fp = next_fp -----
            assert (new_fp == next_fp);
            assert (block_wz - wz < 1);
            assert (block_wz == wz);
            alloc_exact_preserves_wfh_part1 g obj wz next_fp;
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr g))
              (ensures Seq.mem a (objects zero_addr g') /\
                       (U64.v (wosize_of_object a g) >= 1 ==>
                         U64.v (wosize_of_object a g') >= 1) /\
                       (U64.v (wosize_of_object a g) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g' a == read_word g a))
            = alloc_exact_fl_transfer_pre_part1 g obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            chain_avoids_strengthen g next_fp excl (fuel - 1) big_fuel;
            chain_avoids_transfer g g' next_fp excl big_fuel
          end
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // ===== prev_fp <> 0: fp_out = head_fp, heap_out = g2 =====
          let prev_obj : obj_addr = prev_fp in
          let gw = write_word g (prev_obj <: hp_addr) new_fp in
          let g2 = fst (alloc_from_block gw obj wz next_fp) in
          let d = big_fuel - fuel - 1 in
          // excl is not prev: the head chain visits prev and avoids excl.
          walk_chain_valid_prefix g head_fp (big_fuel - fuel) d;
          chain_avoids_weaken g head_fp excl big_fuel d;
          chain_avoids_unfold_steps g head_fp excl d big_fuel;
          assert (chain_avoids g prev_fp excl (big_fuel - d) = true);
          chain_avoids_head_ne g prev_fp excl (big_fuel - d);
          assert (prev_fp <> excl);
          chain_avoids_head_ne g cur_fp excl fuel;
          assert (cur_fp <> excl);

          // --- separation: prev's block is disjoint from obj's ---
          hd_address_spec prev_obj;
          hd_address_bounds prev_obj;
          wosize_of_object_spec prev_obj g;
          wosize_of_object_bound prev_obj g;
          if U64.v prev_fp < U64.v obj then begin
            objects_separated zero_addr g prev_obj obj;
            assert (U64.v (hd_address prev_obj) + 8 <= U64.v hd)
          end else begin
            objects_separated zero_addr g obj prev_obj;
            assert (U64.v prev_fp > U64.v obj + block_wz * 8);
            assert (U64.v (hd_address prev_obj) >= U64.v hd + (block_wz + 1) * 8)
          end;
          assert (U64.v prev_fp <> U64.v hd);

          (if block_wz - wz >= 1 then alloc_split_facts_part1 g obj wz next_fp
           else alloc_from_block_exact g obj wz next_fp);
          assert (new_fp == (if block_wz - wz >= 2 then (obj <: U64.t) else next_fp));
          fl_valid_any_fuel g cur_fp fuel big_fuel;
          (if block_wz - wz >= 2 then ()
           else if new_fp = prev_fp then begin
             assert (read_word g (prev_fp <: obj_addr) == cur_fp);
             assert (read_word g (cur_fp <: obj_addr) == next_fp);
             fl_chain_2cycle_not_terminates g prev_fp cur_fp (fuel - 1);
             assert false
           end else ());
          assert (new_fp <> prev_fp);

          // `gw` differs from `g` at exactly one word, so every OTHER object
          // address reads the same.  Every transfer out of `g` below needs
          // this frame, and it is the only thing they need.
          let frame_aux (a: obj_addr) : Lemma
            (requires (a <: U64.t) <> (prev_obj <: U64.t))
            (ensures read_word gw a == read_word g a)
          = aligned_distinct (prev_obj <: U64.t) (a <: U64.t);
            read_write_different g (prev_obj <: hp_addr) (a <: hp_addr) new_fp
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires frame_aux);

          // --- Step 1a: fl_valid gw head_fp ---
          fl_valid_field_write_tail_part1 g prev_obj new_fp big_fuel;
          fl_valid_field_write_part1 g prev_obj new_fp head_fp big_fuel big_fuel;
          assert (fl_valid gw head_fp big_fuel);

          // --- Step 1b: chain_avoids gw head_fp excl big_fuel ---
          // The suffix out of next_fp survives the single write at prev.
          chain_avoids_prev g prev_fp cur_fp next_fp (fuel - 1);
          chain_avoids_transfer_excl2 g gw next_fp excl prev_fp (fuel - 1);
          fl_chain_terminates_transfer_excl g gw next_fp prev_fp (fuel - 1);
          read_write_same g (prev_obj <: hp_addr) new_fp;
          assert (read_word gw (prev_obj <: obj_addr) == new_fp);
          (if block_wz - wz >= 2 then begin
             // new_fp is cur_fp, whose link in gw is still next_fp.
             read_write_different g (prev_obj <: hp_addr) (cur_fp <: hp_addr) new_fp;
             assert (read_word gw (cur_fp <: obj_addr) == next_fp);
             fl_chain_terminates_step gw cur_fp fuel;
             chain_avoids_unfold_step gw cur_fp excl fuel
           end else begin
             fl_chain_terminates_weaken gw next_fp (fuel - 1) fuel;
             chain_avoids_strengthen gw next_fp excl (fuel - 1) fuel
           end);
          assert (chain_avoids gw new_fp excl fuel = true);
          assert (fl_chain_terminates gw new_fp fuel);
          chain_avoids_unfold_step gw prev_fp excl (fuel + 1);
          fl_chain_terminates_step gw prev_fp (fuel + 1);
          assert (chain_avoids gw prev_fp excl (fuel + 1) = true);
          if d = 0 then begin
            walk_chain_zero g head_fp;
            assert (head_fp == prev_fp);
            chain_avoids_strengthen gw prev_fp excl (fuel + 1) big_fuel
          end else begin
            fl_chain_no_early_repeat g head_fp d big_fuel;
            fl_valid_weaken g head_fp big_fuel d;
            chain_avoids_transfer_excl2 g gw head_fp excl prev_fp d;
            walk_chain_valid_preserved g gw head_fp prev_fp d big_fuel;
            assert (walk_chain gw head_fp d == prev_fp);
            assert (big_fuel - d == fuel + 1);
            chain_avoids_unfold_steps gw head_fp excl d big_fuel
          end;
          assert (chain_avoids gw head_fp excl big_fuel = true);

          // --- Step 2: obj is untouched by the link write ---
          write_body_preserves_wfh_part1 g prev_obj (prev_obj <: hp_addr) new_fp;
          write_body_preserves_objects_local zero_addr g prev_obj (prev_obj <: hp_addr) new_fp;
          read_write_different g (prev_obj <: hp_addr) hd new_fp;
          assert (objects zero_addr gw == objects zero_addr g);
          assert (read_word gw hd == hdr);
          assert (U64.v (getWosize (read_word gw hd)) == block_wz);
          getWosize_bound hdr;
          assert (Seq.mem obj (objects zero_addr gw));

          // --- Step 3: carry it across the block writes ---
          if block_wz - wz >= 2 then begin
            let transfer_aux (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw))
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_split_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux);
            chain_avoids_transfer gw g2 head_fp excl big_fuel
          end
          else if block_wz - wz = 1 then begin
            chain_avoids_after_relink g prev_obj cur_fp next_fp head_fp fuel big_fuel;
            assert (chain_avoids gw head_fp cur_fp big_fuel = true);
            let transfer_aux_f (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw) /\ a <> obj)
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_split_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_f);
            chain_avoids_transfer_excl2 gw g2 head_fp excl cur_fp big_fuel
          end
          else begin
            assert (block_wz == wz);
            let transfer_aux_e (a: obj_addr) : Lemma
              (requires Seq.mem a (objects zero_addr gw))
              (ensures Seq.mem a (objects zero_addr g2) /\
                       (U64.v (wosize_of_object a gw) >= 1 ==>
                         U64.v (wosize_of_object a g2) >= 1) /\
                       (U64.v (wosize_of_object a gw) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size ==>
                         read_word g2 a == read_word gw a))
            = alloc_exact_fl_transfer_pre_part1 gw obj wz next_fp a
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_aux_e);
            chain_avoids_transfer gw g2 head_fp excl big_fuel
          end
        end
        else ()
      end
      else begin
        // ===== Block too small: advance to next =====
        assert (cur_fp <> next_fp);
        assert (read_word g obj == next_fp);
        assert (U64.v hd + 16 <= heap_size);
        alloc_search_advance g head_fp prev_fp cur_fp wz fuel;
        walk_chain_append g head_fp (big_fuel - fuel) 1;
        walk_chain_one_step g cur_fp;
        walk_chain_valid_snoc g head_fp (big_fuel - fuel);
        // chain_avoids for next_fp already established above
        chain_avoids_weaken g next_fp excl (fuel - 1) (fuel - 1);
        // chain_avoids g head_fp excl big_fuel still holds (unchanged)
        alloc_search_preserves_chain_avoids_other g head_fp cur_fp next_fp wz (fuel - 1) excl
      end
    end
#pop-options

/// Helper: when alloc_search fails (obj_out = 0UL), heap and fp are unchanged.
#restart-solver
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
private let rec alloc_search_no_alloc_unchanged
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out = 0UL ==> (r.heap_out == g /\ r.fp_out == head_fp)))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      if block_wz >= wz then begin
        // Two sub-cases, both fine: `alloc_search` either bails on the
        // right-justified address (heap and fp genuinely unchanged) or
        // allocates, and the allocated address is above cur_fp, hence
        // non-null, so the conclusion is vacuous.
        hd_address_spec obj;
        hd_address_bounds obj;
        let leftover = block_wz - wz in
        let ahn = U64.v hd + leftover * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
        else
          assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8)))
                    == ahn + 8)
      end
      else begin
        let next_fp =
          if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
        alloc_search_no_alloc_unchanged g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// Top-level: alloc_spec preserves chain_avoids for a different object.
#restart-solver
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
let alloc_spec_preserves_chain_avoids_other (g: heap) (fp: U64.t) (requested_wz: nat)
                                            (excl: U64.t)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    let big_fuel = heap_words in
    walk_chain_zero g fp;
    walk_chain_valid_zero g fp;
    assert (walk_chain g fp 0 == fp);
    assert (walk_chain_valid g fp 0);
    assert (big_fuel - big_fuel = 0);
    alloc_search_preserves_chain_avoids_other g fp 0UL fp wz big_fuel excl;
    alloc_search_no_alloc_unchanged g fp 0UL fp wz big_fuel
#pop-options

/// ===========================================================================
/// Section P4: alloc_spec preserves well_formed_heap_part4 (no infix objects)
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// P4a: alloc_from_block_preserves_wfh_part4
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
private let alloc_from_block_preserves_wfh_part4
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    well_formed_heap_part4 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz) /\
                    wz >= 1)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    well_formed_heap_part4 g'))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let (g', _) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    hd_address_bounds obj;
    if block_wz - wz >= 1 then begin
      // Split, or a one-word leftover: the same two headers are written, the
      // remainder at `hd` (blue, wosize leftover - 1) and the right-justified
      // allocated block above it (white, wosize wz).  Both carry tag 0.
      alloc_split_facts_part1 g obj wz next_fp;
      let leftover = block_wz - wz in
      let ahn = U64.v hd + leftover * 8 in
      let rem_wz = leftover - 1 in
      // wz >= 1 and hd + (block_wz + 1) * 8 <= heap_size leave a full word
      // above the allocated header, so its object address is in range.
      assert (ahn + 8 + wz * 8 == U64.v hd + (block_wz + 1) * 8);
      assert (ahn + 8 < heap_size);
      let alloc_obj_addr : obj_addr = U64.uint_to_t (ahn + 8) in
      hd_address_of_succ (U64.uint_to_t ahn <: hp_addr) (alloc_obj_addr <: hp_addr);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_infix h g'))
      = tag_of_object_spec h g';
        is_infix_spec h g';
        hd_address_spec h;
        if h = obj then begin
          // Header = make_header rem_wz blue_bits 0UL -> tag = 0
          make_header_getTag (U64.uint_to_t rem_wz) blue_bits 0UL;
          infix_tag_val ()
        end else if h = alloc_obj_addr then begin
          // Header = make_header wz white_bits 0UL -> tag = 0
          make_header_getTag (U64.uint_to_t wz) white_bits 0UL;
          infix_tag_val ()
        end else begin
          // Header unchanged from g, use part4 of g
          let aux_before (p: hp_addr) : Lemma
            (requires U64.v p < U64.v hd)
            (ensures read_word g' p == read_word g p)
          = alloc_split_g3_agrees_part1 g obj wz next_fp p
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
          objects_addresses_gt_start zero_addr g obj;
          split_new_mem_in_old_or_rem_part1 zero_addr g g' obj wz block_wz h;
          assert (Seq.mem h (objects zero_addr g));
          wosize_of_object_spec obj g;
          if U64.v h < U64.v obj then begin
            objects_separated zero_addr g h obj;
            alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
          end else begin
            objects_separated zero_addr g obj h;
            alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
          end;
          // Now read_word g' (hd_address h) == read_word g (hd_address h)
          tag_of_object_spec h g;
          is_infix_spec h g
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else begin
      // Exact fit case: g' = write_word g hd (make_header block_wz white_bits 0UL)
      alloc_from_block_exact g obj wz next_fp;
      let new_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
      make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj new_hdr;
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_infix h g'))
      = tag_of_object_spec h g';
        is_infix_spec h g';
        hd_address_spec h;
        if h = obj then begin
          make_header_getTag (U64.uint_to_t wz) white_bits 0UL;
          read_write_same g hd new_hdr;
          infix_tag_val ()
        end else begin
          if U64.v h < U64.v obj then
            objects_separated zero_addr g h obj
          else
            objects_separated zero_addr g obj h;
          read_write_different g hd (hd_address h) new_hdr;
          tag_of_object_spec h g;
          is_infix_spec h g
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P4b: write_body_preserves_wfh_part4
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
private let write_body_preserves_wfh_part4
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    well_formed_heap_part4 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v addr >= U64.v obj /\
                    U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
                    U64.v addr % 8 = 0)
          (ensures well_formed_heap_part4 (write_word g addr v))
  = write_body_preserves_objects_local zero_addr g obj addr v;
    let g' = write_word g addr v in
    assert (objects zero_addr g' == objects zero_addr g);
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures ~(is_infix h g'))
    = hd_address_spec h;
      hd_address_spec obj;
      tag_of_object_spec h g';
      tag_of_object_spec h g;
      is_infix_spec h g';
      is_infix_spec h g;
      if h = obj then
        read_write_different g addr (hd_address h) v
      else begin
        if U64.v h < U64.v obj then begin
          objects_separated zero_addr g h obj;
          read_write_different g addr (hd_address h) v
        end else begin
          objects_separated zero_addr g obj h;
          read_write_different g addr (hd_address h) v
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// P4c: alloc_search_preserves_wfh_part4 — recursive proof
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_wfh_part4
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    well_formed_heap_part4 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    wz >= 1 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    well_formed_heap_part4 r.heap_out))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      assert (Seq.mem obj (objects zero_addr g));
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // The free-list replacement, read off transparently: `alloc_search`
        // builds `gw` from this exact term, so use the same one here.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        if prev_fp = 0UL then begin
          alloc_from_block_preserves_wfh_part4 g obj wz next_fp;
          alloc_from_block_preserves_wfh_part1 g obj wz next_fp
        end
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // Reordered: the link write runs first, on `g`, and the block writes
          // on the result.  A body write preserves both shape invariants, and
          // the block writes then see exactly the block they saw before.
          let prev : obj_addr = prev_fp in
          let gw = write_word g (prev <: hp_addr) new_fp in
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          hd_address_spec prev;
          hd_address_bounds prev;
          wosize_of_object_spec obj g;
          write_body_preserves_wfh_part4 g prev (prev <: hp_addr) new_fp;
          write_body_preserves_wfh_part1 g prev (prev <: hp_addr) new_fp;
          write_body_preserves_objects_local zero_addr g prev (prev <: hp_addr) new_fp;
          // prev's block is disjoint from obj's, so obj's header survives.
          if U64.v prev < U64.v obj then begin
            objects_separated zero_addr g prev obj;
            assert (U64.v prev + 8 <= U64.v hd)
          end else begin
            objects_separated zero_addr g obj prev;
            assert (U64.v hd + 8 <= U64.v prev)
          end;
          read_write_different g (prev <: hp_addr) hd new_fp;
          assert (objects zero_addr gw == objects zero_addr g);
          assert (read_word gw hd == hdr);
          assert (U64.v (getWosize (read_word gw hd)) == block_wz);
          getWosize_bound hdr;
          assert (Seq.mem obj (objects zero_addr gw));
          alloc_from_block_preserves_wfh_part4 gw obj wz next_fp;
          alloc_from_block_preserves_wfh_part1 gw obj wz next_fp
        end
        else begin
          alloc_from_block_preserves_wfh_part4 g obj wz next_fp;
          alloc_from_block_preserves_wfh_part1 g obj wz next_fp
        end
      end
      else begin
        fl_valid_next g cur_fp fuel;
        assert (cur_fp <> next_fp);
        assert (U64.v hd + 16 <= heap_size);
        assert (fl_valid g next_fp (fuel - 1));
        fl_chain_terminates_elim g cur_fp fuel;
        assert (fl_chain_terminates g next_fp (fuel - 1));
        alloc_search_preserves_wfh_part4 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// P4d: Top-level alloc_spec_preserves_wfh_part4
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_wfh_part4 (g: heap) (fp: U64.t) (requested_wz: nat)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_wfh_part4 g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// Allocation framing: field reads for non-allocated objects
/// ---------------------------------------------------------------------------

/// General helper: alloc_search preserves reads at addresses that:
/// 1. Are in the body of some object `owner` in objects(g)
/// 2. addr > owner (i.e., not at field 0 of owner)
/// 3. owner ≠ cur_fp OR addr doesn't overlap [hd(owner) .. owner+(wz+2)*8)
///
/// Key insight: addr > owner ensures addr ≠ prev_fp even if owner = prev_fp.
#restart-solver
/// Top-level: alloc_spec preserves reads at field j > 0 of non-allocated objects.
/// Re-export Part1 vals (must appear after alloc_spec_read_field_gt0 per .fsti ordering)
let alloc_from_block_rem_in_objects_part1 = alloc_from_block_rem_in_objects_part1
let alloc_from_block_preserves_objects_part1 = alloc_from_block_preserves_objects_part1


/// ---------------------------------------------------------------------------
/// Right-justification creates exactly one object: the allocated block
/// ---------------------------------------------------------------------------

/// In the exact-fit case no object appears: only the header at `hd` is
/// rewritten, and with the same wosize.
#restart-solver
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"
private let alloc_from_block_no_new_objects_exact
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz == wz) /\
                    (let (g', _) = alloc_from_block g obj wz next_fp in
                     Seq.mem h (objects zero_addr g')))
          (ensures Seq.mem h (objects zero_addr g))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    alloc_from_block_exact g obj wz next_fp;
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
    header_write_same_wosize_preserves_objects g obj alloc_hdr
#pop-options

/// The only object allocation can create is the RIGHT-JUSTIFIED allocated
/// block, at `hd + leftover * 8 + 8`.  The remainder keeps `obj`'s address --
/// it only shrinks -- so it is not new, which is exactly the structural gain
/// of right-justification over placing the object at the low end.
#restart-solver
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let alloc_from_block_only_new_is_alloc
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hd = hd_address obj in
                     let block_wz = U64.v (getWosize (read_word g hd)) in
                     block_wz >= wz /\ wz >= 1 /\
                     U64.v hd + (block_wz - wz) * 8 + 8 < heap_size) /\
                    (let (g', _) = alloc_from_block g obj wz next_fp in
                     Seq.mem h (objects zero_addr g') /\
                     ~(Seq.mem h (objects zero_addr g))))
          (ensures (let hd = hd_address obj in
                    let block_wz = U64.v (getWosize (read_word g hd)) in
                    U64.v h == U64.v hd + (block_wz - wz) * 8 + 8))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    if block_wz - wz >= 1 then begin
      alloc_split_facts_part1 g obj wz next_fp;
      let (g3, _) = alloc_from_block g obj wz next_fp in
      let aux_before (p: hp_addr) : Lemma
        (requires U64.v p < U64.v hd)
        (ensures read_word g3 p == read_word g p)
      = alloc_split_g3_agrees_part1 g obj wz next_fp p
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
      objects_addresses_gt_start zero_addr g obj;
      split_new_mem_in_old_or_rem_part1 zero_addr g g3 obj wz block_wz h
    end else
      alloc_from_block_no_new_objects_exact g obj wz next_fp h
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_search_new_objects_blue_part1: recursive proof
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 75 --fuel 1 --ifuel 0"
private let rec alloc_search_new_objects_blue_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    wz >= 1 /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL ==>
                    (forall (x: obj_addr).
                      Seq.mem x (objects zero_addr r.heap_out) /\
                      ~(Seq.mem x (objects zero_addr g)) /\
                      (x <: U64.t) <> r.obj_out ==>
                      is_blue x r.heap_out = true)))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      assert (Seq.mem obj (objects zero_addr g));
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found a suitable block.  Right-justification makes this short: the
        // only object allocation creates is `obj_out` itself, and `obj_out` is
        // exactly what the statement excludes.
        let leftover = block_wz - wz in
        let ahn = U64.v hd + leftover * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then
          // `alloc_search` bails here with obj_out = 0; nothing to prove.
          ()
        else begin
          hd_address_bounds obj;
          wosize_of_object_spec obj g;
          wosize_of_object_bound obj g;
          // The free-list replacement, read off transparently: `alloc_search`
          // builds `gw` from this exact term, so use the same one here.
          let new_rem_fp = alloc_replacement_fp g obj wz next_fp in
          alloc_replacement_fp_eq g obj wz next_fp;
          if prev_fp = 0UL then begin
            let g' = fst (alloc_from_block g obj wz next_fp) in
            let aux (x: obj_addr) : Lemma
              (requires Seq.mem x (objects zero_addr g') /\
                        ~(Seq.mem x (objects zero_addr g)))
              (ensures U64.v x == ahn + 8)
            = alloc_from_block_only_new_is_alloc g obj wz next_fp x
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
          end
          else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                  U64.v prev_fp % U64.v mword = 0 then begin
            // Reordered: the link write runs first, and it changes no object's
            // header, so the enumeration it hands on is still `objects g`.
            let prev : obj_addr = prev_fp in
            let gw = write_word g (prev <: hp_addr) new_rem_fp in
            let g2 = fst (alloc_from_block gw obj wz next_fp) in
            wosize_of_object_spec prev g;
            wosize_of_object_bound prev g;
            hd_address_spec prev;
            hd_address_bounds prev;
            write_body_preserves_wfh_part1 g prev (prev <: hp_addr) new_rem_fp;
            write_body_preserves_objects_local zero_addr g prev (prev <: hp_addr) new_rem_fp;
            if U64.v prev < U64.v obj then begin
              objects_separated zero_addr g prev obj;
              assert (U64.v prev + 8 <= U64.v hd)
            end else begin
              objects_separated zero_addr g obj prev;
              assert (U64.v hd + 8 <= U64.v prev)
            end;
            read_write_different g (prev <: hp_addr) hd new_rem_fp;
            assert (objects zero_addr gw == objects zero_addr g);
            assert (read_word gw hd == hdr);
            assert (U64.v (getWosize (read_word gw hd)) == block_wz);
            getWosize_bound hdr;
            assert (Seq.mem obj (objects zero_addr gw));
            let aux (x: obj_addr) : Lemma
              (requires Seq.mem x (objects zero_addr g2) /\
                        ~(Seq.mem x (objects zero_addr gw)))
              (ensures U64.v x == ahn + 8)
            = alloc_from_block_only_new_is_alloc gw obj wz next_fp x
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
          end
          else ()
        end
      end
      else begin
        if U64.v hd + 16 <= heap_size then begin
          fl_valid_next g cur_fp fuel;
          assert (cur_fp <> next_fp);
          assert (fl_valid g next_fp (fuel - 1));
          fl_chain_terminates_elim g cur_fp fuel;
          assert (fl_chain_terminates g next_fp (fuel - 1));
          alloc_search_new_objects_blue_part1 g head_fp cur_fp next_fp wz (fuel - 1)
        end
        else ()
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: alloc_spec_new_objects_blue_part1
/// ---------------------------------------------------------------------------

let alloc_spec_new_objects_blue_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_new_objects_blue_part1 g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// alloc_from_block_objects_backward_part1:
/// Backward inclusion -- the only new object is the right-justified block.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let alloc_from_block_objects_backward_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  = alloc_from_block_only_new_is_alloc g obj wz next_fp h
#pop-options


/// ===========================================================================
/// Section: alloc_spec preserves no_black_objects (part1 variant)
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// Helper: writing within a body field preserves no_black_objects.
/// No well_formed_heap needed — just objects_separated + read_write_different.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
private let field_write_preserves_no_black_part1
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires GC.Spec.Mark.no_black_objects g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v addr >= U64.v obj /\
                    U64.v addr < U64.v obj + U64.v (wosize_of_object obj g) * 8 /\
                    U64.v addr % 8 = 0)
          (ensures GC.Spec.Mark.no_black_objects (write_word g addr v))
  = let g' = write_word g addr v in
    write_body_preserves_objects_local zero_addr g obj addr v;
    let aux (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr g'))
      (ensures ~(is_black h g'))
    = assert (Seq.mem h (objects zero_addr g));
      hd_address_spec h;
      hd_address_spec obj;
      if U64.v h <= U64.v obj then begin
        read_write_different g addr (hd_address h) v;
        color_of_header_eq h g g'
      end else begin
        objects_separated zero_addr g obj h;
        read_write_different g addr (hd_address h) v;
        color_of_header_eq h g g'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_from_block preserves no_black_objects under well_formed_heap_part1.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let alloc_from_block_preserves_no_black_part1
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires GC.Spec.Mark.no_black_objects g /\
                    well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz /\ wz >= 1))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    GC.Spec.Mark.no_black_objects g'))
  = let hdr = read_word g (hd_address obj) in
    let block_wz = U64.v (getWosize hdr) in
    let hd = hd_address obj in
    let (g', rem_fp) = alloc_from_block g obj wz next_fp in
    hd_address_spec obj;
    getWosize_bound hdr;
    wosize_of_object_spec obj g;
    if block_wz - wz >= 1 then begin
      // Split, or a one-word leftover: the remainder keeps `hd` and turns
      // blue, and the right-justified allocated block above it turns white.
      // Neither is black, and nothing else is touched.
      alloc_split_facts_part1 g obj wz next_fp;
      let leftover = block_wz - wz in
      let ahn = U64.v hd + leftover * 8 in
      let rem_wz = leftover - 1 in
      assert (ahn + 8 + wz * 8 == U64.v hd + (block_wz + 1) * 8);
      assert (ahn + 8 < heap_size);
      let alloc_obj_addr : obj_addr = U64.uint_to_t (ahn + 8) in
      hd_address_of_succ (U64.uint_to_t ahn <: hp_addr) (alloc_obj_addr <: hp_addr);
      // Frame: reads before hd_address(obj) are preserved
      let aux_before (p: hp_addr) : Lemma
        (requires U64.v p < U64.v hd)
        (ensures read_word g' p == read_word g p)
      = alloc_split_g3_agrees_part1 g obj wz next_fp p
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_before);
      // Color facts for the two rewritten headers
      make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
      getColor_raw (make_header (U64.uint_to_t wz) white_bits 0UL);
      make_header_getColor (U64.uint_to_t rem_wz) blue_bits 0UL;
      getColor_raw (make_header (U64.uint_to_t rem_wz) blue_bits 0UL);
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_black h g'))
      = objects_addresses_gt_start zero_addr g obj;
        split_new_mem_in_old_or_rem_part1 zero_addr g g' obj wz block_wz h;
        if U64.v h = ahn + 8 then begin
          // The allocated block: white header -> not black
          hd_address_spec alloc_obj_addr;
          color_of_object_spec alloc_obj_addr g';
          is_black_iff alloc_obj_addr g'
        end else begin
          assert (Seq.mem h (objects zero_addr g));
          if h = obj then begin
            // The remainder, still at `obj`: blue header -> not black
            hd_address_spec obj;
            color_of_object_spec obj g';
            is_black_iff obj g'
          end else begin
            // Pre-existing other object: header unchanged -> not black
            hd_address_spec h;
            if U64.v h < U64.v obj then begin
              objects_separated zero_addr g h obj;
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
            end else begin
              objects_separated zero_addr g obj h;
              assert (U64.v (hd_address h) > U64.v hd + block_wz * 8);
              alloc_split_g3_agrees_part1 g obj wz next_fp (hd_address h)
            end;
            color_of_header_eq h g g'
          end
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else begin
      // Exact fit case
      alloc_from_block_exact g obj wz next_fp;
      let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
      getWosize_bound hdr;
      make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
      header_write_same_wosize_preserves_objects g obj alloc_hdr;
      read_write_same g hd alloc_hdr;
      make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
      getColor_raw alloc_hdr;
      let aux (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr g'))
        (ensures ~(is_black h g'))
      = assert (Seq.mem h (objects zero_addr g));
        if h = obj then begin
          color_of_object_spec obj g';
          is_black_iff obj g'
        end else begin
          hd_address_spec h;
          if U64.v h < U64.v obj then
            objects_separated zero_addr g h obj
          else
            objects_separated zero_addr g obj h;
          read_write_different g hd (hd_address h) alloc_hdr;
          color_of_header_eq h g g'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// alloc_search preserves no_black_objects (part1 variant)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_no_black_part1
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma (requires GC.Spec.Mark.no_black_objects g /\
                    well_formed_heap_part1 g /\
                    wz >= 1 /\
                    fl_valid g cur_fp fuel /\
                    fl_chain_terminates g cur_fp fuel /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    GC.Spec.Mark.no_black_objects r.heap_out))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let block_wz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      fl_valid_gives_mem g cur_fp fuel;
      fl_valid_gives_wosize g cur_fp fuel;
      wosize_of_object_spec obj g;
      assert (Seq.mem obj (objects zero_addr g));
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // The free-list replacement, read off transparently: `alloc_search`
        // builds `gw` from this exact term, so use the same one here.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        if prev_fp = 0UL then
          alloc_from_block_preserves_no_black_part1 g obj wz next_fp
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0 then begin
          // Reordered: the link write runs first, on `g`.  A body write
          // touches no header, so no colour changes; the block writes then
          // run on a heap that still has no black object.
          let prev : obj_addr = prev_fp in
          let gw = write_word g (prev <: hp_addr) new_fp in
          hd_address_spec prev;
          hd_address_bounds prev;
          wosize_of_object_spec prev g;
          wosize_of_object_bound prev g;
          wfh_part1_obj_bound g prev;
          field_write_preserves_no_black_part1 g prev (prev <: hp_addr) new_fp;
          write_body_preserves_wfh_part1 g prev (prev <: hp_addr) new_fp;
          write_body_preserves_objects_local zero_addr g prev (prev <: hp_addr) new_fp;
          if U64.v prev < U64.v obj then begin
            objects_separated zero_addr g prev obj;
            assert (U64.v prev + 8 <= U64.v hd)
          end else begin
            objects_separated zero_addr g obj prev;
            assert (U64.v hd + 8 <= U64.v prev)
          end;
          read_write_different g (prev <: hp_addr) hd new_fp;
          assert (objects zero_addr gw == objects zero_addr g);
          assert (read_word gw hd == hdr);
          assert (U64.v (getWosize (read_word gw hd)) == block_wz);
          getWosize_bound hdr;
          assert (Seq.mem obj (objects zero_addr gw));
          alloc_from_block_preserves_no_black_part1 gw obj wz next_fp
        end
        else
          alloc_from_block_preserves_no_black_part1 g obj wz next_fp
      end
      else begin
        fl_valid_elim g cur_fp fuel;
        (if U64.v hd + 16 <= heap_size then
          fl_chain_terminates_elim g cur_fp fuel);
        alloc_search_preserves_no_black_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Top-level: alloc_spec preserves no_black_objects (part1 variant)
/// ---------------------------------------------------------------------------

let alloc_spec_preserves_no_black_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_no_black_part1 g fp 0UL fp wz heap_words

#pop-options // Module-level z3rlimit 10
