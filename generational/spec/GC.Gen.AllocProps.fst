/// ---------------------------------------------------------------------------
/// GC.Gen.AllocProps — Properties of alloc_spec needed for promotion proofs
/// ---------------------------------------------------------------------------
///
/// Wrapper lemmas that derive needed allocator properties from
/// existing GC.Spec.Allocator.Lemmas infrastructure.

module GC.Gen.AllocProps

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

/// ---------------------------------------------------------------------------
/// When alloc_spec succeeds, the returned obj_out is a valid obj_addr
/// ---------------------------------------------------------------------------

/// Build an `hp_addr` from a word-aligned, in-bounds offset.
///
/// Query splitting checks this refinement in the caller's full context, where
/// `U64.v (U64.uint_to_t a) % U64.v mword == 0` times out; proving it once here
/// keeps the caller's goal trivial.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let mk_hp_addr (a: nat{a < heap_size /\ a % U64.v mword == 0}) : (r: hp_addr{U64.v r == a}) =
  assert (a < pow2 64);
  U64.uint_to_t a

/// Word-aligned offsets stay word-aligned when advanced by whole words.
private let aligned_plus_mul8 (base: nat{base % U64.v mword == 0}) (k: nat)
  : Lemma ((base + k * 8) % U64.v mword == 0)
  = FStar.Math.Lemmas.modulo_addition_lemma base 8 k
#pop-options

/// The allocator only returns cur_fp after checking:
///   U64.v cur_fp >= U64.v mword, < heap_size, % mword == 0
/// So obj_out satisfies the obj_addr refinement.
///
/// Proof strategy: unfold alloc_spec into alloc_search and observe that
/// obj_out is set to cur_fp which already passed all guard checks.
#push-options "--z3rlimit 60 --fuel 4 --ifuel 1"
let rec alloc_search_obj_valid
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0)))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then begin
      // obj_out is now the right-justified object address, cur_fp + leftover*8,
      // and alloc_search guards it: out of bounds means obj_out = 0UL, which
      // makes the implication vacuous.  In bounds, obj_out = ahn + 8 and the
      // guard supplies exactly the three refinement facts.
      let leftover = block_wz - wz in
      let ahn = U64.v hd + leftover * 8 in
      if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
      else begin
        aligned_plus_mul8 (U64.v hd) leftover;
        hd_address_spec obj;
        // cur_fp = hd + 8, so the reported object is ahn + 8, which the guard
        // has just bounded; that also keeps the U64.add below pow2 64.
        assert (leftover * 8 < heap_size);
        assert (U64.v (U64.uint_to_t (leftover * 8)) == leftover * 8);
        assert (U64.v cur_fp + leftover * 8 == ahn + 8);
        assert (ahn + 8 < heap_size)
      end
    end
    else
      alloc_search_obj_valid g head_fp cur_fp next_fp wz (fuel - 1)
  end
#pop-options

/// Top-level: alloc_spec returns a valid obj_addr when successful
let alloc_spec_obj_valid (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0)))
  =
  let wz = if requested_wz = 0 then 1 else requested_wz in
  alloc_search_obj_valid g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// When alloc_spec succeeds, obj_out is in objects zero_addr heap_out
/// ---------------------------------------------------------------------------

/// The allocated object was a free-list node, hence already in objects zero_addr g.
/// alloc_spec_preserves_objects shows all old objects survive.
/// So obj_out is in objects zero_addr heap_out.
///
/// Proof: obj_out = cur_fp which is in the free list. fl_valid ensures
/// free-list nodes are in objects. alloc_spec_preserves_objects preserves them.
/// ---------------------------------------------------------------------------
/// After alloc, wosize of the allocated object >= requested_wz
/// ---------------------------------------------------------------------------

/// alloc_from_block either:
/// - Uses exact fit: writes header with block_wz >= requested_wz
/// - Splits: writes header with exactly requested_wz
/// In both cases: wosize_of_object obj_out heap_out >= requested_wz
///
/// This is harder to prove from outside — we'd need to unfold alloc_from_block.
///
/// Key insight: alloc_from_block either:
/// - Exact fit (bwz - wz < 2): writes header with bwz >= wz
/// - Split: writes header with exactly wz
/// In both cases, wosize_of_object obj heap_out >= wz.
///
/// Strategy: prove a helper for alloc_from_block, then use it in alloc_search.

module SA = GC.Spec.Allocator

/// Helper: after alloc_from_block, the header at obj has wz <= wosize <= wz + 1.
/// Every branch below pins the wosize exactly (to [bwz] on an exact fit, to [wz]
/// on a split), so both bounds fall out of the same case analysis.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
/// The allocated block declares EXACTLY the requested wosize.
///
/// This is the property the whole right-justification change exists to
/// establish.  Note it is stated about the ALLOCATED header, at
/// hd + leftover * 8, not about `obj`: with the object right-justified, the
/// block sitting at `obj` is the remainder (or, at leftover = 1, the empty
/// block), so the old form -- a bound on `wosize_of_object obj` -- no longer
/// describes the allocation at all.
let alloc_from_block_wosize_lemma
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires (let hd = hd_address obj in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz >= wz /\
                     U64.v hd + (bwz - wz) * 8 < heap_size))
          (ensures (let hd = hd_address obj in
                    let bwz = U64.v (getWosize (read_word g hd)) in
                    let ahn = U64.v hd + (bwz - wz) * 8 in
                    let (g', _) = alloc_from_block g obj wz next_fp in
                    ahn % U64.v mword == 0 /\
                    U64.v (getWosize (read_word g' (mk_hp_addr ahn))) == wz))
  =
  let hd = hd_address obj in
  let hdr = read_word g hd in
  let bwz = U64.v (getWosize hdr) in
  let leftover = bwz - wz in
  hd_address_spec obj;
  hd_address_bounds obj;
  aligned_plus_mul8 (U64.v hd) leftover;
  let ahn = U64.v hd + leftover * 8 in
  let ah : hp_addr = mk_hp_addr ahn in
  let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
  AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
  if leftover = 0 then begin
    // ah = hd: a single write, and it is the allocated header.
    SA.alloc_from_block_exact g obj wz next_fp;
    read_write_same g hd ahdr
  end
  else begin
    // Two writes; the allocated header is the second, at ah > hd.
    SA.alloc_from_block_split_normal g obj wz next_fp;
    let rhdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
    let g1 = write_word g hd rhdr in
    read_write_same g1 ah ahdr
  end
#pop-options

/// After alloc_search finds a block and returns obj_out, the output heap
/// has a write_word to prev_fp (if non-zero). This doesn't affect hd_address(obj),
/// provided prev_fp and hd_address(obj) are separated (which holds in alloc_search
/// because prev_fp is a different free-list node than cur_fp/obj).
#push-options "--z3rlimit 12 --fuel 1 --ifuel 1"
/// The write lands on a different word than [obj]'s header, so the header --- and
/// hence the wosize --- is unchanged.  Stating this as an equality subsumes both
/// the lower- and upper-bound forms the callers below need.
private let write_prev_preserves_wosize
  (g_after_alloc: heap) (obj: obj_addr) (prev_fp: U64.t) (val_fp: U64.t)
  : Lemma (requires prev_fp <> 0UL /\
                    U64.v prev_fp >= U64.v mword /\
                    U64.v prev_fp < heap_size /\
                    U64.v prev_fp % U64.v mword = 0 /\
                    prev_fp <> hd_address obj)
          (ensures (let g2 = write_word g_after_alloc (prev_fp <: hp_addr) val_fp in
                    wosize_of_object obj g2 == wosize_of_object obj g_after_alloc))
  =
  let hd = hd_address obj in
  hd_address_spec obj;
  hd_address_bounds obj;
  let g2 = write_word g_after_alloc (prev_fp <: hp_addr) val_fp in
  wosize_of_object_spec obj g2;
  wosize_of_object_spec obj g_after_alloc;
  let p = U64.v (prev_fp <: hp_addr) in
  let h = U64.v hd in
  FStar.Math.Lemmas.lemma_div_exact p 8;
  FStar.Math.Lemmas.lemma_div_exact h 8;
  let kp = p / 8 in
  let kh = h / 8 in
  if kp > kh then begin
    FStar.Math.Lemmas.lemma_mult_le_right 8 (kh + 1) kp;
    FStar.Math.Lemmas.distributivity_add_left kh 1 8
  end else begin
    FStar.Math.Lemmas.lemma_mult_le_right 8 (kp + 1) kh;
    FStar.Math.Lemmas.distributivity_add_left kp 1 8
  end;
  read_write_different g_after_alloc (prev_fp <: hp_addr) hd val_fp
#pop-options

/// Main recursive proof
/// ---------------------------------------------------------------------------
/// Part1-only versions: weaker preconditions (no full well_formed_heap)
/// ---------------------------------------------------------------------------

/// obj_out is an object of the OUTPUT heap.
///
/// Under right-justification the allocated block is a NEW object whenever the
/// block was split -- the remainder keeps `obj` -- so the old route (membership
/// in the INPUT heap from fl_valid, then "alloc preserves objects") no longer
/// works: the allocated address is not in `objects zero_addr g` at all.  At
/// leftover = 0 the allocation is still the original block; at leftover >= 1 it
/// is the second piece of the split, supplied by
/// alloc_from_block_alloc_in_objects_part1.
#push-options "--z3rlimit 60 --fuel 4 --ifuel 1"
let rec alloc_search_obj_in_objects_post_part1
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\ AllocLemmas.fl_valid g cur_fp fuel /\
              // carried so the prev-link write can be shown to leave the
              // enumeration alone; discharged for cur_fp on each recursive step
              (prev_fp = 0UL \/
               (prev_fp <> cur_fp /\
                U64.v prev_fp >= U64.v mword /\
                U64.v prev_fp < heap_size /\
                U64.v prev_fp % U64.v mword = 0 /\
                Seq.mem (prev_fp <: obj_addr) (objects zero_addr g) /\
                U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0 /\
               Seq.mem (r.obj_out <: obj_addr) (objects zero_addr r.heap_out))))
    (decreases fuel)
  =
  alloc_search_obj_valid g head_fp prev_fp cur_fp wz fuel;
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    hd_address_spec obj;
    hd_address_bounds obj;
    if block_wz >= wz then begin
      let leftover = block_wz - wz in
      let ahn = U64.v hd + leftover * 8 in
      if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
      else begin
        aligned_plus_mul8 (U64.v hd) leftover;
        // Reordered: `alloc_search` writes prev's link on `g` FIRST and runs
        // the block writes on the result, so the block lemmas below have to
        // be applied to that intermediate heap, not to `g`.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        let base =
          if prev_fp = 0UL then g
          else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                  U64.v prev_fp % U64.v mword = 0
          then write_word g (prev_fp <: hp_addr) new_fp
          else g
        in
        // `base` is `g` with at most one body word rewritten: same objects,
        // same headers, in particular the same block at `obj`.
        (if prev_fp = 0UL then ()
         else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
           let prev : obj_addr = prev_fp in
           hd_address_spec prev;
           hd_address_bounds prev;
           wosize_of_object_spec prev g;
           wosize_of_object_bound prev g;
           wosize_of_object_spec obj g;
           AllocLemmas.write_body_preserves_wfh_part1 g prev (prev <: hp_addr) new_fp;
           AllocLemmas.write_body_preserves_objects_local
             zero_addr g prev (prev <: hp_addr) new_fp;
           // prev's block is disjoint from obj's, so obj's header survives
           if U64.v prev < U64.v obj then begin
             objects_separated zero_addr g prev obj;
             assert (U64.v prev + 8 <= U64.v hd)
           end else begin
             objects_separated zero_addr g obj prev;
             assert (U64.v hd + 8 <= U64.v prev)
           end;
           read_write_different g (prev <: hp_addr) hd new_fp
         end else ());
        assert (well_formed_heap_part1 base);
        assert (objects zero_addr base == objects zero_addr g);
        assert (read_word base hd == hdr);
        assert (U64.v (getWosize (read_word base hd)) == block_wz);
        assert (Seq.mem (obj <: U64.t) (objects zero_addr base));
        AllocLemmas.alloc_from_block_objects_facts_part1 base obj wz next_fp;
        if leftover = 0 then
          // the allocation IS the original block, already an object
          assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8))) == U64.v obj)
        else begin
          AllocLemmas.alloc_from_block_alloc_in_objects_part1 base obj wz next_fp;
          // bridge the lemma's f_address form to alloc_search's obj_out:
          //   f_address(ahn) = hd + leftover*8 + 8 = cur_fp + leftover*8
          let ah : hp_addr = U64.uint_to_t ahn in
          f_address_spec ah;
          assert (U64.v (f_address ah) == U64.v hd + leftover * 8 + 8);
          assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8)))
                  == U64.v cur_fp + leftover * 8);
          assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8)))
                  == U64.v (f_address ah))
        end
      end
    end
    else begin
      // fl_valid_elim gives next_fp <> cur_fp, which is the strictness
      // objects_separated needs on the next step
      AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
      alloc_search_obj_in_objects_post_part1 g head_fp cur_fp next_fp wz (fuel - 1)
    end
  end
#pop-options

/// After alloc, obj_out is in objects of the output heap (part1 only)
let alloc_spec_obj_in_objects_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words)
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     Seq.mem (r.obj_out <: obj_addr) (objects zero_addr r.heap_out))))
  =
  let wz = if requested_wz = 0 then 1 else requested_wz in
  let fuel = heap_words in
  // obj_out is an object of the OUTPUT heap directly: at leftover = 0 it is the
  // original block, at leftover >= 1 the newly split-off allocated piece.
  alloc_search_obj_in_objects_post_part1 g fp 0UL fp wz fuel

/// The allocated block's *body* lies within the heap, not just its header.
///
/// `alloc_spec_obj_valid` bounds only the object address.  Forwarding an
/// interior pointer needs the stronger statement: the promoted copy of an
/// enclosing closure has to have room for every byte of the closure, because
/// the interior address is `obj_out + offset` for some offset inside the body.
/// Membership in `objects zero_addr r.heap_out` plus part 1 of the target
/// heap's well-formedness says exactly that.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let alloc_spec_obj_body_within_heap (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words)
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     (let obj_out : obj_addr = r.obj_out in
                      U64.v obj_out +
                        U64.v (wosize_of_object obj_out r.heap_out) * 8 <= heap_size))))
  =
  alloc_spec_obj_in_objects_part1 g fp requested_wz;
  AllocLemmas.alloc_spec_preserves_wfh_part1 g fp requested_wz;
  let r = alloc_spec g fp requested_wz in
  if r.obj_out <> 0UL then begin
    let obj_out : obj_addr = r.obj_out in
    hd_address_spec obj_out;
    assert (U64.v (hd_address obj_out) + 8 +
              (U64.v (wosize_of_object obj_out r.heap_out) * 8) <= Seq.length r.heap_out)
  end
#pop-options

/// wosize of obj_out is within [wz, wz+1] (no wfh — only fl_valid needed).
/// Both bounds ride the same induction; the wrappers below project each one.
#push-options "--z3rlimit 12 --fuel 4 --ifuel 1"
private let rec alloc_search_obj_wosize_part1
  (g: heap) (head_fp: U64.t) (prev_fp: U64.t)
  (cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires AllocLemmas.fl_valid g cur_fp fuel /\
              (prev_fp <> 0UL ==>
                (prev_fp <> cur_fp /\
                 U64.v prev_fp >= U64.v mword /\
                 U64.v prev_fp < heap_size /\
                 U64.v prev_fp % U64.v mword = 0 /\
                 Seq.mem prev_fp (objects zero_addr g) /\
                 U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword == 0 /\
               // EXACT, not a range: this is the point of right-justification
               (let obj_out : obj_addr = r.obj_out in
                U64.v (wosize_of_object obj_out r.heap_out) == wz))))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then begin
      let leftover = block_wz - wz in
      let ahn = U64.v hd + leftover * 8 in
      if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
      else begin
        aligned_plus_mul8 (U64.v hd) leftover;
        // Reordered: prev's link is rewritten on `g` first, and the block
        // writes run on the result, so the header lemma applies to `base`.
        let new_fp = alloc_replacement_fp g obj wz next_fp in
        alloc_replacement_fp_eq g obj wz next_fp;
        let base =
          if prev_fp = 0UL then g
          else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                  U64.v prev_fp % U64.v mword = 0
          then write_word g (prev_fp <: hp_addr) new_fp
          else g
        in
        hd_address_spec obj;
        hd_address_bounds obj;
        wosize_of_object_spec obj g;
        (if prev_fp = 0UL then ()
         else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
           let prev_obj : obj_addr = prev_fp in
           hd_address_spec prev_obj;
           hd_address_bounds prev_obj;
           wosize_of_object_spec prev_obj g;
           // prev's block is disjoint from obj's, so obj's header survives
           if U64.v prev_fp < U64.v obj then begin
             objects_separated zero_addr g prev_obj obj;
             assert (U64.v prev_fp + 8 <= U64.v hd)
           end else begin
             objects_separated zero_addr g obj prev_obj;
             assert (U64.v hd + 8 <= U64.v prev_fp)
           end;
           read_write_different g (prev_obj <: hp_addr) hd new_fp
         end else ());
        assert (read_word base hd == hdr);
        assert (U64.v (getWosize (read_word base hd)) == block_wz);
        alloc_from_block_wosize_lemma base obj wz next_fp;
        let g2 = fst (alloc_from_block base obj wz next_fp) in
        let ah : hp_addr = mk_hp_addr ahn in
        f_address_spec ah;
        let alloc_obj : obj_addr = f_address ah in
        // obj_out is the right-justified object, whose header is at ah
        hd_address_spec alloc_obj;
        wosize_of_object_spec alloc_obj g2;
        assert (U64.v (hd_address alloc_obj) == ahn);
        // bridge to alloc_search's obj_out = cur_fp + leftover * 8; the
        // guard above bounds ahn + 8, which keeps the U64.add below pow2 64
        assert (U64.v cur_fp == U64.v hd + 8);
        assert (leftover * 8 < heap_size);
        assert (U64.v (U64.uint_to_t (leftover * 8)) == leftover * 8);
        assert (U64.v cur_fp + leftover * 8 == ahn + 8);
        assert (U64.v cur_fp + leftover * 8 < heap_size);
        assert (U64.v (f_address ah) == U64.v hd + leftover * 8 + 8);
        assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8)))
                == U64.v (f_address ah))
      end
    end
    else begin
      if U64.v hd + 16 <= heap_size then begin
        AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
        AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
        alloc_search_obj_wosize_part1 g head_fp cur_fp next_fp wz (fuel - 1)
      end else ()
    end
  end
#pop-options

let alloc_spec_obj_wosize_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires AllocLemmas.fl_valid g fp heap_words)
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     U64.v (wosize_of_object (r.obj_out <: obj_addr) r.heap_out) >= 
                       (if requested_wz = 0 then 1 else requested_wz))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_wosize_part1 g fp 0UL fp wz heap_words

/// Top-level: after alloc_spec, wosize <= requested_wz.
///
/// This said `<= wz + 1` until right-justification. Together with the `>= wz`
/// lemma above that admitted `wosize in [wz, wz+1]`, and the `+1` is exactly
/// the latitude issue #19 lived in: a free block one word too long handed over
/// whole, with the block's size left in the header. The allocator has been
/// exact since right-justification landed -- `alloc_search_obj_wosize_part1`
/// proves `== wz` -- so the range was a stale projection, not a real bound.
///
/// Phrased as an inequality rather than an equation on purpose: an equation
/// unifies `wz` with a machine integer and would force a `pow2 54` bound onto
/// every caller. The pair of inequalities says the same thing and costs the
/// call sites nothing.
let alloc_spec_obj_wosize_upper_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires AllocLemmas.fl_valid g fp heap_words)
          (ensures (let wz = if requested_wz = 0 then 1 else requested_wz in
                    let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     (let obj_out : obj_addr = r.obj_out in
                      U64.v (wosize_of_object obj_out r.heap_out) <= wz))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_wosize_part1 g fp 0UL fp wz heap_words

/// Top-level, EXACT: the allocated object declares exactly what was asked for.
///
/// The two lemmas above are weaker projections of the same induction, kept
/// because their 29 call sites only need one side. Neither states the property
/// that matters: together they permit `wosize in [wz, wz+1]`, and that `+1` is
/// precisely the latitude issue #19 exploited -- a free block one word too long
/// handed over whole, with the block's size left in the header.
///
/// `alloc_search_obj_wosize_part1` has proved the exact bound since
/// right-justification landed; this exposes it at the `alloc_spec` level, so a
/// caller can rely on the size rather than on a range that still admits the
/// bug.
/// `requested_wz < pow2 54` is the standing wosize bound, needed here and not
/// in the two weaker wrappers only because an equation unifies `wz` with a
/// machine integer where an inequality does not.
let alloc_spec_obj_wosize_exact_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires AllocLemmas.fl_valid g fp heap_words /\ requested_wz < pow2 54)
          (ensures (let wz = if requested_wz = 0 then 1 else requested_wz in
                    let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     (let obj_out : obj_addr = r.obj_out in
                      U64.v (wosize_of_object obj_out r.heap_out) == wz))))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_wosize_part1 g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// alloc_spec returns an object that is IN the pre-alloc chain.
/// Equivalently: if chain_avoids g fp excl fuel = true, then excl ≠ obj_out.
/// ---------------------------------------------------------------------------
///
/// Proof strategy: induction on alloc_search. The invariant is
/// chain_avoids g cur_fp excl fuel = true. At the found step,
/// chain_avoids_head_ne gives cur_fp ≠ excl = obj_out ≠ excl.
/// At the advance step, chain_avoids_tail gives the invariant for next_fp.

#push-options "--z3rlimit 12 --fuel 4 --ifuel 1"
let rec alloc_search_obj_ne_excl
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat) (excl: U64.t)
  : Lemma
    (requires well_formed_heap_part1 g /\
              AllocLemmas.fl_valid g cur_fp fuel /\
              AllocLemmas.chain_avoids g cur_fp excl fuel = true /\
              wz >= 1 /\
              // `excl` is an existing object.  Needed now that the allocation
              // is right-justified: obj_out sits strictly inside the free
              // block rather than at its head, so distinctness comes from
              // object separation, not from chain_avoids_head_ne alone.
              (U64.v excl >= U64.v mword /\
               U64.v excl < heap_size /\
               U64.v excl % U64.v mword = 0 /\
               Seq.mem (excl <: obj_addr) (objects zero_addr g)))
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==> r.obj_out <> excl))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    // cur_fp is a valid obj_addr with fuel > 0
    AllocLemmas.fl_valid_elim g cur_fp fuel;
    // fl_valid_elim gives: Seq.mem cur_fp (objects zero_addr g), wosize >= 1
    // From well_formed_heap_part1 + wosize >= 1: hd + 16 <= heap_size
    let obj : obj_addr = cur_fp in
    hd_address_spec obj;
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    // chain_avoids_head_ne: cur_fp ≠ excl
    AllocLemmas.chain_avoids_head_ne g cur_fp excl fuel;
    AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
    if block_wz >= wz then begin
      // obj_out is cur_fp + leftover * 8, inside the block.  excl is an
      // object: below cur_fp it is below obj_out too; above cur_fp,
      // separation puts it past the whole block; equal is excluded by
      // chain_avoids_head_ne.
      let excl_obj : obj_addr = excl in
      wosize_of_object_spec obj g;
      if U64.v excl < U64.v obj then
        objects_separated zero_addr g excl_obj obj
      else if U64.v excl > U64.v obj then begin
        objects_separated zero_addr g obj excl_obj;
        assert (U64.v excl > U64.v obj + block_wz * 8)
      end else ()
    end
    else begin
      // Advance: need chain_avoids g next_fp excl (fuel-1)
      if U64.v hd + 16 <= heap_size then begin
        AllocLemmas.chain_avoids_tail g cur_fp excl fuel;
        alloc_search_obj_ne_excl g head_fp cur_fp next_fp wz (fuel - 1) excl
      end
      else ()
    end
  end
#pop-options

/// Top-level: if chain_avoids g fp excl fuel = true, then alloc_spec obj_out ≠ excl
let alloc_spec_obj_ne_excl (g: heap) (fp: U64.t) (requested_wz: nat) (excl: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.chain_avoids g fp excl heap_words = true /\
                    // see alloc_search_obj_ne_excl: with the allocation
                    // right-justified, distinctness rests on object separation
                    (U64.v excl >= U64.v mword /\
                     U64.v excl < heap_size /\
                     U64.v excl % U64.v mword = 0 /\
                     Seq.mem (excl <: obj_addr) (objects zero_addr g)))
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==> r.obj_out <> excl))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_ne_excl g fp 0UL fp wz heap_words excl

/// ---------------------------------------------------------------------------
/// (removed) Pre-alloc wosize of obj_out
///
/// `alloc_search_obj_wosize_pre_part1` and its wrapper asserted a wosize for
/// `obj_out` in the INPUT heap.  That only made sense while obj_out was the
/// free block's own address; with the allocation right-justified it is not an
/// object of `g` at all, so the statement is meaningless rather than merely
/// unproven.  Its one consumer (GC.Gen.PromoteUpdate.BlueProm) now works in
/// the output heap instead.
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// OOM lemma: when alloc_spec fails, heap and fp are unchanged
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 12 --fuel 4 --ifuel 1"
private let rec alloc_search_oom_unchanged
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out == 0UL ==>
              (r.heap_out == g /\ r.fp_out == head_fp)))
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
  else if U64.v cur_fp >= heap_size then ()
  else if U64.v cur_fp % U64.v mword <> 0 then ()
  else begin
    let obj : obj_addr = cur_fp in
    let hd = hd_address obj in
    let hdr = read_word g hd in
    let block_wz = U64.v (getWosize hdr) in
    let next_fp =
      if U64.v hd + 16 <= heap_size then read_word g obj
      else 0UL
    in
    if block_wz >= wz then begin
      // Either the geometry guard fires -- and then nothing was written, so
      // heap_out is g -- or an object was allocated, and obj_valid gives
      // obj_out >= mword > 0, making the hypothesis vacuous.
      let leftover = block_wz - wz in
      let ahn = U64.v hd + leftover * 8 in
      if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
      else begin
        aligned_plus_mul8 (U64.v hd) leftover;
        hd_address_spec obj;
        hd_address_bounds obj;
        assert (leftover * 8 < heap_size);
        assert (U64.v (U64.uint_to_t (leftover * 8)) == leftover * 8);
        assert (U64.v cur_fp + leftover * 8 == ahn + 8);
        assert (U64.v cur_fp + leftover * 8 < heap_size);
        // the allocated address is at least cur_fp, hence non-zero
        assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8)))
                >= U64.v cur_fp)
      end
    end
    else
      alloc_search_oom_unchanged g head_fp cur_fp next_fp wz (fuel - 1)
  end
#pop-options

/// Top-level: when alloc_spec fails (obj_out = 0UL), heap and fp are unchanged
let alloc_spec_oom_unchanged (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out == 0UL ==>
                    (r.heap_out == g /\ r.fp_out == fp)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_oom_unchanged g fp 0UL fp wz heap_words

/// ---------------------------------------------------------------------------
/// Allocator properties for blue_fields_closed proofs
/// ---------------------------------------------------------------------------

/// After alloc_from_block, the ALLOCATED object has colour White.
///
/// Stated about the allocated header at hd + leftover * 8, not about `obj`:
/// with the object right-justified, the block at `obj` is the remainder, which
/// is blue.  The old form -- `color_of_object obj g' == White` -- is therefore
/// false for any split.
#restart-solver
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let alloc_from_block_obj_not_blue (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hd = hd_address obj in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz >= wz /\ wz >= 1 /\
                     U64.v hd + (bwz - wz) * 8 + 8 < heap_size))
          (ensures (let hd = hd_address obj in
                    let bwz = U64.v (getWosize (read_word g hd)) in
                    let ahn = U64.v hd + (bwz - wz) * 8 in
                    let (g', _) = alloc_from_block g obj wz next_fp in
                    ahn % U64.v mword == 0 /\ ahn + 8 < heap_size /\
                    (let ao : obj_addr = f_address (mk_hp_addr ahn) in
                     color_of_object ao g' == White /\ is_blue ao g' = false)))
  = let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    let leftover = bwz - wz in
    wfh_part1_obj_bound g obj;
    aligned_plus_mul8 (U64.v hd) leftover;
    let ahn = U64.v hd + leftover * 8 in
    let ah : hp_addr = mk_hp_addr ahn in
    f_address_spec ah;
    let ao : obj_addr = f_address ah in
    hd_address_spec ao;
    assert (U64.v (hd_address ao) == ahn);
    let (g', _) = alloc_from_block g obj wz next_fp in
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    AllocLemmas.make_header_getColor (U64.uint_to_t wz) white_bits 0UL;
    getColor_raw alloc_hdr;
    if leftover = 0 then begin
      // ah = hd and ao = obj: a single write, and it is the allocated header
      GC.Spec.Allocator.alloc_from_block_exact g obj wz next_fp;
      read_write_same g hd alloc_hdr;
      assert (g' == write_word g hd alloc_hdr);
      assert (read_word g' (hd_address ao) == alloc_hdr);
      color_of_object_spec ao g';
      is_blue_iff ao g'
    end else begin
      GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
      let rem_hdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
      let g1 = write_word g hd rem_hdr in
      read_write_same g1 ah alloc_hdr;
      assert (g' == write_word g1 ah alloc_hdr);
      assert (read_word g' (hd_address ao) == alloc_hdr);
      color_of_object_spec ao g';
      is_blue_iff ao g'
    end
#pop-options

/// Writing to an address different from hd_address obj preserves color_of_object.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let write_preserves_color (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr + 8 <= U64.v (hd_address obj) \/
                    U64.v (hd_address obj) + 8 <= U64.v addr)
          (ensures (let g' = write_word g addr v in
                    color_of_object obj g' == color_of_object obj g))
  = hd_address_spec obj;
    read_write_different g addr (hd_address obj) v;
    let g' = write_word g addr v in
    color_of_object_spec obj g;
    color_of_object_spec obj g'
#pop-options

/// Writing the prev_fp link (which is at the prev_fp address, i.e. field[0])
/// does not affect obj's header → obj remains not-blue.
/// Requires prev_fp != hd_address obj (guaranteed by objects_separated at call sites).
/// alloc_from_block preserves reads at addresses outside the modified range.
/// The modified range is: hd_address(obj) (header) and possibly a remainder header/field.
/// If addr is outside obj's block entirely, read_word is unchanged.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let alloc_from_block_read_frame (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
                                (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    U64.v (getWosize (read_word g (hd_address obj))) >= wz /\
                    wz >= 1 /\
                    (U64.v addr + 8 <= U64.v (hd_address obj) \/
                     U64.v addr >= U64.v obj + U64.v (getWosize (read_word g (hd_address obj))) * 8))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    read_word g' addr == read_word g addr))
  = hd_address_spec obj;
    hd_address_bounds obj;
    wfh_part1_obj_bound g obj;
    // `addr >= obj + bwz * 8` is `addr >= hd + (bwz + 1) * 8`, which is exactly
    // the framing lemma's disjointness condition -- and that lemma covers every
    // arm at once, so the old four-way case analysis over the two out-of-bounds
    // variants and the split is no longer needed.
    alloc_from_block_read_outside g obj wz next_fp addr
#pop-options

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
let alloc_from_block_exact_objects_eq_part1 (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let bwz = U64.v (getWosize (read_word g (hd_address obj))) in
                     bwz == wz) /\
                    wz >= 1)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    objects zero_addr g' == objects zero_addr g))
  = let hd = hd_address obj in
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_bounds obj;
    SA.alloc_from_block_exact g obj wz next_fp;
    let ahdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    let g1 = write_word g hd ahdr in
    assert (alloc_from_block g obj wz next_fp == (g1, next_fp));
    getWosize_bound hdr;
    AllocLemmas.make_header_getWosize (U64.uint_to_t wz) white_bits 0UL;
    assert (getWosize ahdr == getWosize hdr);
    write_header_same_wosize_preserves_objects_aux zero_addr g hd ahdr
#pop-options

/// Top-level: alloc_spec result obj is not blue (the allocator writes White color).
/// Proof: alloc_spec calls alloc_search which calls alloc_from_block at the found block.
/// alloc_from_block_obj_not_blue proves the block-level result.
#push-options "--z3rlimit 12 --fuel 4 --ifuel 1"
let rec alloc_search_obj_not_blue
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
             AllocLemmas.fl_valid g cur_fp fuel /\
             AllocLemmas.fl_chain_terminates g cur_fp fuel /\
             wz >= 1)
    (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
              r.obj_out <> 0UL ==>
              (U64.v r.obj_out >= U64.v mword /\
               U64.v r.obj_out < heap_size /\
               U64.v r.obj_out % U64.v mword = 0)))
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
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      if bwz >= wz then ()
      else begin
        if U64.v hd + 16 <= heap_size then begin
          AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
          alloc_search_obj_not_blue g head_fp cur_fp next_fp wz (fuel - 1)
        end else ()
      end
    end
#pop-options

/// alloc_search result has color White (the allocator writes White)
#push-options "--z3rlimit 12 --fuel 4 --ifuel 1"
let rec alloc_search_obj_white
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires well_formed_heap_part1 g /\
             AllocLemmas.fl_valid g cur_fp fuel /\
             AllocLemmas.fl_chain_terminates g cur_fp fuel /\
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
              (let out = r.obj_out in
               U64.v out >= U64.v mword /\
               U64.v out < heap_size /\
               U64.v out % U64.v mword = 0 /\
               color_of_object (out <: obj_addr) r.heap_out == White)))
    (decreases fuel)
  = alloc_search_obj_not_blue g head_fp prev_fp cur_fp wz fuel;
    if fuel = 0 then ()
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
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      AllocLemmas.fl_valid_elim g cur_fp fuel;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      if bwz >= wz then begin
        let leftover = bwz - wz in
        let ahn = U64.v hd + leftover * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
        else begin
          aligned_plus_mul8 (U64.v hd) leftover;
          // Reordered: prev's link is rewritten on `g` first, so the White
          // header lands in `alloc_from_block base ...`, not in `... g ...`.
          let new_fp = alloc_replacement_fp g obj wz next_fp in
          alloc_replacement_fp_eq g obj wz next_fp;
          let base =
            if prev_fp = 0UL then g
            else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                    U64.v prev_fp % U64.v mword = 0
            then write_word g (prev_fp <: hp_addr) new_fp
            else g
          in
          AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
          wosize_of_object_spec obj g;
          (if prev_fp = 0UL then ()
           else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
             let prev_obj : obj_addr = prev_fp in
             hd_address_spec prev_obj;
             hd_address_bounds prev_obj;
             wosize_of_object_spec prev_obj g;
             AllocLemmas.write_body_preserves_wfh_part1
               g prev_obj (prev_obj <: hp_addr) new_fp;
             AllocLemmas.write_body_preserves_objects_local
               zero_addr g prev_obj (prev_obj <: hp_addr) new_fp;
             // prev's block is disjoint from obj's, so obj's header survives
             if U64.v prev_fp < U64.v obj then begin
               objects_separated zero_addr g prev_obj obj;
               assert (U64.v prev_fp + 8 <= U64.v hd)
             end else begin
               objects_separated zero_addr g obj prev_obj;
               assert (U64.v hd + 8 <= U64.v prev_fp)
             end;
             read_write_different g (prev_obj <: hp_addr) hd new_fp
           end else ());
          assert (read_word base hd == hdr);
          assert (U64.v (getWosize (read_word base hd)) == bwz);
          assert (Seq.mem (obj <: U64.t) (objects zero_addr base));
          // the White header is written at the right-justified address
          alloc_from_block_obj_not_blue base obj wz next_fp;
          let ah : hp_addr = mk_hp_addr ahn in
          f_address_spec ah;
          let ao : obj_addr = f_address ah in
          hd_address_spec ao;
          // bridge to obj_out = cur_fp + leftover * 8
          assert (leftover * 8 < heap_size);
          assert (U64.v (U64.uint_to_t (leftover * 8)) == leftover * 8);
          assert (U64.v cur_fp + leftover * 8 == ahn + 8);
          assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8)))
                  == U64.v (f_address ah))
        end
      end else begin
        if U64.v hd + 16 <= heap_size then begin
          AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
          AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
          alloc_search_obj_white g head_fp cur_fp next_fp wz (fuel - 1)
        end else ()
      end
    end
#pop-options

#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let alloc_spec_obj_not_blue_part1 (g: heap) (fp: U64.t) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words)
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword = 0 /\
                     color_of_object (r.obj_out <: obj_addr) r.heap_out == White)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_obj_white g fp 0UL fp wz heap_words
#pop-options

/// ---------------------------------------------------------------------------
/// A blue object other than the allocated block stays blue
/// ---------------------------------------------------------------------------
///
/// Only two headers are written: the remainder's at `hd`, which turns BLUE,
/// and the allocated block's, which turns white -- and that one is `obj_out`.
/// So every other object keeps its colour outright, and the block the
/// allocation came out of keeps its colour by accident of both being blue.
///
/// This is what lets a caller rule out "gray or black afterwards" for a
/// free-list cell, which under right-justification it can no longer get from
/// `alloc_spec_read_header_other_part1` -- that one now wants the object off
/// the chain, which is exactly the fact being established.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let alloc_from_block_preserves_blue
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    Seq.mem (h <: U64.t) (objects zero_addr g) /\
                    is_blue h g = true /\
                    (let hd = hd_address obj in
                     let bwz = U64.v (getWosize (read_word g hd)) in
                     bwz >= wz /\ wz >= 1 /\
                     U64.v hd + (bwz - wz) * 8 + 8 < heap_size /\
                     U64.v h <> U64.v hd + (bwz - wz) * 8 + 8))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    is_blue h g' = true))
  = let hd = hd_address obj in
    hd_address_spec obj;
    hd_address_bounds obj;
    hd_address_spec h;
    hd_address_bounds h;
    let hdr = read_word g hd in
    let bwz = U64.v (getWosize hdr) in
    let leftover = bwz - wz in
    wfh_part1_obj_bound g obj;
    aligned_plus_mul8 (U64.v hd) leftover;
    let ahn = U64.v hd + leftover * 8 in
    let ah : hp_addr = mk_hp_addr ahn in
    let (g', _) = alloc_from_block g obj wz next_fp in
    let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
    // `hd_address h = ah` would make h the allocated block, which is excluded
    f_address_spec ah;
    assert (U64.v (hd_address h) == U64.v h - 8);
    assert (U64.v (hd_address h) <> ahn);
    if leftover = 0 then begin
      // single write, at hd; h = obj keeps a white header, so h <> obj
      GC.Spec.Allocator.alloc_from_block_exact g obj wz next_fp;
      assert (ahn == U64.v hd);
      assert (U64.v (hd_address h) <> U64.v hd);
      write_preserves_color g h hd alloc_hdr;
      is_blue_iff h g;
      is_blue_iff h g'
    end else begin
      GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
      let rem_hdr = make_header (U64.uint_to_t (leftover - 1)) blue_bits 0UL in
      let g1 = write_word g hd rem_hdr in
      AllocLemmas.make_header_getColor (U64.uint_to_t (leftover - 1)) blue_bits 0UL;
      getColor_raw rem_hdr;
      // the allocated header never lands on h's header
      write_preserves_color g1 h ah alloc_hdr;
      if U64.v (hd_address h) = U64.v hd then begin
        // h IS the block we allocated from; its header is now the blue
        // remainder, so it is still blue
        read_write_same g hd rem_hdr;
        color_of_object_spec h g1;
        is_blue_iff h g1;
        is_blue_iff h g'
      end else begin
        write_preserves_color g h hd rem_hdr;
        is_blue_iff h g;
        is_blue_iff h g1;
        is_blue_iff h g'
      end
    end
#pop-options


/// The same fact, lifted over the whole search.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
private let rec alloc_search_preserves_blue
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g cur_fp fuel /\
                    AllocLemmas.fl_chain_terminates g cur_fp fuel /\
                    wz >= 1 /\
                    Seq.mem (h <: U64.t) (objects zero_addr g) /\
                    is_blue h g = true /\
                    (prev_fp <> 0UL ==>
                      (prev_fp <> cur_fp /\
                       U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL /\ (h <: U64.t) <> r.obj_out ==>
                    is_blue h r.heap_out = true))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur_fp < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur_fp >= heap_size then ()
    else if U64.v cur_fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur_fp in
      let hd = hd_address obj in
      let hdr = read_word g hd in
      let bwz = U64.v (getWosize hdr) in
      hd_address_spec obj;
      hd_address_bounds obj;
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
      wosize_of_object_spec obj g;
      let next_fp = if U64.v hd + 16 <= heap_size then read_word g obj else 0UL in
      if bwz >= wz then begin
        let leftover = bwz - wz in
        let ahn = U64.v hd + leftover * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
        else begin
          aligned_plus_mul8 (U64.v hd) leftover;
          assert (U64.v (U64.add cur_fp (U64.uint_to_t (leftover * 8))) == ahn + 8);
          if (h <: U64.t) = U64.add cur_fp (U64.uint_to_t (leftover * 8)) then
            // h IS the allocated block; the conclusion is guarded on this
            ()
          else begin
          let new_fp = alloc_replacement_fp g obj wz next_fp in
          alloc_replacement_fp_eq g obj wz next_fp;
          if prev_fp = 0UL || U64.v prev_fp = U64.v hd ||
             not (U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                  U64.v prev_fp % U64.v mword = 0)
          then
            alloc_from_block_preserves_blue g obj wz next_fp h
          else begin
            // the link write comes first; it touches a field, not a header
            let prev_obj : obj_addr = prev_fp in
            let gw = write_word g (prev_obj <: hp_addr) new_fp in
            hd_address_spec prev_obj;
            hd_address_bounds prev_obj;
            hd_address_spec h;
            hd_address_bounds h;
            wosize_of_object_spec prev_obj g;
            wosize_of_object_bound prev_obj g;
            AllocLemmas.write_body_preserves_wfh_part1
              g prev_obj (prev_obj <: hp_addr) new_fp;
            AllocLemmas.write_body_preserves_objects_local
              zero_addr g prev_obj (prev_obj <: hp_addr) new_fp;
            // prev's link is never h's header: it is h's own first field if
            // h = prev, and otherwise object separation keeps them apart
            (if (h <: U64.t) = prev_fp then ()
             else begin
               wosize_of_object_spec h g;
               if U64.v h < U64.v prev_fp then
                 objects_separated zero_addr g h prev_obj
               else
                 objects_separated zero_addr g prev_obj h
             end);
            write_preserves_color g h (prev_obj <: hp_addr) new_fp;
            is_blue_iff h g;
            is_blue_iff h gw;
            // and it leaves obj's block exactly as it was
            read_write_different g (prev_obj <: hp_addr) hd new_fp;
            alloc_from_block_preserves_blue gw obj wz next_fp h
          end
          end
        end
      end
      else begin
        if U64.v hd + 16 <= heap_size then begin
          AllocLemmas.fl_valid_elim g cur_fp fuel;
          AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
          alloc_search_preserves_blue g head_fp cur_fp next_fp wz (fuel - 1) h
        end else ()
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let alloc_spec_preserves_blue_part1 (g: heap) (fp: U64.t) (requested_wz: nat) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    requested_wz >= 1 /\
                    Seq.mem (h <: U64.t) (objects zero_addr g) /\
                    is_blue h g = true)
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL /\ (h <: U64.t) <> r.obj_out ==>
                    is_blue h r.heap_out = true))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_preserves_blue g fp 0UL fp wz heap_words h
#pop-options

/// Helper: alloc_from_block preserves read at hd_address of a different object.
/// Proof: all writes (hd, rem_hd, rem_field) are within obj's block, which is
/// separated from excl's header by objects_separated.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
private let alloc_from_block_read_header_other
  (g: heap) (obj: obj_addr) (wz: nat) (next_fp: U64.t) (excl: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem obj (objects zero_addr g) /\
                    Seq.mem excl (objects zero_addr g) /\
                    (obj <: U64.t) <> (excl <: U64.t) /\
                    (let hdr = read_word g (hd_address obj) in
                     U64.v (getWosize hdr) >= wz /\ wz >= 1))
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    read_word g' (hd_address excl) == read_word g (hd_address excl)))
  = let hd_obj = hd_address obj in
    let hd_excl = hd_address excl in
    let hdr = read_word g hd_obj in
    let bwz = U64.v (getWosize hdr) in
    hd_address_spec obj;
    hd_address_spec excl;
    hd_address_bounds obj;
    hd_address_bounds excl;
    // Key: objects_separated gives non-overlap
    wosize_of_object_spec obj g;
    wosize_of_object_spec excl g;
    if U64.v excl < U64.v obj then begin
      objects_separated zero_addr g excl obj;
      // excl + wz(excl)*8 < obj, so hd_excl = excl - 8 < obj - 8 = hd_obj
      // and hd_excl + 8 = excl <= obj - wz(excl)*8 - 8 <= obj - 16 < hd_obj
      assert (U64.v hd_excl + 8 <= U64.v hd_obj)
    end else begin
      objects_separated zero_addr g obj excl;
      // obj + wz(obj)*8 < excl = bwz*8 < excl, so hd_excl = excl - 8 >= obj + bwz*8
      // and all writes are in [hd_obj, obj + (bwz+1)*8) which is ≤ hd_excl
      assert (U64.v hd_obj + 8 <= U64.v hd_excl)
    end;
    // Every write lands inside obj's block, and excl's header is outside it,
    // so the framing lemma settles all arms at once.
    assert (U64.v hd_excl + 8 <= U64.v hd_obj \/
            U64.v hd_excl >= U64.v hd_obj + (bwz + 1) * 8);
    alloc_from_block_read_outside g obj wz next_fp hd_excl
#pop-options

/// Inductive: alloc_search preserves the header of excl when excl ≠ obj_out.
#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"
private let rec alloc_search_read_header_other
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat) (excl: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g cur_fp fuel /\
                    AllocLemmas.fl_chain_terminates g cur_fp fuel /\
                    wz >= 1 /\
                    Seq.mem excl (objects zero_addr g) /\
                    (excl <: U64.t) <> (alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out /\
                    // excl must differ from every CELL, not just from obj_out.
                    // Under the old layout obj_out was cur_fp, so excl <> obj_out
                    // already gave that; right-justification separates the two,
                    // and if excl were the cell its header would be rewritten
                    // as the remainder's.
                    AllocLemmas.chain_avoids g cur_fp excl fuel = true /\
                    (prev_fp <> 0UL ==>
                      (U64.v prev_fp >= U64.v mword /\
                       U64.v prev_fp < heap_size /\
                       U64.v prev_fp % U64.v mword = 0 /\
                       Seq.mem prev_fp (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1)))
          (ensures (let r = alloc_search g head_fp prev_fp cur_fp wz fuel in
                    r.obj_out <> 0UL ==>
                    read_word r.heap_out (hd_address excl) ==
                    read_word g (hd_address excl)))
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
      AllocLemmas.fl_valid_gives_mem g cur_fp fuel;
      AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;
      let next_fp =
        if U64.v hd + 16 <= heap_size then read_word g obj
        else 0UL
      in
      if block_wz >= wz then begin
        // Found a block.  obj_out is no longer cur_fp, but this lemma only
        // reads excl's header, which alloc_from_block leaves alone either way.
        let leftover = block_wz - wz in
        let ahn = U64.v hd + leftover * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
        else begin
          AllocLemmas.chain_avoids_head_ne g cur_fp excl fuel;
          // Reordered: prev's link is rewritten on `g` first, and the block
          // writes run on the result, so the frame is taken in two steps.
          let new_fp = alloc_replacement_fp g obj wz next_fp in
          alloc_replacement_fp_eq g obj wz next_fp;
          let base =
            if prev_fp = 0UL then g
            else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                    U64.v prev_fp % U64.v mword = 0 && U64.v prev_fp <> U64.v hd
            then write_word g (prev_fp <: hp_addr) new_fp
            else g
          in
          hd_address_spec excl;
          wosize_of_object_spec obj g;
          (if prev_fp = 0UL then ()
           else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 && U64.v prev_fp <> U64.v hd then begin
             let prev_obj : obj_addr = prev_fp in
             hd_address_spec prev_obj;
             hd_address_bounds prev_obj;
             wosize_of_object_spec prev_obj g;
             wosize_of_object_bound prev_obj g;
             AllocLemmas.write_body_preserves_wfh_part1
               g prev_obj (prev_obj <: hp_addr) new_fp;
             AllocLemmas.write_body_preserves_objects_local
               zero_addr g prev_obj (prev_obj <: hp_addr) new_fp;
             // 1. the link write misses excl's header
             (if (prev_fp <: U64.t) = (excl <: U64.t) then
                assert (U64.v (hd_address excl) + 8 <= U64.v prev_fp)
              else begin
                wosize_of_object_spec excl g;
                if U64.v prev_fp < U64.v excl then begin
                  objects_separated zero_addr g prev_obj excl;
                  assert (U64.v prev_fp + 8 <= U64.v (hd_address excl))
                end else
                  assert (U64.v (hd_address excl) + 8 <= U64.v prev_fp)
              end);
             read_write_different g (prev_obj <: hp_addr) (hd_address excl) new_fp;
             // 2. and it leaves obj's own header alone -- `prev <> hd` here is
             //    a path condition, which is exactly why `alloc_search` guards
             //    on it rather than trusting the free list to be well formed
             read_write_different g (prev_obj <: hp_addr) hd new_fp
           end else ());
          assert (read_word base (hd_address excl) == read_word g (hd_address excl));
          assert (read_word base hd == hdr);
          assert (Seq.mem (excl <: U64.t) (objects zero_addr base));
          alloc_from_block_read_header_other base obj wz next_fp excl
        end
      end else begin
        // Block too small, continue
        if U64.v hd + 16 <= heap_size then begin
          AllocLemmas.fl_valid_elim g cur_fp fuel;
          AllocLemmas.fl_chain_terminates_elim g cur_fp fuel
        end else ();
        AllocLemmas.chain_avoids_tail g cur_fp excl fuel;
        alloc_search_read_header_other g head_fp cur_fp next_fp wz (fuel - 1) excl
      end
    end
#pop-options

/// Top-level: alloc_spec preserves the header of other objects.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let alloc_spec_read_header_other_part1 (g: heap) (fp: U64.t) (requested_wz: nat) (excl: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    Seq.mem excl (objects zero_addr g) /\
                    (excl <: U64.t) <> (alloc_spec g fp requested_wz).obj_out /\
                    // see alloc_search_read_header_other: excl must avoid every
                    // free-list cell, not merely obj_out
                    AllocLemmas.chain_avoids g fp excl heap_words = true)
          (ensures (let r = alloc_spec g fp requested_wz in
                    r.obj_out <> 0UL ==>
                    read_word r.heap_out (hd_address excl) ==
                    read_word g (hd_address excl)))
  = let wz = if requested_wz = 0 then 1 else requested_wz in
    alloc_search_read_header_other g fp 0UL fp wz heap_words excl
#pop-options
