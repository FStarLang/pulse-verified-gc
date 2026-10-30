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

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas
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

/// promote_object preserves allocator invariants
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let promote_object_preserves_alloc_invariants
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  = let fuel : nat = heap_words in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
    if alloc_res.obj_out = 0UL then begin
      // OOM: promote_object returns original heap unchanged
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize (promoted_tag minor obj)
    end else begin
      // Success path: tagged alloc, then copy_fields
      GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize (promoted_tag minor obj);
      let dst_obj : obj_addr = alloc_res.obj_out in
      // Alloc preserves invariants
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize (promoted_tag minor obj);
      GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize (promoted_tag minor obj);
      GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize (promoted_tag minor obj);
      // Copy fields preserves invariants
      chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
      copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
      copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wosize alloc_res.fp_out fuel;
      copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wosize alloc_res.fp_out fuel
    end
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let promote_object_new_addr_body_bound
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  = AllocProps.alloc_spec_obj_body_within_heap major fp wosize (promoted_tag minor obj);
    AllocProps.alloc_spec_obj_wosize_part1 major fp wosize (promoted_tag minor obj)
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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
private let dst_obj_bound_arith (d awz wz len: nat)
  : Lemma (requires d % U64.v mword == 0 /\ d + awz * 8 <= len /\ len == heap_size /\
                    awz >= wz /\ wz > 0)
          (ensures d % 8 == 0 /\ d + (wz - 1) * 8 + 8 <= heap_size)
  = ()

let dst_fields_valid_from_obj (g: heap) (addr: obj_addr) (wz: pos)
  = dst_obj_bound_arith (U64.v addr) (U64.v (wosize_of_object addr g)) wz (Seq.length g);
    dst_fields_valid_from_bounds addr wz
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
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
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
      (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
       alloc_res.obj_out == dst_addr /\
       alloc_res.obj_out <> 0UL))
    (ensures
      (let res = promote_object minor major obj fp wosize in
       read_word res.major_out addr == minor_read_field minor obj j))
  = let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
    assert (alloc_res.obj_out == dst_addr);
    promote_object_success minor major obj fp wosize;
    dst_fields_valid_from_bounds dst_addr wosize;
    copy_fields_all_correct minor alloc_res.heap_out obj dst_addr wosize
#pop-options

/// After promote_object, if allocation succeeds AND the destination
/// has valid bounds, all field data is preserved.
#push-options "--z3rlimit 10 --fuel 0"
let promote_preserves_fields
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
                =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
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
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
  if alloc_res.obj_out = 0UL then ()
  else begin
    // After alloc: old objects are preserved (part1 version)
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize (promoted_tag minor obj);
    // obj_out is a valid obj_addr
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize (promoted_tag minor obj);
    // obj_out is in objects of the output heap (part1 version)
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize (promoted_tag minor obj);
    // wosize of obj_out >= requested (no wfh needed)
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize (promoted_tag minor obj);
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
    assert (objects zero_addr (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects zero_addr alloc_res.heap_out)
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
/// The copy is allocated with the minor tag, so the allocator's part4 lemma
/// applies directly; copy_fields writes no headers.
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let promote_object_preserves_wfh_part4
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  = let fuel : nat = heap_words in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize (promoted_tag minor obj) in
    if alloc_res.obj_out = 0UL then begin
      promote_object_oom minor major obj fp wosize
    end else begin
      GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize (promoted_tag minor obj);
      let dst_obj : obj_addr = alloc_res.obj_out in
      minor_tag_bound minor obj;
      assert (promoted_tag minor obj <> GC.Spec.Object.infix_tag);
      AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_preserves_wfh_part4 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize (promoted_tag minor obj);
      GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize (promoted_tag minor obj);
      GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize (promoted_tag minor obj);
      AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize (promoted_tag minor obj);
      chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
      copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wosize;
      copy_fields_preserves_wfh_part4 minor alloc_res.heap_out obj dst_obj wosize
    end
#pop-options

/// promote_all_aux preserves well_formed_heap_part4 (no infix objects).
/// Top-level: promote_all_spec preserves well_formed_heap_part4
/// ---------------------------------------------------------------------------
/// fields_match_minor intro/elim lemmas (predicate is opaque_to_smt, recursive)
/// ---------------------------------------------------------------------------
