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

/// Promote a single object from minor to major heap.
/// Uses the major-heap allocator spec to get space, then copies fields.
let promote_object (minor: minor_state) (major: heap) (obj: U64.t)
                   (fp: U64.t) (wosize: nat{wosize > 0})
  : GTot promote_one_result =
  // Use the major allocator to get space
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  let new_major = alloc_res.heap_out in
  let new_fp = alloc_res.fp_out in
  let new_addr = alloc_res.obj_out in
  if new_addr = 0UL then
    // OOM in major heap
    { major_out = major; fp_out = fp; new_addr = 0UL }
  else
    // Copy field data from minor to major
    let final_major = copy_fields minor new_major obj new_addr 0 wosize in
    { major_out = final_major; fp_out = new_fp; new_addr = new_addr }

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
                    res.major_out == copy_fields minor alloc_res.heap_out obj alloc_res.obj_out 0 wosize /\
                    res.fp_out == alloc_res.fp_out /\
                    res.new_addr == alloc_res.obj_out)) = ()

/// ---------------------------------------------------------------------------
/// Promote all live objects
/// ---------------------------------------------------------------------------

/// Promote objects from live_set one by one, accumulating results
let rec promote_all_aux (minor: minor_state) (major: heap)
                        (fp: U64.t) (live_set: seq U64.t)
                        (fwd: forwarding_map) (idx: nat)
  : GTot promote_all_result (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then
    { major_final = major; fp_final = fp; fwd_map = fwd }
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      // Skip malformed objects
      promote_all_aux minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then
        // OOM — stop promotion (partial collection)
        { major_final = major; fp_final = fp; fwd_map = fwd }
      else
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux minor res.major_out res.fp_out live_set fwd' (idx + 1)

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

/// Update pointers in a single major-heap object.
/// Iterates fields [i, wosize) and rewrites minor-heap pointers via fwd.
let rec update_object_pointers (major: heap) (obj: U64.t) (wosize: nat)
                               (fwd: forwarding_map) (i: nat)
  : GTot heap (decreases (wosize - i)) =
  if i >= wosize then major
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then major
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then
          let major' = write_word major (U64.uint_to_t field_offset) new_val in
          update_object_pointers major' obj wosize fwd (i + 1)
        else
          update_object_pointers major obj wosize fwd (i + 1)
      else
        update_object_pointers major obj wosize fwd (i + 1)

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

/// Fold update_object_pointers over a sequence of objects, skipping blue (free) objects.
/// Blue objects are free-list cells whose first field is a free-list link, not a user pointer.
/// Rewriting their fields would corrupt the allocator's free chain.
let rec update_all_objects_aux (major: heap) (objs: seq obj_addr)
                               (fwd: forwarding_map) (idx: nat)
  : GTot heap (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then major
  else
    let obj = Seq.index objs idx in
    if is_blue obj major then
      update_all_objects_aux major objs fwd (idx + 1)
    else
      let wz = U64.v (wosize_of_object obj major) in
      let major' = update_object_pointers major obj wz fwd 0 in
      update_all_objects_aux major' objs fwd (idx + 1)

/// Update all pointers in the major heap:
/// Walk all objects and rewrite fields that point into the minor heap.
let update_major_pointers (major: heap) (fwd: forwarding_map) : GTot heap =
  update_all_objects_aux major (objects zero_addr major) fwd 0

/// ---------------------------------------------------------------------------
/// Root rewriting
/// ---------------------------------------------------------------------------

let rec rewrite_roots (roots: seq U64.t) (fwd: forwarding_map)
  : GTot (seq U64.t) (decreases (Seq.length roots)) =
  if Seq.length roots = 0 then Seq.empty
  else
    let r = Seq.index roots 0 in
    let new_r = rewrite_root r fwd in
    let rest = Seq.slice roots 1 (Seq.length roots) in
    Seq.cons new_r (rewrite_roots rest fwd)

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

let minor_collect_spec (minor: minor_state) (major: heap)
                       (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result =
  let live_set = live_set_of minor major roots in
  let prom_res = promote_all_spec minor major fp live_set in
  let updated_major = update_major_pointers prom_res.major_final prom_res.fwd_map in
  let new_roots = rewrite_roots roots prom_res.fwd_map in
  { mc_major = updated_major;
    mc_fp = prom_res.fp_final;
    mc_minor = minor_reset minor;
    mc_roots = new_roots;
    mc_fwd = prom_res.fwd_map }

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
    let rec aux (k: nat)
      : Lemma (requires k <= n)
              (ensures (forall (j:nat). j < k ==>
                (let result = copy_fields minor major src_obj dst_obj 0 n in
                 read_word result (U64.uint_to_t (U64.v dst_obj + j * 8)) ==
                 minor_read_field minor src_obj j)))
              (decreases k) =
      if k = 0 then ()
      else begin
        aux (k - 1);
        copy_fields_preserves minor major src_obj dst_obj 0 n (k - 1)
      end
    in
    aux n
  end
#pop-options

/// After promote_object, if allocation succeeds AND the destination
/// has valid bounds, all field data is preserved.
#push-options "--z3rlimit 20 --fuel 2"
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
       U64.v alloc_res.obj_out + (wosize - 1) * 8 + 8 <= heap_size then
      copy_fields_all_correct minor alloc_res.heap_out obj alloc_res.obj_out wosize
    else ()
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
#push-options "--z3rlimit 40 --fuel 1"
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
    copy_fields_preserves_objects minor alloc_res.heap_out obj dst_obj wosize;
    assert (objects zero_addr (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects zero_addr alloc_res.heap_out)
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
            objects zero_addr alloc_res.heap_out)
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
        assert (AllocLemmas.fl_valid res.major_out res.fp_out fuel);
        assert (AllocLemmas.fl_chain_terminates res.major_out res.fp_out fuel);
        // copy_fields preserves well_formed_heap_part1
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
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
#push-options "--z3rlimit 50 --fuel 1 --split_queries always"
let rec promote_all_aux_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    well_formed_heap_part4 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
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
        assert (well_formed_heap_part1 res.major_out);
        assert (well_formed_heap_part4 res.major_out);
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux_preserves_wfh_part4 minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
#pop-options

/// Top-level: promote_all_spec preserves well_formed_heap_part4
let promote_all_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part4 (promote_all_spec minor major fp live_set).major_final) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_aux_preserves_wfh_part4 minor major fp live_set empty_forwarding 0


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

/// Helper: derive dst_fields_valid from scalar upper bound + alignment
#push-options "--z3rlimit 20"
private let dst_fields_valid_from_bounds (addr: U64.t) (wz: pos)
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

#push-options "--z3rlimit 20"
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
