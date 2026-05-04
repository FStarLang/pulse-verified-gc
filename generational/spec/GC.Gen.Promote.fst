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

#push-options "--z3rlimit 200"
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
private let promote_object_preserves_objects_part1
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

#push-options "--z3rlimit 200 --fuel 1 --split_queries always"
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
#push-options "--z3rlimit 200 --fuel 1 --split_queries always"
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
#push-options "--z3rlimit 200 --fuel 1 --split_queries always"
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
/// Pointer update preserves objects
/// ---------------------------------------------------------------------------

/// update_object_pointers writes only within the body of `obj`, so
/// the objects walk is unchanged.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_objects
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures objects zero_addr (update_object_pointers major obj wosize fwd i) == objects zero_addr major)
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          assert (U64.v addr >= U64.v obj);
          assert (U64.v addr < U64.v obj + (U64.v (wosize_of_object obj major) * 8));
          write_body_preserves_objects major obj addr new_val;
          let major' = write_word major addr new_val in
          hd_address_spec obj;
          read_write_different major addr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_objects major' obj wosize fwd (i + 1)
        end else
          update_object_pointers_preserves_objects major obj wosize fwd (i + 1)
      else
        update_object_pointers_preserves_objects major obj wosize fwd (i + 1)
#pop-options

/// update_object_pointers does not modify headers of OTHER objects.
/// Needed for the fold: after updating obj_a, obj_b's wosize is unchanged.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_other_header
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (other: obj_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      Seq.mem other (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      other <> obj /\
      U64.v other > U64.v obj /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) (hd_address other) ==
      read_word major (hd_address other))
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          // addr = obj + i*8. other > obj, so hd_address other = other - 8 >= obj.
          // By objects_separated: other > obj + wosize*8 >= obj + i*8 = addr
          // So hd_address(other) = other - 8 >= obj + wosize*8 - 8 > addr  
          hd_address_spec other;
          objects_separated 0UL major obj other;
          assert (U64.v addr < U64.v (hd_address other));
          let major' = write_word major addr new_val in
          read_write_different major addr (hd_address other) new_val;
          // Recurse: major' has same objects (proven above)
          write_body_preserves_objects major obj addr new_val;
          hd_address_spec obj;
          read_write_different major addr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_other_header major' obj wosize fwd (i + 1) other
        end else
          update_object_pointers_preserves_other_header major obj wosize fwd (i + 1) other
      else
        update_object_pointers_preserves_other_header major obj wosize fwd (i + 1) other
#pop-options

/// update_object_pointers preserves the header of obj itself.
/// All writes are at obj + i*8 (i >= 0), header is at obj - 8 < obj.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_self_header
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) (hd_address obj) ==
      read_word major (hd_address obj))
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          // addr = obj + i*8 >= obj > obj - 8 = hd_address obj
          hd_address_spec obj;
          assert (U64.v addr > U64.v (hd_address obj));
          let major' = write_word major addr new_val in
          read_write_different major addr (hd_address obj) new_val;
          write_body_preserves_objects major obj addr new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_self_header major' obj wosize fwd (i + 1)
        end else
          update_object_pointers_preserves_self_header major obj wosize fwd (i + 1)
      else
        update_object_pointers_preserves_self_header major obj wosize fwd (i + 1)
#pop-options

/// update_object_pointers preserves reads at any address below obj.
/// All writes are at obj + j*8 >= obj, so any addr < obj is untouched.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_addr_below
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (addr: hp_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      U64.v addr < U64.v obj /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) addr ==
      read_word major addr)
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let waddr : hp_addr = U64.uint_to_t field_offset in
          // waddr = obj + i*8 >= obj > addr
          assert (U64.v waddr >= U64.v obj);
          assert (U64.v addr < U64.v waddr);
          let major' = write_word major waddr new_val in
          read_write_different major waddr addr new_val;
          write_body_preserves_objects major obj waddr new_val;
          hd_address_spec obj;
          read_write_different major waddr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_addr_below major' obj wosize fwd (i + 1) addr
        end else
          update_object_pointers_preserves_addr_below major obj wosize fwd (i + 1) addr
      else
        update_object_pointers_preserves_addr_below major obj wosize fwd (i + 1) addr
#pop-options

/// update_object_pointers preserves reads at addresses >= obj + wosize*8.
/// All writes are at obj + j*8 where j < wosize, so addr above the body is untouched.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_addr_above
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (addr: hp_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      U64.v addr >= U64.v obj + wosize * 8 /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) addr ==
      read_word major addr)
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let waddr : hp_addr = U64.uint_to_t field_offset in
          // waddr = obj + i*8, i < wosize, so waddr < obj + wosize*8 <= addr
          assert (U64.v waddr < U64.v addr);
          let major' = write_word major waddr new_val in
          read_write_different major waddr addr new_val;
          write_body_preserves_objects major obj waddr new_val;
          hd_address_spec obj;
          read_write_different major waddr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_addr_above major' obj wosize fwd (i + 1) addr
        end else
          update_object_pointers_preserves_addr_above major obj wosize fwd (i + 1) addr
      else
        update_object_pointers_preserves_addr_above major obj wosize fwd (i + 1) addr
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_preserves_objects
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major)
    (ensures objects zero_addr (update_all_objects_aux major objs fwd idx) == objs)
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if is_blue obj major then
      // Blue skip: heap unchanged, just recurse at idx+1
      update_all_objects_aux_preserves_objects major objs fwd (idx + 1)
    else begin
      let wz = U64.v (wosize_of_object obj major) in
      // From well_formed_heap_part1: field bounds for obj
      hd_address_spec obj;
      assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
      assert (forall (j:nat). j < wz ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0));
      // Step 1: update_object_pointers preserves objects list
      update_object_pointers_preserves_objects major obj wz fwd 0;
      let major' = update_object_pointers major obj wz fwd 0 in
      assert (objects zero_addr major' == objs);
      // Step 2: show well_formed_heap_part1 major' (all headers unchanged)
      let aux_wfh (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr major'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
      = hd_address_spec h;
        if h = obj then begin
          update_object_pointers_preserves_self_header major obj wz fwd 0;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else if U64.v h > U64.v obj then begin
          update_object_pointers_preserves_other_header major obj wz fwd 0 h;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else begin
          // h < obj: hd_address(h) = h - 8 < h < obj, so it's below obj
          update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
          wosize_of_object_spec h major;
          wosize_of_object_spec h major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      assert (well_formed_heap_part1 major');
      // Step 3: recurse
      update_all_objects_aux_preserves_objects major' objs fwd (idx + 1)
    end
  end
#pop-options

/// update_major_pointers preserves the objects walk.
let update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major) =
  update_all_objects_aux_preserves_objects major (objects zero_addr major) fwd 0

/// update_all_objects_aux preserves well_formed_heap_part1 (inductive).
/// Each step: update_object_pointers preserves all headers → preserves wfh_part1.
#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_preserves_wfh_part1
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major)
    (ensures well_formed_heap_part1 (update_all_objects_aux major objs fwd idx))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if is_blue obj major then
      // Blue skip: heap unchanged, just recurse
      update_all_objects_aux_preserves_wfh_part1 major objs fwd (idx + 1)
    else begin
      let wz = U64.v (wosize_of_object obj major) in
      hd_address_spec obj;
      assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
      // update_object_pointers preserves objects list
      update_object_pointers_preserves_objects major obj wz fwd 0;
      let major' = update_object_pointers major obj wz fwd 0 in
      assert (objects zero_addr major' == objs);
      // Prove wfh_part1 of major' (same structure as in preserves_objects)
      let aux_wfh (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr major'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
      = hd_address_spec h;
        if h = obj then begin
          update_object_pointers_preserves_self_header major obj wz fwd 0;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else if U64.v h > U64.v obj then begin
          update_object_pointers_preserves_other_header major obj wz fwd 0 h;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else begin
          update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
          wosize_of_object_spec h major;
          wosize_of_object_spec h major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      assert (well_formed_heap_part1 major');
      // Recurse
      update_all_objects_aux_preserves_wfh_part1 major' objs fwd (idx + 1)
    end
  end
#pop-options

/// update_major_pointers preserves well_formed_heap_part1.
let update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_major_pointers major fwd)) =
  update_all_objects_aux_preserves_wfh_part1 major (objects zero_addr major) fwd 0

/// ---------------------------------------------------------------------------
/// Exported step/done/unfold lemmas for Pulse implementation
/// ---------------------------------------------------------------------------

/// Step: just unfold the recursive definition
let update_all_objects_aux_step (major: heap) (objs: seq obj_addr)
                                (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length objs /\ well_formed_heap_part1 major /\
                    objs == objects zero_addr major /\
                    is_blue (Seq.index objs idx) major = false)
          (ensures (let obj = Seq.index objs idx in
                    let wz = U64.v (wosize_of_object obj major) in
                    update_all_objects_aux major objs fwd idx ==
                    update_all_objects_aux (update_object_pointers major obj wz fwd 0) objs fwd (idx + 1)))
  = ()

/// Blue skip step: when the object is blue (free), skip without modifying the heap
let update_all_objects_aux_skip_blue (major: heap) (objs: seq obj_addr)
                                     (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx < Seq.length objs /\
                    is_blue (Seq.index objs idx) major)
          (ensures update_all_objects_aux major objs fwd idx ==
                   update_all_objects_aux major objs fwd (idx + 1))
  = ()

/// Done: trivial base case
let update_all_objects_aux_done (major: heap) (objs: seq obj_addr)
                                (fwd: forwarding_map) (idx: nat)
  : Lemma (requires idx >= Seq.length objs)
          (ensures update_all_objects_aux major objs fwd idx == major)
  = ()

/// Unfold: update_major_pointers is update_all_objects_aux at index 0
let update_major_pointers_unfold (major: heap) (fwd: forwarding_map)
  : Lemma (update_major_pointers major fwd ==
           update_all_objects_aux major (objects zero_addr major) fwd 0)
  = ()

/// ---------------------------------------------------------------------------
/// Positional step lemma — connects position-based walk to spec
/// ---------------------------------------------------------------------------

/// Sub-lemma: if two heaps agree on all read_word from start onward, objects from start agree.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec objects_eq_when_reads_agree (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    (forall (a: hp_addr). U64.v a >= U64.v start ==>
                      read_word g1 a == read_word g2 a))
          (ensures objects start g1 == objects start g2)
          (decreases (Seq.length g1 - U64.v start)) =
  if U64.v start + 8 >= Seq.length g1 then ()
  else begin
    assert (read_word g1 start == read_word g2 start);
    let header = read_word g1 start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g1 || next_start_nat >= pow2 64 then ()
    else if next_start_nat >= heap_size then ()
    else begin
      let next_start : hp_addr = U64.uint_to_t next_start_nat in
      objects_eq_when_reads_agree g1 g2 next_start
    end
  end
#pop-options

/// Objects from start are preserved when start >= obj + wz*8.
/// Since all field writes are at addresses < obj + wz*8 <= start,
/// all reads from start onward are unchanged.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
private let update_object_pointers_preserves_objects_above
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map)
  (start: hp_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      U64.v start >= U64.v obj + wosize * 8 /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures objects start (update_object_pointers major obj wosize fwd 0) == objects start major)
  = let major' = update_object_pointers major obj wosize fwd 0 in
    let read_above_helper (a: hp_addr) : Lemma
      (requires U64.v a >= U64.v start)
      (ensures read_word major' a == read_word major a)
    = update_object_pointers_preserves_addr_above major obj wosize fwd 0 a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires read_above_helper);
    objects_eq_when_reads_agree major' major start
#pop-options

/// Objects nonemptiness depends only on the header read at start.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let objects_nonempty_from_header (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    read_word g1 start == read_word g2 start /\
                    Seq.length (objects start g1) > 0)
          (ensures Seq.length (objects start g2) > 0)
  = ()
#pop-options

/// Helper: density is preserved through update_object_pointers
#push-options "--z3rlimit 300 --fuel 0 --split_queries always --z3refresh"
private let update_object_pointers_preserves_density
  (major: heap) (obj: obj_addr) (wz: nat) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    Seq.mem obj (objects zero_addr major) /\
                    U64.v obj + wz * 8 <= heap_size /\
                    wz == U64.v (wosize_of_object obj major))
          (ensures heap_objects_dense (update_object_pointers major obj wz fwd 0))
  = let major' = update_object_pointers major obj wz fwd 0 in
    let field_bounds_helper () : Lemma
      (forall (j:nat). j < wz ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0))
      = assert (U64.v obj % 8 == 0);
        assert (U64.v obj + wz * 8 <= heap_size)
    in
    field_bounds_helper ();
    update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);
    let aux (start: hp_addr) : Lemma
      (requires U64.v start + 8 < heap_size /\
               Seq.mem (f_address start) (objects zero_addr major') /\
               Seq.length (objects start major') > 0)
      (ensures (let wz' = getWosize (read_word major' start) in
                let next = U64.v start + ((U64.v wz' + 1) * 8) in
                next + 8 < heap_size ==>
                Seq.length (objects (U64.uint_to_t next) major') > 0 /\
                Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr major')))
    = // Header at start is preserved
      let fa = f_address start in
      f_address_spec start;
      hd_address_spec fa;
      if U64.v fa = U64.v obj then
        update_object_pointers_preserves_self_header major obj wz fwd 0
      else if U64.v fa > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 fa
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 start;
      assert (read_word major' start == read_word major start);
      // Membership transfers
      assert (Seq.mem (f_address start) (objects zero_addr major));
      // Nonemptiness of objects start in major
      objects_nonempty_from_header major' major start;
      assert (Seq.length (objects start major) > 0);
      // Transfer density from major
      let wz' = getWosize (read_word major start) in
      let next = U64.v start + ((U64.v wz' + 1) * 8) in
      if next + 8 < heap_size then begin
        assert (Seq.length (objects (U64.uint_to_t next) major) > 0);
        assert (Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr major));
        let next_hp : hp_addr = U64.uint_to_t next in
        let fa_next = f_address next_hp in
        f_address_spec next_hp;
        hd_address_spec fa_next;
        if U64.v fa_next = U64.v obj then
          update_object_pointers_preserves_self_header major obj wz fwd 0
        else if U64.v fa_next > U64.v obj then
          update_object_pointers_preserves_other_header major obj wz fwd 0 fa_next
        else
          update_object_pointers_preserves_addr_below major obj wz fwd 0 next_hp;
        assert (read_word major' next_hp == read_word major next_hp);
        objects_nonempty_from_header major major' next_hp
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Shift lemma: processing cons hd tl from index (k+1) is the same as processing tl from index k.
/// This is a structural property of the recursive function update_all_objects_aux.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec update_all_objects_aux_shift
  (g: heap) (hd: obj_addr) (tl: seq obj_addr) (fwd: forwarding_map) (k: nat)
  : Lemma (ensures update_all_objects_aux g (Seq.cons hd tl) fwd (k + 1) ==
                   update_all_objects_aux g tl fwd k)
          (decreases (Seq.length tl - k)) =
  if k >= Seq.length tl then ()
  else begin
    // Seq.index (cons hd tl) (k+1) == Seq.index tl k
    Seq.lemma_index_is_nth tl k;
    Seq.lemma_index_is_nth (Seq.cons hd tl) (k + 1);
    assert (Seq.index (Seq.cons hd tl) (k + 1) == Seq.index tl k);
    let obj = Seq.index tl k in
    if is_blue obj g then
      update_all_objects_aux_shift g hd tl fwd (k + 1)
    else begin
      let wz = U64.v (wosize_of_object obj g) in
      let g' = update_object_pointers g obj wz fwd 0 in
      update_all_objects_aux_shift g' hd tl fwd (k + 1)
    end
  end
#pop-options

/// Master positional step lemma
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
let update_all_objects_positional_step
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let major' = update_object_pointers major obj wz fwd 0 in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    well_formed_heap_part1 major' /\
                    heap_objects_dense major' /\
                    objects zero_addr major' == objects zero_addr major /\
                    (next_nat < heap_size ==>
                      update_all_objects_aux major' (objects (U64.uint_to_t next_nat) major') fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat >= heap_size ==>
                      major' == update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major') /\
                      Seq.length (objects (U64.uint_to_t next_nat) major') > 0)))
  = // Step 1: Establish bounds
    let obj : obj_addr = f_address pos in
    objects_nonempty_head_fits pos major;
    wfh_part1_obj_bound major obj;
    f_address_spec pos;
    hd_f_roundtrip pos;
    let hdr = read_word major pos in
    let wz = U64.v (getWosize hdr) in
    let next_nat = U64.v pos + (wz + 1) * 8 in
    wosize_of_object_spec obj major;
    assert (wz == U64.v (wosize_of_object obj major));
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v pos) ((wz + 1) * 8) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (wz + 1) 8 8;
    objects_nonempty_head pos major;
    objects_nonempty_next pos major;

    // Field bounds
    let field_bounds () : Lemma
      (forall (j:nat). j < wz ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0))
      = assert (U64.v obj % 8 == 0);
        assert (U64.v obj + wz * 8 <= heap_size)
    in
    field_bounds ();

    // Step 2: well_formed_heap_part1 major'
    let major' = update_object_pointers major obj wz fwd 0 in
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = update_object_pointers_preserves_objects major obj wz fwd 0;
      hd_address_spec h;
      if h = obj then begin
        update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec h major'; wosize_of_object_spec h major
      end else if U64.v h > U64.v obj then begin
        update_object_pointers_preserves_other_header major obj wz fwd 0 h;
        wosize_of_object_spec h major'; wosize_of_object_spec h major
      end else begin
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
        wosize_of_object_spec h major; wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    assert (well_formed_heap_part1 major');

    // Step 3: density preserved
    update_object_pointers_preserves_density major obj wz fwd;

    // Step 4: objects zero_addr preserved
    update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);

    // Step 5: Spec equality
    if next_nat < heap_size then begin
      let next_hp : hp_addr = U64.uint_to_t next_nat in
      // next_hp = pos + (wz+1)*8 = obj + wz*8 (since obj = pos + 8)
      // All field writes are at addresses [obj, obj+(wz-1)*8], all < next_hp
      update_object_pointers_preserves_objects_above major obj wz fwd next_hp;
      assert (objects pos major == Seq.cons obj (objects next_hp major));
      assert (objects next_hp major' == objects next_hp major);
      // Use shift lemma
      update_all_objects_aux_shift major' obj (objects next_hp major) fwd 0;
      ()
    end else begin
      // Terminal case
      assert (Seq.length (objects pos major) == 1);
      assert (Seq.index (objects pos major) 0 == obj);
      ()
    end;
    // Step 6: Density at next position
    if next_nat + 8 < heap_size then begin
      let next_hp : hp_addr = U64.uint_to_t next_nat in
      update_object_pointers_preserves_objects_above major obj wz fwd next_hp;
      assert (objects next_hp major' == objects next_hp major);
      f_address_spec next_hp;
      let fa_next = f_address next_hp in
      hd_address_spec fa_next;
      if U64.v fa_next = U64.v obj then
        update_object_pointers_preserves_self_header major obj wz fwd 0
      else if U64.v fa_next > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 fa_next
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 next_hp;
      assert (Seq.mem (f_address pos) (objects zero_addr major));
      assert (Seq.length (objects pos major) > 0)
    end
#pop-options

/// Blue skip step: when the current object is blue (free-list cell),
/// skip it without modifying the heap. The spec connection advances past it.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let update_all_objects_positional_step_blue
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    // Spec: skipping blue advances to the next object with same heap
                    (next_nat < heap_size ==>
                      update_all_objects_aux major (objects (U64.uint_to_t next_nat) major) fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    // Terminal: when next reaches heap_size, result is just major
                    (next_nat >= heap_size ==>
                      major == update_all_objects_aux major (objects pos major) fwd 0) /\
                    // Density: next position is valid
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major) /\
                      Seq.length (objects (U64.uint_to_t next_nat) major) > 0)))
  = let obj : obj_addr = f_address pos in
    objects_nonempty_head_fits pos major;
    wfh_part1_obj_bound major obj;
    f_address_spec pos;
    let hdr = read_word major pos in
    let wz = U64.v (getWosize hdr) in
    let next_nat = U64.v pos + (wz + 1) * 8 in
    wosize_of_object_spec obj major;
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v pos) ((wz + 1) * 8) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (wz + 1) 8 8;
    objects_nonempty_head pos major;
    objects_nonempty_next pos major;
    // Blue skip: update_all_objects_aux skips blue objects, leaving heap unchanged.
    // The objects list at pos is cons obj (objects next major).
    // Since is_blue obj major, the spec function skips obj and recurses at idx+1.
    if next_nat < heap_size then begin
      let next_hp : hp_addr = U64.uint_to_t next_nat in
      assert (objects pos major == Seq.cons obj (objects next_hp major));
      update_all_objects_aux_shift major obj (objects next_hp major) fwd 0
    end else begin
      assert (Seq.length (objects pos major) == 1);
      assert (Seq.index (objects pos major) 0 == obj)
    end
#pop-options

/// Terminal step
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let update_all_objects_terminal_step
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    (next_nat + 8 >= heap_size ==>
                      (let major' = update_object_pointers major obj wz fwd 0 in
                       major' == update_all_objects_aux major (objects pos major) fwd 0))))
  = // With fuel 2, Z3 unfolds update_all_objects_aux on singleton [obj]:
    //   idx=0 < length [obj]=1: unfolds to aux major' [obj] fwd 1
    //   idx=1 >= length [obj]=1: returns major'
    // So result = major'
    let obj : obj_addr = f_address pos in
    objects_nonempty_head_fits pos major;
    wfh_part1_obj_bound major obj;
    f_address_spec pos;
    hd_f_roundtrip pos;
    wosize_of_object_spec obj major;
    let hdr = read_word major pos in
    let wz = U64.v (getWosize hdr) in
    let next_nat = U64.v pos + (wz + 1) * 8 in
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v pos) ((wz + 1) * 8) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (wz + 1) 8 8;
    objects_nonempty_head pos major;
    objects_nonempty_next pos major;
    if next_nat + 8 >= heap_size then begin
      assert (Seq.length (objects pos major) == 1);
      assert (Seq.index (objects pos major) 0 == obj);
      ()
    end
#pop-options

/// Initial membership: first object is at f_address 0UL when heap has objects.
/// The precondition that objects zero_addr g is nonempty is a standard heap invariant
/// (same approach as mark-and-sweep's heap_objects_dense).
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let objects_initial_membership (g: heap)
  : Lemma (requires heap_size > 8 /\ well_formed_heap_part1 g /\
                    Seq.length (objects zero_addr g) > 0)
          (ensures Seq.mem (f_address 0UL) (objects zero_addr g))
  = // With fuel 2, Z3 can unfold objects zero_addr g and see that when it's nonempty,
    // the head is f_address 0UL. From the definition:
    // objects zero_addr g = cons (f_address 0UL) (objects next g) when nonempty.
    // Therefore Seq.mem (f_address 0UL) (objects zero_addr g).
    ()
#pop-options

/// ---------------------------------------------------------------------------
/// update_major_pointers preserves headers (tag, wosize, color)
/// ---------------------------------------------------------------------------

/// Inductive: update_all_objects_aux preserves the header word of any object.
#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_preserves_header
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat) (h: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs)
    (ensures read_word (update_all_objects_aux major objs fwd idx) (hd_address h) ==
             read_word major (hd_address h))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if is_blue obj major then
      // Blue skip: heap unchanged, recurse
      update_all_objects_aux_preserves_header major objs fwd (idx + 1) h
    else begin
      let wz = U64.v (wosize_of_object obj major) in
      hd_address_spec obj;
      assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
      update_object_pointers_preserves_objects major obj wz fwd 0;
      let major' = update_object_pointers major obj wz fwd 0 in
      assert (objects zero_addr major' == objs);
      // Show header of h is preserved through this step
      hd_address_spec h;
      if h = obj then
        update_object_pointers_preserves_self_header major obj wz fwd 0
      else if U64.v h > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 h
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
      assert (read_word major' (hd_address h) == read_word major (hd_address h));
      // Establish wfh_part1 for major' (needed for recursive call)
      let aux_wfh (x: obj_addr) : Lemma
        (requires Seq.mem x (objects zero_addr major'))
        (ensures U64.v (hd_address x) + 8 + (U64.v (wosize_of_object x major') * 8) <= Seq.length major')
      = hd_address_spec x;
        if x = obj then begin
          update_object_pointers_preserves_self_header major obj wz fwd 0;
          wosize_of_object_spec x major'; wosize_of_object_spec x major
        end else if U64.v x > U64.v obj then begin
          update_object_pointers_preserves_other_header major obj wz fwd 0 x;
          wosize_of_object_spec x major'; wosize_of_object_spec x major
        end else begin
          update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address x);
          wosize_of_object_spec x major; wosize_of_object_spec x major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      assert (well_formed_heap_part1 major');
      // Recurse
      update_all_objects_aux_preserves_header major' objs fwd (idx + 1) h
    end
  end
#pop-options

/// update_major_pointers preserves the header word of any object in the objects list.
let update_major_pointers_preserves_header (major: heap) (fwd: forwarding_map) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\ Seq.mem h (objects zero_addr major))
    (ensures read_word (update_major_pointers major fwd) (hd_address h) ==
             read_word major (hd_address h)) =
  update_all_objects_aux_preserves_header major (objects zero_addr major) fwd 0 h

/// update_major_pointers preserves all fields of blue objects (since they are skipped).
/// For non-blue objects that are processed: their body writes are separated from blue's fields.
#push-options "--z3rlimit 400 --fuel 1 --split_queries always"
private let rec update_all_objects_aux_preserves_blue_field
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  (h: obj_addr) (j: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs /\
      is_blue h major /\
      j < U64.v (wosize_of_object h major) /\
      U64.v h + j * 8 + 8 <= heap_size /\
      (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_all_objects_aux major objs fwd idx) field_addr ==
              read_word major field_addr))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    if is_blue obj major then
      // obj is blue: skipped, heap unchanged, recurse
      update_all_objects_aux_preserves_blue_field major objs fwd (idx + 1) h j
    else begin
      let wz = U64.v (wosize_of_object obj major) in
      hd_address_spec obj;
      assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
      assert (Seq.mem obj (objects zero_addr major));
      assert (U64.v obj % 8 == 0);
      assert (U64.v obj + wz * 8 <= heap_size);
      let field_bounds_obj () : Lemma
        (forall (k:nat). k < wz ==>
          (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0))
        = ()
      in
      field_bounds_obj ();
      update_object_pointers_preserves_objects major obj wz fwd 0;
      let major' = update_object_pointers major obj wz fwd 0 in
      assert (objects zero_addr major' == objs);
      // Show field of h is preserved: h != obj (h is blue, obj is not blue)
      // So h and obj are different objects with separated body regions
      let field_addr : hp_addr = U64.uint_to_t (U64.v h + j * 8) in
      if U64.v h > U64.v obj then begin
        // h > obj: field_addr >= h > obj + wz*8, so above obj's body
        objects_separated 0UL major obj h;
        assert (U64.v obj + (wz + 1) * 8 <= U64.v h);
        assert (U64.v field_addr >= U64.v h);
        assert (U64.v field_addr >= U64.v obj + wz * 8);
        update_object_pointers_preserves_addr_above major obj wz fwd 0 field_addr
      end else begin
        // h < obj: field_addr < h + wosize_h * 8 <= obj, so below obj's body
        let wz_h = U64.v (wosize_of_object h major) in
        objects_separated 0UL major h obj;
        assert (U64.v h + (wz_h + 1) * 8 <= U64.v obj);
        assert (U64.v field_addr < U64.v h + wz_h * 8);
        assert (U64.v field_addr < U64.v obj);
        update_object_pointers_preserves_addr_below major obj wz fwd 0 field_addr
      end;
      assert (read_word major' field_addr == read_word major field_addr);
      // Establish wfh_part1 for major'
      let aux_wfh (x: obj_addr) : Lemma
        (requires Seq.mem x (objects zero_addr major'))
        (ensures U64.v (hd_address x) + 8 + (U64.v (wosize_of_object x major') * 8) <= Seq.length major')
      = hd_address_spec x;
        if x = obj then begin
          update_object_pointers_preserves_self_header major obj wz fwd 0;
          wosize_of_object_spec x major'; wosize_of_object_spec x major
        end else if U64.v x > U64.v obj then begin
          update_object_pointers_preserves_other_header major obj wz fwd 0 x;
          wosize_of_object_spec x major'; wosize_of_object_spec x major
        end else begin
          update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address x);
          wosize_of_object_spec x major; wosize_of_object_spec x major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      assert (well_formed_heap_part1 major');
      // h's header is preserved → is_blue h major' and wosize unchanged
      hd_address_spec h;
      if U64.v h > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 h
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
      // Explicitly chain: header preserved → color preserved → is_blue preserved
      color_of_object_spec h major;
      color_of_object_spec h major';
      is_blue_iff h major;
      is_blue_iff h major';
      wosize_of_object_spec h major;
      wosize_of_object_spec h major';
      assert (is_blue h major');
      assert (j < U64.v (wosize_of_object h major'));
      assert (objects zero_addr major' == objs);
      // Recurse
      update_all_objects_aux_preserves_blue_field major' objs fwd (idx + 1) h j
    end
  end
#pop-options

let update_major_pointers_preserves_blue_field
  (major: heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    Seq.mem h (objects zero_addr major) /\
                    is_blue h major /\
                    j < U64.v (wosize_of_object h major) /\
                    U64.v h + j * 8 + 8 <= heap_size /\
                    (U64.v h + j * 8) % 8 == 0)
    (ensures (let field_addr = U64.uint_to_t (U64.v h + j * 8) in
              read_word (update_major_pointers major fwd) field_addr ==
              read_word major field_addr)) =
  update_all_objects_aux_preserves_blue_field major (objects zero_addr major) fwd 0 h j

/// update_major_pointers preserves well_formed_heap_part4 (no infix objects).
#push-options "--z3rlimit 20"
let update_major_pointers_preserves_wfh_part4 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part4 (update_major_pointers major fwd)) =
  update_major_pointers_preserves_objects major fwd;
  let mc = update_major_pointers major fwd in
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr mc))
    (ensures ~(GC.Spec.Object.is_infix h mc))
  = update_major_pointers_preserves_header major fwd h;
    GC.Spec.Object.tag_of_object_spec h mc;
    GC.Spec.Object.tag_of_object_spec h major;
    GC.Spec.Object.is_infix_spec h mc;
    GC.Spec.Object.is_infix_spec h major
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// update_major_pointers preserves well_formed_heap_part3 (infix well-formedness).
/// Since part4 holds (no objects are infix), infix_wf is vacuously true.
#push-options "--z3rlimit 20"
let update_major_pointers_preserves_wfh_part3 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part3 (update_major_pointers major fwd)) =
  update_major_pointers_preserves_wfh_part4 major fwd;
  update_major_pointers_preserves_objects major fwd;
  let mc = update_major_pointers major fwd in
  let pf (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr mc) /\ GC.Spec.Object.is_infix h mc)
    (ensures (let p = GC.Spec.Object.parent_closure_addr_nat h mc in
              p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
              Seq.mem (U64.uint_to_t p) (objects zero_addr mc) /\
              GC.Spec.Object.is_closure (U64.uint_to_t p) mc))
  = // part4 says ~(is_infix h mc), contradiction
    assert (well_formed_heap_part4 mc);
    assert (Seq.mem h (objects zero_addr mc) ==> ~(GC.Spec.Object.is_infix h mc))
  in
  GC.Spec.Object.infix_wf_intro mc (objects zero_addr mc) pf
#pop-options

/// ---------------------------------------------------------------------------
/// Promoted objects land in the final major heap's objects list
/// ---------------------------------------------------------------------------

/// After promote_object succeeds (new_addr ≠ 0), new_addr ∈ objects(result).
#push-options "--z3rlimit 40 --fuel 1"
private let promote_object_adds_new_addr
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              (U64.v res.new_addr >= U64.v mword /\
               U64.v res.new_addr < heap_size /\
               U64.v res.new_addr % U64.v mword == 0 /\
               Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out)))) =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
    assert (objects zero_addr (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects zero_addr alloc_res.heap_out)
  end
#pop-options

/// fwd_all_targets_valid implies fwd_targets_in_objects (for any idx)
let fwd_all_implies_positional (fwd: forwarding_map) (live_set: seq U64.t) (idx: nat) (g: heap)
  : Lemma (requires fwd_all_targets_valid fwd g)
          (ensures fwd_targets_in_objects fwd live_set idx g) = ()

/// The core induction: promote_all_aux puts every forwarded address into objects of the final heap.
/// Uses the simpler fwd_all_targets_valid invariant.
#push-options "--z3rlimit 200 --fuel 1 --split_queries always"
let rec promote_all_aux_adds_promoted
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    fwd_all_targets_valid fwd major)
          (ensures (let res = promote_all_aux minor major fp live_set fwd idx in
                    fwd_all_targets_valid res.fwd_map res.major_final))
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      // Skip: fwd unchanged, heap unchanged — invariant trivially preserved
      promote_all_aux_adds_promoted minor major fp live_set fwd (idx + 1)
    else begin
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then
        // OOM: fwd unchanged, heap unchanged — invariant trivially preserved
        ()
      else begin
        let fuel = heap_size / U64.v mword in
        // new_addr is in objects of res.major_out
        promote_object_adds_new_addr minor major obj fp wz;
        // existing objects persist
        promote_object_preserves_objects_part1 minor major obj fp wz;
        // allocator properties for recursion
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
        // fwd' extends fwd with obj -> new_addr
        let fwd' = extend_forwarding fwd obj res.new_addr in
        // Show fwd_all_targets_valid fwd' res.major_out:
        // For x ≠ obj: fwd'(x) = fwd(x), target in objects(major) ⊆ objects(res.major_out) ✓
        // For x = obj: fwd'(obj) = new_addr, which is in objects(res.major_out) ✓
        assert (fwd_all_targets_valid fwd' res.major_out);
        promote_all_aux_adds_promoted minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
    end
#pop-options

/// Top-level: promote_all_spec produces fwd_all_targets_valid for its final heap.
let promote_all_fwd_all_targets_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_all_targets_valid res.fwd_map res.major_final)) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  assert (fwd_all_targets_valid empty_forwarding major);
  promote_all_aux_adds_promoted minor major fp live_set empty_forwarding 0

/// Top-level: after promote_all_spec, every forwarded object's address is in objects of the final heap.
let promote_all_adds_promoted
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_targets_in_objects res.fwd_map live_set (Seq.length live_set) res.major_final)) =
  promote_all_fwd_all_targets_valid minor major fp live_set;
  let res = promote_all_spec minor major fp live_set in
  fwd_all_implies_positional res.fwd_map live_set (Seq.length live_set) res.major_final

/// ---------------------------------------------------------------------------
/// Minor collection correctness (strengthened)
/// ---------------------------------------------------------------------------

/// After minor collection, every promoted object's forwarded address
/// is in the post-collection major heap's objects list.
let minor_collect_preserves_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t)
  : Lemma (requires
             minor_wf minor /\
             well_formed_heap major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             Seq.mem obj (live_set_of minor major roots))
          (ensures
             (let res = minor_collect_spec minor major fp roots in
              let live_set = live_set_of minor major roots in
              let prom_res = promote_all_spec minor major fp live_set in
              fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major)) =
  let live_set = live_set_of minor major roots in
  promote_all_adds_promoted minor major fp live_set;
  let prom_res = promote_all_spec minor major fp live_set in
  promote_all_preserves_wfh_part1 minor major fp live_set;
  update_major_pointers_preserves_objects prom_res.major_final prom_res.fwd_map;
  minor_collect_spec_unfold minor major fp roots

/// ---------------------------------------------------------------------------
/// Field effect of update_object_pointers (single object)
/// ---------------------------------------------------------------------------

/// After update_object_pointers, reading field j gives the expected result:
/// forwarded if it was a minor pointer with valid fwd, unchanged otherwise.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_field_self
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat) (j: nat)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      j < wosize /\
      i <= j /\
      (forall (k:nat). k < wosize ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))
    (ensures
      (let updated = update_object_pointers major obj wosize fwd i in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = read_word major field_addr in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_val)))
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    assert (field_offset + 8 <= heap_size);
    assert (field_offset % 8 == 0);
    let field_val = read_word major (U64.uint_to_t field_offset) in
    if i = j then begin
      // This iteration processes field j directly
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          write_body_preserves_objects major obj addr new_val;
          let major' = write_word major addr new_val in
          hd_address_spec obj;
          read_write_different major addr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          // After writing fwd(field_val) at field j, subsequent updates (i+1..wz-1)
          // don't touch field j because they write at obj+(i+1)*8, obj+(i+2)*8, etc.
          // After writing fwd(field_val) at field j = i, subsequent updates (i+1..wz-1)
          // write at obj + k*8 for k > i, all indices > addr = obj + i*8.
          // update_obj_ptrs_preserves_earlier_field proves the recursive call preserves addr.
          read_write_same major addr new_val;
          assert (read_word major' addr == new_val);
          update_obj_ptrs_preserves_earlier_field major' obj wosize fwd (i + 1) j
        end else begin
          // field_val is minor pointer but fwd is 0: field unchanged, recursive call starts at i+1 > j
          update_obj_ptrs_preserves_earlier_field major obj wosize fwd (i + 1) j
        end
      else
        // Not a minor pointer: field unchanged, recursive call starts at i+1 > j
        update_obj_ptrs_preserves_earlier_field major obj wosize fwd (i + 1) j
    end else begin
      // i < j: this iteration processes field i, not j
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          write_body_preserves_objects major obj addr new_val;
          let major' = write_word major addr new_val in
          hd_address_spec obj;
          read_write_different major addr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          // Writing at field i doesn't affect field j (i < j, so addr = obj+i*8 < obj+j*8)
          let field_j_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
          assert (U64.v addr < U64.v field_j_addr);
          read_write_different major addr field_j_addr new_val;
          assert (read_word major' field_j_addr == read_word major field_j_addr);
          update_object_pointers_field_self major' obj wosize fwd (i + 1) j
        end else
          update_object_pointers_field_self major obj wosize fwd (i + 1) j
      else
        update_object_pointers_field_self major obj wosize fwd (i + 1) j
    end

/// Helper: update_object_pointers at indices > j doesn't touch field j
and update_obj_ptrs_preserves_earlier_field
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat) (j: nat)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      j < i /\ i <= wosize /\
      (forall (k:nat). k < wosize ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))
    (ensures
      (let field_j_addr = U64.uint_to_t (U64.v obj + j * 8) in
       read_word (update_object_pointers major obj wosize fwd i) field_j_addr ==
       read_word major field_j_addr))
    (decreases (wosize - i)) =
  let field_j_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    assert (field_offset + 8 <= heap_size);
    assert (field_offset % 8 == 0);
    let field_val = read_word major (U64.uint_to_t field_offset) in
    if is_minor_pointer field_val then
      let new_val = fwd field_val in
      if new_val <> 0UL then begin
        let addr : hp_addr = U64.uint_to_t field_offset in
        // addr = obj + i*8 > obj + j*8 = field_j_addr (since i > j)
        assert (U64.v addr > U64.v field_j_addr);
        write_body_preserves_objects major obj addr new_val;
        let major' = write_word major addr new_val in
        read_write_different major addr field_j_addr new_val;
        hd_address_spec obj;
        read_write_different major addr (hd_address obj) new_val;
        wosize_of_object_spec obj major;
        wosize_of_object_spec obj major';
        update_obj_ptrs_preserves_earlier_field major' obj wosize fwd (i + 1) j
      end else
        update_obj_ptrs_preserves_earlier_field major obj wosize fwd (i + 1) j
    else
      update_obj_ptrs_preserves_earlier_field major obj wosize fwd (i + 1) j
#pop-options

/// ---------------------------------------------------------------------------
/// update_all_objects_aux field effect
/// ---------------------------------------------------------------------------

/// Helper: find the index of an element in a sequence
private let rec seq_index_of (#a:eqtype) (s: seq a) (x: a{Seq.mem x s})
  : GTot (n:nat{n < Seq.length s /\ Seq.index s n == x})
  (decreases Seq.length s) =
  if Seq.index s 0 = x then 0
  else begin
    Seq.lemma_index_is_nth s 0;
    let tl = Seq.tail s in
    Seq.lemma_mem_append (Seq.create 1 (Seq.index s 0)) tl;
    1 + seq_index_of tl x
  end

/// Helper: adjacent elements in objects list are strictly ordered.
/// Proof by structural induction on the objects list construction.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
private let rec objects_monotone_adjacent (g: heap) (start: hp_addr) (i: nat)
  : Lemma
    (requires i + 1 < Seq.length (objects start g))
    (ensures U64.v (Seq.index (objects start g) i) < U64.v (Seq.index (objects start g) (i + 1)))
    (decreases (Seq.length g - U64.v start)) =
  // objects start g = if start+8 >= |g| then [] else cons (start+8) (objects next_start g)
  // where next_start = start + (wz+1)*8
  if U64.v start + 8 >= Seq.length g then ()  // impossible: objects is empty, contradicts precond
  else
    let header = read_word g start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()  // impossible
    else begin
      f_address_spec start;
      let first : obj_addr = f_address start in
      if next_start_nat >= heap_size then ()  // objects is singleton, can't have i+1 < 1
      else begin
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        let rest = objects next_start g in
        // objects start g = cons first rest
        // Seq.index (cons first rest) 0 = first
        // Seq.index (cons first rest) (k+1) = Seq.index rest k
        if i = 0 then begin
          // Need: first < Seq.index rest 0
          // All elements of rest are > next_start (from objects_addresses_gt_start)
          // next_start = start + (wz+1)*8 > start + 8 = first (since wz >= 0, (wz+1)*8 >= 8)
          // Actually next_start = start + (wz+1)*8 >= start + 8 = first
          // But wz could be 0 and then next_start = start + 8 = first!
          // No: wz is getWosize header. And next_start_nat < heap_size was checked.
          // If wz = 0, then next_start = start + 8 = first, and objects_addresses_gt_start
          // gives elements of rest > next_start = first. 
          objects_addresses_gt_start next_start g (Seq.index rest 0);
          FStar.Seq.Properties.seq_mem_k rest 0;
          assert (U64.v (Seq.index rest 0) > U64.v next_start);
          assert (U64.v next_start >= U64.v first)
        end else begin
          // i > 0: Seq.index (cons first rest) i = Seq.index rest (i-1)
          //        Seq.index (cons first rest) (i+1) = Seq.index rest i
          // Need: Seq.index rest (i-1) < Seq.index rest i
          // By induction on rest = objects next_start g
          objects_monotone_adjacent g next_start (i - 1)
        end
      end
    end
#pop-options

/// Helper: objects list is strictly monotone — earlier positions have lower addresses.
/// Proof: objects_addresses_gt_start shows all elements at index > 0 have address > first element.
/// By induction on the sequence structure, earlier positions have lower addresses.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec objects_strictly_monotone (g: heap) (i j: nat)
  : Lemma
    (requires
      i < j /\ j < Seq.length (objects zero_addr g))
    (ensures U64.v (Seq.index (objects zero_addr g) i) < U64.v (Seq.index (objects zero_addr g) j))
    (decreases j - i) =
  if j = i + 1 then
    objects_monotone_adjacent g 0UL i
  else begin
    objects_strictly_monotone g i (j - 1);
    objects_strictly_monotone g (j - 1) j
  end
#pop-options

/// Helper: objects before position pos have addresses < obj
#push-options "--z3rlimit 20"
private let objects_below_before (g: heap) (obj: obj_addr) (pos: nat)
  : Lemma
    (requires
      pos < Seq.length (objects zero_addr g) /\
      Seq.index (objects zero_addr g) pos == obj)
    (ensures
      (forall (k:nat). k < pos /\ k < Seq.length (objects zero_addr g) ==>
        U64.v (Seq.index (objects zero_addr g) k) < U64.v obj)) =
  let aux (k: nat{k < Seq.length (objects zero_addr g)}) : Lemma
    (requires k < pos)
    (ensures U64.v (Seq.index (objects zero_addr g) k) < U64.v obj)
  = objects_strictly_monotone g k pos
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Helper: objects after position pos have addresses > obj
#push-options "--z3rlimit 20"
private let objects_above_after (g: heap) (obj: obj_addr) (pos: nat)
  : Lemma
    (requires
      pos < Seq.length (objects zero_addr g) /\
      Seq.index (objects zero_addr g) pos == obj)
    (ensures
      (forall (k:nat). k > pos /\ k < Seq.length (objects zero_addr g) ==>
        U64.v (Seq.index (objects zero_addr g) k) > U64.v obj)) =
  let aux (k: nat{k < Seq.length (objects zero_addr g)}) : Lemma
    (requires k > pos)
    (ensures U64.v (Seq.index (objects zero_addr g) k) > U64.v obj)
  = objects_strictly_monotone g pos k
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// update_all_objects_aux processing objects AFTER obj doesn't change obj's field j.
/// Those objects are at higher addresses, so their body regions don't overlap obj's fields.
#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_after_preserves_field
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map)
  (idx: nat) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem obj objs /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      (forall (k:nat). k >= idx /\ k < Seq.length objs ==>
        U64.v (Seq.index objs k) > U64.v obj))
    (ensures
      (let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       read_word (update_all_objects_aux major objs fwd idx) field_addr ==
       read_word major field_addr))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let other = Seq.index objs idx in
    assert (U64.v other > U64.v obj);
    if is_blue other major then
      // Blue skip: heap unchanged, field trivially preserved
      update_all_objects_aux_after_preserves_field major objs fwd (idx + 1) obj j
    else begin
      let wz_other = U64.v (wosize_of_object other major) in
      hd_address_spec other;
      // obj + j*8 < obj + wz_obj*8 < other (by objects_separated, since obj < other and both in objs)
      let wz_obj = U64.v (wosize_of_object obj major) in
      objects_separated 0UL major obj other;
      assert (U64.v obj + (wz_obj + 1) * 8 <= U64.v other);
      assert (U64.v obj + j * 8 < U64.v other);
      let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
      assert (forall (k:nat). k < wz_other ==>
        (U64.v other + k * 8 + 8 <= heap_size /\ (U64.v other + k * 8) % 8 == 0));
      update_object_pointers_preserves_addr_below major other wz_other fwd 0 field_addr;
      let major' = update_object_pointers major other wz_other fwd 0 in
      update_object_pointers_preserves_objects major other wz_other fwd 0;
      assert (objects zero_addr major' == objs);
      // Establish well_formed_heap_part1 major'
      let aux_wfh (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr major'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
      = hd_address_spec h;
        if h = other then begin
          update_object_pointers_preserves_self_header major other wz_other fwd 0;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else if U64.v h > U64.v other then begin
          update_object_pointers_preserves_other_header major other wz_other fwd 0 h;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else begin
          update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address h);
          wosize_of_object_spec h major;
          wosize_of_object_spec h major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      // wosize of obj is unchanged: hd_address obj < other, so header is preserved
      hd_address_spec obj;
      update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address obj);
      wosize_of_object_spec obj major;
      wosize_of_object_spec obj major';
      update_all_objects_aux_after_preserves_field major' objs fwd (idx + 1) obj j
    end
  end
#pop-options

/// Main induction: update_all_objects_aux computes the expected field effect.
#push-options "--z3rlimit 300 --fuel 1 --split_queries always --z3refresh"
let rec update_all_objects_aux_field_effect
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map)
  (idx: nat) (obj: obj_addr) (j: nat) (pos: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem obj objs /\
      pos < Seq.length objs /\ Seq.index objs pos == obj /\
      idx <= pos /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      is_blue obj major = false /\
      (forall (k:nat). k >= idx /\ k < pos ==>
        U64.v (Seq.index objs k) < U64.v obj))
    (ensures
      (let updated = update_all_objects_aux major objs fwd idx in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = read_word major field_addr in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_val)))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else if idx = pos then begin
    // Processing obj itself
    let wz = U64.v (wosize_of_object obj major) in
    hd_address_spec obj;
    assert (forall (k:nat). k < wz ==>
      (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0));
    update_object_pointers_field_self major obj wz fwd 0 j;
    let major' = update_object_pointers major obj wz fwd 0 in
    update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objs);
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = obj then begin
        update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else if U64.v h > U64.v obj then begin
        update_object_pointers_preserves_other_header major obj wz fwd 0 h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
        wosize_of_object_spec h major;
        wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    update_object_pointers_preserves_self_header major obj wz fwd 0;
    wosize_of_object_spec obj major;
    wosize_of_object_spec obj major';
    // Remaining objects (pos+1..) are all > obj — they don't change field j
    objects_above_after major obj pos;
    let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
    update_all_objects_aux_after_preserves_field major' objs fwd (idx + 1) obj j
  end else begin
    // idx < pos: processing an object before obj (which has lower address)
    let other = Seq.index objs idx in
    assert (U64.v other < U64.v obj);
    if is_blue other major then
      // Blue skip: heap unchanged, recurse
      update_all_objects_aux_field_effect major objs fwd (idx + 1) obj j pos
    else begin
      let wz_other = U64.v (wosize_of_object other major) in
      hd_address_spec other;
      // other's body is [other, other + wz_other*8), and by objects_separated,
      // other + (wz_other+1)*8 <= obj, so obj + j*8 >= obj > other + wz_other*8
      objects_separated 0UL major other obj;
      let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
      assert (U64.v field_addr >= U64.v other + wz_other * 8);
      assert (forall (k:nat). k < wz_other ==>
        (U64.v other + k * 8 + 8 <= heap_size /\ (U64.v other + k * 8) % 8 == 0));
      update_object_pointers_preserves_addr_above major other wz_other fwd 0 field_addr;
      let major' = update_object_pointers major other wz_other fwd 0 in
      update_object_pointers_preserves_objects major other wz_other fwd 0;
      assert (objects zero_addr major' == objs);
      let aux_wfh (h: obj_addr) : Lemma
        (requires Seq.mem h (objects zero_addr major'))
        (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
      = hd_address_spec h;
        if h = other then begin
          update_object_pointers_preserves_self_header major other wz_other fwd 0;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else if U64.v h > U64.v other then begin
          update_object_pointers_preserves_other_header major other wz_other fwd 0 h;
          wosize_of_object_spec h major';
          wosize_of_object_spec h major
        end else begin
          update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address h);
          wosize_of_object_spec h major;
          wosize_of_object_spec h major'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
      // wosize of obj preserved (obj > other, so header of obj preserved)
      hd_address_spec obj;
      // obj > other + wz_other*8, both multiples of 8, so obj >= other + wz_other*8 + 8
      // hence hd_address obj = obj - 8 >= other + wz_other*8
      assert (U64.v (hd_address obj) >= U64.v other + wz_other * 8);
      update_object_pointers_preserves_addr_above major other wz_other fwd 0 (hd_address obj);
      // Explicitly chain: header preserved → color preserved → is_blue preserved
      color_of_object_spec obj major;
      color_of_object_spec obj major';
      is_blue_iff obj major;
      is_blue_iff obj major';
      wosize_of_object_spec obj major;
      wosize_of_object_spec obj major';
      update_all_objects_aux_field_effect major' objs fwd (idx + 1) obj j pos
    end
  end
#pop-options

/// Top-level: update_major_pointers field effect
let update_major_pointers_field_effect
  (major: heap) (fwd: forwarding_map) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      is_blue obj major = false)
    (ensures
      (let updated = update_major_pointers major fwd in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = read_word major field_addr in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_val))) =
  let objs = objects zero_addr major in
  let pos = seq_index_of objs obj in
  objects_below_before major obj pos;
  update_all_objects_aux_field_effect major objs fwd 0 obj j pos

/// Helper: explicit instantiation of blue_fields_closed for a specific object and field
let blue_fields_closed_inst (major: heap) (src: obj_addr) (j: nat)
  : Lemma (requires blue_fields_closed major /\
                    Seq.mem src (objects zero_addr major) /\ is_blue src major /\
                    j < U64.v (wosize_of_object src major) /\
                    U64.v src + j * 8 + 8 <= heap_size)
          (ensures (let v = read_word major (U64.uint_to_t (U64.v src + j * 8)) in
                    is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr major)))
  = reveal_opaque (`%blue_fields_closed) blue_fields_closed

/// update_major_pointers establishes well_formed_heap_part2 (pointer closure).
/// Uses pointer_closure_modulo_fwd (weaker than full part2) + fwd_all_targets_valid.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let update_major_pointers_preserves_wfh_part2 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    pointer_closure_modulo_fwd major fwd /\
                    fwd_all_targets_valid fwd major /\
                    blue_fields_closed major)
    (ensures well_formed_heap_part2 (update_major_pointers major fwd)) =
  let mc = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (objects zero_addr mc) /\
                      j < U64.v (wosize_of_object src mc) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word mc (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr mc)))
    = update_major_pointers_preserves_header major fwd src;
      GC.Spec.Object.wosize_of_object_spec src mc;
      GC.Spec.Object.wosize_of_object_spec src major;
      if is_blue src major then begin
        update_major_pointers_preserves_blue_field major fwd src j;
        blue_fields_closed_inst major src j
      end else begin
        update_major_pointers_field_effect major fwd src j;
        ()
      end
  in
  update_major_pointers_preserves_wfh_part1 major fwd;
  well_formed_heap_part2_from_field_closure mc field_closure
#pop-options

/// ---------------------------------------------------------------------------
/// Promote_all field preservation
/// ---------------------------------------------------------------------------

/// Helper: promote_object preserves reads in the body of a different object
/// that avoids the free-list chain. After alloc + copy_fields, the body of
/// `other` is untouched because:
/// 1. alloc_spec only modifies headers/links of free-list blocks (alloc_spec_read_other)
/// 2. copy_fields writes to the newly allocated body, which is different from other's body
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
private let promote_object_read_other
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (other: obj_addr) (addr: hp_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem other (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
      U64.v addr >= U64.v other /\
      U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8 /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures read_word (promote_object minor major obj fp wosize).major_out addr ==
             read_word major addr)
  = let fuel = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let new_addr = alloc_res.obj_out in
    // Step 1: alloc preserves addr (in other's body, other avoids chain)
    AllocLemmas.alloc_spec_read_other major fp wosize other addr;
    assert (read_word new_major addr == read_word major addr);
    // Step 2: copy_fields to new_addr preserves addr
    // Establish: new_addr is a valid obj_addr in PRE-alloc objects
    GC.Gen.AllocProps.alloc_search_obj_in_objects_pre_part1 major fp 0UL fp
      (if wosize = 0 then 1 else wosize) fuel;
    // new_addr ∈ objects(0UL, major) and other ∈ objects(0UL, major)
    let dst_obj : obj_addr = new_addr in
    // other ≠ new_addr (other avoids the chain, new_addr was in the chain)
    GC.Gen.AllocProps.alloc_spec_obj_ne_excl major fp wosize other;
    assert (new_addr <> other);
    // Pre-alloc wosize of new_addr >= wosize
    GC.Gen.AllocProps.alloc_spec_obj_wosize_pre_part1 major fp wosize;
    assert (U64.v (wosize_of_object dst_obj major) >= wosize);
    // Use objects_separated on the ORIGINAL heap (same wosize as precondition)
    if U64.v other < U64.v new_addr then begin
      objects_separated 0UL major other dst_obj;
      // Gives: new_addr > other + wosize_of_object(other, major)*8
      // Combined with addr + 8 <= other + wosize_of_object(other, major)*8:
      // addr + 8 <= new_addr, so addr is below the write range [new_addr, new_addr+wosize*8)
      // copy_fields_preserves_other precond 2: dst_obj + (wosize-1)*8 + 8 <= heap_size
      // From wfh_part1: hd(new_addr) + 8 + wosize_of_object(new_addr, major)*8 <= heap_size
      // Since wosize_of_object(new_addr, major) >= wosize and hd(new_addr) = new_addr - 8:
      // new_addr + wosize_of_object(new_addr, major)*8 <= heap_size, so new_addr + wosize*8 <= heap_size
      hd_address_spec dst_obj;
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize addr
    end else begin
      // other > new_addr: objects_separated gives other > new_addr + wosize_of_object(new_addr, major)*8
      objects_separated 0UL major dst_obj other;
      // Gives: other > new_addr + wosize_of_object(new_addr, major)*8 >= new_addr + wosize*8
      // Since addr >= other: addr >= new_addr + wosize*8, so addr is above the write range
      hd_address_spec dst_obj;
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize addr
    end
#pop-options

/// Helper: promote_object preserves chain_avoids for an excluded object
/// that was already not in the chain.
#push-options "--z3rlimit 160 --fuel 1 --ifuel 0"
private let promote_object_preserves_chain_avoids
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (excl: U64.t)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp excl (heap_size / U64.v mword) = true /\
      U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
      U64.v excl % U64.v mword == 0 /\
      Seq.mem (excl <: obj_addr) (objects zero_addr major) /\
      U64.v (wosize_of_object (excl <: obj_addr) major) >= 1 /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wosize in
       AllocLemmas.chain_avoids res.major_out res.fp_out excl (heap_size / U64.v mword) = true))
  = let fuel = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let new_fp = alloc_res.fp_out in
    let dst = alloc_res.obj_out in
    // Establish obj_out is a valid obj_addr
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = dst in
    // Step 1: alloc preserves chain_avoids for excl
    AllocLemmas.alloc_spec_preserves_chain_avoids_other major fp wosize excl;
    assert (AllocLemmas.chain_avoids new_major new_fp excl fuel = true);
    // Step 2: chain_avoids for dst_obj in new chain
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
    assert (AllocLemmas.chain_avoids new_major new_fp dst_obj fuel = true);
    // Step 3: fl_valid new_major new_fp fuel
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
    assert (AllocLemmas.fl_valid new_major new_fp fuel);
    // Step 4: well_formed_heap_part1 new_major
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    assert (well_formed_heap_part1 new_major);
    // Step 5: promote_object = alloc + copy_fields
    let res = promote_object minor major obj fp wosize in
    // Step 6: prove the quantifier for chain_avoids_transfer_excl2
    // copy_fields writes only to [dst_obj, dst_obj + wosize*8)
    // For any a ∈ objects(new_major), a ≠ excl, a ≠ dst_obj:
    //   a's first field at address a doesn't overlap [dst_obj, dst_obj + wosize*8)
    //   because objects_separated gives disjoint ranges
    //   So read_word res.major_out a == read_word new_major a
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    assert (Seq.mem dst_obj (objects zero_addr new_major));
    assert (U64.v (wosize_of_object dst_obj new_major) >= wosize);
    // Instantiate wfh_part1 at dst_obj
    hd_address_spec dst_obj;
    assert (U64.v (hd_address dst_obj) + 8 + U64.v (wosize_of_object dst_obj new_major) * 8 <= heap_size);
    assert (U64.v dst_obj + wosize * 8 <= heap_size);
    let transfer_helper (a: hp_addr) : Lemma
      (requires U64.v a >= U64.v mword /\
               Seq.mem a (objects zero_addr new_major) /\ a <> excl /\ a <> dst_obj /\
               U64.v (wosize_of_object (a <: obj_addr) new_major) >= 1 /\
               U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size)
      (ensures read_word res.major_out a == read_word new_major a)
    = let ao : obj_addr = a in
      // a ≠ dst_obj, both in objects(new_major) → objects_separated
      // Then copy_fields at [dst_obj, dst_obj+wosize*8) doesn't touch address a
      // First establish dst_obj body fits in heap (for copy_fields_preserves_other precondition)
      assert (U64.v dst_obj + wosize * 8 <= heap_size);
      if U64.v a < U64.v dst_obj then begin
        objects_separated 0UL new_major ao dst_obj;
        // objects_separated gives: dst_obj > a + wz_a*8 where wz_a >= 1
        assert (U64.v dst_obj > U64.v a + U64.v (wosize_of_object_as_wosize ao new_major) * 8);
        assert (U64.v a + 8 <= U64.v dst_obj);
        assert (forall (k:nat). 0 <= k /\ k < wosize ==> U64.v a + 8 <= U64.v dst_obj + k * 8);
        copy_fields_preserves_other minor new_major obj dst_obj 0 wosize ao
      end else begin
        objects_separated 0UL new_major dst_obj ao;
        // objects_separated gives: a > dst_obj + wz_dst*8
        assert (U64.v a > U64.v dst_obj + U64.v (wosize_of_object_as_wosize dst_obj new_major) * 8);
        assert (U64.v (wosize_of_object dst_obj new_major) >= wosize);
        assert (U64.v a >= U64.v dst_obj + wosize * 8 + 8);
        assert (forall (k:nat). 0 <= k /\ k < wosize ==> U64.v dst_obj + k * 8 + 8 <= U64.v a);
        copy_fields_preserves_other minor new_major obj dst_obj 0 wosize ao
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_helper);
    AllocLemmas.chain_avoids_transfer_excl2 new_major res.major_out new_fp excl dst_obj fuel
#pop-options

/// Top-level helper: promote_object preserves a single field read for a previously promoted object.
#push-options "--z3rlimit 160 --fuel 1 --ifuel 0 --split_queries no"
private let promote_object_preserves_one_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0})
  (prev_addr: obj_addr) (j: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem prev_addr (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp prev_addr (heap_size / U64.v mword) = true /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      U64.v prev_addr + j * 8 + 8 <= heap_size /\
      U64.v prev_addr % 8 == 0 /\
      U64.v prev_addr + j * 8 < U64.v prev_addr + U64.v (wosize_of_object prev_addr major) * 8)
    (ensures read_word (promote_object minor major obj fp wz).major_out
                       (U64.uint_to_t (U64.v prev_addr + j * 8)) ==
             read_word major (U64.uint_to_t (U64.v prev_addr + j * 8)))
  = let field_addr : hp_addr = U64.uint_to_t (U64.v prev_addr + j * 8) in
    promote_object_read_other minor major obj fp wz prev_addr field_addr
#pop-options

/// Inductive proof: promote_all_aux preserves field data of all previously
/// promoted objects AND maintains chain_avoids for all promoted addresses.
///
/// Invariant at index idx:
///   - well_formed_heap_part1 major
///   - fl_valid major fp fuel
///   - fl_chain_terminates major fp fuel
///   - For all k < idx: if fwd(live_set[k]) ≠ 0, then fields match minor
///     AND chain_avoids holds for fwd(live_set[k]) in current state
/// Step lemma: one promote_object call preserves the inductive invariant.

/// Helper: explicitly eliminate the `fields_match_minor` quantifier for a given k and j.
/// Takes field_addr as a pre-computed hp_addr to avoid subtyping issues with --split_queries.
/// This helper does NOT use --split_queries, so Z3 can derive dst_fields_valid from scalar bounds.
#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"
private let fields_match_minor_elim
  (minor: minor_state) (major: heap) (fwd: forwarding_map)
  (live_set: seq U64.t) (idx: nat) (k: nat) (j: nat)
  (field_addr: hp_addr)
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
    let new_addr = fwd obj in
    // Step 1: Prove dst_fields_valid from scalar bounds (Z3 needs the forall proved explicitly)
    introduce forall (i:nat). i < wz ==>
      (U64.v new_addr + i * 8 + 8 <= heap_size /\ (U64.v new_addr + i * 8) % 8 == 0)
    with introduce _ ==> _
    with _. ();
    assert (dst_fields_valid new_addr wz)
    // Step 2: Z3 can now instantiate fields_match_minor with k,j using dst_fields_valid
#pop-options

/// Extracted as a non-recursive top-level lemma for deterministic verification.
#push-options "--z3rlimit 400 --fuel 1 --ifuel 1 --z3refresh"
private let promote_step_preserves_invariant
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      (forall (k:nat). k < idx /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz_k = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj) ==>
         (Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr major) /\
          U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
          AllocLemmas.chain_avoids major fp (fwd obj) (heap_size / U64.v mword) = true))))
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fwd' = extend_forwarding fwd obj res.new_addr in
              well_formed_heap_part1 res.major_out /\
              AllocLemmas.fl_valid res.major_out res.fp_out (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates res.major_out res.fp_out (heap_size / U64.v mword) /\
              fields_match_minor minor res.major_out fwd' live_set (idx + 1) /\
              (forall (k:nat). k < idx + 1 /\ k < Seq.length live_set ==>
                (let ok = Seq.index live_set k in
                 let wz_k = minor_wosize minor ok in
                 fwd' ok <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd' ok) ==>
                 (Seq.mem ((fwd' ok) <: obj_addr) (objects zero_addr res.major_out) /\
                  U64.v (wosize_of_object ((fwd' ok) <: obj_addr) res.major_out) >= wz_k /\
                  AllocLemmas.chain_avoids res.major_out res.fp_out (fwd' ok) (heap_size / U64.v mword) = true)))))
  = let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    let res = promote_object minor major obj fp wz in
    let new_addr = res.new_addr in
    let fwd' = extend_forwarding fwd obj new_addr in
    let fuel = heap_size / U64.v mword in
    // Alloc/copy infrastructure lemmas
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    promote_preserves_fields minor major obj fp wz;
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
    chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
    copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    // For each previous k: fields preserved through promote_object (via helper)
    let aux_field (k:nat) : Lemma
      (requires k < idx /\ k < Seq.length live_set /\
               (let prev_obj = Seq.index live_set k in
                let prev_wz = minor_wosize minor prev_obj in
                fwd prev_obj <> 0UL /\ prev_wz > 0 /\ is_val_addr (fwd prev_obj) /\
                Seq.mem ((fwd prev_obj) <: obj_addr) (objects zero_addr major) /\
                U64.v (wosize_of_object ((fwd prev_obj) <: obj_addr) major) >= prev_wz /\
                AllocLemmas.chain_avoids major fp (fwd prev_obj) (heap_size / U64.v mword) = true))
      (ensures (let prev_obj = Seq.index live_set k in
                let prev_wz = minor_wosize minor prev_obj in
                let prev_addr = fwd prev_obj in
                dst_fields_valid prev_addr prev_wz /\
                U64.v prev_addr % 8 == 0 ==>
                (forall (j:nat). j < prev_wz ==>
                  read_word res.major_out (U64.uint_to_t (U64.v prev_addr + j * 8)) ==
                  minor_read_field minor prev_obj j)))
    = let prev_obj = Seq.index live_set k in
      let prev_wz = minor_wosize minor prev_obj in
      let prev_addr : obj_addr = fwd prev_obj in
      if not (U64.v prev_addr % 8 = 0) then ()
      else if not (U64.v prev_addr + (prev_wz - 1) * 8 + 8 <= heap_size) then ()
      else begin
        let aux_j (j:nat) : Lemma
          (requires j < prev_wz /\
                   U64.v prev_addr + j * 8 + 8 <= heap_size /\
                   (U64.v prev_addr + j * 8) % 8 == 0)
          (ensures read_word res.major_out (U64.uint_to_t (U64.v prev_addr + j * 8)) ==
                   minor_read_field minor prev_obj j) =
          let field_addr : hp_addr = U64.uint_to_t (U64.v prev_addr + j * 8) in
          // Instantiate inductive hypothesis (Z3 can't do nested forall with split_queries)
          fields_match_minor_elim minor major fwd live_set idx k j field_addr;
          // Frame: promote_object preserves existing fields
          promote_object_preserves_one_field minor major obj fp wz prev_addr j
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_j)
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_field);
    // chain_avoids for each previous k is preserved (via helper)
    let aux_chain (k:nat) : Lemma
      (requires k < idx /\ k < Seq.length live_set /\
               (let prev_obj = Seq.index live_set k in
                let prev_wz = minor_wosize minor prev_obj in
                fwd prev_obj <> 0UL /\ prev_wz > 0 /\ is_val_addr (fwd prev_obj) /\
                Seq.mem ((fwd prev_obj) <: obj_addr) (objects zero_addr major) /\
                U64.v (wosize_of_object ((fwd prev_obj) <: obj_addr) major) >= prev_wz /\
                AllocLemmas.chain_avoids major fp (fwd prev_obj) (heap_size / U64.v mword) = true))
      (ensures (let prev_obj = Seq.index live_set k in
                AllocLemmas.chain_avoids res.major_out res.fp_out (fwd prev_obj) fuel = true))
    = let prev_obj = Seq.index live_set k in
      promote_object_preserves_chain_avoids minor major obj fp wz (fwd prev_obj)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_chain);
    // chain_avoids for new_addr
    copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    // Explicitly assert each postcondition conjunct to guide Z3
    assert (well_formed_heap_part1 res.major_out);
    assert (AllocLemmas.fl_valid res.major_out res.fp_out fuel);
    assert (AllocLemmas.fl_chain_terminates res.major_out res.fp_out fuel);
    assert (AllocLemmas.chain_avoids res.major_out res.fp_out res.new_addr fuel = true)
#pop-options

/// Inductive proof: promote_all_aux preserves field data of all previously
/// promoted objects AND maintains chain_avoids for all promoted addresses.
///
/// Invariant at index idx:
///   - well_formed_heap_part1 major
///   - fl_valid major fp fuel
///   - fl_chain_terminates major fp fuel
///   - For all k < idx: if fwd(live_set[k]) ≠ 0, then fields match minor
///     AND chain_avoids holds for fwd(live_set[k]) in current state
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec promote_all_aux_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      (forall (k:nat). k < idx /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz_k = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj) ==>
         (Seq.mem ((fwd obj) <: obj_addr) (objects zero_addr major) /\
          U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
          AllocLemmas.chain_avoids major fp (fwd obj) (heap_size / U64.v mword) = true))))
    (ensures
      (let res = promote_all_aux minor major fp live_set fwd idx in
       fields_match_minor minor res.major_final res.fwd_map live_set (Seq.length live_set)))
    (decreases (Seq.length live_set - idx))
  = if idx >= Seq.length live_set then ()
    else begin
      let obj = Seq.index live_set idx in
      let wz = minor_wosize minor obj in
      if wz = 0 then
        promote_all_aux_preserves_fields minor major fp live_set fwd (idx + 1)
      else begin
        let res = promote_object minor major obj fp wz in
        if res.new_addr = 0UL then ()
        else begin
          promote_step_preserves_invariant minor major fp live_set fwd idx;
          let fwd' = extend_forwarding fwd obj res.new_addr in
          promote_all_aux_preserves_fields minor res.major_out res.fp_out live_set fwd' (idx + 1)
        end
      end
    end
#pop-options

let promote_all_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fields_match_minor minor res.major_final res.fwd_map
                                       live_set (Seq.length live_set)))
  = promote_all_aux_preserves_fields minor major fp live_set empty_forwarding 0

/// ---------------------------------------------------------------------------
/// Frame lemma: promote_all_spec preserves body reads for non-promoted objects
/// ---------------------------------------------------------------------------

/// Inductive: promote_all_aux preserves reads in the body of an object
/// that avoids the free chain.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let rec promote_all_aux_read_other
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem other (objects zero_addr major) /\
      AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
      U64.v addr >= U64.v other /\
      U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8)
    (ensures
      (let res = promote_all_aux minor major fp live_set fwd idx in
       read_word res.major_final addr == read_word major addr))
    (decreases (Seq.length live_set - idx))
  = if idx >= Seq.length live_set then ()
    else begin
      let obj = Seq.index live_set idx in
      let wz = minor_wosize minor obj in
      if wz = 0 then
        promote_all_aux_read_other minor major fp live_set fwd (idx + 1) other addr
      else begin
        let res = promote_object minor major obj fp wz in
        if res.new_addr = 0UL then ()
        else begin
          let fuel = heap_size / U64.v mword in
          // promote_object preserves the read at addr (body of other)
          promote_object_read_other minor major obj fp wz other addr;
          assert (read_word res.major_out addr == read_word major addr);
          // Maintain invariants for recursion:
          // wfh_part1
          AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
          let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
          copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj (alloc_res.obj_out <: obj_addr) wz;
          // fl_valid
          AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
          GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
          let dst_obj : obj_addr = alloc_res.obj_out in
          copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
          // fl_chain_terminates
          AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
          copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
          // chain_avoids preserved for other
          promote_object_preserves_chain_avoids minor major obj fp wz other;
          // other still in objects
          promote_object_preserves_objects_part1 minor major obj fp wz;
          // Recurse
          let fwd' = extend_forwarding fwd obj res.new_addr in
          promote_all_aux_read_other minor res.major_out res.fp_out
                                     live_set fwd' (idx + 1) other addr
        end
      end
    end
#pop-options

let promote_all_read_other
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Seq.mem other (objects zero_addr major) /\
                    AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    read_word res.major_final addr == read_word major addr))
  = promote_all_aux_read_other minor major fp live_set empty_forwarding 0 other addr

/// ---------------------------------------------------------------------------
/// promote_all preserves blue_fields_closed
/// ---------------------------------------------------------------------------

/// Base case: well_formed_heap_part2 implies blue_fields_closed
/// (blue_fields_closed is a weakening of part2 — restricted to blue objects)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries always"
private let wfh_part2_implies_blue_fields_closed (g: heap)
  : Lemma (requires well_formed_heap_part1 g /\ well_formed_heap_part2 g)
          (ensures blue_fields_closed g)
  = reveal_opaque (`%blue_fields_closed) blue_fields_closed;
    let aux (src: obj_addr) (j: nat)
      : Lemma (Seq.mem src (objects zero_addr g) /\ is_blue src g /\
               j < U64.v (wosize_of_object src g) /\
               U64.v src + j * 8 + 8 <= heap_size ==>
               (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr g)))
      = if Seq.mem src (objects zero_addr g) && is_blue src g &&
           j < U64.v (wosize_of_object src g) &&
           U64.v src + j * 8 + 8 <= heap_size
        then begin
          let wz = wosize_of_object src g in
          let far : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
          let v = read_word g far in
          if is_pointer v then begin
            hd_address_spec src;
            assert (well_formed_object g src);
            wosize_of_object_bound src g;
            assert (U64.v wz < pow2 54);
            let k : U64.t = U64.uint_to_t j in
            FStar.Math.Lemmas.pow2_lt_compat 61 54;
            assert (U64.v k < U64.v wz);
            assert (U64.v k < pow2 61);
            assert (U64.v wz <= U64.v (wosize_of_object src g));
            FStar.Math.Lemmas.small_mod (j * U64.v mword) (pow2 64);
            assert (U64.v (U64.mul_mod k mword) == j * 8);
            FStar.Math.Lemmas.small_mod (U64.v src + j * 8) (pow2 64);
            assert (U64.v (U64.add_mod src (U64.mul_mod k mword)) == U64.v src + j * 8);
            assert (U64.v (U64.add_mod src (U64.mul_mod k mword)) < heap_size);
            assert (U64.v (U64.add_mod src (U64.mul_mod k mword)) % 8 == 0);
            assert (is_pointer_to v (v <: obj_addr));
            field_read_implies_exists_pointing g src wz k (v <: obj_addr);
            assert (exists_field_pointing_to_unchecked g src wz (v <: obj_addr))
          end else ()
        end else ()
    in
    FStar.Classical.forall_intro_2 aux
#pop-options

/// Helper: alloc_spec preserves blue_fields_closed.
/// After allocation, blue objects' pointer fields still target valid objects.
///
/// Proof argument (documented for future discharge):
/// After alloc_spec, blue objects in heap_out are:
/// 1. Original blue objects from major (minus dst_obj which became white), headers unchanged
/// 2. The remainder (if split), which is new and blue
///
/// For category 1 (src in objects(major), src != dst_obj, src is blue):
///   alloc only modifies: hd(dst_obj), rem_hd, rem_obj (field 0 of remainder), prev_fp (field 0).
///   - hd(dst_obj), rem_hd, rem_obj are all >= hd(dst_obj). For src < dst_obj: field < hd(dst_obj).
///   - For src > dst_obj and src != remainder: src's body above all writes. prev_fp < dst_obj < src.
///   - prev_fp write: if src = prev_fp and j = 0, written value is remainder_fp or next_fp, both in objects(new).
///   - All other fields: read unchanged from major -> by bfc(major) -> in objects(major) <= objects(new).
///
/// For category 2 (remainder):
///   - Field 0 = next_fp (original next in chain). If is_pointer: in objects by fl_valid.
///   - Fields j > 0: addresses were in body of original dst_obj block (which was blue).
///     By bfc(major) for original block: pointer targets in objects(major) <= objects(new_major).
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --z3refresh --split_queries always"
private let rec alloc_search_preserves_bfc
  (g: heap) (head_fp prev_fp cur_fp: U64.t) (wz: nat) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap_part1 g /\
      AllocLemmas.fl_valid g cur_fp fuel /\
      AllocLemmas.fl_chain_terminates g cur_fp fuel /\
      blue_fields_closed g /\
      wz >= 1 /\
      (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).obj_out <> 0UL /\
      (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) /\ is_blue obj g = false ==>
        AllocLemmas.chain_avoids g cur_fp obj fuel = true) /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
        Seq.mem x (objects zero_addr (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)) /\
      (prev_fp <> 0UL ==>
        (prev_fp <> cur_fp /\
         U64.v prev_fp >= U64.v mword /\ U64.v prev_fp < heap_size /\
         U64.v prev_fp % U64.v mword = 0 /\
         Seq.mem prev_fp (objects zero_addr g) /\
         U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
         is_blue (prev_fp <: obj_addr) g)))
    (ensures
      blue_fields_closed (GC.Spec.Allocator.alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out)
    (decreases fuel)
  =
  let open GC.Spec.Allocator in
  if fuel = 0 then ()
  else if cur_fp = 0UL then ()
  else if U64.v cur_fp < U64.v mword then ()
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
    AllocLemmas.fl_valid_gives_wosize g cur_fp fuel;

    if not (is_blue obj g) then
      AllocLemmas.chain_avoids_head_ne g cur_fp (obj <: U64.t) fuel
    else

    if bwz >= wz then begin
      // *** FOUND CASE ***
      let (g', new_rem_fp) = alloc_from_block g obj wz next_fp in
      let heap_out =
        if prev_fp = 0UL then g'
        else if U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                U64.v prev_fp % U64.v mword = 0
        then write_word g' (prev_fp <: hp_addr) new_rem_fp
        else g'
      in
      assert (heap_out == (alloc_search g head_fp prev_fp cur_fp wz fuel).heap_out);

      reveal_opaque (`%blue_fields_closed) blue_fields_closed;

      let bfc_proof (src: obj_addr) (j: nat)
        : Lemma (Seq.mem src (objects zero_addr heap_out) /\ is_blue src heap_out /\
                 j < U64.v (wosize_of_object src heap_out) /\
                 U64.v src + j * 8 + 8 <= heap_size ==>
                 (let v = read_word heap_out (U64.uint_to_t (U64.v src + j * 8)) in
                  is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr heap_out)))
        = if not (Seq.mem src (objects zero_addr heap_out) && is_blue src heap_out &&
                  j < U64.v (wosize_of_object src heap_out) &&
                  U64.v src + j * 8 + 8 <= heap_size)
          then ()
          else begin
            let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
            let v = read_word heap_out field_addr in
            if not (is_pointer v) then ()
            else if Seq.mem src (objects zero_addr g) then begin
              // Case A: src in objects(g) — frame reasoning
              // Step 1: obj is not blue in heap_out → src ≠ obj
              GC.Gen.AllocProps.alloc_from_block_obj_not_blue g obj wz next_fp;
              hd_address_spec obj;
              if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
                hd_address_spec obj;
                if U64.v prev_fp < U64.v obj then
                  objects_separated 0UL g (prev_fp <: obj_addr) obj
                else
                  objects_separated 0UL g obj (prev_fp <: obj_addr);
                // prev_fp and hd(obj) are word-separated (from objects_separated)
                read_write_different g' (prev_fp <: hp_addr) (hd_address obj) new_rem_fp;
                color_of_header_eq obj (write_word g' (prev_fp <: hp_addr) new_rem_fp) g'
              end else ();
              assert (is_blue obj heap_out = false);
              assert (src <> obj);

              // Step 2: Header of src preserved → color/wosize preserved
              hd_address_spec src;
              hd_address_bounds src;
              wosize_of_object_spec src g;
              wosize_of_object_spec obj g;
              if U64.v src < U64.v obj then
                objects_separated 0UL g src obj
              else
                objects_separated 0UL g obj src;
              GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp (hd_address src);
              if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                 U64.v prev_fp % U64.v mword = 0 then begin
                if U64.v src < U64.v prev_fp then
                  objects_separated 0UL g src (prev_fp <: obj_addr)
                else if U64.v src > U64.v prev_fp then
                  objects_separated 0UL g (prev_fp <: obj_addr) src
                else ();  // src = prev_fp: hd(src) = src - 8 ≠ src = prev_fp (write addr)
                read_write_different g' (prev_fp <: hp_addr) (hd_address src) new_rem_fp
              end else ();
              color_of_header_eq src heap_out g;
              assert (is_blue src g);
              wosize_of_object_spec src heap_out;
              assert (j < U64.v (wosize_of_object src g));

              // Step 3: Field value preservation
              if j > 0 || src <> prev_fp ||
                 prev_fp = 0UL ||
                 not (U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                      U64.v prev_fp % U64.v mword = 0) then begin
                // Field NOT overwritten by prev_fp write
                GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp field_addr;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
                  if src <> prev_fp then begin
                    if U64.v src < U64.v prev_fp then
                      objects_separated 0UL g src (prev_fp <: obj_addr)
                    else
                      objects_separated 0UL g (prev_fp <: obj_addr) src
                  end else ();
                  read_write_different g' (prev_fp <: hp_addr) field_addr new_rem_fp
                end else ();
                blue_fields_closed_inst g src j;
                assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                ()
              end
              else begin
                // j = 0 and src = prev_fp: field_addr = src = prev_fp, overwritten
                // v = new_rem_fp (the overwritten value)
                // Need: is_pointer new_rem_fp ==> new_rem_fp ∈ objects(heap_out)
                wfh_part1_obj_bound g obj;
                assert (U64.v obj + bwz * 8 <= heap_size);
                if bwz - wz < 2 then begin
                  // Exact fit: new_rem_fp = next_fp
                  GC.Spec.Allocator.alloc_from_block_exact g obj wz next_fp;
                  // next_fp = read_word g obj (field 0 of obj)
                  // obj is blue, in objects(g), wosize >= 1
                  blue_fields_closed_inst g obj 0;
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                  ()
                end
                else begin
                  // Split: bwz - wz >= 2
                  let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                  if rem_hd_nat >= heap_size then begin
                    // rem_hd OOB: new_rem_fp = next_fp (same as exact)
                    GC.Spec.Allocator.alloc_from_block_split_rem_hd_oob g obj wz next_fp;
                    blue_fields_closed_inst g obj 0;
                    assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                    assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                    ()
                  end
                  else begin
                    let rem_obj_nat = rem_hd_nat + 8 in
                    if rem_obj_nat >= heap_size then begin
                      // rem_obj OOB: new_rem_fp has address >= heap_size → not a pointer
                      GC.Spec.Allocator.alloc_from_block_split_rem_obj_oob g obj wz next_fp;
                      // is_pointer requires U64.v v < heap_size, contradiction
                      assert (U64.v new_rem_fp >= heap_size);
                      ()
                    end
                    else begin
                      // Normal split: new_rem_fp = remainder object address
                      GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
                      // new_rem_fp ∈ objects(g')
                      AllocLemmas.alloc_from_block_rem_in_objects_part1 g obj wz next_fp;
                      // objects(heap_out) == objects(g') via write_body_preserves_objects
                      AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                      wosize_of_object_spec (prev_fp <: obj_addr) g';
                      write_body_preserves_objects g' (prev_fp <: obj_addr)
                        (prev_fp <: hp_addr) new_rem_fp;
                      ()
                    end
                  end
                end
              end
            end
            else begin
              // Case B: src not in objects(g) — must be the remainder from a normal split.
              assert (~(Seq.mem src (objects zero_addr g)));

              // bwz - wz must be >= 2 (otherwise objects unchanged → contradiction)
              if bwz - wz < 2 then begin
                // Exact fit: objects(g') == objects(g), so objects(heap_out) == objects(g)
                // But src ∈ objects(heap_out) and src ∉ objects(g) — contradiction!
                GC.Gen.AllocProps.alloc_from_block_exact_objects_eq_part1 g obj wz next_fp;
                wosize_of_object_spec obj g;
                wfh_part1_obj_bound g obj;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g));
                  AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g'));
                  assert (prev_fp <> obj);
                  objects_separated 0UL g (prev_fp <: obj_addr) obj;
                  objects_separated 0UL g obj (prev_fp <: obj_addr);
                  hd_address_spec (prev_fp <: obj_addr);
                  wosize_of_object_spec (prev_fp <: obj_addr) g;
                  GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp
                    (hd_address (prev_fp <: obj_addr));
                  wosize_of_object_spec (prev_fp <: obj_addr) g';
                  write_body_preserves_objects g' (prev_fp <: obj_addr)
                    (prev_fp <: hp_addr) new_rem_fp
                end else ();
                // objects(heap_out) == objects(g) in all cases → src ∈ objects(g)
                assert (Seq.mem src (objects zero_addr g))
              end
              else begin
                // Split case: bwz - wz >= 2
                // Establish normal split bounds first (needed by alloc_from_block_split_normal)
                wosize_of_object_spec obj g;
                wfh_part1_obj_bound g obj;
                assert (U64.v obj + bwz * 8 <= heap_size);

                // Establish objects(heap_out) = objects(g') via write_body_preserves_objects
                GC.Spec.Allocator.alloc_from_block_split_normal g obj wz next_fp;
                AllocLemmas.alloc_from_block_rem_in_objects_part1 g obj wz next_fp;
                AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then begin
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g));
                  AllocLemmas.alloc_from_block_preserves_objects_part1 g obj wz next_fp;
                  assert (Seq.mem (prev_fp <: obj_addr) (objects zero_addr g'));
                  // Establish wosize(prev_fp, g') == wosize(prev_fp, g) via frame
                  assert (prev_fp <> obj);
                  objects_separated 0UL g (prev_fp <: obj_addr) obj;
                  objects_separated 0UL g obj (prev_fp <: obj_addr);
                  hd_address_spec (prev_fp <: obj_addr);
                  wosize_of_object_spec (prev_fp <: obj_addr) g;
                  GC.Gen.AllocProps.alloc_from_block_read_frame g obj wz next_fp
                    (hd_address (prev_fp <: obj_addr));
                  wosize_of_object_spec (prev_fp <: obj_addr) g';
                  write_body_preserves_objects g' (prev_fp <: obj_addr)
                    (prev_fp <: hp_addr) new_rem_fp
                end else ();

                // src ∈ objects(g') (from objects(heap_out) = objects(g') and hypothesis)
                AllocLemmas.alloc_from_block_objects_backward_part1 g obj wz next_fp src;
                assert (src == new_rem_fp);
                let rem_hd_nat2 = U64.v hd + (1 + wz) * 8 in
                let rem_obj_nat2 = rem_hd_nat2 + 8 in
                assert (rem_hd_nat2 < heap_size);
                assert (rem_obj_nat2 < heap_size);

                let rem_hd2 : hp_addr = U64.uint_to_t rem_hd_nat2 in

                hd_address_spec (src <: obj_addr);
                assert (hd_address (src <: obj_addr) == rem_hd2);

                // Establish wosize of src in heap_out
                GC.Spec.Allocator.alloc_split_normal_read_rem_hd g obj wz next_fp;
                let rem_wz = bwz - wz - 1 in
                if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                   U64.v prev_fp % U64.v mword = 0 then
                  read_write_different g' (prev_fp <: hp_addr) rem_hd2 new_rem_fp
                else ();
                wosize_of_object_spec (src <: obj_addr) heap_out;
                AllocLemmas.make_header_getWosize (U64.uint_to_t rem_wz) blue_bits 0UL;
                assert (U64.v (wosize_of_object (src <: obj_addr) heap_out) = rem_wz);
                assert (j < rem_wz);

                // Handle field j
                if j = 0 then begin
                  GC.Spec.Allocator.alloc_split_normal_read_rem_field g obj wz next_fp;
                  if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                     U64.v prev_fp % U64.v mword = 0 then
                    read_write_different g' (prev_fp <: hp_addr) (src <: hp_addr) new_rem_fp
                  else ();
                  blue_fields_closed_inst g obj 0;
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                  ()
                end
                else begin
                  GC.Spec.Allocator.alloc_split_normal_read_other g obj wz next_fp field_addr;
                  if prev_fp <> 0UL && U64.v prev_fp >= U64.v mword && U64.v prev_fp < heap_size &&
                     U64.v prev_fp % U64.v mword = 0 then
                    read_write_different g' (prev_fp <: hp_addr) field_addr new_rem_fp
                  else ();
                  assert (wz + 1 + j < bwz);
                  blue_fields_closed_inst g obj (wz + 1 + j);
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr g));
                  assert (Seq.mem (v <: obj_addr) (objects zero_addr heap_out));
                  ()
                end
              end
            end
          end
      in
      FStar.Classical.forall_intro_2 bfc_proof
    end
    else begin
      // *** NOT FOUND: advance to next ***
      if U64.v hd + 16 <= heap_size then begin
        AllocLemmas.fl_chain_terminates_elim g cur_fp fuel;
        let chain_blue_next (nobj: obj_addr)
          : Lemma (requires Seq.mem nobj (objects zero_addr g) /\ is_blue nobj g = false)
                  (ensures AllocLemmas.chain_avoids g next_fp nobj (fuel - 1) = true)
          = AllocLemmas.chain_avoids_tail g cur_fp nobj fuel
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires chain_blue_next);
        alloc_search_preserves_bfc g head_fp cur_fp next_fp wz (fuel - 1)
      end else ()
    end
  end
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
private let alloc_spec_preserves_blue_fields_closed
  (major: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed major /\
      wz >= 1 /\
      (GC.Spec.Allocator.alloc_spec major fp wz).obj_out <> 0UL /\
      chain_objects_blue major fp)
    (ensures
      blue_fields_closed (GC.Spec.Allocator.alloc_spec major fp wz).heap_out)
  =
    let fuel = heap_size / U64.v mword in
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
    let chain_avoids_non_blue (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr major) /\ is_blue obj major = false)
              (ensures AllocLemmas.chain_avoids major fp obj fuel = true)
      = reveal_opaque (`%chain_objects_blue) chain_objects_blue
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires chain_avoids_non_blue);
    alloc_search_preserves_bfc major fp 0UL fp wz fuel
#pop-options

/// Helper: promote_object preserves blue_fields_closed.
/// 1. alloc_spec_preserves_blue_fields_closed -> bfc(new_major)
/// 2. alloc_spec_obj_not_blue_part1 -> dst_obj is not blue in new_major
/// 3. copy_fields only writes to [dst_obj, dst_obj+wosize*8), preserving blue object fields
#push-options "--z3rlimit 400 --fuel 1 --ifuel 0 --z3refresh --split_queries always"
private let promote_object_preserves_bfc
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed major /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      blue_fields_closed (promote_object minor major obj fp wosize).major_out)
  = let fuel = heap_size / U64.v mword in
    let res = promote_object minor major obj fp wosize in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let dst : U64.t = alloc_res.obj_out in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = dst in
    // Step 1: alloc preserves bfc and dst_obj is not blue
    alloc_spec_preserves_blue_fields_closed major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_not_blue_part1 major fp wosize;
    // Key properties of alloc
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    // copy_fields preserves objects and wfh_part1
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
    // Step 2: copy_fields preserves bfc
    reveal_opaque (`%blue_fields_closed) blue_fields_closed;
    let bfc_proof (src: obj_addr) (j: nat)
      : Lemma (Seq.mem src (objects zero_addr res.major_out) /\ is_blue src res.major_out /\
               j < U64.v (wosize_of_object src res.major_out) /\
               U64.v src + j * 8 + 8 <= heap_size ==>
               (let v = read_word res.major_out (U64.uint_to_t (U64.v src + j * 8)) in
                is_pointer v ==> Seq.mem (v <: obj_addr) (objects zero_addr res.major_out)))
      = if not (Seq.mem src (objects zero_addr res.major_out) && is_blue src res.major_out &&
                j < U64.v (wosize_of_object src res.major_out) &&
                U64.v src + j * 8 + 8 <= heap_size)
        then ()
        else begin
          let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
          let v = read_word res.major_out field_addr in
          if not (is_pointer v) then ()
          else begin
            hd_address_spec src;
            hd_address_spec dst_obj;
            assert (Seq.mem src (objects zero_addr new_major));
            // Step A: Show src != dst_obj via color contradiction.
            // hd(dst_obj) = dst_obj - 8 < dst_obj = first write position, so header preserved.
            copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address dst_obj);
            GC.Spec.Object.color_of_header_eq dst_obj res.major_out new_major;
            assert (src <> dst_obj);
            // Step B: Prove header of src is preserved by copy_fields.
            // hd(src) = src - 8. For src < dst_obj: src - 8 < dst_obj (below write range).
            // For src > dst_obj: by objects_separated, src > dst_obj + wosize*8,
            // so src - 8 >= dst_obj + wosize*8 (above write range).
            if U64.v src < U64.v dst_obj then
              objects_separated 0UL new_major src dst_obj
            else
              objects_separated 0UL new_major dst_obj src;
            copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address src);
            // Step C: From header preservation, derive wosize and color equality.
            GC.Spec.Object.color_of_header_eq src res.major_out new_major;
            wosize_of_object_spec src new_major;
            wosize_of_object_spec src res.major_out;
            assert (is_blue src new_major);
            assert (j < U64.v (wosize_of_object src new_major));
            // Step D: Now prove field_addr is also preserved by copy_fields.
            // field_addr = src + j*8. For src < dst_obj: field_addr < src + wosize(src)*8 < dst_obj.
            // For src > dst_obj: field_addr >= src > dst_obj + wosize*8.
            copy_fields_preserves_other minor new_major obj dst_obj 0 wosize field_addr;
            assert (read_word res.major_out field_addr == read_word new_major field_addr);
            // Step E: Instantiate bfc of new_major to conclude.
            blue_fields_closed_inst new_major src j
          end
        end
    in
    FStar.Classical.forall_intro_2 bfc_proof
#pop-options

/// Helper: promote_object preserves chain_objects_blue.
/// After alloc_spec + copy_fields, non-blue objects still avoid the chain.
#push-options "--z3rlimit 400 --fuel 1 --ifuel 0 --z3refresh"
private let promote_object_preserves_chain_objects_blue
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      chain_objects_blue (promote_object minor major obj fp wosize).major_out
                         (promote_object minor major obj fp wosize).fp_out)
  = let fuel = heap_size / U64.v mword in
    let res = promote_object minor major obj fp wosize in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    // Unfold promote_object to connect res with alloc_res + copy_fields
    promote_object_success minor major obj fp wosize;
    assert (res.fp_out == alloc_res.fp_out);
    assert (res.major_out == copy_fields minor new_major obj dst_obj 0 wosize);
    // Key properties of alloc
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wosize;
    // copy_fields preserves objects (equality!) and wfh_part1
    copy_fields_preserves_objects_aux minor new_major obj dst_obj 0 wosize;
    assert (objects zero_addr res.major_out == objects zero_addr new_major);
    copy_fields_preserves_wfh_part1 minor new_major obj dst_obj wosize;
    // dst_obj: chain_avoids preserved through copy_fields
    copy_fields_preserves_chain_avoids_self minor new_major obj dst_obj 0 wosize alloc_res.fp_out fuel;
    // For non-blue obj' ≠ dst_obj: transfer chain_avoids through copy_fields
    let proof_for_obj (excl: obj_addr)
      : Lemma (requires Seq.mem excl (objects zero_addr res.major_out) /\
                        is_blue excl res.major_out = false /\
                        excl <> dst_obj)
              (ensures AllocLemmas.chain_avoids res.major_out res.fp_out excl fuel = true)
      = // 1. excl ∈ objects(new_major) (from objects equality)
        assert (Seq.mem excl (objects zero_addr new_major));
        // 2. Prove excl ∈ objects(major) (new objects from alloc are blue → contradiction)
        AllocLemmas.alloc_spec_new_objects_blue_part1 major fp wosize;
        if not (Seq.mem excl (objects zero_addr major)) then begin
          assert (is_blue excl new_major = true);
          // color preserved through copy_fields (excl ≠ dst_obj)
          hd_address_spec excl;
          hd_address_spec dst_obj;
          if U64.v excl < U64.v dst_obj then
            objects_separated 0UL new_major excl dst_obj
          else
            objects_separated 0UL new_major dst_obj excl;
          copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address excl);
          color_of_header_eq excl res.major_out new_major;
          assert (is_blue excl res.major_out = true);
          assert False
        end;
        assert (Seq.mem excl (objects zero_addr major));
        // 3. dst_obj ∈ objects(major) and excl ≠ dst_obj → objects_separated on major
        GC.Gen.AllocProps.alloc_search_obj_in_objects_pre_part1 major fp 0UL fp
          (if wosize = 0 then 1 else wosize) fuel;
        assert (Seq.mem dst_obj (objects zero_addr major));
        GC.Gen.AllocProps.alloc_spec_obj_wosize_pre_part1 major fp wosize;
        assert (U64.v (wosize_of_object dst_obj major) >= wosize);
        // 4. Header of excl preserved through copy_fields (excl ≠ dst_obj)
        hd_address_spec excl;
        hd_address_spec dst_obj;
        if U64.v excl < U64.v dst_obj then
          objects_separated 0UL major excl dst_obj
        else
          objects_separated 0UL major dst_obj excl;
        copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (hd_address excl);
        color_of_header_eq excl res.major_out new_major;
        // 5. Header preserved through alloc → excl non-blue in major
        GC.Gen.AllocProps.alloc_spec_read_header_other_part1 major fp wosize excl;
        color_of_header_eq excl new_major major;
        assert (is_blue excl major = false);
        // 6. chain_objects_blue → chain_avoids(major, fp, excl, fuel)
        reveal_opaque (`%chain_objects_blue) chain_objects_blue;
        assert (AllocLemmas.chain_avoids major fp excl fuel = true);
        // 7. alloc_spec preserves chain_avoids for excl
        AllocLemmas.alloc_spec_preserves_chain_avoids_other major fp wosize excl;
        // 8. Transfer through copy_fields via chain_avoids_transfer_excl2
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
        let read_pres (ao: obj_addr)
          : Lemma (requires Seq.mem ao (objects zero_addr new_major) /\
                            (ao <: U64.t) <> (excl <: U64.t) /\
                            (ao <: U64.t) <> (dst_obj <: U64.t))
                  (ensures U64.v (wosize_of_object ao new_major) >= 1 /\
                           U64.v (hd_address ao) + 16 <= heap_size ==>
                           read_word res.major_out ao == read_word new_major ao)
          = if U64.v (wosize_of_object ao new_major) >= 1 &&
               U64.v (hd_address ao) + 16 <= heap_size then begin
              hd_address_spec ao;
              if U64.v ao < U64.v dst_obj then
                objects_separated 0UL new_major ao dst_obj
              else
                objects_separated 0UL new_major dst_obj ao;
              copy_fields_preserves_other minor new_major obj dst_obj 0 wosize (ao <: hp_addr)
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires read_pres);
        AllocLemmas.chain_avoids_transfer_excl2 new_major res.major_out alloc_res.fp_out excl dst_obj fuel;
        assert (AllocLemmas.chain_avoids res.major_out alloc_res.fp_out excl fuel = true);
        promote_object_success minor major obj fp wosize
    in
    // Combine: for ALL non-blue obj' in objects(res.major_out), chain_avoids holds
    let full_proof (excl: obj_addr)
      : Lemma (requires Seq.mem excl (objects zero_addr res.major_out) /\
                        is_blue excl res.major_out = false)
              (ensures AllocLemmas.chain_avoids res.major_out res.fp_out excl fuel = true)
      = if excl = dst_obj then ()  // from copy_fields_preserves_chain_avoids_self
        else proof_for_obj excl
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires full_proof);
    reveal_opaque (`%chain_objects_blue) chain_objects_blue
#pop-options

/// Inductive proof: promote_all_aux preserves blue_fields_closed.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let rec promote_all_aux_preserves_bfc
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      blue_fields_closed major /\
      chain_objects_blue major fp)
    (ensures
      blue_fields_closed (promote_all_aux minor major fp live_set fwd idx).major_final)
    (decreases (Seq.length live_set - idx))
  = if idx >= Seq.length live_set then begin
      // Base: no more objects to promote, heap unchanged
      assert (promote_all_aux minor major fp live_set fwd idx ==
              { major_final = major; fp_final = fp; fwd_map = fwd })
    end else begin
      let obj = Seq.index live_set idx in
      let wz = minor_wosize minor obj in
      if wz = 0 then
        // Skip: heap unchanged, recurse
        promote_all_aux_preserves_bfc minor major fp live_set fwd (idx + 1)
      else begin
        let res = promote_object minor major obj fp wz in
        if res.new_addr = 0UL then
          // OOM: result is original major, bfc holds by precondition
          ()
        else begin
          let fuel = heap_size / U64.v mword in
          // promote_object preserves bfc
          promote_object_preserves_bfc minor major obj fp wz;
          assert (blue_fields_closed res.major_out);
          // Establish invariants for recursion
          let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
          GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
          let dst_obj : obj_addr = alloc_res.obj_out in
          AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
          GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
          GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
          copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
          assert (well_formed_heap_part1 res.major_out);
          AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
          AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
          chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
          AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
          copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
          copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
          // Recurse (chain_objects_blue preservation is a separate concern)
          promote_object_preserves_chain_objects_blue minor major obj fp wz;
          let fwd' = extend_forwarding fwd obj res.new_addr in
          promote_all_aux_preserves_bfc minor res.major_out res.fp_out live_set fwd' (idx + 1)
        end
      end
    end
#pop-options

/// After promote_all, blue objects' pointer fields target valid objects.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let promote_all_preserves_blue_fields_closed
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp)
          (ensures blue_fields_closed (promote_all_spec minor major fp live_set).major_final)
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    // Base case: well_formed_heap → well_formed_heap_part2 → blue_fields_closed
    wfh_part2_implies_blue_fields_closed major;
    // Inductive case: promote_all_aux preserves blue_fields_closed
    promote_all_aux_preserves_bfc minor major fp live_set empty_forwarding 0
#pop-options

/// Trivial unfold lemma for minor_collect_all_spec
let minor_collect_all_spec_unfold (minor: minor_state) (major: heap)
                                   (fp: U64.t) (roots: seq U64.t)
  : Lemma (let all_objs = minor_objects minor in
           let prom_res = promote_all_spec minor major fp all_objs in
           (minor_collect_all_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fp == prom_res.fp_final)
  = ()
