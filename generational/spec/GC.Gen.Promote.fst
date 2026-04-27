/// ---------------------------------------------------------------------------
/// GC.Gen.Promote — Implementation of minor→major promotion spec
/// ---------------------------------------------------------------------------

module GC.Gen.Promote

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap

/// ---------------------------------------------------------------------------
/// Promote a single object: copy fields from minor to major
/// ---------------------------------------------------------------------------

/// Copy `n` fields (words) from minor heap at `src_obj + i*8` to major heap at `dst + i*8`
let rec copy_fields (minor: minor_state) (major: heap) 
                    (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : GTot heap (decreases (n - i)) =
  if i >= n then major
  else
    let field_val = minor_read_field minor src_obj (i + 1) in
    let dst_offset = U64.v dst_obj + (i + 1) * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then major
    else
      let major' = write_word major (U64.uint_to_t dst_offset) field_val in
      copy_fields minor major' src_obj dst_obj (i + 1) n

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

let promote_all_spec (minor: minor_state) (major: heap)
                     (fp: U64.t) (live_set: seq U64.t)
  : GTot promote_all_result =
  promote_all_aux minor major fp live_set empty_forwarding 0

/// ---------------------------------------------------------------------------
/// Pointer update: rewrite minor-heap pointers in major heap
/// ---------------------------------------------------------------------------

/// Check if a value looks like a minor-heap pointer
let is_minor_pointer (v: U64.t) : bool =
  U64.v v >= 8 && U64.v v < minor_heap_size && U64.v v % 8 = 0

/// Update pointers in a single major-heap object
let rec update_object_pointers (major: heap) (obj: U64.t) (wosize: nat)
                               (fwd: forwarding_map) (i: nat)
  : GTot heap (decreases (wosize - i)) =
  if i >= wosize then major
  else
    let field_offset = U64.v obj + (i + 1) * 8 in
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

/// Update all pointers in the major heap
/// Walk all objects and rewrite fields that point into the minor heap
let update_major_pointers (major: heap) (fwd: forwarding_map) : GTot heap =
  // For now, simplified: walk objects and update each
  // Full implementation would use GC.Spec.Fields.objects to enumerate
  major  // Placeholder — will implement with proper object walk

/// ---------------------------------------------------------------------------
/// Full minor collection
/// ---------------------------------------------------------------------------

let minor_collect_spec (minor: minor_state) (major: heap)
                       (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result =
  // For now: promote ALL minor objects (conservative — treats everything as live)
  // A more precise version would compute reachability from roots
  let live_set = minor_objects minor in
  let prom_res = promote_all_spec minor major fp live_set in
  let updated_major = update_major_pointers prom_res.major_final prom_res.fwd_map in
  { mc_major = updated_major;
    mc_fp = prom_res.fp_final;
    mc_minor = minor_reset minor }

/// ---------------------------------------------------------------------------
/// Correctness lemmas (placeholders)
/// ---------------------------------------------------------------------------

let minor_collect_preserves_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t)
  : Lemma (requires
             minor_wf minor /\
             Seq.mem obj (minor_objects minor))
          (ensures
             (let res = minor_collect_spec minor major fp roots in
              True)) =
  ()

let promote_preserves_fields
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             U64.v obj >= 8 /\ U64.v obj < minor_heap_size)
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              (forall (i:nat). i >= 1 /\ i <= wosize ==>
                True))) =
  ()
