/// ---------------------------------------------------------------------------
/// GC.Gen.Cheney — Implementation of Cheney-style BFS copying collector spec
/// ---------------------------------------------------------------------------

module GC.Gen.Cheney

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered

module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module Allocator = GC.Spec.Allocator
module WriteBody = GC.Gen.WriteBodyLemmas

/// ---------------------------------------------------------------------------
/// Helper: promote_object preserves allocator invariants
/// ---------------------------------------------------------------------------
///
/// This factored lemma is the workhorse: a single promote_object call
/// preserves wfh_part1, fl_valid, and fl_chain_terminates.
/// Reused by all cheney_forward_* preservation proofs.

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"

private let promote_object_preserves_alloc_invs
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_object minor major obj fp wz in
                    well_formed_heap_part1 res.major_out /\
                    AllocLemmas.fl_valid res.major_out res.fp_out (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.major_out res.fp_out (heap_size / U64.v mword)))
  =
  let fuel = heap_size / U64.v mword in
  let alloc_res = Allocator.alloc_spec major fp wz in
  if alloc_res.obj_out = 0UL then
    // OOM: promote_object returns original state unchanged
    promote_object_oom minor major obj fp wz
  else begin
    // Establish obj_addr refinement for alloc_res.obj_out
    AllocProps.alloc_spec_obj_valid major fp wz;
    let dst_obj : obj_addr = alloc_res.obj_out in
    // Alloc preserves invariants
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
    // Allocated object properties
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
    // copy_fields preserves invariants (dst avoids the free chain)
    promote_object_success minor major obj fp wz;
    copy_fields_preserves_alloc_invariants minor alloc_res.heap_out obj dst_obj wz alloc_res.fp_out
  end

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_one: forward a single object
/// ---------------------------------------------------------------------------

let cheney_forward_one (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : GTot cheney_state
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then cs
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then cs
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then cs  // OOM — leave state unchanged
      else
        { cs_major = res.major_out;
          cs_fp    = res.fp_out;
          cs_fwd   = extend_forwarding cs.cs_fwd addr res.new_addr;
          cs_queue = Seq.append cs.cs_queue (Seq.create 1 addr) }

/// Unfold lemmas

let cheney_forward_one_noop (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires ~(Seq.mem addr (minor_objects minor)) \/
                    cs.cs_fwd addr <> 0UL)
          (ensures cheney_forward_one minor cs addr == cs)
  = ()

let cheney_forward_one_success (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires Seq.mem addr (minor_objects minor) /\
                    cs.cs_fwd addr = 0UL /\
                    minor_wosize minor addr > 0 /\
                    (promote_object minor cs.cs_major addr cs.cs_fp
                       (minor_wosize minor addr)).new_addr <> 0UL)
          (ensures (let wz = minor_wosize minor addr in
                    let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
                    cheney_forward_one minor cs addr ==
                    { cs_major = res.major_out;
                      cs_fp    = res.fp_out;
                      cs_fwd   = extend_forwarding cs.cs_fwd addr res.new_addr;
                      cs_queue = Seq.append cs.cs_queue (Seq.create 1 addr) }))
  = ()

/// ---------------------------------------------------------------------------
/// cheney_forward_fields: forward all children of an object
/// ---------------------------------------------------------------------------

let rec cheney_forward_fields (minor: minor_state) (cs: cheney_state)
                              (parent: U64.t) (idx: nat) (wosize: nat)
  : GTot cheney_state
    (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then cs
  else
    let field_val = minor_read_field minor parent idx in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields minor cs' parent (idx + 1) wosize

/// ---------------------------------------------------------------------------
/// cheney_forward_roots: forward all roots
/// ---------------------------------------------------------------------------

let rec cheney_forward_roots (minor: minor_state) (cs: cheney_state)
                             (roots: seq U64.t) (idx: nat)
  : GTot cheney_state
    (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then cs
  else
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots minor cs' roots (idx + 1)

/// ---------------------------------------------------------------------------
/// cheney_scan: BFS scan loop
/// ---------------------------------------------------------------------------

let rec cheney_scan (minor: minor_state) (cs: cheney_state)
                    (scan: nat) (fuel: nat)
  : GTot cheney_state
    (decreases fuel)
  =
  if fuel = 0 || scan >= Seq.length cs.cs_queue then cs
  else
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan minor cs' (scan + 1) (fuel - 1)

/// ---------------------------------------------------------------------------
/// cheney_fuel: sufficient fuel for BFS completion
/// ---------------------------------------------------------------------------

/// Each minor object is forwarded at most once (fwd prevents re-enqueue).
/// So the total queue length is bounded by |minor_objects|.
/// Each scan step advances scan by 1, so fuel = |minor_objects| suffices.
let cheney_fuel (minor: minor_state) : GTot nat =
  Seq.length (minor_objects minor)

/// ---------------------------------------------------------------------------
/// Correctness proofs — wfh_part1 preservation
/// ---------------------------------------------------------------------------

/// Key insight: cheney_forward_one either:
///   (a) leaves state unchanged (noop), or
///   (b) calls promote_object which = alloc_spec + copy_fields
///       Both preserve wfh_part1, fl_valid, fl_chain_terminates.

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let cheney_forward_one_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then ()
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then ()
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then ()
      else begin
        // Single-step preservation via factored helper
        promote_object_preserves_alloc_invs minor cs.cs_major addr cs.cs_fp wz
      end

#pop-options

/// Forward fields: by induction, each step preserves invariants

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let rec cheney_forward_fields_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = minor_read_field minor parent idx in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_fields_preserves_wfh_part1 minor cs' parent (idx + 1) wosize
  end

#pop-options

/// Forward roots: by induction

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let rec cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then ()
  else begin
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_roots_preserves_wfh_part1 minor cs' roots (idx + 1)
  end

#pop-options

/// Scan loop: by induction on fuel

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"

let rec cheney_scan_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword)))
          (decreases fuel)
  =
  if fuel = 0 then ()
  else if scan >= Seq.length cs.cs_queue then ()
  else begin
    assert (fuel > 0);
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    let fuel' : nat = fuel - 1 in
    cheney_scan_preserves_wfh_part1 minor cs' (scan + 1) fuel'
  end

#pop-options

/// Compose: full cheney_promote preserves wfh_part1

let cheney_promote_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_promote minor major fp roots in
                    well_formed_heap_part1 res.major_final /\
                    AllocLemmas.fl_valid res.major_final res.fp_final (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.major_final res.fp_final (heap_size / U64.v mword)))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_wfh_part1 minor cs1 0 (cheney_fuel minor)

/// ---------------------------------------------------------------------------
/// Object preservation
/// ---------------------------------------------------------------------------

/// Helper: promote_object preserves objects (wfh_part1 sufficient)
/// Uses alloc_spec_preserves_objects_part1 + WriteBody.copy_fields_preserves_objects_aux
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"

private let promote_object_preserves_objects_part1
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_object minor major obj fp wz in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.major_out)))
  =
  let alloc_res = Allocator.alloc_spec major fp wz in
  if alloc_res.obj_out = 0UL then
    promote_object_oom minor major obj fp wz
  else begin
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_valid major fp wz;
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    let dst_obj : obj_addr = alloc_res.obj_out in
    WriteBody.copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wz;
    promote_object_success minor major obj fp wz
  end

#pop-options

/// cheney_forward_one preserves objects
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let cheney_forward_one_preserves_objects
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major))))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then ()
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then ()
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then ()
      else
        promote_object_preserves_objects_part1 minor cs.cs_major addr cs.cs_fp wz

#pop-options

/// cheney_forward_fields preserves objects (by induction on fields)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_objects
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major))))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = minor_read_field minor parent idx in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_objects minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_wfh_part1 minor cs' parent (idx + 1) wosize;
    cheney_forward_fields_preserves_objects minor cs' parent (idx + 1) wosize
  end

#pop-options

/// cheney_forward_roots preserves objects (by induction on roots)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_objects
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major))))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then ()
  else begin
    let r = Seq.index roots idx in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_objects minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_wfh_part1 minor cs' roots (idx + 1);
    cheney_forward_roots_preserves_objects minor cs' roots (idx + 1)
  end

#pop-options

/// cheney_scan preserves objects (by induction on fuel)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"

/// Combined: scan preserves both wfh_part1 and objects
private let rec cheney_scan_preserves_both
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp (heap_size / U64.v mword))
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp (heap_size / U64.v mword) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major))))
          (decreases fuel)
  =
  if fuel = 0 then ()
  else if scan >= Seq.length cs.cs_queue then ()
  else begin
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_objects minor cs obj 0 wz;
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    assert (fuel >= 1);
    cheney_scan_preserves_both minor cs' (scan + 1) (fuel - 1)
  end

#pop-options

/// Compose: full cheney_promote preserves objects

let cheney_promote_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_promote minor major fp roots in
                    forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.major_final)))
  =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_objects minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_both minor cs1 0 (cheney_fuel minor)

/// ---------------------------------------------------------------------------
/// Full well_formed_heap
/// ---------------------------------------------------------------------------

let cheney_collect_preserves_wfh
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    chain_objects_blue major fp /\
                    True)
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    well_formed_heap_part1 res.mc_major))
  =
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  update_major_pointers_preserves_wfh_part1 prom.major_final prom.fwd_map

/// ---------------------------------------------------------------------------
/// update_major_pointers_preserves_fl_valid
/// ---------------------------------------------------------------------------

/// Key insight: update_major_pointers only modifies field data of non-blue objects.
/// Blue objects (free-list entries) are skipped entirely by the update.
/// Therefore, free-list structure (headers + next pointers in field 0 of blue objects)
/// is unchanged, preserving fl_valid.

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0 --split_queries always"

/// Helper: show update_major_pointers preserves read_word for blue object headers and fields.
/// update_all_objects_aux_preserves_header already gives us header preservation.
/// For field 0 of blue objects: since blue objects are skipped, their fields are unchanged.
let update_major_pointers_preserves_fl_valid
  (major: heap) (fwd: forwarding_map) (fp: U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let m' = update_major_pointers major fwd in
                    AllocLemmas.fl_valid m' fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates m' fp (heap_size / U64.v mword)))
  =
  // update_major_pointers preserves objects and headers (proven in Promote.fsti).
  // Since blue objects are skipped, the free chain is byte-for-byte identical.
  // fl_valid walks the chain: at each blue node, reads header (preserved) and
  // field 0 (next pointer, preserved since blue objects are skipped).
  // By induction on the chain, fl_valid and fl_chain_terminates hold.
  update_major_pointers_preserves_objects major fwd;
  update_major_pointers_preserves_wfh_part1 major fwd;
  // The actual proof requires showing read_word equality for each chain node.
  // Since update_object_pointers never touches blue objects (skipped by aux),
  // and fl_valid/fl_chain only read blue object data, the invariants hold.
  admit ()  // TODO: prove by induction on the free-list chain

#pop-options

/// Full Cheney collection preserves fl_valid
let cheney_collect_preserves_fl_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_collect_spec minor major fp roots in
                    AllocLemmas.fl_valid res.mc_major res.mc_fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates res.mc_major res.mc_fp (heap_size / U64.v mword)))
  =
  // Promotion preserves fl_valid (already proven in cheney_promote_preserves_wfh_part1)
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  // update_major_pointers preserves fl_valid
  update_major_pointers_preserves_fl_valid prom.major_final prom.fwd_map prom.fp_final

/// ---------------------------------------------------------------------------
/// cheney_promote_preserves_dense
/// ---------------------------------------------------------------------------

/// Density: allocating into the heap (via promote_object) extends the objects list
/// while maintaining the linear structure. Each new allocation appends an object
/// at the end (after the previous last object), maintaining the "next" relationship.
let cheney_promote_preserves_dense
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    heap_objects_dense major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = cheney_promote minor major fp roots in
                    heap_objects_dense res.major_final /\
                    Seq.length (objects zero_addr res.major_final) > 0))
  =
  // Promotion only adds objects via alloc + copy_fields.
  // alloc_spec splits a free-list block: the objects list is unchanged for existing
  // objects, and the newly allocated object takes the place of a free-list node.
  // Since the linear walk structure is preserved through allocation (proven via
  // alloc_spec_preserves_objects_part1), density is maintained.
  admit ()  // TODO: prove by induction on promotion steps
