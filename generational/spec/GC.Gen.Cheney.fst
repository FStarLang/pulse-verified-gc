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
open GC.Gen.PromoteUpdate
open GC.Gen.Remembered

module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocProps = GC.Gen.AllocProps
module Allocator = GC.Spec.Allocator
module WriteBody = GC.Gen.WriteBodyLemmas
module Object = GC.Spec.Object
module Heap = GC.Spec.Heap
module FreeListShape = GC.Gen.FreeListShape

/// ---------------------------------------------------------------------------
/// Helper: promote_object preserves allocator invariants
/// ---------------------------------------------------------------------------
///
/// This factored lemma is the workhorse: a single promote_object call
/// preserves wfh_part1, fl_valid, and fl_chain_terminates.
/// Reused by all cheney_forward_* preservation proofs.

/// Decrement a fuel counter, carrying the termination witness `r << fuel` in the
/// result type.  The obligation is discharged here in an empty context; proving
/// it at each recursive call site drags the ambient hypotheses of the
/// surrounding preservation lemma into the query, which Z3 4.15.3 cannot
/// handle.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let dec_fuel (fuel: nat{fuel >= 1}) : (r: nat{r == fuel - 1 /\ r << fuel}) =
  fuel - 1
#pop-options

/// `a - p == w * 8` and its consequence `(a - p) % 8 == 0`, in an empty context.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let sub_mod8_of_mul (a p w: nat) : Lemma
  (requires p == a - w * 8)
  (ensures a - p == w * 8 /\ (a - p) % 8 == 0)
  = FStar.Math.Lemmas.multiple_modulo_lemma w 8
#pop-options

/// A sequence with a member is non-empty.  Proved in an empty context: under
/// the enclosing well-formed-heap hypotheses this trivial step diverges.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let mem_nonempty (#a: eqtype) (x: a) (s: Seq.seq a)
  : Lemma (requires Seq.mem x s) (ensures Seq.length s > 0)
  = Seq.mem_index x s
#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let promote_object_preserves_alloc_invs
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = promote_object minor major obj fp wz in
                    well_formed_heap_part1 res.major_out /\
                    AllocLemmas.fl_valid res.major_out res.fp_out heap_words /\
                    AllocLemmas.fl_chain_terminates res.major_out res.fp_out heap_words))
  = promote_object_preserves_alloc_invariants minor major obj fp wz

#pop-options

/// ---------------------------------------------------------------------------
/// cheney_forward_normal: forward a single non-infix object
/// ---------------------------------------------------------------------------

let cheney_forward_normal (minor: minor_state) (cs: cheney_state) (addr: U64.t)
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

/// ---------------------------------------------------------------------------
/// cheney_forward_one: infix-aware forwarding
/// ---------------------------------------------------------------------------

let cheney_forward_one (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  =
  if cs.cs_fwd addr <> 0UL then cs
  else if is_infix_in_minor minor addr then
    let parent = infix_parent minor addr in
    let cs' = cheney_forward_normal minor cs parent in
    if cs'.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      let delta = U64.v addr - U64.v parent in
      { cs' with cs_fwd = extend_forwarding cs'.cs_fwd addr
                             (U64.uint_to_t (U64.v (cs'.cs_fwd parent) + delta)) }
    else cs'
  else
    cheney_forward_normal minor cs addr

/// Unfold lemmas for cheney_forward_normal

let cheney_forward_normal_noop (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_normal_noop_wz0 (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_normal_noop_oom (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_normal_success (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

/// For any y <> addr, cheney_forward_normal on addr leaves cs_fwd y unchanged
let cheney_forward_normal_other_fwd (minor: minor_state) (cs: cheney_state) (addr: U64.t) (y: U64.t)
  = ()

/// Unfold lemmas for cheney_forward_one (infix-aware)

let cheney_forward_one_noop (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_one_normal (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

let cheney_forward_one_infix (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

/// For any y <> addr, the infix case preserves cs_fwd y from the parent forwarding
let cheney_forward_one_infix_fwd (minor: minor_state) (cs: cheney_state) (addr: U64.t) (y: U64.t)
  = ()

/// In the infix case, if the guard passes, the stored value for addr is parent_fwd + delta < heap_size
let cheney_forward_one_infix_bounded (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

/// In the infix case, when the bounded guard fails, cheney_forward_one returns cs'
let cheney_forward_one_infix_guard_fail (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  = ()

/// In the infix case, when the bounded guard passes, the result's cs_fwd is
/// extend_forwarding cs'.cs_fwd addr val, where val = parent_fwd + delta
let cheney_forward_one_infix_guard_pass (minor: minor_state) (cs: cheney_state) (addr: U64.t)
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
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields minor cs' parent (idx + 1) wosize

let cheney_forward_fields_base
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  = ()

let cheney_forward_fields_step
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  = ()

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

let cheney_forward_roots_base
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  = ()

let cheney_forward_roots_step
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  = ()

/// ---------------------------------------------------------------------------
/// cheney_scan: BFS scan loop
/// ---------------------------------------------------------------------------

let rec cheney_scan (minor: minor_state) (cs: cheney_state)
                    (scan: nat) (fuel: nat)
  : GTot cheney_state
    (decreases fuel)
  =
  if fuel < 1 || scan >= Seq.length cs.cs_queue then cs
  else
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_scan minor cs' (scan + 1) (fuel - 1)

let cheney_scan_base
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  = ()

let cheney_scan_step
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  = ()

/// ---------------------------------------------------------------------------
/// cheney_fuel: sufficient fuel for BFS completion
/// ---------------------------------------------------------------------------

/// Each minor object is forwarded at most once (fwd prevents re-enqueue).
/// So the total queue length is bounded by |minor_objects|.
/// Each scan step advances scan by 1, so fuel = |minor_objects| suffices.
let cheney_fuel (minor: minor_state) : GTot nat =
  Seq.length (minor_objects minor)

let cheney_fuel_eq (minor: minor_state)
  = ()

/// ---------------------------------------------------------------------------
/// Correctness proofs — wfh_part1 preservation
/// ---------------------------------------------------------------------------

/// Key insight: cheney_forward_one either:
///   (a) leaves state unchanged (noop), or
///   (b) calls promote_object which = alloc_spec + copy_fields
///       Both preserve wfh_part1, fl_valid, fl_chain_terminates.

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let cheney_forward_normal_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))
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
        promote_object_preserves_alloc_invs minor cs.cs_major addr cs.cs_fp wz
      end

let cheney_forward_one_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  =
  if cs.cs_fwd addr <> 0UL then ()
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_wfh_part1 minor cs parent
    // extend_forwarding doesn't change cs_major/cs_fp
  end
  else
    cheney_forward_normal_preserves_wfh_part1 minor cs addr

#pop-options

/// Forward fields: by induction, each step preserves invariants

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

let rec cheney_forward_fields_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_fields_preserves_wfh_part1 minor cs' parent (idx + 1) wosize
  end

#pop-options

/// Forward roots: by induction

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

let rec cheney_forward_roots_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))
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

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

let rec cheney_scan_preserves_wfh_part1
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words))
          (decreases fuel)
  =
  if fuel < 1 then ()
  else if scan >= Seq.length cs.cs_queue then ()
  else begin
    assert (fuel > 0);
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    let fuel' = dec_fuel fuel in
    cheney_scan_preserves_wfh_part1 minor cs' (scan + 1) fuel'
  end

#pop-options

/// Compose: full cheney_promote preserves wfh_part1

let cheney_promote_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  wf_parts ();
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_wfh_part1 minor cs1 0 (cheney_fuel minor)

/// ---------------------------------------------------------------------------
/// chain_objects_blue preservation through Cheney BFS
/// ---------------------------------------------------------------------------

/// cheney_forward_normal preserves chain_objects_blue.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let cheney_forward_normal_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then ()
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then ()
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then ()
      else
        promote_object_preserves_chain_objects_blue minor cs.cs_major addr cs.cs_fp wz

/// cheney_forward_one preserves chain_objects_blue (infix-aware).
private let cheney_forward_one_preserves_cob
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))
  =
  if cs.cs_fwd addr <> 0UL then ()
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_cob minor cs parent
    // extend_forwarding doesn't change cs_major/cs_fp
  end
  else
    cheney_forward_normal_preserves_cob minor cs addr

#pop-options

/// cheney_forward_fields preserves chain_objects_blue by induction.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_cob
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_cob minor cs field_val;
    cheney_forward_fields_preserves_cob minor cs' parent (idx + 1) wosize
  end

#pop-options

/// cheney_forward_roots preserves chain_objects_blue by induction.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_cob
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then ()
  else begin
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_cob minor cs r;
    cheney_forward_roots_preserves_cob minor cs' roots (idx + 1)
  end

#pop-options

/// cheney_scan preserves chain_objects_blue by induction on fuel.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_scan_preserves_cob
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    chain_objects_blue cs'.cs_major cs'.cs_fp))
          (decreases fuel)
  =
  if fuel < 1 then ()
  else if scan >= Seq.length cs.cs_queue then ()
  else begin
    assert (fuel > 0);
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_cob minor cs obj 0 wz;
    let fuel' = dec_fuel fuel in
    cheney_scan_preserves_cob minor cs' (scan + 1) fuel'
  end

#pop-options

/// Full cheney_promote preserves chain_objects_blue.
let cheney_promote_preserves_cob
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  wf_parts ();
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_cob minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_cob minor cs1 0 (cheney_fuel minor)

/// ---------------------------------------------------------------------------
/// Free-list value-shape preservation through Cheney BFS
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let cheney_forward_normal_preserves_free_list_shape
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    FreeListShape.fp_pointer_or_zero cs.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs.cs_major /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    FreeListShape.fp_pointer_or_zero cs'.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs'.cs_major))
  =
    if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
    then ()
    else
      let wz = minor_wosize minor addr in
      if wz = 0 then ()
      else
        let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
        if res.new_addr = 0UL then ()
        else
          promote_object_preserves_free_list_shape minor cs.cs_major addr cs.cs_fp wz

private let cheney_forward_one_preserves_free_list_shape
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    FreeListShape.fp_pointer_or_zero cs.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs.cs_major /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    FreeListShape.fp_pointer_or_zero cs'.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs'.cs_major))
  =
    if cs.cs_fwd addr <> 0UL then ()
    else if is_infix_in_minor minor addr then begin
      let parent = infix_parent minor addr in
      cheney_forward_normal_preserves_free_list_shape minor cs parent
    end
    else
      cheney_forward_normal_preserves_free_list_shape minor cs addr
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let rec cheney_forward_fields_preserves_free_list_shape
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    FreeListShape.fp_pointer_or_zero cs.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs.cs_major /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    FreeListShape.fp_pointer_or_zero cs'.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs'.cs_major))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
    if idx >= wosize then ()
    else begin
      let field_val = to_minor_offset (minor_read_field minor parent idx) in
      let cs' = cheney_forward_one minor cs field_val in
      cheney_forward_one_preserves_wfh_part1 minor cs field_val;
      cheney_forward_one_preserves_cob minor cs field_val;
      cheney_forward_one_preserves_free_list_shape minor cs field_val;
      cheney_forward_fields_preserves_free_list_shape minor cs' parent (idx + 1) wosize
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let rec cheney_forward_roots_preserves_free_list_shape
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    FreeListShape.fp_pointer_or_zero cs.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs.cs_major /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    FreeListShape.fp_pointer_or_zero cs'.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs'.cs_major))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
    if idx >= Seq.length roots then ()
    else begin
      let r = Seq.index roots idx in
      let cs' = cheney_forward_one minor cs r in
      cheney_forward_one_preserves_wfh_part1 minor cs r;
      cheney_forward_one_preserves_cob minor cs r;
      cheney_forward_one_preserves_free_list_shape minor cs r;
      cheney_forward_roots_preserves_free_list_shape minor cs' roots (idx + 1)
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
private let rec cheney_scan_preserves_free_list_shape
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    FreeListShape.fp_pointer_or_zero cs.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs.cs_major /\
                    chain_objects_blue cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    FreeListShape.fp_pointer_or_zero cs'.cs_fp /\
                    FreeListShape.blue_link_fields_valid cs'.cs_major))
          (decreases fuel)
  =
    if fuel < 1 then ()
    else if scan >= Seq.length cs.cs_queue then ()
    else begin
      assert (fuel > 0);
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = cheney_forward_fields minor cs obj 0 wz in
      cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
      cheney_forward_fields_preserves_cob minor cs obj 0 wz;
      cheney_forward_fields_preserves_free_list_shape minor cs obj 0 wz;
      let fuel' = dec_fuel fuel in
      cheney_scan_preserves_free_list_shape minor cs' (scan + 1) fuel'
    end
#pop-options

let cheney_promote_preserves_free_list_shape
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
    wf_parts ();
    let cs0 : cheney_state =
      { cs_major = major; cs_fp = fp;
        cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
    cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
    cheney_forward_roots_preserves_cob minor cs0 roots 0;
    cheney_forward_roots_preserves_free_list_shape minor cs0 roots 0;
    let cs1 = cheney_forward_roots minor cs0 roots 0 in
    cheney_scan_preserves_free_list_shape minor cs1 0 (cheney_fuel minor)

/// ---------------------------------------------------------------------------
/// Object preservation
/// ---------------------------------------------------------------------------

/// Helper: promote_object preserves objects (wfh_part1 sufficient)
/// Uses alloc_spec_preserves_objects_part1 + WriteBody.copy_fields_preserves_objects_aux
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let promote_object_preserves_objects_part1
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
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
    promote_object_success minor major obj fp wz;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    WriteBody.copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
    let copied = WriteBody.copy_fields minor alloc_res.heap_out obj dst_obj 0 wz in
    let tag = minor_tag minor obj in
    minor_tag_bound minor obj;
    zero_promote_padding_preserves_objects copied dst_obj wz;
    let padded = zero_promote_padding copied dst_obj wz in
    set_promoted_tag_preserves_objects padded dst_obj tag
  end

#pop-options

/// cheney_forward_one preserves objects
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let cheney_forward_normal_preserves_objects
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
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

private let cheney_forward_one_preserves_objects
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major))))
  =
  if cs.cs_fwd addr <> 0UL then ()
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_objects minor cs parent
    // extend_forwarding doesn't change cs_major
  end
  else
    cheney_forward_normal_preserves_objects minor cs addr

#pop-options

/// cheney_forward_fields preserves objects (by induction on fields)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_objects
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major))))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_objects minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_wfh_part1 minor cs' parent (idx + 1) wosize;
    cheney_forward_fields_preserves_objects minor cs' parent (idx + 1) wosize
  end

#pop-options

/// cheney_forward_roots preserves objects (by induction on roots)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_objects
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
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
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

/// Combined: scan preserves both wfh_part1 and objects
private let rec cheney_scan_preserves_both
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    well_formed_heap_part1 cs'.cs_major /\
                    AllocLemmas.fl_valid cs'.cs_major cs'.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs'.cs_major cs'.cs_fp heap_words /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr cs.cs_major) ==>
                      Seq.mem x (objects zero_addr cs'.cs_major))))
          (decreases fuel)
  =
  if fuel < 1 then ()
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
  =
  wf_parts ();
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

/// ---------------------------------------------------------------------------
/// update_major_pointers_preserves_fl_valid
/// ---------------------------------------------------------------------------

/// Key insight: update_major_pointers only modifies field data of non-blue objects.
/// Blue objects (free-list entries) are skipped entirely by the update.
/// Therefore, free-list structure (headers + next pointers in field 0 of blue objects)
/// is unchanged, preserving fl_valid.

/// Recursive helper: by induction on fuel, show fl_valid and fl_chain_terminates
/// are preserved in the updated heap.  The avoids hypothesis generalises
/// chain_objects_blue to arbitrary fuel so that it shrinks in lock-step with
/// fl_valid / fl_chain_terminates.

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec update_preserves_fl_valid_aux
  (major: heap) (fwd: forwarding_map) (fp: U64.t) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp fuel /\
      AllocLemmas.fl_chain_terminates major fp fuel /\
      (forall (obj: obj_addr).
        Seq.mem obj (objects zero_addr major) /\ Object.is_blue obj major = false ==>
        AllocLemmas.chain_avoids major fp obj fuel = true))
    (ensures (let m' = update_major_pointers major fwd in
              AllocLemmas.fl_valid m' fp fuel /\
              AllocLemmas.fl_chain_terminates m' fp fuel))
    (decreases fuel)
  =
  let m' = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;

  // Terminal fp: fl_valid and fl_chain_terminates hold for any heap/fuel
  if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size || U64.v fp % U64.v mword <> 0
  then begin
    (if fuel < 1 then AllocLemmas.fl_valid_zero m' fp
     else AllocLemmas.fl_valid_terminal m' fp fuel);
    AllocLemmas.fl_chain_terminates_terminal m' fp fuel
  end
  // fuel = 0, valid fp: fl_chain_terminates major fp 0 = false (contradicting precondition)
  else if fuel < 1 then
    AllocLemmas.fl_chain_terminates_valid_zero major fp
  else begin
    // Inductive case: fuel > 0, valid fp
    let fp_obj : obj_addr = fp in

    // Step 1: chain_avoids major fp fp fuel = false (by contradiction)
    // If chain_avoids were true, chain_avoids_head_ne would give fp ≠ fp
    (if AllocLemmas.chain_avoids major fp fp fuel then
       AllocLemmas.chain_avoids_head_ne major fp fp fuel
     else ());

    // Step 2: fp is blue (contrapositive of the forall)
    // mem fp objects ∧ ¬is_blue  ⟹  chain_avoids = true  (from forall)
    // But chain_avoids = false  ⟹  contradiction
    // Therefore is_blue = true
    AllocLemmas.fl_valid_gives_mem major fp fuel;

    // Step 3: header preserved → wosize preserved
    update_major_pointers_preserves_header major fwd fp_obj;
    Object.wosize_of_object_spec fp_obj m';
    Object.wosize_of_object_spec fp_obj major;

    // Step 4: wosize >= 1 (from fl_valid)
    AllocLemmas.fl_valid_gives_wosize major fp fuel;

    // Step 5: hd_address arithmetic
    Heap.hd_address_spec fp_obj;
    let hd = Heap.hd_address fp_obj in

    if U64.v hd + 16 > heap_size then begin
      // hd + 16 > heap_size: implication premises false → use intro lemmas
      AllocLemmas.fl_valid_step m' fp fuel;
      AllocLemmas.fl_chain_terminates_step m' fp fuel
    end
    else begin
      // hd + 16 ≤ heap_size

      // Step 6: field 0 preserved (blue object, j = 0)
      update_major_pointers_preserves_blue_field major fwd fp_obj 0;

      // Step 7: Eliminate fl_valid/fl_chain_terminates on major
      AllocLemmas.fl_valid_elim major fp fuel;
      AllocLemmas.fl_chain_terminates_elim major fp fuel;
      let next_fp = Heap.read_word major fp in

      // Step 8: avoids hypothesis for tail (∀ non-blue obj, chain_avoids at next_fp)
      let avoids_next (obj: obj_addr) : Lemma
        (requires Seq.mem obj (objects zero_addr major) /\ Object.is_blue obj major = false)
        (ensures AllocLemmas.chain_avoids major next_fp obj (fuel - 1) = true)
        = AllocLemmas.chain_avoids_tail major fp obj fuel
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires avoids_next);

      // Step 9: recurse on next_fp with fuel - 1
      update_preserves_fl_valid_aux major fwd next_fp (fuel - 1);

      // Step 10: Build fl_valid and fl_chain_terminates on m'
      AllocLemmas.fl_valid_step m' fp fuel;
      AllocLemmas.fl_chain_terminates_step m' fp fuel
    end
  end

#pop-options

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

let update_major_pointers_preserves_fl_valid
  (major: heap) (fwd: forwarding_map) (fp: U64.t)
  =
  let fuel = heap_words in
  reveal_opaque (`%chain_objects_blue) chain_objects_blue;
  update_preserves_fl_valid_aux major fwd fp fuel

#pop-options

/// Full Cheney collection preserves fl_valid
let cheney_collect_preserves_fl_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  // Promotion preserves fl_valid and chain_objects_blue
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  cheney_promote_preserves_cob minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  // update_major_pointers preserves fl_valid
  update_major_pointers_preserves_fl_valid prom.major_final prom.fwd_map prom.fp_final

/// ---------------------------------------------------------------------------
/// cheney_promote_preserves_dense
/// ---------------------------------------------------------------------------

/// Density: allocating into the heap (via promote_object) extends the objects list
/// while maintaining the linear structure. Each new allocation appends an object
/// at the end (after the previous last object), maintaining the "next" relationship.

module Dense = GC.Gen.Cheney.Dense

/// cheney_forward_normal preserves density.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let cheney_forward_normal_preserves_dense
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    heap_objects_dense cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    heap_objects_dense cs'.cs_major))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then ()
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then ()
    else
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then ()
      else
        Dense.promote_object_preserves_dense minor cs.cs_major addr cs.cs_fp wz

/// cheney_forward_one preserves density (infix-aware).
private let cheney_forward_one_preserves_dense
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    heap_objects_dense cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    heap_objects_dense cs'.cs_major))
  =
  if cs.cs_fwd addr <> 0UL then ()
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    cheney_forward_normal_preserves_dense minor cs parent
  end
  else
    cheney_forward_normal_preserves_dense minor cs addr

#pop-options

/// cheney_forward_fields preserves density by induction.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_dense
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    heap_objects_dense cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_fields minor cs parent idx wosize in
                    heap_objects_dense cs'.cs_major))
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    cheney_forward_one_preserves_dense minor cs field_val;
    cheney_forward_fields_preserves_dense minor cs' parent (idx + 1) wosize
  end

#pop-options

/// cheney_forward_roots preserves density by induction.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_dense
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    heap_objects_dense cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_forward_roots minor cs roots idx in
                    heap_objects_dense cs'.cs_major))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then ()
  else begin
    let r = Seq.index roots idx in
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    cheney_forward_one_preserves_dense minor cs r;
    cheney_forward_roots_preserves_dense minor cs' roots (idx + 1)
  end

#pop-options

/// cheney_scan preserves density by induction on fuel.
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_scan_preserves_dense
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part1 cs.cs_major /\
                    heap_objects_dense cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures (let cs' = cheney_scan minor cs scan fuel in
                    heap_objects_dense cs'.cs_major))
          (decreases fuel)
  =
  if fuel < 1 then ()
  else if scan >= Seq.length cs.cs_queue then ()
  else begin
    assert (fuel > 0);
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    cheney_forward_fields_preserves_dense minor cs obj 0 wz;
    let fuel' = dec_fuel fuel in
    cheney_scan_preserves_dense minor cs' (scan + 1) fuel'
  end

#pop-options

/// Full cheney_promote preserves density + objects nonempty.
let cheney_promote_preserves_dense
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  wf_parts ();
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  // Density preservation through forward_roots + scan
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  cheney_forward_roots_preserves_dense minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_dense minor cs1 0 (cheney_fuel minor);
  // Objects nonempty: cheney_promote_preserves_objects shows all originals survive
  cheney_promote_preserves_objects minor major fp roots;
  let res = cheney_promote minor major fp roots in
  // There's at least one object in the original (given by precondition),
  // and preservation gives it in the result.
  let witness : obj_addr = Seq.head (objects zero_addr major) in
  assert (Seq.mem witness (objects zero_addr major));
  assert (Seq.mem witness (objects zero_addr res.major_final));
  mem_nonempty witness (objects zero_addr res.major_final)

/// ---------------------------------------------------------------------------
/// fwd_bounded preservation through Cheney BFS
/// ---------------------------------------------------------------------------

/// cheney_forward_normal preserves fwd_bounded.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let cheney_forward_normal_preserves_fwd_bounded
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_bounded cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures fwd_bounded (cheney_forward_normal minor cs addr).cs_fwd)
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
        AllocProps.alloc_spec_obj_valid cs.cs_major cs.cs_fp wz;
        ()
      end

/// cheney_forward_one preserves fwd_bounded (infix-aware).
/// For infix: derived entry = parent_fwd + delta. Since parent was promoted
/// with full wosize (including the infix), parent_fwd + delta < heap_size.
private let cheney_forward_one_preserves_fwd_bounded
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_bounded cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_bounded (cheney_forward_one minor cs addr).cs_fwd)
  =
  if cs.cs_fwd addr <> 0UL then ()
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_fwd_bounded minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    if cs'.cs_fwd parent <> 0UL then begin
      reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
      let r = cheney_forward_one minor cs addr in
      // Use infix_bounded: if r.cs_fwd addr <> 0, it's < heap_size
      cheney_forward_one_infix_bounded minor cs addr;
      // Use infix_fwd for all y <> addr: r.cs_fwd y == cs'.cs_fwd y (bounded)
      // For y = addr: either 0 (trivially bounded) or < heap_size (by infix_bounded)
      // Also: parent_fwd >= mword, parent % 8 == 0, addr % 8 == 0, so result % 8 == 0
      // and parent_fwd + delta >= parent_fwd >= mword
      let aux (x: U64.t) : Lemma (requires r.cs_fwd x <> 0UL)
                                  (ensures U64.v (r.cs_fwd x) >= U64.v mword /\
                                           U64.v (r.cs_fwd x) < heap_size /\
                                           U64.v (r.cs_fwd x) % U64.v mword == 0) =
        if x = addr then begin
          // r.cs_fwd addr <> 0 → infix_bounded gives value and bound
          let parent_fwd_v = U64.v (cs'.cs_fwd parent) in
          let delta = U64.v addr - U64.v parent in
          assert (U64.v (r.cs_fwd addr) == parent_fwd_v + delta);
          assert (U64.v (r.cs_fwd addr) < heap_size);
          // parent_fwd >= mword from fwd_bounded cs'
          assert (parent_fwd_v >= U64.v mword);
          // delta >= 0, so sum >= mword
          assert (U64.v (r.cs_fwd addr) >= U64.v mword);
          // alignment: parent_fwd % 8 == 0, and delta = wz*8
          assert (parent_fwd_v % U64.v mword == 0);
          // Use the unfold lemma to get U64.v parent == U64.v addr - wz*8
          infix_parent_value minor addr;
          let wz_infix = minor_wosize minor addr in
          assert (U64.v parent == U64.v addr - wz_infix * 8);
          sub_mod8_of_mul (U64.v addr) (U64.v parent) wz_infix;
          assert (delta % 8 == 0);
          assert (delta % U64.v mword == 0);
          // parent_fwd % 8 == 0, delta = wz_infix * 8, so (parent_fwd + delta) % 8 == 0
          FStar.Math.Lemmas.lemma_mod_plus parent_fwd_v wz_infix 8;
          assert ((parent_fwd_v + delta) % U64.v mword == 0);
          assert (U64.v (r.cs_fwd addr) % U64.v mword == 0)
        end else begin
          cheney_forward_one_infix_fwd minor cs addr x
          // r.cs_fwd x == cs'.cs_fwd x, bounded by fwd_bounded cs'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else ()
  end
  else
    cheney_forward_normal_preserves_fwd_bounded minor cs addr

#pop-options

/// Forward fields preserves fwd_bounded
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_fwd_bounded
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires fwd_bounded cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_bounded (cheney_forward_fields minor cs parent idx wosize).cs_fwd)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    cheney_forward_one_preserves_fwd_bounded minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_fwd_bounded minor cs' parent (idx + 1) wosize
  end

#pop-options

/// Forward roots preserves fwd_bounded
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_fwd_bounded
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires fwd_bounded cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_bounded (cheney_forward_roots minor cs roots idx).cs_fwd)
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then ()
  else begin
    let r = Seq.index roots idx in
    cheney_forward_one_preserves_fwd_bounded minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_fwd_bounded minor cs' roots (idx + 1)
  end

#pop-options

/// Scan loop preserves fwd_bounded
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_scan_preserves_fwd_bounded
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires fwd_bounded cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_bounded (cheney_scan minor cs scan fuel).cs_fwd)
          (decreases fuel)
  =
  if fuel < 1 then ()
  else if scan >= Seq.length cs.cs_queue then ()
  else begin
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_fwd_bounded minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    assert (fuel > 0);
    let fuel' = dec_fuel fuel in
    cheney_scan_preserves_fwd_bounded minor cs' (scan + 1) fuel'
  end

#pop-options

/// Full cheney_promote produces a bounded forwarding map
let cheney_promote_fwd_bounded
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  wf_parts ();
  // empty_forwarding maps everything to 0UL, so fwd_bounded trivially holds
  assert (fwd_bounded empty_forwarding);
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_fwd_bounded minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_fwd_bounded minor cs1 0 (cheney_fuel minor)

/// ---------------------------------------------------------------------------
/// fwd_above_zero_addr preservation through Cheney BFS
/// ---------------------------------------------------------------------------

/// cheney_forward_normal preserves fwd_above_zero_addr.
/// New entry comes from alloc_spec, whose result is in objects zero_addr major,
/// hence has value > zero_addr.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let cheney_forward_normal_preserves_fwd_above_zero
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_above_zero_addr cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words)
          (ensures fwd_above_zero_addr (cheney_forward_normal minor cs addr).cs_fwd)
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
        AllocProps.alloc_spec_obj_in_objects_part1 cs.cs_major cs.cs_fp wz;
        let alloc_res = Allocator.alloc_spec cs.cs_major cs.cs_fp wz in
        objects_addresses_gt_start zero_addr alloc_res.heap_out alloc_res.obj_out;
        assert (U64.v res.new_addr > U64.v zero_addr);
        ()
      end

#pop-options

/// cheney_forward_one preserves fwd_above_zero_addr (infix-aware).
/// For infix: value = parent_fwd + delta, where parent_fwd > zero_addr (from IH)
/// and delta >= 0, so sum > zero_addr.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let cheney_forward_one_preserves_fwd_above_zero
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fwd_above_zero_addr cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_above_zero_addr (cheney_forward_one minor cs addr).cs_fwd)
  =
  if cs.cs_fwd addr <> 0UL then ()
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_fwd_above_zero minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    if cs'.cs_fwd parent <> 0UL then begin
      reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
      let r = cheney_forward_one minor cs addr in
      cheney_forward_one_infix_bounded minor cs addr;
      // parent_fwd > zero_addr from fwd_above_zero_addr cs'.cs_fwd
      // delta = addr - parent >= 0, so sum = parent_fwd + delta > zero_addr
      let aux (x: U64.t) : Lemma (requires r.cs_fwd x <> 0UL)
                                  (ensures U64.v (r.cs_fwd x) > U64.v zero_addr) =
        if x = addr then begin
          let parent_fwd_v = U64.v (cs'.cs_fwd parent) in
          let delta = U64.v addr - U64.v parent in
          assert (U64.v (r.cs_fwd addr) == parent_fwd_v + delta);
          assert (parent_fwd_v > U64.v zero_addr);
          assert (U64.v (r.cs_fwd addr) > U64.v zero_addr)
        end else begin
          cheney_forward_one_infix_fwd minor cs addr x
          // r.cs_fwd x == cs'.cs_fwd x, above zero from fwd_above_zero_addr cs'
        end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end else ()
  end
  else
    cheney_forward_normal_preserves_fwd_above_zero minor cs addr

#pop-options

/// Forward fields preserves fwd_above_zero_addr
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_fwd_above_zero
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires fwd_above_zero_addr cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_above_zero_addr (cheney_forward_fields minor cs parent idx wosize).cs_fwd)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    cheney_forward_one_preserves_fwd_above_zero minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_fwd_above_zero minor cs' parent (idx + 1) wosize
  end

#pop-options

/// Forward roots preserves fwd_above_zero_addr
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_fwd_above_zero
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires fwd_above_zero_addr cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_above_zero_addr (cheney_forward_roots minor cs roots idx).cs_fwd)
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then ()
  else begin
    let r = Seq.index roots idx in
    cheney_forward_one_preserves_fwd_above_zero minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_fwd_above_zero minor cs' roots (idx + 1)
  end

#pop-options

/// Scan loop preserves fwd_above_zero_addr
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_scan_preserves_fwd_above_zero
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires fwd_above_zero_addr cs.cs_fwd /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_infix_wf minor)
          (ensures fwd_above_zero_addr (cheney_scan minor cs scan fuel).cs_fwd)
          (decreases fuel)
  =
  if fuel < 1 then ()
  else if scan >= Seq.length cs.cs_queue then ()
  else begin
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_fwd_above_zero minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    assert (fuel > 0);
    let fuel' = dec_fuel fuel in
    cheney_scan_preserves_fwd_above_zero minor cs' (scan + 1) fuel'
  end

#pop-options

/// Full cheney_promote produces a forwarding map with targets above zero_addr
let cheney_promote_fwd_above_zero_addr
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  wf_parts ();
  assert (fwd_above_zero_addr empty_forwarding);
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_fwd_above_zero minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_fwd_above_zero minor cs1 0 (cheney_fuel minor)

/// ---------------------------------------------------------------------------
/// well_formed_heap_part4 preservation through Cheney BFS
/// ---------------------------------------------------------------------------

/// cheney_forward_normal preserves well_formed_heap_part4.
/// New object gets minor_tag (not infix_tag since Seq.mem addr minor_objects).
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let cheney_forward_normal_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_normal minor cs addr).cs_major)
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then ()
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then ()
    else begin
      minor_objects_not_infix minor addr;
      Object.infix_tag_val ();
      promote_object_preserves_wfh_part4 minor cs.cs_major addr cs.cs_fp wz;
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then ()
      else ()
    end

#pop-options

/// cheney_forward_one preserves well_formed_heap_part4 (infix-aware).
/// Infix case: only extends cs_fwd (no heap modification after forwarding parent).
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

private let cheney_forward_one_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_one minor cs addr).cs_major)
  =
  if cs.cs_fwd addr <> 0UL then ()
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    cheney_forward_normal_preserves_wfh_part4 minor cs parent;
    cheney_forward_normal_preserves_wfh_part1 minor cs parent;
    let cs' = cheney_forward_normal minor cs parent in
    // Infix branch only modifies cs_fwd, not cs_major
    ()
  end
  else
    cheney_forward_normal_preserves_wfh_part4 minor cs addr

#pop-options

/// Forward fields preserves well_formed_heap_part4
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_fields_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_fields minor cs parent idx wosize).cs_major)
          (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = to_minor_offset (minor_read_field minor parent idx) in
    cheney_forward_one_preserves_wfh_part4 minor cs field_val;
    cheney_forward_one_preserves_wfh_part1 minor cs field_val;
    let cs' = cheney_forward_one minor cs field_val in
    cheney_forward_fields_preserves_wfh_part4 minor cs' parent (idx + 1) wosize
  end

#pop-options

/// Forward roots preserves well_formed_heap_part4
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

private let rec cheney_forward_roots_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_forward_roots minor cs roots idx).cs_major)
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then ()
  else begin
    let r = Seq.index roots idx in
    cheney_forward_one_preserves_wfh_part4 minor cs r;
    cheney_forward_one_preserves_wfh_part1 minor cs r;
    let cs' = cheney_forward_one minor cs r in
    cheney_forward_roots_preserves_wfh_part4 minor cs' roots (idx + 1)
  end

#pop-options

/// Scan loop preserves well_formed_heap_part4
#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

private let rec cheney_scan_preserves_wfh_part4
  (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires well_formed_heap_part4 cs.cs_major /\
                    well_formed_heap_part1 cs.cs_major /\
                    AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
                    AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
                    minor_wf minor /\
                    minor_infix_wf minor)
          (ensures well_formed_heap_part4 (cheney_scan minor cs scan fuel).cs_major)
          (decreases fuel)
  =
  if fuel < 1 then ()
  else if scan >= Seq.length cs.cs_queue then ()
  else begin
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = cheney_forward_fields minor cs obj 0 wz in
    cheney_forward_fields_preserves_wfh_part4 minor cs obj 0 wz;
    cheney_forward_fields_preserves_wfh_part1 minor cs obj 0 wz;
    assert (fuel > 0);
    let fuel' = dec_fuel fuel in
    cheney_scan_preserves_wfh_part4 minor cs' (scan + 1) fuel'
  end

#pop-options

/// Full cheney_promote preserves well_formed_heap_part4
let cheney_promote_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  =
  wf_parts ();
  let cs0 : cheney_state =
    { cs_major = major; cs_fp = fp;
      cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
  cheney_forward_roots_preserves_wfh_part4 minor cs0 roots 0;
  cheney_forward_roots_preserves_wfh_part1 minor cs0 roots 0;
  let cs1 = cheney_forward_roots minor cs0 roots 0 in
  cheney_scan_preserves_wfh_part4 minor cs1 0 (cheney_fuel minor)
