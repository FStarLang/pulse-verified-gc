/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyFlComplete - a minor collection keeps the free list complete
/// ---------------------------------------------------------------------------
///
/// A minor collection changes the major heap in two phases: Cheney promotion
/// (`cheney_promote`, one `promote_object` per surviving nursery object) and
/// the pointer rewrite that follows (`update_major_pointers`).  Each keeps
/// `fl_complete` -- `GC.Gen.AllocExact.promote_object_preserves_fl_complete`
/// and `update_major_pointers_preserves_fl_complete` -- and this module
/// carries the first through the Cheney traversal, rung by rung, in the same
/// shape as the `chain_objects_blue` ladder in `GC.Gen.Cheney`.

module GC.Gen.CheneyFlComplete

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas
module FL = GC.Spec.FreeList
module AE = GC.Gen.AllocExact

/// What every rung needs of the major heap, and keeps.
let fl_inv (cs: cheney_state) : prop =
  well_formed_heap_part1 cs.cs_major /\
  AllocLemmas.fl_valid cs.cs_major cs.cs_fp heap_words /\
  AllocLemmas.fl_chain_terminates cs.cs_major cs.cs_fp heap_words /\
  FL.fl_complete cs.cs_major cs.cs_fp

private let minor_wosize_bound (minor: minor_state) (obj: U64.t)
  : Lemma (minor_wosize minor obj < pow2 54)
  = if U64.v obj >= 8 && U64.v obj < minor_heap_size then begin
      let hdr_addr = U64.v obj - 8 in
      if hdr_addr + 8 <= minor_heap_size && hdr_addr % 8 = 0 then begin
        let hdr = minor_read_word minor.data (U64.uint_to_t hdr_addr) in
        FStar.UInt.shift_right_value_lemma #64 (U64.v hdr) 10;
        FStar.Math.Lemmas.lemma_div_lt_nat (U64.v hdr) 64 10
      end
    end

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
private let forward_normal_keeps (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fl_inv cs)
          (ensures (let cs' = cheney_forward_normal minor cs addr in
                    FL.fl_complete cs'.cs_major cs'.cs_fp))
  = if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
    then cheney_forward_normal_noop minor cs addr
    else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then cheney_forward_normal_noop_wz0 minor cs addr
      else if (promote_object minor cs.cs_major addr cs.cs_fp wz).new_addr = 0UL
      then cheney_forward_normal_noop_oom minor cs addr
      else begin
        cheney_forward_normal_success minor cs addr;
        minor_wosize_bound minor addr;
        AE.promote_object_preserves_fl_complete minor cs.cs_major addr cs.cs_fp wz
      end
    end

private let forward_one_keeps (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires fl_inv cs)
          (ensures fl_inv (cheney_forward_one minor cs addr))
  = cheney_forward_one_preserves_wfh_part1 minor cs addr;
    if cs.cs_fwd addr <> 0UL ||
       (not (Seq.mem addr (minor_objects minor)) && not (is_infix_in_minor minor addr))
    then cheney_forward_one_noop minor cs addr
    else if not (is_infix_in_minor minor addr) then begin
      cheney_forward_one_normal minor cs addr;
      forward_normal_keeps minor cs addr
    end
    else begin
      let parent = infix_parent minor addr in
      let cs' = cheney_forward_normal minor cs parent in
      forward_normal_keeps minor cs parent;
      if cs'.cs_fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then cheney_forward_one_infix_guard_pass minor cs addr
      else cheney_forward_one_infix_guard_fail minor cs addr
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec forward_fields_keeps (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires fl_inv cs)
          (ensures fl_inv (cheney_forward_fields minor cs parent idx wosize))
          (decreases (if idx < wosize then wosize - idx else 0))
  = if idx >= wosize then cheney_forward_fields_base minor cs parent idx wosize
    else begin
      cheney_forward_fields_step minor cs parent idx wosize;
      let field_val = to_minor_offset (minor_read_field minor parent idx) in
      forward_one_keeps minor cs field_val;
      forward_fields_keeps minor (cheney_forward_one minor cs field_val) parent (idx + 1) wosize
    end

private let rec forward_roots_keeps (minor: minor_state) (cs: cheney_state)
  (roots: seq U64.t) (idx: nat)
  : Lemma (requires fl_inv cs)
          (ensures fl_inv (cheney_forward_roots minor cs roots idx))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  = if idx >= Seq.length roots then cheney_forward_roots_base minor cs roots idx
    else begin
      cheney_forward_roots_step minor cs roots idx;
      let r = Seq.index roots idx in
      forward_one_keeps minor cs r;
      forward_roots_keeps minor (cheney_forward_one minor cs r) roots (idx + 1)
    end

private let rec scan_keeps (minor: minor_state) (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires fl_inv cs)
          (ensures fl_inv (cheney_scan minor cs scan fuel))
          (decreases fuel)
  = if fuel = 0 || scan >= Seq.length cs.cs_queue then cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_scan_wosize minor obj in
      forward_fields_keeps minor cs obj 0 wz;
      scan_keeps minor (cheney_forward_fields minor cs obj 0 wz) (scan + 1) (fuel - 1)
    end
#pop-options

/// **Cheney promotion keeps the free list complete.**
let cheney_promote_preserves_fl_complete
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FL.fl_complete major fp)
          (ensures (let prom = cheney_promote minor major fp roots in
                    FL.fl_complete prom.major_final prom.fp_final))
  = let cs0 : cheney_state =
      { cs_major = major; cs_fp = fp; cs_fwd = empty_forwarding; cs_queue = Seq.empty } in
    forward_roots_keeps minor cs0 roots 0;
    scan_keeps minor (cheney_forward_roots minor cs0 roots 0) 0 (cheney_fuel minor)
