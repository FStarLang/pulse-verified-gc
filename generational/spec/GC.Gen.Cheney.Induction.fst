module GC.Gen.Cheney.Induction

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Cheney

module AllocLemmas = GC.Spec.Allocator.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let cheney_promote_is_run minor major fp roots = ()

/// ---------------------------------------------------------------------------
/// Invariants of the Cheney state
/// ---------------------------------------------------------------------------

/// `one` plus the allocator's invariant.
private let one_alloc_ok (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma (requires alloc_ok cs.cs_major cs.cs_fp)
          (ensures (let cs' = cheney_forward_one minor cs addr in
                    alloc_ok cs'.cs_major cs'.cs_fp))
  = let normal (a: U64.t)
      : Lemma (let cs' = cheney_forward_normal minor cs a in
               alloc_ok cs'.cs_major cs'.cs_fp)
      = if not (Seq.mem a (minor_objects minor)) || cs.cs_fwd a <> 0UL
        then cheney_forward_normal_noop minor cs a
        else begin
          let wz = minor_wosize minor a in
          if wz = 0 then cheney_forward_normal_noop_wz0 minor cs a
          else if (promote_object minor cs.cs_major a cs.cs_fp wz).new_addr = 0UL
          then cheney_forward_normal_noop_oom minor cs a
          else begin
            cheney_forward_normal_success minor cs a;
            promote_object_preserves_alloc_invariants minor cs.cs_major a cs.cs_fp wz
          end
        end
    in
    if cs.cs_fwd addr <> 0UL ||
       (not (Seq.mem addr (minor_objects minor)) && not (is_infix_in_minor minor addr))
    then cheney_forward_one_noop minor cs addr
    else if not (is_infix_in_minor minor addr) then begin
      cheney_forward_one_normal minor cs addr;
      normal addr
    end
    else begin
      let parent = infix_parent minor addr in
      let cs' = cheney_forward_normal minor cs parent in
      normal parent;
      if cs'.cs_fwd parent <> 0UL &&
         U64.v addr >= U64.v parent &&
         U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
      then cheney_forward_one_infix_guard_pass minor cs addr
      else cheney_forward_one_infix_guard_fail minor cs addr
    end

#push-options "--fuel 1"
let rec cheney_forward_fields_induction_plain (minor: minor_state) (inv: cheney_state -> prop)
  (one: one_keeps_plain minor inv)
  (cs: cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires inv cs)
          (ensures inv (cheney_forward_fields minor cs parent idx wosize))
          (decreases (if idx < wosize then wosize - idx else 0))
  = if idx >= wosize then cheney_forward_fields_base minor cs parent idx wosize
    else begin
      cheney_forward_fields_step minor cs parent idx wosize;
      let field_val = to_minor_offset (minor_read_field minor parent idx) in
      one cs field_val;
      cheney_forward_fields_induction_plain minor inv one (cheney_forward_one minor cs field_val) parent (idx + 1) wosize
    end

let rec cheney_forward_roots_induction_plain (minor: minor_state) (inv: cheney_state -> prop)
  (one: one_keeps_plain minor inv)
  (cs: cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires inv cs)
          (ensures inv (cheney_forward_roots minor cs roots idx))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  = if idx >= Seq.length roots then cheney_forward_roots_base minor cs roots idx
    else begin
      cheney_forward_roots_step minor cs roots idx;
      let r = Seq.index roots idx in
      one cs r;
      cheney_forward_roots_induction_plain minor inv one (cheney_forward_one minor cs r) roots (idx + 1)
    end

let rec cheney_scan_induction_plain (minor: minor_state) (inv: cheney_state -> prop)
  (one: one_keeps_plain minor inv)
  (cs: cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires inv cs)
          (ensures inv (cheney_scan minor cs scan fuel))
          (decreases fuel)
  = if fuel = 0 || scan >= Seq.length cs.cs_queue then cheney_scan_base minor cs scan fuel
    else begin
      cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_scan_wosize minor obj in
      cheney_forward_fields_induction_plain minor inv one cs obj 0 wz;
      cheney_scan_induction_plain minor inv one (cheney_forward_fields minor cs obj 0 wz) (scan + 1) (fuel - 1)
    end
#pop-options

let cheney_promote_induction_plain minor inv one major fp roots =
  let cs0 = cheney_init major fp in
  cheney_forward_roots_induction_plain minor inv one cs0 roots 0;
  cheney_scan_induction_plain minor inv one (cheney_forward_roots minor cs0 roots 0) 0 (cheney_fuel minor)

/// `inv` with the allocator's invariant.
private let with_alloc (inv: cheney_state -> prop) (cs: cheney_state) : prop =
  alloc_ok cs.cs_major cs.cs_fp /\ inv cs

private let one_with_alloc (minor: minor_state) (inv: cheney_state -> prop) (one: one_keeps minor inv)
  : one_keeps_plain minor (with_alloc inv)
  = fun cs addr -> one_alloc_ok minor cs addr; one cs addr

let cheney_forward_fields_induction minor inv one cs parent idx wosize =
  cheney_forward_fields_induction_plain minor (with_alloc inv) (one_with_alloc minor inv one) cs parent idx wosize

let cheney_forward_roots_induction minor inv one cs roots idx =
  cheney_forward_roots_induction_plain minor (with_alloc inv) (one_with_alloc minor inv one) cs roots idx

let cheney_scan_induction minor inv one cs scan fuel =
  cheney_scan_induction_plain minor (with_alloc inv) (one_with_alloc minor inv one) cs scan fuel

let cheney_promote_induction minor inv one major fp roots =
  cheney_promote_induction_plain minor (with_alloc inv) (one_with_alloc minor inv one) major fp roots

/// ---------------------------------------------------------------------------
/// The allocator's invariant
/// ---------------------------------------------------------------------------

private let trivial_inv (cs: cheney_state) : prop = True

private let trivial_one (minor: minor_state) : one_keeps minor trivial_inv =
  fun _ _ -> ()

let cheney_forward_normal_preserves_wfh_part1 minor cs addr =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then cheney_forward_normal_noop minor cs addr
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then cheney_forward_normal_noop_wz0 minor cs addr
    else if (promote_object minor cs.cs_major addr cs.cs_fp wz).new_addr = 0UL
    then cheney_forward_normal_noop_oom minor cs addr
    else begin
      cheney_forward_normal_success minor cs addr;
      promote_object_preserves_alloc_invariants minor cs.cs_major addr cs.cs_fp wz
    end
  end

let cheney_forward_one_preserves_wfh_part1 minor cs addr =
  one_alloc_ok minor cs addr

let cheney_forward_fields_preserves_wfh_part1 minor cs parent idx wosize =
  cheney_forward_fields_induction minor trivial_inv (trivial_one minor) cs parent idx wosize

let cheney_forward_roots_preserves_wfh_part1 minor cs roots idx =
  cheney_forward_roots_induction minor trivial_inv (trivial_one minor) cs roots idx

let cheney_scan_preserves_wfh_part1 minor cs scan fuel =
  cheney_scan_induction minor trivial_inv (trivial_one minor) cs scan fuel

/// ---------------------------------------------------------------------------
/// Invariants of the major heap and free pointer
/// ---------------------------------------------------------------------------

/// A nursery object's wosize is a header field, so it is below `2^54`.
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

let cheney_forward_normal_keeps minor p step cs addr =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then cheney_forward_normal_noop minor cs addr
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then cheney_forward_normal_noop_wz0 minor cs addr
    else if (promote_object minor cs.cs_major addr cs.cs_fp wz).new_addr = 0UL
    then cheney_forward_normal_noop_oom minor cs addr
    else begin
      cheney_forward_normal_success minor cs addr;
      promote_object_preserves_alloc_invariants minor cs.cs_major addr cs.cs_fp wz;
      minor_wosize_bound minor addr;
      step cs.cs_major cs.cs_fp addr wz
    end
  end

let cheney_forward_one_keeps minor p step cs addr =
  if cs.cs_fwd addr <> 0UL ||
     (not (Seq.mem addr (minor_objects minor)) && not (is_infix_in_minor minor addr))
  then cheney_forward_one_noop minor cs addr
  else if not (is_infix_in_minor minor addr) then begin
    cheney_forward_one_normal minor cs addr;
    cheney_forward_normal_keeps minor p step cs addr
  end
  else begin
    let parent = infix_parent minor addr in
    let cs' = cheney_forward_normal minor cs parent in
    cheney_forward_normal_keeps minor p step cs parent;
    if cs'.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then cheney_forward_one_infix_guard_pass minor cs addr
    else cheney_forward_one_infix_guard_fail minor cs addr
  end

private let heap_one (minor: minor_state) (p: heap -> U64.t -> prop) (step: promote_keeps minor p)
  : one_keeps minor (heap_inv p)
  = fun cs addr -> cheney_forward_one_keeps minor p step cs addr

let cheney_forward_fields_keeps minor p step cs parent idx wosize =
  cheney_forward_fields_induction minor (heap_inv p) (heap_one minor p step) cs parent idx wosize

let cheney_forward_roots_keeps minor p step cs roots idx =
  cheney_forward_roots_induction minor (heap_inv p) (heap_one minor p step) cs roots idx

let cheney_scan_keeps minor p step cs scan fuel =
  cheney_scan_induction minor (heap_inv p) (heap_one minor p step) cs scan fuel

let cheney_promote_keeps minor p step major fp roots =
  cheney_promote_induction minor (heap_inv p) (heap_one minor p step) major fp roots
