/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Follow - what the minor collection reads, and only that
/// ---------------------------------------------------------------------------
///
/// Design doc §12 (G38(b), G39).  akhil's minor collection assumes two
/// things of the whole nursery:
///
///   * `minor_infix_wf`: every nursery word whose tag is the infix tag is
///     the infix header of a closure.  An ordinary field (the int 124 is the
///     word 249) breaks it, though the collection never reads such a word as
///     a header: it reads the word below an address only when it follows a
///     pointer to that address.
///   * `minor_major_fields_not_free`: every major pointer in a nursery field
///     is itself a block in use.  An infix pointer into a major closure (a
///     young record holding one of a `let rec`'s functions) breaks it,
///     though the collection only copies such a pointer, and a copy needs
///     only what the heap's well-formedness asks of a field: the block it
///     resolves to is in use, and its infix address is well formed.
///
/// This module states the weaker conditions, at what is followed:
///
///   * `infix_at`: akhil's infix conditions at one address;
///   * `follow_ok`: an address read as infix satisfies them;
///   * `fields_follow`: every nursery field value is `follow_ok`;
///   * `roots_follow`: every root is `follow_ok`;
///   * `entries_follow`: every infix address the forwarding map holds is
///     `follow_ok` (the loop's own invariant, kept because only followed
///     addresses are forwarded);
///   * `major_targets`: every major pointer in a nursery field resolves to
///     a block in use, with a well-formed infix address;
///
/// and that akhil's conditions imply them.

module GC.Spec.Pages.Promote.Follow

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Infix addresses
/// ---------------------------------------------------------------------------

/// akhil's infix conditions (`minor_infix_wf`) at one address.
let infix_at (minor: minor_state) (addr: U64.t) : prop =
  let wz = minor_wosize minor addr in
  let parent = infix_parent minor addr in
  wz >= 2 /\
  wz * 8 <= U64.v addr - 8 /\
  U64.v parent >= 8 /\
  U64.v parent % 8 == 0 /\
  Seq.mem parent (minor_objects minor) /\
  minor_tag minor parent == 247 /\
  U64.v addr - U64.v parent < minor_wosize minor parent * 8

/// An address the collection follows: if its header word reads as infix,
/// it is an infix address of a closure.
let follow_ok (minor: minor_state) (addr: U64.t) : prop =
  is_infix_in_minor minor addr ==> infix_at minor addr

/// akhil's `infix_parent_value`, at one address.
#push-options "--z3rlimit 20"
let infix_parent_value_at (minor: minor_state) (addr: U64.t)
  : Lemma (requires is_infix_in_minor minor addr /\ infix_at minor addr)
          (ensures U64.v (infix_parent minor addr) == U64.v addr - minor_wosize minor addr * 8)
  = let off = minor_wosize minor addr * 8 in
    assert (off <= U64.v addr);
    assert (infix_parent minor addr == U64.uint_to_t (U64.v addr - off))
#pop-options

/// The parent of a followed infix address is a nursery object, not infix,
/// and not the address.
let parent_facts_at (minor: minor_state) (addr: U64.t)
  : Lemma (requires minor_wf minor /\ is_infix_in_minor minor addr /\ infix_at minor addr)
          (ensures (let p = infix_parent minor addr in
                    Seq.mem p (minor_objects minor) /\ ~(is_infix_in_minor minor p) /\ p <> addr))
  = minor_objects_not_infix minor (infix_parent minor addr)

/// ---------------------------------------------------------------------------
/// What is followed
/// ---------------------------------------------------------------------------

/// Every value a nursery object's scanned fields hold is followed safely.
[@@"opaque_to_smt"]
let fields_follow (minor: minor_state) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj ==>
    follow_ok minor (to_minor_offset (minor_read_field minor obj j))

let fields_follow_elim (minor: minor_state) (obj: U64.t) (j: nat)
  : Lemma (requires fields_follow minor /\ Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj)
          (ensures follow_ok minor (to_minor_offset (minor_read_field minor obj j)))
  = reveal_opaque (`%fields_follow) (fields_follow minor)

let fields_follow_intro (minor: minor_state)
  (h: (obj: U64.t) -> (j: nat) ->
       Lemma (requires Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj)
             (ensures follow_ok minor (to_minor_offset (minor_read_field minor obj j))))
  : Lemma (fields_follow minor)
  = reveal_opaque (`%fields_follow) (fields_follow minor);
    let h' (obj: U64.t) (j: nat)
      : Lemma (Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj ==>
               follow_ok minor (to_minor_offset (minor_read_field minor obj j)))
      = FStar.Classical.move_requires (h obj) j
    in
    FStar.Classical.forall_intro_2 h'

/// Every root is followed safely.
let roots_follow (minor: minor_state) (roots: seq U64.t) : prop =
  forall (i: nat). i < Seq.length roots ==> follow_ok minor (Seq.index roots i)

/// Every infix address the forwarding map holds was followed safely.
let entries_follow (minor: minor_state) (fwd: GC.Gen.Promote.forwarding_map) : prop =
  forall (m: U64.t). fwd m <> 0UL /\ is_infix_in_minor minor m ==> infix_at minor m

/// Every major pointer a nursery object's scanned fields hold resolves to a
/// block in use for `un`, through a well-formed infix address.
[@@"opaque_to_smt"]
let major_targets (un: free_def) (minor: minor_state) (g: heap) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
    is_pointer_field (minor_read_field minor obj j) ==>
    in_use un g (resolve_object ((minor_read_field minor obj j) <: obj_addr) g) /\
    infix_addr_wf g (objects zero_addr g) ((minor_read_field minor obj j) <: obj_addr)

let major_targets_elim (un: free_def) (minor: minor_state) (g: heap) (obj: U64.t) (j: nat)
  : Lemma (requires major_targets un minor g /\ Seq.mem obj (minor_objects minor) /\
                    j < minor_scan_wosize minor obj /\ is_pointer_field (minor_read_field minor obj j))
          (ensures in_use un g (resolve_object ((minor_read_field minor obj j) <: obj_addr) g) /\
                   infix_addr_wf g (objects zero_addr g) ((minor_read_field minor obj j) <: obj_addr))
  = reveal_opaque (`%major_targets) (major_targets un minor g)

let major_targets_intro (un: free_def) (minor: minor_state) (g: heap)
  (h: (obj: U64.t) -> (j: nat) ->
       Lemma (requires Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
                       is_pointer_field (minor_read_field minor obj j))
             (ensures in_use un g (resolve_object ((minor_read_field minor obj j) <: obj_addr) g) /\
                      infix_addr_wf g (objects zero_addr g) ((minor_read_field minor obj j) <: obj_addr)))
  : Lemma (major_targets un minor g)
  = reveal_opaque (`%major_targets) (major_targets un minor g);
    let h' (obj: U64.t) (j: nat)
      : Lemma (Seq.mem obj (minor_objects minor) /\ j < minor_scan_wosize minor obj /\
               is_pointer_field (minor_read_field minor obj j) ==>
               in_use un g (resolve_object ((minor_read_field minor obj j) <: obj_addr) g) /\
               infix_addr_wf g (objects zero_addr g) ((minor_read_field minor obj j) <: obj_addr))
      = if Seq.mem obj (minor_objects minor) && j < minor_scan_wosize minor obj &&
           is_pointer_field (minor_read_field minor obj j)
        then h obj j
    in
    FStar.Classical.forall_intro_2 h'

/// ---------------------------------------------------------------------------
/// akhil's conditions imply these
/// ---------------------------------------------------------------------------

let follow_of_infix_wf (minor: minor_state) (addr: U64.t)
  : Lemma (requires minor_infix_wf minor) (ensures follow_ok minor addr)
  = reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor)

let fields_of_infix_wf (minor: minor_state)
  : Lemma (requires minor_infix_wf minor) (ensures fields_follow minor)
  = fields_follow_intro minor (fun obj j -> follow_of_infix_wf minor (to_minor_offset (minor_read_field minor obj j)))

let roots_of_infix_wf (minor: minor_state) (roots: seq U64.t)
  : Lemma (requires minor_infix_wf minor) (ensures roots_follow minor roots)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (follow_of_infix_wf minor))

let entries_of_infix_wf (minor: minor_state) (fwd: GC.Gen.Promote.forwarding_map)
  : Lemma (requires minor_infix_wf minor) (ensures entries_follow minor fwd)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (follow_of_infix_wf minor))

/// A block in use is not infix, so it resolves to itself.
#push-options "--z3rlimit 30"
let target_of_in_use (un: free_def) (g: heap) (v: obj_addr)
  : Lemma (requires free_def_ok un /\ well_formed_heap_with un g /\ in_use un g v)
          (ensures in_use un g (resolve_object v g) /\ infix_addr_wf g (objects zero_addr g) v)
  = wf_with_parts ();
    free_def_ok_elim un;
    assert (~(is_infix v g));
    resolve_non_infix v g;
    infix_addr_wf_non_infix g (objects zero_addr g) v
#pop-options

let targets_of_not_free (un: free_def) (minor: minor_state) (g: heap)
  : Lemma (requires free_def_ok un /\ well_formed_heap_with un g /\ GenInv.minor_major_fields_not_free un minor g)
          (ensures major_targets un minor g)
  = major_targets_intro un minor g (fun obj j ->
      GenInv.minor_major_fields_not_free_elim un minor g obj j;
      target_of_in_use un g ((minor_read_field minor obj j) <: obj_addr))

/// ---------------------------------------------------------------------------
/// Where a pointer lands
/// ---------------------------------------------------------------------------

/// An address with a well-formed infix address lies in the block it
/// resolves to: the block itself, or one of its fields.
#push-options "--z3rlimit 30"
let target_range (g: heap) (w: obj_addr)
  : Lemma (requires infix_addr_wf g (objects zero_addr g) w)
          (ensures (let t = resolve_object w g in
                    U64.v t <= U64.v w /\
                    (t == w \/ U64.v w < U64.v t + U64.v (wosize_of_object t g) * 8)))
  = if is_infix w g then begin
      infix_addr_wf_elim g (objects zero_addr g) w;
      parent_closure_addr_nat_spec w g;
      resolve_infix_spec w g
    end else resolve_non_infix w g
#pop-options

/// The queue holds nursery objects.
let qmem (minor: minor_state) (q: seq U64.t) : prop =
  forall (i: nat). i < Seq.length q ==> Seq.mem (Seq.index q i) (minor_objects minor)
