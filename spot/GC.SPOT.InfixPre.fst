module GC.SPOT.InfixPre

module U64 = FStar.UInt64
module Seq = FStar.Seq

open FStar.Seq
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecHeap = GC.Spec.Heap
module SpecFields = GC.Spec.Fields
module SpecObj = GC.Spec.Object
module GenInv = GC.Gen.HeapInvariant
module CheneyBFS = GC.Gen.CheneyBFS
module CheneySpec = GC.Gen.Cheney
module GenImpl = GC.Gen.Impl
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module MinorFwd = GC.Gen.MinorCollectForwarding
module RBridge = GC.Gen.ReachabilityBridge
module Promote = GC.Gen.Promote
module Header = GC.Lib.Header
module Preconditions = GC.SPOT.Preconditions
module InfixMajor = GC.SPOT.InfixMajor

#set-options "--z3rlimit 30 --fuel 1 --ifuel 1"

let spot_infix_minor : minor_state =
  minor_reset (minor_init (Seq.create minor_heap_size 0uy))

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let spot_infix_minor_is_reset (ms: minor_state)
  =
  // `minor_reset`'s result type pins both record fields, so any two resets
  // are the same state.
  let a = minor_reset ms in
  let b = spot_infix_minor in
  assert (a.data == b.data);
  assert (U64.v a.bump == 0 /\ U64.v b.bump == 0);
  U64.v_inj a.bump b.bump
#pop-options

let spot_infix_minor_objects_empty ()
  =
  spot_infix_minor_is_reset (minor_init (Seq.create minor_heap_size 0uy));
  minor_reset_objects_empty (minor_init (Seq.create minor_heap_size 0uy))

/// ---------------------------------------------------------------------------
/// Roots, slots, forwarding array
/// ---------------------------------------------------------------------------

let spot_infix_roots (r: unit{InfixMajor.spot_infix_room}) : seq U64.t =
  Seq.create 1 (InfixMajor.spot_q r <: U64.t)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let spot_infix_roots_len (r: unit{InfixMajor.spot_infix_room})
  =
  FStar.Seq.Base.lemma_create_len 1 (InfixMajor.spot_q r <: U64.t);
  FStar.Seq.Base.lemma_index_create 1 (InfixMajor.spot_q r <: U64.t) 0

let spot_infix_roots_cases (r: unit{InfixMajor.spot_infix_room}) (root: U64.t)
  =
  spot_infix_roots_len r;
  let roots = spot_infix_roots r in
  assert (Seq.length roots == 1);
  let k = FStar.Seq.Properties.index_mem root roots in
  assert (k == 0)
#pop-options

let spot_infix_slots : seq U64.t = Seq.empty

let spot_infix_fwd_array : seq U64.t =
  Seq.create UpdatePtrs.fwd_array_size 0UL

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_infix_fwd_array_zero ()
  =
  FStar.Seq.Base.lemma_create_len UpdatePtrs.fwd_array_size 0UL;
  let aux (i: nat)
    : Lemma (ensures i < Seq.length spot_infix_fwd_array ==>
                     Seq.index spot_infix_fwd_array i == 0UL)
    =
    if i < Seq.length spot_infix_fwd_array then
      FStar.Seq.Base.lemma_index_create UpdatePtrs.fwd_array_size 0UL i
  in
  FStar.Classical.forall_intro aux;
  Preconditions.zero_forwarding_array_intro spot_infix_fwd_array
#pop-options

/// ---------------------------------------------------------------------------
/// Heap shape
/// ---------------------------------------------------------------------------

let spot_infix_collection_heap_shape (r: unit{InfixMajor.spot_infix_room})
  =
  InfixMajor.spot_infix_major_heap_shape r;
  GenInv.collection_heap_shape_after_minor_reset
    (minor_init (Seq.create minor_heap_size 0uy))
    (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r);
  spot_infix_minor_is_reset (minor_init (Seq.create minor_heap_size 0uy))

/// ---------------------------------------------------------------------------
/// Remembered set
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_infix_ref_table_sound (r: unit{InfixMajor.spot_infix_room})
  =
  assert_norm (Seq.length (Seq.empty #U64.t) == 0)
#pop-options

/// No field of this heap holds a minor pointer, so an *empty* remembered set
/// covers it.  The only pointer-valued field is `Q`'s, and it points inside
/// the major heap.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let spot_infix_ref_table_covers (r: unit{InfixMajor.spot_infix_room})
  =
  let g = InfixMajor.spot_infix_heap r in
  assert_norm (Seq.length (Seq.empty #U64.t) == 0);
  let aux (obj: obj_addr) (j: nat)
    : Lemma
        (ensures
          (Seq.mem obj (SpecFields.objects zero_addr g) /\
           SpecObj.is_blue obj g = false /\
           SpecObj.is_no_scan obj g = false /\
           j < U64.v (SpecObj.wosize_of_object obj g) /\
           U64.v obj + j * 8 + 8 <= heap_size) ==>
          ~(Promote.is_minor_pointer
              (to_minor_offset (SpecHeap.read_word g (U64.uint_to_t (U64.v obj + j * 8))))))
    =
    if not (Seq.mem obj (SpecFields.objects zero_addr g) &&
            SpecObj.is_blue obj g = false &&
            SpecObj.is_no_scan obj g = false &&
            j < U64.v (SpecObj.wosize_of_object obj g) &&
            U64.v obj + j * 8 + 8 <= heap_size)
    then ()
    else begin
    InfixMajor.spot_infix_layout_facts r;
    InfixMajor.spot_infix_field_read r obj j;
    let v = SpecHeap.read_word g (U64.uint_to_t (U64.v obj + j * 8)) in
    zero_addr_above_minor ();
    if obj = InfixMajor.spot_q r then begin
      assert (v == (InfixMajor.spot_h r <: U64.t));
      assert (U64.v v >= minor_heap_size);
      to_minor_offset_stable_above_minor v
    end else if obj = InfixMajor.spot_p r && j = 2 then begin
      assert (v == InfixMajor.infix_header_word);
      SpecObj.infix_tag_val ();
      InfixMajor.header_words_decode r;
      SpecObj.header_low_bits_are_tag_low_bits v;
      assert (U64.v v % 8 == 1)
    end else begin
      assert (v == 0UL);
      assert_norm (Promote.is_minor_pointer 0UL == false)
    end
    end
  in
  FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_infix_remembered_targets_in_roots (r: unit{InfixMajor.spot_infix_room})
  =
  assert_norm (Seq.length (Seq.empty #U64.t) == 0);
  GC.Gen.MinorCollectForwarding.Helpers.remembered_targets_in_roots_intro_by_slots
    (InfixMajor.spot_infix_heap r) (spot_infix_roots r) spot_infix_slots 0
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_infix_roots_valid (r: unit{InfixMajor.spot_infix_room})
  =
  let g = InfixMajor.spot_infix_heap r in
  let aux (root: U64.t)
    : Lemma
        (requires Seq.mem root (spot_infix_roots r))
        (ensures
          ((Promote.is_minor_pointer root ==>
            Seq.mem root (minor_objects spot_infix_minor) /\
            minor_wosize spot_infix_minor root > 0) /\
           (~(Promote.is_minor_pointer root) ==>
            is_val_addr root /\
            Seq.mem (root <: obj_addr) (SpecFields.objects zero_addr g) /\
            ~(SpecObj.is_blue (root <: obj_addr) g))))
    =
    spot_infix_roots_cases r root;
    InfixMajor.spot_infix_mem r;
    InfixMajor.spot_infix_q_reads r;
    assert ((root <: obj_addr) == InfixMajor.spot_q r);
    RBridge.major_object_not_minor_pointer g (InfixMajor.spot_q r)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let spot_infix_minor_collect_full_pre (r: unit{InfixMajor.spot_infix_room})
  =
  spot_infix_collection_heap_shape r;
  spot_infix_fwd_array_zero ();
  spot_infix_ref_table_sound r;
  spot_infix_ref_table_covers r;
  Preconditions.singleton_slots_pairwise_distinct spot_infix_slots 0;
  spot_infix_remembered_targets_in_roots r;
  spot_infix_roots_valid r;
  Preconditions.minor_collect_full_pre_intro
    spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r)
    (spot_infix_roots r) spot_infix_fwd_array spot_infix_slots 0

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let spot_infix_gen_gc_pre (r: unit{InfixMajor.spot_infix_room}) (cap: nat{cap >= 1})
  =
  spot_infix_minor_collect_full_pre r;
  spot_infix_roots_len r;
  assert_norm (Seq.length (Seq.empty #obj_addr) == 0);
  Preconditions.gen_gc_pre_intro
    spot_infix_minor (InfixMajor.spot_infix_heap r) (InfixMajor.spot_infix_fp r)
    (spot_infix_roots r) spot_infix_fwd_array spot_infix_slots 0
    Seq.empty cap
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let spot_infix_cheney_no_oom (r: unit{InfixMajor.spot_infix_room})
  =
  let ms0 = minor_init (Seq.create minor_heap_size 0uy) in
  spot_infix_minor_is_reset ms0;
  let no_mem (addr: U64.t)
    : Lemma (ensures ~(Seq.mem addr (minor_objects spot_infix_minor)))
    = minor_reset_objects_not_mem ms0 addr
  in
  FStar.Classical.forall_intro no_mem;
  // A reset nursery holds no infix header either, so the interior-coverage
  // halves of `fwd_well_formed` are vacuous.
  let no_infix (addr: U64.t)
    : Lemma (ensures ~(is_infix_in_minor spot_infix_minor addr))
    = minor_reset_no_infix ms0 addr
  in
  FStar.Classical.forall_intro no_infix
#pop-options

/// ---------------------------------------------------------------------------
/// No out-of-memory
/// ---------------------------------------------------------------------------
///
/// `cheney_oom` witnesses a *failed promotion*, and `promote_fails_for` demands
/// either an allocated minor object or an infix pointer into one.  The nursery
/// is empty, so neither can exist.

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let spot_infix_no_oom (r: unit{InfixMajor.spot_infix_room})
  =
  let ms0 = minor_init (Seq.create minor_heap_size 0uy) in
  spot_infix_minor_is_reset ms0;
  minor_reset_objects_empty ms0;
  assert (minor_objects spot_infix_minor == Seq.empty);
  assert_norm (Seq.length (Seq.empty #U64.t) == 0);
  let no_fail (cs: CheneySpec.cheney_state) (addr: U64.t)
    : Lemma (ensures ~(CheneyBFS.promote_fails_for spot_infix_minor cs addr))
    =
    minor_reset_objects_not_mem ms0 addr;
    minor_reset_no_infix ms0 addr
  in
  FStar.Classical.forall_intro_2 no_fail;
  reveal_opaque (`%CheneyBFS.cheney_oom_reaching) CheneyBFS.cheney_oom_reaching
#pop-options
