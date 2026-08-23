module GC.Gen.MajorPrecondition

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

module SpecObj = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module SpecMark = GC.Spec.Mark
module SpecSweep = GC.Spec.Sweep
module SweepInv = GC.Spec.SweepInv
module SpecMarkBounded = GC.Spec.MarkBounded
module MarkBoundedInv = GC.Spec.MarkBoundedInv
module GenInv = GC.Gen.HeapInvariant
module Promote = GC.Gen.Promote
module Cheney = GC.Gen.Cheney
module CheneyPres = GC.Gen.CheneyPreservation
module MBP = GC.Impl.MarkBoundedPrecondition

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let post_minor_root_obligations_implies_roots_forwarded minor major fp roots st cap
  =
  let prom = Cheney.cheney_promote minor major fp roots in
  let result = Cheney.cheney_collect_spec minor major fp roots in
  zero_addr_above_minor ();
  Promote.rewrite_roots_length roots prom.fwd_map;
  let aux (i: nat)
    : Lemma
        (ensures i < Seq.length roots ==>
                 Promote.is_minor_pointer (Seq.index roots i) ==>
                 prom.fwd_map (Seq.index roots i) <> 0UL)
    =
    if i < Seq.length roots then begin
      let r = Seq.index roots i in
      Promote.rewrite_roots_index roots prom.fwd_map i;
      assert (Seq.index result.mc_roots i == Promote.rewrite_root r prom.fwd_map);
      if Promote.is_minor_pointer r && prom.fwd_map r = 0UL then begin
        // The root survives `rewrite_root` unchanged, so it is still a nursery
        // address -- strictly below `zero_addr`, hence not a major object.
        assert (Seq.index result.mc_roots i == r);
        assert (U64.v r < minor_heap_size);
        assert (U64.v r < U64.v zero_addr + U64.v mword);
        assert (MBP.root_valid_for_darkening result.mc_major (Seq.index result.mc_roots i));
        assert False
      end
    end
  in
  FStar.Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let gray_black_objects_on_stack_weaken (g: heap) (st: seq obj_addr)
  : Lemma (requires CheneyPres.gray_black_objects_on_stack g st)
          (ensures SpecMark.gray_objects_on_stack g st)
  =
  let aux (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj (SpecFields.objects zero_addr g) /\ SpecObj.is_gray obj g)
        (ensures Seq.mem obj st)
    = assert (SpecObj.is_gray obj g \/ SpecObj.is_black obj g)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let gray_objects_on_stack_strengthen (g: heap) (st: seq obj_addr)
  : Lemma (requires SpecMark.gray_objects_on_stack g st /\
                    SpecMark.no_black_objects g)
          (ensures CheneyPres.gray_black_objects_on_stack g st)
  =
  let aux (obj: obj_addr)
    : Lemma
        (requires Seq.mem obj (SpecFields.objects zero_addr g) /\
                  (SpecObj.is_gray obj g \/ SpecObj.is_black obj g))
        (ensures Seq.mem obj st)
    = assert (~(SpecObj.is_black obj g))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// The five conjuncts of `bounded_mark_inv` on the post-minor heap.  Four come
/// from the transported `major_heap_shape`; only `bounded_stack_props` needs a
/// dedicated preservation lemma, because it is the one clause that mentions the
/// caller's stack.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let post_minor_bounded_mark_inv
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (st: seq obj_addr) (cap: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      MarkBoundedInv.bounded_mark_inv major st cap)
    (ensures (
      let result = Cheney.cheney_collect_spec minor major fp roots in
      MarkBoundedInv.bounded_mark_inv result.mc_major st cap))
  =
  let result = Cheney.cheney_collect_spec minor major fp roots in
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  MarkBoundedInv.bounded_mark_inv_elim_bsp major st cap;
  MarkBoundedInv.bounded_mark_inv_elim_cap major st cap;
  CheneyPres.cheney_collect_preserves_bounded_stack_props minor major fp roots st;
  CheneyPres.cheney_collect_preserves_collection_heap_shape minor major fp roots;
  GenInv.collection_heap_shape_elim result.mc_minor result.mc_major result.mc_fp;
  GenInv.major_heap_shape_elim result.mc_major result.mc_fp;
  SweepInv.heap_objects_dense_intro result.mc_major;
  MarkBoundedInv.bounded_mark_inv_intro result.mc_major st cap
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let darken_precondition_after_minor minor major fp roots st cap
  =
  let result = Cheney.cheney_collect_spec minor major fp roots in
  // Pre-minor shape, needed by every preservation lemma below.
  GenInv.collection_heap_shape_elim minor major fp;
  GenInv.major_heap_shape_elim major fp;
  GenInv.minor_heap_shape_elim minor;
  // Conjunct 1.
  post_minor_bounded_mark_inv minor major fp roots st cap;
  // Conjuncts 2-6: all of them are clauses of the transported `major_heap_shape`.
  CheneyPres.cheney_collect_preserves_collection_heap_shape minor major fp roots;
  GenInv.collection_heap_shape_elim result.mc_minor result.mc_major result.mc_fp;
  GenInv.major_heap_shape_elim result.mc_major result.mc_fp;
  // Conjunct 7: the color-stack condition, transported in its gray-or-black form.
  gray_objects_on_stack_strengthen major st;
  CheneyPres.cheney_collect_preserves_gray_black_objects_on_stack minor major fp roots st;
  gray_black_objects_on_stack_weaken result.mc_major st;
  // Conjuncts 8-10 are the caller's, verbatim.
  assert (MBP.darken_precondition result.mc_major st result.mc_roots result.mc_fp cap)
#pop-options
