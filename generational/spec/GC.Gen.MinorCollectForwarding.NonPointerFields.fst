/// ---------------------------------------------------------------------------
/// GC.Gen.MinorCollectForwarding.NonPointerFields
/// ---------------------------------------------------------------------------

module GC.Gen.MinorCollectForwarding.NonPointerFields

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Remembered
open GC.Gen.Reachability
open GC.Gen.Cheney

module Mark = GC.Spec.Mark
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module PromUpdate = GC.Gen.PromoteUpdate
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module CheneyFields = GC.Gen.CheneyPreservation.Fields
module CheneyInj = GC.Gen.CheneyPreservation.Injectivity
module Forwarding = GC.Gen.CheneyPreservation.Forwarding
module CG = GC.Gen.CombinedGraph
open GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module GenInv = GC.Gen.HeapInvariant

module MCFH = GC.Gen.MinorCollectForwarding.Helpers
open GC.Gen.MinorCollectForwarding.Helpers

module MCFE = GC.Gen.MinorCollectForwarding.Edges

private let combined_vertex_cases (v: CG.combined_vertex)
  : Lemma (ensures MinorV? v \/ MajorV? v)
  = match v with
    | CG.MinorV _ -> ()
    | CG.MajorV _ -> ()

/// Helper: if ~(is_infix_in_minor minor x) and (cheney_promote ...).fwd_map x <> 0,
/// then x must be in minor_objects minor.
/// This chains fwd_noninfix_targets_valid -> well_formed_heap_part4 ->
/// fwd_noninfix_sources_in_minor_objects in a clean, isolated context so that
/// the three forall instantiations run cheaply at low rlimit.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
private let fwd_minor_source_in_minor_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (x: U64.t)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      ~(is_infix_in_minor minor x) /\
      (cheney_promote minor major fp roots).fwd_map x <> 0UL)
    (ensures
      Seq.mem x (minor_objects minor))
  =
    let prom = cheney_promote minor major fp roots in
    let fx = prom.fwd_map x in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    Forwarding.cheney_promote_fwd_noninfix_targets_valid minor major fp roots;
    assert (Seq.mem (fx <: obj_addr) (objects zero_addr prom.major_final));
    Cheney.cheney_promote_preserves_wfh_part4 minor major fp roots;
    assert (~(is_infix fx prom.major_final));
    CheneyInj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
private let major_non_pointer_field_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: obj_addr) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      Seq.mem src (objects zero_addr major) /\
      is_blue src major = false /\
      j < U64.v (wosize_of_object src major) /\
      U64.v src + j * 8 + 8 <= heap_size /\
      (U64.v src + j * 8) % 8 == 0 /\
      CG.classify_major_field minor major
        (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None)
    (ensures
      (let res = cheney_collect_spec minor major fp roots in
       let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
       read_word res.mc_major field_addr ==
       read_word major field_addr))
  =
    let prom = cheney_promote minor major fp roots in
    let res = cheney_collect_spec minor major fp roots in
    let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    MCFH.cheney_promote_preserves_old_major_field_context minor major fp roots src j;
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    assert (read_word prom.major_final field_addr == read_word major field_addr);
    if is_no_scan src prom.major_final then begin
      PromUpdate.update_major_pointers_preserves_no_scan_field
        prom.major_final prom.fwd_map src j
    end else begin
      PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map src j;
      let old_raw = read_word prom.major_final field_addr in
      let old_val = to_minor_offset old_raw in
      assert (old_raw == read_word major field_addr);
      if is_minor_pointer old_val && prom.fwd_map old_val <> 0UL then begin
        GenInv.major_minor_fields_no_infix_targets_elim minor major src j;
        assert (~(is_infix_in_minor minor old_val));
        fwd_minor_source_in_minor_objects minor major fp roots old_val;
        CG.classify_major_field_is_minor minor major (read_word major field_addr);
        assert False
      end;
      assert (~(is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL))
    end

private let minor_non_pointer_field_preserved
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (src: U64.t) (j: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      (let prom = cheney_promote minor major fp roots in
       let img = prom.fwd_map src in
       img <> 0UL /\
       Seq.mem src (minor_objects minor) /\
       is_val_addr img /\
       is_infix img prom.major_final = false /\
       Seq.mem (img <: obj_addr) (objects zero_addr prom.major_final) /\
       is_blue (img <: obj_addr) prom.major_final = false /\
       j < minor_wosize minor src /\
       j < U64.v (wosize_of_object (img <: obj_addr) prom.major_final) /\
       U64.v img + j * 8 + 8 <= heap_size /\
       (U64.v img + j * 8) % 8 == 0 /\
       CG.classify_minor_field minor major (minor_read_field minor src j) == None))
    (ensures
      (let prom = cheney_promote minor major fp roots in
       let res = cheney_collect_spec minor major fp roots in
       let img = prom.fwd_map src in
       let field_addr : hp_addr = U64.uint_to_t (U64.v img + j * 8) in
       read_word res.mc_major field_addr ==
       minor_read_field minor src j))
  =
    let prom = cheney_promote minor major fp roots in
    let img = prom.fwd_map src in
    let img_obj : obj_addr = img in
    let res = cheney_collect_spec minor major fp roots in
    let field_addr : hp_addr = U64.uint_to_t (U64.v img + j * 8) in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    CheneyFields.cheney_promote_fwd_target_fields_match minor major fp roots src j;
    assert (read_word prom.major_final field_addr == minor_read_field minor src j);
    Cheney.cheney_promote_preserves_wfh_part1 minor major fp roots;
    if is_no_scan img_obj prom.major_final then begin
      PromUpdate.update_major_pointers_preserves_no_scan_field
        prom.major_final prom.fwd_map img_obj j
    end else begin
      PromUpdate.update_major_pointers_field_effect prom.major_final prom.fwd_map img_obj j;
      let old_raw = read_word prom.major_final field_addr in
      let old_val = to_minor_offset old_raw in
      assert (old_raw == minor_read_field minor src j);
      if is_minor_pointer old_val && prom.fwd_map old_val <> 0UL then begin
        GenInv.minor_fields_no_infix_targets_elim minor src j;
        assert (~(is_infix_in_minor minor old_val));
        fwd_minor_source_in_minor_objects minor major fp roots old_val;
        minor_objects_valid minor old_val;
        is_minor_addr_from_bounds old_val;
        CG.classify_minor_field_minor minor major (minor_read_field minor src j);
        assert False
      end;
      assert (~(is_minor_pointer old_val /\ prom.fwd_map old_val <> 0UL))
    end

let normal_post_non_pointer_fields_preserved
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      GenInv.collection_heap_shape minor major fp /\
      RBridge.major_field_zero_no_minor minor major /\
      UpdatePtrs.ref_table_covers_minor_ptrs major slots n /\
      remembered_targets_in_roots major roots slots n /\
      Mark.no_pointer_to_blue major /\
      RBridge.minor_no_pointer_to_blue minor major /\
      RBridge.roots_valid_nonblue roots major /\
      roots_valid_for_minor_collection minor major roots /\
      CheneyBFS.cheney_no_oom minor major fp roots)
    (ensures normal_post_non_pointer_fields_preserved_prop minor major fp roots)
  =
    let prom = cheney_promote minor major fp roots in
    GenInv.collection_heap_shape_elim minor major fp;
    GenInv.major_heap_shape_elim major fp;
    GenInv.minor_heap_shape_elim minor;
    assert (well_formed_heap major);
    assert (minor_wf minor);
    assert (RBridge.minor_no_pointer_to_blue minor major);
    assert (RBridge.roots_valid_nonblue roots major);
    RBridge.reachable_major_valid_nonblue minor major roots;
    MCFE.combined_reachable_images_valid_or_infix_from_slots minor major fp roots slots n;
    CheneyInj.cheney_promote_fwd_targets_not_blue minor major fp roots;
    CheneyInj.cheney_promote_fwd_noninfix_sources_in_minor_objects minor major fp roots;
    let aux (u: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u)
      (ensures
        (match u with
        | CG.MajorV src ->
          is_val_addr src ==>
          forall (j:nat).
            j < U64.v (wosize_of_object (src <: obj_addr) major) /\
            U64.v src + j * 8 + 8 <= heap_size /\
            (U64.v src + j * 8) % 8 == 0 /\
            CG.classify_major_field minor major
              (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
            read_word (cheney_collect_spec minor major fp roots).mc_major
              (U64.uint_to_t (U64.v src + j * 8)) ==
            read_word major (U64.uint_to_t (U64.v src + j * 8))
        | CG.MinorV src ->
          let img = prom.fwd_map src in
          is_val_addr img ==>
          forall (j:nat).
            j < minor_wosize minor src /\
            j < U64.v (wosize_of_object (img <: obj_addr) prom.major_final) /\
            U64.v img + j * 8 + 8 <= heap_size /\
            (U64.v img + j * 8) % 8 == 0 /\
            CG.classify_minor_field minor major (minor_read_field minor src j) == None ==>
            read_word (cheney_collect_spec minor major fp roots).mc_major
              (U64.uint_to_t (U64.v img + j * 8)) ==
            minor_read_field minor src j
        | _ -> True))
    =
      match u with
      | CG.MajorV src ->
        assert (is_val_addr src);
        let src_obj : obj_addr = src in
        assert (Seq.mem src_obj (objects zero_addr major));
        assert (is_blue src_obj major = false);
        let per_field (j:nat) : Lemma
          (ensures
            (j < U64.v (wosize_of_object src_obj major) /\
             U64.v src + j * 8 + 8 <= heap_size /\
             (U64.v src + j * 8) % 8 == 0 /\
             CG.classify_major_field minor major
               (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
             read_word (cheney_collect_spec minor major fp roots).mc_major
               (U64.uint_to_t (U64.v src + j * 8)) ==
             read_word major (U64.uint_to_t (U64.v src + j * 8))))
        =
          if j < U64.v (wosize_of_object src_obj major) /\
             U64.v src + j * 8 + 8 <= heap_size /\
             (U64.v src + j * 8) % 8 == 0 /\
             CG.classify_major_field minor major
               (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None
          then begin
            let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
            major_non_pointer_field_preserved minor major fp roots src_obj j;
            assert (read_word (cheney_collect_spec minor major fp roots).mc_major field_addr ==
                    read_word major field_addr)
          end
        in
        FStar.Classical.forall_intro per_field
      | CG.MinorV src ->
        assert (prom.fwd_map src <> 0UL);
        assert (is_val_addr (prom.fwd_map src));
        assert (is_infix (prom.fwd_map src) prom.major_final = false);
        assert (Seq.mem ((prom.fwd_map src) <: obj_addr) (objects zero_addr prom.major_final));
        assert (Seq.mem src (minor_objects minor));
        assert (is_blue ((prom.fwd_map src) <: obj_addr) prom.major_final = false);
        let per_field (j:nat) : Lemma
          (ensures
            (j < minor_wosize minor src /\
             j < U64.v (wosize_of_object ((prom.fwd_map src) <: obj_addr) prom.major_final) /\
             U64.v (prom.fwd_map src) + j * 8 + 8 <= heap_size /\
             (U64.v (prom.fwd_map src) + j * 8) % 8 == 0 /\
             CG.classify_minor_field minor major (minor_read_field minor src j) == None ==>
             read_word (cheney_collect_spec minor major fp roots).mc_major
               (U64.uint_to_t (U64.v (prom.fwd_map src) + j * 8)) ==
             minor_read_field minor src j))
        =
          if j < minor_wosize minor src /\
             j < U64.v (wosize_of_object ((prom.fwd_map src) <: obj_addr) prom.major_final) /\
             U64.v (prom.fwd_map src) + j * 8 + 8 <= heap_size /\
             (U64.v (prom.fwd_map src) + j * 8) % 8 == 0 /\
             CG.classify_minor_field minor major (minor_read_field minor src j) == None
          then begin
            let img = prom.fwd_map src in
            let field_addr : hp_addr = U64.uint_to_t (U64.v img + j * 8) in
            minor_non_pointer_field_preserved minor major fp roots src j;
            assert (read_word (cheney_collect_spec minor major fp roots).mc_major field_addr ==
                    minor_read_field minor src j)
          end
        in
        FStar.Classical.forall_intro per_field
      | _ ->
        combined_vertex_cases u;
        assert False
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let normal_post_non_pointer_fields_preserved_to_result
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (post_major: heap)
  : Lemma
    (requires
      post_major == (cheney_collect_spec minor major fp roots).mc_major /\
      normal_post_non_pointer_fields_preserved_prop minor major fp roots)
    (ensures
      normal_result_non_pointer_fields_preserved_prop
        minor major fp roots post_major)
  =
    let prom = cheney_promote minor major fp roots in
    let aux (u: CG.combined_vertex) : Lemma
      (requires normal_src_reachable minor major fp roots u)
      (ensures
        (match u with
        | CG.MajorV src ->
          is_val_addr src ==>
          forall (j:nat).
            j < U64.v (wosize_of_object (src <: obj_addr) major) /\
            U64.v src + j * 8 + 8 <= heap_size /\
            (U64.v src + j * 8) % 8 == 0 /\
            CG.classify_major_field minor major
              (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
            read_word post_major (U64.uint_to_t (U64.v src + j * 8)) ==
            read_word major (U64.uint_to_t (U64.v src + j * 8))
        | CG.MinorV src ->
          let img = prom.fwd_map src in
          is_val_addr img ==>
          forall (j:nat).
            j < minor_wosize minor src /\
            j < U64.v (wosize_of_object (img <: obj_addr) prom.major_final) /\
            U64.v img + j * 8 + 8 <= heap_size /\
            (U64.v img + j * 8) % 8 == 0 /\
            CG.classify_minor_field minor major (minor_read_field minor src j) == None ==>
            read_word post_major (U64.uint_to_t (U64.v img + j * 8)) ==
            minor_read_field minor src j
        | _ -> True))
    =
      match u with
      | CG.MajorV src ->
        if is_val_addr src then begin
          let src_obj : obj_addr = src in
          let per_field (j:nat) : Lemma
            (ensures
              (j < U64.v (wosize_of_object src_obj major) /\
               U64.v src + j * 8 + 8 <= heap_size /\
               (U64.v src + j * 8) % 8 == 0 /\
               CG.classify_major_field minor major
                 (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
               read_word post_major (U64.uint_to_t (U64.v src + j * 8)) ==
               read_word major (U64.uint_to_t (U64.v src + j * 8))))
          =
            if j < U64.v (wosize_of_object src_obj major) /\
               U64.v src + j * 8 + 8 <= heap_size /\
               (U64.v src + j * 8) % 8 == 0 /\
               CG.classify_major_field minor major
                 (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None
            then begin
              let field_addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
              assert (read_word (cheney_collect_spec minor major fp roots).mc_major field_addr ==
                      read_word major field_addr);
              assert (read_word post_major field_addr ==
                      read_word major field_addr)
            end
          in
          FStar.Classical.forall_intro per_field;
          assert (forall (j:nat).
            j < U64.v (wosize_of_object src_obj major) /\
            U64.v src + j * 8 + 8 <= heap_size /\
            (U64.v src + j * 8) % 8 == 0 /\
            CG.classify_major_field minor major
              (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
            read_word post_major (U64.uint_to_t (U64.v src + j * 8)) ==
            read_word major (U64.uint_to_t (U64.v src + j * 8)))
        end;
        assert (is_val_addr src ==> forall (j:nat).
          j < U64.v (wosize_of_object (src <: obj_addr) major) /\
          U64.v src + j * 8 + 8 <= heap_size /\
          (U64.v src + j * 8) % 8 == 0 /\
          CG.classify_major_field minor major
            (read_word major (U64.uint_to_t (U64.v src + j * 8))) == None ==>
          read_word post_major (U64.uint_to_t (U64.v src + j * 8)) ==
          read_word major (U64.uint_to_t (U64.v src + j * 8)))
      | CG.MinorV src ->
        let img = prom.fwd_map src in
        if is_val_addr img then begin
          let img_obj : obj_addr = img in
          let per_field (j:nat) : Lemma
            (ensures
              (j < minor_wosize minor src /\
               j < U64.v (wosize_of_object img_obj prom.major_final) /\
               U64.v img + j * 8 + 8 <= heap_size /\
               (U64.v img + j * 8) % 8 == 0 /\
               CG.classify_minor_field minor major (minor_read_field minor src j) == None ==>
               read_word post_major (U64.uint_to_t (U64.v img + j * 8)) ==
               minor_read_field minor src j))
          =
            if j < minor_wosize minor src /\
               j < U64.v (wosize_of_object img_obj prom.major_final) /\
               U64.v img + j * 8 + 8 <= heap_size /\
               (U64.v img + j * 8) % 8 == 0 /\
               CG.classify_minor_field minor major (minor_read_field minor src j) == None
            then begin
              let field_addr : hp_addr = U64.uint_to_t (U64.v img + j * 8) in
              assert (read_word (cheney_collect_spec minor major fp roots).mc_major field_addr ==
                      minor_read_field minor src j);
              assert (read_word post_major field_addr ==
                      minor_read_field minor src j)
            end
          in
          FStar.Classical.forall_intro per_field;
          assert (forall (j:nat).
            j < minor_wosize minor src /\
            j < U64.v (wosize_of_object img_obj prom.major_final) /\
            U64.v img + j * 8 + 8 <= heap_size /\
            (U64.v img + j * 8) % 8 == 0 /\
            CG.classify_minor_field minor major (minor_read_field minor src j) == None ==>
            read_word post_major (U64.uint_to_t (U64.v img + j * 8)) ==
            minor_read_field minor src j)
        end;
        assert (is_val_addr img ==> forall (j:nat).
          j < minor_wosize minor src /\
          j < U64.v (wosize_of_object (img <: obj_addr) prom.major_final) /\
          U64.v img + j * 8 + 8 <= heap_size /\
          (U64.v img + j * 8) % 8 == 0 /\
          CG.classify_minor_field minor major (minor_read_field minor src j) == None ==>
          read_word post_major (U64.uint_to_t (U64.v img + j * 8)) ==
          minor_read_field minor src j)
      | _ ->
        combined_vertex_cases u;
        assert False
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options
