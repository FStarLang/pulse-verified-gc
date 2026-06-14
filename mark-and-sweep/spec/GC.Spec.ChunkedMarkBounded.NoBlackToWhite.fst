module GC.Spec.ChunkedMarkBounded.NoBlackToWhite

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs
module BPres = GC.Spec.ChunkedMarkBounded.Preservation
module BReady = GC.Spec.ChunkedMarkBounded.TargetReady
module BStackStep = GC.Spec.ChunkedMarkBounded.StackStep
module BColor = GC.Spec.ChunkedMarkBounded.ColorInvariant
module BMetadata = GC.Spec.ChunkedMarkBounded.Metadata
module BTag = GC.Spec.ChunkedMarkBounded.TagInvariant
module BEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

#push-options "--z3rlimit 1"
let chunked_no_black_to_white_vertex_targets
  (mh: MH.major_heap)
  : prop
  =
  forall (src dst: obj_addr).
    ChunkedMajorGraph.chunked_major_edge mh src dst ==>
    ChunkedMajorGraph.chunked_major_vertex mh dst ==>
    SweepDefs.chunked_is_black mh src ==>
    ~(SweepDefs.chunked_is_white mh dst)

let chunked_no_black_to_white_vertex_targets_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst /\
          SweepDefs.chunked_is_black mh src ==>
          ~(SweepDefs.chunked_is_white mh dst))
      (ensures chunked_no_black_to_white_vertex_targets mh)
  =
  let one (src dst: obj_addr)
    : Lemma
        (requires
          ChunkedMajorGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGraph.chunked_major_vertex mh dst /\
          SweepDefs.chunked_is_black mh src)
        (ensures ~(SweepDefs.chunked_is_white mh dst))
    =
    ()
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 one)

let chunked_no_black_to_white_vertex_targets_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMajorGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGraph.chunked_major_vertex mh dst /\
        SweepDefs.chunked_is_black mh src)
      (ensures ~(SweepDefs.chunked_is_white mh dst))
  =
  ()
#pop-options

#push-options "--z3rlimit 10"
let chunked_push_children_bounded_first_step_grays_target
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        U64.v i <= U64.v ws /\
        (let v = MarkDefs.chunked_get_field mh obj i in
         MarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = MarkDefs.chunked_resolve_object mh child_raw in
          child == target /\
          SweepDefs.chunked_is_white mh child)))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ~(SweepDefs.chunked_is_white mh' target)))
  =
  BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
  let v = MarkDefs.chunked_get_field mh obj i in
  let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
  let child = MarkDefs.chunked_resolve_object mh child_raw in
  assert (child == target);
  BPres.chunked_push_children_bounded_preservation_ready_child mh obj i ws;
  assert (Seq.mem target (MH.major_objects mh));
  MarkPres.chunked_make_gray_not_white mh target;
  assert (~(SweepDefs.chunked_is_white
    (MarkDefs.chunked_make_gray mh target) target));
  if U64.v i < U64.v ws then begin
    MarkPres.chunked_make_gray_preserves_well_formed mh target;
    BPres.chunked_push_children_bounded_preservation_ready_next mh obj i ws;
    BColor.chunked_push_children_bounded_no_new_white
      (MarkDefs.chunked_make_gray mh target)
      (if Seq.length st < cap then Seq.cons target st else st)
      obj (U64.add i 1UL) ws cap target;
    let (mh_final, _) =
      BDefs.chunked_push_children_bounded mh st obj i ws cap in
    assert (~(SweepDefs.chunked_is_white mh_final target))
  end else begin
    assert (U64.v i == U64.v ws);
    let step_child =
      MarkDefs.chunked_resolve_object mh
        (MarkDefs.chunked_pointer_field_as_obj_addr mh
          (MarkDefs.chunked_get_field mh obj i)) in
    assert (step_child == target);
    assert (
      MarkDefs.chunked_make_gray mh step_child ==
      MarkDefs.chunked_make_gray mh target);
    if Seq.length st < cap then begin
      assert (Seq.cons step_child st == Seq.cons target st);
      assert (BDefs.chunked_push_children_bounded mh st obj i ws cap ==
        (MarkDefs.chunked_make_gray mh target, Seq.cons target st))
    end else
      assert (BDefs.chunked_push_children_bounded mh st obj i ws cap ==
        (MarkDefs.chunked_make_gray mh target, st));
    let (mh_final, _) =
      BDefs.chunked_push_children_bounded mh st obj i ws cap in
    assert (~(SweepDefs.chunked_is_white mh_final target))
  end
#pop-options

#push-options "--z3rlimit 10"
let chunked_push_children_bounded_current_field_target_non_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        U64.v i <= U64.v ws /\
        ChunkedMajorGraph.chunked_major_field_points_to mh obj i target /\
        ~(SweepDefs.chunked_is_infix mh target))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ~(SweepDefs.chunked_is_white mh' target)))
  =
  BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
  ChunkedMajorGraph.chunked_major_field_points_to_elim mh obj i target;
  let v = MarkDefs.chunked_get_field mh obj i in
  assert (MarkDefs.chunked_is_pointer_field mh v);
  MarkDefs.chunked_pointer_field_as_obj_addr_step mh v;
  let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
  assert (child_raw == target);
  MarkDefs.chunked_resolve_non_infix mh target;
  let child = MarkDefs.chunked_resolve_object mh child_raw in
  assert (child == target);
  if SweepDefs.chunked_is_white mh child then begin
    chunked_push_children_bounded_first_step_grays_target
      mh st obj i ws cap target;
    let (mh_final, _) =
      BDefs.chunked_push_children_bounded mh st obj i ws cap in
    assert (~(SweepDefs.chunked_is_white mh_final target))
  end else if U64.v i < U64.v ws then begin
    BPres.chunked_push_children_bounded_preservation_ready_next mh obj i ws;
    BColor.chunked_push_children_bounded_no_new_white
      mh st obj (U64.add i 1UL) ws cap target;
    let (mh_final, _) =
      BDefs.chunked_push_children_bounded mh st obj i ws cap in
    assert (~(SweepDefs.chunked_is_white mh_final target))
  end else begin
    assert (U64.v i == U64.v ws);
    assert (BDefs.chunked_push_children_bounded mh st obj i ws cap == (mh, st));
    let (mh_final, _) =
      BDefs.chunked_push_children_bounded mh st obj i ws cap in
    assert (~(SweepDefs.chunked_is_white mh_final target))
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_push_children_bounded_field_target_non_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (j: U64.t{U64.v j >= 1})
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        U64.v i <= U64.v j /\
        U64.v j <= U64.v ws /\
        ChunkedMajorGraph.chunked_major_vertex mh target /\
        ChunkedMajorGraph.chunked_major_field_points_to mh obj j target /\
        ~(SweepDefs.chunked_is_infix mh target))
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         ~(SweepDefs.chunked_is_white mh' target)))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    assert False
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    ChunkedMajorGraph.chunked_major_field_points_to_elim mh obj j target;
    let v = MarkDefs.chunked_get_field mh obj i in
    let (mh1, st1) =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          let mh_gray = MarkDefs.chunked_make_gray mh child in
          if Seq.length st < cap then
            (mh_gray, Seq.cons child st)
          else
            (mh_gray, st)
        else
          (mh, st)
      else
        (mh, st)
    in
    if U64.v i = U64.v j then begin
      assert (j == i);
      assert (ChunkedMajorGraph.chunked_major_field_points_to
        mh obj i target);
      assert (U64.v i <= U64.v ws);
      assert (
        MH.well_formed_major_heap mh /\
        BPres.chunked_push_children_bounded_preservation_ready mh obj i ws /\
        U64.v i <= U64.v ws /\
        ChunkedMajorGraph.chunked_major_field_points_to mh obj i target /\
        ~(SweepDefs.chunked_is_infix mh target));
      chunked_push_children_bounded_current_field_target_non_white
        mh st obj i ws cap target;
      let (mh_final, _) =
        BDefs.chunked_push_children_bounded mh st obj i ws cap in
      assert (~(SweepDefs.chunked_is_white mh_final target))
    end else begin
      assert (U64.v i < U64.v j);
      if MarkDefs.chunked_is_pointer_field mh v then begin
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then begin
          BPres.chunked_push_children_bounded_preservation_ready_child
            mh obj i ws;
          assert (Seq.mem child (MH.major_objects mh));
          if child = target then begin
            assert (
              (let v0 = MarkDefs.chunked_get_field mh obj i in
               MarkDefs.chunked_is_pointer_field mh v0 /\
               (let child_raw0 =
                  MarkDefs.chunked_pointer_field_as_obj_addr mh v0 in
                let child0 = MarkDefs.chunked_resolve_object mh child_raw0 in
                child0 == target /\
                SweepDefs.chunked_is_white mh child0)));
            chunked_push_children_bounded_first_step_grays_target
              mh st obj i ws cap target;
            let (mh_final, _) =
              BDefs.chunked_push_children_bounded mh st obj i ws cap in
            assert (~(SweepDefs.chunked_is_white mh_final target))
          end else begin
            MarkPres.chunked_make_gray_preserves_other_white_status
              mh child target;
            MarkPres.chunked_make_gray_preserves_well_formed mh child;
            MarkPres.chunked_make_gray_preserves_major_objects mh child;
            assert (U64.v i < U64.v ws);
            BPres.chunked_push_children_bounded_preservation_ready_next
              mh obj i ws;
            ChunkedMajorGraph.chunked_major_vertex_elim mh obj;
            ChunkedMajorGraph.chunked_major_vertex_elim mh target;
            ChunkedMajorGraph.chunked_major_vertex_intro
              (MarkDefs.chunked_make_gray mh child) obj;
            ChunkedMajorGraph.chunked_major_vertex_intro
              (MarkDefs.chunked_make_gray mh child) target;
            MarkPres.chunked_make_gray_preserves_no_scan_status
              mh child obj;
            MarkPres.chunked_make_gray_preserves_wosize_of_object
              mh child obj;
            MarkPres.chunked_make_gray_preserves_get_field
              mh child obj j;
            MarkPres.chunked_make_gray_preserves_infix_status
              mh child target;
            MarkPres.chunked_make_gray_preserves_ranges mh child;
            let v_old = MarkDefs.chunked_get_field mh obj j in
            let v_new =
              MarkDefs.chunked_get_field
                (MarkDefs.chunked_make_gray mh child) obj j in
            assert (v_new == v_old);
            MarkDefs.chunked_is_pointer_field_step mh v_old;
            MarkDefs.chunked_is_pointer_field_step
              (MarkDefs.chunked_make_gray mh child) v_old;
            GC.Spec.ChunkedSweepCoalesce.RangePreservation.same_chunk_ranges_preserves_is_major_pointer
              mh (MarkDefs.chunked_make_gray mh child) v_old;
            assert (MarkDefs.chunked_is_pointer_field
              (MarkDefs.chunked_make_gray mh child) v_old);
            assert (MarkDefs.chunked_is_pointer_field
              (MarkDefs.chunked_make_gray mh child) v_new);
            MarkDefs.chunked_pointer_field_as_obj_addr_step mh v_old;
            MarkDefs.chunked_pointer_field_as_obj_addr_step
              (MarkDefs.chunked_make_gray mh child) v_new;
            assert (~(MarkDefs.chunked_is_no_scan
              (MarkDefs.chunked_make_gray mh child) obj));
            assert (U64.v j <=
              U64.v (SweepDefs.chunked_wosize_of_object
                (MarkDefs.chunked_make_gray mh child) obj));
            assert (
              (let vj =
                MarkDefs.chunked_get_field
                  (MarkDefs.chunked_make_gray mh child) obj j in
               MarkDefs.chunked_is_pointer_field
                 (MarkDefs.chunked_make_gray mh child) vj /\
               MarkDefs.chunked_pointer_field_as_obj_addr
                 (MarkDefs.chunked_make_gray mh child) vj == target));
            ChunkedMajorGraph.chunked_major_field_points_to_intro
              (MarkDefs.chunked_make_gray mh child) obj j target;
            assert (U64.v (U64.add i 1UL) <= U64.v j);
            assert (U64.v j <= U64.v ws);
            assert (U64.v ws - U64.v (U64.add i 1UL) <
                    U64.v ws - U64.v i);
            assert (
              MH.well_formed_major_heap (MarkDefs.chunked_make_gray mh child) /\
              BPres.chunked_push_children_bounded_preservation_ready
                (MarkDefs.chunked_make_gray mh child) obj (U64.add i 1UL) ws /\
              U64.v (U64.add i 1UL) <= U64.v j /\
              U64.v j <= U64.v ws /\
              ChunkedMajorGraph.chunked_major_vertex
                (MarkDefs.chunked_make_gray mh child) target /\
              ChunkedMajorGraph.chunked_major_field_points_to
                (MarkDefs.chunked_make_gray mh child) obj j target /\
              ~(SweepDefs.chunked_is_infix
                  (MarkDefs.chunked_make_gray mh child) target));
            chunked_push_children_bounded_field_target_non_white
              (MarkDefs.chunked_make_gray mh child)
              (if Seq.length st < cap then Seq.cons child st else st)
              obj (U64.add i 1UL) ws cap j target;
            assert (
              BDefs.chunked_push_children_bounded mh st obj i ws cap ==
              BDefs.chunked_push_children_bounded
                (MarkDefs.chunked_make_gray mh child)
                (if Seq.length st < cap then Seq.cons child st else st)
                obj (U64.add i 1UL) ws cap);
            let (mh_final, _) =
              BDefs.chunked_push_children_bounded mh st obj i ws cap in
            assert (~(SweepDefs.chunked_is_white mh_final target))
          end
        end else begin
        assert (U64.v i < U64.v ws);
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
          assert (U64.v (U64.add i 1UL) <= U64.v j);
          assert (U64.v j <= U64.v ws);
          assert (U64.v ws - U64.v (U64.add i 1UL) <
                  U64.v ws - U64.v i);
          assert (
            MH.well_formed_major_heap mh /\
            BPres.chunked_push_children_bounded_preservation_ready
              mh obj (U64.add i 1UL) ws /\
            U64.v (U64.add i 1UL) <= U64.v j /\
            U64.v j <= U64.v ws /\
            ChunkedMajorGraph.chunked_major_vertex mh target /\
            ChunkedMajorGraph.chunked_major_field_points_to mh obj j target /\
            ~(SweepDefs.chunked_is_infix mh target));
          chunked_push_children_bounded_field_target_non_white
            mh st obj (U64.add i 1UL) ws cap j target;
          assert (
            BDefs.chunked_push_children_bounded mh st obj i ws cap ==
            BDefs.chunked_push_children_bounded
              mh st obj (U64.add i 1UL) ws cap);
          let (mh_final, _) =
            BDefs.chunked_push_children_bounded mh st obj i ws cap in
          assert (~(SweepDefs.chunked_is_white mh_final target))
        end
      end else begin
        assert (U64.v i < U64.v ws);
        BPres.chunked_push_children_bounded_preservation_ready_next
          mh obj i ws;
        assert (U64.v (U64.add i 1UL) <= U64.v j);
        assert (U64.v j <= U64.v ws);
        assert (U64.v ws - U64.v (U64.add i 1UL) <
                U64.v ws - U64.v i);
        assert (
          MH.well_formed_major_heap mh /\
          BPres.chunked_push_children_bounded_preservation_ready
            mh obj (U64.add i 1UL) ws /\
          U64.v (U64.add i 1UL) <= U64.v j /\
          U64.v j <= U64.v ws /\
          ChunkedMajorGraph.chunked_major_vertex mh target /\
          ChunkedMajorGraph.chunked_major_field_points_to mh obj j target /\
          ~(SweepDefs.chunked_is_infix mh target));
        chunked_push_children_bounded_field_target_non_white
          mh st obj (U64.add i 1UL) ws cap j target;
        assert (
          BDefs.chunked_push_children_bounded mh st obj i ws cap ==
          BDefs.chunked_push_children_bounded
            mh st obj (U64.add i 1UL) ws cap);
        let (mh_final, _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
        assert (~(SweepDefs.chunked_is_white mh_final target))
      end
    end
  end
#pop-options

#push-options "--z3rlimit 10"
let chunked_mark_step_bounded_preserves_no_black_to_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_step_bounded_preservation_ready mh st cap /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_no_black_to_white_vertex_targets mh /\
        BEdge.chunked_vertex_edge_targets_non_infix
          (fst (BDefs.chunked_mark_step_bounded mh st cap)))
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         chunked_no_black_to_white_vertex_targets mh'))
  =
  let edge_no_white (src dst: obj_addr)
    : Lemma
        (requires
          (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
           ChunkedMajorGraph.chunked_major_edge mh' src dst /\
           ChunkedMajorGraph.chunked_major_vertex mh' dst /\
           SweepDefs.chunked_is_black mh' src))
        (ensures
          (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
           ~(SweepDefs.chunked_is_white mh' dst)))
    =
    if Seq.length st = 0 then begin
      BDefs.chunked_mark_step_bounded_empty mh st cap;
      chunked_no_black_to_white_vertex_targets_elim mh src dst
    end else begin
      BReady.chunked_bounded_stack_head mh st;
      let obj = Seq.head st in
      let mh_black = MarkDefs.chunked_make_black mh obj in
      ChunkedMajorGraph.chunked_major_edge_source_vertex
        (fst (BDefs.chunked_mark_step_bounded mh st cap)) src dst;
      if MarkDefs.chunked_is_no_scan mh obj then begin
        BDefs.chunked_mark_step_bounded_no_scan mh st cap;
        if src = obj then begin
          MarkPres.chunked_make_black_preserves_no_scan_status mh obj obj;
          ChunkedMajorGraph.chunked_major_edge_source_not_no_scan
            mh_black src dst;
          assert False
        end else begin
          MarkPres.chunked_make_black_preserves_major_objects mh obj;
          ChunkedMajorGraph.chunked_major_vertex_elim mh_black src;
          assert (Seq.mem src (MH.major_objects mh));
          ChunkedMajorGraph.chunked_major_vertex_intro mh src;
          BColor.chunked_mark_step_bounded_field_preserved mh st cap src;
          BMetadata.chunked_mark_step_bounded_preserves_no_scan_status
            mh st cap src;
          BMetadata.chunked_mark_step_bounded_preserves_ranges mh st cap;
          let pc (v: U64.t)
            : Lemma
                (ensures
                  MarkDefs.chunked_is_pointer_field mh v ==
                  MarkDefs.chunked_is_pointer_field mh_black v)
            =
            MarkDefs.chunked_is_pointer_field_step mh v;
            MarkDefs.chunked_is_pointer_field_step mh_black v;
            GC.Spec.ChunkedSweepCoalesce.RangePreservation.same_chunk_ranges_preserves_is_major_pointer
              mh mh_black v
          in
          FStar.Classical.forall_intro pc;
          ChunkedMajorGraph.chunked_major_pointer_classification_preserved_intro
            mh mh_black;
          ChunkedMajorGraph.chunked_major_successors_preserved_from_fields
            mh mh_black src;
          ChunkedMajorGraph.chunked_major_successors_preserved_elim
            mh mh_black src;
          BPres.chunked_mark_step_bounded_preserves_other_black_status
            mh st cap src;
          assert (SweepDefs.chunked_is_black mh src);
          assert (ChunkedMajorGraph.chunked_major_edge mh src dst);
          BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
          ChunkedMajorGraph.chunked_major_vertex_elim mh_black dst;
          ChunkedMajorGraph.chunked_major_vertex_intro mh dst;
          chunked_no_black_to_white_vertex_targets_elim mh src dst;
          BColor.chunked_mark_step_bounded_no_new_white mh st cap dst
        end
      end else begin
        BDefs.chunked_mark_step_bounded_scan mh st cap;
        BPres.chunked_mark_step_bounded_preservation_ready_scan mh st cap;
        MarkPres.chunked_make_black_preserves_well_formed mh obj;
        MarkPres.chunked_make_black_preserves_major_objects mh obj;
        let ws = SweepDefs.chunked_wosize_of_object mh obj in
        let st_tail = Seq.tail st in
        let (mh_final, _) =
          BDefs.chunked_push_children_bounded mh_black st_tail obj 1UL ws cap in
        if src = obj then begin
          ChunkedMajorGraph.chunked_major_vertex_intro mh obj;
          ChunkedMajorGraph.chunked_major_vertex_elim mh obj;
          ChunkedMajorGraph.chunked_major_vertex_intro mh_black obj;
          assert (BPres.chunked_push_children_bounded_preservation_ready
            mh_black obj 1UL ws);
          BColor.chunked_push_children_bounded_field_preserved
            mh_black st_tail obj 1UL ws cap obj;
          BMetadata.chunked_push_children_bounded_preserves_no_scan_status
            mh_black st_tail obj 1UL ws cap obj;
          BMetadata.chunked_push_children_bounded_preserves_ranges
            mh_black st_tail obj 1UL ws cap;
          let pc (v: U64.t)
            : Lemma
                (ensures
                  MarkDefs.chunked_is_pointer_field mh_black v ==
                  MarkDefs.chunked_is_pointer_field mh_final v)
            =
            MarkDefs.chunked_is_pointer_field_step mh_black v;
            MarkDefs.chunked_is_pointer_field_step mh_final v;
            GC.Spec.ChunkedSweepCoalesce.RangePreservation.same_chunk_ranges_preserves_is_major_pointer
              mh_black mh_final v
          in
          FStar.Classical.forall_intro pc;
          ChunkedMajorGraph.chunked_major_pointer_classification_preserved_intro
            mh_black mh_final;
          assert (ChunkedMajorGraph.chunked_major_field_preserved
            mh_black mh_final obj);
          assert (MarkDefs.chunked_is_no_scan mh_black obj ==
            MarkDefs.chunked_is_no_scan mh_final obj);
          assert (ChunkedMajorGraph.chunked_major_pointer_classification_preserved
            mh_black mh_final);
          ChunkedMajorGraph.chunked_major_successors_preserved_from_fields
            mh_black mh_final obj;
          ChunkedMajorGraph.chunked_major_successors_preserved_elim
            mh_black mh_final obj;
          assert (ChunkedMajorGraph.chunked_major_edge mh_black obj dst);
          ChunkedMajorGraph.chunked_major_edge_elim mh_black obj dst;
          let from_field
              (j: U64.t{
                U64.v j >= 1 /\
                ChunkedMajorGraph.chunked_major_field_points_to
                  mh_black obj j dst})
            : Lemma
                (ensures ~(SweepDefs.chunked_is_white mh_final dst))
            =
            ChunkedMajorGraph.chunked_major_field_points_to_elim
              mh_black obj j dst;
            BEdge.chunked_vertex_edge_targets_non_infix_elim
              mh_final obj dst;
            ChunkedMajorGraph.chunked_major_vertex_elim mh_final dst;
            BPres.chunked_push_children_bounded_preserves_major_objects
              mh_black st_tail obj 1UL ws cap;
            ChunkedMajorGraph.chunked_major_vertex_intro mh_black dst;
            ChunkedMajorGraph.chunked_major_vertex_elim mh_black obj;
            MarkPres.chunked_make_black_preserves_wosize_of_object
              mh obj obj;
            assert (SweepDefs.chunked_wosize_of_object mh_black obj == ws);
            assert (U64.v 1UL <= U64.v j);
            assert (U64.v j <= U64.v ws);
            BTag.chunked_push_children_bounded_preserves_infix_status
              mh_black st_tail obj 1UL ws cap dst;
            assert (~(SweepDefs.chunked_is_infix mh_black dst));
            assert (
              MH.well_formed_major_heap mh_black /\
              BPres.chunked_push_children_bounded_preservation_ready
                mh_black obj 1UL ws /\
              U64.v 1UL <= U64.v j /\
              U64.v j <= U64.v ws /\
              ChunkedMajorGraph.chunked_major_vertex mh_black dst /\
              ChunkedMajorGraph.chunked_major_field_points_to
                mh_black obj j dst /\
              ~(SweepDefs.chunked_is_infix mh_black dst));
            chunked_push_children_bounded_field_target_non_white
              mh_black st_tail obj 1UL ws cap j dst
          in
          FStar.Classical.exists_elim
            (~(SweepDefs.chunked_is_white mh_final dst))
            #_
            #(fun (j: U64.t{U64.v j >= 1}) ->
              ChunkedMajorGraph.chunked_major_field_points_to
                mh_black obj j dst)
            ()
            (fun j -> from_field j)
        end else begin
          BPres.chunked_push_children_bounded_preserves_major_objects
            mh_black st_tail obj 1UL ws cap;
          ChunkedMajorGraph.chunked_major_vertex_elim mh_final src;
          ChunkedMajorGraph.chunked_major_vertex_intro mh_black src;
          ChunkedMajorGraph.chunked_major_vertex_elim mh_black src;
          ChunkedMajorGraph.chunked_major_vertex_intro mh src;
          BColor.chunked_mark_step_bounded_field_preserved mh st cap src;
          BMetadata.chunked_mark_step_bounded_preserves_no_scan_status
            mh st cap src;
          BMetadata.chunked_mark_step_bounded_preserves_ranges mh st cap;
          let pc (v: U64.t)
            : Lemma
                (ensures
                  MarkDefs.chunked_is_pointer_field mh v ==
                  MarkDefs.chunked_is_pointer_field mh_final v)
            =
            MarkDefs.chunked_is_pointer_field_step mh v;
            MarkDefs.chunked_is_pointer_field_step mh_final v;
            GC.Spec.ChunkedSweepCoalesce.RangePreservation.same_chunk_ranges_preserves_is_major_pointer
              mh mh_final v
          in
          FStar.Classical.forall_intro pc;
          ChunkedMajorGraph.chunked_major_pointer_classification_preserved_intro
            mh mh_final;
          ChunkedMajorGraph.chunked_major_successors_preserved_from_fields
            mh mh_final src;
          ChunkedMajorGraph.chunked_major_successors_preserved_elim
            mh mh_final src;
          assert (ChunkedMajorGraph.chunked_major_edge mh src dst);
          BPres.chunked_mark_step_bounded_preserves_other_black_status
            mh st cap src;
          assert (SweepDefs.chunked_is_black mh src);
          BPres.chunked_mark_step_bounded_preserves_major_objects mh st cap;
          ChunkedMajorGraph.chunked_major_vertex_elim mh_final dst;
          ChunkedMajorGraph.chunked_major_vertex_intro mh dst;
          chunked_no_black_to_white_vertex_targets_elim mh src dst;
          BColor.chunked_mark_step_bounded_no_new_white mh st cap dst
        end
      end
    end
  in
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 edge_no_white);
  chunked_no_black_to_white_vertex_targets_intro
    (fst (BDefs.chunked_mark_step_bounded mh st cap))
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_inner_loop_preserves_no_black_to_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        BReady.chunked_bounded_stack_props mh st /\
        chunked_no_black_to_white_vertex_targets mh /\
        BEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh', _) =
          BDefs.chunked_mark_inner_loop mh st cap fuel in
         chunked_no_black_to_white_vertex_targets mh'))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then begin
    BDefs.chunked_mark_inner_loop_base mh st cap fuel;
    assert (BDefs.chunked_mark_inner_loop mh st cap fuel == (mh, st))
  end else begin
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    BPres.chunked_mark_inner_loop_preservation_ready_step mh st cap fuel;
    BPres.chunked_mark_step_bounded_preserves_well_formed mh st cap;
    BStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
      mh st cap;
    BEdge.chunked_mark_step_bounded_preserves_vertex_edge_targets_non_infix
      mh st cap;
    chunked_mark_step_bounded_preserves_no_black_to_white mh st cap;
    let (mh_step, st_step) = BDefs.chunked_mark_step_bounded mh st cap in
    assert (fuel - 1 < fuel);
    chunked_mark_inner_loop_preserves_no_black_to_white
      mh_step st_step cap (fuel - 1);
    assert (
      BDefs.chunked_mark_inner_loop mh st cap fuel ==
      BDefs.chunked_mark_inner_loop mh_step st_step cap (fuel - 1))
  end
#pop-options

#push-options "--z3rlimit 10"
let rec chunked_mark_bounded_preserves_no_black_to_white
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        BPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        chunked_no_black_to_white_vertex_targets mh /\
        BEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        chunked_no_black_to_white_vertex_targets
          (BDefs.chunked_mark_bounded mh cap fuel))
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then
      assert (BDefs.chunked_mark_bounded mh cap fuel == mh)
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      BPres.chunked_mark_bounded_preservation_ready_step mh cap fuel;
      BReady.chunked_rescan_heap_bounded_stack_props mh cap;
      chunked_mark_inner_loop_preserves_no_black_to_white
        mh st cap inner_fuel;
      BEdge.chunked_mark_inner_loop_preserves_vertex_edge_targets_non_infix
        mh st cap inner_fuel;
      BPres.chunked_mark_inner_loop_preserves_well_formed
        mh st cap inner_fuel;
      let (mh_inner, _) =
        BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (fuel - 1 < fuel);
      chunked_mark_bounded_preserves_no_black_to_white
        mh_inner cap (fuel - 1);
      assert (
        BDefs.chunked_mark_bounded mh cap fuel ==
        BDefs.chunked_mark_bounded mh_inner cap (fuel - 1))
    end
  end
#pop-options
