module GC.Spec.ChunkedMajorGC.Correctness

module Seq = FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.Mark

module Obj = GC.Spec.Object
module Fields = GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module MH = GC.Spec.MajorHeap
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module DenseCorrectness = GC.Spec.Correctness
module SweepInv = GC.Spec.SweepInv
module BMark = GC.Spec.MarkBounded
module BMarkCorr = GC.Spec.MarkBoundedCorrectness
module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module SpecSweepCoalesce = GC.Spec.SweepCoalesce
module DenseFused = GC.Spec.SweepCoalesce.Defs
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMark = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMarkPres = GC.Spec.ChunkedMarkBounded.Preservation
module MarkDefs = GC.Spec.ChunkedMark.Defs
module ChunkedMarkMetadata = GC.Spec.ChunkedMarkBounded.Metadata
module RangePres = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module ChunkedMarkStackReady = GC.Spec.ChunkedMarkBounded.StackReady
module ChunkedMarkOuter = GC.Spec.ChunkedMarkBounded.OuterCompat
module ChunkedMajorGraph = GC.Spec.ChunkedMajorGC.Graph
module ChunkedLiveRange = GC.Spec.ChunkedSweepCoalesce.LiveRange

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let chunked_no_gray_or_black_objects (mh: MH.major_heap) : prop =
  forall (x: obj_addr). Seq.mem x (MH.major_objects mh) ==>
    SweepDefs.chunked_is_white mh x \/ SweepDefs.chunked_is_blue mh x

let chunked_gc_postcondition (mh: MH.major_heap) : prop =
  MH.well_formed_major_heap mh /\
  chunked_no_gray_or_black_objects mh

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let fields_object_after_zero_addr (g: heap) (x: obj_addr)
  : Lemma
      (requires Seq.mem x (Fields.objects zero_addr g))
      (ensures U64.v x >= U64.v zero_addr + U64.v mword)
  =
  Fields.objects_addresses_gt_start zero_addr g x
#pop-options

let chunked_gc_postcondition_intro (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)
      (ensures chunked_gc_postcondition mh)
  = ()

let chunked_gc_postcondition_elim (mh: MH.major_heap)
  : Lemma
      (requires chunked_gc_postcondition mh)
      (ensures
        MH.well_formed_major_heap mh /\
        chunked_no_gray_or_black_objects mh)
  = ()

let chunked_no_gray_or_black_single_chunk_from_dense (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_no_gray_or_black_objects
          (MH.single_chunk_major_heap g))
  =
  DenseCorrectness.gc_postcondition_elim g;
  MH.single_chunk_major_objects_compat g;
  let aux (x: obj_addr)
    : Lemma
        (requires Seq.mem x (MH.major_objects (MH.single_chunk_major_heap g)))
        (ensures
          SweepDefs.chunked_is_white (MH.single_chunk_major_heap g) x \/
          SweepDefs.chunked_is_blue (MH.single_chunk_major_heap g) x)
    =
    assert (Seq.mem x (Fields.objects zero_addr g));
    fields_object_after_zero_addr g x;
    SweepDefs.chunked_is_white_single_chunk_compat g x;
    SweepDefs.chunked_is_blue_single_chunk_compat g x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let chunked_gc_postcondition_single_chunk_from_dense (g: heap)
  : Lemma
      (requires DenseCorrectness.gc_postcondition g)
      (ensures
        chunked_gc_postcondition (MH.single_chunk_major_heap g))
  =
  DenseCorrectness.gc_postcondition_elim g;
  MH.single_chunk_major_heap_wf g;
  chunked_no_gray_or_black_single_chunk_from_dense g

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_mark_phase_preserves_shape
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         MH.major_objects marked == MH.major_objects mh))
  =
  ChunkedMarkPres.chunked_mark_bounded_preserves_well_formed mh cap fuel;
  ChunkedMarkPres.chunked_mark_bounded_preserves_major_objects mh cap fuel

let chunked_major_gc_bounded_mark_phase_preserves_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        Seq.mem obj
          (MH.major_objects (ChunkedMark.chunked_mark_bounded mh cap fuel)))
  =
  chunked_major_gc_bounded_mark_phase_preserves_shape mh cap fuel

let chunked_major_gc_bounded_mark_phase_marks_target_black
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
      (ensures
        SweepDefs.chunked_is_black
          (ChunkedMark.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMarkPres.chunked_mark_bounded_marks_target_black
    mh cap fuel target

let chunked_major_gc_bounded_mark_phase_pointer_classification_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (ensures
        ChunkedMajorGraph.chunked_major_pointer_classification_preserved
          mh (ChunkedMark.chunked_mark_bounded mh cap fuel))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  ChunkedMarkMetadata.chunked_mark_bounded_preserves_ranges mh cap fuel;
  let one (v: U64.t)
    : Lemma
        (ensures
          MarkDefs.chunked_is_pointer_field mh v ==
          MarkDefs.chunked_is_pointer_field marked v)
    =
    MarkDefs.chunked_is_pointer_field_step mh v;
    MarkDefs.chunked_is_pointer_field_step marked v;
    RangePres.same_chunk_ranges_preserves_is_major_pointer mh marked v
  in
  FStar.Classical.forall_intro one;
  ChunkedMajorGraph.chunked_major_pointer_classification_preserved_intro
    mh marked

let chunked_major_gc_bounded_mark_phase_field_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedMajorGraph.chunked_major_field_preserved
          mh (ChunkedMark.chunked_mark_bounded mh cap fuel) target)
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  chunked_major_gc_bounded_mark_phase_preserves_shape mh cap fuel;
  assert (MH.major_objects marked == MH.major_objects mh);
  ChunkedMajorGraph.chunked_major_vertex_intro mh target;
  ChunkedMajorGraph.chunked_major_vertex_intro marked target;
  ChunkedMarkMetadata.chunked_mark_bounded_preserves_wosize_of_object
    mh cap fuel target;
  let field_eq (i: U64.t{U64.v i >= 1})
    : Lemma
        (requires
          U64.v i <= U64.v (SweepDefs.chunked_wosize_of_object mh target))
        (ensures
          MarkDefs.chunked_get_field mh target i ==
          MarkDefs.chunked_get_field marked target i)
    =
    ChunkedMarkMetadata.chunked_mark_bounded_preserves_get_field
      mh cap fuel target i
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires field_eq);
  ChunkedMajorGraph.chunked_major_field_preserved_intro mh marked target

let chunked_major_gc_bounded_mark_phase_live_subgraph_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        (forall (target: obj_addr).
          live target ==> Seq.mem target (MH.major_objects mh)))
      (ensures
        ChunkedMajorGraph.chunked_major_live_subgraph_preserved
          mh (ChunkedMark.chunked_mark_bounded mh cap fuel) live)
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  let fields (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          ChunkedMajorGraph.chunked_major_field_preserved
            mh marked target)
    =
    assert (Seq.mem target (MH.major_objects mh));
    chunked_major_gc_bounded_mark_phase_field_preserved
      mh cap fuel target
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires fields);
  chunked_major_gc_bounded_mark_phase_pointer_classification_preserved
    mh cap fuel;
  ChunkedMajorGraph.chunked_major_live_subgraph_preserved_from_fields
    mh marked live
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_marked_live_subgraph_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_idx: obj_addr -> nat)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (j: nat). j < Seq.length marked ==>
           forall (o: obj_addr).
           Seq.mem o (MH.objects_in_chunk (Seq.index marked j)) ==>
           U64.v (SweepDefs.chunked_wosize_of_object marked o) ==
           MH.object_wosize_in_chunk (Seq.index marked j) o) /\
         (forall (target: obj_addr).
           live target ==>
           live_idx target < Seq.length marked /\
           Seq.mem target
             (MH.objects_in_chunk (Seq.index marked (live_idx target))) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           SweepDefs.chunked_is_black marked target /\
           U64.v (Obj.getWosize (live_hdr target)) ==
             MH.object_wosize_in_chunk
               (Seq.index marked (live_idx target)) target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  let (mh_final, fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
  ChunkedMajorGC.chunked_major_gc_bounded_equation mh cap fuel;
  SweepDefs.chunked_fused_sweep_coalesce_step marked;
  ChunkedLiveRange.chunked_fused_sweep_coalesce_live_subgraph_preserved
    marked 0UL live live_idx live_hdr
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_wosize_of_object_from_chunk_member
  (mh: MH.major_heap)
  (j: nat)
  (o: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        j < Seq.length mh /\
        Seq.mem o (MH.objects_in_chunk (Seq.index mh j)))
      (ensures
        U64.v (SweepDefs.chunked_wosize_of_object mh o) ==
        MH.object_wosize_in_chunk (Seq.index mh j) o)
  =
  let c = Seq.index mh j in
  MH.objects_in_chunk_member_header_fits c o;
  assert (MH.object_header_size_fits_in_chunk c o);
  assert (MH.word_in_chunk c (hd_address o));
  MH.lookup_chunk_index_word_in_chunk mh (hd_address o) j;
  assert (MH.lookup_chunk_index mh (hd_address o) == Some j);
  MH.read_word_in_major_at_lookup_index mh (hd_address o) j;
  let hdr = MH.read_word_in_chunk c (hd_address o) in
  assert (MH.read_word_in_major mh (hd_address o) == Some hdr);
  SweepDefs.chunked_read_header_step mh o;
  assert (SweepDefs.chunked_read_header mh o == Some hdr);
  SweepDefs.chunked_wosize_of_object_some mh o hdr;
  assert (SweepDefs.chunked_wosize_of_object mh o == Obj.getWosize hdr);
  assert (MH.object_wosize_in_chunk c o == U64.v (Obj.getWosize hdr))

let chunked_major_gc_bounded_marked_black_live_subgraph_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (j: nat). j < Seq.length marked ==>
           forall (o: obj_addr).
           Seq.mem o (MH.objects_in_chunk (Seq.index marked j)) ==>
           U64.v (SweepDefs.chunked_wosize_of_object marked o) ==
           MH.object_wosize_in_chunk (Seq.index marked j) o) /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           SweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  let live_idx (target: obj_addr) =
    MH.lookup_chunk_index_value marked (hd_address target) in
  let live_facts (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          live_idx target < Seq.length marked /\
          Seq.mem target
            (MH.objects_in_chunk (Seq.index marked (live_idx target))) /\
          SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target) /\
          SweepDefs.chunked_is_black marked target /\
          U64.v (Obj.getWosize (live_hdr target)) ==
            MH.object_wosize_in_chunk
              (Seq.index marked (live_idx target)) target)
    =
    assert (Seq.mem target (MH.major_objects marked));
    assert (SweepDefs.chunked_read_header marked target ==
      Some (live_hdr target));
    assert (SweepDefs.chunked_is_black marked target);
    SweepDefs.chunked_read_header_step marked target;
    assert (MH.read_word_in_major marked (hd_address target) ==
      Some (live_hdr target));
    MH.read_word_in_major_lookup_index
      marked (hd_address target) (live_hdr target);
    let idx = live_idx target in
    assert (idx < Seq.length marked);
    assert (MH.word_in_chunk (Seq.index marked idx) (hd_address target));
    MH.major_objects_member_in_lookup_chunk marked idx target;
    assert (Seq.mem target (MH.objects_in_chunk (Seq.index marked idx)));
    assert (MH.read_word_in_chunk (Seq.index marked idx) (hd_address target) ==
            live_hdr target);
    assert (MH.object_wosize_in_chunk (Seq.index marked idx) target ==
            U64.v (Obj.getWosize (live_hdr target)))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires live_facts);
  chunked_major_gc_bounded_marked_live_subgraph_preserved
    mh cap fuel live live_idx live_hdr

let chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           SweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  let wosize_facts (j: nat{j < Seq.length marked})
    : Lemma
        (ensures
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index marked j)) ==>
          U64.v (SweepDefs.chunked_wosize_of_object marked o) ==
          MH.object_wosize_in_chunk (Seq.index marked j) o)
    =
    let one (o: obj_addr)
      : Lemma
          (requires Seq.mem o (MH.objects_in_chunk (Seq.index marked j)))
          (ensures
            U64.v (SweepDefs.chunked_wosize_of_object marked o) ==
            MH.object_wosize_in_chunk (Seq.index marked j) o)
      =
      chunked_wosize_of_object_from_chunk_member marked j o
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
  in
  FStar.Classical.forall_intro wosize_facts;
  chunked_major_gc_bounded_marked_black_live_subgraph_preserved
    mh cap fuel live live_hdr
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           SweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  let (mh_final, fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
  let live_idx (target: obj_addr) =
    MH.lookup_chunk_index_value marked (hd_address target) in
  let wosize_facts (j: nat{j < Seq.length marked})
    : Lemma
        (ensures
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index marked j)) ==>
          U64.v (SweepDefs.chunked_wosize_of_object marked o) ==
          MH.object_wosize_in_chunk (Seq.index marked j) o)
    =
    let one (o: obj_addr)
      : Lemma
          (requires Seq.mem o (MH.objects_in_chunk (Seq.index marked j)))
          (ensures
            U64.v (SweepDefs.chunked_wosize_of_object marked o) ==
            MH.object_wosize_in_chunk (Seq.index marked j) o)
      =
      chunked_wosize_of_object_from_chunk_member marked j o
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
  in
  FStar.Classical.forall_intro wosize_facts;
  let live_facts (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          live_idx target < Seq.length marked /\
          Seq.mem target
            (MH.objects_in_chunk (Seq.index marked (live_idx target))) /\
          SweepDefs.chunked_is_black marked target)
    =
    assert (Seq.mem target (MH.major_objects marked));
    assert (SweepDefs.chunked_is_black marked target);
    SweepDefs.chunked_is_black_read_header marked target;
    match SweepDefs.chunked_read_header marked target with
    | None -> assert False
    | Some hdr ->
      SweepDefs.chunked_read_header_step marked target;
      assert (MH.read_word_in_major marked (hd_address target) ==
              Some hdr);
      MH.read_word_in_major_lookup_index
        marked (hd_address target) hdr;
      let idx = live_idx target in
      assert (idx < Seq.length marked);
      assert (MH.word_in_chunk (Seq.index marked idx) (hd_address target));
      MH.major_objects_member_in_lookup_chunk marked idx target;
      assert (Seq.mem target (MH.objects_in_chunk (Seq.index marked idx)))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires live_facts);
  ChunkedMajorGC.chunked_major_gc_bounded_equation mh cap fuel;
  SweepDefs.chunked_fused_sweep_coalesce_step marked;
  ChunkedLiveRange.chunked_fused_sweep_coalesce_live_subgraph_preserved_from_black_membership
    marked 0UL live live_idx
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap mh /\
         ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
             mh cap fuel target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  chunked_major_gc_bounded_mark_phase_preserves_shape mh cap fuel;
  let marked_live_facts (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          Seq.mem target (MH.major_objects marked) /\
          SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target) /\
          SweepDefs.chunked_is_black marked target)
    =
    assert (Seq.mem target (MH.major_objects mh));
    assert (MH.major_objects marked == MH.major_objects mh);
    assert (Seq.mem target (MH.major_objects marked));
    chunked_major_gc_bounded_mark_phase_marks_target_black
      mh cap fuel target;
    assert (SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target))
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires marked_live_facts);
  chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership
    mh cap fuel live live_hdr
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
            mh cap fuel target))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  chunked_major_gc_bounded_mark_phase_preserves_shape mh cap fuel;
  let marked_live_facts (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          Seq.mem target (MH.major_objects marked) /\
          SweepDefs.chunked_is_black marked target)
    =
    assert (Seq.mem target (MH.major_objects mh));
    assert (MH.major_objects marked == MH.major_objects mh);
    assert (Seq.mem target (MH.major_objects marked));
    chunked_major_gc_bounded_mark_phase_marks_target_black
      mh cap fuel target
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires marked_live_facts);
  chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership_no_header
    mh cap fuel live
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_live_subgraph_preserved_from_gray_rescan
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         fuel > 0 /\
         MH.well_formed_major_heap mh /\
         ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
         Seq.length (MH.major_objects mh) <= cap /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           ChunkedMark.chunked_is_gray mh target /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target))))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  let target_ready (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          Seq.mem target (MH.major_objects mh) /\
          SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target) /\
          ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
            mh cap fuel target)
    =
    assert (Seq.mem target (MH.major_objects mh));
    assert (ChunkedMark.chunked_is_gray mh target);
    assert (SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target));
    ChunkedMarkStackReady.chunked_mark_bounded_marks_rescan_member_ready
      mh cap fuel target
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires target_ready);
  chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready
    mh cap fuel live live_hdr
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_live_subgraph_preserved_from_gray_rescan_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          ChunkedMark.chunked_is_gray mh target))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let target_ready (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          Seq.mem target (MH.major_objects mh) /\
          ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
            mh cap fuel target)
    =
    assert (Seq.mem target (MH.major_objects mh));
    assert (ChunkedMark.chunked_is_gray mh target);
    ChunkedMarkStackReady.chunked_mark_bounded_marks_rescan_member_ready
      mh cap fuel target
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires target_ready);
  chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready_no_header
    mh cap fuel live
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         fuel > 0 /\
         MH.well_formed_major_heap mh /\
         ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
         Seq.length (MH.major_objects mh) <= cap /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           (ChunkedMark.chunked_is_gray mh target \/
            SweepDefs.chunked_is_black mh target) /\
           SweepDefs.chunked_read_header marked target ==
             Some (live_hdr target))))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  let target_ready (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          Seq.mem target (MH.major_objects mh) /\
          SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target) /\
          ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
            mh cap fuel target)
    =
    assert (Seq.mem target (MH.major_objects mh));
    assert (ChunkedMark.chunked_is_gray mh target \/
            SweepDefs.chunked_is_black mh target);
    assert (SweepDefs.chunked_read_header marked target ==
            Some (live_hdr target));
    ChunkedMarkStackReady.chunked_mark_bounded_marks_rescan_gray_or_black_member_ready
      mh cap fuel target
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires target_ready);
  chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready
    mh cap fuel live live_hdr

let chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          (ChunkedMark.chunked_is_gray mh target \/
           SweepDefs.chunked_is_black mh target)))
      (ensures
        (let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  let target_ready (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures
          Seq.mem target (MH.major_objects mh) /\
          ChunkedMarkPres.chunked_mark_bounded_marks_target_ready
            mh cap fuel target)
    =
    assert (Seq.mem target (MH.major_objects mh));
    assert (ChunkedMark.chunked_is_gray mh target \/
            SweepDefs.chunked_is_black mh target);
    ChunkedMarkStackReady.chunked_mark_bounded_marks_rescan_gray_or_black_member_ready
      mh cap fuel target
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires target_ready);
  chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready_no_header
    mh cap fuel live

let chunked_major_gc_bounded_live_subgraph_preserved_from_initial_gray_or_black_rescan_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          (ChunkedMark.chunked_is_gray mh target \/
           SweepDefs.chunked_is_black mh target)))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           mh mh_final live))
  =
  let marked = ChunkedMark.chunked_mark_bounded mh cap fuel in
  let (mh_final, fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
  let live_mem (target: obj_addr)
    : Lemma
        (requires live target)
        (ensures Seq.mem target (MH.major_objects mh))
    =
    assert (Seq.mem target (MH.major_objects mh))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires live_mem);
  chunked_major_gc_bounded_mark_phase_live_subgraph_preserved
    mh cap fuel live;
  chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan_no_header
    mh cap fuel live;
  ChunkedMajorGraph.chunked_major_live_subgraph_preserved_trans
    mh marked mh_final live
#pop-options

let bounded_mark_no_gray_for_fused
    (h_init: heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        fuel >= BMark.count_non_black h_init)
      (ensures
        (let h_mark = BMark.mark_bounded h_init cap fuel in
         forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr h_mark) ==>
           ~(Obj.is_gray x h_mark)))
  =
  let h_mark = BMark.mark_bounded h_init cap fuel in
  BMark.mark_bounded_completes h_init cap fuel;
  let no_gray (x: obj_addr)
    : Lemma
        (requires Seq.mem x (Fields.objects zero_addr h_mark))
        (ensures ~(Obj.is_gray x h_mark))
    =
    SweepInv.no_gray_elim x h_mark
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_gray)

let chunked_major_gc_bounded_single_chunk_postcondition
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         chunked_gc_postcondition mh_final))
  =
  let h_mark = BMark.mark_bounded h_init cap fuel in
  BMarkCorr.mark_bounded_satisfies_mark_post h_init roots fp cap fuel;
  DenseCorrectness.mark_post_elim_wfh h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_density h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_fp h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_no_grey h_init h_mark roots fp;
  bounded_mark_no_gray_for_fused h_init cap fuel;
  assert (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr h_mark) ==>
    ~(Obj.is_gray x h_mark));
  SpecSweepCoalesce.fused_eq_sweep_coalesce h_mark fp;
  DenseCorrectness.gc_postcondition_gen h_init h_mark roots fp;
  ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
    h_init cap fuel;
  let (h_final, fp_final) = DenseFused.fused_sweep_coalesce h_mark in
  assert (DenseCorrectness.gc_postcondition h_final);
  chunked_gc_postcondition_single_chunk_from_dense h_final

let chunked_major_gc_bounded_single_chunk_full_correctness
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let h_mark = BMark.mark_bounded h_init cap fuel in
         let (h_final, dense_fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         mh_final == MH.single_chunk_major_heap h_final /\
         DenseCorrectness.full_gc_correctness h_init h_final roots /\
         chunked_gc_postcondition mh_final))
  =
  let h_mark = BMark.mark_bounded h_init cap fuel in
  BMarkCorr.mark_bounded_satisfies_mark_post h_init roots fp cap fuel;
  DenseCorrectness.mark_post_elim_wfh h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_density h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_fp h_init h_mark roots fp;
  bounded_mark_no_gray_for_fused h_init cap fuel;
  assert (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr h_mark) ==>
    ~(Obj.is_gray x h_mark));
  SpecSweepCoalesce.fused_eq_sweep_coalesce h_mark fp;
  DenseCorrectness.full_gc_correctness_through_coalesce_gen
    h_init h_mark roots fp;
  ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
    h_init cap fuel;
  let (h_final, dense_fp_final) =
    DenseFused.fused_sweep_coalesce h_mark in
  assert (DenseCorrectness.full_gc_correctness h_init h_final roots);
  chunked_major_gc_bounded_single_chunk_postcondition
    h_init roots fp cap fuel

let chunked_major_gc_bounded_single_chunk_dense_graph_pillars
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let h_mark = BMark.mark_bounded h_init cap fuel in
         let (h_final, dense_fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         mh_final == MH.single_chunk_major_heap h_final /\
         DenseCorrectness.major_gc_live_subgraph_isomorphism
           h_init h_final roots /\
         DenseCorrectness.major_gc_unreachable_final_blue
           h_init h_final roots))
  =
  let h_mark = BMark.mark_bounded h_init cap fuel in
  BMarkCorr.mark_bounded_satisfies_mark_post h_init roots fp cap fuel;
  DenseCorrectness.mark_post_elim_wfh h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_density h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_fp h_init h_mark roots fp;
  bounded_mark_no_gray_for_fused h_init cap fuel;
  assert (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr h_mark) ==>
    ~(Obj.is_gray x h_mark));
  SpecSweepCoalesce.fused_eq_sweep_coalesce h_mark fp;
  DenseCorrectness.major_gc_live_subgraph_isomorphism_gen
    h_init h_mark roots fp;
  DenseCorrectness.major_gc_unreachable_final_blue_gen
    h_init h_mark roots fp;
  ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
    h_init cap fuel;
  let (h_final, dense_fp_final) =
    DenseFused.fused_sweep_coalesce h_mark in
  assert (DenseCorrectness.major_gc_live_subgraph_isomorphism
    h_init h_final roots);
  assert (DenseCorrectness.major_gc_unreachable_final_blue
    h_init h_final roots)

let chunked_major_gc_bounded_single_chunk_live_field_data_preserved
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         forall (x: obj_addr).
           DenseCorrectness.heap_reachable h_init roots x ==>
           ChunkedMajorGraph.chunked_major_field_data_preserved
             (MH.single_chunk_major_heap h_init)
             mh_final
             x))
  =
  chunked_major_gc_bounded_single_chunk_dense_graph_pillars
    h_init roots fp cap fuel;
  let h_mark = BMark.mark_bounded h_init cap fuel in
  let (h_final, dense_fp_final) =
    DenseFused.fused_sweep_coalesce h_mark in
  let (mh_final, chunked_fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded
      (MH.single_chunk_major_heap h_init) cap fuel in
  let aux (x: obj_addr)
    : Lemma
        (requires DenseCorrectness.heap_reachable h_init roots x)
        (ensures
          ChunkedMajorGraph.chunked_major_field_data_preserved
            (MH.single_chunk_major_heap h_init)
            mh_final
            x)
    =
    assert (mh_final == MH.single_chunk_major_heap h_final);
    assert (DenseCorrectness.major_gc_live_subgraph_isomorphism
      h_init h_final roots);
    assert (Seq.mem x (Fields.objects zero_addr h_final));
    graph_vertices_mem h_init x;
    assert (Seq.mem x (Fields.objects zero_addr h_init));
    fields_object_after_zero_addr h_init x;
    ChunkedMajorGraph.chunked_major_field_data_preserved_single_chunk_from_dense
      h_init h_final x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let bounded_major_gc_live_wosize_preserved_dense
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
    (x: obj_addr)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices) /\
        DenseCorrectness.heap_reachable h_init roots x)
      (ensures
        (let h_mark = BMark.mark_bounded h_init cap fuel in
         let (h_final, dense_fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         wosize_of_object x h_final == wosize_of_object x h_init))
  =
  let h_mark = BMark.mark_bounded h_init cap fuel in
  BMarkCorr.mark_color_inv_init h_init;
  BMarkCorr.mark_bounded_preserves_color_inv h_init h_init cap fuel;
  BMarkCorr.mark_bounded_reachable_is_black h_init roots cap fuel;
  BMarkCorr.mark_bounded_satisfies_mark_post h_init roots fp cap fuel;
  DenseCorrectness.mark_post_elim_wfh h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_density h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_fp h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_objects h_init h_mark roots fp;
  DenseCorrectness.mark_post_elim_no_grey h_init h_mark roots fp;
  bounded_mark_no_gray_for_fused h_init cap fuel;
  assert (forall (y: obj_addr). Seq.mem y (Fields.objects zero_addr h_mark) ==>
    ~(Obj.is_gray y h_mark));
  SpecSweepCoalesce.fused_eq_sweep_coalesce h_mark fp;
  DenseCorrectness.sweep_post_sweep_strong_gen h_init h_mark roots fp;
  let graph = create_graph h_init in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  graph_vertices_mem h_init x;
  assert (Seq.mem x (Fields.objects zero_addr h_init));
  assert (Seq.mem x (Fields.objects zero_addr h_mark));
  assert (Obj.is_black x h_mark);
  assert (wosize_of_object x h_mark == wosize_of_object x h_init);
  let h_sweep = fst (SpecSweep.sweep h_mark fp) in
  SpecSweep.sweep_preserves_wosize_black h_mark fp x;
  SpecSweep.sweep_black_survives h_mark fp;
  assert (Seq.mem x (Fields.objects zero_addr h_sweep));
  assert (Obj.is_white x h_sweep);
  SpecCoalesce.coalesce_preserves_survivor_header h_sweep x;
  let (h_final, dense_fp_final) =
    DenseFused.fused_sweep_coalesce h_mark in
  assert (h_final == fst (SpecCoalesce.coalesce h_sweep));
  wosize_of_object_spec x h_sweep;
  wosize_of_object_spec x h_final

let chunked_major_gc_bounded_single_chunk_live_field_preserved
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         forall (x: obj_addr).
           DenseCorrectness.heap_reachable h_init roots x ==>
           ChunkedMajorGraph.chunked_major_field_preserved
             (MH.single_chunk_major_heap h_init)
             mh_final
             x))
  =
  chunked_major_gc_bounded_single_chunk_dense_graph_pillars
    h_init roots fp cap fuel;
  let h_mark = BMark.mark_bounded h_init cap fuel in
  let (h_final, dense_fp_final) =
    DenseFused.fused_sweep_coalesce h_mark in
  let (mh_final, chunked_fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded
      (MH.single_chunk_major_heap h_init) cap fuel in
  let aux (x: obj_addr)
    : Lemma
        (requires DenseCorrectness.heap_reachable h_init roots x)
        (ensures
          ChunkedMajorGraph.chunked_major_field_preserved
            (MH.single_chunk_major_heap h_init)
            mh_final
            x)
    =
    assert (mh_final == MH.single_chunk_major_heap h_final);
    assert (DenseCorrectness.major_gc_live_subgraph_isomorphism
      h_init h_final roots);
    assert (Seq.mem x (Fields.objects zero_addr h_final));
    graph_vertices_mem h_init x;
    assert (Seq.mem x (Fields.objects zero_addr h_init));
    fields_object_after_zero_addr h_init x;
    bounded_major_gc_live_wosize_preserved_dense
      h_init roots fp cap fuel x;
    ChunkedMajorGraph.chunked_major_field_preserved_single_chunk_from_dense
      h_init h_final x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let bounded_major_gc_live_successors_preserved_at
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
    (x: obj_addr)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices) /\
        DenseCorrectness.heap_reachable h_init roots x)
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         ChunkedMajorGraph.chunked_major_successors_preserved
           (MH.single_chunk_major_heap h_init)
           mh_final
           x))
  =
  chunked_major_gc_bounded_single_chunk_dense_graph_pillars
    h_init roots fp cap fuel;
  let h_mark = BMark.mark_bounded h_init cap fuel in
  let (h_final, dense_fp_final) =
    DenseFused.fused_sweep_coalesce h_mark in
  let (mh_final, chunked_fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded
      (MH.single_chunk_major_heap h_init) cap fuel in
  ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
    h_init cap fuel;
  ChunkedMajorGraph.chunked_major_pointer_classification_preserved_single_chunk
    h_init h_final;
  assert (mh_final == MH.single_chunk_major_heap h_final);
  assert (DenseCorrectness.major_gc_live_subgraph_isomorphism
    h_init h_final roots);
  assert (Seq.mem x (Fields.objects zero_addr h_final));
  graph_vertices_mem h_init x;
  assert (Seq.mem x (Fields.objects zero_addr h_init));
  fields_object_after_zero_addr h_init x;
  bounded_major_gc_live_wosize_preserved_dense
    h_init roots fp cap fuel x;
  ChunkedMajorGraph.chunked_major_field_preserved_single_chunk_from_dense
    h_init h_final x;
  assert (ChunkedMajorGraph.chunked_major_field_preserved
    (MH.single_chunk_major_heap h_init) mh_final x);
  assert (ChunkedMajorGraph.chunked_major_pointer_classification_preserved
    (MH.single_chunk_major_heap h_init) mh_final);
  ChunkedMajorGraph.chunked_major_successors_preserved_from_fields
    (MH.single_chunk_major_heap h_init)
    mh_final
    x

let chunked_major_gc_bounded_single_chunk_live_successors_preserved
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         forall (x: obj_addr).
           DenseCorrectness.heap_reachable h_init roots x ==>
           ChunkedMajorGraph.chunked_major_successors_preserved
             (MH.single_chunk_major_heap h_init)
             mh_final
             x))
  =
  let (mh_final, chunked_fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded
      (MH.single_chunk_major_heap h_init) cap fuel in
  let aux (x: obj_addr)
    : Lemma
        (requires DenseCorrectness.heap_reachable h_init roots x)
        (ensures
          ChunkedMajorGraph.chunked_major_successors_preserved
            (MH.single_chunk_major_heap h_init)
            mh_final
            x)
    =
    chunked_major_gc_bounded_single_chunk_dense_graph_pillars
      h_init roots fp cap fuel;
    let h_mark = BMark.mark_bounded h_init cap fuel in
    let (h_final, dense_fp_final) =
      DenseFused.fused_sweep_coalesce h_mark in
    let (mh_final, chunked_fp_final) =
      ChunkedMajorGC.chunked_major_gc_bounded
        (MH.single_chunk_major_heap h_init) cap fuel in
    ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
      h_init cap fuel;
    ChunkedMajorGraph.chunked_major_pointer_classification_preserved_single_chunk
      h_init h_final;
    assert (mh_final == MH.single_chunk_major_heap h_final);
    assert (DenseCorrectness.major_gc_live_subgraph_isomorphism
      h_init h_final roots);
    assert (Seq.mem x (Fields.objects zero_addr h_final));
    graph_vertices_mem h_init x;
    assert (Seq.mem x (Fields.objects zero_addr h_init));
    fields_object_after_zero_addr h_init x;
    bounded_major_gc_live_wosize_preserved_dense
      h_init roots fp cap fuel x;
    ChunkedMajorGraph.chunked_major_field_preserved_single_chunk_from_dense
      h_init h_final x;
    assert (ChunkedMajorGraph.chunked_major_field_preserved
      (MH.single_chunk_major_heap h_init) mh_final x);
    assert (ChunkedMajorGraph.chunked_major_pointer_classification_preserved
      (MH.single_chunk_major_heap h_init) mh_final);
    ChunkedMajorGraph.chunked_major_successors_preserved_from_fields
      (MH.single_chunk_major_heap h_init)
      mh_final
      x;
    assert (ChunkedMajorGraph.chunked_major_successors_preserved
      (MH.single_chunk_major_heap h_init) mh_final x);
    ChunkedMajorGraph.chunked_major_successors_preserved_elim
      (MH.single_chunk_major_heap h_init)
      mh_final
      x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let chunked_major_gc_bounded_single_chunk_live_edges_preserved
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         forall (x: obj_addr).
           DenseCorrectness.heap_reachable h_init roots x ==>
           forall (y: obj_addr).
             ChunkedMajorGraph.chunked_major_edge
               (MH.single_chunk_major_heap h_init) x y <==>
             ChunkedMajorGraph.chunked_major_edge mh_final x y))
  =
  chunked_major_gc_bounded_single_chunk_live_successors_preserved
    h_init roots fp cap fuel;
  let edge_eq (x: obj_addr)
    : Lemma
        (requires DenseCorrectness.heap_reachable h_init roots x)
        (ensures
          (let (mh_final, chunked_fp_final) =
             ChunkedMajorGC.chunked_major_gc_bounded
               (MH.single_chunk_major_heap h_init) cap fuel in
           forall (y: obj_addr).
             ChunkedMajorGraph.chunked_major_edge
               (MH.single_chunk_major_heap h_init) x y <==>
             ChunkedMajorGraph.chunked_major_edge mh_final x y))
    =
    chunked_major_gc_bounded_single_chunk_dense_graph_pillars
      h_init roots fp cap fuel;
    let h_mark = BMark.mark_bounded h_init cap fuel in
    let (h_final, dense_fp_final) =
      DenseFused.fused_sweep_coalesce h_mark in
    let (mh_final, chunked_fp_final) =
      ChunkedMajorGC.chunked_major_gc_bounded
        (MH.single_chunk_major_heap h_init) cap fuel in
    ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
      h_init cap fuel;
    ChunkedMajorGraph.chunked_major_pointer_classification_preserved_single_chunk
      h_init h_final;
    assert (mh_final == MH.single_chunk_major_heap h_final);
    assert (DenseCorrectness.major_gc_live_subgraph_isomorphism
      h_init h_final roots);
    assert (Seq.mem x (Fields.objects zero_addr h_final));
    graph_vertices_mem h_init x;
    assert (Seq.mem x (Fields.objects zero_addr h_init));
    fields_object_after_zero_addr h_init x;
    bounded_major_gc_live_wosize_preserved_dense
      h_init roots fp cap fuel x;
    ChunkedMajorGraph.chunked_major_field_preserved_single_chunk_from_dense
      h_init h_final x;
    assert (ChunkedMajorGraph.chunked_major_field_preserved
      (MH.single_chunk_major_heap h_init) mh_final x);
    assert (ChunkedMajorGraph.chunked_major_pointer_classification_preserved
      (MH.single_chunk_major_heap h_init) mh_final);
    ChunkedMajorGraph.chunked_major_successors_preserved_from_fields
      (MH.single_chunk_major_heap h_init)
      mh_final
      x;
    assert (ChunkedMajorGraph.chunked_major_successors_preserved
      (MH.single_chunk_major_heap h_init) mh_final x);
    ChunkedMajorGraph.chunked_major_successors_preserved_elim
      (MH.single_chunk_major_heap h_init)
      mh_final
      x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires edge_eq)

let chunked_major_gc_bounded_single_chunk_live_subgraph_preserved
    (h_init: heap)
    (roots: Seq.seq obj_addr)
    (fp: U64.t)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        well_formed_heap h_init /\
        Seq.length (objects zero_addr h_init) > 0 /\
        SweepInv.heap_objects_dense h_init /\
        root_props h_init roots /\
        GC.Spec.Sweep.fp_in_heap fp h_init /\
        no_black_objects h_init /\
        no_pointer_to_blue h_init /\
        no_scan_invariant h_init /\
        fuel >= BMark.count_non_black h_init /\
        ChunkedMarkOuter.mark_bounded_single_chunk_ready h_init cap fuel /\
        (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) /\
          (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
        (let graph = create_graph h_init in
         let roots' = HeapGraph.coerce_to_vertex_list roots in
         graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap h_init) cap fuel in
         ChunkedMajorGraph.chunked_major_live_subgraph_preserved
           (MH.single_chunk_major_heap h_init)
           mh_final
           (fun (x: obj_addr) -> DenseCorrectness.heap_reachable h_init roots x)))
  =
  chunked_major_gc_bounded_single_chunk_dense_graph_pillars
    h_init roots fp cap fuel;
  chunked_major_gc_bounded_single_chunk_live_edges_preserved
    h_init roots fp cap fuel;
  let h_mark = BMark.mark_bounded h_init cap fuel in
  let (h_final, dense_fp_final) =
    DenseFused.fused_sweep_coalesce h_mark in
  let (mh_final, chunked_fp_final) =
    ChunkedMajorGC.chunked_major_gc_bounded
      (MH.single_chunk_major_heap h_init) cap fuel in
  ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat
    h_init cap fuel;
  assert (mh_final == MH.single_chunk_major_heap h_final);
  assert (DenseCorrectness.major_gc_live_subgraph_isomorphism
    h_init h_final roots);
  let live = fun (x: obj_addr) -> DenseCorrectness.heap_reachable h_init roots x in
  let vertices (x: obj_addr)
    : Lemma
        (requires live x)
        (ensures
          ChunkedMajorGraph.chunked_major_vertex
            (MH.single_chunk_major_heap h_init) x /\
          ChunkedMajorGraph.chunked_major_vertex mh_final x)
    =
    graph_vertices_mem h_init x;
    assert (Seq.mem x (Fields.objects zero_addr h_init));
    ChunkedMajorGraph.chunked_major_vertex_single_chunk_compat h_init x;
    assert (Seq.mem x (Fields.objects zero_addr h_final));
    ChunkedMajorGraph.chunked_major_vertex_single_chunk_compat h_final x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires vertices);
  let edge_src (x: obj_addr)
    : Lemma
        (requires live x)
        (ensures
          forall (y: obj_addr).
          ChunkedMajorGraph.chunked_major_edge
            (MH.single_chunk_major_heap h_init) x y <==>
          ChunkedMajorGraph.chunked_major_edge mh_final x y)
    =
    bounded_major_gc_live_successors_preserved_at
      h_init roots fp cap fuel x;
    assert (ChunkedMajorGraph.chunked_major_successors_preserved
      (MH.single_chunk_major_heap h_init) mh_final x);
    ChunkedMajorGraph.chunked_major_successors_preserved_elim
      (MH.single_chunk_major_heap h_init)
      mh_final
      x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires edge_src);
  ChunkedMajorGraph.chunked_major_live_subgraph_preserved_intro
    (MH.single_chunk_major_heap h_init)
    mh_final
    live
