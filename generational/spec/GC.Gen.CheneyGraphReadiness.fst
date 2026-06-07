module GC.Gen.CheneyGraphReadiness

open FStar.Seq
module U64 = FStar.UInt64
module SeqProps = FStar.Seq.Properties
module ML = FStar.Math.Lemmas

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote
open GC.Gen.Cheney

module MH = GC.Spec.MajorHeap
module SpecMajorAlloc = GC.Spec.MajorAllocator
module PromotionDemand = GC.Gen.PromotionDemand
module ChunkedCheney = GC.Gen.ChunkedCheney
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module CC = GC.Gen.CheneyCorrectness
module CReach = GC.Gen.ChunkedReachabilityBridge

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
private let aligned_gt_ge_plus_mword (x z: nat)
  : Lemma
    (requires x > z /\ x % U64.v mword == 0 /\ z % U64.v mword == 0)
    (ensures x >= z + U64.v mword)
  =
  if x < z + U64.v mword then begin
    assert (x - z > 0);
    assert (x - z < U64.v mword);
    ML.lemma_mod_sub_distr x z (U64.v mword);
    assert ((x - z) % U64.v mword == 0);
    ML.small_mod (x - z) (U64.v mword);
    assert False
  end
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
private let rec major_object_above_minor_from_chunks
  (major: MH.major_heap) (obj: obj_addr)
  : Lemma
    (requires
      chunked_major_chunks_above_minor major /\
      Seq.mem obj (MH.major_objects major))
    (ensures U64.v obj >= minor_heap_size)
    (decreases Seq.length major)
  =
  if Seq.length major = 0 then
    assert False
  else begin
    assert (Seq.length major > 0);
    let hd = Seq.head major in
    let tl = Seq.tail major in
    assert (Seq.length tl < Seq.length major);
    assert (MH.major_objects major ==
            Seq.append (MH.objects_in_chunk hd) (MH.major_objects tl));
    SeqProps.lemma_mem_append (MH.objects_in_chunk hd) (MH.major_objects tl);
    if Seq.mem obj (MH.objects_in_chunk hd) then begin
      MH.objects_in_chunk_member_in_chunk hd obj;
      assert (U64.v obj >= MH.chunk_start hd + U64.v mword);
      assert (hd == Seq.index major 0);
      assert (U64.v (Seq.index major 0).base >= minor_heap_size);
      assert (U64.v hd.base >= minor_heap_size);
      assert (U64.v obj >= minor_heap_size)
    end else begin
      assert (Seq.mem obj (MH.major_objects tl));
      let tl_chunks_above (i: nat{i < Seq.length tl})
        : Lemma (U64.v (Seq.index tl i).base >= minor_heap_size)
        =
        let imajor : n:nat{n < Seq.length major} = i + 1 in
        assert (Seq.index tl i == Seq.index major imajor)
      in
      FStar.Classical.forall_intro tl_chunks_above;
      assert (chunked_major_chunks_above_minor tl);
      major_object_above_minor_from_chunks tl obj
    end
  end

let chunked_major_chunks_above_minor_objects_above_minor
  (major: MH.major_heap)
  : Lemma
    (requires chunked_major_chunks_above_minor major)
    (ensures chunked_major_objects_above_minor major)
  =
  let prove (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (MH.major_objects major))
      (ensures U64.v obj >= minor_heap_size)
    =
    major_object_above_minor_from_chunks major obj
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove)

let chunked_major_chunks_above_minor_single_chunk
  (g: heap)
  : Lemma
    (ensures chunked_major_chunks_above_minor (MH.single_chunk_major_heap g))
  =
  zero_addr_above_minor ();
  let prove (i: nat{i < Seq.length (MH.single_chunk_major_heap g)})
    : Lemma
      (ensures
        U64.v (Seq.index (MH.single_chunk_major_heap g) i).base >=
        minor_heap_size)
    =
    assert (i == 0);
    assert (Seq.index (MH.single_chunk_major_heap g) i ==
            MH.single_chunk_of_heap g);
    assert ((MH.single_chunk_of_heap g).base == zero_addr)
  in
  FStar.Classical.forall_intro prove

let chunked_major_objects_above_minor_single_chunk
  (g: heap)
  : Lemma
    (ensures chunked_major_objects_above_minor (MH.single_chunk_major_heap g))
  =
  chunked_major_chunks_above_minor_single_chunk g;
  chunked_major_chunks_above_minor_objects_above_minor
    (MH.single_chunk_major_heap g)

let chunked_major_objects_above_minor_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      U64.v fresh.base >= minor_heap_size)
    (ensures
      chunked_major_objects_above_minor
        (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  let er = SpecMajorAlloc.expand_major_heap major fresh fp in
  SpecMajorAlloc.expand_major_heap_objects major fresh fp;
  SpecMajorAlloc.expand_major_heap_link major fresh fp;
  let prove (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (MH.major_objects er.major_out))
      (ensures U64.v obj >= minor_heap_size)
    =
    assert (MH.major_objects er.major_out ==
            Seq.cons er.fp_out (MH.major_objects major));
    SeqProps.mem_cons er.fp_out (MH.major_objects major);
    if obj = er.fp_out then begin
      SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
      assert (er.fp_out == SpecMajorAlloc.fresh_chunk_object fresh);
      assert (U64.v obj >= U64.v fresh.base + U64.v mword);
      assert (U64.v obj >= minor_heap_size)
    end else begin
      assert (Seq.mem obj (MH.major_objects major));
      assert (U64.v obj >= minor_heap_size)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove)

let chunked_major_objects_above_minor_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       U64.v fresh.base >= U64.v zero_addr))
    (ensures
      (let r =
         SpecMajorAlloc.ensure_major_head_capacity_spec
           major fp fuel needed fresh in
       chunked_major_objects_above_minor r.capacity_major_out))
  =
  if SpecMajorAlloc.major_fl_head_wosize major fp >= needed then
    ()
  else begin
    zero_addr_above_minor ();
    assert (U64.v fresh.base >= minor_heap_size);
    chunked_major_objects_above_minor_expand_major_heap major fresh fp
  end

private let rec major_object_pointer_field_from_chunks
  (major: MH.major_heap) (obj: obj_addr)
  : Lemma
    (requires
      chunked_major_chunks_above_zero_addr major /\
      Seq.mem obj (MH.major_objects major))
    (ensures GC.Spec.Fields.is_pointer_field obj)
    (decreases Seq.length major)
  =
  if Seq.length major = 0 then
    assert False
  else begin
    assert (Seq.length major > 0);
    let hd = Seq.head major in
    let tl = Seq.tail major in
    assert (Seq.length tl < Seq.length major);
    assert (MH.major_objects major ==
            Seq.append (MH.objects_in_chunk hd) (MH.major_objects tl));
    SeqProps.lemma_mem_append (MH.objects_in_chunk hd) (MH.major_objects tl);
    if Seq.mem obj (MH.objects_in_chunk hd) then begin
      MH.objects_in_chunk_member_in_chunk hd obj;
      assert (U64.v obj >= MH.chunk_start hd + U64.v mword);
      assert (hd == Seq.index major 0);
      assert (U64.v (Seq.index major 0).base >= U64.v zero_addr);
      assert (U64.v hd.base >= U64.v zero_addr);
      assert (U64.v obj >= U64.v zero_addr + U64.v mword);
      assert (U64.v obj < heap_size);
      assert (U64.v obj % U64.v mword == 0)
    end else begin
      assert (Seq.mem obj (MH.major_objects tl));
      let tl_chunks_above_zero (i: nat{i < Seq.length tl})
        : Lemma (U64.v (Seq.index tl i).base >= U64.v zero_addr)
        =
        let imajor : n:nat{n < Seq.length major} = i + 1 in
        assert (Seq.index tl i == Seq.index major imajor)
      in
      FStar.Classical.forall_intro tl_chunks_above_zero;
      assert (chunked_major_chunks_above_zero_addr tl);
      major_object_pointer_field_from_chunks tl obj
    end
  end

let chunked_major_chunks_above_zero_addr_objects_are_pointer_fields
  (major: MH.major_heap)
  : Lemma
    (requires chunked_major_chunks_above_zero_addr major)
    (ensures chunked_major_objects_are_pointer_fields major)
  =
  let prove (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (MH.major_objects major))
      (ensures GC.Spec.Fields.is_pointer_field obj)
    =
    major_object_pointer_field_from_chunks major obj
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove)

let chunked_major_chunks_above_zero_addr_single_chunk
  (g: heap)
  : Lemma
    (ensures chunked_major_chunks_above_zero_addr (MH.single_chunk_major_heap g))
  =
  let prove (i: nat{i < Seq.length (MH.single_chunk_major_heap g)})
    : Lemma
      (ensures
        U64.v (Seq.index (MH.single_chunk_major_heap g) i).base >=
        U64.v zero_addr)
    =
    assert (i == 0);
    assert (Seq.index (MH.single_chunk_major_heap g) i ==
            MH.single_chunk_of_heap g);
    assert ((MH.single_chunk_of_heap g).base == zero_addr)
  in
  FStar.Classical.forall_intro prove

let chunked_major_chunks_above_zero_addr_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_major_chunks_above_zero_addr major /\
      U64.v fresh.base >= U64.v zero_addr)
    (ensures
      chunked_major_chunks_above_zero_addr
        (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  let er = SpecMajorAlloc.expand_major_heap major fresh fp in
  let r = SpecMajorAlloc.init_fresh_chunk fresh fp in
  SpecMajorAlloc.init_fresh_chunk_preserves_range fresh fp;
  assert (er.major_out == MH.add_chunk major r.chunk_out);
  let prove (i: nat{i < Seq.length er.major_out})
    : Lemma
      (ensures U64.v (Seq.index er.major_out i).base >= U64.v zero_addr)
    =
    if i <= 0 then begin
      assert (i == 0);
      assert (Seq.index er.major_out i == r.chunk_out);
      assert (r.chunk_out.base == fresh.base)
    end else begin
      assert (i > 0);
      assert (er.major_out == Seq.cons r.chunk_out major);
      assert (Seq.length er.major_out == Seq.length major + 1);
      assert (i - 1 >= 0);
      assert (i - 1 < Seq.length major);
      let imajor : n:nat{n < Seq.length major} = i - 1 in
      assert (Seq.index er.major_out i == Seq.index major imajor)
    end
  in
  FStar.Classical.forall_intro prove

let chunked_major_chunks_above_zero_addr_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_major_chunks_above_zero_addr major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       U64.v fresh.base >= U64.v zero_addr))
    (ensures
      (let r =
         SpecMajorAlloc.ensure_major_head_capacity_spec
           major fp fuel needed fresh in
       chunked_major_chunks_above_zero_addr r.capacity_major_out))
  =
  if SpecMajorAlloc.major_fl_head_wosize major fp >= needed then
    ()
  else
    chunked_major_chunks_above_zero_addr_expand_major_heap major fresh fp

let chunked_major_chunks_above_zero_addr_chunks_above_minor
  (major: MH.major_heap)
  : Lemma
    (requires chunked_major_chunks_above_zero_addr major)
    (ensures chunked_major_chunks_above_minor major)
  =
  zero_addr_above_minor ();
  let prove (i: nat{i < Seq.length major})
    : Lemma
      (ensures U64.v (Seq.index major i).base >= minor_heap_size)
    =
    assert (U64.v (Seq.index major i).base >= U64.v zero_addr);
    assert (U64.v (Seq.index major i).base >= minor_heap_size)
  in
  FStar.Classical.forall_intro prove

let chunked_major_chunks_above_zero_addr_objects_above_minor
  (major: MH.major_heap)
  : Lemma
    (requires chunked_major_chunks_above_zero_addr major)
    (ensures chunked_major_objects_above_minor major)
  =
  chunked_major_chunks_above_zero_addr_chunks_above_minor major;
  chunked_major_chunks_above_minor_objects_above_minor major

#pop-options

#push-options "--split_queries always --z3rlimit 20 --fuel 1 --ifuel 0"
let chunked_major_objects_are_pointer_fields_single_chunk
  (g: heap)
  : Lemma
    (ensures
      chunked_major_objects_are_pointer_fields (MH.single_chunk_major_heap g))
  =
  MH.single_chunk_major_objects_compat g;
  let prove (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (MH.major_objects (MH.single_chunk_major_heap g)))
      (ensures GC.Spec.Fields.is_pointer_field obj)
    =
    assert (Seq.mem obj (GC.Spec.Fields.objects zero_addr g));
    GC.Spec.Fields.objects_addresses_gt_start zero_addr g obj;
    assert (U64.v obj > U64.v zero_addr);
    aligned_gt_ge_plus_mword (U64.v obj) (U64.v zero_addr);
    assert (U64.v obj >= U64.v zero_addr + U64.v mword);
    assert (U64.v obj < heap_size);
    assert (U64.v obj % U64.v mword == 0)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove)

let chunked_major_objects_are_pointer_fields_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_major_objects_are_pointer_fields major /\
      U64.v fresh.base >= U64.v zero_addr)
    (ensures
      chunked_major_objects_are_pointer_fields
        (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  let er = SpecMajorAlloc.expand_major_heap major fresh fp in
  SpecMajorAlloc.expand_major_heap_objects major fresh fp;
  SpecMajorAlloc.expand_major_heap_link major fresh fp;
  let prove (obj: obj_addr)
    : Lemma
      (requires Seq.mem obj (MH.major_objects er.major_out))
      (ensures GC.Spec.Fields.is_pointer_field obj)
    =
    assert (MH.major_objects er.major_out ==
            Seq.cons er.fp_out (MH.major_objects major));
    SeqProps.mem_cons er.fp_out (MH.major_objects major);
    if obj = er.fp_out then begin
      SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
      assert (er.fp_out == SpecMajorAlloc.fresh_chunk_object fresh);
      assert (U64.v obj >= U64.v fresh.base + U64.v mword);
      assert (U64.v obj >= U64.v zero_addr + U64.v mword);
      assert (U64.v obj < heap_size);
      assert (U64.v obj % U64.v mword == 0)
    end else begin
      assert (Seq.mem obj (MH.major_objects major));
      assert (GC.Spec.Fields.is_pointer_field obj)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove)

let chunked_major_objects_are_pointer_fields_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_major_objects_are_pointer_fields major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       U64.v fresh.base >= U64.v zero_addr))
    (ensures
      (let r =
         SpecMajorAlloc.ensure_major_head_capacity_spec
           major fp fuel needed fresh in
       chunked_major_objects_are_pointer_fields r.capacity_major_out))
  =
  if SpecMajorAlloc.major_fl_head_wosize major fp >= needed then
    ()
  else
    chunked_major_objects_are_pointer_fields_expand_major_heap major fresh fp
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
private let minor_major_edge_target_above_minor_witness
  (minor: minor_state) (major: MH.major_heap)
  (src: U64.t) (dst: U64.t)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      CG.mem_ce (CG.MinorV src, CG.MajorV dst)
        (CG.build_chunked_combined_graph minor major))
    (ensures
      exists (dst_obj: obj_addr).
        dst_obj == dst /\ U64.v dst_obj >= minor_heap_size)
  =
  CG.chunked_minor_edge_elim minor major src (CG.MajorV dst);
  let i =
    FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i ->
        i < minor_wosize minor src /\
        CG.chunked_classify_minor_field
          minor major (minor_read_field minor src i) == Some (CG.MajorV dst)) in
  let field_v = minor_read_field minor src i in
  assert (CG.chunked_classify_minor_field minor major field_v ==
          Some (CG.MajorV dst));
  CG.chunked_classify_minor_field_inv_major minor major field_v dst;
  let dst_obj = (field_v <: obj_addr) in
  assert (dst_obj == dst);
  assert (Seq.mem dst_obj (MH.major_objects major));
  assert (U64.v dst_obj >= minor_heap_size)

private let major_major_edge_target_above_minor_witness
  (minor: minor_state) (major: MH.major_heap)
  (src: obj_addr) (dst: U64.t)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      CG.mem_ce (CG.MajorV src, CG.MajorV dst)
        (CG.build_chunked_combined_graph minor major))
    (ensures
      exists (dst_obj: obj_addr).
        dst_obj == dst /\ U64.v dst_obj >= minor_heap_size)
  =
  CG.chunked_major_edge_elim minor major src (CG.MajorV dst);
  let i =
    FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i ->
        exists (field_addr: hp_addr).
        exists (v: U64.t).
          i < CG.chunked_wosize_nat_of_object major src /\
          CG.chunked_major_field_slot src i == Some field_addr /\
          MH.read_word_in_major major field_addr == Some v /\
          CG.chunked_classify_major_field minor major v == Some (CG.MajorV dst)) in
  let field_addr =
    FStar.IndefiniteDescription.indefinite_description_ghost hp_addr
      (fun field_addr ->
        exists (v: U64.t).
          i < CG.chunked_wosize_nat_of_object major src /\
          CG.chunked_major_field_slot src i == Some field_addr /\
          MH.read_word_in_major major field_addr == Some v /\
          CG.chunked_classify_major_field minor major v == Some (CG.MajorV dst)) in
  let field_v =
    FStar.IndefiniteDescription.indefinite_description_ghost U64.t
      (fun v ->
        i < CG.chunked_wosize_nat_of_object major src /\
        CG.chunked_major_field_slot src i == Some field_addr /\
        MH.read_word_in_major major field_addr == Some v /\
        CG.chunked_classify_major_field minor major v == Some (CG.MajorV dst)) in
  assert (CG.chunked_classify_major_field minor major field_v ==
          Some (CG.MajorV dst));
  CG.chunked_classify_major_field_inv_major minor major field_v dst;
  let dst_obj = (field_v <: obj_addr) in
  assert (dst_obj == dst);
  assert (Seq.mem dst_obj (MH.major_objects major));
  assert (U64.v dst_obj >= minor_heap_size)
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_graph_edge_maps_to_major_edge_targets_ready_implies_nonblue_sources_above_minor_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      chunked_major_objects_above_minor major /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_edge_targets_ready
        minor major fp roots alloc_fuel fresh u v)
    (ensures
      CC.chunked_graph_edge_maps_to_major_nonblue_sources_above_minor_targets_ready
        minor major fp roots alloc_fuel fresh u v)
  =
  match u, v with
  | CG.MinorV src, CG.MinorV dst -> ()
  | CG.MinorV src, CG.MajorV dst ->
    minor_major_edge_target_above_minor_witness minor major src dst
  | CG.MajorV src, CG.MajorV dst ->
    let src_obj =
      FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
        (fun src_obj ->
          src_obj == src /\
          Seq.mem src_obj (MH.major_objects major) /\
          ~(GenInv.chunked_is_blue major src_obj)) in
    assert (src_obj == src);
    assert (CG.mem_ce (CG.MajorV src_obj, CG.MajorV dst)
              (CG.build_chunked_combined_graph minor major));
    major_major_edge_target_above_minor_witness minor major src_obj dst
  | CG.MajorV src, CG.MinorV dst -> ()
  | _, _ -> assert False
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edge_edge_targets_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_edge_targets_ready
        minor major fp roots alloc_fuel fresh u v)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
       let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
       CG.mem_ce
        (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
         CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
        (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))
  =
  chunked_graph_edge_maps_to_major_edge_targets_ready_implies_nonblue_sources_above_minor_targets_ready
    minor major fp roots alloc_fuel fresh u v;
  CC.chunked_cheney_gc_correct_after_preflight_graph_edge_nonblue_sources_above_minor_targets_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edges_edge_targets_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_edges_edge_targets_map_to_major_edges_prop
        minor major fp roots alloc_fuel fresh)
  =
  let prove_for_u (u: CG.combined_vertex)
    : Lemma
      (ensures
        forall (v: CG.combined_vertex).
          CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
          chunked_graph_edge_maps_to_major_edge_targets_ready
            minor major fp roots alloc_fuel fresh u v ==>
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
             SpecMajorAlloc.ensure_major_head_capacity_spec
               major fp alloc_fuel needed fresh in
           let collect =
             ChunkedCheney.chunked_cheney_collect_spec
               minor r.capacity_major_out r.capacity_fp_out roots
               r.capacity_fuel_out in
           CG.mem_ce
            (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
             CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
            (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
    =
    let prove_for_v (v: CG.combined_vertex)
      : Lemma
        (requires
          CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
          chunked_graph_edge_maps_to_major_edge_targets_ready
            minor major fp roots alloc_fuel fresh u v)
        (ensures
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
             SpecMajorAlloc.ensure_major_head_capacity_spec
               major fp alloc_fuel needed fresh in
           let collect =
             ChunkedCheney.chunked_cheney_collect_spec
               minor r.capacity_major_out r.capacity_fp_out roots
               r.capacity_fuel_out in
           CG.mem_ce
            (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
             CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
            (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
      =
      chunked_cheney_gc_correct_after_preflight_graph_edge_edge_targets_maps_to_major_edge
        minor major fp roots alloc_fuel fresh u v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_v)
  in
  FStar.Classical.forall_intro prove_for_u
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
private let minor_minor_edge_target_positive
  (minor: minor_state) (major: MH.major_heap)
  (src dst: U64.t)
  : Lemma
    (requires
      minor_wf minor /\
      CG.mem_ce (CG.MinorV src, CG.MinorV dst)
        (CG.build_chunked_combined_graph minor major))
    (ensures minor_wosize minor dst > 0)
  =
  CG.chunked_minor_edge_elim minor major src (CG.MinorV dst);
  let i =
    FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun i ->
        i < minor_wosize minor src /\
        CG.chunked_classify_minor_field
          minor major (minor_read_field minor src i) == Some (CG.MinorV dst)) in
  let field_v = minor_read_field minor src i in
  assert (CG.chunked_classify_minor_field minor major field_v ==
          Some (CG.MinorV dst));
  CG.chunked_classify_minor_field_inv_minor minor major field_v dst;
  assert (Seq.mem dst (minor_objects minor));
  minor_objects_body_bound minor dst

let chunked_graph_edge_maps_to_major_reachable_targets_ready_implies_edge_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_reachable_targets_ready
        minor major fp roots alloc_fuel fresh u v)
    (ensures
      chunked_graph_edge_maps_to_major_edge_targets_ready
        minor major fp roots alloc_fuel fresh u v)
  =
  match u, v with
  | CG.MinorV src, CG.MinorV dst ->
    minor_minor_edge_target_positive minor major src dst
  | CG.MinorV src, CG.MajorV dst -> ()
  | CG.MajorV src, CG.MajorV dst -> ()
  | CG.MajorV src, CG.MinorV dst ->
    CC.chunked_cheney_gc_correct_after_preflight_reachable_forwarding_target_in_major
      minor major fp roots alloc_fuel fresh dst;
    let needed = PromotionDemand.minor_promotion_demand minor + 1 in
    let r =
      SpecMajorAlloc.ensure_major_head_capacity_spec
        major fp alloc_fuel needed fresh in
    let collect =
      ChunkedCheney.chunked_cheney_collect_spec
        minor r.capacity_major_out r.capacity_fp_out roots
        r.capacity_fuel_out in
    assert (is_val_addr (collect.cmc_fwd dst));
    assert (U64.v (collect.cmc_fwd dst) >= U64.v mword);
    assert (collect.cmc_fwd dst <> 0UL)
  | _, _ -> assert False
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edge_reachable_targets_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_reachable_targets_ready
        minor major fp roots alloc_fuel fresh u v)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
       let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
       CG.mem_ce
        (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
         CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
        (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))
  =
  chunked_graph_edge_maps_to_major_reachable_targets_ready_implies_edge_targets_ready
    minor major fp roots alloc_fuel fresh u v;
  chunked_cheney_gc_correct_after_preflight_graph_edge_edge_targets_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edges_reachable_targets_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_edges_reachable_targets_map_to_major_edges_prop
        minor major fp roots alloc_fuel fresh)
  =
  let prove_for_u (u: CG.combined_vertex)
    : Lemma
      (ensures
        forall (v: CG.combined_vertex).
          CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
          chunked_graph_edge_maps_to_major_reachable_targets_ready
            minor major fp roots alloc_fuel fresh u v ==>
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
             SpecMajorAlloc.ensure_major_head_capacity_spec
               major fp alloc_fuel needed fresh in
           let collect =
             ChunkedCheney.chunked_cheney_collect_spec
               minor r.capacity_major_out r.capacity_fp_out roots
               r.capacity_fuel_out in
           CG.mem_ce
            (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
             CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
            (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
    =
    let prove_for_v (v: CG.combined_vertex)
      : Lemma
        (requires
          CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
          chunked_graph_edge_maps_to_major_reachable_targets_ready
            minor major fp roots alloc_fuel fresh u v)
        (ensures
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
             SpecMajorAlloc.ensure_major_head_capacity_spec
               major fp alloc_fuel needed fresh in
           let collect =
             ChunkedCheney.chunked_cheney_collect_spec
               minor r.capacity_major_out r.capacity_fp_out roots
               r.capacity_fuel_out in
           CG.mem_ce
            (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
             CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
            (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
      =
      chunked_cheney_gc_correct_after_preflight_graph_edge_reachable_targets_maps_to_major_edge
        minor major fp roots alloc_fuel fresh u v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_v)
  in
  FStar.Classical.forall_intro prove_for_u
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_graph_vertex_maps_to_major_membership_ready_implies_ready
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u: CG.combined_vertex)
  : Lemma
    (requires
      CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_vertex_maps_to_major_membership_ready minor roots u)
    (ensures
      CC.chunked_graph_vertex_maps_to_major_ready minor major roots u)
  =
  match u with
  | CG.MinorV src -> ()
  | CG.MajorV src ->
    CG.chunked_major_vertex_valid minor major src;
    let src_obj : obj_addr = src in
    assert (src_obj == src);
    assert (Seq.mem src_obj (MH.major_objects major))
  | _ -> assert False
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_vertex_membership_ready_maps_to_major_vertex
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_vertex_maps_to_major_membership_ready minor roots u)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
       let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
       CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
        (CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major)))
  =
  chunked_graph_vertex_maps_to_major_membership_ready_implies_ready
    minor major roots u;
  CC.chunked_cheney_gc_correct_after_preflight_graph_vertex_maps_to_major_vertex
    minor major fp roots alloc_fuel fresh u
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_vertices_membership_ready_map_to_major_vertices
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_vertices_membership_ready_map_to_major_vertices_prop
        minor major fp roots alloc_fuel fresh)
  =
  let prove_for_u (u: CG.combined_vertex)
    : Lemma
      (requires
        CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
        chunked_graph_vertex_maps_to_major_membership_ready minor roots u)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
          (CG.build_chunked_combined_graph collect.cmc_minor collect.cmc_major)))
    =
    chunked_cheney_gc_correct_after_preflight_graph_vertex_membership_ready_maps_to_major_vertex
      minor major fp roots alloc_fuel fresh u
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_u)
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_membership_ready_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_membership_ready_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)
  =
  chunked_cheney_gc_correct_after_preflight_graph_vertices_membership_ready_map_to_major_vertices
    minor major fp roots alloc_fuel fresh;
  chunked_cheney_gc_correct_after_preflight_graph_edges_reachable_targets_map_to_major_edges
    minor major fp roots alloc_fuel fresh
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 1 --ifuel 1"
let chunked_minor_source_edge_not_no_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      chunked_major_objects_are_pointer_fields major /\
      CG.mem_ce (CG.MinorV src, dst)
        (CG.build_chunked_combined_graph minor major))
    (ensures
      minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag)
  =
  GenInv.chunked_collection_heap_shape_elim minor major fp fuel;
  GenInv.minor_heap_shape_elim minor;
  assert (minor_no_scan_invariant minor);
  CG.chunked_minor_edge_elim minor major src dst;
  assert (Seq.mem src (minor_objects minor));
  let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
    (fun i -> i < minor_wosize minor src /\
      CG.chunked_classify_minor_field
        minor major (minor_read_field minor src i) == Some dst) in
  assert (i < minor_wosize minor src);
  assert (CG.chunked_classify_minor_field
    minor major (minor_read_field minor src i) == Some dst);
  GC.Spec.Object.no_scan_tag_val ();
  if minor_tag minor src >= U64.v GC.Spec.Object.no_scan_tag then begin
    assert (minor_tag minor src >= 251);
    let field = minor_read_field minor src i in
    match dst with
    | CG.MinorV d ->
      CG.chunked_classify_minor_field_inv_minor minor major field d;
      assert (to_minor_offset field == d);
      assert (Seq.mem d (minor_objects minor));
      minor_objects_valid minor d;
      assert (is_minor_pointer d);
      assert (is_minor_pointer (to_minor_offset field));
      assert (~(is_minor_pointer (to_minor_offset field)));
      assert False
    | CG.MajorV d ->
      CG.chunked_classify_minor_field_inv_major minor major field d;
      assert (field == d);
      is_val_addr_spec field;
      assert (Seq.mem (field <: obj_addr) (MH.major_objects major));
      assert (GC.Spec.Fields.is_pointer_field (field <: obj_addr));
      assert (GC.Spec.Fields.is_pointer_field field);
      assert (~(GC.Spec.Fields.is_pointer_field field));
      assert False
  end
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_reachable_major_vertex_live_selected
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (v: U64.t)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_objects_are_pointer_fields major /\
      CG.combined_reachable
        (CG.build_chunked_combined_graph minor major)
        (CG.classify_roots roots)
        (CG.MajorV v))
    (ensures
      chunked_live_selected_graph_vertex minor major roots (CG.MajorV v))
  =
  assert (CReach.chunked_major_objects_are_pointer_fields major);
  CReach.chunked_reachable_major_valid_nonblue minor major fp fuel roots;
  assert (U64.v v >= U64.v mword);
  assert (U64.v v < heap_size);
  assert (U64.v v % U64.v mword == 0);
  let obj : obj_addr = v in
  assert (Seq.mem obj (MH.major_objects major));
  assert (~(GenInv.chunked_is_blue major obj));
  CG.chunked_major_vertex_char minor major obj;
  assert (CG.mem_cv (CG.MajorV obj)
    (CG.build_chunked_combined_graph minor major));
  assert (CG.MajorV obj == CG.MajorV v);
  assert (exists (src_obj: obj_addr).
    src_obj == v /\
    Seq.mem src_obj (MH.major_objects major) /\
    ~(GenInv.chunked_is_blue major src_obj))

let chunked_reachable_major_vertex_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (v: U64.t)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CG.combined_reachable
        (CG.build_chunked_combined_graph minor major)
        (CG.classify_roots roots)
        (CG.MajorV v))
    (ensures
      chunked_live_selected_graph_vertex minor major roots (CG.MajorV v))
  =
  chunked_major_chunks_above_zero_addr_objects_are_pointer_fields major;
  chunked_reachable_major_vertex_live_selected minor major fp fuel roots v

let chunked_reachable_positive_minor_vertex_live_selected
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (v: U64.t)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_objects_are_pointer_fields major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
      CG.combined_reachable
        (CG.build_chunked_combined_graph minor major)
        (CG.classify_roots roots)
        (CG.MinorV v) /\
      minor_wosize minor v > 0)
    (ensures
      chunked_live_selected_graph_vertex minor major roots (CG.MinorV v))
  =
  assert (CReach.chunked_major_objects_are_pointer_fields major);
  CReach.chunked_combined_minor_reachable_in_minor_reachable
    minor major fp fuel roots;
  assert (Seq.mem v (minor_reachable minor roots));
  minor_reachable_subset minor roots;
  assert (Seq.mem v (minor_objects minor));
  CG.chunked_minor_vertex_char minor major v;
  assert (CG.mem_cv (CG.MinorV v)
    (CG.build_chunked_combined_graph minor major));
  assert (chunked_graph_vertex_maps_to_major_membership_ready
    minor roots (CG.MinorV v))

let chunked_reachable_positive_minor_vertex_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (v: U64.t)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
      CG.combined_reachable
        (CG.build_chunked_combined_graph minor major)
        (CG.classify_roots roots)
        (CG.MinorV v) /\
      minor_wosize minor v > 0)
    (ensures
      chunked_live_selected_graph_vertex minor major roots (CG.MinorV v))
  =
  chunked_major_chunks_above_zero_addr_objects_are_pointer_fields major;
  chunked_reachable_positive_minor_vertex_live_selected
    minor major fp fuel roots v
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_live_selected_graph_edge_implies_live_selected_ready
  (minor: minor_state) (major: MH.major_heap) (roots: seq U64.t)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      chunked_live_selected_graph_edge minor major roots u v)
    (ensures
      chunked_graph_edge_maps_to_major_live_selected_ready
        minor major roots u v)
  =
  match u, v with
  | CG.MinorV src, CG.MinorV dst -> ()
  | CG.MinorV src, CG.MajorV dst -> ()
  | CG.MajorV src, CG.MajorV dst -> ()
  | CG.MajorV src, CG.MinorV dst -> ()
  | _, _ -> assert False
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_graph_edge_maps_to_major_live_selected_ready_implies_selected_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      chunked_major_objects_are_pointer_fields major /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_live_selected_ready
        minor major roots u v)
    (ensures
      chunked_graph_edge_maps_to_major_selected_ready minor major roots u v)
  =
  match u, v with
  | CG.MinorV src, CG.MinorV dst ->
    chunked_minor_source_edge_not_no_scan minor major fp fuel src (CG.MinorV dst)
  | CG.MinorV src, CG.MajorV dst ->
    chunked_minor_source_edge_not_no_scan minor major fp fuel src (CG.MajorV dst)
  | CG.MajorV src, CG.MajorV dst -> ()
  | CG.MajorV src, CG.MinorV dst -> ()
  | _, _ -> assert False
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_graph_edge_maps_to_major_selected_ready_implies_reachable_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      chunked_graph_edge_maps_to_major_selected_ready minor major roots u v)
    (ensures
      chunked_graph_edge_maps_to_major_reachable_targets_ready
        minor major fp roots alloc_fuel fresh u v)
  =
  match u, v with
  | CG.MinorV src, CG.MinorV dst -> ()
  | CG.MinorV src, CG.MajorV dst -> ()
  | CG.MajorV src, CG.MajorV dst -> ()
  | CG.MajorV src, CG.MinorV dst -> ()
  | _, _ -> assert False
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edge_selected_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_selected_ready
        minor major roots u v)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
       SpecMajorAlloc.ensure_major_head_capacity_spec
         major fp alloc_fuel needed fresh in
       let collect =
       ChunkedCheney.chunked_cheney_collect_spec
         minor r.capacity_major_out r.capacity_fp_out roots
         r.capacity_fuel_out in
       CG.mem_ce
        (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
         CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
        (CG.build_chunked_combined_graph
         collect.cmc_minor collect.cmc_major)))
  =
  chunked_graph_edge_maps_to_major_selected_ready_implies_reachable_targets_ready
    minor major fp roots alloc_fuel fresh u v;
  chunked_cheney_gc_correct_after_preflight_graph_edge_reachable_targets_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edge_live_selected_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      chunked_major_objects_are_pointer_fields major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0) /\
      CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
      chunked_graph_edge_maps_to_major_live_selected_ready
        minor major roots u v)
    (ensures
      (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
       let r =
        SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp alloc_fuel needed fresh in
       let collect =
        ChunkedCheney.chunked_cheney_collect_spec
          minor r.capacity_major_out r.capacity_fp_out roots
          r.capacity_fuel_out in
       CG.mem_ce
        (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
         CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
        (CG.build_chunked_combined_graph
          collect.cmc_minor collect.cmc_major)))
  =
  chunked_graph_edge_maps_to_major_live_selected_ready_implies_selected_ready
    minor major fp alloc_fuel roots u v;
  chunked_cheney_gc_correct_after_preflight_graph_edge_selected_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      chunked_major_objects_are_pointer_fields major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_live_selected_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)
  =
  let prove_vertex (u: CG.combined_vertex)
    : Lemma
      (requires
        chunked_live_selected_graph_vertex minor major roots u)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel needed fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
           (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
    =
    match u with
    | CG.MinorV src ->
      chunked_cheney_gc_correct_after_preflight_graph_vertex_membership_ready_maps_to_major_vertex
        minor major fp roots alloc_fuel fresh u
    | CG.MajorV src ->
      assert (chunked_graph_vertex_maps_to_major_membership_ready
        minor roots u);
      chunked_cheney_gc_correct_after_preflight_graph_vertex_membership_ready_maps_to_major_vertex
        minor major fp roots alloc_fuel fresh u
    | _ -> assert False
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_vertex);
  let prove_edge_u (u: CG.combined_vertex)
    : Lemma
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel needed fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         forall (v: CG.combined_vertex).
          chunked_live_selected_graph_edge minor major roots u v ==>
          CG.mem_ce
            (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
             CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
            (CG.build_chunked_combined_graph
              collect.cmc_minor collect.cmc_major)))
    =
    let prove_edge_v (v: CG.combined_vertex)
      : Lemma
        (requires
          chunked_live_selected_graph_edge minor major roots u v)
        (ensures
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
            SpecMajorAlloc.ensure_major_head_capacity_spec
              major fp alloc_fuel needed fresh in
           let collect =
            ChunkedCheney.chunked_cheney_collect_spec
              minor r.capacity_major_out r.capacity_fp_out roots
              r.capacity_fuel_out in
           CG.mem_ce
            (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
             CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
            (CG.build_chunked_combined_graph
              collect.cmc_minor collect.cmc_major)))
      =
      chunked_live_selected_graph_edge_implies_live_selected_ready
        minor major roots u v;
      chunked_cheney_gc_correct_after_preflight_graph_edge_live_selected_maps_to_major_edge
        minor major fp roots alloc_fuel fresh u v
    in
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires prove_edge_v)
  in
  FStar.Classical.forall_intro prove_edge_u
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_chunks_above_zero_addr major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_live_selected_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)
  =
  chunked_major_chunks_above_zero_addr_objects_above_minor major;
  chunked_major_chunks_above_zero_addr_objects_are_pointer_fields major;
  chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph
    minor major fp roots alloc_fuel fresh
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_reachable_live_graph_vertex_implies_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (u: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
      chunked_reachable_live_graph_vertex minor major roots u)
    (ensures
      chunked_live_selected_graph_vertex minor major roots u)
  =
  match u with
  | CG.MinorV v ->
    assert (minor_wosize minor v > 0);
    chunked_reachable_positive_minor_vertex_live_selected_from_chunk_bases
      minor major fp fuel roots v
  | CG.MajorV v ->
    chunked_reachable_major_vertex_live_selected_from_chunk_bases
      minor major fp fuel roots v
  | _ -> assert False

let chunked_reachable_live_graph_edge_implies_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t) (u v: CG.combined_vertex)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
      chunked_reachable_live_graph_edge minor major roots u v)
    (ensures
      chunked_live_selected_graph_edge minor major roots u v)
  =
  chunked_reachable_live_graph_vertex_implies_live_selected_from_chunk_bases
    minor major fp fuel roots u;
  chunked_reachable_live_graph_vertex_implies_live_selected_from_chunk_bases
    minor major fp fuel roots v;
  match u, v with
  | CG.MinorV _, CG.MinorV _ -> ()
  | CG.MinorV _, CG.MajorV _ -> ()
  | CG.MajorV _, CG.MajorV _ -> ()
  | CG.MajorV _, CG.MinorV _ -> ()
  | _, _ -> assert False

let chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)
  =
  chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph_from_chunk_bases
    minor major fp roots alloc_fuel fresh;
  let prove_vertex (u: CG.combined_vertex)
    : Lemma
      (requires chunked_reachable_live_graph_vertex minor major roots u)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_cv (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u))
           (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
    =
    chunked_reachable_live_graph_vertex_implies_live_selected_from_chunk_bases
      minor major fp alloc_fuel roots u;
    assert (chunked_live_selected_graph_vertex minor major roots u)
  in
  let prove_edge_u (u: CG.combined_vertex)
    : Lemma
      (ensures
        forall (v: CG.combined_vertex).
          chunked_reachable_live_graph_edge minor major roots u v ==>
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
             SpecMajorAlloc.ensure_major_head_capacity_spec
               major fp alloc_fuel needed fresh in
           let collect =
             ChunkedCheney.chunked_cheney_collect_spec
               minor r.capacity_major_out r.capacity_fp_out roots
               r.capacity_fuel_out in
           CG.mem_ce
             (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
              CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
             (CG.build_chunked_combined_graph
               collect.cmc_minor collect.cmc_major)))
    =
    let prove_edge_v (v: CG.combined_vertex)
      : Lemma
        (requires chunked_reachable_live_graph_edge minor major roots u v)
        (ensures
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
             SpecMajorAlloc.ensure_major_head_capacity_spec
               major fp alloc_fuel needed fresh in
           let collect =
             ChunkedCheney.chunked_cheney_collect_spec
               minor r.capacity_major_out r.capacity_fp_out roots
               r.capacity_fuel_out in
           CG.mem_ce
             (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
              CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
             (CG.build_chunked_combined_graph
               collect.cmc_minor collect.cmc_major)))
      =
      chunked_reachable_live_graph_edge_implies_live_selected_from_chunk_bases
        minor major fp alloc_fuel roots u v;
      assert (chunked_live_selected_graph_edge minor major roots u v)
    in
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires prove_edge_v)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_vertex);
  FStar.Classical.forall_intro prove_edge_u
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_edges_selected_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_edges_selected_map_to_major_edges_prop
        minor major fp roots alloc_fuel fresh)
  =
  let prove_for_u (u: CG.combined_vertex)
    : Lemma
      (ensures
        forall (v: CG.combined_vertex).
          CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
          chunked_graph_edge_maps_to_major_selected_ready
            minor major roots u v ==>
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
             SpecMajorAlloc.ensure_major_head_capacity_spec
               major fp alloc_fuel needed fresh in
           let collect =
             ChunkedCheney.chunked_cheney_collect_spec
               minor r.capacity_major_out r.capacity_fp_out roots
               r.capacity_fuel_out in
           CG.mem_ce
            (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
             CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
            (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
    =
    let prove_for_v (v: CG.combined_vertex)
      : Lemma
        (requires
          CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
          chunked_graph_edge_maps_to_major_selected_ready
            minor major roots u v)
        (ensures
          (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
           let r =
             SpecMajorAlloc.ensure_major_head_capacity_spec
               major fp alloc_fuel needed fresh in
           let collect =
             ChunkedCheney.chunked_cheney_collect_spec
               minor r.capacity_major_out r.capacity_fp_out roots
               r.capacity_fuel_out in
           CG.mem_ce
            (CG.MajorV (CG.fwd_morphism collect.cmc_fwd u),
             CG.MajorV (CG.fwd_morphism collect.cmc_fwd v))
            (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
      =
      chunked_cheney_gc_correct_after_preflight_graph_edge_selected_maps_to_major_edge
        minor major fp roots alloc_fuel fresh u v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_v)
  in
  FStar.Classical.forall_intro prove_for_u
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_graph_selected_ready_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_graph_selected_ready_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)
  =
  chunked_cheney_gc_correct_after_preflight_graph_vertices_membership_ready_map_to_major_vertices
    minor major fp roots alloc_fuel fresh;
  chunked_cheney_gc_correct_after_preflight_graph_edges_selected_map_to_major_edges
    minor major fp roots alloc_fuel fresh
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_selected_graph_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      chunked_major_objects_above_minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_selected_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)
  =
  chunked_cheney_gc_correct_after_preflight_graph_selected_ready_maps_to_major_graph
    minor major fp roots alloc_fuel fresh
#pop-options

module CRem = GC.Gen.ChunkedRemembered

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue roots major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      CRem.chunked_minor_roots_in_roots minor major roots /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_maps_to_major_graph_prop
        minor major fp roots alloc_fuel fresh)
  =
  CRem.chunked_remembered_minor_edges_in_roots_from_scan minor major roots;
  chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases
    minor major fp roots alloc_fuel fresh
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 1 --ifuel 0"
let chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scanned_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      minor_wf minor /\
      alloc_fuel > 1 /\
      GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
      GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
      CReach.chunked_roots_valid_nonblue
        (CRem.chunked_minor_collection_roots minor major base_roots) major /\
      chunked_major_chunks_above_zero_addr major /\
      CReach.chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp <
       PromotionDemand.minor_promotion_demand minor + 1 ==>
       MH.chunk_disjoint_from_all fresh major /\
       fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
       U64.v fresh.base >= U64.v zero_addr /\
       SpecMajorAlloc.fresh_chunk_wosize fresh >=
       PromotionDemand.minor_promotion_demand minor + 1 /\
       CG.chunked_all_major_object_expansion_safe
       major fresh (MH.major_objects major) 0))
    (ensures
      chunked_reachable_live_graph_maps_to_major_graph_prop
        minor major fp
        (CRem.chunked_minor_collection_roots minor major base_roots)
        alloc_fuel fresh)
  =
  CRem.chunked_minor_roots_in_collection_roots minor major base_roots;
  chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scan
    minor major fp
    (CRem.chunked_minor_collection_roots minor major base_roots)
    alloc_fuel fresh
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_reachable_live_graph_image_isomorphism_from_injective
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_reachable_live_graph_injective_prop
        minor major fp roots alloc_fuel fresh)
    (ensures
      chunked_reachable_live_graph_image_isomorphism_prop
        minor major fp roots alloc_fuel fresh)
  =
  let needed = PromotionDemand.minor_promotion_demand minor + 1 in
  let r =
    SpecMajorAlloc.ensure_major_head_capacity_spec
      major fp alloc_fuel needed fresh in
  let collect =
    ChunkedCheney.chunked_cheney_collect_spec
      minor r.capacity_major_out r.capacity_fp_out roots
      r.capacity_fuel_out in
  let image_valid (u: CG.combined_vertex)
    : Lemma
      (requires chunked_reachable_live_graph_vertex minor major roots u)
      (ensures
        chunked_reachable_live_graph_image_vertex
          minor major fp roots alloc_fuel fresh
          (CG.fwd_morphism collect.cmc_fwd u))
    =
    FStar.Classical.exists_intro
      (fun (x: CG.combined_vertex) ->
        chunked_reachable_live_graph_vertex minor major roots x /\
        CG.fwd_morphism collect.cmc_fwd x ==
        CG.fwd_morphism collect.cmc_fwd u)
      u
  in
  let inj (u v: CG.combined_vertex)
    : Lemma
      (requires
        chunked_reachable_live_graph_vertex minor major roots u /\
        chunked_reachable_live_graph_vertex minor major roots v /\
        CG.fwd_morphism collect.cmc_fwd u ==
        CG.fwd_morphism collect.cmc_fwd v)
      (ensures u == v)
    =
    ()
  in
  let surj (w: U64.t)
    : Lemma
      (requires
        chunked_reachable_live_graph_image_vertex
          minor major fp roots alloc_fuel fresh w)
      (ensures
        exists (u: CG.combined_vertex).
          chunked_reachable_live_graph_vertex minor major roots u /\
          CG.fwd_morphism collect.cmc_fwd u == w)
    =
    ()
  in
  let edge (u v: CG.combined_vertex)
    : Lemma
      (requires
        chunked_reachable_live_graph_vertex minor major roots u /\
        chunked_reachable_live_graph_vertex minor major roots v)
      (ensures
        (chunked_reachable_live_graph_edge minor major roots u v <==>
         chunked_reachable_live_graph_image_edge
          minor major fp roots alloc_fuel fresh
          (CG.fwd_morphism collect.cmc_fwd u)
          (CG.fwd_morphism collect.cmc_fwd v)))
    =
    if chunked_reachable_live_graph_edge minor major roots u v then
      FStar.Classical.exists_intro
        (fun (u': CG.combined_vertex) ->
          exists (v': CG.combined_vertex).
            chunked_reachable_live_graph_edge minor major roots u' v' /\
            CG.fwd_morphism collect.cmc_fwd u' ==
            CG.fwd_morphism collect.cmc_fwd u /\
            CG.fwd_morphism collect.cmc_fwd v' ==
            CG.fwd_morphism collect.cmc_fwd v)
        u
    else begin
      if chunked_reachable_live_graph_image_edge
           minor major fp roots alloc_fuel fresh
           (CG.fwd_morphism collect.cmc_fwd u)
           (CG.fwd_morphism collect.cmc_fwd v)
      then begin
        let u' =
          FStar.IndefiniteDescription.indefinite_description_ghost
            CG.combined_vertex
            (fun u' ->
              exists (v': CG.combined_vertex).
                chunked_reachable_live_graph_edge minor major roots u' v' /\
                CG.fwd_morphism collect.cmc_fwd u' ==
                CG.fwd_morphism collect.cmc_fwd u /\
                CG.fwd_morphism collect.cmc_fwd v' ==
                CG.fwd_morphism collect.cmc_fwd v) in
        let v' =
          FStar.IndefiniteDescription.indefinite_description_ghost
            CG.combined_vertex
            (fun v' ->
              chunked_reachable_live_graph_edge minor major roots u' v' /\
              CG.fwd_morphism collect.cmc_fwd u' ==
              CG.fwd_morphism collect.cmc_fwd u /\
              CG.fwd_morphism collect.cmc_fwd v' ==
              CG.fwd_morphism collect.cmc_fwd v) in
        assert (chunked_reachable_live_graph_edge minor major roots u' v');
        assert (chunked_reachable_live_graph_vertex minor major roots u');
        assert (chunked_reachable_live_graph_vertex minor major roots v');
        inj u' u;
        inj v' v;
        assert (u' == u);
        assert (v' == v);
        assert False
      end
    end
  in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires image_valid);
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 inj);
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires surj);
  FStar.Classical.forall_intro_2
    (fun u -> FStar.Classical.move_requires (edge u))
#pop-options
