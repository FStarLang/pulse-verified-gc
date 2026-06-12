module GC.Gen.ChunkedReachabilityBridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Reachability

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph
module RBridge = GC.Gen.ReachabilityBridge
module ML = FStar.Math.Lemmas

private let combined_vertex_cases (v: CG.combined_vertex)
  : Lemma (ensures CG.MinorV? v \/ CG.MajorV? v)
  = match v with
    | CG.MinorV _ -> ()
    | CG.MajorV _ -> ()

private let aligned_gt_ge_plus_mword (x z: nat)
  : Lemma (requires x > z /\ x % U64.v mword == 0 /\ z % U64.v mword == 0)
          (ensures x >= z + U64.v mword)
  =
    if x < z + U64.v mword then begin
      assert (x - z > 0);
      assert (x - z < U64.v mword);
      ML.lemma_mod_sub_distr x z (U64.v mword);
      assert ((x - z) % U64.v mword == 0);
      assert False
    end

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_reachable_major_valid_nonblue
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      chunked_roots_valid_nonblue roots major /\
      chunked_major_objects_are_pointer_fields major)
    (ensures (
      let cg = CG.build_chunked_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MajorV v) ==>
        U64.v v >= U64.v mword /\
        U64.v v < heap_size /\
        U64.v v % U64.v mword == 0 /\
        Seq.mem (v <: obj_addr) (MH.major_objects major) /\
        ~(GenInv.chunked_is_blue major (v <: obj_addr)))
    )
  =
  let cg = CG.build_chunked_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  GenInv.chunked_collection_heap_shape_elim minor major fp fuel;
  let p (cv: CG.combined_vertex) : prop =
    match cv with
    | CG.MajorV v ->
      U64.v v >= U64.v mword /\
      U64.v v < heap_size /\
      U64.v v % U64.v mword == 0 /\
      Seq.mem (v <: obj_addr) (MH.major_objects major) /\
      ~(GenInv.chunked_is_blue major (v <: obj_addr))
    | CG.MinorV _ -> True
    | _ -> True
  in
  let base (r: CG.combined_vertex)
    : Lemma
      (requires Seq.mem r combined_roots /\ CG.mem_cv r cg)
      (ensures p r)
    =
    match r with
    | CG.MinorV _ -> ()
    | CG.MajorV v ->
      CG.chunked_major_vertex_valid minor major v;
      CG.classify_roots_inv_major roots v;
      assert (is_val_addr v);
      let obj : obj_addr = v in
      assert (Seq.mem obj (MH.major_objects major));
      assert (~(GenInv.chunked_is_blue major obj))
    | _ -> ()
  in
  let edge (u w: CG.combined_vertex)
    : Lemma
      (requires p u /\ CG.mem_ce (u, w) cg)
      (ensures p w)
    =
    combined_vertex_cases w;
    assert (CG.MinorV? w \/ CG.MajorV? w);
    match w with
    | CG.MinorV _ -> ()
    | CG.MajorV dst ->
      combined_vertex_cases u;
      assert (CG.MinorV? u \/ CG.MajorV? u);
      match u with
      | CG.MinorV src ->
        CG.chunked_minor_edge_elim minor major src (CG.MajorV dst);
        let prove_witness (i: nat)
          : Lemma
            (requires
              i < minor_wosize minor src /\
              CG.chunked_classify_minor_field
                minor major (minor_read_field minor src i) ==
              Some (CG.MajorV dst))
            (ensures p (CG.MajorV dst))
          =
          let raw = minor_read_field minor src i in
          CG.chunked_classify_minor_field_inv_major minor major raw dst;
          assert (raw == dst);
          assert (is_val_addr raw);
          let dst_obj : obj_addr = dst in
          assert (raw == dst_obj);
          assert (Seq.mem dst_obj (MH.major_objects major));
          assert (is_pointer_field dst_obj);
          assert (is_pointer_field raw);
          GenInv.chunked_minor_major_fields_no_blue_elim minor major src i;
          assert ((raw <: obj_addr) == dst_obj);
          assert (~(GenInv.chunked_is_blue major dst_obj))
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires prove_witness)
      | CG.MajorV src ->
        assert (U64.v src >= U64.v mword);
        assert (U64.v src < heap_size);
        assert (U64.v src % U64.v mword == 0);
        let src_obj : obj_addr = src in
        assert (Seq.mem src_obj (MH.major_objects major));
        assert (~(GenInv.chunked_is_blue major src_obj));
        CG.chunked_major_edge_elim minor major src_obj (CG.MajorV dst);
        let prove_witness (i: nat) (field_addr: hp_addr) (raw: U64.t)
          : Lemma
            (requires
              i < CG.chunked_wosize_nat_of_object major src_obj /\
              CG.chunked_major_field_slot src_obj i == Some field_addr /\
              MH.read_word_in_major major field_addr == Some raw /\
              CG.chunked_classify_major_field minor major raw ==
              Some (CG.MajorV dst))
            (ensures p (CG.MajorV dst))
          =
          CG.chunked_classify_major_field_inv_major minor major raw dst;
          assert (raw == dst);
          let dst_obj : obj_addr = dst in
          assert (raw == dst_obj);
          assert (Seq.mem dst_obj (MH.major_objects major));
          assert (is_pointer_field dst_obj);
          assert (is_pointer_field raw);
          assert (is_pointer_to raw dst_obj);
          GenInv.chunked_no_pointer_to_blue_elim
            major src_obj dst_obj i field_addr raw;
          assert (~(GenInv.chunked_is_blue major dst_obj))
        in
        FStar.Classical.forall_intro_3
          #(nat)
          #(fun _ -> hp_addr)
          #(fun _ _ -> U64.t)
          #(fun i field_addr raw ->
            i < CG.chunked_wosize_nat_of_object major src_obj /\
            CG.chunked_major_field_slot src_obj i == Some field_addr /\
            MH.read_word_in_major major field_addr == Some raw /\
            CG.chunked_classify_major_field minor major raw ==
            Some (CG.MajorV dst) ==>
            p (CG.MajorV dst))
          (FStar.Classical.move_requires_3
            #(nat) #(fun _ -> hp_addr) #(fun _ _ -> U64.t)
            #(fun i field_addr raw ->
              i < CG.chunked_wosize_nat_of_object major src_obj /\
              CG.chunked_major_field_slot src_obj i == Some field_addr /\
              MH.read_word_in_major major field_addr == Some raw /\
              CG.chunked_classify_major_field minor major raw ==
              Some (CG.MajorV dst))
            #(fun _ _ _ -> p (CG.MajorV dst))
            prove_witness)
      | _ ->
        combined_vertex_cases u;
        assert (CG.MinorV? u \/ CG.MajorV? u);
        assert False
    | _ -> ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires base);
  FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u));
  let aux (v: U64.t)
    : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MajorV v))
      (ensures p (CG.MajorV v))
    =
    CG.combined_reachable_ind cg combined_roots p (CG.MajorV v)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_major_field_zero_no_minor_single_chunk_compat
  (minor: minor_state) (major: heap)
  : Lemma
    (requires RBridge.major_field_zero_no_minor minor major)
    (ensures
      chunked_major_field_zero_no_minor
        minor (MH.single_chunk_major_heap major))
  =
  let single = MH.single_chunk_major_heap major in
  let prove (src: obj_addr) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
      (requires
        Seq.mem src (MH.major_objects single) /\
        ~(GenInv.chunked_is_blue single src) /\
        CG.chunked_is_no_scan single src == false /\
        CG.chunked_major_field_slot src 0 == Some field_addr /\
        MH.read_word_in_major single field_addr == Some raw)
      (ensures
        ~(is_minor_pointer (to_minor_offset raw) /\
          Seq.mem (to_minor_offset raw) (minor_objects minor)))
    =
    MH.single_chunk_major_objects_compat major;
    assert (Seq.mem src (objects zero_addr major));
    objects_addresses_gt_start zero_addr major src;
    aligned_gt_ge_plus_mword (U64.v src) (U64.v zero_addr);
    hd_address_bounds src;
    hd_address_spec src;
    assert_norm (U64.v mword == 8);
    assert (U64.v (hd_address src) >= U64.v zero_addr);
    let hdr = read_word major (hd_address src) in
    MH.single_chunk_read_word_compat major (hd_address src);
    CG.chunked_is_no_scan_header single src hdr;
    tag_of_object_spec src major;
    is_no_scan_spec src major;
    assert (CG.chunked_is_no_scan single src == is_no_scan src major);
    assert (~(is_no_scan src major));
    CG.chunked_major_field_slot_elim src 0 field_addr;
    assert (U64.v field_addr == U64.v src);
    U64.v_inj field_addr src;
    assert (field_addr == src);
    assert (U64.v field_addr >= U64.v zero_addr);
    MH.single_chunk_read_word_compat major field_addr;
    assert (raw == read_word major field_addr);
    assert (raw == read_word major src)
  in
  FStar.Classical.forall_intro_3
    #(obj_addr)
    #(fun _ -> hp_addr)
    #(fun _ _ -> U64.t)
    #(fun src field_addr raw ->
      Seq.mem src (MH.major_objects single) /\
      ~(GenInv.chunked_is_blue single src) /\
      CG.chunked_is_no_scan single src == false /\
      CG.chunked_major_field_slot src 0 == Some field_addr /\
      MH.read_word_in_major single field_addr == Some raw ==>
      ~(is_minor_pointer (to_minor_offset raw) /\
        Seq.mem (to_minor_offset raw) (minor_objects minor)))
    (FStar.Classical.move_requires_3
      #(obj_addr) #(fun _ -> hp_addr) #(fun _ _ -> U64.t)
      #(fun src field_addr raw ->
        Seq.mem src (MH.major_objects single) /\
        ~(GenInv.chunked_is_blue single src) /\
        CG.chunked_is_no_scan single src == false /\
        CG.chunked_major_field_slot src 0 == Some field_addr /\
        MH.read_word_in_major single field_addr == Some raw)
      #(fun _ _ raw ->
        ~(is_minor_pointer (to_minor_offset raw) /\
          Seq.mem (to_minor_offset raw) (minor_objects minor)))
      prove)
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_combined_minor_reachable_in_minor_reachable
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: seq U64.t)
  : Lemma
    (requires
      GenInv.chunked_collection_heap_shape minor major fp fuel /\
      chunked_roots_valid_nonblue roots major /\
      chunked_major_objects_are_pointer_fields major /\
      chunked_major_field_zero_no_minor minor major /\
      chunked_remembered_minor_edges_in_roots minor major roots)
    (ensures (
      let cg = CG.build_chunked_combined_graph minor major in
      let combined_roots = CG.classify_roots roots in
      forall (v: U64.t).
        CG.combined_reachable cg combined_roots (CG.MinorV v) ==>
        Seq.mem v (minor_reachable minor roots))
    )
  =
  let cg = CG.build_chunked_combined_graph minor major in
  let combined_roots = CG.classify_roots roots in
  let p (cv: CG.combined_vertex) : prop =
    match cv with
    | CG.MinorV v -> Seq.mem v (minor_reachable minor roots)
    | CG.MajorV _ -> True
    | _ -> True
  in
  let base (r: CG.combined_vertex)
    : Lemma
      (requires Seq.mem r combined_roots /\ CG.mem_cv r cg)
      (ensures p r)
    =
    combined_vertex_cases r;
    assert (CG.MinorV? r \/ CG.MajorV? r);
    match r with
    | CG.MinorV v ->
      CG.classify_roots_inv_minor roots v;
      CG.chunked_minor_vertex_char minor major v;
      assert (Seq.mem v (minor_objects minor));
      minor_reachable_roots minor roots
    | CG.MajorV _ -> ()
    | _ -> ()
  in
  let edge (u w: CG.combined_vertex)
    : Lemma
      (requires CG.combined_reachable cg combined_roots u /\ p u /\
                CG.mem_ce (u, w) cg)
      (ensures p w)
    =
    combined_vertex_cases w;
    assert (CG.MinorV? w \/ CG.MajorV? w);
    match w with
    | CG.MajorV _ -> ()
    | CG.MinorV dst ->
      combined_vertex_cases u;
      assert (CG.MinorV? u \/ CG.MajorV? u);
      match u with
      | CG.MinorV src ->
        CG.chunked_minor_edge_elim minor major src (CG.MinorV dst);
        let prove_witness (i: nat)
          : Lemma
            (requires
              i < minor_wosize minor src /\
              CG.chunked_classify_minor_field
                minor major (minor_read_field minor src i) ==
              Some (CG.MinorV dst))
            (ensures Seq.mem dst (minor_successors minor src))
          =
          let raw = minor_read_field minor src i in
          CG.chunked_classify_minor_field_inv_minor minor major raw dst;
          assert (to_minor_offset raw == dst);
          assert (is_minor_addr dst);
          assert (Seq.mem dst (minor_objects minor));
          minor_successors_char minor src dst;
          assert (exists (j: nat).
            j < minor_wosize minor src /\
            to_minor_offset (minor_read_field minor src j) == dst /\
            is_minor_addr dst /\
            Seq.mem dst (minor_objects minor))
        in
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires prove_witness);
        minor_reachable_closed minor roots src dst
      | CG.MajorV src ->
        chunked_reachable_major_valid_nonblue minor major fp fuel roots;
        assert (U64.v src >= U64.v mword);
        assert (U64.v src < heap_size);
        assert (U64.v src % U64.v mword == 0);
        let src_obj : obj_addr = src in
        assert (Seq.mem src_obj (MH.major_objects major));
        assert (~(GenInv.chunked_is_blue major src_obj));
        CG.chunked_major_edge_elim minor major src_obj (CG.MinorV dst);
        let prove_witness (i: nat) (field_addr: hp_addr) (raw: U64.t)
          : Lemma
            (requires
              i < CG.chunked_wosize_nat_of_object major src_obj /\
              CG.chunked_major_field_slot src_obj i == Some field_addr /\
              MH.read_word_in_major major field_addr == Some raw /\
              CG.chunked_classify_major_field minor major raw ==
              Some (CG.MinorV dst))
            (ensures Seq.mem dst (minor_reachable minor roots))
          =
          CG.chunked_classify_major_field_inv_minor minor major raw dst;
          assert (to_minor_offset raw == dst);
          assert (is_minor_pointer dst);
          assert (Seq.mem dst (minor_objects minor));
          if i = 0 then begin
            assert (CG.chunked_major_field_slot src_obj 0 == Some field_addr);
            assert (is_minor_pointer (to_minor_offset raw));
            assert (Seq.mem (to_minor_offset raw) (minor_objects minor));
            assert False
          end else begin
            assert (i <> 0);
            assert (Seq.mem dst roots);
            minor_reachable_roots minor roots
          end
        in
        FStar.Classical.forall_intro_3
          #(nat)
          #(fun _ -> hp_addr)
          #(fun _ _ -> U64.t)
          #(fun i field_addr raw ->
            i < CG.chunked_wosize_nat_of_object major src_obj /\
            CG.chunked_major_field_slot src_obj i == Some field_addr /\
            MH.read_word_in_major major field_addr == Some raw /\
            CG.chunked_classify_major_field minor major raw ==
            Some (CG.MinorV dst) ==>
            Seq.mem dst (minor_reachable minor roots))
          (FStar.Classical.move_requires_3
            #(nat) #(fun _ -> hp_addr) #(fun _ _ -> U64.t)
            #(fun i field_addr raw ->
              i < CG.chunked_wosize_nat_of_object major src_obj /\
              CG.chunked_major_field_slot src_obj i == Some field_addr /\
              MH.read_word_in_major major field_addr == Some raw /\
              CG.chunked_classify_major_field minor major raw ==
              Some (CG.MinorV dst))
            #(fun _ _ _ -> Seq.mem dst (minor_reachable minor roots))
            prove_witness)
      | _ -> ()
    | _ -> ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires base);
  FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (edge u));
  let aux (v: U64.t)
    : Lemma
      (requires CG.combined_reachable cg combined_roots (CG.MinorV v))
      (ensures p (CG.MinorV v))
    =
    CG.combined_reachable_ind_with_reach
      cg combined_roots p (CG.MinorV v)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options
