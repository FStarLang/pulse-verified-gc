module GC.Gen.ChunkedReachabilityBridge

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module GenInv = GC.Gen.HeapInvariant
module CG = GC.Gen.CombinedGraph

private let combined_vertex_cases (v: CG.combined_vertex)
  : Lemma (ensures CG.MinorV? v \/ CG.MajorV? v)
  = match v with
    | CG.MinorV _ -> ()
    | CG.MajorV _ -> ()

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
