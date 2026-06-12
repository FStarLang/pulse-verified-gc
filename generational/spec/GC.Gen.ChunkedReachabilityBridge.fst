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
module SpecMajorAlloc = GC.Spec.MajorAllocator
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

private let rec seq_mem_to_index (#a:eqtype) (x:a) (s:seq a)
  : Ghost nat
    (requires Seq.mem x s)
    (ensures fun i -> i < Seq.length s /\ Seq.index s i == x)
    (decreases Seq.length s)
  =
  if Seq.index s 0 == x then 0
  else begin
    let tl = Seq.slice s 1 (Seq.length s) in
    Seq.lemma_count_slice s 1;
    1 + seq_mem_to_index x tl
  end

private let rec major_object_address_disjoint_from_chunk
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (x: obj_addr)
  : Lemma
    (requires
      MH.chunk_disjoint_from_all fresh mh /\
      Seq.mem x (MH.major_objects mh))
    (ensures ~(MH.chunk_contains_addr fresh x))
    (decreases Seq.length mh)
  =
  if Seq.length mh = 0 then
    assert False
  else begin
    let hd = Seq.head mh in
    let tl = Seq.tail mh in
    assert (MH.major_objects mh ==
      Seq.append (MH.objects_in_chunk hd) (MH.major_objects tl));
    Seq.lemma_mem_append (MH.objects_in_chunk hd) (MH.major_objects tl);
    if Seq.mem x (MH.objects_in_chunk hd) then begin
      MH.objects_in_chunk_member_in_chunk hd x;
      assert (MH.chunk_contains_addr hd x);
      MH.chunks_disjoint_symmetric fresh hd;
      MH.chunks_disjoint_no_shared_addr hd fresh x
    end else begin
      assert (Seq.mem x (MH.major_objects tl));
      MH.chunk_disjoint_from_all_tail fresh mh;
      major_object_address_disjoint_from_chunk tl fresh x
    end
  end

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_roots_valid_nonblue_single_chunk_compat
  (roots: seq U64.t) (major: heap)
  : Lemma
    (requires RBridge.roots_valid_nonblue roots major)
    (ensures
      chunked_roots_valid_nonblue roots (MH.single_chunk_major_heap major))
  =
  let single = MH.single_chunk_major_heap major in
  let prove (r: U64.t)
    : Lemma
      (ensures
        Seq.mem r roots /\
        ~(is_minor_pointer r) /\
        is_val_addr r /\
        Seq.mem (r <: obj_addr) (MH.major_objects single) ==>
        ~(GenInv.chunked_is_blue single (r <: obj_addr)))
    =
    if Seq.mem r roots /\
      ~(is_minor_pointer r) /\
      is_val_addr r /\
      Seq.mem (r <: obj_addr) (MH.major_objects single) then begin
      is_val_addr_spec r;
      let obj : obj_addr = r in
      MH.single_chunk_major_objects_compat major;
      assert (Seq.mem obj (objects zero_addr major));
      objects_addresses_gt_start zero_addr major obj;
      aligned_gt_ge_plus_mword (U64.v obj) (U64.v zero_addr);
      hd_address_bounds obj;
      hd_address_spec obj;
      assert_norm (U64.v mword == 8);
      assert (U64.v (hd_address obj) >= U64.v zero_addr);
      let hdr = read_word major (hd_address obj) in
      MH.single_chunk_read_word_compat major (hd_address obj);
      GenInv.chunked_is_blue_header single obj hdr;
      color_of_object_spec obj major;
      is_blue_iff obj major;
      assert (GenInv.chunked_is_blue single obj == is_blue obj major);
      assert (~(is_blue obj major))
    end
  in
  FStar.Classical.forall_intro prove
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_roots_valid_nonblue_preserved_by_expansion
  (roots: seq U64.t) (major: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_roots_valid_nonblue roots major /\
      chunked_roots_disjoint_from_chunk roots fresh /\
      MH.chunk_disjoint_from_all fresh major)
    (ensures
      chunked_roots_valid_nonblue
        roots (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap major fresh fp).major_out in
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  let prove (r: U64.t)
    : Lemma
      (ensures
        Seq.mem r roots /\ ~(is_minor_pointer r) /\
        is_val_addr r /\ Seq.mem (r <: obj_addr) (MH.major_objects expanded) ==>
        ~(GenInv.chunked_is_blue expanded (r <: obj_addr)))
    =
    if Seq.mem r roots /\
      ~(is_minor_pointer r) /\
      is_val_addr r /\
      Seq.mem (r <: obj_addr) (MH.major_objects expanded) then begin
      let obj : obj_addr = r in
      assert (obj == r);
      SpecMajorAlloc.expand_major_heap_objects major fresh fp;
      if obj == fresh_obj then begin
        SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
        assert (MH.pointer_in_chunk fresh fresh_obj);
        assert (MH.pointer_in_chunk fresh r);
        assert False
      end else begin
        if ~(Seq.mem obj (MH.major_objects major)) then begin
          GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
            fresh_obj obj (MH.major_objects major);
          assert False
        end;
        assert (Seq.mem obj (MH.major_objects major));
        assert (~(GenInv.chunked_is_blue major obj));
        GenInv.chunked_is_blue_preserved_by_expansion major fresh fp obj;
        assert (GenInv.chunked_is_blue expanded obj ==
                GenInv.chunked_is_blue major obj)
      end
    end
  in
  FStar.Classical.forall_intro prove

let chunked_roots_valid_nonblue_ensure_head_capacity
  (roots: seq U64.t) (major: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_roots_valid_nonblue roots major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       chunked_roots_disjoint_from_chunk roots fresh /\
       MH.chunk_disjoint_from_all fresh major))
    (ensures
      chunked_roots_valid_nonblue
        roots
        (SpecMajorAlloc.ensure_major_head_capacity_spec
          major fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize major fp >= needed then
    ()
  else
    chunked_roots_valid_nonblue_preserved_by_expansion
      roots major fresh fp

let chunked_roots_valid_nonblue_append_minor_pointers
  (roots suffix: seq U64.t) (major: MH.major_heap)
  : Lemma
    (requires
      chunked_roots_valid_nonblue roots major /\
      chunked_roots_all_minor_pointers suffix)
    (ensures
      chunked_roots_valid_nonblue (Seq.append roots suffix) major)
  =
  let prove (r: U64.t)
    : Lemma
      (ensures
        Seq.mem r (Seq.append roots suffix) /\
        ~(is_minor_pointer r) /\
        is_val_addr r /\
        Seq.mem (r <: obj_addr) (MH.major_objects major) ==>
        ~(GenInv.chunked_is_blue major (r <: obj_addr)))
    =
    if Seq.mem r (Seq.append roots suffix) /\
      ~(is_minor_pointer r) /\
      is_val_addr r /\
      Seq.mem (r <: obj_addr) (MH.major_objects major) then begin
      Seq.lemma_mem_append roots suffix;
      if Seq.mem r roots then
        ()
      else begin
        assert (Seq.mem r suffix);
        assert (is_minor_pointer r);
        assert False
      end
    end
  in
  FStar.Classical.forall_intro prove

let chunked_roots_disjoint_from_chunk_minor_pointers_above_zero
  (roots: seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_roots_all_minor_pointers roots /\
      U64.v fresh.base >= U64.v zero_addr)
    (ensures chunked_roots_disjoint_from_chunk roots fresh)
  =
  let prove (r: U64.t)
    : Lemma
      (ensures Seq.mem r roots ==> ~(MH.pointer_in_chunk fresh r))
    =
    if Seq.mem r roots then begin
      assert (is_minor_pointer r);
      zero_addr_above_minor ();
      assert (U64.v r < minor_heap_size);
      assert (U64.v r < U64.v fresh.base + U64.v mword)
    end
  in
  FStar.Classical.forall_intro prove
#pop-options

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
let chunked_major_field_zero_no_minor_preserved_by_expansion
  (minor: minor_state) (major: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
    (requires
      chunked_major_field_zero_no_minor minor major /\
      MH.chunk_disjoint_from_all fresh major /\
      CG.chunked_all_major_object_expansion_safe
        major fresh (MH.major_objects major) 0)
    (ensures
      chunked_major_field_zero_no_minor
        minor (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  let expanded = (SpecMajorAlloc.expand_major_heap major fresh fp).major_out in
  let fresh_obj = SpecMajorAlloc.fresh_chunk_object fresh in
  let prove (src: obj_addr) (field_addr: hp_addr) (raw: U64.t)
    : Lemma
      (requires
        Seq.mem src (MH.major_objects expanded) /\
        ~(GenInv.chunked_is_blue expanded src) /\
        CG.chunked_is_no_scan expanded src == false /\
        CG.chunked_major_field_slot src 0 == Some field_addr /\
        MH.read_word_in_major expanded field_addr == Some raw)
      (ensures
        ~(is_minor_pointer (to_minor_offset raw) /\
          Seq.mem (to_minor_offset raw) (minor_objects minor)))
    =
    if src == fresh_obj then begin
      assert (src == fresh_obj);
      assert (~(GenInv.chunked_is_blue expanded src));
      SpecMajorAlloc.expand_major_heap_header_fields major fresh fp;
      f_address_spec fresh.base;
      hd_address_spec fresh_obj;
      assert (hd_address fresh_obj == fresh.base);
      match MH.read_word_in_major expanded fresh.base with
      | Some hdr ->
        assert (getColor hdr == GC.Lib.Header.Blue);
        assert (MH.read_word_in_major expanded (hd_address fresh_obj) == Some hdr);
        GenInv.chunked_is_blue_header expanded fresh_obj hdr;
        assert (GenInv.chunked_is_blue expanded fresh_obj);
        assert (GenInv.chunked_is_blue expanded src);
        assert False
      | None -> assert False
    end else begin
      SpecMajorAlloc.expand_major_heap_objects major fresh fp;
      if ~(Seq.mem src (MH.major_objects major)) then begin
        GC.Spec.SeqMemLemmas.seq_mem_cons_not_mem_implies_eq
          fresh_obj src (MH.major_objects major);
        assert False
      end;
      assert (Seq.mem src (MH.major_objects major));
      let k = seq_mem_to_index src (MH.major_objects major) in
      CG.chunked_all_major_object_expansion_safe_at
        major fresh (MH.major_objects major) 0 k;
      CG.chunked_major_object_expansion_safe_header major fresh src;
      CG.chunked_major_object_expansion_safe_fields major fresh src;
      GenInv.chunked_is_blue_preserved_by_expansion major fresh fp src;
      CG.chunked_is_no_scan_preserved_by_expansion major fresh fp src;
      CG.chunked_major_field_slot_elim src 0 field_addr;
      assert (U64.v field_addr == U64.v src);
      U64.v_inj field_addr src;
      assert (field_addr == src);
      major_object_address_disjoint_from_chunk major fresh src;
      SpecMajorAlloc.expand_major_heap_old_read major fresh fp field_addr;
      assert (MH.read_word_in_major major field_addr == Some raw);
      assert (~(GenInv.chunked_is_blue major src));
      assert (CG.chunked_is_no_scan major src == false)
    end
  in
  FStar.Classical.forall_intro_3
    #(obj_addr)
    #(fun _ -> hp_addr)
    #(fun _ _ -> U64.t)
    #(fun src field_addr raw ->
      Seq.mem src (MH.major_objects expanded) /\
      ~(GenInv.chunked_is_blue expanded src) /\
      CG.chunked_is_no_scan expanded src == false /\
      CG.chunked_major_field_slot src 0 == Some field_addr /\
      MH.read_word_in_major expanded field_addr == Some raw ==>
      ~(is_minor_pointer (to_minor_offset raw) /\
        Seq.mem (to_minor_offset raw) (minor_objects minor)))
    (FStar.Classical.move_requires_3
      #(obj_addr) #(fun _ -> hp_addr) #(fun _ _ -> U64.t)
      #(fun src field_addr raw ->
        Seq.mem src (MH.major_objects expanded) /\
        ~(GenInv.chunked_is_blue expanded src) /\
        CG.chunked_is_no_scan expanded src == false /\
        CG.chunked_major_field_slot src 0 == Some field_addr /\
        MH.read_word_in_major expanded field_addr == Some raw)
      #(fun _ _ raw ->
        ~(is_minor_pointer (to_minor_offset raw) /\
          Seq.mem (to_minor_offset raw) (minor_objects minor)))
      prove)
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 0"
let chunked_major_field_zero_no_minor_ensure_head_capacity
  (minor: minor_state) (major: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
    (requires
      chunked_major_field_zero_no_minor minor major /\
      (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
       MH.chunk_disjoint_from_all fresh major /\
       CG.chunked_all_major_object_expansion_safe
           major fresh (MH.major_objects major) 0))
    (ensures
      chunked_major_field_zero_no_minor
          minor
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp fuel needed fresh).capacity_major_out)
  =
  if SpecMajorAlloc.major_fl_head_wosize major fp >= needed then
    ()
  else
    chunked_major_field_zero_no_minor_preserved_by_expansion
      minor major fresh fp
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
