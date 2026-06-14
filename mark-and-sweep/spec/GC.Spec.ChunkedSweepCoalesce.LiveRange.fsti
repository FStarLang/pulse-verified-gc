module GC.Spec.ChunkedSweepCoalesce.LiveRange

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object

val chunked_fused_sweep_coalesce_prefix_live_field_data_preserved
  (source: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (j: nat). j < idx ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          source target == Some hdr /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let work =
           fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source 0 idx) source source fp) in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
           work target == Some hdr /\
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
           work target == Obj.getWosize hdr /\
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_field_data_preserved
           source work target))

val chunked_fused_sweep_coalesce_target_suffix_live_field_preserved_work
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        GC.Spec.ChunkedSweepCoalesce.RangePreservation.same_chunk_ranges
          source work /\
        idx < Seq.length source /\
        idx < Seq.length work /\
        (let c = Seq.index source idx in
         MH.chunk_start (Seq.index work idx) == MH.chunk_start c /\
         MH.chunk_end (Seq.index work idx) == MH.chunk_end c /\
         Seq.mem target (MH.objects_in_chunk c) /\
         MH.objects_in_chunk_from (Seq.index work idx) c.base ==
           MH.objects_in_chunk c /\
         (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
           MH.object_wosize_in_chunk (Seq.index work idx) o ==
           MH.object_wosize_in_chunk c o) /\
         (forall (j: nat). idx <= j /\ j < Seq.length source ==>
           forall (o: obj_addr).
           Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
           U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                   source o) ==
           MH.object_wosize_in_chunk (Seq.index source j) o) /\
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
           source target == Some hdr /\
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
           work target == Some hdr /\
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
         U64.v (Obj.getWosize hdr) ==
           MH.object_wosize_in_chunk c target /\
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_field_data_preserved
           source work target))
      (ensures
        (let c = Seq.index source idx in
         let step =
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
             source work (MH.objects_in_chunk c) 0UL 0 fp in
         let work' = fst step in
         let fp' = snd step in
         let final =
           fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source (idx + 1) (Seq.length source))
             source work' fp') in
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_field_preserved
           source final target /\
         GC.Spec.ChunkedMark.Defs.chunked_is_no_scan source target ==
         GC.Spec.ChunkedMark.Defs.chunked_is_no_scan final target))

val chunked_fused_sweep_coalesce_live_field_preserved
  (source: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (j: nat). j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          source target == Some hdr /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let final =
           fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
             source source source fp) in
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_field_preserved
           source final target /\
         GC.Spec.ChunkedMark.Defs.chunked_is_no_scan source target ==
         GC.Spec.ChunkedMark.Defs.chunked_is_no_scan final target))

val chunked_fused_sweep_coalesce_live_subgraph_preserved
  (source: MH.major_heap)
  (fp: U64.t)
  (live: obj_addr -> prop)
  (live_idx: obj_addr -> nat)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        (forall (j: nat). j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        (forall (target: obj_addr).
          live target ==>
          live_idx target < Seq.length source /\
          Seq.mem target
            (MH.objects_in_chunk (Seq.index source (live_idx target))) /\
          GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
            source target == Some (live_hdr target) /\
          GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
          U64.v (Obj.getWosize (live_hdr target)) ==
            MH.object_wosize_in_chunk
              (Seq.index source (live_idx target)) target))
      (ensures
        (let final =
           fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
             source source source fp) in
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_live_subgraph_preserved
           source final live))

val chunked_fused_sweep_coalesce_live_subgraph_preserved_from_black_membership
  (source: MH.major_heap)
  (fp: U64.t)
  (live: obj_addr -> prop)
  (live_idx: obj_addr -> nat)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        (forall (j: nat). j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                 source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        (forall (target: obj_addr).
          live target ==>
          live_idx target < Seq.length source /\
          Seq.mem target
           (MH.objects_in_chunk (Seq.index source (live_idx target))) /\
          GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target))
      (ensures
        (let final =
           fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
            source source source fp) in
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_live_subgraph_preserved
           source final live))

val chunked_fused_sweep_coalesce_target_suffix_live_field_preserved
  (source: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (j: nat). idx <= j /\ j < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source j)) ==>
          U64.v (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object
                  source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_read_header
          source target == Some hdr /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let c = Seq.index source idx in
         let step =
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_aux
             source source (MH.objects_in_chunk c) 0UL 0 fp in
         let work = fst step in
         let fp' = snd step in
         let final =
           fst (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source (idx + 1) (Seq.length source))
             source work fp') in
         GC.Spec.ChunkedMajorGC.Graph.chunked_major_field_preserved
           source final target))
