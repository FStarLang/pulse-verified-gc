module GC.SPOT.HeapExpansion

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Promote
open GC.Gen.Cheney

module MH = GC.Spec.MajorHeap
module MHReadFrame = GC.Spec.MajorHeap.ReadFrame
module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module Fields = GC.Spec.Fields
module Mark = GC.Spec.Mark
module BMark = GC.Spec.MarkBounded
module SpecAlloc = GC.Spec.Allocator
module SpecMajorAlloc = GC.Spec.MajorAllocator
module SpecMajorAllocMultiAlloc = GC.Spec.MajorAllocator.MultiAlloc
module PromotionDemand = GC.Gen.PromotionDemand
module CheneyPreservation = GC.Gen.CheneyPreservation
module CheneyCorrectness = GC.Gen.CheneyCorrectness
module CheneyGraphReadiness = GC.Gen.CheneyGraphReadiness
module SingleChunkInvariant = GC.Gen.SingleChunkInvariant
module RBridge = GC.Gen.ReachabilityBridge
module CReach = GC.Gen.ChunkedReachabilityBridge
module GenMajorGCBridge = GC.Gen.ChunkedMajorGCBridge
module CRem = GC.Gen.ChunkedRemembered
module ChunkedPromote = GC.Gen.ChunkedPromote
module ChunkedCheney = GC.Gen.ChunkedCheney
module ChunkedUpdate = GC.Gen.ChunkedUpdate
module ChunkedSweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module ChunkedSweepPending = GC.Spec.ChunkedSweepCoalesce.PendingRun
module ChunkedSweepCompat = GC.Spec.ChunkedSweepCoalesce.Compat
module ChunkedSweepPres = GC.Spec.ChunkedSweepCoalesce.Preservation
module ChunkedSweepRange = GC.Spec.ChunkedSweepCoalesce.RangePreservation
module ChunkedSweepLive = GC.Spec.ChunkedSweepCoalesce.LivePreservation
module ChunkedSweepSeq = GC.Spec.ChunkedSweepCoalesce.SequencePreservation
module ChunkedSweepVertex = GC.Spec.ChunkedSweepCoalesce.VertexPreservation
module ChunkedSweepVertexSteps = GC.Spec.ChunkedSweepCoalesce.VertexSteps
module ChunkedSweepVertexOrder = GC.Spec.ChunkedSweepCoalesce.VertexOrder
module ChunkedSweepVertexReach = GC.Spec.ChunkedSweepCoalesce.VertexReach
module ChunkedSweepVertexReachPrefix = GC.Spec.ChunkedSweepCoalesce.VertexReachPrefix
module ChunkedSweepVertexSeq = GC.Spec.ChunkedSweepCoalesce.VertexSequence
module ChunkedSweepVertexRange = GC.Spec.ChunkedSweepCoalesce.VertexRange
module ChunkedSweepLiveRange = GC.Spec.ChunkedSweepCoalesce.LiveRange
module SpecCoalesce = GC.Spec.Coalesce
module SpecSweep = GC.Spec.Sweep
module SpecGCPost = GC.Spec.Correctness
module DenseFused = GC.Spec.SweepCoalesce.Defs
module ChunkedMarkDefs = GC.Spec.ChunkedMark.Defs
module ChunkedMarkPres = GC.Spec.ChunkedMark.Preservation
module ChunkedMarkCompat = GC.Spec.ChunkedMark.Compat
module ChunkedMarkNoPointer = GC.Spec.ChunkedMark.NoPointerCompat
module ChunkedMarkPush = GC.Spec.ChunkedMark.PushCompat
module ChunkedMarkLoop = GC.Spec.ChunkedMark.MarkCompat
module ChunkedMarkBounded = GC.Spec.ChunkedMarkBounded.Defs
module ChunkedMarkBoundedPres = GC.Spec.ChunkedMarkBounded.Preservation
module ChunkedMarkBoundedReadiness = GC.Spec.ChunkedMarkBounded.Readiness
module ChunkedMarkBoundedTargetMembership = GC.Spec.ChunkedMarkBounded.TargetMembership
module ChunkedMarkBoundedReady = GC.Spec.ChunkedMarkBounded.TargetReady
module ChunkedMarkBoundedCount = GC.Spec.ChunkedMarkBounded.Count
module ChunkedMarkBoundedCountStep = GC.Spec.ChunkedMarkBounded.CountStep
module ChunkedMarkBoundedStackStep = GC.Spec.ChunkedMarkBounded.StackStep
module ChunkedMarkBoundedStackReady = GC.Spec.ChunkedMarkBounded.StackReady
module ChunkedMarkBoundedComplete = GC.Spec.ChunkedMarkBounded.Completion
module ChunkedMarkBoundedMetadata = GC.Spec.ChunkedMarkBounded.Metadata
module ChunkedMarkBoundedColor = GC.Spec.ChunkedMarkBounded.ColorInvariant
module ChunkedMarkBoundedTag = GC.Spec.ChunkedMarkBounded.TagInvariant
module ChunkedMarkBoundedEdge = GC.Spec.ChunkedMarkBounded.EdgeInvariant
module ChunkedMarkBoundedNoBlack = GC.Spec.ChunkedMarkBounded.NoBlackToWhite
module ChunkedMarkBoundedCompat = GC.Spec.ChunkedMarkBounded.Compat
module ChunkedMarkBoundedLoop = GC.Spec.ChunkedMarkBounded.LoopCompat
module ChunkedMarkBoundedOuter = GC.Spec.ChunkedMarkBounded.OuterCompat
module ChunkedMajorGC = GC.Spec.ChunkedMajorGC.Defs
module ChunkedMajorGCCorr = GC.Spec.ChunkedMajorGC.Correctness
module ChunkedMajorGCGraph = GC.Spec.ChunkedMajorGC.Graph
module ChunkedMajorGCReach = GC.Spec.ChunkedMajorGC.Reachability
module ChunkedMajorGCMarkReach = GC.Spec.ChunkedMajorGC.MarkReachability
module ChunkedMajorGCMarkLive = GC.Spec.ChunkedMajorGC.MarkLiveness
module ChunkedMajorGCMarkLiveNoBlack = GC.Spec.ChunkedMajorGC.MarkLivenessNoBlack
module ChunkedMajorGCRoots = GC.Spec.ChunkedMajorGC.Roots
module WriteBody = GC.Gen.WriteBodyLemmas
module CG = GC.Gen.CombinedGraph
module GenInv = GC.Gen.HeapInvariant

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
let spot_write_word_in_major_preserves_other_read
  (mh: MH.major_heap)
  (write_addr: hp_addr)
  (value: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v write_addr + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v write_addr))
      (ensures
        (match MH.write_word_in_major mh write_addr value with
        | Some mh' -> MH.read_word_in_major mh' read_addr == Some old
        | None -> True))
  =
  MHReadFrame.write_word_in_major_preserves_other_read
    mh write_addr value read_addr old

let spot_write_word_in_major_preserves_same_read
  (mh: MH.major_heap)
  (addr: hp_addr)
  (old: U64.t)
  (value: U64.t)
  : Lemma
      (requires MH.read_word_in_major mh addr == Some old)
      (ensures
        (match MH.write_word_in_major mh addr value with
         | Some mh' -> MH.read_word_in_major mh' addr == Some value
         | None -> False))
  =
  MHReadFrame.write_word_in_major_preserves_same_read mh addr old value

let spot_chunked_sweep_read_header_step
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ChunkedSweepDefs.chunked_read_header mh obj ==
       MH.read_word_in_major mh (hd_address obj))
  =
  ChunkedSweepDefs.chunked_read_header_step mh obj

let spot_chunked_color_of_object_elim
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Obj.color)
  : Lemma
      (requires ChunkedSweepDefs.chunked_color_of_object mh obj == Some color)
      (ensures
        (match ChunkedSweepDefs.chunked_read_header mh obj with
         | Some hdr -> Obj.getColor hdr == color
         | None -> False))
  =
  ChunkedSweepDefs.chunked_color_of_object_elim mh obj color

let spot_chunked_is_white_read_header
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedSweepDefs.chunked_is_white mh obj)
      (ensures
        (match ChunkedSweepDefs.chunked_read_header mh obj with
         | Some hdr -> Obj.getColor hdr == Header.White
         | None -> False))
  =
  ChunkedSweepDefs.chunked_is_white_read_header mh obj

let spot_chunked_is_blue_read_header
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedSweepDefs.chunked_is_blue mh obj)
      (ensures
        (match ChunkedSweepDefs.chunked_read_header mh obj with
         | Some hdr -> Obj.getColor hdr == Header.Blue
         | None -> False))
  =
  ChunkedSweepDefs.chunked_is_blue_read_header mh obj

let spot_chunked_is_infix_step
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ChunkedSweepDefs.chunked_is_infix mh obj ==
       (ChunkedSweepDefs.chunked_tag_of_object mh obj = Obj.infix_tag))
  =
  ChunkedSweepDefs.chunked_is_infix_step mh obj

let spot_chunked_make_gray_preserves_tag_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_tag_of_object
          (ChunkedMarkDefs.chunked_make_gray mh obj) target ==
        ChunkedSweepDefs.chunked_tag_of_object mh target)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_tag_of_object mh obj target

let spot_chunked_make_black_preserves_tag_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_tag_of_object
          (ChunkedMarkDefs.chunked_make_black mh obj) target ==
        ChunkedSweepDefs.chunked_tag_of_object mh target)
  =
  ChunkedMarkPres.chunked_make_black_preserves_tag_of_object mh obj target

let spot_chunked_make_gray_preserves_infix_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_is_infix
          (ChunkedMarkDefs.chunked_make_gray mh obj) target ==
        ChunkedSweepDefs.chunked_is_infix mh target)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_infix_status mh obj target

let spot_chunked_make_black_preserves_infix_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_is_infix
          (ChunkedMarkDefs.chunked_make_black mh obj) target ==
        ChunkedSweepDefs.chunked_is_infix mh target)
  =
  ChunkedMarkPres.chunked_make_black_preserves_infix_status mh obj target

let spot_major_write_word_or_same_read_same
  (mh: MH.major_heap)
  (write_addr: hp_addr)
  (value: U64.t)
  (idx: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh write_addr == Some idx /\
        MH.word_in_chunk (Seq.index mh idx) write_addr)
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          write_addr == Some value)
  =
  ChunkedSweepPres.major_write_word_or_same_read_same
    mh write_addr value idx

let spot_chunked_set_object_color_preserves_self_wosize
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (ChunkedSweepDefs.chunked_set_object_color mh obj color)
          obj ==
        Obj.getWosize hdr)
  =
  ChunkedSweepPres.chunked_set_object_color_preserves_self_wosize
    mh obj color hdr

let spot_chunked_set_object_color_header_effect
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  (hdr: U64.t)
  : Lemma
      (requires
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        (let new_hdr = Obj.colorHeader hdr color in
         ChunkedSweepDefs.chunked_read_header
           (ChunkedSweepDefs.chunked_set_object_color mh obj color)
           obj == Some new_hdr /\
         Obj.getWosize new_hdr == Obj.getWosize hdr /\
         ChunkedSweepDefs.chunked_wosize_of_object
           (ChunkedSweepDefs.chunked_set_object_color mh obj color)
           obj ==
         Obj.getWosize hdr))
  =
  ChunkedSweepPres.chunked_set_object_color_header_effect
    mh obj color hdr

let spot_chunked_make_white_header_effect
  (mh: MH.major_heap)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        (let new_hdr = Obj.colorHeader hdr Header.White in
         ChunkedSweepDefs.chunked_read_header
           (ChunkedSweepDefs.chunked_make_white mh obj)
           obj == Some new_hdr /\
         Obj.getWosize new_hdr == Obj.getWosize hdr /\
         ChunkedSweepDefs.chunked_wosize_of_object
           (ChunkedSweepDefs.chunked_make_white mh obj)
           obj ==
         Obj.getWosize hdr))
  =
  ChunkedSweepPres.chunked_make_white_header_effect mh obj hdr

let spot_chunked_make_white_preserves_self_wosize
  (mh: MH.major_heap)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (ChunkedSweepDefs.chunked_make_white mh obj)
          obj ==
        Obj.getWosize hdr)
  =
  ChunkedSweepPres.chunked_make_white_preserves_self_wosize mh obj hdr

let spot_chunked_make_blue_preserves_self_wosize
  (mh: MH.major_heap)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (ChunkedSweepDefs.chunked_make_blue mh obj)
          obj ==
        Obj.getWosize hdr)
  =
  ChunkedSweepPres.chunked_make_blue_preserves_self_wosize mh obj hdr

let spot_chunked_set_object_color_preserves_other_read
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (ChunkedSweepDefs.chunked_set_object_color mh obj color)
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_set_object_color_preserves_other_read
    mh obj color read_addr old

let spot_chunked_zero_fields_preserves_read_before
  (mh: MH.major_heap)
  (addr: U64.t)
  (n: nat)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v read_addr + U64.v mword <= U64.v addr)
      (ensures
        MH.read_word_in_major
          (ChunkedSweepDefs.chunked_zero_fields mh addr n)
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_zero_fields_preserves_read_before
    mh addr n read_addr old

let spot_chunked_zero_fields_preserves_read_after
  (mh: MH.major_heap)
  (addr: U64.t)
  (n: nat)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v addr + n * U64.v mword <= U64.v read_addr)
      (ensures
        MH.read_word_in_major
          (ChunkedSweepDefs.chunked_zero_fields mh addr n)
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_zero_fields_preserves_read_after
    mh addr n read_addr old

let spot_chunked_flush_blue_preserves_read_before
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        U64.v read_addr + U64.v mword * 2 <= U64.v first_blue)
      (ensures
        MH.read_word_in_major
          (fst (ChunkedSweepDefs.chunked_flush_blue
            mh first_blue run_words fp))
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_flush_blue_preserves_read_before
    mh first_blue run_words fp read_addr old

let spot_chunked_flush_blue_preserves_read_after
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr))
      (ensures
        MH.read_word_in_major
          (fst (ChunkedSweepDefs.chunked_flush_blue
            mh first_blue run_words fp))
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_flush_blue_preserves_read_after
    mh first_blue run_words fp read_addr old

let spot_chunked_flush_blue_preserves_other_read
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr))
      (ensures
        MH.read_word_in_major
          (fst (ChunkedSweepDefs.chunked_flush_blue
            mh first_blue run_words fp))
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_flush_blue_preserves_other_read
    mh first_blue run_words fp read_addr old

let spot_chunked_make_white_preserves_other_read
  (mh: MH.major_heap)
  (obj: obj_addr)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (ChunkedSweepDefs.chunked_make_white mh obj)
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_make_white_preserves_other_read
    mh obj read_addr old

let spot_chunked_make_blue_preserves_other_read
  (mh: MH.major_heap)
  (obj: obj_addr)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (ChunkedSweepDefs.chunked_make_blue mh obj)
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_make_blue_preserves_other_read
    mh obj read_addr old

let spot_chunked_flush_blue_make_white_preserves_other_read
  (mh: MH.major_heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (obj: obj_addr)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue \/
         U64.v first_blue + (run_words - 1) * U64.v mword <= U64.v read_addr) /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)))
      (ensures
        MH.read_word_in_major
          (ChunkedSweepDefs.chunked_make_white
            (fst (ChunkedSweepDefs.chunked_flush_blue
              mh first_blue run_words fp))
            obj)
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_flush_blue_make_white_preserves_other_read
    mh first_blue run_words fp obj read_addr old

let spot_chunked_sweep_aux_empty_length
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (fp: U64.t)
  : Lemma
      (requires Seq.length objs = 0)
      (ensures ChunkedSweepDefs.chunked_sweep_aux mh objs fp == (mh, fp))
  =
  ChunkedSweepDefs.chunked_sweep_aux_empty_length mh objs fp

let spot_chunked_sweep_object_preserves_other_read
  (mh: MH.major_heap)
  (obj: obj_addr)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
        (U64.v obj + U64.v mword <= U64.v read_addr \/
         U64.v read_addr + U64.v mword <= U64.v obj))
      (ensures
        MH.read_word_in_major
          (fst (ChunkedSweepDefs.chunked_sweep_object mh obj fp))
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_sweep_object_preserves_other_read
    mh obj fp read_addr old

let spot_chunked_sweep_aux_preserves_other_read
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh read_addr == Some old /\
        (forall (obj: obj_addr). Seq.mem obj objs ==>
          (U64.v (hd_address obj) + U64.v mword <= U64.v read_addr \/
           U64.v read_addr + U64.v mword <= U64.v (hd_address obj)) /\
          (U64.v obj + U64.v mword <= U64.v read_addr \/
           U64.v read_addr + U64.v mword <= U64.v obj)))
      (ensures
        MH.read_word_in_major
          (fst (ChunkedSweepDefs.chunked_sweep_aux mh objs fp))
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_sweep_aux_preserves_other_read
    mh objs fp read_addr old

let spot_chunked_fused_aux_empty_length
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires Seq.length objs = 0)
      (ensures
        ChunkedSweepDefs.chunked_fused_aux
          source work objs first_blue run_words fp ==
        ChunkedSweepDefs.chunked_flush_blue work first_blue run_words fp)
  =
  ChunkedSweepDefs.chunked_fused_aux_empty_length
    source work objs first_blue run_words fp

let spot_chunked_fused_aux_read_frame_ready_from_all_after
  (source: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (read_addr: hp_addr)
  : Lemma
      (requires
        (run_words = 0 \/
         U64.v read_addr + U64.v mword * 2 <= U64.v first_blue) /\
        (forall (obj: obj_addr). Seq.mem obj objs ==>
          U64.v read_addr + U64.v mword * 2 <= U64.v obj))
      (ensures
        ChunkedSweepPres.chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)
  =
  ChunkedSweepPres.chunked_fused_aux_read_frame_ready_from_all_after
    source objs first_blue run_words read_addr

let spot_chunked_fused_aux_read_frame_ready_from_chunk_before
  (source: MH.major_heap)
  (idx: nat{idx < Seq.length source})
  (base start: hp_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (read_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        ChunkedSweepPending.pending_run_before_start
          source idx base start first_blue run_words /\
        MH.chunk_end (Seq.index source idx) <= U64.v read_addr /\
        (forall (o: obj_addr).
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source idx) start) ==>
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source idx) base)) /\
        (forall (o: obj_addr).
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source idx) start) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        ChunkedSweepPres.chunked_fused_aux_read_frame_ready
          source
          (MH.objects_in_chunk_from (Seq.index source idx) start)
          first_blue run_words read_addr)
  =
  ChunkedSweepPres.chunked_fused_aux_read_frame_ready_from_chunk_before
    source idx base start first_blue run_words read_addr

let spot_chunked_fused_aux_read_frame_ready_from_chunk_after
  (source: MH.major_heap)
  (idx: nat{idx < Seq.length source})
  (base start: hp_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (read_addr: hp_addr)
  : Lemma
      (requires
        ChunkedSweepPending.pending_run_before_start
          source idx base start first_blue run_words /\
        U64.v read_addr + U64.v mword <=
          MH.chunk_start (Seq.index source idx))
      (ensures
        ChunkedSweepPres.chunked_fused_aux_read_frame_ready
          source
          (MH.objects_in_chunk_from (Seq.index source idx) start)
          first_blue run_words read_addr)
  =
  ChunkedSweepPres.chunked_fused_aux_read_frame_ready_from_chunk_after
    source idx base start first_blue run_words read_addr

let spot_chunked_fused_aux_read_frame_ready_from_live_target
  (source: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (target: obj_addr)
  (read_addr: hp_addr)
  : Lemma
      (requires
        ChunkedSweepPres.chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words target read_addr)
      (ensures
        ChunkedSweepPres.chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)
  =
  ChunkedSweepPres.chunked_fused_aux_read_frame_ready_from_live_target
    source objs first_blue run_words target read_addr

let spot_chunked_fused_aux_live_read_frame_ready_from_chunk
  (source: MH.major_heap)
  (c: MH.heap_chunk)
  (target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        Seq.mem target (MH.objects_in_chunk c) /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk c o) /\
        ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v i <= U64.v (Obj.getWosize hdr) /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target /\
        U64.v (hd_address target) + U64.v mword * U64.v i +
          U64.v mword <= heap_size /\
        field_addr == U64.add (hd_address target) (U64.mul mword i))
      (ensures
        ChunkedSweepPres.chunked_fused_aux_live_read_frame_ready
          source (MH.objects_in_chunk c) 0UL 0 target field_addr)
  =
  ChunkedSweepPres.chunked_fused_aux_live_read_frame_ready_from_chunk
    source c target i field_addr hdr

let spot_chunked_fused_aux_preserves_other_read
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major work read_addr == Some old /\
        ChunkedSweepPres.chunked_fused_aux_read_frame_ready
          source objs first_blue run_words read_addr)
      (ensures
        MH.read_word_in_major
          (fst (ChunkedSweepDefs.chunked_fused_aux
            source work objs first_blue run_words fp))
          read_addr == Some old)
  =
  ChunkedSweepPres.chunked_fused_aux_preserves_other_read
    source work objs first_blue run_words fp read_addr old

let spot_chunked_fused_aux_preserves_get_field_read_some
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size /\
        field_addr == U64.add (hd_address obj) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        ChunkedSweepPres.chunked_fused_aux_read_frame_ready
          source objs first_blue run_words field_addr)
      (ensures
        ChunkedMarkDefs.chunked_get_field
          (fst (ChunkedSweepDefs.chunked_fused_aux
            source work objs first_blue run_words fp))
          obj i ==
        ChunkedMarkDefs.chunked_get_field work obj i)
  =
  ChunkedSweepPres.chunked_fused_aux_preserves_get_field_read_some
    source work objs first_blue run_words fp obj i field_addr old

let spot_chunked_fused_aux_preserves_get_field_from_live_target
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <=
          heap_size /\
        field_addr == U64.add (hd_address obj) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        ChunkedSweepPres.chunked_fused_aux_live_read_frame_ready
          source objs first_blue run_words obj field_addr)
      (ensures
        ChunkedMarkDefs.chunked_get_field
          (fst (ChunkedSweepDefs.chunked_fused_aux
            source work objs first_blue run_words fp))
          obj i ==
        ChunkedMarkDefs.chunked_get_field work obj i)
  =
  ChunkedSweepPres.chunked_fused_aux_preserves_get_field_from_live_target
    source work objs first_blue run_words fp obj i field_addr old

let spot_chunked_fused_aux_live_field_data_preserved_from_chunk
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
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target /\
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedMajorGCGraph.chunked_major_vertex final target))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedMajorGCGraph.chunked_major_field_data_preserved
           source final target))
  =
  ChunkedSweepPres.chunked_fused_aux_live_field_data_preserved_from_chunk
    source idx fp target hdr

let spot_chunked_fused_aux_preserves_get_field_from_chunk_before
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        U64.v (hd_address target) + U64.v mword * U64.v i +
          U64.v mword <= heap_size /\
        field_addr == U64.add (hd_address target) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        MH.chunk_end (Seq.index source idx) <= U64.v field_addr /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedMarkDefs.chunked_get_field final target i ==
         ChunkedMarkDefs.chunked_get_field work target i))
  =
  ChunkedSweepLive.chunked_fused_aux_preserves_get_field_from_chunk_before
    source work idx fp target i field_addr old

let spot_chunked_fused_aux_preserves_get_field_from_chunk_after
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        idx < Seq.length source /\
        U64.v (hd_address target) + U64.v mword * U64.v i +
          U64.v mword <= heap_size /\
        field_addr == U64.add (hd_address target) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        U64.v field_addr + U64.v mword <=
          MH.chunk_start (Seq.index source idx))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedMarkDefs.chunked_get_field final target i ==
         ChunkedMarkDefs.chunked_get_field work target i))
  =
  ChunkedSweepLive.chunked_fused_aux_preserves_get_field_from_chunk_after
    source work idx fp target i field_addr old

let spot_chunked_fused_aux_preserves_get_field_from_other_chunk
  (source work: MH.major_heap)
  (proc_idx target_idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        proc_idx < Seq.length source /\
        target_idx < Seq.length source /\
        proc_idx <> target_idx /\
        MH.word_in_chunk (Seq.index source target_idx) field_addr /\
        U64.v (hd_address target) + U64.v mword * U64.v i +
          U64.v mword <= heap_size /\
        field_addr == U64.add (hd_address target) (U64.mul mword i) /\
        MH.read_word_in_major work field_addr == Some old /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source proc_idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source proc_idx))
            0UL 0 fp) in
         ChunkedMarkDefs.chunked_get_field final target i ==
         ChunkedMarkDefs.chunked_get_field work target i))
  =
  ChunkedSweepLive.chunked_fused_aux_preserves_get_field_from_other_chunk
    source work proc_idx target_idx fp target i field_addr old

let spot_chunked_fused_aux_preserves_read_from_chunk_before
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        MH.read_word_in_major work read_addr == Some old /\
        MH.chunk_end (Seq.index source idx) <= U64.v read_addr /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  ChunkedSweepSeq.chunked_fused_aux_preserves_read_from_chunk_before
    source work idx fp read_addr old

let spot_chunked_fused_aux_preserves_read_from_chunk_after
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        idx < Seq.length source /\
        MH.read_word_in_major work read_addr == Some old /\
        U64.v read_addr + U64.v mword <=
          MH.chunk_start (Seq.index source idx))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  ChunkedSweepSeq.chunked_fused_aux_preserves_read_from_chunk_after
    source work idx fp read_addr old

let spot_chunked_fused_aux_preserves_read_from_other_chunk
  (source work: MH.major_heap)
  (proc_idx target_idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        proc_idx < Seq.length source /\
        target_idx < Seq.length source /\
        proc_idx <> target_idx /\
        MH.word_in_chunk (Seq.index source target_idx) read_addr /\
        MH.read_word_in_major work read_addr == Some old /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source proc_idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source proc_idx))
            0UL 0 fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  ChunkedSweepSeq.chunked_fused_aux_preserves_read_from_other_chunk
    source work proc_idx target_idx fp read_addr old

let spot_chunked_fused_sweep_coalesce_chunk_range_preserves_read
  (source work: MH.major_heap)
  (start stop target_idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        start <= stop /\
        stop <= Seq.length source /\
        target_idx < Seq.length source /\
        (target_idx < start \/ stop <= target_idx) /\
        MH.word_in_chunk (Seq.index source target_idx) read_addr /\
        MH.read_word_in_major work read_addr == Some old /\
        (forall (idx: nat). start <= idx /\ idx < stop ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source start stop) source work fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  ChunkedSweepSeq.chunked_fused_sweep_coalesce_chunk_range_preserves_read
    source work start stop target_idx fp read_addr old

let spot_chunked_fused_sweep_coalesce_prefix_preserves_read
  (source work: MH.major_heap)
  (target_idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        target_idx < Seq.length source /\
        MH.word_in_chunk (Seq.index source target_idx) read_addr /\
        MH.read_word_in_major work read_addr == Some old /\
        (forall (idx: nat). idx < target_idx ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source 0 target_idx) source work fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  ChunkedSweepSeq.chunked_fused_sweep_coalesce_prefix_preserves_read
    source work target_idx fp read_addr old

let spot_chunked_fused_sweep_coalesce_suffix_preserves_read
  (source work: MH.major_heap)
  (target_idx: nat)
  (fp: U64.t)
  (read_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        target_idx < Seq.length source /\
        MH.word_in_chunk (Seq.index source target_idx) read_addr /\
        MH.read_word_in_major work read_addr == Some old /\
        (forall (idx: nat). target_idx < idx /\ idx < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source (target_idx + 1) (Seq.length source))
            source work fp) in
         MH.read_word_in_major final read_addr == Some old))
  =
  ChunkedSweepSeq.chunked_fused_sweep_coalesce_suffix_preserves_read
    source work target_idx fp read_addr old

let spot_chunked_fused_aux_black_head_preserves_wosize
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        Seq.head objs == target /\
        ChunkedSweepDefs.chunked_is_black source target /\
        ChunkedSweepDefs.chunked_read_header work target == Some hdr /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword <=
           U64.v (hd_address target)) /\
        (forall (o: obj_addr). Seq.mem o (Seq.tail objs) ==>
          U64.v (hd_address target) + U64.v mword * 2 <= U64.v o))
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (fst (ChunkedSweepDefs.chunked_fused_aux
            source work objs first_blue run_words fp))
          target ==
        Obj.getWosize hdr)
  =
  ChunkedSweepLive.chunked_fused_aux_black_head_preserves_wosize
    source work objs first_blue run_words fp target hdr

let spot_chunked_fused_aux_black_head_preserves_vertex_from_chunk
  (source work: MH.major_heap)
  (idx: nat)
  (c: MH.heap_chunk)
  (start: hp_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        idx < Seq.length work /\
        MH.chunk_start (Seq.index work idx) == MH.chunk_start c /\
        MH.chunk_end (Seq.index work idx) == MH.chunk_end c /\
        Seq.mem target (MH.objects_in_chunk_from c start) /\
        Seq.length (MH.objects_in_chunk_from c start) > 0 /\
        Seq.head (MH.objects_in_chunk_from c start) == target /\
        hd_address target == start /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index work idx) c.base) /\
        ChunkedSweepDefs.chunked_read_header work target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk_from c start) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk c o) /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v first_blue + (run_words - 1) * U64.v mword ==
            U64.v start /\
          (let fb : obj_addr = first_blue in
           Seq.mem fb
             (MH.objects_in_chunk_from (Seq.index work idx) c.base) /\
           U64.v fb < MH.chunk_end (Seq.index work idx) /\
           U64.v start <= MH.chunk_end (Seq.index work idx) /\
           MH.word_in_chunk (Seq.index work idx) (hd_address fb) /\
           Seq.mem target
             (MH.objects_in_chunk_from (Seq.index work idx) start)))))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work (MH.objects_in_chunk_from c start)
            first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index final idx) c.base) /\
         ChunkedMajorGCGraph.chunked_major_vertex final target /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index work idx)))
  =
  ChunkedSweepLive.chunked_fused_aux_black_head_preserves_vertex_from_chunk
    source work idx c start first_blue run_words fp target hdr

let spot_chunked_fused_aux_live_wosize_preserved_from_chunk
  (source: MH.major_heap)
  (c: MH.heap_chunk)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        Seq.mem target (MH.objects_in_chunk c) /\
        (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk c o) /\
        ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target)
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (fst (ChunkedSweepDefs.chunked_fused_aux
            source source (MH.objects_in_chunk c) 0UL 0 fp))
          target ==
        Obj.getWosize hdr)
  =
  ChunkedSweepLive.chunked_fused_aux_live_wosize_preserved_from_chunk
    source c fp target hdr

let spot_chunked_fused_aux_live_vertex_preserved_from_chunk
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
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let c = Seq.index source idx in
         let final =
           fst (ChunkedSweepDefs.chunked_fused_aux
             source source (MH.objects_in_chunk c) 0UL 0 fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index final idx) c.base) /\
         ChunkedMajorGCGraph.chunked_major_vertex final target /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index source idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index source idx)))
  =
  ChunkedSweepLive.chunked_fused_aux_live_vertex_preserved_from_chunk
    source idx fp target hdr

let spot_chunked_fused_aux_live_wosize_preserved_from_chunk_work
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        idx < Seq.length source /\
        Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        ChunkedSweepDefs.chunked_read_header work target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let c = Seq.index source idx in
         ChunkedSweepDefs.chunked_wosize_of_object
           (fst (ChunkedSweepDefs.chunked_fused_aux
             source work (MH.objects_in_chunk c) 0UL 0 fp))
           target ==
         Obj.getWosize hdr))
  =
  ChunkedSweepLive.chunked_fused_aux_live_wosize_preserved_from_chunk_work
    source work idx fp target hdr

let spot_chunked_fused_aux_live_vertex_preserved_from_chunk_work
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
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
         (forall (o: obj_addr). Seq.mem o (MH.objects_in_chunk c) ==>
           U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
           MH.object_wosize_in_chunk c o) /\
         ChunkedSweepDefs.chunked_read_header work target == Some hdr /\
         ChunkedSweepDefs.chunked_is_black source target /\
         U64.v (Obj.getWosize hdr) == MH.object_wosize_in_chunk c target))
      (ensures
        (let c = Seq.index source idx in
         let final =
           fst (ChunkedSweepDefs.chunked_fused_aux
             source work (MH.objects_in_chunk c) 0UL 0 fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index final idx) c.base) /\
         ChunkedMajorGCGraph.chunked_major_vertex final target /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index work idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index work idx)))
  =
  ChunkedSweepLive.chunked_fused_aux_live_vertex_preserved_from_chunk_work
    source work idx fp target hdr

let spot_chunked_fused_aux_live_field_preserved_from_chunk
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
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedMajorGCGraph.chunked_major_field_preserved
           source final target))
  =
  ChunkedSweepLive.chunked_fused_aux_live_field_preserved_from_chunk
    source idx fp target hdr

let spot_same_chunk_ranges_refl
  (mh: MH.major_heap)
  : Lemma
      (ensures ChunkedSweepRange.same_chunk_ranges mh mh)
  =
  ChunkedSweepRange.same_chunk_ranges_refl mh

let spot_same_chunk_ranges_trans
  (mh0 mh1 mh2: MH.major_heap)
  : Lemma
      (requires
        ChunkedSweepRange.same_chunk_ranges mh0 mh1 /\
        ChunkedSweepRange.same_chunk_ranges mh1 mh2)
      (ensures ChunkedSweepRange.same_chunk_ranges mh0 mh2)
  =
  ChunkedSweepRange.same_chunk_ranges_trans mh0 mh1 mh2

let spot_same_chunk_ranges_length
  (before after: MH.major_heap)
  : Lemma
      (requires ChunkedSweepRange.same_chunk_ranges before after)
      (ensures Seq.length before == Seq.length after)
  =
  ChunkedSweepRange.same_chunk_ranges_length before after

let spot_same_chunk_ranges_index
  (before after: MH.major_heap)
  (idx: nat)
  : Lemma
      (requires
        ChunkedSweepRange.same_chunk_ranges before after /\
        idx < Seq.length before)
      (ensures
        idx < Seq.length after /\
        MH.chunk_start (Seq.index after idx) ==
        MH.chunk_start (Seq.index before idx) /\
        MH.chunk_end (Seq.index after idx) ==
        MH.chunk_end (Seq.index before idx))
  =
  ChunkedSweepRange.same_chunk_ranges_index before after idx

let spot_same_chunk_ranges_word_in_chunk
  (before after: MH.major_heap)
  (idx: nat)
  (addr: hp_addr)
  : Lemma
      (requires
        ChunkedSweepRange.same_chunk_ranges before after /\
        idx < Seq.length before /\
        MH.word_in_chunk (Seq.index before idx) addr)
      (ensures
        idx < Seq.length after /\
        MH.word_in_chunk (Seq.index after idx) addr)
  =
  ChunkedSweepRange.same_chunk_ranges_word_in_chunk before after idx addr

let spot_chunked_fused_aux_preserves_ranges
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (ensures
        ChunkedSweepRange.same_chunk_ranges work
          (fst (ChunkedSweepDefs.chunked_fused_aux
            source work objs first_blue run_words fp)))
  =
  ChunkedSweepRange.chunked_fused_aux_preserves_ranges
    source work objs first_blue run_words fp

let spot_chunked_fused_aux_pointer_classification_preserved
  (source work: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (ensures
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          work
          (fst (ChunkedSweepDefs.chunked_fused_aux
            source work objs first_blue run_words fp)))
  =
  ChunkedSweepRange.chunked_fused_aux_pointer_classification_preserved
    source work objs first_blue run_words fp

let spot_chunked_fused_sweep_coalesce_chunks_preserves_ranges
  (source_chunks source work: MH.major_heap)
  (fp: U64.t)
  : Lemma
      (ensures
        ChunkedSweepRange.same_chunk_ranges work
          (fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
            source_chunks source work fp)))
  =
  ChunkedSweepRange.chunked_fused_sweep_coalesce_chunks_preserves_ranges
    source_chunks source work fp

let spot_chunked_fused_sweep_coalesce_preserves_ranges
  (mh: MH.major_heap)
  : Lemma
      (ensures
        ChunkedSweepRange.same_chunk_ranges mh
          (fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce mh)))
  =
  ChunkedSweepRange.chunked_fused_sweep_coalesce_preserves_ranges mh

let spot_chunked_fused_sweep_coalesce_chunks_pointer_classification_preserved
  (source_chunks source work: MH.major_heap)
  (fp: U64.t)
  : Lemma
      (ensures
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          work
          (fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
            source_chunks source work fp)))
  =
  ChunkedSweepRange.chunked_fused_sweep_coalesce_chunks_pointer_classification_preserved
    source_chunks source work fp

let spot_chunked_fused_sweep_coalesce_pointer_classification_preserved
  (mh: MH.major_heap)
  : Lemma
      (ensures
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          mh
          (fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce mh)))
  =
  ChunkedSweepRange.chunked_fused_sweep_coalesce_pointer_classification_preserved mh

let spot_chunked_fused_aux_live_subgraph_preserved_from_chunk
  (source: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        idx < Seq.length source /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o) /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.objects_in_chunk (Seq.index source idx)) /\
          ChunkedSweepDefs.chunked_read_header source target == Some (live_hdr target) /\
          ChunkedSweepDefs.chunked_is_black source target /\
          U64.v (Obj.getWosize (live_hdr target)) ==
            MH.object_wosize_in_chunk (Seq.index source idx) target))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source source (MH.objects_in_chunk (Seq.index source idx))
            0UL 0 fp) in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           source final live))
  =
  ChunkedSweepLive.chunked_fused_aux_live_subgraph_preserved_from_chunk
    source idx fp live live_hdr

let spot_chunked_set_object_color_preserves_major_objects
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (color: GC.Lib.Header.color_sem)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.major_objects
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) ==
        MH.major_objects mh)
  =
  ChunkedSweepLive.chunked_set_object_color_preserves_major_objects
    mh idx obj color hdr

let spot_chunked_make_white_preserves_major_objects
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.major_objects (ChunkedSweepDefs.chunked_make_white mh obj) ==
        MH.major_objects mh)
  =
  ChunkedSweepLive.chunked_make_white_preserves_major_objects
    mh idx obj hdr

let spot_chunked_make_blue_preserves_major_objects
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address obj) == Some idx /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.major_objects (ChunkedSweepDefs.chunked_make_blue mh obj) ==
        MH.major_objects mh)
  =
  ChunkedSweepLive.chunked_make_blue_preserves_major_objects
    mh idx obj hdr

let spot_chunked_merged_block_step
  (c: MH.heap_chunk)
  (fb: obj_addr)
  (run_words: pos)
  (start: hp_addr)
  (x: obj_addr)
  : Lemma
      (requires
        U64.v fb >= U64.v mword /\
        U64.v fb < heap_size /\
        U64.v fb < MH.chunk_end c /\
        U64.v fb % U64.v mword == 0 /\
        U64.v fb + (run_words - 1) * U64.v mword == U64.v start /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v start <= MH.chunk_end c /\
        MH.word_in_chunk c (hd_address fb) /\
        MH.read_word_in_chunk c (hd_address fb) ==
          Obj.makeHeader
            (U64.uint_to_t (run_words - 1)) Header.Blue 0UL /\
        (U64.v start < MH.chunk_end c ==>
          Seq.mem x (MH.objects_in_chunk_from c start)))
      (ensures
        Seq.mem fb (MH.objects_in_chunk_from c (hd_address fb)) /\
        (U64.v start < MH.chunk_end c ==>
          Seq.mem x (MH.objects_in_chunk_from c (hd_address fb))))
  =
  ChunkedSweepVertex.chunked_merged_block_step
    c fb run_words start x

#push-options "--z3rlimit 1 --fuel 0 --ifuel 0 --split_queries always"
let spot_major_write_word_or_same_after_member_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
            U64.v mword <=
          U64.v addr)
      (ensures
        MH.well_formed_major_heap
          (SpecMajorAlloc.major_write_word_or_same mh addr value) /\
        idx <
          Seq.length
            (SpecMajorAlloc.major_write_word_or_same mh addr value) /\
        Seq.mem obj
          (MH.objects_in_chunk
            (Seq.index
              (SpecMajorAlloc.major_write_word_or_same mh addr value)
              idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx)
          obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
        MH.chunk_start
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end
          (Seq.index
            (SpecMajorAlloc.major_write_word_or_same mh addr value)
            idx) ==
        MH.chunk_end (Seq.index mh idx))
  =
  ChunkedSweepVertex.major_write_word_or_same_after_member_preserves_chunk_member
    mh idx obj addr value

let spot_major_write_word_or_same_after_member_preserves_vertex
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
            U64.v mword <=
          U64.v addr)
      (ensures
        Seq.mem obj
          (MH.major_objects
            (SpecMajorAlloc.major_write_word_or_same mh addr value)))
  =
  ChunkedSweepVertex.major_write_word_or_same_after_member_preserves_vertex
    mh idx obj addr value

let spot_chunked_zero_fields_after_member_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v addr + n * U64.v mword <= MH.chunk_end (Seq.index mh idx) /\
        U64.v (hd_address obj) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
            U64.v mword <=
          U64.v addr)
      (ensures
        MH.well_formed_major_heap
          (ChunkedSweepDefs.chunked_zero_fields mh addr n) /\
        idx < Seq.length (ChunkedSweepDefs.chunked_zero_fields mh addr n) /\
        Seq.mem obj
          (MH.objects_in_chunk
            (Seq.index
              (ChunkedSweepDefs.chunked_zero_fields mh addr n) idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index (ChunkedSweepDefs.chunked_zero_fields mh addr n) idx)
          obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj)
  =
  ChunkedSweepVertex.chunked_zero_fields_after_member_preserves_chunk_member
    mh idx obj addr n

let spot_chunked_flush_blue_after_member_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index mh idx) hd /\
           U64.v (hd_address obj) +
             (1 + MH.object_wosize_in_chunk (Seq.index mh idx) obj) *
               U64.v mword <=
             U64.v hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index mh idx))))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_flush_blue
            mh first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem obj (MH.objects_in_chunk (Seq.index final idx)) /\
         MH.object_wosize_in_chunk (Seq.index final idx) obj ==
         MH.object_wosize_in_chunk (Seq.index mh idx) obj))
  =
  ChunkedSweepVertex.chunked_flush_blue_after_member_preserves_chunk_member
    mh idx obj first_blue run_words fp

let spot_chunked_make_white_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        MH.well_formed_major_heap
          (ChunkedSweepDefs.chunked_make_white mh obj) /\
        idx < Seq.length (ChunkedSweepDefs.chunked_make_white mh obj) /\
        Seq.mem obj
          (MH.objects_in_chunk
            (Seq.index
              (ChunkedSweepDefs.chunked_make_white mh obj) idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx)
          obj ==
        MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
        MH.chunk_start
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx) ==
        MH.chunk_end (Seq.index mh idx))
  =
  ChunkedSweepVertex.chunked_make_white_preserves_chunk_member
    mh idx obj hdr

let spot_chunked_make_white_after_member_preserves_chunk_member
  (mh: MH.major_heap)
  (idx: nat)
  (protected: obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
            U64.v mword <=
          U64.v (hd_address obj))
      (ensures
        MH.well_formed_major_heap
          (ChunkedSweepDefs.chunked_make_white mh obj) /\
        idx < Seq.length (ChunkedSweepDefs.chunked_make_white mh obj) /\
        Seq.mem protected
          (MH.objects_in_chunk
            (Seq.index
              (ChunkedSweepDefs.chunked_make_white mh obj) idx)) /\
        MH.object_wosize_in_chunk
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx)
          protected ==
        MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
        MH.chunk_start
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx) ==
        MH.chunk_end (Seq.index mh idx))
  =
  ChunkedSweepVertex.chunked_make_white_after_member_preserves_chunk_member
    mh idx protected obj

let spot_major_write_word_or_same_payload_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (blk: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem blk (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v blk <= U64.v addr /\
        U64.v addr + U64.v mword <=
          U64.v blk +
            MH.object_wosize_in_chunk (Seq.index mh idx) blk *
              U64.v mword)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) blk ==
         MH.object_wosize_in_chunk (Seq.index mh idx) blk /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertex.major_write_word_or_same_payload_preserves_objects_from
    mh idx start blk addr value

let spot_chunked_zero_fields_payload_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (blk: obj_addr)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem blk (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v blk <= U64.v addr /\
        U64.v addr + n * U64.v mword <=
          U64.v blk +
            MH.object_wosize_in_chunk (Seq.index mh idx) blk *
              U64.v mword)
      (ensures
        (let mh' = ChunkedSweepDefs.chunked_zero_fields mh addr n in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) blk ==
         MH.object_wosize_in_chunk (Seq.index mh idx) blk /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertex.chunked_zero_fields_payload_preserves_objects_from
    mh idx start blk addr n

let spot_chunked_flush_blue_prefix_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (fb: obj_addr)
  (run_words: pos)
  (start: hp_addr)
  (target: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        U64.v fb < MH.chunk_end (Seq.index mh idx) /\
        U64.v fb + (run_words - 1) * U64.v mword == U64.v start /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v start <= MH.chunk_end (Seq.index mh idx) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address fb) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index mh idx) start))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_flush_blue mh fb run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from
             (Seq.index final idx) (hd_address fb)) /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertex.chunked_flush_blue_prefix_preserves_objects_from
    mh idx fb run_words start target fp

let spot_chunked_flush_blue_prefix_preserves_base_member
  (mh: MH.major_heap)
  (idx: nat)
  (base: hp_addr)
  (fb: obj_addr)
  (run_words: pos)
  (start: hp_addr)
  (target: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
        U64.v fb < MH.chunk_end (Seq.index mh idx) /\
        U64.v fb + (run_words - 1) * U64.v mword == U64.v start /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v start <= MH.chunk_end (Seq.index mh idx) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address fb) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index mh idx) start))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_flush_blue mh fb run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index final idx) base) /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertexReachPrefix.chunked_flush_blue_prefix_preserves_base_member
    mh idx base fb run_words start target fp

let spot_base_member_and_header_member_implies_base_member
  (final: MH.major_heap)
  (idx: nat)
  (base: hp_addr)
  (fb: obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        idx < Seq.length final /\
        Seq.mem fb (MH.objects_in_chunk_from (Seq.index final idx) base) /\
        Seq.mem target
          (MH.objects_in_chunk_from (Seq.index final idx) (hd_address fb)))
      (ensures
        Seq.mem target (MH.objects_in_chunk_from (Seq.index final idx) base))
  =
  ChunkedSweepVertexReachPrefix.base_member_and_header_member_implies_base_member
    final idx base fb target

let spot_major_write_member_header_same_wosize_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (obj: obj_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (Obj.getWosize value) ==
          MH.object_wosize_in_chunk (Seq.index mh idx) obj)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same
                    mh (hd_address obj) value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) obj ==
         MH.object_wosize_in_chunk (Seq.index mh idx) obj /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertexReach.major_write_member_header_same_wosize_preserves_objects_from
    mh idx start obj value

let spot_major_write_word_or_same_before_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v addr + U64.v mword <= U64.v start)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertexReach.major_write_word_or_same_before_preserves_objects_from
    mh idx start addr value

let spot_chunked_zero_fields_before_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        U64.v addr % U64.v mword == 0 /\
        (n <> 0 ==> U64.v addr >= MH.chunk_start (Seq.index mh idx)) /\
        U64.v addr + n * U64.v mword <= U64.v start /\
        U64.v addr + n * U64.v mword <= MH.chunk_end (Seq.index mh idx))
      (ensures
        (let mh' = ChunkedSweepDefs.chunked_zero_fields mh addr n in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertexReach.chunked_zero_fields_before_preserves_objects_from
    mh idx start addr n

let spot_chunked_make_white_before_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        ChunkedSweepDefs.chunked_read_header mh obj == Some hdr /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address obj) + U64.v mword <= U64.v start)
      (ensures
        (let mh' = ChunkedSweepDefs.chunked_make_white mh obj in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertexReach.chunked_make_white_before_preserves_objects_from
    mh idx start obj hdr

let spot_chunked_make_white_before_preserves_objects_from_at_index
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address obj) + U64.v mword <= U64.v start)
      (ensures
        (let mh' = ChunkedSweepDefs.chunked_make_white mh obj in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertexReach.chunked_make_white_before_preserves_objects_from_at_index
    mh idx start obj

let spot_chunked_flush_blue_then_make_white_head_preserves_base_member
  (mh: MH.major_heap)
  (idx: nat)
  (base: hp_addr)
  (target: obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem target (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
        ChunkedSweepDefs.chunked_read_header mh target == Some hdr /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v first_blue + (run_words - 1) * U64.v mword ==
            U64.v (hd_address target) /\
          (let fb : obj_addr = first_blue in
           Seq.mem fb (MH.objects_in_chunk_from (Seq.index mh idx) base) /\
           U64.v fb < MH.chunk_end (Seq.index mh idx) /\
           U64.v (hd_address target) <= MH.chunk_end (Seq.index mh idx) /\
           MH.word_in_chunk (Seq.index mh idx) (hd_address fb) /\
           Seq.mem target
             (MH.objects_in_chunk_from
               (Seq.index mh idx) (hd_address target))))))
      (ensures
        (let flushed =
          ChunkedSweepDefs.chunked_flush_blue
            mh first_blue run_words fp in
         let work' = fst flushed in
         let work'' = ChunkedSweepDefs.chunked_make_white work' target in
         MH.well_formed_major_heap work'' /\
         idx < Seq.length work'' /\
         Seq.mem target
           (MH.objects_in_chunk_from (Seq.index work'' idx) base) /\
         MH.object_wosize_in_chunk (Seq.index work'' idx) target ==
         U64.v (Obj.getWosize hdr) /\
         MH.chunk_start (Seq.index work'' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index work'' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertexReachPrefix.chunked_flush_blue_then_make_white_head_preserves_base_member
    mh idx base target first_blue run_words fp hdr

let spot_chunked_flush_blue_before_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        (run_words = 0 \/
         (~(U64.v first_blue < U64.v mword) /\
          ~(U64.v first_blue >= heap_size) /\
          ~(U64.v first_blue % U64.v mword <> 0) /\
          run_words - 1 < pow2 54 /\
          run_words - 1 < pow2 64 /\
          U64.v start <= MH.chunk_end (Seq.index mh idx) /\
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index mh idx) hd /\
           U64.v hd + run_words * U64.v mword <= U64.v start))))
      (ensures
        (let final =
          fst
            (ChunkedSweepDefs.chunked_flush_blue
              mh first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final idx) start ==
         MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertexReachPrefix.chunked_flush_blue_before_preserves_objects_from
    mh idx start first_blue run_words fp

let spot_major_write_word_or_same_after_member_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (protected: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) addr /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
            U64.v mword <=
          U64.v addr)
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index mh' idx) start) /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertex.major_write_word_or_same_after_member_preserves_objects_from
    mh idx start protected addr value

let spot_chunked_zero_fields_after_member_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (protected: obj_addr)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v addr + n * U64.v mword <= MH.chunk_end (Seq.index mh idx) /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
            U64.v mword <=
          U64.v addr)
      (ensures
        (let mh' = ChunkedSweepDefs.chunked_zero_fields mh addr n in
         MH.well_formed_major_heap mh' /\
         idx < Seq.length mh' /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index mh' idx) start) /\
         MH.object_wosize_in_chunk (Seq.index mh' idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
         MH.chunk_start (Seq.index mh' idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index mh' idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertex.chunked_zero_fields_after_member_preserves_objects_from
    mh idx start protected addr n

let spot_chunked_flush_blue_after_member_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (protected: obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index mh idx) hd /\
           U64.v (hd_address protected) +
             (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
               U64.v mword <=
             U64.v hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index mh idx))))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_flush_blue
            mh first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final idx) start) /\
         MH.object_wosize_in_chunk (Seq.index final idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
         MH.chunk_start (Seq.index final idx) ==
         MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
         MH.chunk_end (Seq.index mh idx)))
  =
  ChunkedSweepVertex.chunked_flush_blue_after_member_preserves_objects_from
    mh idx start protected first_blue run_words fp

let spot_chunked_make_white_after_member_preserves_objects_from
  (mh: MH.major_heap)
  (idx: nat)
  (start: hp_addr)
  (protected: obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh idx) start) /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        U64.v (hd_address protected) +
          (1 + MH.object_wosize_in_chunk (Seq.index mh idx) protected) *
            U64.v mword <=
          U64.v (hd_address obj))
      (ensures
        MH.well_formed_major_heap (ChunkedSweepDefs.chunked_make_white mh obj) /\
        idx < Seq.length (ChunkedSweepDefs.chunked_make_white mh obj) /\
        Seq.mem protected
          (MH.objects_in_chunk_from
            (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx)
            start) /\
        MH.object_wosize_in_chunk
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx)
          protected ==
        MH.object_wosize_in_chunk (Seq.index mh idx) protected /\
        MH.chunk_start
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx) ==
        MH.chunk_start (Seq.index mh idx) /\
        MH.chunk_end
          (Seq.index (ChunkedSweepDefs.chunked_make_white mh obj) idx) ==
        MH.chunk_end (Seq.index mh idx))
  =
  ChunkedSweepVertex.chunked_make_white_after_member_preserves_objects_from
    mh idx start protected obj

let spot_major_write_word_or_same_other_chunk_preserves_objects_from
  (mh: MH.major_heap)
  (proc_idx target_idx: nat)
  (start: hp_addr)
  (protected: obj_addr)
  (addr: hp_addr)
  (value: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        proc_idx < Seq.length mh /\
        target_idx < Seq.length mh /\
        proc_idx <> target_idx /\
        MH.word_in_chunk (Seq.index mh proc_idx) addr /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh target_idx) start))
      (ensures
        (let mh' = SpecMajorAlloc.major_write_word_or_same mh addr value in
         MH.well_formed_major_heap mh' /\
         proc_idx < Seq.length mh' /\
         target_idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' target_idx) start ==
         MH.objects_in_chunk_from (Seq.index mh target_idx) start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index mh' target_idx) start) /\
         MH.object_wosize_in_chunk (Seq.index mh' target_idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh target_idx) protected /\
         MH.chunk_start (Seq.index mh' proc_idx) ==
         MH.chunk_start (Seq.index mh proc_idx) /\
         MH.chunk_end (Seq.index mh' proc_idx) ==
         MH.chunk_end (Seq.index mh proc_idx) /\
         MH.chunk_start (Seq.index mh' target_idx) ==
         MH.chunk_start (Seq.index mh target_idx) /\
         MH.chunk_end (Seq.index mh' target_idx) ==
         MH.chunk_end (Seq.index mh target_idx)))
  =
  ChunkedSweepVertex.major_write_word_or_same_other_chunk_preserves_objects_from
    mh proc_idx target_idx start protected addr value

let spot_chunked_zero_fields_other_chunk_preserves_objects_from
  (mh: MH.major_heap)
  (proc_idx target_idx: nat)
  (start: hp_addr)
  (protected: obj_addr)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        proc_idx < Seq.length mh /\
        target_idx < Seq.length mh /\
        proc_idx <> target_idx /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh target_idx) start) /\
        U64.v addr % U64.v mword == 0 /\
        U64.v addr + n * U64.v mword <=
          MH.chunk_end (Seq.index mh proc_idx) /\
        (n <> 0 ==> MH.chunk_start (Seq.index mh proc_idx) <= U64.v addr))
      (ensures
        (let mh' = ChunkedSweepDefs.chunked_zero_fields mh addr n in
         MH.well_formed_major_heap mh' /\
         target_idx < Seq.length mh' /\
         MH.objects_in_chunk_from (Seq.index mh' target_idx) start ==
         MH.objects_in_chunk_from (Seq.index mh target_idx) start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index mh' target_idx) start) /\
         MH.object_wosize_in_chunk (Seq.index mh' target_idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh target_idx) protected /\
         MH.chunk_start (Seq.index mh' target_idx) ==
         MH.chunk_start (Seq.index mh target_idx) /\
         MH.chunk_end (Seq.index mh' target_idx) ==
         MH.chunk_end (Seq.index mh target_idx)))
  =
  ChunkedSweepVertex.chunked_zero_fields_other_chunk_preserves_objects_from
    mh proc_idx target_idx start protected addr n

let spot_chunked_flush_blue_other_chunk_preserves_objects_from
  (mh: MH.major_heap)
  (proc_idx target_idx: nat)
  (start: hp_addr)
  (protected: obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        proc_idx < Seq.length mh /\
        target_idx < Seq.length mh /\
        proc_idx <> target_idx /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh target_idx) start) /\
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index mh proc_idx) hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index mh proc_idx))))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_flush_blue
            mh first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) start ==
         MH.objects_in_chunk_from (Seq.index mh target_idx) start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
         MH.object_wosize_in_chunk (Seq.index mh target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
         MH.chunk_start (Seq.index mh target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
         MH.chunk_end (Seq.index mh target_idx)))
  =
  ChunkedSweepVertex.chunked_flush_blue_other_chunk_preserves_objects_from
    mh proc_idx target_idx start protected first_blue run_words fp

let spot_chunked_make_white_other_chunk_preserves_objects_from
  (mh: MH.major_heap)
  (proc_idx target_idx: nat)
  (start: hp_addr)
  (protected: obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        proc_idx < Seq.length mh /\
        target_idx < Seq.length mh /\
        proc_idx <> target_idx /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index mh target_idx) start) /\
        MH.word_in_chunk (Seq.index mh proc_idx) (hd_address obj))
      (ensures
        MH.well_formed_major_heap
          (ChunkedSweepDefs.chunked_make_white mh obj) /\
        target_idx <
          Seq.length (ChunkedSweepDefs.chunked_make_white mh obj) /\
        MH.objects_in_chunk_from
          (Seq.index
            (ChunkedSweepDefs.chunked_make_white mh obj)
            target_idx)
          start ==
        MH.objects_in_chunk_from (Seq.index mh target_idx) start /\
        Seq.mem protected
          (MH.objects_in_chunk_from
            (Seq.index
              (ChunkedSweepDefs.chunked_make_white mh obj)
              target_idx)
            start) /\
        MH.object_wosize_in_chunk
          (Seq.index
            (ChunkedSweepDefs.chunked_make_white mh obj)
            target_idx)
          protected ==
        MH.object_wosize_in_chunk (Seq.index mh target_idx) protected /\
        MH.chunk_start
          (Seq.index
            (ChunkedSweepDefs.chunked_make_white mh obj)
            target_idx) ==
        MH.chunk_start (Seq.index mh target_idx) /\
        MH.chunk_end
          (Seq.index
            (ChunkedSweepDefs.chunked_make_white mh obj)
            target_idx) ==
        MH.chunk_end (Seq.index mh target_idx))
  =
  ChunkedSweepVertex.chunked_make_white_other_chunk_preserves_objects_from
    mh proc_idx target_idx start protected obj

let spot_chunked_fused_aux_other_chunk_preserves_objects_from_from
  (source work: MH.major_heap)
  (proc_idx: nat{proc_idx < Seq.length source})
  (target_idx: nat)
  (proc_start target_start: hp_addr)
  (protected: obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        proc_idx < Seq.length work /\
        target_idx < Seq.length work /\
        proc_idx <> target_idx /\
        MH.chunk_start (Seq.index work proc_idx) ==
          MH.chunk_start (Seq.index source proc_idx) /\
        MH.chunk_end (Seq.index work proc_idx) ==
          MH.chunk_end (Seq.index source proc_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        ChunkedSweepPending.pending_run_before_start
          work proc_idx (Seq.index source proc_idx).base proc_start
          first_blue run_words /\
        (forall (o: obj_addr).
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source proc_idx) proc_start) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work
            (MH.objects_in_chunk_from (Seq.index source proc_idx) proc_start)
            first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
  =
  ChunkedSweepVertexSeq.chunked_fused_aux_other_chunk_preserves_objects_from_from
    source work proc_idx target_idx proc_start target_start protected
    first_blue run_words fp

let spot_chunked_fused_aux_other_chunk_preserves_objects_from
  (source work: MH.major_heap)
  (proc_idx: nat{proc_idx < Seq.length source})
  (target_idx: nat)
  (target_start: hp_addr)
  (protected: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        proc_idx < Seq.length work /\
        target_idx < Seq.length work /\
        proc_idx <> target_idx /\
        MH.chunk_start (Seq.index work proc_idx) ==
          MH.chunk_start (Seq.index source proc_idx) /\
        MH.chunk_end (Seq.index work proc_idx) ==
          MH.chunk_end (Seq.index source proc_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source proc_idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source proc_idx))
            0UL 0 fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
  =
  ChunkedSweepVertexSeq.chunked_fused_aux_other_chunk_preserves_objects_from
    source work proc_idx target_idx target_start protected fp

let spot_chunked_fused_sweep_coalesce_chunk_range_preserves_objects_from
  (source work: MH.major_heap)
  (start stop target_idx: nat)
  (target_start: hp_addr)
  (protected: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        ChunkedSweepRange.same_chunk_ranges source work /\
        start <= stop /\
        stop <= Seq.length source /\
        target_idx < Seq.length source /\
        target_idx < Seq.length work /\
        (target_idx < start \/ stop <= target_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (idx: nat). start <= idx /\ idx < stop ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source start stop) source work fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
  =
  ChunkedSweepVertexRange.chunked_fused_sweep_coalesce_chunk_range_preserves_objects_from
    source work start stop target_idx target_start protected fp

let spot_chunked_fused_sweep_coalesce_prefix_preserves_objects_from
  (source work: MH.major_heap)
  (target_idx: nat)
  (target_start: hp_addr)
  (protected: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        ChunkedSweepRange.same_chunk_ranges source work /\
        target_idx < Seq.length source /\
        target_idx < Seq.length work /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (idx: nat). idx < target_idx ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source 0 target_idx) source work fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
  =
  ChunkedSweepVertexRange.chunked_fused_sweep_coalesce_prefix_preserves_objects_from
    source work target_idx target_start protected fp

let spot_chunked_fused_sweep_coalesce_suffix_preserves_objects_from
  (source work: MH.major_heap)
  (target_idx: nat)
  (target_start: hp_addr)
  (protected: obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        ChunkedSweepRange.same_chunk_ranges source work /\
        target_idx < Seq.length source /\
        target_idx < Seq.length work /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (idx: nat). target_idx < idx /\ idx < Seq.length source ==>
          forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source idx)) ==>
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source idx) o))
      (ensures
        (let final =
          fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
            (Seq.slice source (target_idx + 1) (Seq.length source))
            source work fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
  =
  ChunkedSweepVertexRange.chunked_fused_sweep_coalesce_suffix_preserves_objects_from
    source work target_idx target_start protected fp

let spot_chunked_fused_sweep_coalesce_prefix_live_field_data_preserved
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
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let work =
           fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source 0 idx) source source fp) in
         ChunkedSweepDefs.chunked_read_header work target == Some hdr /\
         ChunkedSweepDefs.chunked_wosize_of_object work target ==
           Obj.getWosize hdr /\
         ChunkedMajorGCGraph.chunked_major_field_data_preserved
           source work target))
  =
  ChunkedSweepLiveRange.chunked_fused_sweep_coalesce_prefix_live_field_data_preserved
    source idx fp target hdr

let spot_chunked_fused_sweep_coalesce_target_suffix_live_field_preserved_work
  (source work: MH.major_heap)
  (idx: nat)
  (fp: U64.t)
  (target: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap source /\
        MH.well_formed_major_heap work /\
        ChunkedSweepRange.same_chunk_ranges source work /\
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
           U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
           MH.object_wosize_in_chunk (Seq.index source j) o) /\
         ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
         ChunkedSweepDefs.chunked_read_header work target == Some hdr /\
         ChunkedSweepDefs.chunked_is_black source target /\
         U64.v (Obj.getWosize hdr) ==
           MH.object_wosize_in_chunk c target /\
         ChunkedMajorGCGraph.chunked_major_field_data_preserved
           source work target))
      (ensures
        (let c = Seq.index source idx in
         let step =
           ChunkedSweepDefs.chunked_fused_aux
             source work (MH.objects_in_chunk c) 0UL 0 fp in
         let work' = fst step in
         let fp' = snd step in
         let final =
           fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source (idx + 1) (Seq.length source))
             source work' fp') in
         ChunkedMajorGCGraph.chunked_major_field_preserved
           source final target))
  =
  ChunkedSweepLiveRange.chunked_fused_sweep_coalesce_target_suffix_live_field_preserved_work
    source work idx fp target hdr

let spot_chunked_fused_sweep_coalesce_live_field_preserved
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
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let final =
           fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
             source source source fp) in
         ChunkedMajorGCGraph.chunked_major_field_preserved
           source final target))
  =
  ChunkedSweepLiveRange.chunked_fused_sweep_coalesce_live_field_preserved
    source idx fp target hdr

let spot_chunked_fused_sweep_coalesce_live_subgraph_preserved
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
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        (forall (target: obj_addr).
          live target ==>
          live_idx target < Seq.length source /\
          Seq.mem target
            (MH.objects_in_chunk (Seq.index source (live_idx target))) /\
          ChunkedSweepDefs.chunked_read_header source target ==
            Some (live_hdr target) /\
          ChunkedSweepDefs.chunked_is_black source target /\
          U64.v (Obj.getWosize (live_hdr target)) ==
            MH.object_wosize_in_chunk
              (Seq.index source (live_idx target)) target))
      (ensures
        (let final =
           fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
             source source source fp) in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           source final live))
  =
  ChunkedSweepLiveRange.chunked_fused_sweep_coalesce_live_subgraph_preserved
    source fp live live_idx live_hdr

let spot_chunked_fused_sweep_coalesce_live_subgraph_preserved_from_black_membership
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
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        (forall (target: obj_addr).
          live target ==>
          live_idx target < Seq.length source /\
          Seq.mem target
            (MH.objects_in_chunk (Seq.index source (live_idx target))) /\
          ChunkedSweepDefs.chunked_is_black source target))
      (ensures
        (let final =
           fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
             source source source fp) in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           source final live))
  =
  ChunkedSweepLiveRange.chunked_fused_sweep_coalesce_live_subgraph_preserved_from_black_membership
    source fp live live_idx

let spot_chunked_fused_sweep_coalesce_target_suffix_live_field_preserved
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
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source j) o) /\
        ChunkedSweepDefs.chunked_read_header source target == Some hdr /\
        ChunkedSweepDefs.chunked_is_black source target /\
        U64.v (Obj.getWosize hdr) ==
          MH.object_wosize_in_chunk (Seq.index source idx) target)
      (ensures
        (let c = Seq.index source idx in
         let step =
           ChunkedSweepDefs.chunked_fused_aux
             source source (MH.objects_in_chunk c) 0UL 0 fp in
         let work = fst step in
         let fp' = snd step in
         let final =
           fst (ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
             (Seq.slice source (idx + 1) (Seq.length source))
             source work fp') in
         ChunkedMajorGCGraph.chunked_major_field_preserved
           source final target))
  =
  ChunkedSweepLiveRange.chunked_fused_sweep_coalesce_target_suffix_live_field_preserved
    source idx fp target hdr

let spot_chunked_fused_aux_after_member_ready_from_chunk_order
    (source work: MH.major_heap)
    (idx: nat)
    (c: MH.heap_chunk)
    (start: hp_addr)
    (protected_start: hp_addr)
    (protected: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        ChunkedSweepVertexOrder.after_member_chunk_order_pre
          source work idx c start protected_start protected first_blue run_words)
      (ensures
        ChunkedSweepVertexSteps.chunked_fused_aux_after_member_ready
          source work idx protected_start protected
          (MH.objects_in_chunk_from c start) first_blue run_words fp)
  =
  ChunkedSweepVertexOrder.chunked_fused_aux_after_member_ready_from_chunk_order
    source work idx c start protected_start protected first_blue run_words fp
#pop-options

let spot_major_fl_head_wosize_single_chunk_from_dense
  (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
    (requires
      Fields.well_formed_heap g /\
      GC.Gen.FreeListShape.fp_pointer_or_zero fp /\
      GC.Spec.Allocator.Lemmas.fl_valid g fp fuel /\
      fuel > 0)
    (ensures
      SpecMajorAlloc.major_fl_head_wosize
        (MH.single_chunk_major_heap g) fp ==
      (if fp = 0UL then 0
       else if GC.Spec.HeapGraph.is_pointer_field fp
       then U64.v (Obj.wosize_of_object (fp <: obj_addr) g)
       else 0))
  =
  SingleChunkInvariant.major_fl_head_wosize_single_chunk_from_dense g fp fuel

let spot_chunked_major_alloc_shape_single_chunk_from_dense
  (g: heap) (fp: U64.t)
  : Lemma
    (requires GenInv.major_heap_shape g fp)
    (ensures
      GenInv.chunked_major_alloc_shape
        (MH.single_chunk_major_heap g) fp SpecAlloc.alloc_search_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates
        (MH.single_chunk_major_heap g) fp SpecAlloc.alloc_search_fuel = true /\
      GenInv.chunked_chain_objects_blue
        (MH.single_chunk_major_heap g) fp SpecAlloc.alloc_search_fuel)
  =
  SingleChunkInvariant.chunked_major_alloc_shape_single_chunk_from_dense g fp

let spot_chunked_no_black_objects_single_chunk_from_dense
  (g: heap)
  : Lemma
    (requires Mark.no_black_objects g)
    (ensures
      GenInv.chunked_no_black_objects (MH.single_chunk_major_heap g))
  =
  SingleChunkInvariant.chunked_no_black_objects_single_chunk_from_dense g

let spot_chunked_minor_major_fields_no_blue_single_chunk_from_dense
  (minor: minor_state) (g: heap)
  : Lemma
    (requires GenInv.minor_major_fields_no_blue minor g)
    (ensures
      GenInv.chunked_minor_major_fields_no_blue
        minor (MH.single_chunk_major_heap g))
  =
  SingleChunkInvariant.chunked_minor_major_fields_no_blue_single_chunk_from_dense
    minor g

let spot_chunked_no_scan_invariant_single_chunk_from_dense
  (g: heap)
  : Lemma
    (requires Fields.no_scan_invariant g)
    (ensures
      GenInv.chunked_no_scan_invariant (MH.single_chunk_major_heap g))
  =
  SingleChunkInvariant.chunked_no_scan_invariant_single_chunk_from_dense g

let spot_chunked_major_minor_fields_no_infix_targets_single_chunk_from_dense
  (minor: minor_state) (g: heap)
  : Lemma
    (requires GenInv.major_minor_fields_no_infix_targets minor g)
    (ensures
      GenInv.chunked_major_minor_fields_no_infix_targets
        minor (MH.single_chunk_major_heap g))
  =
  SingleChunkInvariant
    .chunked_major_minor_fields_no_infix_targets_single_chunk_from_dense
    minor g

let spot_chunked_no_pointer_to_blue_single_chunk_from_dense
  (g: heap)
  : Lemma
    (requires Fields.well_formed_heap g /\ Mark.no_pointer_to_blue g)
    (ensures
      GenInv.chunked_no_pointer_to_blue (MH.single_chunk_major_heap g))
  =
  SingleChunkInvariant.chunked_no_pointer_to_blue_single_chunk_from_dense g

let spot_chunked_collection_heap_shape_single_chunk_from_dense
  (minor: minor_state) (g: heap) (fp: U64.t)
  : Lemma
    (requires GenInv.collection_heap_shape minor g fp)
    (ensures
      GenInv.chunked_collection_heap_shape
        minor (MH.single_chunk_major_heap g) fp SpecAlloc.alloc_search_fuel /\
      SpecMajorAlloc.major_fl_chain_terminates
        (MH.single_chunk_major_heap g) fp SpecAlloc.alloc_search_fuel = true /\
      GenInv.chunked_chain_objects_blue
        (MH.single_chunk_major_heap g) fp SpecAlloc.alloc_search_fuel)
  =
  SingleChunkInvariant.chunked_collection_heap_shape_single_chunk_from_dense
    minor g fp
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
let spot_chunked_sweep_chunks_step
  (source_chunks work: MH.major_heap) (fp: U64.t)
  : Lemma
      (requires Seq.length source_chunks > 0)
      (ensures
        (let c = Seq.head source_chunks in
         let (work', fp') =
           ChunkedSweepDefs.chunked_sweep_aux
             work (MH.objects_in_chunk c) fp
         in
         ChunkedSweepDefs.chunked_sweep_chunks source_chunks work fp ==
         ChunkedSweepDefs.chunked_sweep_chunks
           (Seq.tail source_chunks) work' fp'))
  =
  ChunkedSweepDefs.chunked_sweep_chunks_step source_chunks work fp

let spot_chunked_fused_aux_empty
  (source work: MH.major_heap) (first_blue: U64.t) (run_words: nat)
  (fp: U64.t)
  : Lemma
      (ChunkedSweepDefs.chunked_fused_aux
         source work Seq.empty first_blue run_words fp ==
       ChunkedSweepDefs.chunked_flush_blue work first_blue run_words fp)
  =
  ChunkedSweepDefs.chunked_fused_aux_empty
    source work first_blue run_words fp

let spot_chunked_fused_aux_black_step
  (source work: MH.major_heap) (objs: Seq.seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0 /\
                ChunkedSweepDefs.chunked_is_black source (Seq.head objs))
      (ensures
        (let obj = Seq.head objs in
         let rest = Seq.tail objs in
         let (work', fp') =
           ChunkedSweepDefs.chunked_flush_blue
             work first_blue run_words fp
         in
         let work'' = ChunkedSweepDefs.chunked_make_white work' obj in
         ChunkedSweepDefs.chunked_fused_aux
           source work objs first_blue run_words fp ==
         ChunkedSweepDefs.chunked_fused_aux source work'' rest 0UL 0 fp'))
  =
  ChunkedSweepDefs.chunked_fused_aux_black_step
    source work objs first_blue run_words fp

let spot_chunked_fused_aux_nonblack_step
  (source work: MH.major_heap) (objs: Seq.seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
      (requires Seq.length objs > 0 /\
                ~(ChunkedSweepDefs.chunked_is_black source (Seq.head objs)))
      (ensures
        (let obj = Seq.head objs in
         let rest = Seq.tail objs in
         let ws =
           U64.v (ChunkedSweepDefs.chunked_wosize_of_object source obj) in
         let new_first : U64.t =
           if run_words = 0 then obj else first_blue in
         ChunkedSweepDefs.chunked_fused_aux
           source work objs first_blue run_words fp ==
         ChunkedSweepDefs.chunked_fused_aux
           source work rest new_first (run_words + ws + 1) fp))
  =
  ChunkedSweepDefs.chunked_fused_aux_nonblack_step
    source work objs first_blue run_words fp

let spot_chunked_fused_aux_nonblack_run_end_at_next_start
    (start: hp_addr)
    (first: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (wz: U64.t)
    (next_start: hp_addr)
  : Lemma
      (requires
        U64.v first == U64.v start + U64.v mword /\
        U64.v next_start ==
          U64.v start + (U64.v wz + 1) * U64.v mword /\
        (run_words = 0 \/
         U64.v first_blue + (run_words - 1) * U64.v mword == U64.v start))
      (ensures
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + U64.v wz + 1 in
         new_run = 0 \/
         U64.v new_first + (new_run - 1) * U64.v mword == U64.v next_start))
  =
  ChunkedSweepPending.chunked_fused_aux_nonblack_run_end_at_next_start
    start first first_blue run_words wz next_start

let spot_pending_run_before_start_index
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires
        ChunkedSweepPending.pending_run_before_start
          work idx base start first_blue run_words)
      (ensures idx < Seq.length work)
  =
  ChunkedSweepPending.pending_run_before_start_index
    work idx base start first_blue run_words

let spot_pending_run_before_start_empty
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
  : Lemma
      (requires idx < Seq.length work)
      (ensures
        ChunkedSweepPending.pending_run_before_start
          work idx base start 0UL 0)
  =
  ChunkedSweepPending.pending_run_before_start_empty
    work idx base start

let spot_pending_run_before_start_nonempty_elim
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: pos)
  : Lemma
      (requires
        ChunkedSweepPending.pending_run_before_start
          work idx base start first_blue run_words)
      (ensures
        idx < Seq.length work /\
        ~(U64.v first_blue < U64.v mword) /\
        ~(U64.v first_blue >= heap_size) /\
        ~(U64.v first_blue % U64.v mword <> 0) /\
        run_words - 1 < pow2 54 /\
        run_words - 1 < pow2 64 /\
        U64.v first_blue + (run_words - 1) * U64.v mword ==
          U64.v start /\
        (let fb : obj_addr = first_blue in
         let hd = hd_address fb in
         Seq.mem fb (MH.objects_in_chunk_from (Seq.index work idx) base) /\
         U64.v fb < MH.chunk_end (Seq.index work idx) /\
         U64.v start <= MH.chunk_end (Seq.index work idx) /\
         MH.word_in_chunk (Seq.index work idx) hd))
  =
  ChunkedSweepPending.pending_run_before_start_nonempty_elim
    work idx base start first_blue run_words

let spot_nonblack_tail_pending_run_before_start_from_empty
    (work: MH.major_heap)
    (idx: nat)
    (base start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
  : Lemma
      (requires
        idx < Seq.length work /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        Seq.mem first (MH.objects_in_chunk_from (Seq.index work idx) base) /\
        U64.v first < MH.chunk_end (Seq.index work idx) /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v start + (U64.v wz + 1) * U64.v mword ==
          U64.v next_start /\
        U64.v next_start <= MH.chunk_end (Seq.index work idx))
      (ensures
        ChunkedSweepPending.pending_run_before_start
          work idx base next_start first (U64.v wz + 1))
  =
  ChunkedSweepPending.nonblack_tail_pending_run_before_start_from_empty
    work idx base start next_start first wz

let spot_nonblack_tail_pending_run_before_start_from_nonempty
    (work: MH.major_heap)
    (idx: nat)
    (base start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
    (first_blue: U64.t)
    (run_words: pos)
  : Lemma
      (requires
        idx < Seq.length work /\
        ChunkedSweepPending.pending_run_before_start
          work idx base start first_blue run_words /\
        U64.v first == U64.v start + U64.v mword /\
        U64.v start + (U64.v wz + 1) * U64.v mword ==
          U64.v next_start /\
        U64.v next_start <= MH.chunk_end (Seq.index work idx))
      (ensures
        ChunkedSweepPending.pending_run_before_start
          work idx base next_start first_blue
          (run_words + U64.v wz + 1))
  =
  ChunkedSweepPending.nonblack_tail_pending_run_before_start_from_nonempty
    work idx base start next_start first wz first_blue run_words

let spot_chunked_fused_sweep_coalesce_chunks_empty_length
  (source_chunks source work: MH.major_heap) (fp: U64.t)
  : Lemma
      (requires Seq.length source_chunks = 0)
      (ensures
        ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
          source_chunks source work fp ==
        (work, fp))
  =
  ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks_empty_length
    source_chunks source work fp

let spot_chunked_fused_sweep_coalesce_chunks_step
  (source_chunks source work: MH.major_heap) (fp: U64.t)
  : Lemma
      (requires Seq.length source_chunks > 0)
      (ensures
        (let c = Seq.head source_chunks in
         let (work', fp') =
           ChunkedSweepDefs.chunked_fused_aux
             source work (MH.objects_in_chunk c) 0UL 0 fp
         in
         ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
           source_chunks source work fp ==
         ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks
           (Seq.tail source_chunks) source work' fp'))
  =
  ChunkedSweepDefs.chunked_fused_sweep_coalesce_chunks_step
    source_chunks source work fp

let spot_chunked_sweep_header_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_read_header
         (MH.single_chunk_major_heap g) obj ==
       Some (read_word g (hd_address obj)))
  =
  ChunkedSweepDefs.chunked_read_header_single_chunk_compat g obj

let spot_chunked_sweep_color_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_color_of_object
         (MH.single_chunk_major_heap g) obj ==
       Some (Obj.color_of_object obj g))
  =
  ChunkedSweepDefs.chunked_color_of_object_single_chunk_compat g obj

let spot_chunked_sweep_wosize_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_wosize_of_object
         (MH.single_chunk_major_heap g) obj ==
       Obj.wosize_of_object obj g)
  =
  ChunkedSweepDefs.chunked_wosize_of_object_single_chunk_compat g obj

let spot_chunked_sweep_tag_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_tag_of_object
         (MH.single_chunk_major_heap g) obj ==
       Obj.tag_of_object obj g)
  =
  ChunkedSweepDefs.chunked_tag_of_object_single_chunk_compat g obj

let spot_chunked_sweep_is_white_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_is_white
         (MH.single_chunk_major_heap g) obj ==
       Obj.is_white obj g)
  =
  ChunkedSweepDefs.chunked_is_white_single_chunk_compat g obj

let spot_chunked_sweep_is_blue_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_is_blue
         (MH.single_chunk_major_heap g) obj ==
       Obj.is_blue obj g)
  =
  ChunkedSweepDefs.chunked_is_blue_single_chunk_compat g obj

let spot_chunked_sweep_is_black_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_is_black
         (MH.single_chunk_major_heap g) obj ==
       Obj.is_black obj g)
  =
  ChunkedSweepDefs.chunked_is_black_single_chunk_compat g obj

let spot_chunked_sweep_is_infix_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_is_infix
         (MH.single_chunk_major_heap g) obj ==
       Obj.is_infix obj g)
  =
  ChunkedSweepDefs.chunked_is_infix_single_chunk_compat g obj

let spot_chunked_color_of_object_some
  (mh: MH.major_heap)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        ChunkedSweepDefs.chunked_color_of_object mh obj ==
        Some (Obj.getColor hdr))
  =
  ChunkedSweepDefs.chunked_color_of_object_some mh obj hdr

let spot_chunked_is_black_from_color
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        ChunkedSweepDefs.chunked_color_of_object mh obj == Some Header.Black)
      (ensures ChunkedSweepDefs.chunked_is_black mh obj)
  =
  ChunkedSweepDefs.chunked_is_black_from_color mh obj

let spot_chunked_is_white_from_color
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        ChunkedSweepDefs.chunked_color_of_object mh obj == Some Header.White)
      (ensures ChunkedSweepDefs.chunked_is_white mh obj)
  =
  ChunkedSweepDefs.chunked_is_white_from_color mh obj

let spot_chunked_is_blue_from_color
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        ChunkedSweepDefs.chunked_color_of_object mh obj == Some Header.Blue)
      (ensures ChunkedSweepDefs.chunked_is_blue mh obj)
  =
  ChunkedSweepDefs.chunked_is_blue_from_color mh obj

let spot_chunked_is_black_read_header
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedSweepDefs.chunked_is_black mh obj)
      (ensures
        (match ChunkedSweepDefs.chunked_read_header mh obj with
         | Some hdr -> Obj.getColor hdr == Header.Black
         | None -> False))
  =
  ChunkedSweepDefs.chunked_is_black_read_header mh obj

let spot_chunked_is_white_not_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedSweepDefs.chunked_is_black mh obj)
      (ensures ~(ChunkedSweepDefs.chunked_is_white mh obj))
  =
  ChunkedSweepDefs.chunked_is_white_not_black mh obj

let spot_chunked_wosize_of_object_some
  (mh: MH.major_heap)
  (obj: obj_addr)
  (hdr: U64.t)
  : Lemma
      (requires ChunkedSweepDefs.chunked_read_header mh obj == Some hdr)
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object mh obj ==
        Obj.getWosize hdr)
  =
  ChunkedSweepDefs.chunked_wosize_of_object_some mh obj hdr

let spot_chunked_wosize_of_object_none
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedSweepDefs.chunked_read_header mh obj == None)
      (ensures ChunkedSweepDefs.chunked_wosize_of_object mh obj == 0UL)
  =
  ChunkedSweepDefs.chunked_wosize_of_object_none mh obj

let spot_chunked_make_white_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_make_white
        (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeWhite obj g))
  =
  ChunkedSweepCompat.chunked_make_white_single_chunk_compat g obj

let spot_chunked_make_blue_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedSweepDefs.chunked_make_blue
        (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeBlue obj g))
  =
  ChunkedSweepCompat.chunked_make_blue_single_chunk_compat g obj

let spot_chunked_sweep_object_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (fp: U64.t)
  : Lemma
      (ChunkedSweepDefs.chunked_sweep_object
        (MH.single_chunk_major_heap g) obj fp ==
       (let (g', fp') = SpecSweep.sweep_object g obj fp in
        (MH.single_chunk_major_heap g', fp')))
  =
  ChunkedSweepCompat.chunked_sweep_object_single_chunk_compat g obj fp

let spot_chunked_sweep_aux_single_chunk_compat
  (g: heap)
  (objs: Seq.seq obj_addr)
  (fp: U64.t)
  : Lemma
      (requires
        forall (o: obj_addr).
          Seq.mem o objs ==> U64.v o >= U64.v zero_addr + U64.v mword)
      (ensures
        ChunkedSweepDefs.chunked_sweep_aux
          (MH.single_chunk_major_heap g) objs fp ==
        (let (g', fp') = SpecSweep.sweep_aux g objs fp in
         (MH.single_chunk_major_heap g', fp')))
  =
  ChunkedSweepCompat.chunked_sweep_aux_single_chunk_compat g objs fp

let spot_chunked_sweep_single_chunk_compat
  (g: heap)
  (fp: U64.t)
  : Lemma
      (ChunkedSweepDefs.chunked_sweep
        (MH.single_chunk_major_heap g) fp ==
       (let (g', fp') = SpecSweep.sweep g fp in
        (MH.single_chunk_major_heap g', fp')))
  =
  ChunkedSweepCompat.chunked_sweep_single_chunk_compat g fp

let spot_chunked_zero_fields_single_chunk_compat
  (g: heap)
  (addr: U64.t)
  (n: nat)
  : Lemma
      (requires n = 0 \/ U64.v addr >= U64.v zero_addr)
      (ensures
        ChunkedSweepDefs.chunked_zero_fields
          (MH.single_chunk_major_heap g) addr n ==
        MH.single_chunk_major_heap (SpecAlloc.zero_fields g addr n))
  =
  ChunkedSweepCompat.chunked_zero_fields_single_chunk_compat g addr n

let spot_chunked_flush_blue_single_chunk_compat
  (g: heap)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        run_words = 0 \/
        U64.v first_blue >= U64.v zero_addr + U64.v mword)
      (ensures
        ChunkedSweepDefs.chunked_flush_blue
          (MH.single_chunk_major_heap g) first_blue run_words fp ==
        (let (g', fp') =
          SpecCoalesce.flush_blue g first_blue run_words fp in
         (MH.single_chunk_major_heap g', fp')))
  =
  ChunkedSweepCompat.chunked_flush_blue_single_chunk_compat
    g first_blue run_words fp

let spot_chunked_fused_aux_single_chunk_compat
  (source work: heap)
  (objs: Seq.seq obj_addr)
  (first_blue: U64.t)
  (run_words: nat)
  (fp: U64.t)
  : Lemma
      (requires
        (forall (o: obj_addr).
          Seq.mem o objs ==> U64.v o >= U64.v zero_addr + U64.v mword) /\
        (run_words = 0 \/
         U64.v first_blue >= U64.v zero_addr + U64.v mword))
      (ensures
        ChunkedSweepDefs.chunked_fused_aux
          (MH.single_chunk_major_heap source)
          (MH.single_chunk_major_heap work)
          objs first_blue run_words fp ==
        (let (work', fp') =
          DenseFused.fused_aux source work objs first_blue run_words fp in
         (MH.single_chunk_major_heap work', fp')))
  =
  ChunkedSweepCompat.chunked_fused_aux_single_chunk_compat
    source work objs first_blue run_words fp

let spot_chunked_fused_sweep_coalesce_single_chunk_compat
  (g: heap)
  : Lemma
      (ChunkedSweepDefs.chunked_fused_sweep_coalesce
        (MH.single_chunk_major_heap g) ==
       (let (g', fp') = DenseFused.fused_sweep_coalesce g in
        (MH.single_chunk_major_heap g', fp')))
  =
  ChunkedSweepCompat.chunked_fused_sweep_coalesce_single_chunk_compat g

let spot_chunked_mark_pointer_field_is_obj_addr
  (mh: MH.major_heap)
  (v: U64.t)
  : Lemma
      (requires ChunkedMarkDefs.chunked_is_pointer_field mh v)
      (ensures U64.v v >= U64.v mword /\
               U64.v v < heap_size /\
               U64.v v % U64.v mword == 0)
  =
  ChunkedMarkDefs.chunked_is_pointer_field_is_obj_addr mh v

let spot_chunked_mark_pointer_field_as_obj_addr_step
  (mh: MH.major_heap)
  (v: U64.t{ChunkedMarkDefs.chunked_is_pointer_field mh v})
  : Lemma
      (ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v == v)
  =
  ChunkedMarkDefs.chunked_pointer_field_as_obj_addr_step mh v

let spot_chunked_make_gray_step
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ChunkedMarkDefs.chunked_make_gray mh obj ==
       ChunkedSweepDefs.chunked_set_object_color mh obj Header.Gray)
  =
  ChunkedMarkDefs.chunked_make_gray_step mh obj

let spot_chunked_make_black_step
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ChunkedMarkDefs.chunked_make_black mh obj ==
       ChunkedSweepDefs.chunked_set_object_color mh obj Header.Black)
  =
  ChunkedMarkDefs.chunked_make_black_step mh obj

let spot_chunked_set_object_color_member_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) ==
        MH.major_objects mh)
  =
  ChunkedMarkPres.chunked_set_object_color_member_preserves_major_objects
    mh obj color

let spot_chunked_make_gray_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects (ChunkedMarkDefs.chunked_make_gray mh obj) ==
        MH.major_objects mh)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_major_objects mh obj

let spot_chunked_make_black_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects (ChunkedMarkDefs.chunked_make_black mh obj) ==
        MH.major_objects mh)
  =
  ChunkedMarkPres.chunked_make_black_preserves_major_objects mh obj

let spot_chunked_set_object_color_member_read_header
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        (match ChunkedSweepDefs.chunked_read_header mh obj with
         | Some hdr ->
           ChunkedSweepDefs.chunked_read_header
             (ChunkedSweepDefs.chunked_set_object_color mh obj color) obj ==
           Some (Obj.colorHeader hdr color)
         | None -> False))
  =
  ChunkedMarkPres.chunked_set_object_color_member_read_header mh obj color

let spot_chunked_set_object_color_preserves_wosize_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) target ==
        ChunkedSweepDefs.chunked_wosize_of_object mh target)
  =
  ChunkedMarkPres.chunked_set_object_color_preserves_wosize_of_object
    mh obj target color

let spot_chunked_set_object_color_preserves_get_field
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <= U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh target))
      (ensures
        ChunkedMarkDefs.chunked_get_field
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) target i ==
        ChunkedMarkDefs.chunked_get_field mh target i)
  =
  ChunkedMarkPres.chunked_set_object_color_preserves_get_field
    mh obj target color i

let spot_chunked_set_object_color_preserves_ranges
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (ensures
        ChunkedSweepRange.same_chunk_ranges mh
          (ChunkedSweepDefs.chunked_set_object_color mh obj color))
  =
  ChunkedMarkPres.chunked_set_object_color_preserves_ranges mh obj color

let spot_chunked_set_object_color_member_sets_color
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_color_of_object
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) obj ==
        Some color)
  =
  ChunkedMarkPres.chunked_set_object_color_member_sets_color mh obj color

let spot_chunked_make_gray_makes_gray
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_color_of_object
          (ChunkedMarkDefs.chunked_make_gray mh obj) obj ==
        Some Header.Gray)
  =
  ChunkedMarkPres.chunked_make_gray_makes_gray mh obj

let spot_chunked_make_gray_preserves_wosize_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (ChunkedMarkDefs.chunked_make_gray mh obj) target ==
        ChunkedSweepDefs.chunked_wosize_of_object mh target)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_wosize_of_object
    mh obj target

let spot_chunked_make_gray_preserves_get_field
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <= U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh target))
      (ensures
        ChunkedMarkDefs.chunked_get_field
          (ChunkedMarkDefs.chunked_make_gray mh obj) target i ==
        ChunkedMarkDefs.chunked_get_field mh target i)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_get_field
    mh obj target i

let spot_chunked_make_gray_preserves_ranges
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ensures
        ChunkedSweepRange.same_chunk_ranges mh
          (ChunkedMarkDefs.chunked_make_gray mh obj))
  =
  ChunkedMarkPres.chunked_make_gray_preserves_ranges mh obj

let spot_chunked_make_black_makes_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkDefs.chunked_make_black mh obj) obj)
  =
  ChunkedMarkPres.chunked_make_black_makes_black mh obj

let spot_chunked_make_black_preserves_wosize_of_object
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (ChunkedMarkDefs.chunked_make_black mh obj) target ==
        ChunkedSweepDefs.chunked_wosize_of_object mh target)
  =
  ChunkedMarkPres.chunked_make_black_preserves_wosize_of_object
    mh obj target

let spot_chunked_make_black_preserves_get_field
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <= U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh target))
      (ensures
        ChunkedMarkDefs.chunked_get_field
          (ChunkedMarkDefs.chunked_make_black mh obj) target i ==
        ChunkedMarkDefs.chunked_get_field mh target i)
  =
  ChunkedMarkPres.chunked_make_black_preserves_get_field
    mh obj target i

let spot_chunked_make_black_preserves_ranges
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ensures
        ChunkedSweepRange.same_chunk_ranges mh
          (ChunkedMarkDefs.chunked_make_black mh obj))
  =
  ChunkedMarkPres.chunked_make_black_preserves_ranges mh obj

let spot_chunked_make_gray_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(ChunkedSweepDefs.chunked_is_blue
          (ChunkedMarkDefs.chunked_make_gray mh obj) obj))
  =
  ChunkedMarkPres.chunked_make_gray_not_blue mh obj

let spot_chunked_make_black_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        ~(ChunkedSweepDefs.chunked_is_blue
          (ChunkedMarkDefs.chunked_make_black mh obj) obj))
  =
  ChunkedMarkPres.chunked_make_black_not_blue mh obj

let spot_chunked_make_gray_preserves_other_blue_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        ChunkedSweepDefs.chunked_is_blue
          (ChunkedMarkDefs.chunked_make_gray mh obj) target ==
        ChunkedSweepDefs.chunked_is_blue mh target)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_other_blue_status mh obj target

let spot_chunked_make_black_preserves_other_blue_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        ChunkedSweepDefs.chunked_is_blue
          (ChunkedMarkDefs.chunked_make_black mh obj) target ==
        ChunkedSweepDefs.chunked_is_blue mh target)
  =
  ChunkedMarkPres.chunked_make_black_preserves_other_blue_status mh obj target

let spot_chunked_set_object_color_preserves_other_black
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_is_black mh target)
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) target)
  =
  ChunkedMarkPres.chunked_set_object_color_preserves_other_black
    mh obj target color

let spot_chunked_set_object_color_preserves_other_black_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_is_black
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) target)
      (ensures ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMarkPres.chunked_set_object_color_preserves_other_black_back
    mh obj target color

let spot_chunked_set_object_color_preserves_other_black_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires obj <> target)
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) target ==
        ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMarkPres.chunked_set_object_color_preserves_other_black_status
    mh obj target color

let spot_chunked_make_gray_preserves_other_black
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_is_black mh target)
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkDefs.chunked_make_gray mh obj) target)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_other_black mh obj target

let spot_chunked_make_gray_preserves_other_black_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkDefs.chunked_make_gray mh obj) target ==
        ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_other_black_status mh obj target

let spot_chunked_make_black_preserves_other_black_status
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires obj <> target)
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkDefs.chunked_make_black mh obj) target ==
        ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMarkPres.chunked_make_black_preserves_other_black_status mh obj target

let spot_chunked_set_object_color_preserves_other_gray
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_color_of_object mh target == Some Header.Gray)
      (ensures
        ChunkedSweepDefs.chunked_color_of_object
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) target ==
        Some Header.Gray)
  =
  ChunkedMarkPres.chunked_set_object_color_preserves_other_gray
    mh obj target color

let spot_chunked_set_object_color_preserves_other_gray_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_color_of_object
          (ChunkedSweepDefs.chunked_set_object_color mh obj color) target ==
        Some Header.Gray)
      (ensures
        ChunkedSweepDefs.chunked_color_of_object mh target ==
        Some Header.Gray)
  =
  ChunkedMarkPres.chunked_set_object_color_preserves_other_gray_back
    mh obj target color

let spot_chunked_make_gray_preserves_other_gray
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_color_of_object mh target == Some Header.Gray)
      (ensures
        ChunkedSweepDefs.chunked_color_of_object
          (ChunkedMarkDefs.chunked_make_gray mh obj) target ==
        Some Header.Gray)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_other_gray mh obj target

let spot_chunked_make_gray_preserves_other_gray_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_color_of_object
          (ChunkedMarkDefs.chunked_make_gray mh obj) target ==
        Some Header.Gray)
      (ensures
        ChunkedSweepDefs.chunked_color_of_object mh target ==
        Some Header.Gray)
  =
  ChunkedMarkPres.chunked_make_gray_preserves_other_gray_back mh obj target

let spot_chunked_make_black_preserves_other_gray
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_color_of_object mh target == Some Header.Gray)
      (ensures
        ChunkedSweepDefs.chunked_color_of_object
          (ChunkedMarkDefs.chunked_make_black mh obj) target ==
        Some Header.Gray)
  =
  ChunkedMarkPres.chunked_make_black_preserves_other_gray mh obj target

let spot_chunked_make_black_preserves_other_gray_back
  (mh: MH.major_heap)
  (obj target: obj_addr)
  : Lemma
      (requires
        obj <> target /\
        ChunkedSweepDefs.chunked_color_of_object
          (ChunkedMarkDefs.chunked_make_black mh obj) target ==
        Some Header.Gray)
      (ensures
        ChunkedSweepDefs.chunked_color_of_object mh target ==
        Some Header.Gray)
  =
  ChunkedMarkPres.chunked_make_black_preserves_other_gray_back mh obj target

let spot_chunked_set_object_color_member_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (ChunkedSweepDefs.chunked_set_object_color mh obj color))
  =
  ChunkedMarkPres.chunked_set_object_color_member_preserves_well_formed
    mh obj color

let spot_chunked_make_gray_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap (ChunkedMarkDefs.chunked_make_gray mh obj))
  =
  ChunkedMarkPres.chunked_make_gray_preserves_well_formed mh obj

let spot_chunked_make_black_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap (ChunkedMarkDefs.chunked_make_black mh obj))
  =
  ChunkedMarkPres.chunked_make_black_preserves_well_formed mh obj

let spot_chunked_push_children_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_push_children_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          ChunkedMarkDefs.chunked_push_children mh st obj i ws in
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedMarkPres.chunked_push_children_preserves_major_objects
    mh st obj i ws

let spot_chunked_push_children_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_push_children_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          ChunkedMarkDefs.chunked_push_children mh st obj i ws in
         MH.well_formed_major_heap mh'))
  =
  ChunkedMarkPres.chunked_push_children_preserves_well_formed
    mh st obj i ws

let spot_chunked_push_children_preserves_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        ChunkedMarkPres.chunked_push_children_preservation_ready mh obj i ws /\
        ChunkedSweepDefs.chunked_is_black mh target)
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_push_children mh st obj i ws in
         ChunkedSweepDefs.chunked_is_black mh' target))
  =
  ChunkedMarkPres.chunked_push_children_preserves_black
    mh st obj target i ws

let spot_chunked_stack_objects_in_major_elim
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        ChunkedMarkPres.stack_objects_in_major mh st /\
        Seq.mem obj st)
      (ensures Seq.mem obj (MH.major_objects mh))
  =
  ChunkedMarkPres.stack_objects_in_major_elim mh st obj

let spot_chunked_stack_objects_in_major_tail
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        ChunkedMarkPres.stack_objects_in_major mh st)
      (ensures ChunkedMarkPres.stack_objects_in_major mh (Seq.tail st))
  =
  ChunkedMarkPres.stack_objects_in_major_tail mh st

let spot_chunked_stack_objects_in_major_empty
  (mh: MH.major_heap)
  : Lemma
      (ensures ChunkedMarkPres.stack_objects_in_major mh Seq.empty)
  =
  ChunkedMarkPres.stack_objects_in_major_empty mh

let spot_chunked_stack_objects_in_major_cons
  (mh: MH.major_heap)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMarkPres.stack_objects_in_major mh st)
      (ensures
        ChunkedMarkPres.stack_objects_in_major mh (Seq.cons obj st))
  =
  ChunkedMarkPres.stack_objects_in_major_cons mh obj st

let spot_chunked_mark_step_empty_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedMarkPres.chunked_mark_step_empty_preserves_major_objects mh st

let spot_chunked_mark_step_empty_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st = 0 /\
        MH.well_formed_major_heap mh)
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))
  =
  ChunkedMarkPres.chunked_mark_step_empty_preserves_well_formed mh st

let spot_chunked_mark_step_no_scan_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedMarkPres.chunked_mark_step_no_scan_preserves_major_objects mh st

let spot_chunked_mark_step_no_scan_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))
  =
  ChunkedMarkPres.chunked_mark_step_no_scan_preserves_well_formed mh st

let spot_chunked_mark_step_no_scan_preserves_stack_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.stack_objects_in_major mh st /\
        ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', st') = ChunkedMarkDefs.chunked_mark_step mh st in
         ChunkedMarkPres.stack_objects_in_major mh' st'))
  =
  ChunkedMarkPres.chunked_mark_step_no_scan_preserves_stack_objects mh st

let spot_chunked_mark_step_scan_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st)) /\
        (let obj = Seq.head st in
         let mh' = ChunkedMarkDefs.chunked_make_black mh obj in
         let ws = ChunkedSweepDefs.chunked_wosize_of_object mh obj in
         ChunkedMarkPres.chunked_push_children_preservation_ready mh' obj 1UL ws))
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedMarkPres.chunked_mark_step_scan_preserves_major_objects mh st

let spot_chunked_mark_step_scan_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st)) /\
        (let obj = Seq.head st in
         let mh' = ChunkedMarkDefs.chunked_make_black mh obj in
         let ws = ChunkedSweepDefs.chunked_wosize_of_object mh obj in
         ChunkedMarkPres.chunked_push_children_preservation_ready mh' obj 1UL ws))
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))
  =
  ChunkedMarkPres.chunked_mark_step_scan_preserves_well_formed mh st

let spot_chunked_mark_step_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedMarkPres.chunked_mark_step_preserves_major_objects mh st

let spot_chunked_mark_step_marks_head_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         ChunkedSweepDefs.chunked_is_black mh' (Seq.head st)))
  =
  ChunkedMarkPres.chunked_mark_step_marks_head_black mh st

let spot_chunked_mark_step_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = ChunkedMarkDefs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))
  =
  ChunkedMarkPres.chunked_mark_step_preserves_well_formed mh st

let spot_chunked_mark_aux_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_aux_preservation_ready mh st fuel)
      (ensures
        MH.major_objects (ChunkedMarkDefs.chunked_mark_aux mh st fuel) ==
        MH.major_objects mh)
  =
  ChunkedMarkPres.chunked_mark_aux_preserves_major_objects mh st fuel

let spot_chunked_mark_aux_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_aux_preservation_ready mh st fuel)
      (ensures
        MH.well_formed_major_heap
          (ChunkedMarkDefs.chunked_mark_aux mh st fuel))
  =
  ChunkedMarkPres.chunked_mark_aux_preserves_well_formed mh st fuel

let spot_chunked_mark_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_preservation_ready mh st)
      (ensures
        MH.major_objects (ChunkedMarkDefs.chunked_mark mh st) ==
        MH.major_objects mh)
  =
  ChunkedMarkPres.chunked_mark_preserves_major_objects mh st

let spot_chunked_mark_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkPres.chunked_mark_preservation_ready mh st)
      (ensures
        MH.well_formed_major_heap (ChunkedMarkDefs.chunked_mark mh st))
  =
  ChunkedMarkPres.chunked_mark_preserves_well_formed mh st

let spot_chunked_mark_step_empty
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures ChunkedMarkDefs.chunked_mark_step mh st == (mh, st))
  =
  ChunkedMarkDefs.chunked_mark_step_empty mh st

let spot_chunked_mark_step_no_scan
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st > 0 /\
                ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let obj = Seq.head st in
         let st' = Seq.tail st in
         ChunkedMarkDefs.chunked_mark_step mh st ==
         (ChunkedMarkDefs.chunked_make_black mh obj, st')))
  =
  ChunkedMarkDefs.chunked_mark_step_no_scan mh st

let spot_chunked_mark_step_scan
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st > 0 /\
                ~(ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st)))
      (ensures
        (let obj = Seq.head st in
         let st' = Seq.tail st in
         let mh' = ChunkedMarkDefs.chunked_make_black mh obj in
         let ws = ChunkedSweepDefs.chunked_wosize_of_object mh obj in
         ChunkedMarkDefs.chunked_mark_step mh st ==
         ChunkedMarkDefs.chunked_push_children mh' st' obj 1UL ws))
  =
  ChunkedMarkDefs.chunked_mark_step_scan mh st

let spot_chunked_mark_aux_step
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat{fuel > 0})
  : Lemma
      (requires Seq.length st > 0)
      (ensures
        (let (mh', st') = ChunkedMarkDefs.chunked_mark_step mh st in
         ChunkedMarkDefs.chunked_mark_aux mh st fuel ==
         ChunkedMarkDefs.chunked_mark_aux mh' st' (fuel - 1)))
  =
  ChunkedMarkDefs.chunked_mark_aux_step mh st fuel

let spot_chunked_mark_equation
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (ChunkedMarkDefs.chunked_mark mh st ==
       ChunkedMarkDefs.chunked_mark_aux mh st (heap_size / U64.v mword))
  =
  ChunkedMarkDefs.chunked_mark_equation mh st

let spot_chunked_get_field_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (ChunkedMarkDefs.chunked_get_field
        (MH.single_chunk_major_heap g) obj i ==
       GC.Spec.HeapGraph.get_field g obj i)
  =
  ChunkedMarkCompat.chunked_get_field_single_chunk_compat g obj i

let spot_chunked_mark_pointer_field_single_chunk_compat
  (g: heap)
  (v: U64.t)
  : Lemma
      (ChunkedMarkDefs.chunked_is_pointer_field
        (MH.single_chunk_major_heap g) v ==
       GC.Spec.HeapGraph.is_pointer_field v)
  =
  ChunkedMarkCompat.chunked_is_pointer_field_single_chunk_compat g v

let spot_chunked_make_gray_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedMarkDefs.chunked_make_gray
        (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeGray obj g))
  =
  ChunkedMarkCompat.chunked_make_gray_single_chunk_compat g obj

let spot_chunked_make_black_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedMarkDefs.chunked_make_black
        (MH.single_chunk_major_heap g) obj ==
       MH.single_chunk_major_heap (Obj.makeBlack obj g))
  =
  ChunkedMarkCompat.chunked_make_black_single_chunk_compat g obj

let spot_chunked_mark_no_scan_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedMarkDefs.chunked_is_no_scan
        (MH.single_chunk_major_heap g) obj ==
       Obj.is_no_scan obj g)
  =
  ChunkedMarkCompat.chunked_is_no_scan_single_chunk_compat g obj

let spot_chunked_resolve_object_single_chunk_compat
  (g: heap)
  (addr: obj_addr{U64.v addr >= U64.v zero_addr + U64.v mword})
  : Lemma
      (requires
        Obj.is_infix addr g ==>
        (let p = Obj.parent_closure_addr_nat addr g in
         p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
         Fields.is_pointer (U64.uint_to_t p)))
      (ensures
        ChunkedMarkDefs.chunked_resolve_object
          (MH.single_chunk_major_heap g) addr ==
        Obj.resolve_object addr g)
  =
  ChunkedMarkCompat.chunked_resolve_object_single_chunk_compat g addr

let spot_chunked_mark_step_empty_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        ChunkedMarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkCompat.chunked_mark_step_empty_single_chunk_compat g st

let spot_chunked_mark_step_no_scan_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st > 0 /\
                U64.v (Seq.head st) >= U64.v zero_addr + U64.v mword /\
                Obj.is_no_scan (Seq.head st) g)
      (ensures
        ChunkedMarkDefs.chunked_mark_step (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkCompat.chunked_mark_step_no_scan_single_chunk_compat g st

let spot_chunked_push_children_no_pointer_fields_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        ChunkedMarkNoPointer.no_pointer_fields g obj i ws)
      (ensures
        ChunkedMarkDefs.chunked_push_children
          (MH.single_chunk_major_heap g) st obj i ws ==
        (let (g', st') = Mark.push_children g st obj i ws in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkNoPointer.chunked_push_children_no_pointer_fields_single_chunk_compat
    g st obj i ws

let spot_chunked_mark_step_scan_no_pointer_fields_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        U64.v (Seq.head st) >= U64.v zero_addr + U64.v mword /\
        ~(Obj.is_no_scan (Seq.head st) g) /\
        ChunkedMarkNoPointer.no_pointer_fields
          (Obj.makeBlack (Seq.head st) g)
          (Seq.head st)
          1UL
          (Obj.wosize_of_object (Seq.head st) g))
      (ensures
        ChunkedMarkDefs.chunked_mark_step
          (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkNoPointer.chunked_mark_step_scan_no_pointer_fields_single_chunk_compat
    g st

let spot_chunked_push_children_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        ChunkedMarkPush.push_children_single_chunk_ready g obj i ws)
      (ensures
        ChunkedMarkDefs.chunked_push_children
          (MH.single_chunk_major_heap g) st obj i ws ==
        (let (g', st') = Mark.push_children g st obj i ws in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkPush.chunked_push_children_single_chunk_compat g st obj i ws

let spot_chunked_mark_step_scan_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        U64.v (Seq.head st) >= U64.v zero_addr + U64.v mword /\
        ~(Obj.is_no_scan (Seq.head st) g) /\
        ChunkedMarkPush.push_children_single_chunk_ready
          (Obj.makeBlack (Seq.head st) g)
          (Seq.head st)
          1UL
          (Obj.wosize_of_object (Seq.head st) g))
      (ensures
        ChunkedMarkDefs.chunked_mark_step
          (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkPush.chunked_mark_step_scan_single_chunk_compat g st

let spot_chunked_mark_step_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires ChunkedMarkLoop.mark_step_single_chunk_ready g st)
      (ensures
        ChunkedMarkDefs.chunked_mark_step
          (MH.single_chunk_major_heap g) st ==
        (let (g', st') = Mark.mark_step g st in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkLoop.chunked_mark_step_single_chunk_compat g st

let spot_chunked_mark_aux_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires ChunkedMarkLoop.mark_aux_single_chunk_ready g st fuel)
      (ensures
        ChunkedMarkDefs.chunked_mark_aux
          (MH.single_chunk_major_heap g) st fuel ==
        MH.single_chunk_major_heap (Mark.mark_aux g st fuel))
  =
  ChunkedMarkLoop.chunked_mark_aux_single_chunk_compat g st fuel

let spot_chunked_mark_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        ChunkedMarkLoop.mark_aux_single_chunk_ready
          g st (heap_size / U64.v mword))
      (ensures
        ChunkedMarkDefs.chunked_mark (MH.single_chunk_major_heap g) st ==
        MH.single_chunk_major_heap (Mark.mark g st))
  =
  ChunkedMarkLoop.chunked_mark_single_chunk_compat g st

let spot_chunked_mark_bounded_is_gray_step
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (ChunkedMarkBounded.chunked_is_gray mh obj ==
       (match ChunkedSweepDefs.chunked_color_of_object mh obj with
        | Some Header.Gray -> true
        | _ -> false))
  =
  ChunkedMarkBounded.chunked_is_gray_step mh obj

let spot_chunked_is_gray_from_color
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        ChunkedSweepDefs.chunked_color_of_object mh obj == Some Header.Gray)
      (ensures ChunkedMarkBounded.chunked_is_gray mh obj)
  =
  ChunkedMarkBounded.chunked_is_gray_from_color mh obj

let spot_chunked_is_gray_read_header
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedMarkBounded.chunked_is_gray mh obj)
      (ensures
        (match ChunkedSweepDefs.chunked_read_header mh obj with
         | Some hdr -> Obj.getColor hdr == Header.Gray
         | None -> False))
  =
  ChunkedMarkBounded.chunked_is_gray_read_header mh obj

let spot_chunked_push_children_bounded_step
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires U64.v i <= U64.v ws)
      (ensures
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         let (mh', st') =
           if ChunkedMarkDefs.chunked_is_pointer_field mh v then
             let child_raw =
               ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
             let child = ChunkedMarkDefs.chunked_resolve_object mh child_raw in
             if ChunkedSweepDefs.chunked_is_white mh child then
               let mh' = ChunkedMarkDefs.chunked_make_gray mh child in
               if Seq.length st < cap then
                 (mh', Seq.cons child st)
               else
                 (mh', st)
             else
               (mh, st)
           else
             (mh, st)
         in
         ChunkedMarkBounded.chunked_push_children_bounded
           mh st obj i ws cap ==
         (if U64.v i < U64.v ws then
            ChunkedMarkBounded.chunked_push_children_bounded
              mh' st' obj (U64.add i 1UL) ws cap
          else
            (mh', st'))))
  =
  ChunkedMarkBounded.chunked_push_children_bounded_step
    mh st obj i ws cap

let spot_chunked_mark_step_bounded_scan
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires Seq.length st > 0 /\
                ~(ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st)))
      (ensures
        (let obj = Seq.head st in
         let st' = Seq.tail st in
         let mh' = ChunkedMarkDefs.chunked_make_black mh obj in
         let ws = ChunkedSweepDefs.chunked_wosize_of_object mh obj in
         ChunkedMarkBounded.chunked_mark_step_bounded mh st cap ==
         ChunkedMarkBounded.chunked_push_children_bounded
           mh' st' obj 1UL ws cap))
  =
  ChunkedMarkBounded.chunked_mark_step_bounded_scan mh st cap

let spot_chunked_rescan_heap_equation
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (ChunkedMarkBounded.chunked_rescan_heap mh st cap ==
       ChunkedMarkBounded.chunked_rescan_objects
         mh (MH.major_objects mh) st cap)
  =
  ChunkedMarkBounded.chunked_rescan_heap_equation mh st cap

let spot_chunked_mark_bounded_step
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat{fuel > 0})
  : Lemma
      (ensures
        (let st = ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap in
         ChunkedMarkBounded.chunked_mark_bounded mh cap fuel ==
         (if Seq.length st = 0 then mh
          else
            let inner_fuel =
              ChunkedMarkBounded.chunked_count_non_black mh in
            let (mh', _) =
              ChunkedMarkBounded.chunked_mark_inner_loop
                mh st cap inner_fuel in
            ChunkedMarkBounded.chunked_mark_bounded
              mh' cap (fuel - 1))))
  =
  ChunkedMarkBounded.chunked_mark_bounded_step mh cap fuel

let spot_chunked_push_children_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedMarkBoundedPres.chunked_push_children_bounded_preserves_major_objects
    mh st obj i ws cap

let spot_chunked_push_children_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         MH.well_formed_major_heap mh'))
  =
  ChunkedMarkBoundedPres.chunked_push_children_bounded_preserves_well_formed
    mh st obj i ws cap

let spot_chunked_push_children_bounded_preserves_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        ChunkedSweepDefs.chunked_is_black mh target)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         ChunkedSweepDefs.chunked_is_black mh' target))
  =
  ChunkedMarkBoundedPres.chunked_push_children_bounded_preserves_black
    mh st obj target i ws cap

let spot_chunked_push_children_bounded_ready_child
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         ChunkedMarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw =
            ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = ChunkedMarkDefs.chunked_resolve_object mh child_raw in
          ChunkedSweepDefs.chunked_is_white mh child)))
      (ensures
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         let child_raw =
           ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child = ChunkedMarkDefs.chunked_resolve_object mh child_raw in
         Seq.mem child (MH.major_objects mh)))
  =
  ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready_child
    mh obj i ws

let spot_chunked_push_children_bounded_ready_next
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        U64.v i < U64.v ws /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws)
      (ensures
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         let mh' =
           if ChunkedMarkDefs.chunked_is_pointer_field mh v then
             let child_raw =
               ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
             let child = ChunkedMarkDefs.chunked_resolve_object mh child_raw in
             if ChunkedSweepDefs.chunked_is_white mh child then
               ChunkedMarkDefs.chunked_make_gray mh child
             else
               mh
           else
             mh in
         ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
           mh' obj (U64.add i 1UL) ws))
  =
  ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready_next
    mh obj i ws

let spot_chunked_push_children_bounded_ready_from_target_membership
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        ChunkedMarkBoundedReadiness.chunked_push_children_target_membership_policy
          mh obj i ws)
      (ensures
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws)
  =
  ChunkedMarkBoundedReadiness.chunked_push_children_bounded_preservation_ready_from_target_membership
    mh obj i ws

let spot_chunked_scanned_white_targets_in_major_elim
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        ChunkedMarkBoundedTargetMembership.chunked_scanned_white_targets_in_major
          mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh obj) /\
        U64.v i <=
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh obj) /\
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         ChunkedMarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw =
           ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = ChunkedMarkDefs.chunked_resolve_object mh child_raw in
          ChunkedSweepDefs.chunked_is_white mh child)))
      (ensures
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         let child_raw =
           ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child = ChunkedMarkDefs.chunked_resolve_object mh child_raw in
         Seq.mem child (MH.major_objects mh)))
  =
  ChunkedMarkBoundedTargetMembership.chunked_scanned_white_targets_in_major_elim
    mh obj i

let spot_chunked_scanned_white_targets_in_major_from_raw_targets
  (mh: MH.major_heap)
  : Lemma
      (requires
        ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major
          mh)
      (ensures
        ChunkedMarkBoundedTargetMembership.chunked_scanned_white_targets_in_major
          mh)
  =
  ChunkedMarkBoundedTargetMembership.chunked_scanned_white_targets_in_major_from_raw_targets
    mh

let spot_chunked_scanned_raw_targets_in_major_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (obj: obj_addr) (i: U64.t{U64.v i >= 1}).
          Seq.mem obj (MH.major_objects mh) /\
          ~(ChunkedMarkDefs.chunked_is_no_scan mh obj) /\
          U64.v i <= U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh obj) ==>
          (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
           if ChunkedMarkDefs.chunked_is_pointer_field mh v then
             let child_raw =
               ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
             Seq.mem child_raw (MH.major_objects mh) /\
             ~(ChunkedSweepDefs.chunked_is_infix mh child_raw)
           else
             True))
      (ensures
        ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major
          mh)
  =
  ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major_intro
    mh

let spot_chunked_push_children_target_membership_policy_from_scanned_targets
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh obj) /\
        U64.v ws <=
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh obj) /\
        ChunkedMarkBoundedTargetMembership.chunked_push_children_scanned_targets_policy
          mh obj i ws)
      (ensures
        ChunkedMarkBoundedReadiness.chunked_push_children_target_membership_policy
          mh obj i ws)
  =
  ChunkedMarkBoundedTargetMembership.chunked_push_children_target_membership_policy_from_scanned_targets
    mh obj i ws

let spot_chunked_mark_step_target_membership_policy_from_scanned_targets
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedTargetMembership.chunked_mark_step_scanned_targets_policy
          mh st cap)
      (ensures
        ChunkedMarkBoundedReadiness.chunked_mark_step_target_membership_policy
          mh st cap)
  =
  ChunkedMarkBoundedTargetMembership.chunked_mark_step_target_membership_policy_from_scanned_targets
    mh st cap

let spot_chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedTargetMembership.chunked_mark_inner_loop_scanned_targets_policy
          mh st cap fuel)
      (ensures
        ChunkedMarkBoundedReadiness.chunked_mark_inner_loop_target_membership_policy
          mh st cap fuel)
  =
  ChunkedMarkBoundedTargetMembership.chunked_mark_inner_loop_target_membership_policy_from_scanned_targets
    mh st cap fuel

let spot_chunked_mark_bounded_target_membership_policy_from_scanned_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_scanned_targets_policy
          mh cap fuel)
      (ensures
        ChunkedMarkBoundedReadiness.chunked_mark_bounded_target_membership_policy
          mh cap fuel)
  =
  ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_target_membership_policy_from_scanned_targets
    mh cap fuel

let spot_chunked_mark_bounded_scanned_targets_policy_from_raw_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_raw_targets_policy
          mh cap fuel)
      (ensures
        ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_scanned_targets_policy
          mh cap fuel)
  =
  ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_scanned_targets_policy_from_raw_targets
    mh cap fuel

let spot_chunked_mark_bounded_target_membership_policy_from_raw_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_raw_targets_policy
          mh cap fuel)
      (ensures
        ChunkedMarkBoundedReadiness.chunked_mark_bounded_target_membership_policy
          mh cap fuel)
  =
  ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_target_membership_policy_from_raw_targets
    mh cap fuel

let spot_chunked_mark_bounded_preservation_ready_from_scanned_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_scanned_targets_policy
          mh cap fuel)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel)
  =
  ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_preservation_ready_from_scanned_targets
    mh cap fuel

let spot_chunked_mark_bounded_preservation_ready_from_raw_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_raw_targets_policy
          mh cap fuel)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel)
  =
  ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_preservation_ready_from_raw_targets
    mh cap fuel

let spot_chunked_mark_bounded_raw_targets_policy_from_static
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major
          mh /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= Seq.length (MH.major_objects mh))
      (ensures
        ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_raw_targets_policy
          mh cap fuel)
  =
  ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_raw_targets_policy_from_static
    mh cap fuel

let spot_chunked_push_children_bounded_preserves_black_status
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         ChunkedSweepDefs.chunked_is_black mh' target ==
         ChunkedSweepDefs.chunked_is_black mh target))
  =
  ChunkedMarkBoundedPres.chunked_push_children_bounded_preserves_black_status
    mh st obj target i ws cap

let spot_chunked_mark_step_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedMarkBoundedPres.chunked_mark_step_bounded_preserves_major_objects
    mh st cap

let spot_chunked_mark_step_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         MH.well_formed_major_heap mh'))
  =
  ChunkedMarkBoundedPres.chunked_mark_step_bounded_preserves_well_formed
    mh st cap

let spot_chunked_mark_step_bounded_marks_head_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedSweepDefs.chunked_is_black mh' (Seq.head st)))
  =
  ChunkedMarkBoundedPres.chunked_mark_step_bounded_marks_head_black mh st cap

let spot_chunked_mark_step_bounded_preserves_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedSweepDefs.chunked_is_black mh target)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedSweepDefs.chunked_is_black mh' target))
  =
  ChunkedMarkBoundedPres.chunked_mark_step_bounded_preserves_black
    mh st cap target

let spot_chunked_mark_step_bounded_ready_scan
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh (Seq.head st)))
      (ensures
        (let obj = Seq.head st in
         let mh' = ChunkedMarkDefs.chunked_make_black mh obj in
         let ws = ChunkedSweepDefs.chunked_wosize_of_object mh obj in
         ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
           mh' obj 1UL ws))
  =
  ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready_scan
    mh st cap

let spot_chunked_mark_step_bounded_ready_from_target_membership
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedReadiness.chunked_mark_step_target_membership_policy
          mh st cap)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap)
  =
  ChunkedMarkBoundedReadiness.chunked_mark_step_bounded_preservation_ready_from_target_membership
    mh st cap

let spot_chunked_mark_step_bounded_preserves_other_black_status
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        target <> Seq.head st /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedSweepDefs.chunked_is_black mh' target ==
         ChunkedSweepDefs.chunked_is_black mh target))
  =
  ChunkedMarkBoundedPres.chunked_mark_step_bounded_preserves_other_black_status
    mh st cap target

let spot_chunked_mark_step_bounded_decreases_count
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ChunkedMarkBounded.chunked_is_gray mh (Seq.head st))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMarkBounded.chunked_count_non_black mh' <
         ChunkedMarkBounded.chunked_count_non_black mh))
  =
  ChunkedMarkBoundedCountStep.chunked_mark_step_bounded_decreases_count
    mh st cap

let spot_chunked_is_white_not_gray
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedSweepDefs.chunked_is_white mh obj)
      (ensures ~(ChunkedMarkBounded.chunked_is_gray mh obj))
  =
  ChunkedMarkBoundedStackStep.chunked_is_white_not_gray mh obj

let spot_chunked_push_children_bounded_preserves_stack_props
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', st') =
          ChunkedMarkBounded.chunked_push_children_bounded mh st obj i ws cap in
         ChunkedMarkBoundedReady.chunked_bounded_stack_props mh' st'))
  =
  ChunkedMarkBoundedStackStep.chunked_push_children_bounded_preserves_bounded_stack_props
    mh st obj i ws cap

let spot_chunked_mark_step_bounded_preserves_stack_props
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st)
      (ensures
        (let (mh', st') =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMarkBoundedReady.chunked_bounded_stack_props mh' st'))
  =
  ChunkedMarkBoundedStackStep.chunked_mark_step_bounded_preserves_bounded_stack_props
    mh st cap

let spot_chunked_mark_inner_loop_preservation_ready_step
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        Seq.length st > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        (let (mh', st') =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
           mh' st' cap (fuel - 1)))
  =
  ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready_step
    mh st cap fuel

let spot_chunked_mark_inner_loop_ready_from_target_membership
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedReadiness.chunked_mark_inner_loop_target_membership_policy
          mh st cap fuel)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel)
  =
  ChunkedMarkBoundedReadiness.chunked_mark_inner_loop_preservation_ready_from_target_membership
    mh st cap fuel

let spot_chunked_mark_inner_loop_marks_stack_member_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        Seq.mem target st)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_target_ready
          mh st cap fuel target)
  =
  ChunkedMarkBoundedStackReady.chunked_mark_inner_loop_marks_stack_member_ready
    mh st cap fuel target

let spot_chunked_mark_bounded_preservation_ready_step
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        (let st =
          ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap in
         Seq.length st > 0))
      (ensures
        (let st =
          ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap in
         let inner_fuel =
          ChunkedMarkBounded.chunked_count_non_black mh in
         ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap inner_fuel /\
         (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap inner_fuel in
          ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
            mh' cap (fuel - 1))))
  =
  ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready_step
    mh cap fuel

let spot_chunked_mark_bounded_ready_from_target_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedReadiness.chunked_mark_bounded_target_membership_policy
          mh cap fuel)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel)
  =
  ChunkedMarkBoundedReadiness.chunked_mark_bounded_preservation_ready_from_target_membership
    mh cap fuel

let spot_chunked_mark_bounded_marks_rescan_ready_from_inner
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        ~ (ChunkedSweepDefs.chunked_is_black mh target) /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        (let st =
          ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap in
         Seq.length st > 0 /\
         (let inner_fuel =
          ChunkedMarkBounded.chunked_count_non_black mh in
          ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_target_ready
            mh st cap inner_fuel target)))
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
  =
  ChunkedMarkBoundedPres.chunked_mark_bounded_marks_rescan_ready_from_inner
    mh cap fuel target

let spot_chunked_mark_bounded_marks_rescan_member_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.mem target (MH.major_objects mh) /\
        ChunkedMarkBounded.chunked_is_gray mh target /\
        Seq.length (MH.major_objects mh) <= cap)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
  =
  ChunkedMarkBoundedStackReady.chunked_mark_bounded_marks_rescan_member_ready
    mh cap fuel target

let spot_chunked_mark_bounded_marks_rescan_gray_or_black_member_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.mem target (MH.major_objects mh) /\
        (ChunkedMarkBounded.chunked_is_gray mh target \/
         ChunkedSweepDefs.chunked_is_black mh target) /\
        Seq.length (MH.major_objects mh) <= cap)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
  =
  ChunkedMarkBoundedStackReady.chunked_mark_bounded_marks_rescan_gray_or_black_member_ready
    mh cap fuel target

let spot_chunked_push_children_bounded_preserves_wosize_of_object
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
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         ChunkedSweepDefs.chunked_wosize_of_object mh' target ==
         ChunkedSweepDefs.chunked_wosize_of_object mh target))
  =
  ChunkedMarkBoundedMetadata.chunked_push_children_bounded_preserves_wosize_of_object
    mh st obj i ws cap target

let spot_chunked_push_children_bounded_preserves_get_field
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (target: obj_addr)
  (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         ChunkedMarkDefs.chunked_get_field mh' target j ==
         ChunkedMarkDefs.chunked_get_field mh target j))
  =
  ChunkedMarkBoundedMetadata.chunked_push_children_bounded_preserves_get_field
    mh st obj i ws cap target j

let spot_chunked_push_children_bounded_preserves_ranges
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded mh st obj i ws cap in
         ChunkedSweepRange.same_chunk_ranges mh mh'))
  =
  ChunkedMarkBoundedMetadata.chunked_push_children_bounded_preserves_ranges
    mh st obj i ws cap

let spot_chunked_mark_step_bounded_preserves_wosize_of_object
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedSweepDefs.chunked_wosize_of_object mh' target ==
         ChunkedSweepDefs.chunked_wosize_of_object mh target))
  =
  ChunkedMarkBoundedMetadata.chunked_mark_step_bounded_preserves_wosize_of_object
    mh st cap target

let spot_chunked_mark_step_bounded_preserves_get_field
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMarkDefs.chunked_get_field mh' target j ==
         ChunkedMarkDefs.chunked_get_field mh target j))
  =
  ChunkedMarkBoundedMetadata.chunked_mark_step_bounded_preserves_get_field
    mh st cap target j

let spot_chunked_mark_step_bounded_preserves_ranges
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (ensures
        (let (mh', _) = ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedSweepRange.same_chunk_ranges mh mh'))
  =
  ChunkedMarkBoundedMetadata.chunked_mark_step_bounded_preserves_ranges
    mh st cap

let spot_chunked_mark_inner_loop_preserves_wosize_of_object
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedSweepDefs.chunked_wosize_of_object mh' target ==
         ChunkedSweepDefs.chunked_wosize_of_object mh target))
  =
  ChunkedMarkBoundedMetadata.chunked_mark_inner_loop_preserves_wosize_of_object
    mh st cap fuel target

let spot_chunked_mark_inner_loop_preserves_get_field
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh target))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedMarkDefs.chunked_get_field mh' target j ==
         ChunkedMarkDefs.chunked_get_field mh target j))
  =
  ChunkedMarkBoundedMetadata.chunked_mark_inner_loop_preserves_get_field
    mh st cap fuel target j

let spot_chunked_mark_inner_loop_preserves_ranges
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (ensures
        (let (mh', _) = ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedSweepRange.same_chunk_ranges mh mh'))
  =
  ChunkedMarkBoundedMetadata.chunked_mark_inner_loop_preserves_ranges
    mh st cap fuel

let spot_chunked_mark_bounded_preserves_wosize_of_object
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target ==
        ChunkedSweepDefs.chunked_wosize_of_object mh target)
  =
  ChunkedMarkBoundedMetadata.chunked_mark_bounded_preserves_wosize_of_object
    mh cap fuel target

let spot_chunked_mark_bounded_preserves_get_field
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  (j: U64.t{U64.v j >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v j <= U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh target))
      (ensures
        ChunkedMarkDefs.chunked_get_field
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target j ==
        ChunkedMarkDefs.chunked_get_field mh target j)
  =
  ChunkedMarkBoundedMetadata.chunked_mark_bounded_preserves_get_field
    mh cap fuel target j

let spot_chunked_mark_bounded_preserves_ranges
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (ensures
        ChunkedSweepRange.same_chunk_ranges mh
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMarkBoundedMetadata.chunked_mark_bounded_preserves_ranges
    mh cap fuel

let spot_chunked_mark_inner_loop_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedMarkBoundedPres.chunked_mark_inner_loop_preserves_major_objects
    mh st cap fuel

let spot_chunked_mark_inner_loop_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         MH.well_formed_major_heap mh'))
  =
  ChunkedMarkBoundedPres.chunked_mark_inner_loop_preserves_well_formed
    mh st cap fuel

let spot_chunked_mark_inner_loop_preserves_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedSweepDefs.chunked_is_black mh target)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedSweepDefs.chunked_is_black mh' target))
  =
  ChunkedMarkBoundedPres.chunked_mark_inner_loop_preserves_black
    mh st cap fuel target

let spot_chunked_mark_inner_loop_marks_target_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_target_ready
          mh st cap fuel target)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedSweepDefs.chunked_is_black mh' target))
  =
  ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_target_black
    mh st cap fuel target

let spot_chunked_mark_inner_loop_marks_head_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        Seq.length st > 0 /\
        target == Seq.head st /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_target_ready
          mh st cap fuel target)
  =
  ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_head_ready
    mh st cap fuel target

let spot_chunked_mark_inner_loop_marks_tail_ready_from_step
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        Seq.length st > 0 /\
        target <> Seq.head st /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        (let (mh', st') =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_target_ready
           mh' st' cap (fuel - 1) target))
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_target_ready
          mh st cap fuel target)
  =
  ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_tail_ready_from_step
    mh st cap fuel target

let spot_chunked_mark_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel)
      (ensures
        MH.major_objects
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) ==
        MH.major_objects mh)
  =
  ChunkedMarkBoundedPres.chunked_mark_bounded_preserves_major_objects
    mh cap fuel

let spot_chunked_mark_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel)
      (ensures
        MH.well_formed_major_heap
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMarkBoundedPres.chunked_mark_bounded_preserves_well_formed
    mh cap fuel

let spot_chunked_mark_bounded_preserves_black
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedSweepDefs.chunked_is_black mh target)
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMarkBoundedPres.chunked_mark_bounded_preserves_black
    mh cap fuel target

let spot_chunked_mark_bounded_marks_target_black
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_black
    mh cap fuel target

let spot_chunked_mark_bounded_rescan_head_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        (let st =
          ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap in
         Seq.length st > 0 /\
         target == Seq.head st /\
         Seq.mem target (MH.major_objects mh)))
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
  =
  ChunkedMarkBoundedReady.chunked_mark_bounded_marks_rescan_head_ready
    mh cap fuel target

let spot_chunked_mark_bounded_ready_from_later_rescan
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        ~ (ChunkedSweepDefs.chunked_is_black mh target) /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        (let st =
          ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap in
         Seq.length st > 0 /\
         (let inner_fuel =
           ChunkedMarkBounded.chunked_count_non_black mh in
          let (mh', _) =
            ChunkedMarkBounded.chunked_mark_inner_loop
              mh st cap inner_fuel in
          ~ (ChunkedMarkBoundedPres.chunked_mark_inner_loop_marks_target_ready
              mh st cap inner_fuel target) /\
          ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
            mh' cap (fuel - 1) target)))
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
  =
  ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready_from_later_rescan
    mh cap fuel target

let spot_chunked_count_non_black_in_bound
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  : Lemma
      (ensures
        ChunkedMarkBounded.chunked_count_non_black_in mh objs <=
        Seq.length objs)
  =
  ChunkedMarkBoundedReady.chunked_count_non_black_in_bound mh objs

let spot_chunked_count_non_black_bound
  (mh: MH.major_heap)
  : Lemma
      (ensures
        ChunkedMarkBounded.chunked_count_non_black mh <=
        Seq.length (MH.major_objects mh))
  =
  ChunkedMarkBoundedReady.chunked_count_non_black_bound mh

let spot_chunked_count_non_black_in_preserved_by_black_status
  (mh mh': MH.major_heap)
  (objs: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (obj: obj_addr).
          Seq.mem obj objs ==>
            ChunkedSweepDefs.chunked_is_black mh' obj ==
            ChunkedSweepDefs.chunked_is_black mh obj))
      (ensures
        ChunkedMarkBounded.chunked_count_non_black_in mh' objs ==
        ChunkedMarkBounded.chunked_count_non_black_in mh objs)
  =
  ChunkedMarkBoundedCount.chunked_count_non_black_in_preserved_by_black_status
    mh mh' objs

let spot_chunked_count_non_black_preserved_by_black_status
  (mh mh': MH.major_heap)
  : Lemma
      (requires
        MH.major_objects mh' == MH.major_objects mh /\
        (forall (obj: obj_addr).
          Seq.mem obj (MH.major_objects mh) ==>
            ChunkedSweepDefs.chunked_is_black mh' obj ==
            ChunkedSweepDefs.chunked_is_black mh obj))
      (ensures
        ChunkedMarkBounded.chunked_count_non_black mh' ==
        ChunkedMarkBounded.chunked_count_non_black mh)
  =
  ChunkedMarkBoundedCount.chunked_count_non_black_preserved_by_black_status
    mh mh'

let spot_chunked_count_non_black_in_black_status_flip_le
  (mh mh': MH.major_heap)
  (objs: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        ChunkedSweepDefs.chunked_is_black mh' target /\
        (forall (obj: obj_addr).
          Seq.mem obj objs /\ obj <> target ==>
            ChunkedSweepDefs.chunked_is_black mh' obj ==
            ChunkedSweepDefs.chunked_is_black mh obj))
      (ensures
        ChunkedMarkBounded.chunked_count_non_black_in mh' objs <=
        ChunkedMarkBounded.chunked_count_non_black_in mh objs)
  =
  ChunkedMarkBoundedCount.chunked_count_non_black_in_black_status_flip_le
    mh mh' objs target

let spot_chunked_count_non_black_in_black_status_flip_decreases
  (mh mh': MH.major_heap)
  (objs: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.mem target objs /\
        ~(ChunkedSweepDefs.chunked_is_black mh target) /\
        ChunkedSweepDefs.chunked_is_black mh' target /\
        (forall (obj: obj_addr).
          Seq.mem obj objs /\ obj <> target ==>
            ChunkedSweepDefs.chunked_is_black mh' obj ==
            ChunkedSweepDefs.chunked_is_black mh obj))
      (ensures
        ChunkedMarkBounded.chunked_count_non_black_in mh' objs <
        ChunkedMarkBounded.chunked_count_non_black_in mh objs)
  =
  ChunkedMarkBoundedCount.chunked_count_non_black_in_black_status_flip_decreases
    mh mh' objs target

let spot_chunked_is_gray_not_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedMarkBounded.chunked_is_gray mh obj)
      (ensures ~(ChunkedSweepDefs.chunked_is_black mh obj))
  =
  ChunkedMarkBoundedCount.chunked_is_gray_not_black mh obj

let spot_chunked_push_children_bounded_preserves_stack_member
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires Seq.mem target st)
      (ensures
        (let (_, st') =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         Seq.mem target st'))
  =
  ChunkedMarkBoundedReady.chunked_push_children_bounded_preserves_stack_member
    mh st obj i ws cap target

let spot_chunked_mark_step_bounded_preserves_tail_member
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        Seq.mem target (Seq.tail st))
      (ensures
        (let (_, st') =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         Seq.mem target st'))
  =
  ChunkedMarkBoundedReady.chunked_mark_step_bounded_preserves_tail_member
    mh st cap target

let spot_chunked_rescan_heap_adds_gray_with_capacity
  (mh: MH.major_heap)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.mem target (MH.major_objects mh) /\
        ChunkedMarkBounded.chunked_is_gray mh target /\
        Seq.length (MH.major_objects mh) <= cap)
      (ensures
        Seq.mem target
          (ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap))
  =
  ChunkedMarkBoundedReady.chunked_rescan_heap_adds_gray_with_capacity
    mh cap target

let spot_chunked_stack_points_to_gray_elim
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        ChunkedMarkBoundedReady.chunked_stack_points_to_gray mh st /\
        Seq.mem target st)
      (ensures ChunkedMarkBounded.chunked_is_gray mh target)
  =
  ChunkedMarkBoundedReady.chunked_stack_points_to_gray_elim
    mh st target

let spot_chunked_stack_points_to_gray_intro
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (target: obj_addr).
          Seq.mem target st ==>
          ChunkedMarkBounded.chunked_is_gray mh target))
      (ensures ChunkedMarkBoundedReady.chunked_stack_points_to_gray mh st)
  =
  ChunkedMarkBoundedReady.chunked_stack_points_to_gray_intro mh st

let spot_chunked_bounded_stack_props_intro
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        ChunkedMarkPres.stack_objects_in_major mh st /\
        ChunkedMarkBoundedReady.chunked_stack_points_to_gray mh st /\
        Mark.stack_no_dups st)
      (ensures ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st)
  =
  ChunkedMarkBoundedReady.chunked_bounded_stack_props_intro mh st

let spot_chunked_bounded_stack_props_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st)
      (ensures ChunkedMarkPres.stack_objects_in_major mh st)
  =
  ChunkedMarkBoundedReady.chunked_bounded_stack_props_objects mh st

let spot_chunked_bounded_stack_props_gray
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st)
      (ensures ChunkedMarkBoundedReady.chunked_stack_points_to_gray mh st)
  =
  ChunkedMarkBoundedReady.chunked_bounded_stack_props_gray mh st

let spot_chunked_bounded_stack_props_no_dups
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st)
      (ensures Mark.stack_no_dups st)
  =
  ChunkedMarkBoundedReady.chunked_bounded_stack_props_no_dups mh st

let spot_chunked_rescan_heap_stack_gray
  (mh: MH.major_heap)
  (cap: nat)
  : Lemma
      (ensures
        ChunkedMarkBoundedReady.chunked_stack_points_to_gray mh
          (ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap))
  =
  ChunkedMarkBoundedReady.chunked_rescan_heap_stack_gray mh cap

let spot_chunked_rescan_objects_preserves_stack_no_dups
  (mh: MH.major_heap)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires Mark.stack_no_dups st)
      (ensures
        Mark.stack_no_dups
          (ChunkedMarkBounded.chunked_rescan_objects mh objs st cap))
  =
  ChunkedMarkBoundedReady.chunked_rescan_objects_preserves_stack_no_dups
    mh objs st cap

let spot_chunked_rescan_heap_stack_no_dups
  (mh: MH.major_heap)
  (cap: nat)
  : Lemma
      (ensures
        Mark.stack_no_dups
          (ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap))
  =
  ChunkedMarkBoundedReady.chunked_rescan_heap_stack_no_dups mh cap

let spot_chunked_rescan_heap_stack_objects_in_major
  (mh: MH.major_heap)
  (cap: nat)
  : Lemma
      (ensures
        ChunkedMarkPres.stack_objects_in_major mh
          (ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap))
  =
  ChunkedMarkBoundedReady.chunked_rescan_heap_stack_objects_in_major
    mh cap

let spot_chunked_rescan_heap_bounded_stack_props
  (mh: MH.major_heap)
  (cap: nat)
  : Lemma
      (ensures
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh
          (ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap))
  =
  ChunkedMarkBoundedReady.chunked_rescan_heap_bounded_stack_props
    mh cap

let spot_chunked_bounded_stack_head
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st)
      (ensures
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ChunkedMarkBounded.chunked_is_gray mh (Seq.head st))
  =
  ChunkedMarkBoundedReady.chunked_bounded_stack_head mh st

let spot_chunked_bounded_is_gray_single_chunk_compat
  (g: heap)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  : Lemma
      (ChunkedMarkBounded.chunked_is_gray
        (MH.single_chunk_major_heap g) obj ==
       Obj.is_gray obj g)
  =
  ChunkedMarkBoundedCompat.chunked_is_gray_single_chunk_compat g obj

let spot_chunked_push_children_bounded_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr{U64.v obj >= U64.v zero_addr + U64.v mword})
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedCompat.push_children_bounded_single_chunk_ready
          g st obj i ws cap)
      (ensures
        ChunkedMarkBounded.chunked_push_children_bounded
          (MH.single_chunk_major_heap g) st obj i ws cap ==
        (let (g', st') =
          BMark.push_children_bounded g st obj i ws cap in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkBoundedCompat.chunked_push_children_bounded_single_chunk_compat
    g st obj i ws cap

let spot_chunked_mark_step_bounded_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        (if Seq.length st = 0 then True
         else
           let obj = Seq.head st in
           U64.v obj >= U64.v zero_addr + U64.v mword /\
           (if Obj.is_no_scan obj g then
              True
            else
              ChunkedMarkBoundedCompat.push_children_bounded_single_chunk_ready
                (Obj.makeBlack obj g)
                (Seq.tail st)
                obj
                1UL
                (Obj.wosize_of_object obj g)
                cap)))
      (ensures
        ChunkedMarkBounded.chunked_mark_step_bounded
          (MH.single_chunk_major_heap g) st cap ==
        (let (g', st') = BMark.mark_step_bounded g st cap in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkBoundedCompat.chunked_mark_step_bounded_single_chunk_compat
    g st cap

let spot_chunked_count_non_black_in_single_chunk_compat
  (g: heap)
  (objs: Seq.seq obj_addr)
  : Lemma
      (requires ChunkedMarkBoundedLoop.object_list_ready objs)
      (ensures
        ChunkedMarkBounded.chunked_count_non_black_in
          (MH.single_chunk_major_heap g) objs ==
        BMark.count_non_black_in g objs)
  =
  ChunkedMarkBoundedLoop.chunked_count_non_black_in_single_chunk_compat
    g objs

let spot_chunked_count_non_black_single_chunk_compat
  (g: heap)
  : Lemma
      (requires
        ChunkedMarkBoundedLoop.object_list_ready
          (Fields.objects zero_addr g))
      (ensures
        ChunkedMarkBounded.chunked_count_non_black
          (MH.single_chunk_major_heap g) ==
        BMark.count_non_black g)
  =
  ChunkedMarkBoundedLoop.chunked_count_non_black_single_chunk_compat g

let spot_chunked_rescan_objects_single_chunk_compat
  (g: heap)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires ChunkedMarkBoundedLoop.object_list_ready objs)
      (ensures
        ChunkedMarkBounded.chunked_rescan_objects
          (MH.single_chunk_major_heap g) objs st cap ==
        BMark.rescan_heap g objs st cap)
  =
  ChunkedMarkBoundedLoop.chunked_rescan_objects_single_chunk_compat
    g objs st cap

let spot_chunked_rescan_heap_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedLoop.object_list_ready
          (Fields.objects zero_addr g))
      (ensures
        ChunkedMarkBounded.chunked_rescan_heap
          (MH.single_chunk_major_heap g) st cap ==
        BMark.rescan_heap g (Fields.objects zero_addr g) st cap)
  =
  ChunkedMarkBoundedLoop.chunked_rescan_heap_single_chunk_compat
    g st cap

let spot_chunked_mark_inner_loop_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedLoop.mark_inner_loop_single_chunk_ready
          g st cap fuel)
      (ensures
        ChunkedMarkBounded.chunked_mark_inner_loop
          (MH.single_chunk_major_heap g) st cap fuel ==
        (let (g', st') = BMark.mark_inner_loop g st cap fuel in
         (MH.single_chunk_major_heap g', st')))
  =
  ChunkedMarkBoundedLoop.chunked_mark_inner_loop_single_chunk_compat
    g st cap fuel

let spot_chunked_mark_bounded_single_chunk_compat
  (g: heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel)
      (ensures
        ChunkedMarkBounded.chunked_mark_bounded
          (MH.single_chunk_major_heap g) cap fuel ==
        MH.single_chunk_major_heap (BMark.mark_bounded g cap fuel))
  =
  ChunkedMarkBoundedOuter.chunked_mark_bounded_single_chunk_compat
    g cap fuel

let spot_chunked_major_gc_bounded_equation
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel ==
       ChunkedSweepDefs.chunked_fused_sweep_coalesce
         (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMajorGC.chunked_major_gc_bounded_equation mh cap fuel

let spot_chunked_major_gc_bounded_single_chunk_compat
  (g: heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel)
      (ensures
        ChunkedMajorGC.chunked_major_gc_bounded
          (MH.single_chunk_major_heap g) cap fuel ==
        (let h_mark = BMark.mark_bounded g cap fuel in
         let (h_final, fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         (MH.single_chunk_major_heap h_final, fp_final)))
  =
  ChunkedMajorGC.chunked_major_gc_bounded_single_chunk_compat g cap fuel

let spot_chunked_gc_postcondition_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGCCorr.chunked_no_gray_or_black_objects mh)
      (ensures ChunkedMajorGCCorr.chunked_gc_postcondition mh)
  =
  ChunkedMajorGCCorr.chunked_gc_postcondition_intro mh

let spot_chunked_gc_postcondition_single_chunk_from_dense
  (g: heap)
  : Lemma
      (requires SpecGCPost.gc_postcondition g)
      (ensures
        ChunkedMajorGCCorr.chunked_gc_postcondition
          (MH.single_chunk_major_heap g))
  =
  ChunkedMajorGCCorr.chunked_gc_postcondition_single_chunk_from_dense g

let spot_chunked_major_gc_bounded_single_chunk_postcondition
  (g: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        Fields.well_formed_heap g /\
        Seq.length (Fields.objects zero_addr g) > 0 /\
        GC.Spec.SweepInv.heap_objects_dense g /\
        Mark.root_props g roots /\
        SpecSweep.fp_in_heap fp g /\
        Mark.no_black_objects g /\
        Mark.no_pointer_to_blue g /\
        Fields.no_scan_invariant g /\
        fuel >= BMark.count_non_black g /\
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel /\
        (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr g) /\
          (Obj.is_gray x g \/ Obj.is_black x g) ==> Seq.mem x roots) /\
        (let graph = GC.Spec.HeapModel.create_graph g in
         let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
         GC.Spec.Graph.graph_wf graph /\
         GC.Spec.Graph.is_vertex_set roots' /\
         GC.Spec.Graph.subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap g) cap fuel in
         ChunkedMajorGCCorr.chunked_gc_postcondition mh_final))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_single_chunk_postcondition
    g roots fp cap fuel

let spot_chunked_major_gc_bounded_single_chunk_full_correctness
  (g: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        Fields.well_formed_heap g /\
        Seq.length (Fields.objects zero_addr g) > 0 /\
        GC.Spec.SweepInv.heap_objects_dense g /\
        Mark.root_props g roots /\
        SpecSweep.fp_in_heap fp g /\
        Mark.no_black_objects g /\
        Mark.no_pointer_to_blue g /\
        Fields.no_scan_invariant g /\
        fuel >= BMark.count_non_black g /\
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel /\
        (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr g) /\
          (Obj.is_gray x g \/ Obj.is_black x g) ==> Seq.mem x roots) /\
        (let graph = GC.Spec.HeapModel.create_graph g in
         let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
         GC.Spec.Graph.graph_wf graph /\
         GC.Spec.Graph.is_vertex_set roots' /\
         GC.Spec.Graph.subset_vertices roots' graph.vertices))
      (ensures
        (let h_mark = BMark.mark_bounded g cap fuel in
         let (h_final, dense_fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap g) cap fuel in
         mh_final == MH.single_chunk_major_heap h_final /\
         SpecGCPost.full_gc_correctness g h_final roots /\
         ChunkedMajorGCCorr.chunked_gc_postcondition mh_final))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_single_chunk_full_correctness
    g roots fp cap fuel

let spot_chunked_major_gc_bounded_single_chunk_dense_graph_pillars
  (g: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        Fields.well_formed_heap g /\
        Seq.length (Fields.objects zero_addr g) > 0 /\
        GC.Spec.SweepInv.heap_objects_dense g /\
        Mark.root_props g roots /\
        SpecSweep.fp_in_heap fp g /\
        Mark.no_black_objects g /\
        Mark.no_pointer_to_blue g /\
        Fields.no_scan_invariant g /\
        fuel >= BMark.count_non_black g /\
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel /\
        (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr g) /\
          (Obj.is_gray x g \/ Obj.is_black x g) ==> Seq.mem x roots) /\
        (let graph = GC.Spec.HeapModel.create_graph g in
         let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
         GC.Spec.Graph.graph_wf graph /\
         GC.Spec.Graph.is_vertex_set roots' /\
         GC.Spec.Graph.subset_vertices roots' graph.vertices))
      (ensures
        (let h_mark = BMark.mark_bounded g cap fuel in
         let (h_final, dense_fp_final) =
           DenseFused.fused_sweep_coalesce h_mark in
         let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap g) cap fuel in
         mh_final == MH.single_chunk_major_heap h_final /\
         SpecGCPost.major_gc_live_subgraph_isomorphism
           g h_final roots /\
         SpecGCPost.major_gc_unreachable_final_blue
           g h_final roots))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_single_chunk_dense_graph_pillars
    g roots fp cap fuel

let spot_chunked_major_gc_bounded_single_chunk_live_field_data_preserved
  (g: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        Fields.well_formed_heap g /\
        Seq.length (Fields.objects zero_addr g) > 0 /\
        GC.Spec.SweepInv.heap_objects_dense g /\
        Mark.root_props g roots /\
        SpecSweep.fp_in_heap fp g /\
        Mark.no_black_objects g /\
        Mark.no_pointer_to_blue g /\
        Fields.no_scan_invariant g /\
        fuel >= BMark.count_non_black g /\
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel /\
        (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr g) /\
          (Obj.is_gray x g \/ Obj.is_black x g) ==> Seq.mem x roots) /\
        (let graph = GC.Spec.HeapModel.create_graph g in
         let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
         GC.Spec.Graph.graph_wf graph /\
         GC.Spec.Graph.is_vertex_set roots' /\
         GC.Spec.Graph.subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap g) cap fuel in
         forall (x: obj_addr).
           SpecGCPost.heap_reachable g roots x ==>
           ChunkedMajorGCGraph.chunked_major_field_data_preserved
             (MH.single_chunk_major_heap g)
             mh_final
             x))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_single_chunk_live_field_data_preserved
    g roots fp cap fuel

let spot_chunked_major_gc_bounded_single_chunk_live_field_preserved
  (g: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        Fields.well_formed_heap g /\
        Seq.length (Fields.objects zero_addr g) > 0 /\
        GC.Spec.SweepInv.heap_objects_dense g /\
        Mark.root_props g roots /\
        SpecSweep.fp_in_heap fp g /\
        Mark.no_black_objects g /\
        Mark.no_pointer_to_blue g /\
        Fields.no_scan_invariant g /\
        fuel >= BMark.count_non_black g /\
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel /\
        (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr g) /\
          (Obj.is_gray x g \/ Obj.is_black x g) ==> Seq.mem x roots) /\
        (let graph = GC.Spec.HeapModel.create_graph g in
         let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
         GC.Spec.Graph.graph_wf graph /\
         GC.Spec.Graph.is_vertex_set roots' /\
         GC.Spec.Graph.subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap g) cap fuel in
         forall (x: obj_addr).
           SpecGCPost.heap_reachable g roots x ==>
           ChunkedMajorGCGraph.chunked_major_field_preserved
             (MH.single_chunk_major_heap g)
             mh_final
             x))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_single_chunk_live_field_preserved
    g roots fp cap fuel

let spot_chunked_major_gc_bounded_single_chunk_live_successors_preserved
  (g: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        Fields.well_formed_heap g /\
        Seq.length (Fields.objects zero_addr g) > 0 /\
        GC.Spec.SweepInv.heap_objects_dense g /\
        Mark.root_props g roots /\
        SpecSweep.fp_in_heap fp g /\
        Mark.no_black_objects g /\
        Mark.no_pointer_to_blue g /\
        Fields.no_scan_invariant g /\
        fuel >= BMark.count_non_black g /\
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel /\
        (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr g) /\
          (Obj.is_gray x g \/ Obj.is_black x g) ==> Seq.mem x roots) /\
        (let graph = GC.Spec.HeapModel.create_graph g in
         let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
         GC.Spec.Graph.graph_wf graph /\
         GC.Spec.Graph.is_vertex_set roots' /\
         GC.Spec.Graph.subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap g) cap fuel in
         forall (x: obj_addr).
           SpecGCPost.heap_reachable g roots x ==>
           ChunkedMajorGCGraph.chunked_major_successors_preserved
             (MH.single_chunk_major_heap g)
             mh_final
             x))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_single_chunk_live_successors_preserved
    g roots fp cap fuel

let spot_chunked_major_gc_bounded_single_chunk_live_edges_preserved
  (g: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        Fields.well_formed_heap g /\
        Seq.length (Fields.objects zero_addr g) > 0 /\
        GC.Spec.SweepInv.heap_objects_dense g /\
        Mark.root_props g roots /\
        SpecSweep.fp_in_heap fp g /\
        Mark.no_black_objects g /\
        Mark.no_pointer_to_blue g /\
        Fields.no_scan_invariant g /\
        fuel >= BMark.count_non_black g /\
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel /\
        (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr g) /\
          (Obj.is_gray x g \/ Obj.is_black x g) ==> Seq.mem x roots) /\
        (let graph = GC.Spec.HeapModel.create_graph g in
         let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
         GC.Spec.Graph.graph_wf graph /\
         GC.Spec.Graph.is_vertex_set roots' /\
         GC.Spec.Graph.subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap g) cap fuel in
         forall (x: obj_addr).
           SpecGCPost.heap_reachable g roots x ==>
           forall (y: obj_addr).
             ChunkedMajorGCGraph.chunked_major_edge
               (MH.single_chunk_major_heap g) x y <==>
             ChunkedMajorGCGraph.chunked_major_edge mh_final x y))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_single_chunk_live_edges_preserved
    g roots fp cap fuel

let spot_chunked_major_gc_bounded_single_chunk_live_subgraph_preserved
  (g: heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        Fields.well_formed_heap g /\
        Seq.length (Fields.objects zero_addr g) > 0 /\
        GC.Spec.SweepInv.heap_objects_dense g /\
        Mark.root_props g roots /\
        SpecSweep.fp_in_heap fp g /\
        Mark.no_black_objects g /\
        Mark.no_pointer_to_blue g /\
        Fields.no_scan_invariant g /\
        fuel >= BMark.count_non_black g /\
        ChunkedMarkBoundedOuter.mark_bounded_single_chunk_ready
          g cap fuel /\
        (forall (x: obj_addr). Seq.mem x (Fields.objects zero_addr g) /\
          (Obj.is_gray x g \/ Obj.is_black x g) ==> Seq.mem x roots) /\
        (let graph = GC.Spec.HeapModel.create_graph g in
         let roots' = GC.Spec.HeapGraph.coerce_to_vertex_list roots in
         GC.Spec.Graph.graph_wf graph /\
         GC.Spec.Graph.is_vertex_set roots' /\
         GC.Spec.Graph.subset_vertices roots' graph.vertices))
      (ensures
        (let (mh_final, chunked_fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded
             (MH.single_chunk_major_heap g) cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           (MH.single_chunk_major_heap g)
           mh_final
           (fun (x: obj_addr) -> SpecGCPost.heap_reachable g roots x)))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_single_chunk_live_subgraph_preserved
    g roots fp cap fuel

let spot_chunked_major_gc_bounded_mark_phase_preserves_shape
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel)
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         MH.major_objects marked == MH.major_objects mh))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_mark_phase_preserves_shape
    mh cap fuel

let spot_chunked_major_gc_bounded_mark_phase_preserves_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        Seq.mem obj
          (MH.major_objects
            (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel)))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_mark_phase_preserves_membership
    mh cap fuel obj

let spot_chunked_major_gc_bounded_mark_phase_marks_target_black
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel target)
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_mark_phase_marks_target_black
    mh cap fuel target

let spot_chunked_major_gc_bounded_mark_phase_pointer_classification_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (ensures
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          mh (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_mark_phase_pointer_classification_preserved
    mh cap fuel

let spot_chunked_major_gc_bounded_mark_phase_field_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedMajorGCGraph.chunked_major_field_preserved
          mh (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_mark_phase_field_preserved
    mh cap fuel target

let spot_chunked_major_gc_bounded_mark_phase_live_subgraph_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        (forall (target: obj_addr).
          live target ==> Seq.mem target (MH.major_objects mh)))
      (ensures
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) live)
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_mark_phase_live_subgraph_preserved
    mh cap fuel live

let spot_chunked_major_gc_bounded_mark_phase_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMajorGCMarkReach.chunked_mark_bounded_reachability_ready
          mh cap fuel /\
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
      (ensures
        ChunkedMajorGCReach.chunked_gray_black_reachable
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) roots)
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_mark_phase_preserves_gray_black_reachable
    mh roots cap fuel

let spot_chunked_major_gc_bounded_marked_live_subgraph_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_idx: obj_addr -> nat)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (j: nat). j < Seq.length marked ==>
           forall (o: obj_addr).
           Seq.mem o (MH.objects_in_chunk (Seq.index marked j)) ==>
           U64.v (ChunkedSweepDefs.chunked_wosize_of_object marked o) ==
           MH.object_wosize_in_chunk (Seq.index marked j) o) /\
         (forall (target: obj_addr).
           live target ==>
           live_idx target < Seq.length marked /\
           Seq.mem target
             (MH.objects_in_chunk (Seq.index marked (live_idx target))) /\
           ChunkedSweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           ChunkedSweepDefs.chunked_is_black marked target /\
           U64.v (Obj.getWosize (live_hdr target)) ==
             MH.object_wosize_in_chunk
               (Seq.index marked (live_idx target)) target)))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_marked_live_subgraph_preserved
    mh cap fuel live live_idx live_hdr

let spot_chunked_major_gc_bounded_marked_black_live_subgraph_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (j: nat). j < Seq.length marked ==>
           forall (o: obj_addr).
           Seq.mem o (MH.objects_in_chunk (Seq.index marked j)) ==>
           U64.v (ChunkedSweepDefs.chunked_wosize_of_object marked o) ==
           MH.object_wosize_in_chunk (Seq.index marked j) o) /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           ChunkedSweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           ChunkedSweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_marked_black_live_subgraph_preserved
    mh cap fuel live live_hdr

let spot_chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           ChunkedSweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           ChunkedSweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership
    mh cap fuel live live_hdr

let spot_chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap marked /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects marked) /\
           ChunkedSweepDefs.chunked_is_black marked target)))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_marked_black_live_subgraph_preserved_from_membership_no_header
    mh cap fuel live

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         MH.well_formed_major_heap mh /\
         ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
           mh cap fuel /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           ChunkedSweepDefs.chunked_read_header marked target ==
             Some (live_hdr target) /\
           ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
             mh cap fuel target)))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready
    mh cap fuel live live_hdr

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
            mh cap fuel target))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_target_ready_no_header
    mh cap fuel live

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_gray_rescan
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         fuel > 0 /\
         MH.well_formed_major_heap mh /\
         ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
           mh cap fuel /\
         Seq.length (MH.major_objects mh) <= cap /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           ChunkedMarkBounded.chunked_is_gray mh target /\
           ChunkedSweepDefs.chunked_read_header marked target ==
             Some (live_hdr target))))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_gray_rescan
    mh cap fuel live live_hdr

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_gray_rescan_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          ChunkedMarkBounded.chunked_is_gray mh target))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_gray_rescan_no_header
    mh cap fuel live

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  (live_hdr: obj_addr -> U64.t)
  : Lemma
      (requires
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         fuel > 0 /\
         MH.well_formed_major_heap mh /\
         ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
           mh cap fuel /\
         Seq.length (MH.major_objects mh) <= cap /\
         (forall (target: obj_addr).
           live target ==>
           Seq.mem target (MH.major_objects mh) /\
           (ChunkedMarkBounded.chunked_is_gray mh target \/
            ChunkedSweepDefs.chunked_is_black mh target) /\
           ChunkedSweepDefs.chunked_read_header marked target ==
             Some (live_hdr target))))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan
    mh cap fuel live live_hdr

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          (ChunkedMarkBounded.chunked_is_gray mh target \/
           ChunkedSweepDefs.chunked_is_black mh target)))
      (ensures
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         let (mh_final, fp_final) =
           ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           marked mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_gray_or_black_rescan_no_header
    mh cap fuel live

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_initial_gray_or_black_rescan_no_header
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          (ChunkedMarkBounded.chunked_is_gray mh target \/
           ChunkedSweepDefs.chunked_is_black mh target)))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           mh mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_initial_gray_or_black_rescan_no_header
    mh cap fuel live

let spot_chunked_major_gc_selected_live_intro
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          (ChunkedMarkBounded.chunked_is_gray mh target \/
           ChunkedSweepDefs.chunked_is_black mh target)))
      (ensures
        ChunkedMajorGCCorr.chunked_major_gc_selected_live mh cap fuel live)
  =
  ChunkedMajorGCCorr.chunked_major_gc_selected_live_intro mh cap fuel live

let spot_chunked_major_gc_selected_live_elim
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        ChunkedMajorGCCorr.chunked_major_gc_selected_live mh cap fuel live)
      (ensures
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        (forall (target: obj_addr).
          live target ==>
          Seq.mem target (MH.major_objects mh) /\
          (ChunkedMarkBounded.chunked_is_gray mh target \/
           ChunkedSweepDefs.chunked_is_black mh target)))
  =
  ChunkedMajorGCCorr.chunked_major_gc_selected_live_elim mh cap fuel live

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_selected_live
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        ChunkedMajorGCCorr.chunked_major_gc_selected_live mh cap fuel live)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_selected_live
    mh cap fuel live

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_marked_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets
          mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh /\
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         forall (target: obj_addr).
           live target ==>
           ChunkedMajorGCReach.chunked_major_reachable_from_roots
             marked roots target))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_marked_reachable
    mh roots cap fuel live

let spot_chunked_major_marked_reachable_live_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel)
          roots target)
      (ensures
        ChunkedMajorGCCorr.chunked_major_marked_reachable_live
          mh roots cap fuel target)
  =
  ChunkedMajorGCCorr.chunked_major_marked_reachable_live_intro
    mh roots cap fuel target

let spot_chunked_major_marked_reachable_live_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCCorr.chunked_major_marked_reachable_live
          mh roots cap fuel target)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel)
          roots target)
  =
  ChunkedMajorGCCorr.chunked_major_marked_reachable_live_elim
    mh roots cap fuel target

let spot_chunked_major_initial_reachable_live_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots target)
      (ensures
        ChunkedMajorGCCorr.chunked_major_initial_reachable_live
          mh roots target)
  =
  ChunkedMajorGCCorr.chunked_major_initial_reachable_live_intro
    mh roots target

let spot_chunked_major_initial_reachable_live_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCCorr.chunked_major_initial_reachable_live
          mh roots target)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots target)
  =
  ChunkedMajorGCCorr.chunked_major_initial_reachable_live_elim
    mh roots target

let spot_chunked_major_gc_bounded_marked_reachable_live_subgraph_preserved
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets
          mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_marked_reachable_live
            mh roots cap fuel)))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_marked_reachable_live_subgraph_preserved
    mh roots cap fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets
          mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved
    mh roots cap fuel

let spot_chunked_major_gc_bounded_live_subgraph_preserved_from_marked_reachable_vertex_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets
          mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh /\
        (let marked = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         forall (target: obj_addr).
          live target ==>
          ChunkedMajorGCReach.chunked_major_reachable_from_roots
            marked roots target))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final live))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_live_subgraph_preserved_from_marked_reachable_vertex_targets
    mh roots cap fuel live

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_vertex_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets
          mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  ChunkedMajorGCCorr.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_vertex_targets
    mh roots cap fuel

let spot_chunked_sweep_black_implies_gen_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedSweepDefs.chunked_is_black mh obj)
      (ensures GenInv.chunked_is_black mh obj)
  =
  GenMajorGCBridge.chunked_sweep_black_implies_gen_black mh obj

let spot_chunked_no_black_objects_implies_no_black_to_white_vertex_targets
  (mh: MH.major_heap)
  : Lemma
      (requires GenInv.chunked_no_black_objects mh)
      (ensures
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets
          mh)
  =
  GenMajorGCBridge.chunked_no_black_objects_implies_no_black_to_white_vertex_targets
    mh

let spot_chunked_collection_heap_shape_implies_no_black_to_white_vertex_targets
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel)
      (ensures
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets
          mh)
  =
  GenMajorGCBridge.chunked_collection_heap_shape_implies_no_black_to_white_vertex_targets
    minor mh fp fuel

let spot_chunked_major_edge_gen_field_witness_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGCGraph.chunked_major_vertex mh dst ==>
          exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
            Seq.mem src (MH.major_objects mh) /\
            idx < CG.chunked_wosize_nat_of_object mh src /\
            CG.chunked_major_field_slot src idx == Some field_addr /\
            MH.read_word_in_major mh field_addr == Some raw /\
            Seq.mem dst (MH.major_objects mh) /\
            Fields.is_pointer_to raw dst)
      (ensures
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh)
  =
  GenMajorGCBridge.chunked_major_edge_gen_field_witness_intro mh

let spot_chunked_major_edge_gen_field_witness_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh /\
        ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGCGraph.chunked_major_vertex mh dst)
      (ensures
        exists (idx: nat) (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          Fields.is_pointer_to raw dst)
  =
  GenMajorGCBridge.chunked_major_edge_gen_field_witness_elim
    mh src dst

let spot_chunked_major_edge_gen_field_witness_from_pointer_fields
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        (forall (obj: obj_addr).
          Seq.mem obj (MH.major_objects mh) ==>
          Fields.is_pointer_field obj))
      (ensures
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh)
  =
  GenMajorGCBridge.chunked_major_edge_gen_field_witness_from_pointer_fields
    mh

let spot_chunked_major_edge_gen_field_witness_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh)
      (ensures
        GenMajorGCBridge.chunked_major_edge_gen_field_witness
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  GenMajorGCBridge.chunked_major_edge_gen_field_witness_preserved_by_gray_roots
    mh roots

let spot_chunked_major_field_targets_non_infix_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr) (idx: nat)
               (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          Seq.mem dst (MH.major_objects mh) /\
          Fields.is_pointer_to raw dst ==>
          ~(ChunkedSweepDefs.chunked_is_infix mh dst))
      (ensures
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh)
  =
  GenMajorGCBridge.chunked_major_field_targets_non_infix_intro mh

let spot_chunked_major_field_targets_non_infix_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  (idx: nat)
  (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        Seq.mem dst (MH.major_objects mh) /\
        Fields.is_pointer_to raw dst)
      (ensures ~(ChunkedSweepDefs.chunked_is_infix mh dst))
  =
  GenMajorGCBridge.chunked_major_field_targets_non_infix_elim
    mh src dst idx field_addr raw

let spot_chunked_major_field_targets_non_infix_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh)
      (ensures
        GenMajorGCBridge.chunked_major_field_targets_non_infix
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  GenMajorGCBridge.chunked_major_field_targets_non_infix_preserved_by_gray_roots
    mh roots

let spot_chunked_major_field_targets_non_infix_implies_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh)
      (ensures
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
  =
  GenMajorGCBridge.chunked_major_field_targets_non_infix_implies_vertex_edge_targets_non_infix
    mh

let spot_chunked_major_gc_bounded_liveness_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots)
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy_intro
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_liveness_policy_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)
      (ensures
        mark_fuel > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy_elim
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_liveness_policy_after_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy_after_gray_roots
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy_intro
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_policy_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy_elim
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_target_membership_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkBoundedReadiness.chunked_mark_bounded_target_membership_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_target_membership_policy_intro
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_policy_from_target_membership
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy_from_target_membership
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_raw_target_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkBoundedTargetMembership.chunked_mark_bounded_raw_targets_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_raw_target_policy_intro
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_intro
    mh roots cap mark_fuel

let spot_chunked_major_raw_field_targets_in_major_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src: obj_addr) (idx: nat) (field_addr: hp_addr) (raw: U64.t).
          Seq.mem src (MH.major_objects mh) /\
          idx < CG.chunked_wosize_nat_of_object mh src /\
          CG.chunked_major_field_slot src idx == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some raw /\
          ChunkedMarkDefs.chunked_is_pointer_field mh raw ==>
          Seq.mem (ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh raw)
            (MH.major_objects mh))
      (ensures
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major mh)
  =
  GenMajorGCBridge.chunked_major_raw_field_targets_in_major_intro mh

let spot_chunked_major_raw_field_targets_in_major_elim
  (mh: MH.major_heap)
  (src: obj_addr)
  (idx: nat)
  (field_addr: hp_addr)
  (raw: U64.t)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major mh /\
        Seq.mem src (MH.major_objects mh) /\
        idx < CG.chunked_wosize_nat_of_object mh src /\
        CG.chunked_major_field_slot src idx == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some raw /\
        ChunkedMarkDefs.chunked_is_pointer_field mh raw)
      (ensures
        Seq.mem (ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh raw)
          (MH.major_objects mh))
  =
  GenMajorGCBridge.chunked_major_raw_field_targets_in_major_elim
    mh src idx field_addr raw

let spot_chunked_scanned_raw_targets_in_major_from_major_raw_field_targets
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major mh /\
        (forall (target: obj_addr).
          Seq.mem target (MH.major_objects mh) ==>
          Fields.is_pointer_field target) /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh)
      (ensures
        ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major
          mh)
  =
  GenMajorGCBridge.chunked_scanned_raw_targets_in_major_from_major_raw_field_targets
    mh

let spot_chunked_scanned_raw_targets_in_major_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major mh)
      (ensures
        ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major_preserved_by_gray_roots
    mh roots

let spot_chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_from_pre_gray
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major mh /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_from_pre_gray
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_from_raw_field_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        mark_fuel > 0 /\
        GenMajorGCBridge.chunked_major_raw_field_targets_in_major mh /\
        (forall (target: obj_addr).
          Seq.mem target (MH.major_objects mh) ==>
          Fields.is_pointer_field target) /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy_from_raw_field_targets
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_raw_target_policy_from_static
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_raw_target_policy_from_static
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_raw_targets
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_policy_from_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy_from_raw_targets
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_static_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_target_membership_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_target_membership_policy_from_static_raw_targets
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_after_gray_roots_policy_from_static_raw_targets
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
          mh roots cap mark_fuel)
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy_from_static_raw_targets
    mh roots cap mark_fuel

let spot_chunked_major_gc_bounded_liveness_policy_after_gray_roots_from_policy
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          roots cap mark_fuel)
  =
  GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy_after_gray_roots_from_policy
    mh roots cap mark_fuel

let spot_chunked_no_black_objects_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_no_black_objects mh)
      (ensures
        GenInv.chunked_no_black_objects
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  GenMajorGCBridge.chunked_no_black_objects_preserved_by_gray_roots
    mh roots

let spot_chunked_blue_status_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        GenMajorGCBridge.chunked_major_roots_nonblue mh roots)
      (ensures
        GenInv.chunked_is_blue
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        GenInv.chunked_is_blue mh target)
  =
  GenMajorGCBridge.chunked_blue_status_preserved_by_gray_roots
    mh roots target

let spot_chunked_minor_major_fields_no_blue_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenMajorGCBridge.chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_minor_major_fields_no_blue minor mh)
      (ensures
        GenInv.chunked_minor_major_fields_no_blue minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  GenMajorGCBridge.chunked_minor_major_fields_no_blue_preserved_by_gray_roots
    minor mh roots

let spot_chunked_no_scan_invariant_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenMajorGCBridge.chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_no_scan_invariant mh)
      (ensures
        GenInv.chunked_no_scan_invariant
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  GenMajorGCBridge.chunked_no_scan_invariant_preserved_by_gray_roots
    mh roots

let spot_chunked_no_pointer_to_blue_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenMajorGCBridge.chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_no_pointer_to_blue mh)
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  GenMajorGCBridge.chunked_no_pointer_to_blue_preserved_by_gray_roots
    mh roots

let spot_chunked_major_minor_fields_no_infix_targets_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenMajorGCBridge.chunked_major_roots_nonblue mh roots /\
        GenInv.chunked_major_minor_fields_no_infix_targets minor mh)
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  GenMajorGCBridge.chunked_major_minor_fields_no_infix_targets_preserved_by_gray_roots
    minor mh roots

let spot_chunked_major_alloc_shape_preserved_by_gray_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires GenInv.chunked_major_alloc_shape mh fp fuel)
      (ensures
        GenInv.chunked_major_alloc_shape
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp fuel)
  =
  GenMajorGCBridge.chunked_major_alloc_shape_preserved_by_gray_roots
    mh roots fp fuel

let spot_chunked_collection_heap_shape_preserved_by_gray_roots
  (minor: minor_state)
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp fuel /\
        GenMajorGCBridge.chunked_major_roots_nonblue mh roots)
      (ensures
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp fuel)
  =
  GenMajorGCBridge.chunked_collection_heap_shape_preserved_by_gray_roots
    minor mh roots fp fuel

let spot_chunked_sweep_not_blue_vertex_implies_gen_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGCGraph.chunked_major_vertex mh obj /\
        ~(ChunkedSweepDefs.chunked_is_blue mh obj))
      (ensures ~(GenInv.chunked_is_blue mh obj))
  =
  GenMajorGCBridge.chunked_sweep_not_blue_vertex_implies_gen_not_blue
    mh obj

let spot_chunked_gen_not_blue_vertex_implies_sweep_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGCGraph.chunked_major_vertex mh obj /\
        ~(GenInv.chunked_is_blue mh obj))
      (ensures ~(ChunkedSweepDefs.chunked_is_blue mh obj))
  =
  GenMajorGCBridge.chunked_gen_not_blue_vertex_implies_sweep_not_blue
    mh obj

let spot_chunked_no_pointer_to_blue_implies_mark_vertex_targets
  (mh: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_no_pointer_to_blue mh /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh)
      (ensures
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets
          mh)
  =
  GenMajorGCBridge.chunked_no_pointer_to_blue_implies_mark_vertex_targets
    mh

let spot_chunked_collection_heap_shape_implies_mark_vertex_targets_no_pointer_to_blue
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp fuel /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh)
      (ensures
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets
          mh)
  =
  GenMajorGCBridge.chunked_collection_heap_shape_implies_mark_vertex_targets_no_pointer_to_blue
    minor mh fp fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape
    minor mh fp shape_fuel roots cap mark_fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_vertex_targets
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_vertex_targets
    minor mh fp shape_fuel roots cap mark_fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_field_policies
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        mark_fuel > 0 /\
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_field_policies
    minor mh fp shape_fuel roots cap mark_fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh /\
        GenMajorGCBridge.chunked_major_gc_bounded_liveness_policy
          mh roots cap mark_fuel)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded mh cap mark_fuel in
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_from_collection_shape_policy
    minor mh fp shape_fuel roots cap mark_fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_grayed_collection_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp shape_fuel /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_grayed_collection_shape_policy
    minor mh fp shape_fuel roots cap mark_fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_field_policies
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        GenInv.chunked_collection_heap_shape minor
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          fp shape_fuel /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_field_policies
    minor mh fp shape_fuel roots cap mark_fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        GenMajorGCBridge.chunked_major_roots_nonblue mh roots /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
          cap mark_fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        mark_fuel > 0 /\
        mark_fuel >= Seq.length (MH.major_objects mh))
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape
    minor mh fp shape_fuel roots cap mark_fuel

let spot_chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape_policy
  (minor: minor_state)
  (mh: MH.major_heap)
  (fp: U64.t)
  (shape_fuel: nat)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor mh fp shape_fuel /\
        GenMajorGCBridge.chunked_major_roots_nonblue mh roots /\
        GenMajorGCBridge.chunked_major_edge_gen_field_witness mh /\
        GenMajorGCBridge.chunked_major_field_targets_non_infix mh /\
        GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy
          mh roots cap mark_fuel)
      (ensures
        (let (mh_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots mh roots)
            cap mark_fuel in
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh mh_final
          (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
            mh roots)))
  =
  GenMajorGCBridge.chunked_major_gc_bounded_initial_reachable_live_subgraph_preserved_after_gray_roots_from_original_shape_policy
    minor mh fp shape_fuel roots cap mark_fuel

let spot_chunked_major_reachable_refl
  (mh: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires ChunkedMajorGCGraph.chunked_major_vertex mh x)
      (ensures ChunkedMajorGCReach.chunked_major_reachable mh x x)
  =
  ChunkedMajorGCReach.chunked_major_reachable_refl mh x

let spot_chunked_major_edge_reachable
  (mh: MH.major_heap)
  (x y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_vertex mh x /\
        ChunkedMajorGCGraph.chunked_major_vertex mh y /\
        ChunkedMajorGCGraph.chunked_major_edge mh x y)
      (ensures ChunkedMajorGCReach.chunked_major_reachable mh x y)
  =
  ChunkedMajorGCReach.chunked_major_edge_reachable mh x y

let spot_chunked_major_reachable_extend_edge
  (mh: MH.major_heap)
  (x y z: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable mh x y /\
        ChunkedMajorGCGraph.chunked_major_vertex mh z /\
        ChunkedMajorGCGraph.chunked_major_edge mh y z)
      (ensures ChunkedMajorGCReach.chunked_major_reachable mh x z)
  =
  ChunkedMajorGCReach.chunked_major_reachable_extend_edge mh x y z

let spot_chunked_major_root_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_vertex mh x /\
        Seq.mem x roots)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots x)
  =
  ChunkedMajorGCReach.chunked_major_root_reachable mh roots x

let spot_chunked_major_reachable_from_roots_vertex
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots x)
      (ensures ChunkedMajorGCGraph.chunked_major_vertex mh x)
  =
  ChunkedMajorGCReach.chunked_major_reachable_from_roots_vertex
    mh roots x

let spot_chunked_major_reachable_from_roots_extend_edge
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots x /\
        ChunkedMajorGCGraph.chunked_major_vertex mh y /\
        ChunkedMajorGCGraph.chunked_major_edge mh x y)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots y)
  =
  ChunkedMajorGCReach.chunked_major_reachable_from_roots_extend_edge
    mh roots x y

let spot_chunked_major_reachable_from_roots_field
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots x /\
        ChunkedMajorGCGraph.chunked_major_vertex mh y /\
        ChunkedMajorGCGraph.chunked_major_field_points_to mh x i y)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots y)
  =
  ChunkedMajorGCReach.chunked_major_reachable_from_roots_field
    mh roots x i y

let spot_chunked_major_reachable_from_roots_induct
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (p: obj_addr -> prop)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots x /\
        (forall (r: obj_addr).
          ChunkedMajorGCGraph.chunked_major_vertex mh r /\
          Seq.mem r roots ==>
          p r) /\
        (forall (y z: obj_addr).
          ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots y /\
          p y /\
          ChunkedMajorGCGraph.chunked_major_vertex mh z /\
          ChunkedMajorGCGraph.chunked_major_edge mh y z ==>
          p z))
      (ensures p x)
  =
  ChunkedMajorGCReach.chunked_major_reachable_from_roots_induct
    mh roots p x

let spot_chunked_gray_roots_empty
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length roots = 0)
      (ensures ChunkedMajorGCRoots.chunked_gray_roots mh roots == mh)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_empty mh roots

let spot_chunked_gray_roots_cons_mem
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length roots > 0 /\
        Seq.mem (Seq.head roots) (MH.major_objects mh))
      (ensures
        ChunkedMajorGCRoots.chunked_gray_roots mh roots ==
        ChunkedMajorGCRoots.chunked_gray_roots
          (ChunkedMarkDefs.chunked_make_gray mh (Seq.head roots))
          (Seq.tail roots))
  =
  ChunkedMajorGCRoots.chunked_gray_roots_cons_mem mh roots

let spot_chunked_gray_roots_cons_miss
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length roots > 0 /\
        ~(Seq.mem (Seq.head roots) (MH.major_objects mh)))
      (ensures
        ChunkedMajorGCRoots.chunked_gray_roots mh roots ==
        ChunkedMajorGCRoots.chunked_gray_roots mh (Seq.tail roots))
  =
  ChunkedMajorGCRoots.chunked_gray_roots_cons_miss mh roots

let spot_chunked_gray_roots_preserves_major_objects
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MH.major_objects (ChunkedMajorGCRoots.chunked_gray_roots mh roots) ==
        MH.major_objects mh)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_major_objects
    mh roots

let spot_chunked_gray_roots_preserves_well_formed
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        MH.well_formed_major_heap
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_well_formed
    mh roots

let spot_chunked_gray_roots_preserves_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        (ChunkedMarkBounded.chunked_is_gray mh target \/
         ChunkedSweepDefs.chunked_is_black mh target))
      (ensures
        ChunkedMarkBounded.chunked_is_gray
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target \/
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_gray_or_black
    mh roots target

let spot_chunked_gray_roots_preserves_blue_status
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        (forall (root: obj_addr).
          Seq.mem root roots /\
          Seq.mem root (MH.major_objects mh) ==>
          ~(ChunkedSweepDefs.chunked_is_blue mh root)))
      (ensures
        ChunkedSweepDefs.chunked_is_blue
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        ChunkedSweepDefs.chunked_is_blue mh target)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_blue_status
    mh roots target

let spot_chunked_gray_roots_preserves_black_status
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        (forall (root: obj_addr).
          Seq.mem root roots /\
          Seq.mem root (MH.major_objects mh) ==>
          ~(ChunkedSweepDefs.chunked_is_black mh root)))
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_black_status
    mh roots target

let spot_chunked_gray_roots_preserves_ranges
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (ensures
        ChunkedSweepRange.same_chunk_ranges
          mh (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_ranges
    mh roots

let spot_chunked_gray_roots_pointer_classification_preserved
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (ensures
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          mh (ChunkedMajorGCRoots.chunked_gray_roots mh roots))
  =
  ChunkedMajorGCRoots.chunked_gray_roots_pointer_classification_preserved
    mh roots

let spot_chunked_gray_roots_preserves_wosize_of_object
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_wosize_of_object
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        ChunkedSweepDefs.chunked_wosize_of_object mh target)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_wosize_of_object
    mh roots target

let spot_chunked_gray_roots_preserves_get_field
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh) /\
        U64.v i <=
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh target))
      (ensures
        ChunkedMarkDefs.chunked_get_field
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target i ==
        ChunkedMarkDefs.chunked_get_field mh target i)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_get_field
    mh roots target i

let spot_chunked_gray_roots_preserves_no_scan_status
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedMarkDefs.chunked_is_no_scan
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        ChunkedMarkDefs.chunked_is_no_scan mh target)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_no_scan_status
    mh roots target

let spot_chunked_gray_roots_preserves_tag_of_object
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_tag_of_object
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        ChunkedSweepDefs.chunked_tag_of_object mh target)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_tag_of_object
    mh roots target

let spot_chunked_gray_roots_preserves_infix_status
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_is_infix
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target ==
        ChunkedSweepDefs.chunked_is_infix mh target)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_preserves_infix_status
    mh roots target

let spot_chunked_gray_roots_field_preserved
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedMajorGCGraph.chunked_major_field_preserved
          mh (ChunkedMajorGCRoots.chunked_gray_roots mh roots) target)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_field_preserved
    mh roots target

let spot_chunked_gray_roots_live_subgraph_preserved
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        (forall (target: obj_addr).
          live target ==> Seq.mem target (MH.major_objects mh)))
      (ensures
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh (ChunkedMajorGCRoots.chunked_gray_roots mh roots) live)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_live_subgraph_preserved
    mh roots live

let spot_chunked_gray_roots_roots_gray_or_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires MH.well_formed_major_heap mh)
      (ensures
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black
          (ChunkedMajorGCRoots.chunked_gray_roots mh roots) roots)
  =
  ChunkedMajorGCRoots.chunked_gray_roots_roots_gray_or_black
    mh roots

let spot_chunked_roots_gray_or_black_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (root: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures
        ChunkedMarkBounded.chunked_is_gray mh root \/
        ChunkedSweepDefs.chunked_is_black mh root)
  =
  ChunkedMajorGCMarkLive.chunked_roots_gray_or_black_elim mh roots root

let spot_chunked_mark_bounded_root_ready
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (root: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures
        ChunkedMarkBoundedPres.chunked_mark_bounded_marks_target_ready
          mh cap fuel root)
  =
  ChunkedMajorGCMarkLive.chunked_mark_bounded_root_ready
    mh roots cap fuel root

let spot_chunked_mark_bounded_roots_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots)
      (ensures
        ChunkedMajorGCMarkLive.chunked_roots_black
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) roots)
  =
  ChunkedMajorGCMarkLive.chunked_mark_bounded_roots_black
    mh roots cap fuel

let spot_chunked_mark_bounded_completes
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        Seq.mem obj
          (MH.major_objects
            (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel)))
      (ensures
        ~(ChunkedMarkBounded.chunked_is_gray
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) obj))
  =
  ChunkedMarkBoundedComplete.chunked_mark_bounded_completes
    mh cap fuel

let spot_chunked_mark_bounded_no_gray_objects
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh)
      (ensures
        ChunkedMajorGCMarkLive.chunked_no_gray_objects
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMajorGCMarkLive.chunked_mark_bounded_no_gray_objects
    mh cap fuel

let spot_chunked_push_children_bounded_no_new_blue
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
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        ~(ChunkedSweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_push_children_bounded
             mh st obj i ws cap in
         ~(ChunkedSweepDefs.chunked_is_blue mh' target)))
  =
  ChunkedMarkBoundedColor.chunked_push_children_bounded_no_new_blue
    mh st obj i ws cap target

let spot_chunked_mark_step_bounded_no_new_blue
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ~(ChunkedSweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ~(ChunkedSweepDefs.chunked_is_blue mh' target)))
  =
  ChunkedMarkBoundedColor.chunked_mark_step_bounded_no_new_blue
    mh st cap target

let spot_chunked_mark_inner_loop_no_new_blue
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ~(ChunkedSweepDefs.chunked_is_blue mh target))
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ~(ChunkedSweepDefs.chunked_is_blue mh' target)))
  =
  ChunkedMarkBoundedColor.chunked_mark_inner_loop_no_new_blue
    mh st cap fuel target

let spot_chunked_mark_bounded_no_new_blue
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ~(ChunkedSweepDefs.chunked_is_blue mh target))
      (ensures
        ~(ChunkedSweepDefs.chunked_is_blue
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target))
  =
  ChunkedMarkBoundedColor.chunked_mark_bounded_no_new_blue
    mh cap fuel target

let spot_chunked_push_children_bounded_no_new_white
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
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        ~(ChunkedSweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_push_children_bounded
             mh st obj i ws cap in
         ~(ChunkedSweepDefs.chunked_is_white mh' target)))
  =
  ChunkedMarkBoundedColor.chunked_push_children_bounded_no_new_white
    mh st obj i ws cap target

let spot_chunked_mark_step_bounded_no_new_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ~(ChunkedSweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ~(ChunkedSweepDefs.chunked_is_white mh' target)))
  =
  ChunkedMarkBoundedColor.chunked_mark_step_bounded_no_new_white
    mh st cap target

let spot_chunked_mark_inner_loop_no_new_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ~(ChunkedSweepDefs.chunked_is_white mh target))
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ~(ChunkedSweepDefs.chunked_is_white mh' target)))
  =
  ChunkedMarkBoundedColor.chunked_mark_inner_loop_no_new_white
    mh st cap fuel target

let spot_chunked_mark_bounded_no_new_white
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ~(ChunkedSweepDefs.chunked_is_white mh target))
      (ensures
        ~(ChunkedSweepDefs.chunked_is_white
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target))
  =
  ChunkedMarkBoundedColor.chunked_mark_bounded_no_new_white
    mh cap fuel target

let spot_chunked_push_children_bounded_preserves_blue
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
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        ChunkedSweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_push_children_bounded
             mh st obj i ws cap in
         ChunkedSweepDefs.chunked_is_blue mh' target))
  =
  ChunkedMarkBoundedColor.chunked_push_children_bounded_preserves_blue
    mh st obj i ws cap target

let spot_chunked_mark_step_bounded_preserves_blue
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ChunkedSweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedSweepDefs.chunked_is_blue mh' target))
  =
  ChunkedMarkBoundedColor.chunked_mark_step_bounded_preserves_blue
    mh st cap target

let spot_chunked_mark_inner_loop_preserves_blue
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ChunkedSweepDefs.chunked_is_blue mh target)
      (ensures
        (let (mh', _) =
           ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedSweepDefs.chunked_is_blue mh' target))
  =
  ChunkedMarkBoundedColor.chunked_mark_inner_loop_preserves_blue
    mh st cap fuel target

let spot_chunked_mark_bounded_preserves_blue
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedSweepDefs.chunked_is_blue mh target)
      (ensures
        ChunkedSweepDefs.chunked_is_blue
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMarkBoundedColor.chunked_mark_bounded_preserves_blue
    mh cap fuel target

let spot_chunked_mark_bounded_field_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMajorGCGraph.chunked_major_vertex mh target)
      (ensures
        ChunkedMajorGCGraph.chunked_major_field_preserved
          mh (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMarkBoundedColor.chunked_mark_bounded_field_preserved
    mh cap fuel target

let spot_chunked_mark_bounded_pointer_classification_preserved
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel)
      (ensures
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          mh (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMarkBoundedColor.chunked_mark_bounded_pointer_classification_preserved
    mh cap fuel

let spot_chunked_push_children_bounded_preserves_infix_status
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
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded mh st obj i ws cap in
         ChunkedSweepDefs.chunked_is_infix mh' target ==
         ChunkedSweepDefs.chunked_is_infix mh target))
  =
  ChunkedMarkBoundedTag.chunked_push_children_bounded_preserves_infix_status
    mh st obj i ws cap target

let spot_chunked_mark_step_bounded_preserves_infix_status
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedSweepDefs.chunked_is_infix mh' target ==
         ChunkedSweepDefs.chunked_is_infix mh target))
  =
  ChunkedMarkBoundedTag.chunked_mark_step_bounded_preserves_infix_status
    mh st cap target

let spot_chunked_mark_bounded_preserves_tag_of_object
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_tag_of_object
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target ==
        ChunkedSweepDefs.chunked_tag_of_object mh target)
  =
  ChunkedMarkBoundedTag.chunked_mark_bounded_preserves_tag_of_object
    mh cap fuel target

let spot_chunked_mark_bounded_preserves_infix_status
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.mem target (MH.major_objects mh))
      (ensures
        ChunkedSweepDefs.chunked_is_infix
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target ==
        ChunkedSweepDefs.chunked_is_infix mh target)
  =
  ChunkedMarkBoundedTag.chunked_mark_bounded_preserves_infix_status
    mh cap fuel target

let spot_chunked_vertex_edge_targets_non_infix_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh /\
        ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGCGraph.chunked_major_vertex mh dst)
      (ensures ~(ChunkedSweepDefs.chunked_is_infix mh dst))
  =
  ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix_elim
    mh src dst

let spot_chunked_mark_step_bounded_preserves_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh'))
  =
  ChunkedMarkBoundedEdge.chunked_mark_step_bounded_preserves_vertex_edge_targets_non_infix
    mh st cap

let spot_chunked_mark_inner_loop_preserves_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh'))
  =
  ChunkedMarkBoundedEdge.chunked_mark_inner_loop_preserves_vertex_edge_targets_non_infix
    mh st cap fuel

let spot_chunked_mark_bounded_preserves_vertex_edge_targets_non_infix
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMarkBoundedEdge.chunked_mark_bounded_preserves_vertex_edge_targets_non_infix
    mh cap fuel

let spot_chunked_no_black_to_white_vertex_targets_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGCGraph.chunked_major_vertex mh dst /\
          ChunkedSweepDefs.chunked_is_black mh src ==>
          ~(ChunkedSweepDefs.chunked_is_white mh dst))
      (ensures
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh)
  =
  ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets_intro mh

let spot_chunked_no_black_to_white_vertex_targets_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGCGraph.chunked_major_vertex mh dst /\
        ChunkedSweepDefs.chunked_is_black mh src)
      (ensures ~(ChunkedSweepDefs.chunked_is_white mh dst))
  =
  ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets_elim
    mh src dst

let spot_chunked_push_children_bounded_field_target_non_white
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
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        U64.v i <= U64.v j /\
        U64.v j <= U64.v ws /\
        ChunkedMajorGCGraph.chunked_major_vertex mh target /\
        ChunkedMajorGCGraph.chunked_major_field_points_to mh obj j target /\
        ~(ChunkedSweepDefs.chunked_is_infix mh target))
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         ~(ChunkedSweepDefs.chunked_is_white mh' target)))
  =
  ChunkedMarkBoundedNoBlack.chunked_push_children_bounded_field_target_non_white
    mh st obj i ws cap j target

let spot_chunked_mark_step_bounded_preserves_no_black_to_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix
          (fst (ChunkedMarkBounded.chunked_mark_step_bounded mh st cap)))
      (ensures
        (let (mh', _) = ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh'))
  =
  ChunkedMarkBoundedNoBlack.chunked_mark_step_bounded_preserves_no_black_to_white
    mh st cap

let spot_chunked_mark_inner_loop_preserves_no_black_to_white
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMarkBoundedReady.chunked_bounded_stack_props mh st /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh'))
  =
  ChunkedMarkBoundedNoBlack.chunked_mark_inner_loop_preserves_no_black_to_white
    mh st cap fuel

let spot_chunked_mark_bounded_preserves_no_black_to_white
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh)
      (ensures
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMarkBoundedNoBlack.chunked_mark_bounded_preserves_no_black_to_white
    mh cap fuel

let spot_chunked_mark_bounded_preserves_no_pointer_to_blue
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh)
      (ensures
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMarkBoundedColor.chunked_mark_bounded_preserves_no_pointer_to_blue
    mh cap fuel

let spot_chunked_roots_black_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (root: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCMarkLive.chunked_roots_black mh roots /\
        ChunkedMajorGCGraph.chunked_major_vertex mh root /\
        Seq.mem root roots)
      (ensures ChunkedSweepDefs.chunked_is_black mh root)
  =
  ChunkedMajorGCMarkLive.chunked_roots_black_elim mh roots root

let spot_chunked_no_gray_objects_elim
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCMarkLive.chunked_no_gray_objects mh /\
        ChunkedMajorGCGraph.chunked_major_vertex mh obj)
      (ensures ~(ChunkedMarkBounded.chunked_is_gray mh obj))
  =
  ChunkedMajorGCMarkLive.chunked_no_gray_objects_elim mh obj

let spot_chunked_no_pointer_to_blue_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
          ~(ChunkedSweepDefs.chunked_is_blue mh src) ==>
          ~(ChunkedSweepDefs.chunked_is_blue mh dst))
      (ensures ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh)
  =
  ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_intro mh

let spot_chunked_no_pointer_to_blue_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
        ~(ChunkedSweepDefs.chunked_is_blue mh src))
      (ensures ~(ChunkedSweepDefs.chunked_is_blue mh dst))
  =
  ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_elim mh src dst

let spot_chunked_no_pointer_to_blue_vertex_targets_intro
  (mh: MH.major_heap)
  : Lemma
      (requires
        forall (src dst: obj_addr).
          ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
          ChunkedMajorGCGraph.chunked_major_vertex mh dst /\
          ~(ChunkedSweepDefs.chunked_is_blue mh src) ==>
          ~(ChunkedSweepDefs.chunked_is_blue mh dst))
      (ensures
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets mh)
  =
  ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets_intro mh

let spot_chunked_no_pointer_to_blue_vertex_targets_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets mh /\
        ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
        ChunkedMajorGCGraph.chunked_major_vertex mh dst /\
        ~(ChunkedSweepDefs.chunked_is_blue mh src))
      (ensures ~(ChunkedSweepDefs.chunked_is_blue mh dst))
  =
  ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets_elim
    mh src dst

let spot_chunked_no_black_to_white_elim
  (mh: MH.major_heap)
  (src dst: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCMarkLive.chunked_no_black_to_white mh /\
        ChunkedMajorGCGraph.chunked_major_edge mh src dst /\
        ChunkedSweepDefs.chunked_is_black mh src)
      (ensures ~(ChunkedSweepDefs.chunked_is_white mh dst))
  =
  ChunkedMajorGCMarkLive.chunked_no_black_to_white_elim mh src dst

let spot_chunked_is_black_not_blue
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires ChunkedSweepDefs.chunked_is_black mh obj)
      (ensures ~(ChunkedSweepDefs.chunked_is_blue mh obj))
  =
  ChunkedMajorGCMarkLive.chunked_is_black_not_blue mh obj

let spot_chunked_not_white_gray_blue_implies_black
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGCGraph.chunked_major_vertex mh obj /\
        ~(ChunkedSweepDefs.chunked_is_white mh obj) /\
        ~(ChunkedMarkBounded.chunked_is_gray mh obj) /\
        ~(ChunkedSweepDefs.chunked_is_blue mh obj))
      (ensures ChunkedSweepDefs.chunked_is_black mh obj)
  =
  ChunkedMajorGCMarkLive.chunked_not_white_gray_blue_implies_black mh obj

let spot_chunked_major_reachable_from_roots_black_from_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGCMarkLive.chunked_roots_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_gray_objects mh /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMajorGCMarkLive.chunked_no_black_to_white mh /\
        ChunkedMajorGCGraph.chunked_major_vertex mh target /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots target)
      (ensures ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMajorGCMarkLive.chunked_major_reachable_from_roots_black_from_invariants
    mh roots target

let spot_chunked_major_reachable_from_roots_black_from_vertex_target_no_pointer_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGCMarkLive.chunked_roots_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_gray_objects mh /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets mh /\
        ChunkedMajorGCMarkLive.chunked_no_black_to_white mh /\
        ChunkedMajorGCGraph.chunked_major_vertex mh target /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots target)
      (ensures ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMajorGCMarkLive.chunked_major_reachable_from_roots_black_from_vertex_target_invariants
    mh roots target

let spot_chunked_major_reachable_from_roots_black_from_vertex_target_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGCMarkLive.chunked_roots_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_gray_objects mh /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMajorGCGraph.chunked_major_vertex mh target /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots target)
      (ensures ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMajorGCMarkLiveNoBlack.chunked_major_reachable_from_roots_black_from_vertex_target_invariants
    mh roots target

let spot_chunked_major_reachable_from_roots_black_from_all_vertex_target_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMajorGCMarkLive.chunked_roots_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_gray_objects mh /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMajorGCGraph.chunked_major_vertex mh target /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots target)
      (ensures ChunkedSweepDefs.chunked_is_black mh target)
  =
  ChunkedMajorGCMarkLiveNoBlack.chunked_major_reachable_from_roots_black_from_all_vertex_target_invariants
    mh roots target

let spot_chunked_mark_bounded_preserves_no_pointer_to_blue_vertex_targets
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets mh)
      (ensures
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel))
  =
  ChunkedMajorGCMarkLiveNoBlack.chunked_mark_bounded_preserves_no_pointer_to_blue_vertex_targets
    mh cap fuel

let spot_chunked_mark_bounded_reachable_black_from_all_vertex_target_invariants
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue_vertex_targets mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh /\
        (let mh_mark = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_vertex mh_mark target /\
         ChunkedMajorGCReach.chunked_major_reachable_from_roots
           mh_mark roots target))
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMajorGCMarkLiveNoBlack.chunked_mark_bounded_reachable_black_from_all_vertex_target_invariants
    mh roots cap fuel target

let spot_chunked_mark_bounded_reachable_black_from_vertex_no_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        Seq.length (MH.major_objects mh) <= cap /\
        fuel >= ChunkedMarkBounded.chunked_count_non_black mh /\
        ChunkedMajorGCMarkLive.chunked_roots_gray_or_black mh roots /\
        ChunkedMajorGCMarkLive.chunked_no_pointer_to_blue mh /\
        ChunkedMarkBoundedNoBlack.chunked_no_black_to_white_vertex_targets mh /\
        ChunkedMarkBoundedEdge.chunked_vertex_edge_targets_non_infix mh /\
        (let mh_mark = ChunkedMarkBounded.chunked_mark_bounded mh cap fuel in
         ChunkedMajorGCGraph.chunked_major_vertex mh_mark target /\
         ChunkedMajorGCReach.chunked_major_reachable_from_roots
           mh_mark roots target))
      (ensures
        ChunkedSweepDefs.chunked_is_black
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) target)
  =
  ChunkedMajorGCMarkLiveNoBlack.chunked_mark_bounded_reachable_black_from_vertex_no_black
    mh roots cap fuel target

let spot_chunked_major_reachable_preserved_by_live_subgraph
  (mh0 mh1: MH.major_heap)
  (live: obj_addr -> prop)
  (x y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh0 mh1 live /\
        (forall (v: obj_addr).
          ChunkedMajorGCGraph.chunked_major_vertex mh0 v ==> live v) /\
        ChunkedMajorGCReach.chunked_major_reachable mh0 x y)
      (ensures ChunkedMajorGCReach.chunked_major_reachable mh1 x y)
  =
  ChunkedMajorGCReach.chunked_major_reachable_preserved_by_live_subgraph
    mh0 mh1 live x y

let spot_chunked_major_reachable_from_roots_preserved_by_live_subgraph
  (mh0 mh1: MH.major_heap)
  (live: obj_addr -> prop)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh0 mh1 live /\
        (forall (v: obj_addr).
          ChunkedMajorGCGraph.chunked_major_vertex mh0 v ==> live v) /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh0 roots x)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh1 roots x)
  =
  ChunkedMajorGCReach.chunked_major_reachable_from_roots_preserved_by_live_subgraph
    mh0 mh1 live roots x

let spot_chunked_gray_black_reachable_init
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (x: obj_addr).
          ChunkedMajorGCGraph.chunked_major_vertex mh x /\
          (ChunkedMarkBounded.chunked_is_gray mh x \/
           ChunkedSweepDefs.chunked_is_black mh x) ==>
          Seq.mem x roots))
      (ensures ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
  =
  ChunkedMajorGCReach.chunked_gray_black_reachable_init mh roots

let spot_chunked_gray_black_reachable_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (x: obj_addr).
          ChunkedMajorGCGraph.chunked_major_vertex mh x /\
          (ChunkedMarkBounded.chunked_is_gray mh x \/
           ChunkedSweepDefs.chunked_is_black mh x) ==>
          ChunkedMajorGCReach.chunked_major_reachable_from_roots
            mh roots x))
      (ensures ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
  =
  ChunkedMajorGCReach.chunked_gray_black_reachable_intro mh roots

let spot_chunked_gray_black_reachable_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots /\
        ChunkedMajorGCGraph.chunked_major_vertex mh x /\
        (ChunkedMarkBounded.chunked_is_gray mh x \/
         ChunkedSweepDefs.chunked_is_black mh x))
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots x)
  =
  ChunkedMajorGCReach.chunked_gray_black_reachable_elim mh roots x

let spot_chunked_stack_reachable_from_roots_intro
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        (forall (obj: obj_addr).
          Seq.mem obj st ==>
          ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots obj))
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
  =
  ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots_intro
    mh roots st

let spot_chunked_stack_reachable_from_roots_elim
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st /\
        Seq.mem obj st)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots obj)
  =
  ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots_elim
    mh roots st obj

let spot_chunked_stack_reachable_from_roots_empty
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  : Lemma
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots Seq.empty)
  =
  ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots_empty
    mh roots

let spot_chunked_stack_reachable_from_roots_cons
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots obj /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots (Seq.cons obj st))
  =
  ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots_cons
    mh roots obj st

let spot_chunked_stack_reachable_from_roots_tail
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots (Seq.tail st))
  =
  ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots_tail
    mh roots st

let spot_chunked_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots /\
        ChunkedMarkPres.stack_objects_in_major mh st /\
        ChunkedMarkBoundedReady.chunked_stack_points_to_gray mh st)
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
  =
  ChunkedMajorGCMarkReach.chunked_stack_reachable_from_gray_black
    mh roots st

let spot_chunked_rescan_objects_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (objs: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots /\
        ChunkedMarkPres.stack_objects_in_major mh st /\
        ChunkedMarkBoundedReady.chunked_stack_points_to_gray mh st /\
        (forall (obj: obj_addr).
          Seq.mem obj objs ==> Seq.mem obj (MH.major_objects mh)))
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots
          (ChunkedMarkBounded.chunked_rescan_objects mh objs st cap))
  =
  ChunkedMajorGCMarkReach.chunked_rescan_objects_stack_reachable_from_gray_black
    mh roots objs st cap

let spot_chunked_rescan_heap_stack_reachable_from_gray_black
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots
          (ChunkedMarkBounded.chunked_rescan_heap mh Seq.empty cap))
  =
  ChunkedMajorGCMarkReach.chunked_rescan_heap_stack_reachable_from_gray_black
    mh roots cap

let spot_chunked_resolved_pointer_field_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots obj /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh obj) /\
        U64.v i <=
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh obj) /\
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         ChunkedMarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw =
           ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child =
           ChunkedMarkDefs.chunked_resolve_object mh child_raw in
          child == child_raw /\
          ChunkedMajorGCGraph.chunked_major_vertex mh child)))
      (ensures
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         let child_raw =
           ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child =
           ChunkedMarkDefs.chunked_resolve_object mh child_raw in
         ChunkedMajorGCReach.chunked_major_reachable_from_roots
           mh roots child))
  =
  ChunkedMajorGCMarkReach.chunked_resolved_pointer_field_reachable_from_roots
    mh roots obj i

let spot_chunked_non_infix_pointer_field_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots obj /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh obj) /\
        U64.v i <=
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh obj) /\
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         ChunkedMarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw =
          ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
          ~(ChunkedSweepDefs.chunked_is_infix mh child_raw) /\
          ChunkedMajorGCGraph.chunked_major_vertex mh child_raw)))
      (ensures
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         let child_raw =
          ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
         let child =
          ChunkedMarkDefs.chunked_resolve_object mh child_raw in
         ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots child))
  =
  ChunkedMajorGCMarkReach.chunked_non_infix_pointer_field_reachable_from_roots
    mh roots obj i

let spot_chunked_make_gray_preserves_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots target)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          (ChunkedMarkDefs.chunked_make_gray mh obj) roots target)
  =
  ChunkedMajorGCMarkReach.chunked_make_gray_preserves_reachable_from_roots
    mh roots obj target

let spot_chunked_push_children_bounded_reachability_ready_child
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        ChunkedMajorGCMarkReach.chunked_push_children_bounded_reachability_ready
          mh obj i ws /\
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         ChunkedMarkDefs.chunked_is_pointer_field mh v /\
         (let child_raw =
           ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
          let child = ChunkedMarkDefs.chunked_resolve_object mh child_raw in
          ChunkedSweepDefs.chunked_is_white mh child)))
      (ensures
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         let child_raw =
          ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
         ~(ChunkedSweepDefs.chunked_is_infix mh child_raw) /\
         ChunkedMajorGCGraph.chunked_major_vertex mh child_raw))
  =
  ChunkedMajorGCMarkReach.chunked_push_children_bounded_reachability_ready_child
    mh obj i ws

let spot_chunked_push_children_bounded_reachability_ready_next
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        U64.v i < U64.v ws /\
        ChunkedMajorGCMarkReach.chunked_push_children_bounded_reachability_ready
          mh obj i ws)
      (ensures
        (let v = ChunkedMarkDefs.chunked_get_field mh obj i in
         let mh' =
           if ChunkedMarkDefs.chunked_is_pointer_field mh v then
             let child_raw =
               ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v in
             let child =
               ChunkedMarkDefs.chunked_resolve_object mh child_raw in
             if ChunkedSweepDefs.chunked_is_white mh child then
               ChunkedMarkDefs.chunked_make_gray mh child
             else
               mh
           else
             mh in
         ChunkedMajorGCMarkReach.chunked_push_children_bounded_reachability_ready
           mh' obj (U64.add i 1UL) ws))
  =
  ChunkedMajorGCMarkReach.chunked_push_children_bounded_reachability_ready_next
    mh obj i ws

let spot_chunked_make_gray_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          (ChunkedMarkDefs.chunked_make_gray mh obj) roots st)
  =
  ChunkedMajorGCMarkReach.chunked_make_gray_preserves_stack_reachable_from_roots
    mh roots obj st

let spot_chunked_make_black_preserves_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots target)
      (ensures
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          (ChunkedMarkDefs.chunked_make_black mh obj) roots target)
  =
  ChunkedMajorGCMarkReach.chunked_make_black_preserves_reachable_from_roots
    mh roots obj target

let spot_chunked_make_black_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
      (ensures
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          (ChunkedMarkDefs.chunked_make_black mh obj) roots st)
  =
  ChunkedMajorGCMarkReach.chunked_make_black_preserves_stack_reachable_from_roots
    mh roots obj st

let spot_chunked_make_gray_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots obj /\
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
      (ensures
        ChunkedMajorGCReach.chunked_gray_black_reachable
          (ChunkedMarkDefs.chunked_make_gray mh obj) roots)
  =
  ChunkedMajorGCMarkReach.chunked_make_gray_preserves_gray_black_reachable
    mh roots obj

let spot_chunked_make_black_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh) /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots
          mh roots obj /\
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
      (ensures
        ChunkedMajorGCReach.chunked_gray_black_reachable
          (ChunkedMarkDefs.chunked_make_black mh obj) roots)
  =
  ChunkedMajorGCMarkReach.chunked_make_black_preserves_gray_black_reachable
    mh roots obj

let spot_chunked_push_children_bounded_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        ChunkedMajorGCMarkReach.chunked_push_children_bounded_reachability_ready
          mh obj i ws /\
        ws == ChunkedSweepDefs.chunked_wosize_of_object mh obj /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh obj) /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots obj /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
      (ensures
        (let (mh', st') =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
           mh' roots st'))
  =
  ChunkedMajorGCMarkReach.chunked_push_children_bounded_preserves_stack_reachable_from_roots
    mh roots st obj i ws cap

let spot_chunked_push_children_bounded_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_push_children_bounded_preservation_ready
          mh obj i ws /\
        ChunkedMajorGCMarkReach.chunked_push_children_bounded_reachability_ready
          mh obj i ws /\
        ws == ChunkedSweepDefs.chunked_wosize_of_object mh obj /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh obj) /\
        ChunkedMajorGCReach.chunked_major_reachable_from_roots mh roots obj /\
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_push_children_bounded
            mh st obj i ws cap in
         ChunkedMajorGCReach.chunked_gray_black_reachable mh' roots))
  =
  ChunkedMajorGCMarkReach.chunked_push_children_bounded_preserves_gray_black_reachable
    mh roots st obj i ws cap

let spot_chunked_mark_step_bounded_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMajorGCMarkReach.chunked_mark_step_bounded_reachability_ready
          mh st cap /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
      (ensures
        (let (mh', st') =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
           mh' roots st'))
  =
  ChunkedMajorGCMarkReach.chunked_mark_step_bounded_preserves_stack_reachable_from_roots
    mh roots st cap

let spot_chunked_mark_step_bounded_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_step_bounded_preservation_ready
          mh st cap /\
        ChunkedMajorGCMarkReach.chunked_mark_step_bounded_reachability_ready
          mh st cap /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st /\
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_step_bounded mh st cap in
         ChunkedMajorGCReach.chunked_gray_black_reachable mh' roots))
  =
  ChunkedMajorGCMarkReach.chunked_mark_step_bounded_preserves_gray_black_reachable
    mh roots st cap

let spot_chunked_mark_inner_loop_preserves_stack_reachable_from_roots
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMajorGCMarkReach.chunked_mark_inner_loop_reachability_ready
          mh st cap fuel /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st)
      (ensures
        (let (mh', st') =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
           mh' roots st'))
  =
  ChunkedMajorGCMarkReach.chunked_mark_inner_loop_preserves_stack_reachable_from_roots
    mh roots st cap fuel

let spot_chunked_mark_inner_loop_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_inner_loop_preservation_ready
          mh st cap fuel /\
        ChunkedMajorGCMarkReach.chunked_mark_inner_loop_reachability_ready
          mh st cap fuel /\
        ChunkedMajorGCMarkReach.chunked_stack_reachable_from_roots
          mh roots st /\
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
      (ensures
        (let (mh', _) =
          ChunkedMarkBounded.chunked_mark_inner_loop mh st cap fuel in
         ChunkedMajorGCReach.chunked_gray_black_reachable mh' roots))
  =
  ChunkedMajorGCMarkReach.chunked_mark_inner_loop_preserves_gray_black_reachable
    mh roots st cap fuel

let spot_chunked_mark_bounded_preserves_gray_black_reachable
  (mh: MH.major_heap)
  (roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        ChunkedMarkBoundedPres.chunked_mark_bounded_preservation_ready
          mh cap fuel /\
        ChunkedMajorGCMarkReach.chunked_mark_bounded_reachability_ready
          mh cap fuel /\
        ChunkedMajorGCReach.chunked_gray_black_reachable mh roots)
      (ensures
        ChunkedMajorGCReach.chunked_gray_black_reachable
          (ChunkedMarkBounded.chunked_mark_bounded mh cap fuel) roots)
  =
  ChunkedMajorGCMarkReach.chunked_mark_bounded_preserves_gray_black_reachable
    mh roots cap fuel

let spot_chunked_major_vertex_single_chunk_compat
  (g: heap)
  (x: obj_addr)
  : Lemma
      (ensures
        (ChunkedMajorGCGraph.chunked_major_vertex
          (MH.single_chunk_major_heap g) x <==>
         Seq.mem x (Fields.objects zero_addr g)))
  =
  ChunkedMajorGCGraph.chunked_major_vertex_single_chunk_compat g x

let spot_chunked_major_vertex_intro
  (mh: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires Seq.mem x (MH.major_objects mh))
      (ensures ChunkedMajorGCGraph.chunked_major_vertex mh x)
  =
  ChunkedMajorGCGraph.chunked_major_vertex_intro mh x

let spot_chunked_major_vertex_elim
  (mh: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires ChunkedMajorGCGraph.chunked_major_vertex mh x)
      (ensures Seq.mem x (MH.major_objects mh))
  =
  ChunkedMajorGCGraph.chunked_major_vertex_elim mh x

let spot_chunked_major_vertex_from_chunk
  (mh: MH.major_heap)
  (idx: nat)
  (x: obj_addr)
  : Lemma
      (requires
        idx < Seq.length mh /\
        Seq.mem x (MH.objects_in_chunk (Seq.index mh idx)))
      (ensures ChunkedMajorGCGraph.chunked_major_vertex mh x)
  =
  ChunkedMajorGCGraph.chunked_major_vertex_from_chunk mh idx x

let spot_chunked_major_field_points_to_intro
  (mh: MH.major_heap)
  (x: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_vertex mh x /\
        ~(ChunkedMarkDefs.chunked_is_no_scan mh x) /\
        U64.v i <=
          U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh x) /\
        (let v = ChunkedMarkDefs.chunked_get_field mh x i in
         ChunkedMarkDefs.chunked_is_pointer_field mh v /\
         ChunkedMarkDefs.chunked_pointer_field_as_obj_addr mh v == y))
      (ensures
        ChunkedMajorGCGraph.chunked_major_field_points_to mh x i y)
  =
  ChunkedMajorGCGraph.chunked_major_field_points_to_intro mh x i y

let spot_chunked_major_edge_intro
  (mh: MH.major_heap)
  (x y: obj_addr)
  (i: U64.t{U64.v i >= 1})
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_field_points_to mh x i y)
      (ensures ChunkedMajorGCGraph.chunked_major_edge mh x y)
  =
  ChunkedMajorGCGraph.chunked_major_edge_intro mh x y i

let spot_chunked_major_gc_edge_elim
  (mh: MH.major_heap)
  (x y: obj_addr)
  : Lemma
      (requires ChunkedMajorGCGraph.chunked_major_edge mh x y)
      (ensures exists (i: U64.t{U64.v i >= 1}).
        ChunkedMajorGCGraph.chunked_major_field_points_to mh x i y)
  =
  ChunkedMajorGCGraph.chunked_major_edge_elim mh x y

let spot_chunked_major_field_points_to_source_vertex
  (mh: MH.major_heap)
  (x: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_field_points_to mh x i y)
      (ensures ChunkedMajorGCGraph.chunked_major_vertex mh x)
  =
  ChunkedMajorGCGraph.chunked_major_field_points_to_source_vertex mh x i y

let spot_chunked_major_field_points_to_source_not_no_scan
  (mh: MH.major_heap)
  (x: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (y: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_field_points_to mh x i y)
      (ensures ~(ChunkedMarkDefs.chunked_is_no_scan mh x))
  =
  ChunkedMajorGCGraph.chunked_major_field_points_to_source_not_no_scan
    mh x i y

let spot_chunked_major_edge_source_vertex
  (mh: MH.major_heap)
  (x y: obj_addr)
  : Lemma
      (requires ChunkedMajorGCGraph.chunked_major_edge mh x y)
      (ensures ChunkedMajorGCGraph.chunked_major_vertex mh x)
  =
  ChunkedMajorGCGraph.chunked_major_edge_source_vertex mh x y

let spot_chunked_major_edge_source_not_no_scan
  (mh: MH.major_heap)
  (x y: obj_addr)
  : Lemma
      (requires ChunkedMajorGCGraph.chunked_major_edge mh x y)
      (ensures ~(ChunkedMarkDefs.chunked_is_no_scan mh x))
  =
  ChunkedMajorGCGraph.chunked_major_edge_source_not_no_scan mh x y

let spot_chunked_major_field_preserved_intro
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_vertex mh_init x /\
        ChunkedMajorGCGraph.chunked_major_vertex mh_final x /\
        ChunkedSweepDefs.chunked_wosize_of_object mh_init x ==
          ChunkedSweepDefs.chunked_wosize_of_object mh_final x /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <=
            U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh_init x) ==>
          ChunkedMarkDefs.chunked_get_field mh_init x i ==
            ChunkedMarkDefs.chunked_get_field mh_final x i))
      (ensures
        ChunkedMajorGCGraph.chunked_major_field_preserved
          mh_init mh_final x)
  =
  ChunkedMajorGCGraph.chunked_major_field_preserved_intro
    mh_init mh_final x

let spot_chunked_major_field_preserved_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_field_preserved
          mh_init mh_final x)
      (ensures
        ChunkedMajorGCGraph.chunked_major_vertex mh_init x /\
        ChunkedMajorGCGraph.chunked_major_vertex mh_final x /\
        ChunkedSweepDefs.chunked_wosize_of_object mh_init x ==
          ChunkedSweepDefs.chunked_wosize_of_object mh_final x /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <=
            U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh_init x) ==>
          ChunkedMarkDefs.chunked_get_field mh_init x i ==
            ChunkedMarkDefs.chunked_get_field mh_final x i))
  =
  ChunkedMajorGCGraph.chunked_major_field_preserved_elim
    mh_init mh_final x

let spot_chunked_major_field_data_preserved_intro
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_vertex mh_init x /\
        ChunkedMajorGCGraph.chunked_major_vertex mh_final x /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <=
            U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh_init x) ==>
          ChunkedMarkDefs.chunked_get_field mh_init x i ==
            ChunkedMarkDefs.chunked_get_field mh_final x i))
      (ensures
        ChunkedMajorGCGraph.chunked_major_field_data_preserved
          mh_init mh_final x)
  =
  ChunkedMajorGCGraph.chunked_major_field_data_preserved_intro
    mh_init mh_final x

let spot_chunked_major_field_data_preserved_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_field_data_preserved
          mh_init mh_final x)
      (ensures
        ChunkedMajorGCGraph.chunked_major_vertex mh_init x /\
        ChunkedMajorGCGraph.chunked_major_vertex mh_final x /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <=
            U64.v (ChunkedSweepDefs.chunked_wosize_of_object mh_init x) ==>
          ChunkedMarkDefs.chunked_get_field mh_init x i ==
            ChunkedMarkDefs.chunked_get_field mh_final x i))
  =
  ChunkedMajorGCGraph.chunked_major_field_data_preserved_elim
    mh_init mh_final x

let spot_chunked_major_field_preserved_single_chunk_from_dense
  (g_init: heap)
  (g_final: heap)
  (x: obj_addr)
  : Lemma
      (requires
        Seq.mem x (Fields.objects zero_addr g_init) /\
        Seq.mem x (Fields.objects zero_addr g_final) /\
        U64.v x >= U64.v zero_addr + U64.v mword /\
        Obj.wosize_of_object x g_init ==
          Obj.wosize_of_object x g_final /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <= U64.v (Obj.wosize_of_object x g_init) ==>
          GC.Spec.HeapGraph.get_field g_init x i ==
          GC.Spec.HeapGraph.get_field g_final x i))
      (ensures
        ChunkedMajorGCGraph.chunked_major_field_preserved
          (MH.single_chunk_major_heap g_init)
          (MH.single_chunk_major_heap g_final)
          x)
  =
  ChunkedMajorGCGraph.chunked_major_field_preserved_single_chunk_from_dense
    g_init g_final x

let spot_chunked_major_field_data_preserved_single_chunk_from_dense
  (g_init: heap)
  (g_final: heap)
  (x: obj_addr)
  : Lemma
      (requires
        Seq.mem x (Fields.objects zero_addr g_init) /\
        Seq.mem x (Fields.objects zero_addr g_final) /\
        U64.v x >= U64.v zero_addr + U64.v mword /\
        (forall (i: U64.t). U64.v i >= 1 /\
          U64.v i <= U64.v (Obj.wosize_of_object x g_init) ==>
          GC.Spec.HeapGraph.get_field g_init x i ==
          GC.Spec.HeapGraph.get_field g_final x i))
      (ensures
        ChunkedMajorGCGraph.chunked_major_field_data_preserved
          (MH.single_chunk_major_heap g_init)
          (MH.single_chunk_major_heap g_final)
          x)
  =
  ChunkedMajorGCGraph.chunked_major_field_data_preserved_single_chunk_from_dense
    g_init g_final x

let spot_chunked_major_pointer_classification_preserved_intro
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  : Lemma
      (requires
        (forall (v: U64.t).
          ChunkedMarkDefs.chunked_is_pointer_field mh_init v ==
          ChunkedMarkDefs.chunked_is_pointer_field mh_final v))
      (ensures
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          mh_init mh_final)
  =
  ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved_intro
    mh_init mh_final

let spot_chunked_major_pointer_classification_preserved_single_chunk
  (g_init: heap)
  (g_final: heap)
  : Lemma
      (ensures
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          (MH.single_chunk_major_heap g_init)
          (MH.single_chunk_major_heap g_final))
  =
  ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved_single_chunk
    g_init g_final

let spot_chunked_major_successors_preserved_from_fields
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_field_preserved
          mh_init mh_final x /\
        ChunkedMarkDefs.chunked_is_no_scan mh_init x ==
          ChunkedMarkDefs.chunked_is_no_scan mh_final x /\
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          mh_init mh_final)
      (ensures
        ChunkedMajorGCGraph.chunked_major_successors_preserved
          mh_init mh_final x)
  =
  ChunkedMajorGCGraph.chunked_major_successors_preserved_from_fields
    mh_init mh_final x

let spot_chunked_major_live_subgraph_preserved_from_fields
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        (forall (x: obj_addr).
          live x ==>
          ChunkedMajorGCGraph.chunked_major_field_preserved
            mh_init mh_final x) /\
        (forall (x: obj_addr).
          live x ==>
          ChunkedMarkDefs.chunked_is_no_scan mh_init x ==
            ChunkedMarkDefs.chunked_is_no_scan mh_final x) /\
        ChunkedMajorGCGraph.chunked_major_pointer_classification_preserved
          mh_init mh_final)
      (ensures
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh_init mh_final live)
  =
  ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved_from_fields
    mh_init mh_final live

let spot_chunked_major_successors_preserved_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (x: obj_addr)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_successors_preserved
          mh_init mh_final x)
      (ensures
        forall (y: obj_addr).
          ChunkedMajorGCGraph.chunked_major_edge mh_init x y <==>
          ChunkedMajorGCGraph.chunked_major_edge mh_final x y)
  =
  ChunkedMajorGCGraph.chunked_major_successors_preserved_elim
    mh_init mh_final x

let spot_chunked_major_live_subgraph_preserved_intro
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        (forall (x: obj_addr).
          live x ==>
          ChunkedMajorGCGraph.chunked_major_vertex mh_init x /\
          ChunkedMajorGCGraph.chunked_major_vertex mh_final x) /\
        (forall (x: obj_addr).
          live x ==>
          forall (y: obj_addr).
          (ChunkedMajorGCGraph.chunked_major_edge mh_init x y <==>
           ChunkedMajorGCGraph.chunked_major_edge mh_final x y)))
      (ensures
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh_init mh_final live)
  =
  ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved_intro
    mh_init mh_final live

let spot_chunked_major_live_subgraph_vertices_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh_init mh_final live)
      (ensures
        forall (x: obj_addr).
          live x ==>
          ChunkedMajorGCGraph.chunked_major_vertex mh_init x /\
          ChunkedMajorGCGraph.chunked_major_vertex mh_final x)
  =
  ChunkedMajorGCGraph.chunked_major_live_subgraph_vertices_elim
    mh_init mh_final live

let spot_chunked_major_live_subgraph_edges_elim
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh_init mh_final live)
      (ensures
        forall (x: obj_addr).
          live x ==>
          forall (y: obj_addr).
          (ChunkedMajorGCGraph.chunked_major_edge mh_init x y <==>
           ChunkedMajorGCGraph.chunked_major_edge mh_final x y))
  =
  ChunkedMajorGCGraph.chunked_major_live_subgraph_edges_elim
    mh_init mh_final live

let spot_chunked_major_live_subgraph_preserved_trans
  (mh0 mh1 mh2: MH.major_heap)
  (live: obj_addr -> prop)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh0 mh1 live /\
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh1 mh2 live)
      (ensures
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh0 mh2 live)
  =
  ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved_trans
    mh0 mh1 mh2 live

let spot_chunked_major_live_subgraph_preserved_subset
  (mh_init: MH.major_heap)
  (mh_final: MH.major_heap)
  (live_big live_small: obj_addr -> prop)
  : Lemma
      (requires
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh_init mh_final live_big /\
        (forall (x: obj_addr). live_small x ==> live_big x))
      (ensures
        ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
          mh_init mh_final live_small)
  =
  ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved_subset
    mh_init mh_final live_big live_small

let spot_chunked_mark_aux_empty_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        ChunkedMarkDefs.chunked_mark_aux
          (MH.single_chunk_major_heap g) st fuel ==
        MH.single_chunk_major_heap (Mark.mark_aux g st fuel))
  =
  ChunkedMarkCompat.chunked_mark_aux_empty_single_chunk_compat g st fuel

let spot_chunked_mark_aux_out_of_fuel_single_chunk_compat
  (g: heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (ensures
        ChunkedMarkDefs.chunked_mark_aux
          (MH.single_chunk_major_heap g) st 0 ==
        MH.single_chunk_major_heap (Mark.mark_aux g st 0))
  =
  ChunkedMarkCompat.chunked_mark_aux_out_of_fuel_single_chunk_compat g st
#pop-options

let spot_expand_on_oom_pre
  (mh: MH.major_heap) (fp: U64.t) (requested_wz fuel: nat)
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t) : Tot prop =
  MH.well_formed_major_heap mh /\
  MH.chunk_disjoint_from_all fresh mh /\
  (SpecMajorAlloc.major_alloc_spec_with_fuel
    mh fp requested_wz fuel).major_obj_out == 0UL /\
  U64.v fresh.base >= U64.v zero_addr /\
  requested_wz > 0 /\
  SpecMajorAlloc.fresh_chunk_wosize fresh >= requested_wz /\
  SpecAlloc.normalized_wosize requested_wz <=
    SpecMajorAlloc.fresh_chunk_wosize fresh /\
  ~(MH.chunk_contains_addr fresh old_addr) /\
  MH.read_word_in_major mh old_addr == Some old_value

let spot_expand_on_oom_allocates_fresh_and_preserves_old_read
  (mh: MH.major_heap) (fp: U64.t) (requested_wz fuel: nat)
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t)
  : Lemma
      (requires spot_expand_on_oom_pre
        mh fp requested_wz fuel fresh old_addr old_value)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_expand_on_oom
             mh fp requested_wz fuel fresh in
         r.major_obj_out == SpecMajorAlloc.fresh_chunk_object fresh /\
         r.major_obj_out <> 0UL /\
         MH.read_word_in_major r.major_alloc_out old_addr == Some old_value /\
         ~(Seq.mem
            (SpecMajorAlloc.fresh_chunk_object fresh)
            (MH.major_objects mh))))
  =
  SpecMajorAlloc.major_alloc_expand_on_oom_returns_fresh
    mh fp requested_wz fuel fresh;
  SpecMajorAlloc.major_alloc_expand_on_oom_preserves_old_read
    mh fp requested_wz fuel fresh old_addr;
  SpecMajorAlloc.expand_major_heap_fresh_not_old mh fresh fp;
  SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
  assert (U64.v (SpecMajorAlloc.fresh_chunk_object fresh) >= U64.v fresh.base + U64.v mword);
  assert (U64.v (SpecMajorAlloc.fresh_chunk_object fresh) >= U64.v mword);
  assert (SpecMajorAlloc.fresh_chunk_object fresh <> 0UL)

let spot_ensure_capacity_pre
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t) : Tot prop =
  MH.well_formed_major_heap mh /\
  SpecMajorAlloc.major_fl_valid mh fp fuel /\
  SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
  SpecMajorAlloc.major_fl_capacity mh fp fuel < needed /\
  MH.chunk_disjoint_from_all fresh mh /\
  SpecMajorAlloc.fresh_chunk_wosize fresh +
    SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed /\
  fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
  U64.v fresh.base >= U64.v zero_addr /\
  ~(MH.chunk_contains_addr fresh old_addr) /\
  MH.read_word_in_major mh old_addr == Some old_value

let spot_ensure_capacity_expands_and_preserves_old_read
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t)
  : Lemma
      (requires spot_ensure_capacity_pre
        mh fp fuel needed fresh old_addr old_value)
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_capacity_spec
             mh fp fuel needed fresh in
         SpecMajorAlloc.major_fl_capacity
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed /\
         SpecMajorAlloc.major_fl_valid
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_above_zero
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         MH.well_formed_major_heap r.capacity_major_out /\
         MH.read_word_in_major r.capacity_major_out old_addr == Some old_value))
  =
  SpecMajorAlloc.ensure_major_capacity_has_capacity mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_fl_valid mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_fl_above_zero mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_wf mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_capacity_preserves_old_read mh fp fuel needed fresh old_addr

let spot_expand_major_heap_head_wosize
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires U64.v fresh.base >= U64.v zero_addr)
      (ensures
        (let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
         SpecMajorAlloc.major_fl_head_wosize r.major_out r.fp_out ==
         SpecMajorAlloc.fresh_chunk_wosize fresh))
  = SpecMajorAlloc.expand_major_heap_head_wosize mh fresh fp

let spot_head_preflight_alloc_no_oom
  (mh: MH.major_heap) (fp: U64.t) (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  SpecAlloc.normalized_wosize requested_wz)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\ r.major_obj_out <> 0UL))
  = SpecMajorAlloc.major_alloc_spec_with_fuel_head_no_oom
      mh fp requested_wz fuel

let spot_ensure_head_capacity_preserves_shape_and_old_read
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk) (old_addr: hp_addr) (old_value: U64.t)
  : Lemma
      (requires MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                MH.read_word_in_major mh old_addr == Some old_value /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 ~(MH.chunk_contains_addr fresh old_addr)))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             mh fp fuel needed fresh in
         SpecMajorAlloc.major_fl_head_wosize
           r.capacity_major_out r.capacity_fp_out >= needed /\
         SpecMajorAlloc.major_fl_valid
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_above_zero
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_blocks_fit
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         MH.well_formed_major_heap r.capacity_major_out /\
         MH.read_word_in_major r.capacity_major_out old_addr == Some old_value))
  =
  SpecMajorAlloc.ensure_major_head_capacity_has_head_wosize
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_valid
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_above_zero
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_fl_blocks_fit
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_wf
    mh fp fuel needed fresh;
  SpecMajorAlloc.ensure_major_head_capacity_preserves_old_read
    mh fp fuel needed fresh old_addr

let spot_ensure_head_capacity_alloc_no_oom
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requested_wz: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 0 /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             mh fp fuel
             (SpecMajorAlloc.major_alloc_demand_wosize requested_wz) fresh in
         let a =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             r.capacity_major_out r.capacity_fp_out requested_wz
             r.capacity_fuel_out in
         a.major_obj_out == r.capacity_fp_out /\ a.major_obj_out <> 0UL))
  = SpecMajorAlloc.ensure_major_head_capacity_alloc_no_oom
      mh fp fuel requested_wz fresh

let spot_major_alloc_after_expand_split_preserves_head_wosize
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (requested_wz fuel remaining: nat)
  : Lemma
      (requires U64.v fresh.base >= U64.v zero_addr /\
                requested_wz > 0 /\
                remaining > 0 /\
                SpecMajorAlloc.fresh_chunk_wosize fresh >=
                  requested_wz + 1 + remaining)
      (ensures
        (let er = SpecMajorAlloc.expand_major_heap mh fresh fp in
         let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             er.major_out er.fp_out requested_wz (fuel + 1) in
         r.major_obj_out == er.fp_out /\
         r.major_fp_out <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           r.major_alloc_out r.major_fp_out >= remaining))
  = SpecMajorAlloc.major_alloc_after_expand_split_preserves_head_wosize
      mh fresh fp requested_wz fuel remaining

let spot_major_alloc_head_split_preserves_head_wosize
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel remaining: nat)
  : Lemma
      (requires fuel > 0 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                remaining > 0 /\
                MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  requested_wz + 1 + remaining)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         MH.well_formed_major_heap r.major_alloc_out /\
         SpecMajorAlloc.major_alloc_result_fp_in_objects r /\
         SpecMajorAlloc.major_fl_head_wosize
           r.major_alloc_out r.major_fp_out >= remaining))
  = SpecMajorAlloc.major_alloc_head_split_preserves_head_wosize
      mh fp requested_wz fuel remaining

let spot_major_alloc_head_split_link_not_self
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                MH.well_formed_major_heap mh /\
                SpecMajorAlloc.major_fl_valid mh fp fuel /\
                SpecMajorAlloc.major_fl_above_zero mh fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >= requested_wz + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         SpecMajorAlloc.major_alloc_result_fp_link_not_self r))
  = SpecMajorAlloc.major_alloc_head_split_link_not_self
      mh fp requested_wz fuel

let spot_chunked_major_alloc_shape_active_head_split
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                requested_wz > 0 /\
                GenInv.chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  requested_wz + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel
             mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         SpecMajorAlloc.major_alloc_result_fp_in_objects r /\
         GenInv.chunked_major_alloc_shape
           r.major_alloc_out r.major_fp_out fuel))
  = GenInv.chunked_major_alloc_shape_active_head_split
      mh fp requested_wz fuel

let spot_chunked_major_alloc_shape_alloc_list_head_split
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  SpecMajorAllocMultiAlloc.allocation_list_demand requests + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  = GenInv.chunked_major_alloc_shape_alloc_list_head_split
      mh fp fuel requests

let spot_chunked_major_alloc_shape_alloc_list_with_budget
  (mh: MH.major_heap) (fp: U64.t) (fuel: nat)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >= budget + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  = GenInv.chunked_major_alloc_shape_alloc_list_head_split_with_budget
      mh fp fuel requests budget

let spot_dense_alloc_list_single_chunk_with_budget_no_oom
  (g: heap) (fp: U64.t) (fuel: nat)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap g) /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap g) fp fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap g) fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap g) fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap g) fp >= budget + 1)
      (ensures
        (let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_spec
             g fp fuel requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))
  =
  SpecMajorAllocMultiAlloc.dense_alloc_list_head_split_nonzero_single_chunk_with_budget
    g fp fuel requests budget

let spot_chunked_major_alloc_shape_alloc_minor_objects_head_split
  (minor: minor_state) (mh: MH.major_heap) (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires fuel > 1 /\
                minor_wf minor /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape mh fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize mh fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let requests = PromotionDemand.minor_promotion_requests minor in
         let r =
           SpecMajorAllocMultiAlloc.major_alloc_list_spec
             mh fp fuel requests in
         r.list_fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape r.list_major_out r.list_fp_out fuel /\
         SpecMajorAlloc.major_fl_head_wosize
           r.list_major_out r.list_fp_out >= 1 /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.list_objs_out))
  = GenInv.chunked_major_alloc_shape_alloc_minor_objects_head_split
      minor mh fp fuel

let spot_chunked_collection_shape_ensure_minor_promotion_allocs
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let requests = PromotionDemand.minor_promotion_requests minor in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_minor_promotion_head_capacity_allocs
      minor mh fp fuel fresh

let spot_chunked_collection_shape_ensure_head_capacity_with_chain
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_with_chain
      minor mh fp fuel needed fresh

let spot_chunked_collection_shape_ensure_head_capacity_with_chain_blue
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
                GenInv.chunked_chain_objects_blue mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
        GenInv.chunked_chain_objects_blue
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_with_chain_blue
      minor mh fp fuel needed fresh

let spot_chunked_collection_shape_ensure_head_capacity_with_chain_blue_value_safety
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
                GenInv.chunked_chain_objects_blue mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 (forall (obj:obj_addr).
                  Seq.mem obj (MH.major_objects mh) ==>
                    CG.chunked_major_field_values_miss_fresh
                      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        SpecMajorAlloc.major_fl_chain_terminates
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
        GenInv.chunked_chain_objects_blue
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_with_chain_blue_value_safety
      minor mh fp fuel needed fresh

let spot_chunked_collection_shape_ensure_head_capacity_alloc_list_budget
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < budget + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= budget + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = budget + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_alloc_list_with_budget
      minor mh fp fuel fresh requests budget

let spot_chunked_collection_shape_ensure_head_capacity_alloc_list_budget_value_safety
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  (requests: list nat) (budget: nat)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  budget /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < budget + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= budget + 1 /\
                 (forall (obj:obj_addr).
                  Seq.mem obj (MH.major_objects mh) ==>
                    CG.chunked_major_field_values_miss_fresh
                      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)))
      (ensures (
        let needed = budget + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_alloc_list_with_budget_value_safety
      minor mh fp fuel fresh requests budget

let spot_chunked_collection_shape_ensure_minor_promotion_budget_alloc_list
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  PromotionDemand.minor_promotion_demand minor /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_minor_promotion_budget_alloc_list
      minor mh fp fuel fresh requests

let spot_chunked_collection_shape_ensure_minor_promotion_budget_alloc_list_value_safety
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  (requests: list nat)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                SpecMajorAllocMultiAlloc.all_requests_positive requests /\
                SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
                  PromotionDemand.minor_promotion_demand minor /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 (forall (obj:obj_addr).
                  Seq.mem obj (MH.major_objects mh) ==>
                    CG.chunked_major_field_values_miss_fresh
                      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_minor_promotion_budget_alloc_list_value_safety
      minor mh fp fuel fresh requests

let spot_chunked_collection_shape_ensure_minor_promotion_head_capacity_allocs_value_safety
  (minor: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 1 /\
                GenInv.chunked_collection_heap_shape minor mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   PromotionDemand.minor_promotion_demand minor + 1 ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   PromotionDemand.minor_promotion_demand minor + 1 /\
                 (forall (obj:obj_addr).
                  Seq.mem obj (MH.major_objects mh) ==>
                    CG.chunked_major_field_values_miss_fresh
                      mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)))
      (ensures (
        let needed = PromotionDemand.minor_promotion_demand minor + 1 in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let requests = PromotionDemand.minor_promotion_requests minor in
        let a =
          SpecMajorAllocMultiAlloc.major_alloc_list_spec
            r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out
            requests in
        GenInv.chunked_collection_heap_shape
          minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.list_fp_out <> 0UL /\
        GenInv.chunked_major_alloc_shape a.list_major_out a.list_fp_out
          r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          a.list_major_out a.list_fp_out >= 1 /\
        SpecMajorAllocMultiAlloc.allocated_objects_nonzero
          a.list_objs_out))
  = GenInv.chunked_collection_heap_shape_ensure_minor_promotion_head_capacity_allocs_value_safety
      minor mh fp fuel fresh

let spot_cheney_forwarded_minor_requests_budget
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires minor_wf minor)
      (ensures
        (let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         SpecMajorAllocMultiAlloc.all_requests_positive requests /\
         SpecMajorAllocMultiAlloc.allocation_list_demand requests <=
           PromotionDemand.minor_promotion_demand minor))
  =
  CheneyPreservation.cheney_forwarded_minor_requests_positive
    minor major fp roots;
  CheneyPreservation.cheney_forwarded_minor_requests_demand_bound
    minor major fp roots

let spot_cheney_unforwarded_split_demand_bound
  (minor: minor_state) (cs: cheney_state)
  : Lemma
      (ensures
        CheneyPreservation.cheney_unforwarded_split_demand minor cs <=
        PromotionDemand.minor_promotion_demand minor)
  =
  CheneyPreservation.cheney_unforwarded_split_demand_bound minor cs

let spot_cheney_forwarded_dense_alloc_list_single_chunk_no_oom
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (fuel: nat)
  : Lemma
      (requires minor_wf minor /\
                fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap major) /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_spec
             major fp fuel requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))
  =
  CheneyPreservation.cheney_forwarded_dense_alloc_list_single_chunk_no_oom
    minor major fp roots fuel

let spot_cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                MH.well_formed_major_heap
                  (MH.single_chunk_major_heap major) /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         let r =
           SpecMajorAllocMultiAlloc.dense_alloc_list_default_spec
             major fp requests in
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           r.dense_list_objs_out))
  =
  CheneyPreservation.cheney_forwarded_dense_alloc_list_default_single_chunk_no_oom
    minor major fp roots

let spot_promote_object_head_no_oom_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >= wosize)
      (ensures
        (promote_object minor major obj fp wosize).new_addr <> 0UL)
  =
  CheneyPreservation.promote_object_head_no_oom_single_chunk
    minor major obj fp wosize

let spot_promote_minor_object_head_no_oom_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0})
  : Lemma
      (requires minor_wf minor /\
                Seq.mem obj (minor_objects minor) /\
                wosize == minor_wosize minor obj /\
                SpecAlloc.alloc_search_fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (promote_object minor major obj fp wosize).new_addr <> 0UL)
  =
  CheneyPreservation.promote_minor_object_head_no_oom_single_chunk
    minor major obj fp wosize

let spot_chunked_copy_fields_frame_after
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (target: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        U64.v dst_obj + n * U64.v mword <= U64.v target)
      (ensures
        MH.read_word_in_major
          (ChunkedPromote.chunked_copy_fields
            minor mh src_obj dst_obj i n)
          target == Some old)
  =
  ChunkedPromote.chunked_copy_fields_frame_after
    minor mh src_obj dst_obj i n target old

let spot_chunked_copy_fields_preserves_major_objects
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj dst_obj: U64.t) (i n idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        U64.v dst_obj >= U64.v mword /\
        U64.v dst_obj < heap_size /\
        U64.v dst_obj % U64.v mword == 0 /\
        i <= n /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (dst_obj <: obj_addr)) == Some idx /\
        Seq.mem (dst_obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (dst_obj <: obj_addr)) ==
          Some hdr /\
        n <= U64.v (Obj.getWosize hdr))
      (ensures
        (let mh' =
           ChunkedPromote.chunked_copy_fields
             minor mh src_obj dst_obj i n in
         MH.well_formed_major_heap mh' /\
         MH.major_objects mh' == MH.major_objects mh /\
         MH.read_word_in_major mh' (hd_address (dst_obj <: obj_addr)) ==
           Some hdr))
  =
  ChunkedPromote.chunked_copy_fields_preserves_major_objects
    minor mh src_obj dst_obj i n idx hdr

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
let spot_chunked_copy_fields_field_effect
  (minor: minor_state) (mh: MH.major_heap)
  (src_obj dst_obj: U64.t) (i n j idx: nat)
  (field_addr: hp_addr) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        U64.v dst_obj >= U64.v mword /\
        U64.v dst_obj < heap_size /\
        U64.v dst_obj % U64.v mword == 0 /\
        i <= j /\ j < n /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (dst_obj <: obj_addr)) == Some idx /\
        Seq.mem (dst_obj <: obj_addr) (MH.major_objects mh) /\
        CG.chunked_major_field_slot (dst_obj <: obj_addr) j == Some field_addr /\
        MH.read_word_in_major mh (hd_address (dst_obj <: obj_addr)) ==
         Some hdr /\
        n <= U64.v (Obj.getWosize hdr))
      (ensures
        (let result =
          ChunkedPromote.chunked_copy_fields
            minor mh src_obj dst_obj i n in
         MH.read_word_in_major result field_addr ==
          Some (minor_read_field minor src_obj j)))
  =
  ChunkedPromote.chunked_copy_fields_field_effect
    minor mh src_obj dst_obj i n j idx hdr;
  let result =
    ChunkedPromote.chunked_copy_fields minor mh src_obj dst_obj i n in
  let addr_nat = U64.v dst_obj + j * U64.v mword in
  let addr : hp_addr = U64.uint_to_t addr_nat in
  CG.chunked_major_field_slot_elim (dst_obj <: obj_addr) j field_addr;
  assert (U64.v field_addr == addr_nat);
  assert (U64.v addr == addr_nat);
  U64.v_inj addr field_addr;
  assert (addr == field_addr)
#pop-options

let spot_chunked_promote_object_success_field_effect
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (j: nat) (field_addr: hp_addr) (idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        (let alloc_res =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst = alloc_res.major_obj_out in
         alloc_res.major_obj_out <> 0UL /\
         U64.v dst >= U64.v mword /\
         U64.v dst < heap_size /\
         U64.v dst % U64.v mword == 0 /\
         j < wosize /\
         U64.v field_addr == U64.v dst + j * U64.v mword /\
         MH.well_formed_major_heap alloc_res.major_alloc_out /\
         idx < Seq.length alloc_res.major_alloc_out /\
         MH.lookup_chunk_index alloc_res.major_alloc_out
           (hd_address (dst <: obj_addr)) == Some idx /\
         Seq.mem (dst <: obj_addr)
           (MH.major_objects alloc_res.major_alloc_out) /\
         MH.read_word_in_major alloc_res.major_alloc_out
           (hd_address (dst <: obj_addr)) == Some hdr /\
         U64.v (Obj.getWosize hdr) == wosize))
      (ensures
        (let alloc_res =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst = alloc_res.major_obj_out in
         let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         let addr_nat = U64.v dst + j * U64.v mword in
         res.new_addr == dst /\
         addr_nat + U64.v mword <= heap_size /\
         addr_nat % U64.v mword == 0 /\
         MH.read_word_in_major res.major_out field_addr ==
           Some (minor_read_field minor obj j)))
  =
  ChunkedPromote.chunked_promote_object_success_field_effect
    minor mh obj fp wosize fuel j field_addr idx hdr

let spot_chunked_promote_object_success_header_effect
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        (let alloc_res =
          SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst = alloc_res.major_obj_out in
         alloc_res.major_obj_out <> 0UL /\
         U64.v dst >= U64.v mword /\
         U64.v dst < heap_size /\
         U64.v dst % U64.v mword == 0 /\
         MH.well_formed_major_heap alloc_res.major_alloc_out /\
         idx < Seq.length alloc_res.major_alloc_out /\
         MH.lookup_chunk_index alloc_res.major_alloc_out
          (hd_address (dst <: obj_addr)) == Some idx /\
         Seq.mem (dst <: obj_addr)
          (MH.major_objects alloc_res.major_alloc_out) /\
         MH.read_word_in_major alloc_res.major_alloc_out
          (hd_address (dst <: obj_addr)) == Some hdr /\
         U64.v (Obj.getWosize hdr) == wosize /\
         minor_tag minor obj < 256))
      (ensures
        (let alloc_res =
          SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
          let dst = alloc_res.major_obj_out in
          let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
          res.new_addr == dst /\
          MH.well_formed_major_heap res.major_out /\
          Seq.mem (dst <: obj_addr) (MH.major_objects res.major_out) /\
          (match MH.read_word_in_major res.major_out
             (hd_address (dst <: obj_addr)) with
           | Some final_hdr ->
             U64.v (Obj.getWosize final_hdr) == wosize /\
             Obj.getColor final_hdr == GC.Lib.Header.White /\
             U64.v (Obj.getTag final_hdr) == minor_tag minor obj
           | None -> False)))
  =
  ChunkedPromote.chunked_promote_object_success_header_effect
    minor mh obj fp wosize fuel idx hdr

let spot_chunked_cheney_forward_normal_head_split_field_effect
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat) (field_addr: hp_addr)
  : Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        j < minor_wosize minor addr /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
        U64.v field_addr ==
          U64.v cs.ccs_fp + j * U64.v mword)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         cs'.ccs_fwd addr == cs.ccs_fp /\
         MH.read_word_in_major cs'.ccs_major field_addr ==
           Some (minor_read_field minor addr j)))
  =
  ChunkedCheney.chunked_cheney_forward_normal_head_split_field_effect
    minor cs addr fuel j field_addr

let spot_chunked_cheney_forward_normal_head_split_header_effect
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal minor cs addr fuel in
         cs'.ccs_fwd addr == cs.ccs_fp /\
         MH.well_formed_major_heap cs'.ccs_major /\
         Seq.mem (cs.ccs_fp <: obj_addr) (MH.major_objects cs'.ccs_major) /\
         (match MH.read_word_in_major cs'.ccs_major
            (hd_address (cs.ccs_fp <: obj_addr)) with
          | Some final_hdr ->
            U64.v (Obj.getWosize final_hdr) == minor_wosize minor addr /\
            Obj.getColor final_hdr == GC.Lib.Header.White /\
            U64.v (Obj.getTag final_hdr) == minor_tag minor addr
          | None -> False)))
  =
  ChunkedCheney.chunked_cheney_forward_normal_head_split_header_effect
    minor cs addr fuel

let spot_chunked_cheney_forward_one_normal_head_split_field_effect
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat) (field_addr: hp_addr)
  : Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        j < minor_wosize minor addr /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
        U64.v field_addr ==
          U64.v cs.ccs_fp + j * U64.v mword)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         cs'.ccs_fwd addr == cs.ccs_fp /\
         MH.read_word_in_major cs'.ccs_major field_addr ==
           Some (minor_read_field minor addr j)))
  =
  ChunkedCheney.chunked_cheney_forward_one_normal_head_split_field_effect
    minor cs addr fuel j field_addr

let spot_chunked_cheney_forward_one_normal_head_split_header_effect
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         cs'.ccs_fwd addr == cs.ccs_fp /\
         MH.well_formed_major_heap cs'.ccs_major /\
         Seq.mem (cs.ccs_fp <: obj_addr) (MH.major_objects cs'.ccs_major) /\
         (match MH.read_word_in_major cs'.ccs_major
            (hd_address (cs.ccs_fp <: obj_addr)) with
          | Some final_hdr ->
            U64.v (Obj.getWosize final_hdr) == minor_wosize minor addr /\
            Obj.getColor final_hdr == GC.Lib.Header.White /\
            U64.v (Obj.getTag final_hdr) == minor_tag minor addr
          | None -> False)))
  =
  ChunkedCheney.chunked_cheney_forward_one_normal_head_split_header_effect
    minor cs addr fuel

let spot_major_write_word_or_same_read_frame
  (mh: MH.major_heap) (write_addr target: hp_addr)
  (value old: U64.t)
  : Lemma
      (requires
        MH.read_word_in_major mh target == Some old /\
        (U64.v target + U64.v mword <= U64.v write_addr \/
         U64.v write_addr + U64.v mword <= U64.v target))
      (ensures
        MH.read_word_in_major
          (SpecMajorAlloc.major_write_word_or_same mh write_addr value)
          target == Some old)
  =
  ChunkedPromote.major_write_word_or_same_read_frame
    mh write_addr target value old

let spot_chunked_set_promoted_tag_read_frame
  (mh: MH.major_heap) (obj: U64.t) (tag: nat)
  (target: hp_addr) (old: U64.t)
  : Lemma
      (requires
        U64.v obj >= U64.v mword /\
        U64.v obj < heap_size /\
        U64.v obj % U64.v mword == 0 /\
        MH.read_word_in_major mh target == Some old /\
        (let dst : obj_addr = obj in
         U64.v target + U64.v mword <= U64.v (hd_address dst) \/
         U64.v (hd_address dst) + U64.v mword <= U64.v target))
      (ensures
        MH.read_word_in_major
          (ChunkedPromote.chunked_set_promoted_tag mh obj tag)
          target == Some old)
  =
  ChunkedPromote.chunked_set_promoted_tag_read_frame
    mh obj tag target old

let spot_chunked_set_promoted_tag_preserves_major_objects
  (mh: MH.major_heap) (obj: U64.t) (tag idx: nat) (hdr: U64.t)
  : Lemma
      (requires
        tag < 256 /\
        MH.well_formed_major_heap mh /\
        U64.v obj >= U64.v mword /\
        U64.v obj < heap_size /\
        U64.v obj % U64.v mword == 0 /\
        idx < Seq.length mh /\
        MH.lookup_chunk_index mh (hd_address (obj <: obj_addr)) == Some idx /\
        Seq.mem (obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (obj <: obj_addr)) == Some hdr)
      (ensures
        (let mh' = ChunkedPromote.chunked_set_promoted_tag mh obj tag in
         MH.well_formed_major_heap mh' /\
         MH.major_objects mh' == MH.major_objects mh))
  =
  ChunkedPromote.chunked_set_promoted_tag_preserves_major_objects
    mh obj tag idx hdr

let spot_chunked_set_promoted_tag_header_effect
  (mh: MH.major_heap) (obj: U64.t) (tag: nat) (hdr: U64.t)
  : Lemma
      (requires
        tag < 256 /\
        MH.well_formed_major_heap mh /\
        U64.v obj >= U64.v mword /\
        U64.v obj < heap_size /\
        U64.v obj % U64.v mword == 0 /\
        Seq.mem (obj <: obj_addr) (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address (obj <: obj_addr)) == Some hdr)
      (ensures
        (let new_hdr =
           Obj.makeHeader (Obj.getWosize hdr) GC.Lib.Header.White
             (U64.uint_to_t tag) in
         let mh' = ChunkedPromote.chunked_set_promoted_tag mh obj tag in
         MH.well_formed_major_heap mh' /\
         MH.major_objects mh' == MH.major_objects mh /\
         MH.read_word_in_major mh' (hd_address (obj <: obj_addr)) ==
           Some new_hdr /\
         Obj.getWosize new_hdr == Obj.getWosize hdr /\
         Obj.getColor new_hdr == GC.Lib.Header.White /\
         Obj.getTag new_hdr == U64.uint_to_t tag))
  =
  ChunkedPromote.chunked_set_promoted_tag_header_effect mh obj tag hdr

let spot_chunked_promote_object_default_single_chunk_compat
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires
        (let alloc_res = SpecAlloc.alloc_spec major fp wosize in
         alloc_res.obj_out <> 0UL ==>
         U64.v alloc_res.obj_out >= U64.v zero_addr + U64.v mword /\
         U64.v alloc_res.obj_out < heap_size /\
         U64.v alloc_res.obj_out % U64.v mword == 0))
      (ensures
        (let chunked =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor (MH.single_chunk_major_heap major) obj fp wosize
             SpecAlloc.alloc_search_fuel in
         let dense = promote_object minor major obj fp wosize in
         chunked.major_out == MH.single_chunk_major_heap dense.major_out /\
         chunked.fp_out == dense.fp_out /\
         chunked.new_addr == dense.new_addr))
  =
  CheneyPreservation.chunked_promote_object_default_single_chunk_compat
    minor major obj fp wosize

let spot_chunked_cheney_forward_one_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_one
          minor (ChunkedCheney.single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_one minor cs addr))
  =
  CheneyPreservation.chunked_cheney_forward_one_default_single_chunk_compat
    minor cs addr

let spot_chunked_cheney_forward_fields_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_fields
          minor (ChunkedCheney.single_chunk_cheney_state cs) parent idx wosize
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_fields minor cs parent idx wosize))
  =
  CheneyPreservation.chunked_cheney_forward_fields_default_single_chunk_compat
    minor cs parent idx wosize

let spot_chunked_cheney_forward_roots_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (roots: Seq.seq U64.t) (idx: nat)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_forward_roots
          minor (ChunkedCheney.single_chunk_cheney_state cs) roots idx
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_forward_roots minor cs roots idx))
  =
  CheneyPreservation.chunked_cheney_forward_roots_default_single_chunk_compat
    minor cs roots idx

let spot_chunked_cheney_scan_default_single_chunk_compat
  (minor: minor_state) (cs: cheney_state) (scan scan_fuel: nat)
  : Lemma
      (ensures
        ChunkedCheney.chunked_cheney_scan
          minor (ChunkedCheney.single_chunk_cheney_state cs) scan scan_fuel
          SpecAlloc.alloc_search_fuel ==
        ChunkedCheney.single_chunk_cheney_state
          (cheney_scan minor cs scan scan_fuel))
  =
  CheneyPreservation.chunked_cheney_scan_default_single_chunk_compat
    minor cs scan scan_fuel

let spot_chunked_cheney_promote_default_single_chunk_compat
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (ensures
        (let chunked =
           ChunkedCheney.chunked_cheney_promote
             minor (MH.single_chunk_major_heap major) fp roots
             SpecAlloc.alloc_search_fuel in
         let dense = cheney_promote minor major fp roots in
         chunked.major_final == MH.single_chunk_major_heap dense.major_final /\
         chunked.fp_final == dense.fp_final /\
         chunked.fwd_map == dense.fwd_map))
  =
  CheneyPreservation.chunked_cheney_promote_default_single_chunk_compat
    minor major fp roots

let spot_chunked_cheney_forward_normal_noalloc_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        ((~(Seq.mem addr (minor_objects minor)) \/
          cs.ccs_fwd addr <> 0UL) \/
         (Seq.mem addr (minor_objects minor) /\
          cs.ccs_fwd addr = 0UL /\
          minor_wosize minor addr = 0) \/
         (Seq.mem addr (minor_objects minor) /\
          cs.ccs_fwd addr = 0UL /\
          minor_wosize minor addr > 0 /\
          (ChunkedPromote.chunked_promote_object_with_fuel
            minor cs.ccs_major addr cs.ccs_fp
            (minor_wosize minor addr) fuel).new_addr = 0UL)))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal
             minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_normal_noalloc_preserves_chunked_alloc_shape
    minor cs addr fuel

let spot_chunked_cheney_forward_normal_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal
             minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_normal_head_split_preserves_chunked_alloc_shape
    minor cs addr fuel

let spot_chunked_cheney_forward_normal_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         minor_wosize minor addr > 0 ==>
         cs.ccs_fp <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_normal
             minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         GenInv.chunked_chain_objects_blue cs'.ccs_major cs'.ccs_fp fuel))
  =
  CheneyPreservation.chunked_cheney_forward_normal_head_split_preserves_chain_objects_blue
    minor cs addr fuel

let spot_chunked_cheney_forward_one_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         ~(is_infix_in_minor minor addr) /\
         minor_wosize minor addr > 0 ==>
           cs.ccs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2) /\
        (cs.ccs_fwd addr = 0UL /\
         is_infix_in_minor minor addr ==>
           (let parent = infix_parent minor addr in
            Seq.mem parent (minor_objects minor) /\
            cs.ccs_fwd parent = 0UL /\
            minor_wosize minor parent > 0 ==>
              cs.ccs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= minor_wosize minor parent + 2)))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_one_head_split_preserves_chunked_alloc_shape
    minor cs addr fuel

let spot_chunked_cheney_forward_one_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        (Seq.mem addr (minor_objects minor) /\
         cs.ccs_fwd addr = 0UL /\
         ~(is_infix_in_minor minor addr) /\
         minor_wosize minor addr > 0 ==>
           cs.ccs_fp <> 0UL /\
           SpecMajorAlloc.major_fl_head_wosize
             cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2) /\
        (cs.ccs_fwd addr = 0UL /\
         is_infix_in_minor minor addr ==>
           (let parent = infix_parent minor addr in
            Seq.mem parent (minor_objects minor) /\
            cs.ccs_fwd parent = 0UL /\
            minor_wosize minor parent > 0 ==>
              cs.ccs_fp <> 0UL /\
              SpecMajorAlloc.major_fl_head_wosize
                cs.ccs_major cs.ccs_fp >= minor_wosize minor parent + 2)))
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         GenInv.chunked_chain_objects_blue cs'.ccs_major cs'.ccs_fp fuel))
  =
  CheneyPreservation.chunked_cheney_forward_one_head_split_preserves_chain_objects_blue
    minor cs addr fuel

let spot_chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        CheneyPreservation.chunked_cheney_forward_one_budget_ready
          minor cs addr remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         GenInv.chunked_major_alloc_shape cs'.ccs_major cs'.ccs_fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  CheneyPreservation.chunked_cheney_forward_one_head_split_preserves_remaining_head_wosize
    minor cs addr fuel remaining

let spot_chunked_cheney_forward_roots_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (idx: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_roots_split_ready
          minor cs roots idx alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_roots_head_split_preserves_chunked_alloc_shape
    minor cs roots idx alloc_fuel

let spot_chunked_cheney_forward_roots_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (idx: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_forward_roots_split_ready
          minor cs roots idx alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_forward_roots_head_split_preserves_chain_objects_blue
    minor cs roots idx alloc_fuel

let spot_chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (idx: nat) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_roots_budget_ready
          minor cs roots idx alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_roots
             minor cs roots idx alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  CheneyPreservation.chunked_cheney_forward_roots_head_split_preserves_remaining_head_wosize
    minor cs roots idx alloc_fuel remaining

let spot_chunked_cheney_forward_roots_covers_roots_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_roots_budget_ready
          minor cs roots 0 alloc_fuel remaining)
      (ensures
        GC.Gen.CheneyBFS.fwd_covers_roots minor
          (ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots 0 alloc_fuel).ccs_fwd
          roots)
  =
  CheneyPreservation.chunked_cheney_forward_roots_covers_roots_from_budget
    minor cs roots alloc_fuel remaining

let spot_chunked_cheney_forward_fields_covers_successors_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_fields_budget_ready
          minor cs parent 0 (minor_wosize minor parent)
          alloc_fuel remaining)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent 0 (minor_wosize minor parent) alloc_fuel in
         forall (y:U64.t).
          Seq.mem y (GC.Gen.Reachability.minor_successors minor parent) /\
          minor_wosize minor y > 0 ==>
          cs'.ccs_fwd y <> 0UL))
  =
  CheneyPreservation.chunked_cheney_forward_fields_covers_successors_from_budget
    minor cs parent alloc_fuel remaining

let spot_chunked_cheney_scan_fwd_monotone
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat) (x: U64.t)
  : Lemma
      (requires cs.ccs_fwd x <> 0UL)
      (ensures
        (ChunkedCheney.chunked_cheney_scan
          minor cs scan scan_fuel alloc_fuel).ccs_fwd x <> 0UL)
  =
  CheneyPreservation.chunked_cheney_scan_fwd_monotone
    minor cs scan scan_fuel alloc_fuel x

let spot_chunked_scanned_prefix_step_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_scanned_prefix_closed minor cs scan /\
        scan < Seq.length cs.ccs_queue /\
        (let parent = Seq.index cs.ccs_queue scan in
         CheneyPreservation.chunked_cheney_forward_fields_budget_ready
          minor cs parent 0 (minor_wosize minor parent)
          alloc_fuel remaining))
      (ensures
        (let parent = Seq.index cs.ccs_queue scan in
         let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent 0 (minor_wosize minor parent) alloc_fuel in
         CheneyPreservation.chunked_scanned_prefix_closed
          minor cs' (scan + 1)))
  =
  CheneyPreservation.chunked_scanned_prefix_step_from_budget
    minor cs scan alloc_fuel remaining

let spot_chunked_cheney_scan_scanned_prefix_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_scanned_prefix_closed minor cs scan /\
        CheneyPreservation.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining)
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         CheneyPreservation.chunked_scanned_prefix_closed minor cs'
          (CheneyPreservation.chunked_cheney_scan_end_index
            minor cs scan scan_fuel alloc_fuel)))
  =
  CheneyPreservation.chunked_cheney_scan_scanned_prefix_from_budget
    minor cs scan scan_fuel alloc_fuel remaining

let spot_chunked_cheney_forward_roots_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (roots: Seq.seq U64.t) (idx alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        CheneyPreservation.chunked_fwd_in_queue minor cs)
      (ensures
        CheneyPreservation.chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_forward_roots
            minor cs roots idx alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_forward_roots_preserves_fwd_in_queue
    minor cs roots idx alloc_fuel

let spot_chunked_cheney_scan_preserves_fwd_in_queue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        CheneyPreservation.chunked_fwd_in_queue minor cs)
      (ensures
        CheneyPreservation.chunked_fwd_in_queue minor
          (ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_scan_preserves_fwd_in_queue
    minor cs scan scan_fuel alloc_fuel

let spot_chunked_cheney_scan_fwd_closed_from_budget
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_fwd_in_queue minor cs /\
        CheneyPreservation.chunked_scanned_prefix_closed minor cs scan /\
        CheneyPreservation.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining /\
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         CheneyPreservation.chunked_cheney_scan_end_index
          minor cs scan scan_fuel alloc_fuel >= Seq.length cs'.ccs_queue))
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_scan
            minor cs scan scan_fuel alloc_fuel in
         GC.Gen.CheneyBFS.fwd_closed minor cs'.ccs_fwd))
  =
  CheneyPreservation.chunked_cheney_scan_fwd_closed_from_budget
    minor cs scan scan_fuel alloc_fuel remaining

let spot_chunked_cheney_scan_end_exhausted_or_fuel
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan scan_fuel alloc_fuel: nat)
  : Lemma
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         let end_idx =
           CheneyPreservation.chunked_cheney_scan_end_index
             minor cs scan scan_fuel alloc_fuel in
         end_idx >= Seq.length cs'.ccs_queue \/
         end_idx == scan + scan_fuel))
  =
  CheneyPreservation.chunked_cheney_scan_end_exhausted_or_fuel
    minor cs scan scan_fuel alloc_fuel

let spot_chunked_cheney_promote_scan_exhaustion
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires minor_wf minor)
      (ensures
        (let cs0 : ChunkedCheney.chunked_cheney_state =
          { ccs_major = major; ccs_fp = fp;
            ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
         let cs1 =
          ChunkedCheney.chunked_cheney_forward_roots
            minor cs0 roots 0 alloc_fuel in
         let cs2 =
          ChunkedCheney.chunked_cheney_scan
            minor cs1 0 (cheney_fuel minor) alloc_fuel in
         CheneyPreservation.chunked_cheney_scan_end_index
          minor cs1 0 (cheney_fuel minor) alloc_fuel >=
         Seq.length cs2.ccs_queue))
  =
  CheneyPreservation.chunked_cheney_promote_scan_exhaustion
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_no_oom_from_budget_and_scan_exhaustion
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize major fp >=
          PromotionDemand.minor_promotion_demand minor + 1 /\
        (let cs0 : ChunkedCheney.chunked_cheney_state =
          { ccs_major = major; ccs_fp = fp;
            ccs_fwd = empty_forwarding; ccs_queue = Seq.empty } in
         let cs1 =
          ChunkedCheney.chunked_cheney_forward_roots
            minor cs0 roots 0 alloc_fuel in
         let cs2 =
          ChunkedCheney.chunked_cheney_scan
            minor cs1 0 (cheney_fuel minor) alloc_fuel in
         CheneyPreservation.chunked_cheney_scan_end_index
          minor cs1 0 (cheney_fuel minor) alloc_fuel >=
         Seq.length cs2.ccs_queue))
      (ensures
        CheneyPreservation.chunked_cheney_no_oom
          minor major fp roots alloc_fuel)
  =
  CheneyPreservation.chunked_cheney_promote_no_oom_from_budget_and_scan_exhaustion
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_no_oom_from_budget
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize major fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyPreservation.chunked_cheney_no_oom
          minor major fp roots alloc_fuel)
  =
  CheneyPreservation.chunked_cheney_promote_no_oom_from_budget
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_forwards_reachable_from_budget
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize major fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         forall (x:U64.t).
          Seq.mem x (minor_reachable minor roots) /\
          minor_wosize minor x > 0 ==>
          res.fwd_map x <> 0UL))
  =
  CheneyPreservation.chunked_cheney_promote_forwards_reachable_from_budget
    minor major fp roots alloc_fuel

let spot_chunked_cheney_forward_fields_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_fields_split_ready
          minor cs parent idx wosize alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true))
  =
  CheneyPreservation.chunked_cheney_forward_fields_head_split_preserves_chunked_alloc_shape
    minor cs parent idx wosize alloc_fuel

let spot_chunked_cheney_forward_fields_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_forward_fields_split_ready
          minor cs parent idx wosize alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_forward_fields_head_split_preserves_chain_objects_blue
    minor cs parent idx wosize alloc_fuel

let spot_chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (alloc_fuel: nat)
  (remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_forward_fields_budget_ready
          minor cs parent idx wosize alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_forward_fields
             minor cs parent idx wosize alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  CheneyPreservation.chunked_cheney_forward_fields_head_split_preserves_remaining_head_wosize
    minor cs parent idx wosize alloc_fuel remaining

let spot_chunked_cheney_scan_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_scan_split_ready
          minor cs scan scan_fuel alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true))
  =
  CheneyPreservation.chunked_cheney_scan_head_split_preserves_chunked_alloc_shape
    minor cs scan scan_fuel alloc_fuel

let spot_chunked_cheney_scan_head_split_preserves_chain_objects_blue
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_scan_split_ready
          minor cs scan scan_fuel alloc_fuel)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           cs'.ccs_major cs'.ccs_fp alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_scan_head_split_preserves_chain_objects_blue
    minor cs scan scan_fuel alloc_fuel

let spot_chunked_cheney_scan_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (scan: nat) (scan_fuel: nat) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_scan_budget_ready
          minor cs scan scan_fuel alloc_fuel remaining)
      (ensures
        (let cs' =
           ChunkedCheney.chunked_cheney_scan
             minor cs scan scan_fuel alloc_fuel in
         GenInv.chunked_major_alloc_shape
           cs'.ccs_major cs'.ccs_fp alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           cs'.ccs_major cs'.ccs_fp alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           cs'.ccs_major cs'.ccs_fp >= remaining))
  =
  CheneyPreservation.chunked_cheney_scan_head_split_preserves_remaining_head_wosize
    minor cs scan scan_fuel alloc_fuel remaining

let spot_chunked_cheney_promote_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final alloc_fuel = true))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_chunked_alloc_shape
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_head_split_preserves_old_major_objects
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         forall (src: obj_addr).
          Seq.mem src (MH.major_objects major) ==>
          Seq.mem src (MH.major_objects res.major_final)))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_old_major_objects
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_head_split_preserves_old_non_blue_header
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getWosize hdr) >= 1)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final (hd_address src) ==
           Some hdr))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_old_non_blue_header
    minor major fp roots alloc_fuel src hdr

let spot_chunked_cheney_promote_head_split_preserves_old_non_blue_field
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (src: obj_addr) (hdr: U64.t)
  (j: nat) (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel /\
        Seq.mem src (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         MH.read_word_in_major res.major_final field_addr == Some old))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_old_non_blue_field
    minor major fp roots alloc_fuel src hdr j field_addr old

let spot_chunked_cheney_promote_head_split_preserves_chain_objects_blue
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_promote_split_ready
          minor major fp roots alloc_fuel)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final alloc_fuel = true /\
         GenInv.chunked_chain_objects_blue
           res.major_final res.fp_final alloc_fuel))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_chain_objects_blue
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (remaining: nat)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining)
      (ensures
        (let res =
           ChunkedCheney.chunked_cheney_promote
             minor major fp roots alloc_fuel in
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final alloc_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final alloc_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           res.major_final res.fp_final >= remaining))
  =
  CheneyPreservation.chunked_cheney_promote_head_split_preserves_remaining_head_wosize
    minor major fp roots alloc_fuel remaining

let spot_chunked_cheney_promote_fwd_target_fields_match
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (remaining: nat)
  (x: U64.t) (j: nat) (field_addr: hp_addr)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel remaining /\
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         res.fwd_map x <> 0UL /\
         Seq.mem x (minor_objects minor) /\
         ~(is_infix_in_minor minor x) /\
         j < minor_wosize minor x /\
         U64.v field_addr == U64.v (res.fwd_map x) + j * U64.v mword))
      (ensures
        (let res =
          ChunkedCheney.chunked_cheney_promote
            minor major fp roots alloc_fuel in
         U64.v (res.fwd_map x) >= U64.v mword /\
         U64.v (res.fwd_map x) < heap_size /\
         U64.v (res.fwd_map x) % U64.v mword == 0 /\
         (let target : obj_addr = res.fwd_map x in
          Seq.mem target (MH.major_objects res.major_final) /\
          (match MH.read_word_in_major res.major_final (hd_address target) with
           | Some hdr ->
             Obj.getColor hdr <> GC.Lib.Header.Blue /\
             U64.v (Obj.getTag hdr) == minor_tag minor x /\
             j < U64.v (Obj.getWosize hdr) /\
             CG.chunked_major_field_slot target j == Some field_addr /\
             MH.read_word_in_major res.major_final field_addr ==
              Some (minor_read_field minor x j)
           | None -> False))))
  =
  CheneyPreservation.chunked_cheney_promote_fwd_target_fields_match
    minor major fp roots alloc_fuel remaining x j field_addr

let spot_chunked_cheney_promote_budget_ready_from_minor_demand
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize major fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyPreservation.chunked_cheney_promote_budget_ready
          minor major fp roots alloc_fuel 1)
  =
  CheneyPreservation.chunked_cheney_promote_budget_ready_from_minor_demand
    minor major fp roots alloc_fuel

let spot_chunked_cheney_promote_after_minor_promotion_head_preflight
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let res =
           ChunkedCheney.chunked_cheney_promote
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         GenInv.chunked_collection_heap_shape
           minor r.capacity_major_out r.capacity_fp_out
           r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_head_wosize
           r.capacity_major_out r.capacity_fp_out >= needed /\
         SpecMajorAlloc.major_fl_chain_terminates
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         CheneyPreservation.chunked_fwd_targets_above_minor res.fwd_map /\
         CheneyPreservation.chunked_fwd_targets_valid_addr res.fwd_map /\
         CheneyPreservation.chunked_fwd_noninfix_targets_in_major
           minor res.fwd_map res.major_final /\
         (forall (x:U64.t).
           Seq.mem x (minor_reachable minor roots) /\
           minor_wosize minor x > 0 ==>
           res.fwd_map x <> 0UL) /\
         (forall (src: obj_addr).
           Seq.mem src (MH.major_objects major) ==>
           Seq.mem src (MH.major_objects res.major_final)) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
           Seq.mem src (MH.major_objects major) /\
           MH.read_word_in_major major (hd_address src) == Some hdr /\
           Obj.getColor hdr <> GC.Lib.Header.Blue /\
           U64.v (Obj.getWosize hdr) >= 1 ==>
           MH.read_word_in_major res.major_final (hd_address src) ==
             Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
           Seq.mem src (MH.major_objects major) /\
           MH.read_word_in_major major (hd_address src) == Some hdr /\
           Obj.getColor hdr <> GC.Lib.Header.Blue /\
           j < U64.v (Obj.getWosize hdr) /\
           U64.v field_addr == U64.v src + j * U64.v mword /\
           MH.read_word_in_major major field_addr == Some old ==>
           MH.read_word_in_major res.major_final field_addr == Some old) /\
         GenInv.chunked_major_alloc_shape
           res.major_final res.fp_final r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_final res.fp_final r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           res.major_final res.fp_final r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_head_wosize
           res.major_final res.fp_final >= 1))
  =
  CheneyPreservation.chunked_cheney_promote_after_minor_promotion_head_preflight
    minor major fp roots alloc_fuel fresh

let spot_chunked_minor_preflight_value_policy_all_object_expansion_safe
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh)
      (ensures
        (SpecMajorAlloc.major_fl_head_wosize major fp <
         PromotionDemand.minor_promotion_demand minor + 1 ==>
         CG.chunked_all_major_object_expansion_safe
           major fresh (MH.major_objects major) 0))
  =
  CheneyGraphReadiness.chunked_minor_preflight_value_policy_all_object_expansion_safe
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_promote_after_preflight_value_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh)
      (ensures
        CheneyGraphReadiness.chunked_cheney_promote_after_minor_promotion_head_preflight_post
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_promote_after_minor_promotion_head_preflight_from_preflight_value_policy
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_collect_after_preflight_value_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh)
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_from_preflight_value_policy
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_collect_then_major_gc_live_subgraph_from_preflight_value_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (major_roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         GenInv.chunked_collection_heap_shape
           collect.cmc_minor collect.cmc_major collect.cmc_fp
           r.capacity_fuel_out /\
         GenMajorGCBridge.chunked_major_roots_nonblue
           collect.cmc_major major_roots /\
         GenMajorGCBridge.chunked_major_edge_gen_field_witness
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_field_targets_non_infix
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_policy
           collect.cmc_major major_roots cap mark_fuel))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor major fp roots alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         let (major_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots
              collect.cmc_major major_roots)
            cap mark_fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           collect.cmc_major major_final
           (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
             collect.cmc_major major_roots)))
  =
  CheneyGraphReadiness.chunked_cheney_collect_then_major_gc_live_subgraph_from_preflight_value_policy
    minor major fp roots alloc_fuel fresh major_roots cap mark_fuel

let spot_chunked_cheney_collect_then_major_gc_live_subgraph_from_target_membership_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (major_roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         GenInv.chunked_collection_heap_shape
           collect.cmc_minor collect.cmc_major collect.cmc_fp
           r.capacity_fuel_out /\
         GenMajorGCBridge.chunked_major_roots_nonblue
           collect.cmc_major major_roots /\
         GenMajorGCBridge.chunked_major_edge_gen_field_witness
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_field_targets_non_infix
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_target_membership_policy
           collect.cmc_major major_roots cap mark_fuel))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor major fp roots alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         let (major_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots
              collect.cmc_major major_roots)
            cap mark_fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           collect.cmc_major major_final
           (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
             collect.cmc_major major_roots)))
  =
  CheneyGraphReadiness.chunked_cheney_collect_then_major_gc_live_subgraph_from_target_membership_policy
    minor major fp roots alloc_fuel fresh major_roots cap mark_fuel

let spot_chunked_cheney_collect_then_major_gc_live_subgraph_from_raw_target_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (major_roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         GenInv.chunked_collection_heap_shape
           collect.cmc_minor collect.cmc_major collect.cmc_fp
           r.capacity_fuel_out /\
         GenMajorGCBridge.chunked_major_roots_nonblue
           collect.cmc_major major_roots /\
         GenMajorGCBridge.chunked_major_edge_gen_field_witness
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_field_targets_non_infix
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_raw_target_policy
           collect.cmc_major major_roots cap mark_fuel))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor major fp roots alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         let (major_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots
              collect.cmc_major major_roots)
            cap mark_fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           collect.cmc_major major_final
           (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
             collect.cmc_major major_roots)))
  =
  CheneyGraphReadiness.chunked_cheney_collect_then_major_gc_live_subgraph_from_raw_target_policy
    minor major fp roots alloc_fuel fresh major_roots cap mark_fuel

let spot_chunked_cheney_collect_then_major_gc_live_subgraph_from_static_raw_target_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (major_roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         GenInv.chunked_collection_heap_shape
           collect.cmc_minor collect.cmc_major collect.cmc_fp
           r.capacity_fuel_out /\
         GenMajorGCBridge.chunked_major_roots_nonblue
           collect.cmc_major major_roots /\
         GenMajorGCBridge.chunked_major_edge_gen_field_witness
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_field_targets_non_infix
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_gc_bounded_after_gray_roots_static_raw_target_policy
           collect.cmc_major major_roots cap mark_fuel))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor major fp roots alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         let (major_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots
              collect.cmc_major major_roots)
            cap mark_fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           collect.cmc_major major_final
           (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
             collect.cmc_major major_roots)))
  =
  CheneyGraphReadiness.chunked_cheney_collect_then_major_gc_live_subgraph_from_static_raw_target_policy
    minor major fp roots alloc_fuel fresh major_roots cap mark_fuel

let spot_chunked_cheney_collect_then_major_gc_live_subgraph_from_pre_gray_static_raw_target_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (major_roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         GenInv.chunked_collection_heap_shape
           collect.cmc_minor collect.cmc_major collect.cmc_fp
           r.capacity_fuel_out /\
         GenMajorGCBridge.chunked_major_roots_nonblue
           collect.cmc_major major_roots /\
         GenMajorGCBridge.chunked_major_edge_gen_field_witness
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_field_targets_non_infix
           collect.cmc_major /\
         ChunkedMarkBoundedTargetMembership.chunked_scanned_raw_targets_in_major
           collect.cmc_major /\
         Seq.length (MH.major_objects collect.cmc_major) <= cap /\
         mark_fuel > 0 /\
         mark_fuel >= Seq.length (MH.major_objects collect.cmc_major)))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor major fp roots alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         let (major_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots
              collect.cmc_major major_roots)
            cap mark_fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           collect.cmc_major major_final
           (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
             collect.cmc_major major_roots)))
  =
  CheneyGraphReadiness.chunked_cheney_collect_then_major_gc_live_subgraph_from_pre_gray_static_raw_target_policy
    minor major fp roots alloc_fuel fresh major_roots cap mark_fuel

let spot_chunked_cheney_collect_then_major_gc_live_subgraph_from_raw_field_target_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (major_roots: Seq.seq obj_addr)
  (cap: nat{cap > 0})
  (mark_fuel: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp roots fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         GenInv.chunked_collection_heap_shape
           collect.cmc_minor collect.cmc_major collect.cmc_fp
           r.capacity_fuel_out /\
         GenMajorGCBridge.chunked_major_roots_nonblue
           collect.cmc_major major_roots /\
         GenMajorGCBridge.chunked_major_edge_gen_field_witness
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_field_targets_non_infix
           collect.cmc_major /\
         GenMajorGCBridge.chunked_major_raw_field_targets_in_major
           collect.cmc_major /\
         (forall (target: obj_addr).
           Seq.mem target (MH.major_objects collect.cmc_major) ==>
           Fields.is_pointer_field target) /\
         Seq.length (MH.major_objects collect.cmc_major) <= cap /\
         mark_fuel > 0 /\
         mark_fuel >= Seq.length (MH.major_objects collect.cmc_major)))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor major fp roots alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1)
            fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         let (major_final, fp_final) =
          ChunkedMajorGC.chunked_major_gc_bounded
            (ChunkedMajorGCRoots.chunked_gray_roots
              collect.cmc_major major_roots)
            cap mark_fuel in
         ChunkedMajorGCGraph.chunked_major_live_subgraph_preserved
           collect.cmc_major major_final
           (ChunkedMajorGCCorr.chunked_major_initial_reachable_live
             collect.cmc_major major_roots)))
  =
  CheneyGraphReadiness.chunked_cheney_collect_then_major_gc_live_subgraph_from_raw_field_target_policy
    minor major fp roots alloc_fuel fresh major_roots cap mark_fuel

let spot_chunked_alloc_head_split_alloc_header_wosize
  (mh: MH.major_heap) (fp: U64.t)
  (wosize: nat{wosize > 0 /\
                wosize < pow2 54 /\
                FStar.UInt.size wosize 64})
  (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let r =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let dst : obj_addr = fp in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         MH.read_word_in_major r.major_alloc_out (hd_address dst) ==
           Some (SpecAlloc.make_header (U64.uint_to_t wosize)
                   SpecAlloc.white_bits 0UL) /\
         U64.v (Obj.getWosize
           (SpecAlloc.make_header (U64.uint_to_t wosize)
             SpecAlloc.white_bits 0UL)) == wosize))
  =
  CheneyPreservation.chunked_alloc_head_split_alloc_header_wosize
    mh fp wosize fuel

let spot_chunked_promote_head_split_padding_noop
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let alloc_res =
           SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
         let copied =
           ChunkedPromote.chunked_copy_fields
             minor alloc_res.major_alloc_out obj fp 0 wosize in
         ChunkedPromote.chunked_zero_promote_padding copied fp wosize ==
           copied))
  =
  CheneyPreservation.chunked_promote_head_split_padding_noop
    minor mh obj fp wosize fuel

let spot_chunked_promote_object_head_split_preserves_chunked_alloc_shape
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_out res.fp_out fuel = true /\
         (let alloc_res =
            SpecMajorAlloc.major_alloc_spec_with_fuel mh fp wosize fuel in
          MH.major_objects res.major_out ==
            MH.major_objects alloc_res.major_alloc_out /\
          (forall (src:obj_addr).
            Seq.mem src (MH.major_objects mh) ==>
            Seq.mem src (MH.major_objects res.major_out)) /\
          (forall (src:obj_addr). forall (hdr:U64.t).
            Seq.mem src (MH.major_objects mh) /\
            src <> fp /\
            MH.read_word_in_major mh (hd_address src) == Some hdr /\
            U64.v (Obj.getWosize hdr) >= 1 ==>
            MH.read_word_in_major res.major_out (hd_address src) ==
              Some hdr) /\
          Seq.mem (fp <: obj_addr)
            (MH.major_objects alloc_res.major_alloc_out) /\
          Seq.mem (fp <: obj_addr) (MH.major_objects res.major_out))))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_chunked_alloc_shape
    minor mh obj fp wosize fuel

let spot_chunked_promote_object_head_split_preserves_chain_objects_blue
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_out res.fp_out fuel = true /\
         GenInv.chunked_chain_objects_blue res.major_out res.fp_out fuel))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_chain_objects_blue
    minor mh obj fp wosize fuel

let spot_chunked_promote_object_head_split_preserves_old_non_blue_header
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (src: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2 /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getWosize hdr) >= 1)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         MH.read_word_in_major res.major_out (hd_address src) == Some hdr))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_old_non_blue_header
    minor mh obj fp wosize fuel src hdr

let spot_chunked_promote_object_head_split_preserves_old_non_blue_field
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (src: obj_addr) (hdr: U64.t) (j: nat) (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        GenInv.chunked_chain_objects_blue mh fp fuel /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >= wosize + 2 /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        MH.read_word_in_major mh field_addr == Some old)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         MH.read_word_in_major res.major_out field_addr == Some old))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_old_non_blue_field
    minor mh obj fp wosize fuel src hdr j field_addr old

let spot_chunked_promote_object_head_split_preserves_remaining_head_wosize
  (minor: minor_state) (mh: MH.major_heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (fuel: nat)
  (remaining: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        remaining > 0 /\
        GenInv.chunked_major_alloc_shape mh fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates mh fp fuel = true /\
        SpecMajorAlloc.major_fl_head_wosize mh fp >=
          wosize + 1 + remaining)
      (ensures
        (let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor mh obj fp wosize fuel in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape res.major_out res.fp_out fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           res.major_out res.fp_out fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           res.major_out res.fp_out >= remaining))
  =
  CheneyPreservation.chunked_promote_object_head_split_preserves_remaining_head_wosize
    minor mh obj fp wosize fuel remaining

let spot_alloc_spec_head_split_alloc_wosize_single_chunk
  (major: heap) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >= wosize + 2)
      (ensures
        (let r = SpecAlloc.alloc_spec major fp wosize in
         r.obj_out == fp /\
         r.fp_out <> 0UL /\
         U64.v (Obj.wosize_of_object (fp <: obj_addr) r.heap_out) == wosize /\
         U64.v fp + (wosize - 1) * U64.v mword + U64.v mword <= heap_size))
  =
  CheneyPreservation.alloc_spec_head_split_alloc_wosize_single_chunk
    major fp wosize

let spot_promote_object_head_split_padding_noop_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 0 /\
                fp <> 0UL /\
                SpecMajorAlloc.major_fl_valid
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_above_zero
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_blocks_fit
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >= wosize + 2)
      (ensures
        (let r = SpecAlloc.alloc_spec major fp wosize in
         let copied = WriteBody.copy_fields minor r.heap_out obj fp 0 wosize in
         zero_promote_padding copied (fp <: obj_addr) wosize == copied))
  =
  CheneyPreservation.promote_object_head_split_padding_noop_single_chunk
    minor major obj fp wosize

let spot_promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >= wosize + 2)
      (ensures
        (let res = promote_object minor major obj fp wosize in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_out) res.fp_out
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_out) res.fp_out
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.promote_object_head_split_preserves_chunked_alloc_shape_single_chunk
    minor major obj fp wosize

let spot_promote_object_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0}) (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                remaining > 0 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                wosize + 1 + remaining)
      (ensures
        (let res = promote_object minor major obj fp wosize in
         res.new_addr == fp /\
         res.fp_out <> 0UL /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap res.major_out) res.fp_out >=
         remaining))
  =
  CheneyPreservation.promote_object_head_split_preserves_remaining_head_wosize_single_chunk
    minor major obj fp wosize remaining

let spot_cheney_forward_one_split_ready_from_minor_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires minor_wf minor /\
                cs.cs_fp <> 0UL /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyPreservation.cheney_forward_one_split_ready_single_chunk
          minor cs addr)
  =
  CheneyPreservation.cheney_forward_one_split_ready_from_minor_demand_single_chunk
    minor cs addr

let spot_cheney_forward_one_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                (Seq.mem addr (minor_objects minor) /\
                 cs.cs_fwd addr = 0UL /\
                 ~(is_infix_in_minor minor addr) /\
                 minor_wosize minor addr > 0 ==>
                   cs.cs_fp <> 0UL /\
                   SpecMajorAlloc.major_fl_head_wosize
                     (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                   minor_wosize minor addr + 2) /\
                (cs.cs_fwd addr = 0UL /\
                 is_infix_in_minor minor addr ==>
                   (let parent = infix_parent minor addr in
                    Seq.mem parent (minor_objects minor) /\
                    cs.cs_fwd parent = 0UL /\
                    minor_wosize minor parent > 0 ==>
                      cs.cs_fp <> 0UL /\
                      SpecMajorAlloc.major_fl_head_wosize
                        (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                      minor_wosize minor parent + 2)))
      (ensures
        (let cs' = cheney_forward_one minor cs addr in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_forward_one_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs addr

let spot_cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_one_budget_ready_single_chunk
                  minor cs addr remaining)
      (ensures
        (let cs' = cheney_forward_one minor cs addr in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         remaining))
  =
  CheneyPreservation.cheney_forward_one_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs addr remaining

let spot_cheney_forward_one_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (addr: U64.t)
  (remaining: nat)
  : Lemma
      (requires remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                CheneyPreservation.cheney_forward_one_split_demand
                  minor cs addr + remaining)
      (ensures
        CheneyPreservation.cheney_forward_one_budget_ready_single_chunk
          minor cs addr remaining)
  =
  CheneyPreservation.cheney_forward_one_budget_ready_from_split_demand_single_chunk
    minor cs addr remaining

let spot_cheney_forward_roots_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: Seq.seq U64.t) (idx: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_roots_split_ready_single_chunk
                  minor cs roots idx)
      (ensures
        (let cs' = cheney_forward_roots minor cs roots idx in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_forward_roots_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs roots idx

let spot_cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: Seq.seq U64.t) (idx: nat)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_roots_budget_ready_single_chunk
                  minor cs roots idx remaining)
      (ensures
        (let cs' = cheney_forward_roots minor cs roots idx in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         remaining))
  =
  CheneyPreservation.cheney_forward_roots_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs roots idx remaining

let spot_cheney_forward_roots_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (roots: Seq.seq U64.t) (idx: nat)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                CheneyPreservation.cheney_forward_roots_split_demand
                  minor cs roots idx + remaining)
      (ensures
        CheneyPreservation.cheney_forward_roots_budget_ready_single_chunk
          minor cs roots idx remaining)
  =
  CheneyPreservation.cheney_forward_roots_budget_ready_from_split_demand_single_chunk
    minor cs roots idx remaining

let spot_cheney_forward_fields_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_fields_split_ready_single_chunk
                  minor cs parent idx wosize)
      (ensures
        (let cs' = cheney_forward_fields minor cs parent idx wosize in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_forward_fields_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs parent idx wosize

let spot_cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_forward_fields_budget_ready_single_chunk
                  minor cs parent idx wosize remaining)
      (ensures
        (let cs' = cheney_forward_fields minor cs parent idx wosize in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         remaining))
  =
  CheneyPreservation.cheney_forward_fields_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs parent idx wosize remaining

let spot_cheney_forward_fields_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state)
  (parent: U64.t) (idx: nat) (wosize: nat) (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                CheneyPreservation.cheney_forward_fields_split_demand
                  minor cs parent idx wosize + remaining)
      (ensures
        CheneyPreservation.cheney_forward_fields_budget_ready_single_chunk
          minor cs parent idx wosize remaining)
  =
  CheneyPreservation.cheney_forward_fields_budget_ready_from_split_demand_single_chunk
    minor cs parent idx wosize remaining

let spot_cheney_scan_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan fuel: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_scan_split_ready_single_chunk
                  minor cs scan fuel)
      (ensures
        (let cs' = cheney_scan minor cs scan fuel in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_scan_head_split_preserves_chunked_alloc_shape_single_chunk
    minor cs scan fuel

let spot_cheney_scan_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan fuel remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_scan_budget_ready_single_chunk
                  minor cs scan fuel remaining)
      (ensures
        (let cs' = cheney_scan minor cs scan fuel in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap cs'.cs_major) cs'.cs_fp >=
         remaining))
  =
  CheneyPreservation.cheney_scan_head_split_preserves_remaining_head_wosize_single_chunk
    minor cs scan fuel remaining

let spot_cheney_scan_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (cs: cheney_state) (scan fuel remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp
                  SpecAlloc.alloc_search_fuel = true /\
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap cs.cs_major) cs.cs_fp >=
                CheneyPreservation.cheney_scan_split_demand
                  minor cs scan fuel + remaining)
      (ensures
        CheneyPreservation.cheney_scan_budget_ready_single_chunk
          minor cs scan fuel remaining)
  =
  CheneyPreservation.cheney_scan_budget_ready_from_split_demand_single_chunk
    minor cs scan fuel remaining

let spot_cheney_promote_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_promote_split_ready_single_chunk
                  minor major fp roots)
      (ensures
        (let res = cheney_promote minor major fp roots in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true))
  =
  CheneyPreservation.cheney_promote_head_split_preserves_chunked_alloc_shape_single_chunk
    minor major fp roots

let spot_cheney_promote_head_split_preserves_remaining_head_wosize_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                CheneyPreservation.cheney_promote_budget_ready_single_chunk
                  minor major fp roots remaining)
      (ensures
        (let res = cheney_promote minor major fp roots in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAlloc.major_fl_head_wosize
           (MH.single_chunk_major_heap res.major_final) res.fp_final >=
         remaining))
  =
  CheneyPreservation.cheney_promote_head_split_preserves_remaining_head_wosize_single_chunk
    minor major fp roots remaining

let spot_cheney_promote_budget_ready_from_split_demand_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (remaining: nat)
  : Lemma
      (requires SpecAlloc.alloc_search_fuel > 1 /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                remaining > 0 /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                CheneyPreservation.cheney_promote_split_demand
                  minor major fp roots + remaining)
      (ensures
        CheneyPreservation.cheney_promote_budget_ready_single_chunk
          minor major fp roots remaining)
  =
  CheneyPreservation.cheney_promote_budget_ready_from_split_demand_single_chunk
    minor major fp roots remaining

let spot_cheney_promote_budget_ready_from_minor_demand_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyPreservation.cheney_promote_budget_ready_single_chunk
          minor major fp roots 1)
  =
  CheneyPreservation.cheney_promote_budget_ready_from_minor_demand_single_chunk
    minor major fp roots

let spot_cheney_promote_budgeted_head_split_preserves_chunked_alloc_shape_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_major_alloc_shape
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let res = cheney_promote minor major fp roots in
         let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         let alloc_trace =
           SpecMajorAllocMultiAlloc.dense_alloc_list_default_spec
             major fp requests in
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           alloc_trace.dense_list_objs_out))
  =
  CheneyPreservation.cheney_promote_budgeted_head_split_preserves_chunked_alloc_shape_single_chunk
    minor major fp roots

let spot_cheney_promote_after_minor_promotion_head_preflight_no_expansion_single_chunk
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires minor_wf minor /\
                SpecAlloc.alloc_search_fuel > 1 /\
                fp <> 0UL /\
                GenInv.chunked_collection_heap_shape
                  minor (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel /\
                SpecMajorAlloc.major_fl_chain_terminates
                  (MH.single_chunk_major_heap major) fp
                  SpecAlloc.alloc_search_fuel = true /\
                SpecMajorAlloc.major_fl_head_wosize
                  (MH.single_chunk_major_heap major) fp >=
                  PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             (MH.single_chunk_major_heap major) fp
             SpecAlloc.alloc_search_fuel needed fresh in
         let res = cheney_promote minor major fp roots in
         let requests =
           CheneyPreservation.cheney_forwarded_minor_requests
             minor major fp roots in
         let alloc_trace =
           SpecMajorAllocMultiAlloc.dense_alloc_list_default_spec
             major fp requests in
         r.capacity_major_out == MH.single_chunk_major_heap major /\
         r.capacity_fp_out == fp /\
         r.capacity_fuel_out == SpecAlloc.alloc_search_fuel /\
         GenInv.chunked_collection_heap_shape
           minor r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out = true /\
         GenInv.chunked_major_alloc_shape
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel /\
         SpecMajorAlloc.major_fl_chain_terminates
           (MH.single_chunk_major_heap res.major_final) res.fp_final
           SpecAlloc.alloc_search_fuel = true /\
         SpecMajorAllocMultiAlloc.allocated_objects_nonzero
           alloc_trace.dense_list_objs_out))
  =
  CheneyPreservation.cheney_promote_after_minor_promotion_head_preflight_no_expansion_single_chunk
    minor major fp roots fresh

let spot_chunked_is_blue_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures
        GenInv.chunked_is_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        GenInv.chunked_is_blue mh obj)
  = GenInv.chunked_is_blue_preserved_by_expansion mh fresh fp obj

let spot_chunked_minor_major_fields_no_blue_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_minor_major_fields_no_blue ms mh /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        GenInv.chunked_minor_major_fields_no_blue ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_minor_major_fields_no_blue_preserved_by_expansion
      ms mh fresh fp

let spot_chunked_minor_major_fields_no_blue_ensure_capacity
  (ms: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_minor_major_fields_no_blue ms mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        GenInv.chunked_minor_major_fields_no_blue ms
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_minor_major_fields_no_blue_ensure_capacity
      ms mh fp fuel needed fresh

let spot_chunked_is_black_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                Seq.mem obj (MH.major_objects mh))
      (ensures
        GenInv.chunked_is_black
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        GenInv.chunked_is_black mh obj)
  = GenInv.chunked_is_black_preserved_by_expansion mh fresh fp obj

let spot_chunked_no_black_objects_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_no_black_objects mh /\
                MH.chunk_disjoint_from_all fresh mh)
      (ensures
        GenInv.chunked_no_black_objects
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_no_black_objects_preserved_by_expansion mh fresh fp

let spot_chunked_no_black_objects_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_no_black_objects mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh))
      (ensures
        GenInv.chunked_no_black_objects
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_no_black_objects_ensure_capacity mh fp fuel needed fresh

let spot_chunked_no_scan_invariant_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_no_scan_invariant mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_no_scan_invariant
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_no_scan_invariant_preserved_by_expansion mh fresh fp

let spot_chunked_no_scan_invariant_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_no_scan_invariant mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_no_scan_invariant
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_no_scan_invariant_ensure_capacity mh fp fuel needed fresh

let spot_chunked_no_pointer_to_blue_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_no_pointer_to_blue mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_no_pointer_to_blue_preserved_by_expansion mh fresh fp

let spot_chunked_no_pointer_to_blue_ensure_capacity
  (mh: MH.major_heap) (fp: obj_addr) (fuel needed: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_no_pointer_to_blue mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_no_pointer_to_blue
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_no_pointer_to_blue_ensure_capacity mh fp fuel needed fresh

let spot_chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires GenInv.chunked_major_minor_fields_no_infix_targets ms mh /\
                MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  = GenInv.chunked_major_minor_fields_no_infix_targets_preserved_by_expansion
      ms mh fresh fp

let spot_chunked_major_minor_fields_no_infix_targets_ensure_capacity
  (ms: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_major_minor_fields_no_infix_targets ms mh /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures
        GenInv.chunked_major_minor_fields_no_infix_targets ms
          (SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh).capacity_major_out)
  = GenInv.chunked_major_minor_fields_no_infix_targets_ensure_capacity
      ms mh fp fuel needed fresh

let spot_chunked_collection_heap_shape_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: obj_addr) (fuel: nat)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape ms mh fp fuel /\
                MH.chunk_disjoint_from_all fresh mh /\
                fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                U64.v fresh.base >= U64.v zero_addr /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures (
        let r = SpecMajorAlloc.expand_major_heap mh fresh fp in
        GenInv.chunked_collection_heap_shape ms r.major_out r.fp_out
          (fuel + 1)))
  = GenInv.chunked_collection_heap_shape_preserved_by_expansion
      ms mh fresh fp fuel

let spot_chunked_collection_heap_shape_ensure_capacity
  (ms: minor_state) (mh: MH.major_heap)
  (fp: obj_addr) (fuel needed: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape ms mh fp fuel /\
                (SpecMajorAlloc.major_fl_capacity mh fp fuel < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh +
                   SpecMajorAlloc.major_fl_capacity mh fp fuel >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_capacity_spec
            mh fp fuel needed fresh in
        GenInv.chunked_collection_heap_shape
          ms r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_capacity
          r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out >= needed))
  = GenInv.chunked_collection_heap_shape_ensure_capacity
      ms mh fp fuel needed fresh

let spot_chunked_collection_heap_shape_ensure_head_capacity
  (ms: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires GenInv.chunked_collection_heap_shape ms mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp < needed ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        GenInv.chunked_collection_heap_shape
          ms r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity
      ms mh fp fuel needed fresh

let spot_chunked_collection_heap_shape_ensure_head_capacity_alloc_no_oom
  (ms: minor_state) (mh: MH.major_heap)
  (fp: U64.t) (fuel: nat) (requested_wz: nat)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires fuel > 0 /\
                GenInv.chunked_collection_heap_shape ms mh fp fuel /\
                (SpecMajorAlloc.major_fl_head_wosize mh fp <
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz ==>
                 MH.chunk_disjoint_from_all fresh mh /\
                 fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
                 U64.v fresh.base >= U64.v zero_addr /\
                 SpecMajorAlloc.fresh_chunk_wosize fresh >=
                   SpecMajorAlloc.major_alloc_demand_wosize requested_wz /\
                 CG.chunked_all_major_object_expansion_safe
                   mh fresh (MH.major_objects mh) 0))
      (ensures (
        let needed = SpecMajorAlloc.major_alloc_demand_wosize requested_wz in
        let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            mh fp fuel needed fresh in
        let a =
          SpecMajorAlloc.major_alloc_spec_with_fuel
            r.capacity_major_out r.capacity_fp_out requested_wz
            r.capacity_fuel_out in
        GenInv.chunked_collection_heap_shape
          ms r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out /\
        SpecMajorAlloc.major_fl_head_wosize
          r.capacity_major_out r.capacity_fp_out >= needed /\
        a.major_obj_out == r.capacity_fp_out /\
        a.major_obj_out <> 0UL))
  = GenInv.chunked_collection_heap_shape_ensure_head_capacity_alloc_no_oom
      ms mh fp fuel requested_wz fresh

let spot_chunked_classify_minor_field (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : GTot (option CG.combined_vertex)
  = CG.chunked_classify_minor_field ms mh v

let spot_chunked_classify_major_field (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : GTot (option CG.combined_vertex)
  = CG.chunked_classify_major_field ms mh v

let spot_major_member_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (v: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        Seq.mem v
          (MH.major_objects
            (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out) ==
        Seq.mem v (MH.major_objects mh))
  = CG.chunked_major_member_preserved_by_expansion mh fresh fp v

let spot_chunked_classify_minor_field_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (v: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        spot_chunked_classify_minor_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        spot_chunked_classify_minor_field ms mh v)
  = CG.chunked_classify_minor_field_preserved_by_expansion ms mh fresh fp v

let spot_chunked_classify_major_field_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (v: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        spot_chunked_classify_major_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        spot_chunked_classify_major_field ms mh v)
  = CG.chunked_classify_major_field_preserved_by_expansion ms mh fresh fp v

let spot_chunked_minor_field_edges
  (ms: minor_state) (mh: MH.major_heap) (src: U64.t) (wz: nat) (i: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_minor_field_edges ms mh src wz i

let spot_chunked_minor_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (src: U64.t) (wz: nat) (i: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_minor_field_expansion_safe ms fresh src wz i)
      (ensures
        spot_chunked_minor_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        spot_chunked_minor_field_edges ms mh src wz i)
  = CG.chunked_minor_field_edges_preserved_by_expansion
      ms mh fresh fp src wz i

let spot_chunked_classify_minor_field_minor
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : Lemma
      (requires
        (let vo = to_minor_offset v in
         is_minor_addr vo /\ Seq.mem vo (minor_objects ms)))
      (ensures
        CG.chunked_classify_minor_field ms mh v ==
        Some (CG.MinorV (to_minor_offset v)))
  =
  CG.chunked_classify_minor_field_minor ms mh v

let spot_chunked_classify_minor_field_inv_minor
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t) (x: U64.t)
  : Lemma
      (requires CG.chunked_classify_minor_field ms mh v == Some (CG.MinorV x))
      (ensures to_minor_offset v == x /\
               is_minor_addr x /\
               Seq.mem x (minor_objects ms))
  = CG.chunked_classify_minor_field_inv_minor ms mh v x

let spot_chunked_classify_minor_field_inv_major
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t) (x: U64.t)
  : Lemma
      (requires CG.chunked_classify_minor_field ms mh v == Some (CG.MajorV x))
      (ensures v == x /\
               is_val_addr v /\
               Seq.mem (v <: obj_addr) (MH.major_objects mh) /\
               (let vo = to_minor_offset v in
                ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms))))
  = CG.chunked_classify_minor_field_inv_major ms mh v x

let spot_chunked_classify_major_field_inv_minor
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t) (x: U64.t)
  : Lemma
      (requires CG.chunked_classify_major_field ms mh v == Some (CG.MinorV x))
      (ensures to_minor_offset v == x /\
               is_minor_pointer x /\
               Seq.mem x (minor_objects ms))
  = CG.chunked_classify_major_field_inv_minor ms mh v x

let spot_chunked_minor_field_edge_intro_full
  (ms: minor_state) (mh: MH.major_heap)
  (src: U64.t) (i: nat) (dst: CG.combined_vertex)
  : Lemma
      (requires Seq.mem src (minor_objects ms) /\
                i < minor_wosize ms src /\
                CG.chunked_classify_minor_field
                  ms mh (minor_read_field ms src i) == Some dst)
      (ensures
        CG.mem_ce (CG.MinorV src, dst)
          (CG.build_chunked_combined_graph ms mh))
  =
  CG.chunked_minor_field_edge_intro_full ms mh src i dst

let spot_chunked_minor_object_edges
  (ms: minor_state) (mh: MH.major_heap) (obj: U64.t)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_minor_object_edges ms mh obj

let spot_chunked_minor_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_minor_object_expansion_safe ms fresh obj)
      (ensures
        spot_chunked_minor_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        spot_chunked_minor_object_edges ms mh obj)
  = CG.chunked_minor_object_edges_preserved_by_expansion ms mh fresh fp obj

let spot_chunked_all_minor_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: Seq.seq U64.t) (idx: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_all_minor_edges ms mh objs idx

let spot_chunked_all_minor_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: Seq.seq U64.t) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe ms fresh objs idx)
      (ensures
        spot_chunked_all_minor_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs idx ==
        spot_chunked_all_minor_edges ms mh objs idx)
  = CG.chunked_all_minor_edges_preserved_by_expansion
      ms mh fresh fp objs idx

let spot_build_chunked_combined_graph_from_major_objects
  (ms: minor_state) (mh: MH.major_heap) (major_objs: Seq.seq obj_addr)
  : GTot CG.combined_graph
  = CG.build_chunked_combined_graph_from_major_objects ms mh major_objs

let spot_build_chunked_combined_graph
  (ms: minor_state) (mh: MH.major_heap)
  : GTot CG.combined_graph
  = CG.build_chunked_combined_graph ms mh

let spot_combined_vertex_exhaustive (u: CG.combined_vertex)
  : Lemma
      (ensures
        (match u with
         | CG.MinorV _ -> True
         | CG.MajorV _ -> True
         | _ -> False))
  = CG.combined_vertex_exhaustive u

let spot_chunked_minor_vertex_char
  (ms: minor_state) (mh: MH.major_heap) (a: U64.t)
  : Lemma
      (ensures
        CG.mem_cv (CG.MinorV a) (spot_build_chunked_combined_graph ms mh) <==>
        Seq.mem a (minor_objects ms))
  = CG.chunked_minor_vertex_char ms mh a

let spot_chunked_major_vertex_char
  (ms: minor_state) (mh: MH.major_heap) (a: obj_addr)
  : Lemma
      (ensures
        CG.mem_cv (CG.MajorV a) (spot_build_chunked_combined_graph ms mh) <==>
        Seq.mem a (MH.major_objects mh))
  = CG.chunked_major_vertex_char ms mh a

let spot_chunked_major_vertex_valid
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : Lemma
      (requires CG.mem_cv (CG.MajorV v)
                  (spot_build_chunked_combined_graph ms mh))
      (ensures U64.v v >= U64.v mword /\
               U64.v v < heap_size /\
               U64.v v % U64.v mword == 0 /\
               Seq.mem (v <: obj_addr) (MH.major_objects mh))
  = CG.chunked_major_vertex_valid ms mh v

let spot_chunked_edge_source_decomposition
  (ms: minor_state) (mh: MH.major_heap) (e: CG.combined_edge)
  : Lemma
      (requires CG.mem_ce e (spot_build_chunked_combined_graph ms mh))
      (ensures
        (match fst e with
         | CG.MinorV src -> Seq.mem src (minor_objects ms)
         | CG.MajorV src ->
           U64.v src >= U64.v mword /\
           U64.v src < heap_size /\
           U64.v src % U64.v mword == 0 /\
           Seq.mem (src <: obj_addr) (MH.major_objects mh)))
  = CG.chunked_edge_source_decomposition ms mh e

let spot_chunked_edge_source_vertex
  (ms: minor_state) (mh: MH.major_heap) (e: CG.combined_edge)
  : Lemma
      (requires CG.mem_ce e (spot_build_chunked_combined_graph ms mh))
      (ensures CG.mem_cv (fst e) (spot_build_chunked_combined_graph ms mh))
  = CG.chunked_edge_source_vertex ms mh e

let spot_chunked_minor_edge_elim
  (ms: minor_state) (mh: MH.major_heap)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
      (requires
        CG.mem_ce (CG.MinorV src, dst)
          (spot_build_chunked_combined_graph ms mh))
      (ensures Seq.mem src (minor_objects ms) /\
               (exists (i: nat). i < minor_wosize ms src /\
                 CG.chunked_classify_minor_field
                   ms mh (minor_read_field ms src i) == Some dst))
  = CG.chunked_minor_edge_elim ms mh src dst

let spot_chunked_major_edge_elim
  (ms: minor_state) (mh: MH.major_heap)
  (src: obj_addr) (dst: CG.combined_vertex)
  : Lemma
      (requires
        CG.mem_ce (CG.MajorV src, dst)
          (spot_build_chunked_combined_graph ms mh))
      (ensures Seq.mem src (MH.major_objects mh) /\
               CG.chunked_is_no_scan mh src == false /\
               (exists (i: nat). exists (field_addr: hp_addr).
                exists (v: U64.t).
                  i < CG.chunked_wosize_nat_of_object mh src /\
                  CG.chunked_major_field_slot src i == Some field_addr /\
                  MH.read_word_in_major mh field_addr == Some v /\
                  CG.chunked_classify_major_field ms mh v == Some dst))
  = CG.chunked_major_edge_elim ms mh src dst

let spot_chunked_combined_graph_old_view_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (major_objs: Seq.seq obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh major_objs 0)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        let g' =
          spot_build_chunked_combined_graph_from_major_objects
            ms mh' major_objs in
        let g =
          spot_build_chunked_combined_graph_from_major_objects
            ms mh major_objs in
        g'.cg_vertices == g.cg_vertices /\ g'.cg_edges == g.cg_edges))
  = CG.chunked_combined_graph_old_view_preserved_by_expansion
      ms mh fresh fp major_objs

let spot_chunked_build_combined_graph_old_view_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        let g' =
          spot_build_chunked_combined_graph_from_major_objects
            ms mh' (MH.major_objects mh) in
        let g = spot_build_chunked_combined_graph ms mh in
        g'.cg_vertices == g.cg_vertices /\ g'.cg_edges == g.cg_edges))
  = CG.chunked_build_combined_graph_old_view_preserved_by_expansion
      ms mh fresh fp

let spot_chunked_old_view_reachable_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (roots: Seq.seq CG.combined_vertex) (v: CG.combined_vertex)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                CG.chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0 /\
                CG.combined_reachable
                  (spot_build_chunked_combined_graph ms mh) roots v)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        CG.combined_reachable
          (spot_build_chunked_combined_graph_from_major_objects
            ms mh' (MH.major_objects mh))
          roots v))
  = CG.chunked_old_view_reachable_preserved_by_expansion
      ms mh fresh fp roots v

let spot_chunked_header_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_header_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_header_of_object mh obj)
  = CG.chunked_header_of_object_preserved_by_expansion mh fresh fp obj

let spot_chunked_wosize_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_wosize_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_wosize_of_object mh obj)
  = CG.chunked_wosize_of_object_preserved_by_expansion mh fresh fp obj

let spot_chunked_wosize_nat_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_wosize_nat_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_wosize_nat_of_object mh obj)
  = CG.chunked_wosize_nat_of_object_preserved_by_expansion mh fresh fp obj

let spot_chunked_tag_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_tag_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_tag_of_object mh obj)
  = CG.chunked_tag_of_object_preserved_by_expansion mh fresh fp obj

let spot_chunked_is_no_scan_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        CG.chunked_is_no_scan
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        CG.chunked_is_no_scan mh obj)
  = CG.chunked_is_no_scan_preserved_by_expansion mh fresh fp obj

let spot_chunked_major_field_slot_of_object_header
  (mh: MH.major_heap) (src: obj_addr) (hdr: U64.t) (i: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        i < U64.v (Obj.getWosize hdr))
      (ensures CG.chunked_major_field_slot src i <> None)
  = CG.chunked_major_field_slot_of_object_header mh src hdr i

let spot_chunked_major_field_edges
  (ms: minor_state) (mh: MH.major_heap) (src: obj_addr) (wz: nat) (i: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_major_field_edges ms mh src wz i

let spot_chunked_major_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (src: obj_addr) (wz: nat) (i: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_major_field_expansion_safe mh fresh src wz i)
      (ensures
        spot_chunked_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        spot_chunked_major_field_edges ms mh src wz i)
  = CG.chunked_major_field_edges_preserved_by_expansion ms mh fresh fp src wz i

let spot_chunked_major_object_edges
  (ms: minor_state) (mh: MH.major_heap) (obj: obj_addr)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_major_object_edges ms mh obj

let spot_chunked_major_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_major_object_expansion_safe mh fresh obj)
      (ensures
        spot_chunked_major_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        spot_chunked_major_object_edges ms mh obj)
  = CG.chunked_major_object_edges_preserved_by_expansion ms mh fresh fp obj

let spot_chunked_major_object_expansion_safe_from_values_miss_fresh
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MH.chunk_disjoint_from_all fresh mh /\
        Seq.mem obj (MH.major_objects mh) /\
        CG.chunked_major_field_values_miss_fresh
          mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0)
      (ensures CG.chunked_major_object_expansion_safe mh fresh obj)
  =
  CG.chunked_major_object_expansion_safe_from_values_miss_fresh
    mh fresh obj

let spot_chunked_all_major_object_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: Seq.seq obj_addr) (idx: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_all_major_object_edges ms mh objs idx

let spot_chunked_all_major_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: Seq.seq obj_addr) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_object_expansion_safe mh fresh objs idx)
      (ensures
        spot_chunked_all_major_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs idx ==
        spot_chunked_all_major_object_edges ms mh objs idx)
  = CG.chunked_all_major_object_edges_preserved_by_expansion
      ms mh fresh fp objs idx

let spot_chunked_all_major_object_expansion_safe_from_values_miss_fresh
  (mh: MH.major_heap) (fresh: MH.heap_chunk)
  (objs: Seq.seq obj_addr) (idx: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MH.chunk_disjoint_from_all fresh mh /\
        (forall (k:nat).
          idx <= k /\ k < Seq.length objs ==>
            Seq.mem (Seq.index objs k) (MH.major_objects mh) /\
            CG.chunked_major_field_values_miss_fresh
              mh fresh (Seq.index objs k)
              (CG.chunked_wosize_nat_of_object mh (Seq.index objs k)) 0))
      (ensures CG.chunked_all_major_object_expansion_safe mh fresh objs idx)
  =
  CG.chunked_all_major_object_expansion_safe_from_values_miss_fresh
    mh fresh objs idx

let spot_chunked_major_objects_expansion_safe_from_values_miss_fresh
  (mh: MH.major_heap) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        MH.chunk_disjoint_from_all fresh mh /\
        (forall (obj:obj_addr).
          Seq.mem obj (MH.major_objects mh) ==>
            CG.chunked_major_field_values_miss_fresh
              mh fresh obj (CG.chunked_wosize_nat_of_object mh obj) 0))
      (ensures
        CG.chunked_all_major_object_expansion_safe
          mh fresh (MH.major_objects mh) 0)
  =
  CG.chunked_major_objects_expansion_safe_from_values_miss_fresh
    mh fresh

let spot_chunked_all_major_field_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: Seq.seq obj_addr)
  (wz_of: obj_addr -> GTot nat) (idx: nat)
  : GTot (Seq.seq CG.combined_edge)
  = CG.chunked_all_major_field_edges ms mh objs wz_of idx

let spot_chunked_all_major_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: Seq.seq obj_addr) (wz_of: obj_addr -> GTot nat) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                CG.chunked_all_major_field_expansion_safe
                  mh fresh objs wz_of idx)
      (ensures
        spot_chunked_all_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs wz_of idx ==
        spot_chunked_all_major_field_edges ms mh objs wz_of idx)
  = CG.chunked_all_major_field_edges_preserved_by_expansion
      ms mh fresh fp objs wz_of idx

let spot_chunked_update_major_pointers_single_chunk_compat
  (major: heap) (fwd: forwarding_map)
  : Lemma
      (ensures
        ChunkedUpdate.chunked_update_major_pointers
          (MH.single_chunk_major_heap major) fwd ==
        MH.single_chunk_major_heap (update_major_pointers major fwd))
  =
  ChunkedUpdate.chunked_update_major_pointers_single_chunk_compat major fwd

let spot_chunked_update_major_pointers_preserves_wf_and_major_objects
  (major: MH.major_heap) (fwd: forwarding_map)
  : Lemma
      (requires MH.well_formed_major_heap major)
      (ensures
        MH.well_formed_major_heap
          (ChunkedUpdate.chunked_update_major_pointers major fwd) /\
        MH.major_objects
          (ChunkedUpdate.chunked_update_major_pointers major fwd) ==
          MH.major_objects major)
  =
  ChunkedUpdate.chunked_update_major_pointers_preserves_wf_and_major_objects
    major fwd

let spot_chunked_update_field_preserves_read_disjoint
  (major: MH.major_heap) (field_addr addr: hp_addr)
  (old: U64.t) (fwd: forwarding_map)
  : Lemma
      (requires MH.well_formed_major_heap major /\
                MH.read_word_in_major major addr == Some old /\
                ChunkedUpdate.chunked_words_disjoint field_addr addr)
      (ensures
        MH.well_formed_major_heap
          (ChunkedUpdate.chunked_update_field major field_addr fwd) /\
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_field major field_addr fwd)
          addr == Some old)
  =
  ChunkedUpdate.chunked_update_field_preserves_wf_and_read_disjoint
    major field_addr addr old fwd

let spot_chunked_update_field_effect
  (major: MH.major_heap) (field_addr: hp_addr) (old: U64.t)
  (fwd: forwarding_map)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        (let old_val = to_minor_offset old in
         let updated = ChunkedUpdate.chunked_update_field major field_addr fwd in
         (is_minor_pointer old_val /\ fwd old_val <> 0UL ==>
          MH.read_word_in_major updated field_addr == Some (fwd old_val)) /\
         (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==>
          MH.read_word_in_major updated field_addr == Some old)))
  =
  ChunkedUpdate.chunked_update_field_effect major field_addr old fwd

let spot_chunked_update_field_slot_in_object_chunk
  (major: MH.major_heap) (obj: obj_addr) (i: nat) (field_addr: hp_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem obj (MH.major_objects major) /\
        i < ChunkedUpdate.chunked_wosize_nat_of_object major obj /\
        ChunkedUpdate.chunked_update_field_slot obj i == Some field_addr)
      (ensures
        (let idx = MH.lookup_chunk_index_value major (hd_address obj) in
        MH.lookup_chunk_index major (hd_address obj) == Some idx /\
        idx < Seq.length major /\
        MH.word_in_chunk (Seq.index major idx) (hd_address obj) /\
        MH.word_in_chunk (Seq.index major idx) field_addr /\
        MH.lookup_chunk_index major field_addr == Some idx))
  =
  ChunkedUpdate.chunked_update_field_slot_in_object_chunk
    major obj i field_addr

let spot_chunked_update_object_pointers_preserves_read_disjoint
  (major: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat) (addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        MH.read_word_in_major major addr == Some old /\
        (forall (k:nat) (field_addr:hp_addr).
          i <= k /\ k < wosize /\
          ChunkedUpdate.chunked_update_field_slot obj k == Some field_addr ==>
          ChunkedUpdate.chunked_words_disjoint field_addr addr))
      (ensures
        (let major' =
           ChunkedUpdate.chunked_update_object_pointers
             major obj wosize fwd i in
         MH.well_formed_major_heap major' /\
         MH.read_word_in_major major' addr == Some old))
  =
  ChunkedUpdate.chunked_update_object_pointers_preserves_read_disjoint
    major obj wosize fwd i addr old

let spot_chunked_update_object_pointers_field_effect
  (major: MH.major_heap) (obj: obj_addr) (wosize: nat)
  (fwd: forwarding_map) (i: nat) (j: nat) (field_addr: hp_addr)
  (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem obj (MH.major_objects major) /\
        wosize == ChunkedUpdate.chunked_wosize_nat_of_object major obj /\
        i <= j /\ j < wosize /\
        ChunkedUpdate.chunked_update_field_slot obj j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        (let major' =
           ChunkedUpdate.chunked_update_object_pointers
             major obj wosize fwd i in
         let old_val = to_minor_offset old in
         MH.well_formed_major_heap major' /\
         MH.major_objects major' == MH.major_objects major /\
         ChunkedUpdate.chunked_header_of_object major' obj ==
           ChunkedUpdate.chunked_header_of_object major obj /\
         (is_minor_pointer old_val /\ fwd old_val <> 0UL ==>
          MH.read_word_in_major major' field_addr == Some (fwd old_val)) /\
         (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==>
          MH.read_word_in_major major' field_addr == Some old)))
  =
  ChunkedUpdate.chunked_update_object_pointers_field_effect
    major obj wosize fwd i j field_addr old

let spot_chunked_update_major_pointers_preserves_header
  (major: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem h (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address h) == Some hdr)
      (ensures
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_major_pointers major fwd)
          (hd_address h) == Some hdr)
  =
  ChunkedUpdate.chunked_update_major_pointers_preserves_header
    major fwd h hdr

let spot_chunked_update_major_pointers_preserves_blue_field
  (major: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem h (MH.major_objects major) /\
        ChunkedUpdate.chunked_is_blue major h /\
        j < ChunkedUpdate.chunked_wosize_nat_of_object major h /\
        ChunkedUpdate.chunked_update_field_slot h j == Some field_addr /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_major_pointers major fwd)
          field_addr == Some old)
  =
  ChunkedUpdate.chunked_update_major_pointers_preserves_blue_field
    major fwd h j field_addr old

let spot_chunked_update_major_pointers_preserves_no_scan_field
  (major: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (hdr: U64.t)
  (j: nat) (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem h (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address h) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getTag hdr) >= U64.v Obj.no_scan_tag /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v h + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old)
      (ensures
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_major_pointers major fwd)
          field_addr == Some old)
  =
  ChunkedUpdate.chunked_update_major_pointers_preserves_no_scan_field
    major fwd h hdr j field_addr old

let spot_chunked_update_major_pointers_field_effect_stable
  (major: MH.major_heap) (fwd: forwarding_map) (h: obj_addr) (hdr: U64.t)
  (j: nat) (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        Seq.mem h (MH.major_objects major) /\
        MH.read_word_in_major major (hd_address h) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v h + j * U64.v mword /\
        MH.read_word_in_major major field_addr == Some old /\
        ChunkedUpdate.chunked_update_value_stable fwd
          (ChunkedUpdate.chunked_update_expected_value fwd old))
      (ensures
        MH.read_word_in_major
          (ChunkedUpdate.chunked_update_major_pointers major fwd)
          field_addr ==
        Some (ChunkedUpdate.chunked_update_expected_value fwd old))
  =
  ChunkedUpdate.chunked_update_major_pointers_field_effect_stable
    major fwd h hdr j field_addr old

let spot_chunked_chain_objects_blue_elim
  (major: MH.major_heap) (fp: U64.t) (fuel: nat) (obj: obj_addr)
  : Lemma
      (requires GenInv.chunked_chain_objects_blue major fp fuel /\
                Seq.mem obj (MH.major_objects major) /\
                ~(GenInv.chunked_is_blue major obj))
      (ensures
        SpecMajorAlloc.major_fl_chain_avoids major fp obj fuel = true)
  =
  GenInv.chunked_chain_objects_blue_elim major fp fuel obj

let spot_chunked_chain_objects_blue_preserved_by_expansion
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (fuel: nat)
  : Lemma
      (requires
        GenInv.chunked_chain_objects_blue major fp fuel /\
        MH.well_formed_major_heap major /\
        SpecMajorAlloc.major_fl_valid major fp fuel /\
        SpecMajorAlloc.major_fl_above_zero major fp fuel /\
        MH.chunk_disjoint_from_all fresh major)
      (ensures
        (let r = SpecMajorAlloc.expand_major_heap major fresh fp in
         GenInv.chunked_chain_objects_blue r.major_out r.fp_out (fuel + 1)))
  =
  GenInv.chunked_chain_objects_blue_preserved_by_expansion
    major fresh fp fuel

let spot_chunked_chain_objects_blue_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.chunked_chain_objects_blue major fp fuel /\
        MH.well_formed_major_heap major /\
        SpecMajorAlloc.major_fl_valid major fp fuel /\
        SpecMajorAlloc.major_fl_above_zero major fp fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
         MH.chunk_disjoint_from_all fresh major))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp fuel needed fresh in
         GenInv.chunked_chain_objects_blue
           r.capacity_major_out r.capacity_fp_out r.capacity_fuel_out))
  =
  GenInv.chunked_chain_objects_blue_ensure_head_capacity
    major fp fuel needed fresh

let spot_chunked_update_major_pointers_preserves_alloc_shape
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (fwd: forwarding_map)
  : Lemma
      (requires
        GenInv.chunked_major_alloc_shape major fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates major fp fuel = true /\
        GenInv.chunked_chain_objects_blue major fp fuel)
      (ensures
        (let updated =
           ChunkedUpdate.chunked_update_major_pointers major fwd in
         GenInv.chunked_major_alloc_shape updated fp fuel /\
         SpecMajorAlloc.major_fl_chain_terminates updated fp fuel = true /\
         GenInv.chunked_chain_objects_blue updated fp fuel))
  =
  CheneyPreservation.chunked_update_major_pointers_preserves_alloc_shape
    major fp fuel fwd

let spot_chunked_cheney_collect_default_single_chunk_compat
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: Seq.seq U64.t)
  : Lemma
      (ensures
        (let chunked =
           ChunkedCheney.chunked_cheney_collect_spec
             minor (MH.single_chunk_major_heap major) fp roots
             SpecAlloc.alloc_search_fuel in
         let dense = cheney_collect_spec minor major fp roots in
         chunked.cmc_major == MH.single_chunk_major_heap dense.mc_major /\
         chunked.cmc_fp == dense.mc_fp /\
         chunked.cmc_minor == dense.mc_minor /\
         chunked.cmc_roots == dense.mc_roots /\
         chunked.cmc_fwd == dense.mc_fwd))
  =
  ChunkedCheney.chunked_cheney_collect_default_single_chunk_compat
    minor major fp roots

let spot_chunked_cheney_collect_after_minor_promotion_head_preflight
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let prom =
           ChunkedCheney.chunked_cheney_promote
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         collect.cmc_fp == prom.fp_final /\
         collect.cmc_minor == minor_reset minor /\
         minor_wf collect.cmc_minor /\
         U64.v collect.cmc_minor.bump == 0 /\
         collect.cmc_roots == rewrite_roots roots prom.fwd_map /\
         collect.cmc_fwd == prom.fwd_map /\
         CheneyPreservation.chunked_fwd_targets_above_minor collect.cmc_fwd /\
         CheneyPreservation.chunked_fwd_targets_valid_addr collect.cmc_fwd /\
         CheneyPreservation.chunked_fwd_noninfix_targets_in_major
           minor collect.cmc_fwd collect.cmc_major /\
         GenInv.chunked_major_alloc_shape
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         (forall (src: obj_addr).
          Seq.mem src (MH.major_objects major) ==>
          Seq.mem src (MH.major_objects collect.cmc_major)) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          U64.v (Obj.getWosize hdr) >= 1 ==>
          MH.read_word_in_major collect.cmc_major (hd_address src) ==
            Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old /\
          (U64.v (Obj.getTag hdr) >= U64.v Obj.no_scan_tag \/
           ~(is_minor_pointer (to_minor_offset old) /\
             collect.cmc_fwd (to_minor_offset old) <> 0UL)) ==>
          MH.read_word_in_major collect.cmc_major field_addr == Some old) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old ==>
          MH.read_word_in_major collect.cmc_major field_addr ==
            Some (ChunkedUpdate.chunked_update_expected_value
              collect.cmc_fwd old)) /\
         (forall (x:U64.t).
          Seq.mem x (minor_reachable minor roots) /\
          minor_wosize minor x > 0 ==>
          collect.cmc_fwd x <> 0UL)))
  =
  CheneyPreservation.chunked_cheney_collect_after_minor_promotion_head_preflight
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_collect_after_preflight_forwards_reachable
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
           collect.cmc_fwd x <> 0UL \/ minor_wosize minor x = 0))
  =
  CheneyCorrectness.chunked_cheney_collect_after_preflight_forwards_reachable
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_minor_successor_forwarded
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: U64.t) (j: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem src (minor_reachable minor roots) /\
        j < minor_wosize minor src /\
        to_minor_offset (minor_read_field minor src j) == dst /\
        is_minor_addr dst /\
        Seq.mem dst (minor_objects minor) /\
        minor_wosize minor dst > 0)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MinorV src, CG.MinorV dst)
           (CG.build_chunked_combined_graph minor major) /\
         collect.cmc_fwd src <> 0UL /\
         collect.cmc_fwd dst <> 0UL))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_minor_successor_forwarded
    minor major fp roots alloc_fuel fresh src dst j

let spot_chunked_cheney_gc_correct_after_preflight_minor_successor_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: U64.t) (j: nat) (field_addr: hp_addr)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem src (minor_reachable minor roots) /\
        j < minor_wosize minor src /\
        minor_tag minor src < U64.v Obj.no_scan_tag /\
        to_minor_offset (minor_read_field minor src j) == dst /\
        is_minor_addr dst /\
        Seq.mem dst (minor_objects minor) /\
        minor_wosize minor dst > 0 /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         U64.v field_addr == U64.v (collect.cmc_fwd src) + j * U64.v mword))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MajorV (collect.cmc_fwd src),
                    CG.MajorV (collect.cmc_fwd dst))
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_minor_successor_major_edge
    minor major fp roots alloc_fuel fresh src dst j field_addr

let spot_chunked_cheney_gc_correct_after_preflight_minor_successor_major_edge_no_field_addr
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: U64.t) (j: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem src (minor_reachable minor roots) /\
        j < minor_wosize minor src /\
        minor_tag minor src < U64.v Obj.no_scan_tag /\
        to_minor_offset (minor_read_field minor src j) == dst /\
        is_minor_addr dst /\
        Seq.mem dst (minor_objects minor) /\
        minor_wosize minor dst > 0)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MajorV (collect.cmc_fwd src),
                    CG.MajorV (collect.cmc_fwd dst))
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_minor_successor_major_edge_no_field_addr
    minor major fp roots alloc_fuel fresh src dst j

let spot_chunked_cheney_gc_correct_after_preflight_minor_successor_edge_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: U64.t) (j: nat) (field_addr: hp_addr)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem src (minor_reachable minor roots) /\
        j < minor_wosize minor src /\
        minor_tag minor src < U64.v Obj.no_scan_tag /\
        to_minor_offset (minor_read_field minor src j) == dst /\
        is_minor_addr dst /\
        Seq.mem dst (minor_objects minor) /\
        minor_wosize minor dst > 0 /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         U64.v field_addr == U64.v (collect.cmc_fwd src) + j * U64.v mword))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MinorV src, CG.MinorV dst)
          (CG.build_chunked_combined_graph minor major) /\
         collect.cmc_fwd src <> 0UL /\
         collect.cmc_fwd dst <> 0UL /\
         CG.mem_ce (CG.MajorV (collect.cmc_fwd src),
                    CG.MajorV (collect.cmc_fwd dst))
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_minor_successor_edge_maps_to_major_edge
    minor major fp roots alloc_fuel fresh src dst j field_addr

let spot_chunked_cheney_gc_correct_after_preflight_minor_successor_edge_maps_to_major_edge_no_field_addr
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: U64.t) (j: nat)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem src (minor_reachable minor roots) /\
        j < minor_wosize minor src /\
        minor_tag minor src < U64.v Obj.no_scan_tag /\
        to_minor_offset (minor_read_field minor src j) == dst /\
        is_minor_addr dst /\
        Seq.mem dst (minor_objects minor) /\
        minor_wosize minor dst > 0)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MinorV src, CG.MinorV dst)
          (CG.build_chunked_combined_graph minor major) /\
         collect.cmc_fwd src <> 0UL /\
         collect.cmc_fwd dst <> 0UL /\
         CG.mem_ce (CG.MajorV (collect.cmc_fwd src),
                    CG.MajorV (collect.cmc_fwd dst))
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_minor_successor_edge_maps_to_major_edge_no_field_addr
    minor major fp roots alloc_fuel fresh src dst j

let spot_chunked_cheney_gc_correct_after_preflight_minor_graph_edge_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem src (minor_reachable minor roots) /\
        minor_tag minor src < U64.v Obj.no_scan_tag /\
        CG.mem_ce (CG.MinorV src, CG.MinorV dst)
          (CG.build_chunked_combined_graph minor major) /\
        minor_wosize minor dst > 0)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         collect.cmc_fwd src <> 0UL /\
         collect.cmc_fwd dst <> 0UL /\
         CG.mem_ce (CG.MajorV (collect.cmc_fwd src),
                    CG.MajorV (collect.cmc_fwd dst))
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_minor_graph_edge_maps_to_major_edge
    minor major fp roots alloc_fuel fresh src dst

let spot_chunked_cheney_gc_correct_after_preflight_minor_major_graph_edge_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src: U64.t) (dst: obj_addr)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem src (minor_reachable minor roots) /\
        minor_tag minor src < U64.v Obj.no_scan_tag /\
        CG.mem_ce (CG.MinorV src, CG.MajorV dst)
          (CG.build_chunked_combined_graph minor major) /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         ~(is_minor_pointer (to_minor_offset dst) /\
           collect.cmc_fwd (to_minor_offset dst) <> 0UL)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         collect.cmc_fwd src <> 0UL /\
         CG.mem_ce (CG.MajorV (collect.cmc_fwd src), CG.MajorV dst)
           (CG.build_chunked_combined_graph
             collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_minor_major_graph_edge_maps_to_major_edge
    minor major fp roots alloc_fuel fresh src dst

let spot_chunked_cheney_gc_correct_after_preflight
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let prom =
           ChunkedCheney.chunked_cheney_promote
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         collect.cmc_fp == prom.fp_final /\
         collect.cmc_minor == minor_reset minor /\
         minor_wf collect.cmc_minor /\
         U64.v collect.cmc_minor.bump == 0 /\
         collect.cmc_roots == rewrite_roots roots prom.fwd_map /\
         collect.cmc_fwd == prom.fwd_map /\
         CheneyPreservation.chunked_fwd_targets_above_minor collect.cmc_fwd /\
         CheneyPreservation.chunked_fwd_targets_valid_addr collect.cmc_fwd /\
         CheneyPreservation.chunked_fwd_noninfix_targets_in_major
           minor collect.cmc_fwd collect.cmc_major /\
         GenInv.chunked_major_alloc_shape
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         (forall (src: obj_addr).
           Seq.mem src (MH.major_objects major) ==>
           Seq.mem src (MH.major_objects collect.cmc_major)) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
           Seq.mem src (MH.major_objects major) /\
           MH.read_word_in_major major (hd_address src) == Some hdr /\
           Obj.getColor hdr <> GC.Lib.Header.Blue /\
           U64.v (Obj.getWosize hdr) >= 1 ==>
           MH.read_word_in_major collect.cmc_major (hd_address src) ==
             Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old /\
          (U64.v (Obj.getTag hdr) >= U64.v Obj.no_scan_tag \/
           ~(is_minor_pointer (to_minor_offset old) /\
             collect.cmc_fwd (to_minor_offset old) <> 0UL)) ==>
          MH.read_word_in_major collect.cmc_major field_addr == Some old) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old ==>
          MH.read_word_in_major collect.cmc_major field_addr ==
            Some (ChunkedUpdate.chunked_update_expected_value
              collect.cmc_fwd old)) /\
         (forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
           collect.cmc_fwd x <> 0UL \/ minor_wosize minor x = 0)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_value_safety
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          (forall (obj:obj_addr).
            Seq.mem obj (MH.major_objects major) ==>
              CG.chunked_major_field_values_miss_fresh
                major fresh obj
                (CG.chunked_wosize_nat_of_object major obj) 0)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let prom =
           ChunkedCheney.chunked_cheney_promote
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         collect.cmc_fp == prom.fp_final /\
         collect.cmc_minor == minor_reset minor /\
         minor_wf collect.cmc_minor /\
         U64.v collect.cmc_minor.bump == 0 /\
         collect.cmc_roots == rewrite_roots roots prom.fwd_map /\
         collect.cmc_fwd == prom.fwd_map /\
         CheneyPreservation.chunked_fwd_targets_above_minor collect.cmc_fwd /\
         CheneyPreservation.chunked_fwd_targets_valid_addr collect.cmc_fwd /\
         CheneyPreservation.chunked_fwd_noninfix_targets_in_major
           minor collect.cmc_fwd collect.cmc_major /\
         GenInv.chunked_major_alloc_shape
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         SpecMajorAlloc.major_fl_chain_terminates
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out = true /\
         GenInv.chunked_chain_objects_blue
           collect.cmc_major collect.cmc_fp r.capacity_fuel_out /\
         (forall (src: obj_addr).
           Seq.mem src (MH.major_objects major) ==>
           Seq.mem src (MH.major_objects collect.cmc_major)) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
           Seq.mem src (MH.major_objects major) /\
           MH.read_word_in_major major (hd_address src) == Some hdr /\
           Obj.getColor hdr <> GC.Lib.Header.Blue /\
           U64.v (Obj.getWosize hdr) >= 1 ==>
           MH.read_word_in_major collect.cmc_major (hd_address src) ==
             Some hdr) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old /\
          (U64.v (Obj.getTag hdr) >= U64.v Obj.no_scan_tag \/
           ~(is_minor_pointer (to_minor_offset old) /\
             collect.cmc_fwd (to_minor_offset old) <> 0UL)) ==>
          MH.read_word_in_major collect.cmc_major field_addr == Some old) /\
         (forall (src: obj_addr). forall (hdr: U64.t).
          forall (j:nat). forall (field_addr: hp_addr).
          forall (old: U64.t).
          Seq.mem src (MH.major_objects major) /\
          MH.read_word_in_major major (hd_address src) == Some hdr /\
          Obj.getColor hdr <> GC.Lib.Header.Blue /\
          U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
          j < U64.v (Obj.getWosize hdr) /\
          U64.v field_addr == U64.v src + j * U64.v mword /\
          MH.read_word_in_major major field_addr == Some old ==>
          MH.read_word_in_major collect.cmc_major field_addr ==
            Some (ChunkedUpdate.chunked_update_expected_value
              collect.cmc_fwd old)) /\
         (forall (x: U64.t). Seq.mem x (minor_reachable minor roots) ==>
           collect.cmc_fwd x <> 0UL \/ minor_wosize minor x = 0)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_value_safety
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_forwarded_minor_object_in_major
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (x: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem x (minor_objects minor) /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel needed fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         collect.cmc_fwd x <> 0UL))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel needed fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         is_val_addr (collect.cmc_fwd x) /\
         Seq.mem ((collect.cmc_fwd x) <: obj_addr)
          (MH.major_objects collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_forwarded_minor_object_in_major
    minor major fp roots alloc_fuel fresh x

let spot_chunked_cheney_gc_correct_after_preflight_reachable_forwarding_target_in_major
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (x: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        Seq.mem x (minor_reachable minor roots) /\
        minor_wosize minor x > 0)
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel needed fresh in
         let collect =
          ChunkedCheney.chunked_cheney_collect_spec
            minor r.capacity_major_out r.capacity_fp_out roots
            r.capacity_fuel_out in
         is_val_addr (collect.cmc_fwd x) /\
         Seq.mem ((collect.cmc_fwd x) <: obj_addr)
          (MH.major_objects collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_reachable_forwarding_target_in_major
    minor major fp roots alloc_fuel fresh x

let spot_chunked_update_forwarded_minor_field_edge
  (minor: minor_state) (mh: MH.major_heap) (fwd: forwarding_map)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        CheneyPreservation.chunked_fwd_targets_above_minor fwd /\
        Seq.mem src (MH.major_objects mh) /\
        Seq.mem expected (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major mh field_addr == Some old /\
        (let x = to_minor_offset old in
         is_minor_pointer x /\ fwd x <> 0UL /\ fwd x == expected))
      (ensures
        CG.mem_ce (CG.MajorV src, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            (minor_reset minor)
            (ChunkedUpdate.chunked_update_major_pointers mh fwd)))
  =
  CheneyCorrectness.chunked_update_forwarded_minor_field_edge
    minor mh fwd src expected hdr j field_addr old

let spot_chunked_forward_one_normal_updated_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat)
  (promoted expected: obj_addr) (hdr: U64.t) (field_addr: hp_addr)
  : Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        j < minor_wosize minor addr /\
        promoted == cs.ccs_fp /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
        U64.v field_addr == U64.v promoted + j * U64.v mword /\
        (let cs' = ChunkedCheney.chunked_cheney_forward_one
            minor cs addr fuel in
         let old = minor_read_field minor addr j in
         let x = to_minor_offset old in
         MH.well_formed_major_heap cs'.ccs_major /\
         CheneyPreservation.chunked_fwd_targets_above_minor cs'.ccs_fwd /\
         Seq.mem promoted (MH.major_objects cs'.ccs_major) /\
         Seq.mem expected (MH.major_objects cs'.ccs_major) /\
         MH.read_word_in_major cs'.ccs_major (hd_address promoted) ==
           Some hdr /\
         Obj.getColor hdr <> GC.Lib.Header.Blue /\
         U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
         j < U64.v (Obj.getWosize hdr) /\
         CG.chunked_major_field_slot promoted j == Some field_addr /\
         is_minor_pointer x /\
         cs'.ccs_fwd x <> 0UL /\
         cs'.ccs_fwd x == expected))
      (ensures
        (let cs' = ChunkedCheney.chunked_cheney_forward_one
          minor cs addr fuel in
         CG.mem_ce (CG.MajorV promoted, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            (minor_reset minor)
            (ChunkedUpdate.chunked_update_major_pointers
              cs'.ccs_major cs'.ccs_fwd))))
  =
  CheneyCorrectness.chunked_forward_one_normal_updated_field_edge
    minor cs addr fuel j promoted expected hdr field_addr

let spot_chunked_forward_one_normal_head_split_updated_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat)
  (promoted expected: obj_addr) (field_addr: hp_addr)
  : Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        minor_tag minor addr < U64.v Obj.no_scan_tag /\
        j < minor_wosize minor addr /\
        promoted == cs.ccs_fp /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
        U64.v field_addr == U64.v promoted + j * U64.v mword /\
        CG.chunked_major_field_slot promoted j == Some field_addr /\
        (let cs' = ChunkedCheney.chunked_cheney_forward_one
            minor cs addr fuel in
         let old = minor_read_field minor addr j in
         let x = to_minor_offset old in
         CheneyPreservation.chunked_fwd_targets_above_minor cs'.ccs_fwd /\
         Seq.mem expected (MH.major_objects cs'.ccs_major) /\
         is_minor_pointer x /\
         cs'.ccs_fwd x <> 0UL /\
         cs'.ccs_fwd x == expected))
      (ensures
        (let cs' = ChunkedCheney.chunked_cheney_forward_one
          minor cs addr fuel in
         CG.mem_ce (CG.MajorV promoted, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            (minor_reset minor)
            (ChunkedUpdate.chunked_update_major_pointers
              cs'.ccs_major cs'.ccs_fwd))))
  =
  CheneyCorrectness.chunked_forward_one_normal_head_split_updated_field_edge
    minor cs addr fuel j promoted expected field_addr

let spot_chunked_forward_one_normal_existing_forwarded_updated_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat)
  (promoted expected: obj_addr) (field_addr: hp_addr)
  : Lemma
      (requires
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        minor_tag minor addr < U64.v Obj.no_scan_tag /\
        j < minor_wosize minor addr /\
        promoted == cs.ccs_fp /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        CheneyPreservation.chunked_fwd_targets_above_minor cs.ccs_fwd /\
        CheneyPreservation.chunked_cheney_forward_one_budget_ready
          minor cs addr 1 /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
        U64.v field_addr == U64.v promoted + j * U64.v mword /\
        CG.chunked_major_field_slot promoted j == Some field_addr /\
        (let old = minor_read_field minor addr j in
         let x = to_minor_offset old in
         is_minor_pointer x /\
         cs.ccs_fwd x <> 0UL /\
         cs.ccs_fwd x == expected /\
         Seq.mem expected (MH.major_objects cs.ccs_major)))
      (ensures
        (let cs' = ChunkedCheney.chunked_cheney_forward_one
          minor cs addr fuel in
         CG.mem_ce (CG.MajorV promoted, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            (minor_reset minor)
            (ChunkedUpdate.chunked_update_major_pointers
              cs'.ccs_major cs'.ccs_fwd))))
  =
  CheneyCorrectness.chunked_forward_one_normal_existing_forwarded_updated_field_edge
    minor cs addr fuel j promoted expected field_addr

let spot_chunked_forward_fields_preserved_forwarded_minor_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_forward_fields_split_ready
          minor cs parent idx wosize alloc_fuel /\
        Seq.mem src (MH.major_objects cs.ccs_major) /\
        MH.read_word_in_major cs.ccs_major (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major cs.ccs_major field_addr == Some old /\
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel in
         let x = to_minor_offset old in
         CheneyPreservation.chunked_fwd_targets_above_minor cs'.ccs_fwd /\
         Seq.mem expected (MH.major_objects cs'.ccs_major) /\
         is_minor_pointer x /\
         cs'.ccs_fwd x <> 0UL /\
         cs'.ccs_fwd x == expected))
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel in
         CG.mem_ce (CG.MajorV src, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            (minor_reset minor)
            (ChunkedUpdate.chunked_update_major_pointers
              cs'.ccs_major cs'.ccs_fwd))))
  =
  CheneyCorrectness.chunked_forward_fields_preserved_forwarded_minor_field_edge
    minor cs parent idx wosize alloc_fuel src expected hdr j field_addr old

let spot_chunked_forward_fields_preserved_minor_object_field_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (parent: U64.t) (idx wosize alloc_fuel: nat)
  (src: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_major_alloc_shape
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue
          cs.ccs_major cs.ccs_fp alloc_fuel /\
        CheneyPreservation.chunked_cheney_forward_fields_split_ready
          minor cs parent idx wosize alloc_fuel /\
        Seq.mem src (MH.major_objects cs.ccs_major) /\
        MH.read_word_in_major cs.ccs_major (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
        j < U64.v (Obj.getWosize hdr) /\
        U64.v field_addr == U64.v src + j * U64.v mword /\
        CG.chunked_major_field_slot src j == Some field_addr /\
        MH.read_word_in_major cs.ccs_major field_addr == Some old /\
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel in
         let x = to_minor_offset old in
         CheneyPreservation.chunked_fwd_targets_above_minor cs'.ccs_fwd /\
         CheneyPreservation.chunked_fwd_noninfix_targets_in_major
          minor cs'.ccs_fwd cs'.ccs_major /\
         is_minor_pointer x /\
         Seq.mem x (minor_objects minor) /\
         cs'.ccs_fwd x <> 0UL))
      (ensures
        (let cs' =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs parent idx wosize alloc_fuel in
         let x = to_minor_offset old in
         CG.mem_ce (CG.MajorV src, CG.MajorV (cs'.ccs_fwd x))
          (CG.build_chunked_combined_graph
            (minor_reset minor)
            (ChunkedUpdate.chunked_update_major_pointers
              cs'.ccs_major cs'.ccs_fwd))))
  =
  CheneyCorrectness.chunked_forward_fields_preserved_minor_object_field_edge
    minor cs parent idx wosize alloc_fuel src hdr j field_addr old

let spot_chunked_forward_one_normal_then_fields_minor_successor_edge
  (minor: minor_state) (cs: ChunkedCheney.chunked_cheney_state)
  (addr: U64.t) (fuel: nat) (j: nat)
  (promoted: obj_addr) (field_addr: hp_addr)
  : Lemma
      (requires
        minor_wf minor /\
        fuel > 1 /\
        Seq.mem addr (minor_objects minor) /\
        cs.ccs_fwd addr = 0UL /\
        ~(is_infix_in_minor minor addr) /\
        minor_wosize minor addr > 0 /\
        minor_wosize minor addr < pow2 54 /\
        FStar.UInt.size (minor_wosize minor addr) 64 /\
        minor_tag minor addr < U64.v Obj.no_scan_tag /\
        j < minor_wosize minor addr /\
        promoted == cs.ccs_fp /\
        GenInv.chunked_major_alloc_shape cs.ccs_major cs.ccs_fp fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          cs.ccs_major cs.ccs_fp fuel = true /\
        GenInv.chunked_chain_objects_blue cs.ccs_major cs.ccs_fp fuel /\
        cs.ccs_fp <> 0UL /\
        SpecMajorAlloc.major_fl_head_wosize
          cs.ccs_major cs.ccs_fp >= minor_wosize minor addr + 2 /\
        U64.v field_addr == U64.v promoted + j * U64.v mword /\
        CG.chunked_major_field_slot promoted j == Some field_addr /\
        (let cs1 =
          ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         let cs2 =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs1 addr 0 (minor_wosize minor addr) fuel in
         let old = minor_read_field minor addr j in
         let x = to_minor_offset old in
         CheneyPreservation.chunked_cheney_forward_fields_split_ready
          minor cs1 addr 0 (minor_wosize minor addr) fuel /\
         CheneyPreservation.chunked_cheney_forward_fields_budget_ready
          minor cs1 addr 0 (minor_wosize minor addr) fuel 1 /\
         CheneyPreservation.chunked_fwd_targets_above_minor cs2.ccs_fwd /\
         CheneyPreservation.chunked_fwd_noninfix_targets_in_major
          minor cs2.ccs_fwd cs2.ccs_major /\
         is_minor_pointer x /\
         Seq.mem x (minor_objects minor) /\
         minor_wosize minor x > 0))
      (ensures
        (let cs1 =
          ChunkedCheney.chunked_cheney_forward_one minor cs addr fuel in
         let cs2 =
          ChunkedCheney.chunked_cheney_forward_fields
            minor cs1 addr 0 (minor_wosize minor addr) fuel in
         let x = to_minor_offset (minor_read_field minor addr j) in
         CG.mem_ce (CG.MajorV promoted, CG.MajorV (cs2.ccs_fwd x))
          (CG.build_chunked_combined_graph
            (minor_reset minor)
            (ChunkedUpdate.chunked_update_major_pointers
              cs2.ccs_major cs2.ccs_fwd))))
  =
  CheneyCorrectness.chunked_forward_one_normal_then_fields_minor_successor_edge
    minor cs addr fuel j promoted field_addr

let spot_chunked_cheney_gc_correct_after_preflight_old_major_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         Seq.mem src (MH.major_objects major) /\
         MH.read_word_in_major major (hd_address src) == Some hdr /\
         Obj.getColor hdr <> GC.Lib.Header.Blue /\
         U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
         j < U64.v (Obj.getWosize hdr) /\
         U64.v field_addr == U64.v src + j * U64.v mword /\
         CG.chunked_major_field_slot src j == Some field_addr /\
         MH.read_word_in_major major field_addr == Some old /\
         ChunkedUpdate.chunked_update_expected_value collect.cmc_fwd old ==
           expected /\
         Seq.mem expected (MH.major_objects collect.cmc_major)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MajorV src, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_old_major_field_edge
    minor major fp roots alloc_fuel fresh src expected hdr j field_addr old

let spot_chunked_cheney_gc_correct_after_preflight_old_major_nonforwarded_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         Seq.mem src (MH.major_objects major) /\
         Seq.mem dst (MH.major_objects major) /\
         MH.read_word_in_major major (hd_address src) == Some hdr /\
         Obj.getColor hdr <> GC.Lib.Header.Blue /\
         U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
         j < U64.v (Obj.getWosize hdr) /\
         U64.v field_addr == U64.v src + j * U64.v mword /\
         CG.chunked_major_field_slot src j == Some field_addr /\
         MH.read_word_in_major major field_addr == Some old /\
         old == dst /\
         ~(is_minor_pointer (to_minor_offset old) /\
           collect.cmc_fwd (to_minor_offset old) <> 0UL)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MajorV src, CG.MajorV dst)
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_old_major_nonforwarded_field_edge
    minor major fp roots alloc_fuel fresh src dst hdr j field_addr old

let spot_chunked_cheney_gc_correct_after_preflight_old_major_forwarded_minor_field_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src expected: obj_addr) (hdr: U64.t) (j: nat)
  (field_addr: hp_addr) (old: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let x = to_minor_offset old in
         Seq.mem src (MH.major_objects major) /\
         MH.read_word_in_major major (hd_address src) == Some hdr /\
         Obj.getColor hdr <> GC.Lib.Header.Blue /\
         U64.v (Obj.getTag hdr) < U64.v Obj.no_scan_tag /\
         j < U64.v (Obj.getWosize hdr) /\
         U64.v field_addr == U64.v src + j * U64.v mword /\
         CG.chunked_major_field_slot src j == Some field_addr /\
         MH.read_word_in_major major field_addr == Some old /\
         is_minor_pointer x /\
         collect.cmc_fwd x <> 0UL /\
         collect.cmc_fwd x == expected /\
         Seq.mem expected (MH.major_objects collect.cmc_major)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         let x = to_minor_offset old in
         CG.mem_ce (CG.MajorV src, CG.MajorV expected)
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_old_major_forwarded_minor_field_edge
    minor major fp roots alloc_fuel fresh src expected hdr j field_addr old

let spot_chunked_cheney_gc_correct_after_preflight_old_major_major_graph_edge_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src dst: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
          CG.mem_ce (CG.MajorV src, CG.MajorV dst)
          (CG.build_chunked_combined_graph minor major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         ~(is_minor_pointer (to_minor_offset dst) /\
           collect.cmc_fwd (to_minor_offset dst) <> 0UL)))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MajorV src, CG.MajorV dst)
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_old_major_major_graph_edge_maps_to_major_edge
    minor major fp roots alloc_fuel fresh src dst hdr

let spot_chunked_cheney_gc_correct_after_preflight_old_major_minor_graph_edge_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (src: obj_addr) (dst: U64.t) (hdr: U64.t)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CG.mem_ce (CG.MajorV src, CG.MinorV dst)
          (CG.build_chunked_combined_graph minor major) /\
        MH.read_word_in_major major (hd_address src) == Some hdr /\
        Obj.getColor hdr <> GC.Lib.Header.Blue /\
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         collect.cmc_fwd dst <> 0UL))
      (ensures
        (let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp alloc_fuel needed fresh in
         let collect =
           ChunkedCheney.chunked_cheney_collect_spec
             minor r.capacity_major_out r.capacity_fp_out roots
             r.capacity_fuel_out in
         CG.mem_ce (CG.MajorV src, CG.MajorV (collect.cmc_fwd dst))
          (CG.build_chunked_combined_graph
            collect.cmc_minor collect.cmc_major)))
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_old_major_minor_graph_edge_maps_to_major_edge
    minor major fp roots alloc_fuel fresh src dst hdr

let spot_chunked_cheney_gc_correct_after_preflight_graph_edge_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
        CheneyCorrectness.chunked_graph_edge_maps_to_major_ready
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
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_edge_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_vertex_maps_to_major_vertex
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyCorrectness.chunked_graph_vertex_maps_to_major_ready
          minor major roots u)
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
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_vertex_maps_to_major_vertex
    minor major fp roots alloc_fuel fresh u

let spot_chunked_cheney_gc_correct_after_preflight_graph_vertices_map_to_major_vertices
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyCorrectness.chunked_graph_vertices_map_to_major_vertices_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_vertices_map_to_major_vertices
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_graph_edges_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyCorrectness.chunked_graph_edges_map_to_major_edges_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_edges_map_to_major_edges
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_graph_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyCorrectness.chunked_graph_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_maps_to_major_graph
    minor major fp roots alloc_fuel fresh

let spot_chunked_graph_edge_maps_to_major_above_minor_targets_ready_implies_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        CheneyCorrectness.chunked_graph_edge_maps_to_major_above_minor_targets_ready
          minor major fp roots alloc_fuel fresh u v)
      (ensures
        CheneyCorrectness.chunked_graph_edge_maps_to_major_ready
          minor major fp roots alloc_fuel fresh u v)
  =
  CheneyCorrectness.chunked_graph_edge_maps_to_major_above_minor_targets_ready_implies_ready
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edge_above_minor_targets_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
        CheneyCorrectness.chunked_graph_edge_maps_to_major_above_minor_targets_ready
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
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_edge_above_minor_targets_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edges_above_minor_targets_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyCorrectness.chunked_graph_edges_above_minor_targets_map_to_major_edges_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_edges_above_minor_targets_map_to_major_edges
    minor major fp roots alloc_fuel fresh

let spot_chunked_graph_edge_maps_to_major_nonblue_sources_above_minor_targets_ready_implies_above_minor_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        CheneyCorrectness.chunked_graph_edge_maps_to_major_nonblue_sources_above_minor_targets_ready
          minor major fp roots alloc_fuel fresh u v)
      (ensures
        CheneyCorrectness.chunked_graph_edge_maps_to_major_above_minor_targets_ready
          minor major fp roots alloc_fuel fresh u v)
  =
  CheneyCorrectness.chunked_graph_edge_maps_to_major_nonblue_sources_above_minor_targets_ready_implies_above_minor_targets_ready
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edge_nonblue_sources_above_minor_targets_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
        CheneyCorrectness.chunked_graph_edge_maps_to_major_nonblue_sources_above_minor_targets_ready
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
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_edge_nonblue_sources_above_minor_targets_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edges_nonblue_sources_above_minor_targets_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyCorrectness.chunked_graph_edges_nonblue_sources_above_minor_targets_map_to_major_edges_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyCorrectness.chunked_cheney_gc_correct_after_preflight_graph_edges_nonblue_sources_above_minor_targets_map_to_major_edges
    minor major fp roots alloc_fuel fresh

let spot_chunked_graph_edge_maps_to_major_edge_targets_ready_implies_nonblue_sources_above_minor_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
        CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_edge_targets_ready
          minor major fp roots alloc_fuel fresh u v)
      (ensures
        CheneyCorrectness.chunked_graph_edge_maps_to_major_nonblue_sources_above_minor_targets_ready
          minor major fp roots alloc_fuel fresh u v)
  =
  CheneyGraphReadiness.chunked_graph_edge_maps_to_major_edge_targets_ready_implies_nonblue_sources_above_minor_targets_ready
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_major_chunks_above_minor_objects_above_minor
  (major: MH.major_heap)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_chunks_above_minor major)
      (ensures
        CheneyGraphReadiness.chunked_major_objects_above_minor major)
  =
  CheneyGraphReadiness.chunked_major_chunks_above_minor_objects_above_minor
    major

let spot_chunked_major_objects_above_minor_single_chunk
  (g: heap)
  : Lemma
      (ensures
        CheneyGraphReadiness.chunked_major_objects_above_minor
          (MH.single_chunk_major_heap g))
  =
  CheneyGraphReadiness.chunked_major_objects_above_minor_single_chunk g

let spot_chunked_major_objects_above_minor_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
        U64.v fresh.base >= minor_heap_size)
      (ensures
        CheneyGraphReadiness.chunked_major_objects_above_minor
          (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  CheneyGraphReadiness.chunked_major_objects_above_minor_expand_major_heap
    major fresh fp

let spot_chunked_major_objects_above_minor_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
        (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
         U64.v fresh.base >= U64.v zero_addr))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp fuel needed fresh in
         CheneyGraphReadiness.chunked_major_objects_above_minor
           r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_major_objects_above_minor_ensure_head_capacity
    major fp fuel needed fresh

let spot_chunked_major_chunks_above_zero_addr_objects_are_pointer_fields
  (major: MH.major_heap)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major)
      (ensures
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major)
  =
  CheneyGraphReadiness.chunked_major_chunks_above_zero_addr_objects_are_pointer_fields
    major

let spot_chunked_major_chunks_above_zero_addr_single_chunk
  (g: heap)
  : Lemma
      (ensures
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
          (MH.single_chunk_major_heap g))
  =
  CheneyGraphReadiness.chunked_major_chunks_above_zero_addr_single_chunk g

let spot_chunked_major_chunks_above_zero_addr_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
        U64.v fresh.base >= U64.v zero_addr)
      (ensures
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
          (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  CheneyGraphReadiness.chunked_major_chunks_above_zero_addr_expand_major_heap
    major fresh fp

let spot_chunked_major_chunks_above_zero_addr_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
        (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
         U64.v fresh.base >= U64.v zero_addr))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp fuel needed fresh in
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
           r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_major_chunks_above_zero_addr_ensure_head_capacity
    major fp fuel needed fresh

let spot_chunked_major_chunks_above_zero_addr_chunks_above_minor
  (major: MH.major_heap)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major)
      (ensures
        CheneyGraphReadiness.chunked_major_chunks_above_minor major)
  =
  CheneyGraphReadiness.chunked_major_chunks_above_zero_addr_chunks_above_minor
    major

let spot_chunked_major_chunks_above_zero_addr_objects_above_minor
  (major: MH.major_heap)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major)
      (ensures
        CheneyGraphReadiness.chunked_major_objects_above_minor major)
  =
  CheneyGraphReadiness.chunked_major_chunks_above_zero_addr_objects_above_minor
    major

let spot_chunked_major_objects_are_pointer_fields_single_chunk
  (g: heap)
  : Lemma
      (ensures
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
          (MH.single_chunk_major_heap g))
  =
  CheneyGraphReadiness.chunked_major_objects_are_pointer_fields_single_chunk g

let spot_chunked_major_objects_are_pointer_fields_expand_major_heap
  (major: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major /\
        U64.v fresh.base >= U64.v zero_addr)
      (ensures
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
          (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  CheneyGraphReadiness.chunked_major_objects_are_pointer_fields_expand_major_heap
    major fresh fp

let spot_chunked_major_objects_are_pointer_fields_ensure_head_capacity
  (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (needed: nat{needed > 0}) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major /\
        (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
         U64.v fresh.base >= U64.v zero_addr))
      (ensures
        (let r =
           SpecMajorAlloc.ensure_major_head_capacity_spec
             major fp fuel needed fresh in
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
           r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_major_objects_are_pointer_fields_ensure_head_capacity
    major fp fuel needed fresh

let spot_chunked_major_edge_gen_field_witness_from_readiness_pointer_fields
  (major: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major)
      (ensures
        GenMajorGCBridge.chunked_major_edge_gen_field_witness major)
  =
  CheneyGraphReadiness.chunked_major_edge_gen_field_witness_from_pointer_fields
    major

let spot_chunked_major_edge_gen_field_witness_from_chunk_bases
  (major: MH.major_heap)
  : Lemma
      (requires
        MH.well_formed_major_heap major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major)
      (ensures
        GenMajorGCBridge.chunked_major_edge_gen_field_witness major)
  =
  CheneyGraphReadiness.chunked_major_edge_gen_field_witness_from_chunk_bases
    major

let spot_chunked_cheney_gc_correct_after_preflight_graph_edge_edge_targets_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_edge_targets_ready
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
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_edge_edge_targets_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edges_edge_targets_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_edges_edge_targets_map_to_major_edges_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_edges_edge_targets_map_to_major_edges
    minor major fp roots alloc_fuel fresh

let spot_chunked_graph_edge_maps_to_major_reachable_targets_ready_implies_edge_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_reachable_targets_ready
          minor major fp roots alloc_fuel fresh u v)
      (ensures
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_edge_targets_ready
          minor major fp roots alloc_fuel fresh u v)
  =
  CheneyGraphReadiness.chunked_graph_edge_maps_to_major_reachable_targets_ready_implies_edge_targets_ready
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edge_reachable_targets_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_reachable_targets_ready
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
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_edge_reachable_targets_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edges_reachable_targets_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_edges_reachable_targets_map_to_major_edges_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_edges_reachable_targets_map_to_major_edges
    minor major fp roots alloc_fuel fresh

let spot_chunked_graph_vertex_maps_to_major_membership_ready_implies_ready
  (minor: minor_state) (major: MH.major_heap) (roots: Seq.seq U64.t)
  (u: CG.combined_vertex)
  : Lemma
      (requires
        CG.mem_cv u (CG.build_chunked_combined_graph minor major) /\
        CheneyGraphReadiness.chunked_graph_vertex_maps_to_major_membership_ready
          minor roots u)
      (ensures
        CheneyCorrectness.chunked_graph_vertex_maps_to_major_ready
          minor major roots u)
  =
  CheneyGraphReadiness.chunked_graph_vertex_maps_to_major_membership_ready_implies_ready
    minor major roots u

let spot_chunked_cheney_gc_correct_after_preflight_graph_vertex_membership_ready_maps_to_major_vertex
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyGraphReadiness.chunked_graph_vertex_maps_to_major_membership_ready
          minor roots u)
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
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_vertex_membership_ready_maps_to_major_vertex
    minor major fp roots alloc_fuel fresh u

let spot_chunked_cheney_gc_correct_after_preflight_graph_vertices_membership_ready_map_to_major_vertices
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyGraphReadiness.chunked_graph_vertices_membership_ready_map_to_major_vertices_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_vertices_membership_ready_map_to_major_vertices
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_graph_membership_ready_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_membership_ready_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_membership_ready_maps_to_major_graph
    minor major fp roots alloc_fuel fresh

let spot_chunked_minor_source_edge_not_no_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (src: U64.t) (dst: CG.combined_vertex)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major /\
        CG.mem_ce (CG.MinorV src, dst)
          (CG.build_chunked_combined_graph minor major))
      (ensures
        minor_tag minor src < U64.v GC.Spec.Object.no_scan_tag)
  =
  CheneyGraphReadiness.chunked_minor_source_edge_not_no_scan
    minor major fp fuel src dst

let spot_chunked_graph_edge_maps_to_major_live_selected_ready_implies_selected_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t) (u v: CG.combined_vertex)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major /\
        CG.mem_ce (u, v) (CG.build_chunked_combined_graph minor major) /\
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_live_selected_ready
          minor major roots u v)
      (ensures
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_selected_ready
          minor major roots u v)
  =
  CheneyGraphReadiness.chunked_graph_edge_maps_to_major_live_selected_ready_implies_selected_ready
    minor major fp fuel roots u v

let spot_chunked_live_selected_graph_edge_implies_live_selected_ready
  (minor: minor_state) (major: MH.major_heap) (roots: Seq.seq U64.t)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_live_selected_graph_edge
          minor major roots u v)
      (ensures
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_live_selected_ready
          minor major roots u v)
  =
  CheneyGraphReadiness.chunked_live_selected_graph_edge_implies_live_selected_ready
    minor major roots u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edge_live_selected_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major /\
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
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_live_selected_ready
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
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_edge_live_selected_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_reachable_major_valid_nonblue
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CReach.chunked_major_objects_are_pointer_fields major)
      (ensures
        (let cg = CG.build_chunked_combined_graph minor major in
         let combined_roots = CG.classify_roots roots in
         forall (v: U64.t).
           CG.combined_reachable cg combined_roots (CG.MajorV v) ==>
           U64.v v >= U64.v mword /\
           U64.v v < heap_size /\
           U64.v v % U64.v mword == 0 /\
           Seq.mem (v <: obj_addr) (MH.major_objects major) /\
           ~(GenInv.chunked_is_blue major (v <: obj_addr))))
  =
  CReach.chunked_reachable_major_valid_nonblue
    minor major fp fuel roots

let spot_chunked_roots_valid_nonblue_single_chunk_compat
  (roots: Seq.seq U64.t) (major: heap)
  : Lemma
      (requires RBridge.roots_valid_nonblue roots major)
      (ensures
        CReach.chunked_roots_valid_nonblue
          roots (MH.single_chunk_major_heap major))
  =
  CReach.chunked_roots_valid_nonblue_single_chunk_compat
    roots major

let spot_chunked_roots_valid_nonblue_preserved_by_expansion
  (roots: Seq.seq U64.t) (major: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires
        CReach.chunked_roots_valid_nonblue roots major /\
        CReach.chunked_roots_disjoint_from_chunk roots fresh /\
        MH.chunk_disjoint_from_all fresh major)
      (ensures
        CReach.chunked_roots_valid_nonblue
          roots (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  CReach.chunked_roots_valid_nonblue_preserved_by_expansion
    roots major fresh fp

let spot_chunked_roots_valid_nonblue_ensure_head_capacity
  (roots: Seq.seq U64.t) (major: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CReach.chunked_roots_valid_nonblue roots major /\
        (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
          CReach.chunked_roots_disjoint_from_chunk roots fresh /\
          MH.chunk_disjoint_from_all fresh major))
      (ensures
        CReach.chunked_roots_valid_nonblue
          roots
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp fuel needed fresh).capacity_major_out)
  =
  CReach.chunked_roots_valid_nonblue_ensure_head_capacity
    roots major fp fuel needed fresh

let spot_chunked_roots_valid_nonblue_append_minor_pointers
  (roots suffix: Seq.seq U64.t) (major: MH.major_heap)
  : Lemma
      (requires
        CReach.chunked_roots_valid_nonblue roots major /\
        CReach.chunked_roots_all_minor_pointers suffix)
      (ensures
        CReach.chunked_roots_valid_nonblue
          (Seq.append roots suffix) major)
  =
  CReach.chunked_roots_valid_nonblue_append_minor_pointers
    roots suffix major

let spot_chunked_roots_disjoint_from_chunk_minor_pointers_above_zero
  (roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CReach.chunked_roots_all_minor_pointers roots /\
        U64.v fresh.base >= U64.v zero_addr)
      (ensures CReach.chunked_roots_disjoint_from_chunk roots fresh)
  =
  CReach.chunked_roots_disjoint_from_chunk_minor_pointers_above_zero
    roots fresh

let spot_chunked_roots_valid_nonblue_collection_roots_ensure_head_capacity
  (minor: minor_state) (major: MH.major_heap) (roots: Seq.seq U64.t)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CReach.chunked_roots_valid_nonblue roots major /\
        (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
          CReach.chunked_roots_disjoint_from_chunk roots fresh /\
          MH.chunk_disjoint_from_all fresh major))
      (ensures
        CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor major roots)
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp fuel needed fresh).capacity_major_out)
  =
  CRem.chunked_roots_valid_nonblue_collection_roots_ensure_head_capacity
    minor major roots fp fuel needed fresh

let spot_chunked_collection_roots_disjoint_from_chunk
  (minor: minor_state) (major: MH.major_heap) (roots: Seq.seq U64.t)
  (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CReach.chunked_roots_disjoint_from_chunk roots fresh /\
        U64.v fresh.base >= U64.v zero_addr)
      (ensures
        CReach.chunked_roots_disjoint_from_chunk
          (CRem.chunked_minor_collection_roots minor major roots) fresh)
  =
  CRem.chunked_collection_roots_disjoint_from_chunk
    minor major roots fresh

let spot_chunked_major_field_zero_no_minor_single_chunk_compat
  (minor: minor_state) (major: heap)
  : Lemma
      (requires RBridge.major_field_zero_no_minor minor major)
      (ensures
        CReach.chunked_major_field_zero_no_minor
          minor (MH.single_chunk_major_heap major))
  =
  CReach.chunked_major_field_zero_no_minor_single_chunk_compat
    minor major

let spot_chunked_major_field_zero_no_minor_preserved_by_expansion
  (minor: minor_state) (major: MH.major_heap)
  (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires
        CReach.chunked_major_field_zero_no_minor minor major /\
        MH.chunk_disjoint_from_all fresh major /\
        CG.chunked_all_major_object_expansion_safe
          major fresh (MH.major_objects major) 0)
      (ensures
        CReach.chunked_major_field_zero_no_minor
          minor (SpecMajorAlloc.expand_major_heap major fresh fp).major_out)
  =
  CReach.chunked_major_field_zero_no_minor_preserved_by_expansion
    minor major fresh fp

let spot_chunked_major_field_zero_no_minor_ensure_head_capacity
  (minor: minor_state) (major: MH.major_heap)
  (fp: U64.t) (fuel: nat) (needed: nat{needed > 0})
  (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CReach.chunked_major_field_zero_no_minor minor major /\
        (SpecMajorAlloc.major_fl_head_wosize major fp < needed ==>
          MH.chunk_disjoint_from_all fresh major /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0))
      (ensures
        CReach.chunked_major_field_zero_no_minor
          minor
          (SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp fuel needed fresh).capacity_major_out)
  =
  CReach.chunked_major_field_zero_no_minor_ensure_head_capacity
    minor major fp fuel needed fresh

let spot_chunked_reachable_major_vertex_live_selected
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t) (v: U64.t)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major /\
        CG.combined_reachable
          (CG.build_chunked_combined_graph minor major)
          (CG.classify_roots roots)
          (CG.MajorV v))
      (ensures
        CheneyGraphReadiness.chunked_live_selected_graph_vertex
          minor major roots (CG.MajorV v))
  =
  CheneyGraphReadiness.chunked_reachable_major_vertex_live_selected
    minor major fp fuel roots v

let spot_chunked_reachable_major_vertex_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t) (v: U64.t)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
        CG.combined_reachable
          (CG.build_chunked_combined_graph minor major)
          (CG.classify_roots roots)
          (CG.MajorV v))
      (ensures
        CheneyGraphReadiness.chunked_live_selected_graph_vertex
          minor major roots (CG.MajorV v))
  =
  CheneyGraphReadiness.chunked_reachable_major_vertex_live_selected_from_chunk_bases
    minor major fp fuel roots v

let spot_chunked_combined_minor_reachable_in_minor_reachable
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CReach.chunked_major_objects_are_pointer_fields major /\
        CReach.chunked_major_field_zero_no_minor minor major /\
        CReach.chunked_remembered_minor_edges_in_roots minor major roots)
      (ensures
        (let cg = CG.build_chunked_combined_graph minor major in
         let combined_roots = CG.classify_roots roots in
         forall (v: U64.t).
           CG.combined_reachable cg combined_roots (CG.MinorV v) ==>
           Seq.mem v (minor_reachable minor roots)))
  =
  CReach.chunked_combined_minor_reachable_in_minor_reachable
    minor major fp fuel roots

let spot_chunked_reachable_positive_minor_vertex_live_selected
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t) (v: U64.t)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major /\
        CReach.chunked_major_field_zero_no_minor minor major /\
        CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
        CG.combined_reachable
          (CG.build_chunked_combined_graph minor major)
          (CG.classify_roots roots)
          (CG.MinorV v) /\
        minor_wosize minor v > 0)
      (ensures
        CheneyGraphReadiness.chunked_live_selected_graph_vertex
          minor major roots (CG.MinorV v))
  =
  CheneyGraphReadiness.chunked_reachable_positive_minor_vertex_live_selected
    minor major fp fuel roots v

let spot_chunked_reachable_positive_minor_vertex_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t) (v: U64.t)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
        CReach.chunked_major_field_zero_no_minor minor major /\
        CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
        CG.combined_reachable
          (CG.build_chunked_combined_graph minor major)
          (CG.classify_roots roots)
          (CG.MinorV v) /\
        minor_wosize minor v > 0)
      (ensures
        CheneyGraphReadiness.chunked_live_selected_graph_vertex
          minor major roots (CG.MinorV v))
  =
  CheneyGraphReadiness.chunked_reachable_positive_minor_vertex_live_selected_from_chunk_bases
    minor major fp fuel roots v

let spot_chunked_reachable_live_graph_vertex_implies_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t) (u: CG.combined_vertex)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
        CReach.chunked_major_field_zero_no_minor minor major /\
        CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
        CheneyGraphReadiness.chunked_reachable_live_graph_vertex
          minor major roots u)
      (ensures
        CheneyGraphReadiness.chunked_live_selected_graph_vertex
          minor major roots u)
  =
  CheneyGraphReadiness.chunked_reachable_live_graph_vertex_implies_live_selected_from_chunk_bases
    minor major fp fuel roots u

let spot_chunked_minor_roots_from_major_complete
  (minor: minor_state) (major: MH.major_heap) (src: obj_addr)
  (i: nat) (field_addr: hp_addr) (raw v: U64.t)
  : Lemma
      (requires
        Seq.mem src (MH.major_objects major) /\
        ~(GenInv.chunked_is_blue major src) /\
        CG.chunked_is_no_scan major src == false /\
        i <> 0 /\
        i < CG.chunked_wosize_nat_of_object major src /\
        CG.chunked_major_field_slot src i == Some field_addr /\
        MH.read_word_in_major major field_addr == Some raw /\
        CG.chunked_classify_major_field minor major raw ==
          Some (CG.MinorV v))
      (ensures
        Seq.mem v (CRem.chunked_minor_roots_from_major minor major))
  =
  CRem.chunked_minor_roots_from_major_complete
    minor major src i field_addr raw v

let spot_chunked_remembered_minor_edges_in_roots_from_scan
  (minor: minor_state) (major: MH.major_heap) (roots: Seq.seq U64.t)
  : Lemma
      (requires CRem.chunked_minor_roots_in_roots minor major roots)
      (ensures CReach.chunked_remembered_minor_edges_in_roots minor major roots)
  =
  CRem.chunked_remembered_minor_edges_in_roots_from_scan minor major roots

let spot_chunked_minor_roots_in_collection_roots
  (minor: minor_state) (major: MH.major_heap) (roots: Seq.seq U64.t)
  : Lemma
      (ensures
        CRem.chunked_minor_roots_in_roots
          minor major (CRem.chunked_minor_collection_roots minor major roots))
  =
  CRem.chunked_minor_roots_in_collection_roots minor major roots

let spot_chunked_reachable_live_graph_edge_implies_live_selected_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t) (fuel: nat)
  (roots: Seq.seq U64.t) (u v: CG.combined_vertex)
  : Lemma
      (requires
        GenInv.chunked_collection_heap_shape minor major fp fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
        CReach.chunked_major_field_zero_no_minor minor major /\
        CReach.chunked_remembered_minor_edges_in_roots minor major roots /\
        CheneyGraphReadiness.chunked_reachable_live_graph_edge
          minor major roots u v)
      (ensures
        CheneyGraphReadiness.chunked_live_selected_graph_edge
          minor major roots u v)
  =
  CheneyGraphReadiness.chunked_reachable_live_graph_edge_implies_live_selected_from_chunk_bases
    minor major fp fuel roots u v

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scan
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_minor_images_injective_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_minor_images_injective_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_minor_images_injective_from_chunk_bases_and_scan
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_minor_images_disjoint_from_major_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_minor_images_disjoint_from_major_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_minor_images_disjoint_from_major_from_chunk_bases_and_scan
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scanned_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor major base_roots) major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_maps_to_major_graph_prop
          minor major fp
          (CRem.chunked_minor_collection_roots minor major base_roots)
          alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_maps_to_major_graph_from_chunk_bases_and_scanned_roots
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_reachable_live_graph_image_isomorphism_from_injective
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_reachable_live_graph_injective_prop
          minor major fp roots alloc_fuel fresh)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_image_isomorphism_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_reachable_live_graph_image_isomorphism_from_injective
    minor major fp roots alloc_fuel fresh

let spot_chunked_reachable_live_graph_image_subgraph_of_post_major_graph_from_maps
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_reachable_live_graph_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_reachable_live_graph_image_subgraph_of_post_major_graph_from_maps
    minor major fp roots alloc_fuel fresh

let spot_chunked_reachable_live_graph_injective_from_minor_image_facts
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_reachable_live_minor_images_injective_prop
          minor major fp roots alloc_fuel fresh /\
        CheneyGraphReadiness.chunked_reachable_live_minor_images_disjoint_from_major_prop
          minor major fp roots alloc_fuel fresh)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_injective_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_reachable_live_graph_injective_from_minor_image_facts
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_injective_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_injective_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_injective_from_chunk_bases_and_scan
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_isomorphism_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_image_isomorphism_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_isomorphism_from_chunk_bases_and_scan
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_subgraph_of_post_major_graph_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_subgraph_of_post_major_graph_from_chunk_bases_and_scan
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_root_images_in_post_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_root_images_in_post_roots_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_root_images_in_post_roots
    minor major fp roots alloc_fuel fresh

let spot_chunked_reachable_live_graph_image_reachable_in_post_major_graph_from_roots_and_subgraph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_reachable_live_graph_root_images_in_post_roots_prop
          minor major fp roots alloc_fuel fresh /\
        CheneyGraphReadiness.chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
          minor major fp roots alloc_fuel fresh)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_image_reachable_in_post_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_reachable_live_graph_image_reachable_in_post_major_graph_from_roots_and_subgraph
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_reachable_in_post_major_graph_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_image_reachable_in_post_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_image_reachable_in_post_major_graph_from_chunk_bases_and_scan
    minor major fp roots alloc_fuel fresh

let spot_chunked_reachable_live_graph_post_reachable_image_isomorphism_from_image_facts
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_reachable_live_graph_image_isomorphism_prop
          minor major fp roots alloc_fuel fresh /\
        CheneyGraphReadiness.chunked_reachable_live_graph_image_subgraph_of_post_major_graph_prop
          minor major fp roots alloc_fuel fresh /\
        CheneyGraphReadiness.chunked_reachable_live_graph_image_reachable_in_post_major_graph_prop
          minor major fp roots alloc_fuel fresh)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_from_image_facts
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_scan
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_scan
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_scanned_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor major base_roots) major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor major fp
          (CRem.chunked_minor_collection_roots minor major base_roots)
          alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_scanned_roots
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_base_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue base_roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor major fp
          (CRem.chunked_minor_collection_roots minor major base_roots)
          alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_reachable_live_graph_post_reachable_image_isomorphism_from_chunk_bases_and_base_roots
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_policy_and_post_reachable_image_from_base_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue base_roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor major fp
          (CRem.chunked_minor_collection_roots minor major base_roots)
          alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
           r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
           r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
           minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_policy_and_post_reachable_image_from_base_roots
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_base_roots
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue base_roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
        CReach.chunked_major_field_zero_no_minor minor major /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            major fresh (MH.major_objects major) 0))
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor major fp
          (CRem.chunked_minor_collection_roots minor major base_roots)
          alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue
           base_roots r.capacity_major_out /\
          CReach.chunked_roots_valid_nonblue
            (CRem.chunked_minor_collection_roots minor major base_roots)
            r.capacity_major_out /\
          (SpecMajorAlloc.major_fl_head_wosize major fp <
           PromotionDemand.minor_promotion_demand minor + 1 ==>
           CReach.chunked_roots_disjoint_from_chunk
             (CRem.chunked_minor_collection_roots minor major base_roots)
             fresh) /\
          CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
            r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
           r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
           minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_base_roots
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_base_roots_value_safety
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CReach.chunked_roots_valid_nonblue base_roots major /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
        CReach.chunked_major_field_zero_no_minor minor major /\
        (SpecMajorAlloc.major_fl_head_wosize major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
          MH.chunk_disjoint_from_all fresh major /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          (forall (obj:obj_addr).
            Seq.mem obj (MH.major_objects major) ==>
              CG.chunked_major_field_values_miss_fresh
                major fresh obj
                (CG.chunked_wosize_nat_of_object major obj) 0)))
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor major fp
          (CRem.chunked_minor_collection_roots minor major base_roots)
          alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue
           base_roots r.capacity_major_out /\
          CReach.chunked_roots_valid_nonblue
            (CRem.chunked_minor_collection_roots minor major base_roots)
            r.capacity_major_out /\
          (SpecMajorAlloc.major_fl_head_wosize major fp <
            PromotionDemand.minor_promotion_demand minor + 1 ==>
            CReach.chunked_roots_disjoint_from_chunk
              (CRem.chunked_minor_collection_roots minor major base_roots)
              fresh) /\
          CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
            r.capacity_major_out /\
          CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
            r.capacity_major_out /\
          CReach.chunked_major_field_zero_no_minor
            minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_base_roots_value_safety
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_minor_preflight_value_policy_core_expansion_safety
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp base_roots fresh)
      (ensures
        (SpecMajorAlloc.major_fl_head_wosize major fp <
         PromotionDemand.minor_promotion_demand minor + 1 ==>
         MH.chunk_disjoint_from_all fresh major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >=
           PromotionDemand.minor_promotion_demand minor + 1 /\
         (forall (obj:obj_addr).
           Seq.mem obj (MH.major_objects major) ==>
             CG.chunked_major_field_values_miss_fresh
               major fresh obj (CG.chunked_wosize_nat_of_object major obj) 0)))
  =
  CheneyGraphReadiness.chunked_minor_preflight_value_policy_core_expansion_safety
    minor major fp base_roots fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_preflight_value_policy
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor major fp base_roots fresh)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor major fp
          (CRem.chunked_minor_collection_roots minor major base_roots)
          alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue
           base_roots r.capacity_major_out /\
          CReach.chunked_roots_valid_nonblue
            (CRem.chunked_minor_collection_roots minor major base_roots)
            r.capacity_major_out /\
          (SpecMajorAlloc.major_fl_head_wosize major fp <
            PromotionDemand.minor_promotion_demand minor + 1 ==>
            CReach.chunked_roots_disjoint_from_chunk
              (CRem.chunked_minor_collection_roots minor major base_roots)
              fresh) /\
          CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
            r.capacity_major_out /\
          CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
            r.capacity_major_out /\
          CReach.chunked_major_field_zero_no_minor
            minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_from_preflight_value_policy
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_minor_preflight_value_policy_single_chunk_from_dense
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
         (forall (obj:obj_addr).
          Seq.mem obj (MH.major_objects chunked_major) ==>
            CG.chunked_major_field_values_miss_fresh
              chunked_major fresh obj
              (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
      (ensures
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor (MH.single_chunk_major_heap major) fp base_roots fresh)
  =
  CheneyGraphReadiness.chunked_minor_preflight_value_policy_single_chunk_from_dense
    minor major fp base_roots fresh

let spot_chunked_major_field_values_miss_fresh_single_chunk_from_dense_wf
  (major: heap) (fresh: MH.heap_chunk) (src: obj_addr)
  : Lemma
      (requires
        Fields.well_formed_heap major /\
        MH.chunk_disjoint_from_all fresh (MH.single_chunk_major_heap major) /\
        U64.v fresh.base >= U64.v zero_addr /\
        Seq.mem src (MH.major_objects (MH.single_chunk_major_heap major)))
      (ensures
        CG.chunked_major_field_values_miss_fresh
          (MH.single_chunk_major_heap major) fresh src
          (CG.chunked_wosize_nat_of_object (MH.single_chunk_major_heap major) src)
          0)
  =
  CheneyGraphReadiness.chunked_major_field_values_miss_fresh_single_chunk_from_dense_wf
    major fresh src

let spot_chunked_minor_preflight_value_policy_single_chunk_from_dense_wf
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        Fields.well_formed_heap major /\
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures
        CheneyGraphReadiness.chunked_minor_preflight_value_policy
          minor (MH.single_chunk_major_heap major) fp base_roots fresh)
  =
  CheneyGraphReadiness.chunked_minor_preflight_value_policy_single_chunk_from_dense_wf
    minor major fp base_roots fresh

let spot_chunked_cheney_promote_after_minor_promotion_head_preflight_single_chunk_from_dense_value_safety
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
         (forall (obj:obj_addr).
          Seq.mem obj (MH.major_objects chunked_major) ==>
            CG.chunked_major_field_values_miss_fresh
              chunked_major fresh obj
              (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
      (ensures
        CheneyGraphReadiness.chunked_cheney_promote_after_minor_promotion_head_preflight_post
          minor (MH.single_chunk_major_heap major) fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_promote_after_minor_promotion_head_preflight_single_chunk_from_dense_value_safety
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_value_safety
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
         (forall (obj:obj_addr).
          Seq.mem obj (MH.major_objects chunked_major) ==>
            CG.chunked_major_field_values_miss_fresh
              chunked_major fresh obj
              (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor (MH.single_chunk_major_heap major) fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_value_safety
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_promote_after_minor_promotion_head_preflight_single_chunk_from_dense_wf
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        Fields.well_formed_heap major /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures
        CheneyGraphReadiness.chunked_cheney_promote_after_minor_promotion_head_preflight_post
          minor (MH.single_chunk_major_heap major) fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_promote_after_minor_promotion_head_preflight_single_chunk_from_dense_wf
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_wf
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        Fields.well_formed_heap major /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor (MH.single_chunk_major_heap major) fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_wf
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_policy
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy
          minor major fp roots alloc_fuel fresh)
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor (MH.single_chunk_major_heap major) fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_policy
    minor major fp roots alloc_fuel fresh

let spot_fixed_heap_minor_collect_preflight_policy_from_dense_minor_collect_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures
        CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy
          minor major fp roots SpecAlloc.alloc_search_fuel fresh)
  =
  CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy_from_dense_minor_collect_preconditions
    minor major fp roots fresh

let spot_fixed_heap_minor_collect_preflight_policy_from_dense_minor_collect_preconditions_no_expansion
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap major) fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy
          minor major fp roots SpecAlloc.alloc_search_fuel fresh)
  =
  CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy_from_dense_minor_collect_preconditions_no_expansion
    minor major fp roots fresh

let spot_chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_minor_collect_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor (MH.single_chunk_major_heap major) fp roots
          SpecAlloc.alloc_search_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_minor_collect_preconditions
    minor major fp roots fresh

let spot_chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_minor_collect_preconditions_no_expansion
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap major) fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor (MH.single_chunk_major_heap major) fp roots
          SpecAlloc.alloc_search_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_minor_collect_preconditions_no_expansion
    minor major fp roots fresh

let spot_fixed_heap_minor_collect_preflight_policy_no_expansion
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        Fields.well_formed_heap major /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap major) fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy_no_expansion
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_no_expansion
  (minor: minor_state) (major: heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        Fields.well_formed_heap major /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap major) fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_post
          minor (MH.single_chunk_major_heap major) fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_collect_after_minor_promotion_head_preflight_single_chunk_from_dense_no_expansion
    minor major fp roots alloc_fuel fresh

let spot_fixed_heap_minor_collect_preflight_policy_core_expansion_safety
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy
          minor major fp base_roots alloc_fuel fresh)
      (ensures
        (let chunked_major = MH.single_chunk_major_heap major in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
         PromotionDemand.minor_promotion_demand minor + 1 ==>
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >=
           PromotionDemand.minor_promotion_demand minor + 1 /\
         (forall (obj:obj_addr).
           Seq.mem obj (MH.major_objects chunked_major) ==>
             CG.chunked_major_field_values_miss_fresh
               chunked_major fresh obj
               (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
  =
  CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy_core_expansion_safety
    minor major fp base_roots alloc_fuel fresh

let spot_fixed_heap_minor_collect_preflight_policy_core_expansion_safety_no_expansion
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        Fields.well_formed_heap major /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap major) fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        (let chunked_major = MH.single_chunk_major_heap major in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
         PromotionDemand.minor_promotion_demand minor + 1 ==>
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >=
           PromotionDemand.minor_promotion_demand minor + 1 /\
         (forall (obj:obj_addr).
           Seq.mem obj (MH.major_objects chunked_major) ==>
             CG.chunked_major_field_values_miss_fresh
               chunked_major fresh obj
               (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
  =
  CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy_core_expansion_safety_no_expansion
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_minor_preflight_value_policy_core_expansion_safety_single_chunk_from_dense
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
         (forall (obj:obj_addr).
          Seq.mem obj (MH.major_objects chunked_major) ==>
            CG.chunked_major_field_values_miss_fresh
              chunked_major fresh obj
              (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
      (ensures
        (let chunked_major = MH.single_chunk_major_heap major in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
         PromotionDemand.minor_promotion_demand minor + 1 ==>
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >=
           PromotionDemand.minor_promotion_demand minor + 1 /\
         (forall (obj:obj_addr).
           Seq.mem obj (MH.major_objects chunked_major) ==>
             CG.chunked_major_field_values_miss_fresh
               chunked_major fresh obj
               (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
  =
  CheneyGraphReadiness.chunked_minor_preflight_value_policy_core_expansion_safety_single_chunk_from_dense
    minor major fp base_roots fresh

let spot_chunked_cheney_gc_correct_after_preflight_policy_and_post_reachable_image_single_chunk_from_dense_roots
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap major) fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          MH.chunk_disjoint_from_all
            fresh (MH.single_chunk_major_heap major) /\
          fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
          U64.v fresh.base >= U64.v zero_addr /\
          SpecMajorAlloc.fresh_chunk_wosize fresh >=
            PromotionDemand.minor_promotion_demand minor + 1 /\
          CG.chunked_all_major_object_expansion_safe
            (MH.single_chunk_major_heap major) fresh
            (MH.major_objects (MH.single_chunk_major_heap major)) 0))
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor (MH.single_chunk_major_heap major) fp
          (CRem.chunked_minor_collection_roots
            minor (MH.single_chunk_major_heap major) base_roots)
          alloc_fuel fresh /\
        (let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            (MH.single_chunk_major_heap major) fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
           r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
           r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
           minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_policy_and_post_reachable_image_single_chunk_from_dense_roots
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_roots_value_safety
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed /\
         (forall (obj:obj_addr).
          Seq.mem obj (MH.major_objects chunked_major) ==>
            CG.chunked_major_field_values_miss_fresh
              chunked_major fresh obj
              (CG.chunked_wosize_nat_of_object chunked_major obj) 0)))
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor (MH.single_chunk_major_heap major) fp
          (CRem.chunked_minor_collection_roots
            minor (MH.single_chunk_major_heap major) base_roots)
          alloc_fuel fresh /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            chunked_major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
         CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
          r.capacity_major_out /\
         (SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          CReach.chunked_roots_disjoint_from_chunk
            (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
            fresh) /\
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
          r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
          r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
          minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_roots_value_safety
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_roots_wf
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        Fields.well_formed_heap major /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor (MH.single_chunk_major_heap major) fp
          (CRem.chunked_minor_collection_roots
            minor (MH.single_chunk_major_heap major) base_roots)
          alloc_fuel fresh /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            chunked_major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
         CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
          r.capacity_major_out /\
         (SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          CReach.chunked_roots_disjoint_from_chunk
            (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
            fresh) /\
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
          r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
          r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
          minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_roots_wf
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_policy
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        CheneyGraphReadiness.fixed_heap_minor_collect_preflight_policy
          minor major fp base_roots alloc_fuel fresh)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor (MH.single_chunk_major_heap major) fp
          (CRem.chunked_minor_collection_roots
            minor (MH.single_chunk_major_heap major) base_roots)
          alloc_fuel fresh /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            chunked_major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
         CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
          r.capacity_major_out /\
         (SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          CReach.chunked_roots_disjoint_from_chunk
            (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
            fresh) /\
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
          r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
          r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
          minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_policy
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_no_expansion
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        alloc_fuel > 1 /\
        Fields.well_formed_heap major /\
        alloc_fuel == SpecAlloc.alloc_search_fuel /\
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap major) fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor (MH.single_chunk_major_heap major) fp
          (CRem.chunked_minor_collection_roots
            minor (MH.single_chunk_major_heap major) base_roots)
          alloc_fuel fresh /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            chunked_major fp alloc_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
         CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
          r.capacity_major_out /\
         (SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          CReach.chunked_roots_disjoint_from_chunk
            (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
            fresh) /\
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
          r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
          r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
          minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_no_expansion
    minor major fp base_roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_minor_collect_preconditions
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let needed = PromotionDemand.minor_promotion_demand minor + 1 in
         SpecMajorAlloc.major_fl_head_wosize chunked_major fp < needed ==>
         CReach.chunked_roots_disjoint_from_chunk base_roots fresh /\
         MH.chunk_disjoint_from_all fresh chunked_major /\
         fp <> SpecMajorAlloc.fresh_chunk_object fresh /\
         U64.v fresh.base >= U64.v zero_addr /\
         SpecMajorAlloc.fresh_chunk_wosize fresh >= needed))
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor (MH.single_chunk_major_heap major) fp
          (CRem.chunked_minor_collection_roots
            minor (MH.single_chunk_major_heap major) base_roots)
          SpecAlloc.alloc_search_fuel fresh /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            chunked_major fp SpecAlloc.alloc_search_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
         CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
          r.capacity_major_out /\
         (SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          CReach.chunked_roots_disjoint_from_chunk
            (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
            fresh) /\
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
          r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
          r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
          minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_minor_collect_preconditions
    minor major fp base_roots fresh

let spot_chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_minor_collect_preconditions_no_expansion
  (minor: minor_state) (major: heap) (fp: U64.t)
  (base_roots: Seq.seq U64.t) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        GenInv.collection_heap_shape minor major fp /\
        RBridge.roots_valid_nonblue base_roots major /\
        RBridge.major_field_zero_no_minor minor major /\
        SpecMajorAlloc.major_fl_head_wosize
          (MH.single_chunk_major_heap major) fp >=
          PromotionDemand.minor_promotion_demand minor + 1)
      (ensures
        CheneyGraphReadiness.chunked_reachable_live_graph_post_reachable_image_isomorphism_prop
          minor (MH.single_chunk_major_heap major) fp
          (CRem.chunked_minor_collection_roots
            minor (MH.single_chunk_major_heap major) base_roots)
          SpecAlloc.alloc_search_fuel fresh /\
        (let chunked_major = MH.single_chunk_major_heap major in
         let r =
          SpecMajorAlloc.ensure_major_head_capacity_spec
            chunked_major fp SpecAlloc.alloc_search_fuel
            (PromotionDemand.minor_promotion_demand minor + 1) fresh in
         CReach.chunked_roots_valid_nonblue base_roots r.capacity_major_out /\
         CReach.chunked_roots_valid_nonblue
          (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
          r.capacity_major_out /\
         (SpecMajorAlloc.major_fl_head_wosize chunked_major fp <
          PromotionDemand.minor_promotion_demand minor + 1 ==>
          CReach.chunked_roots_disjoint_from_chunk
            (CRem.chunked_minor_collection_roots minor chunked_major base_roots)
            fresh) /\
         CheneyGraphReadiness.chunked_major_chunks_above_zero_addr
          r.capacity_major_out /\
         CheneyGraphReadiness.chunked_major_objects_are_pointer_fields
          r.capacity_major_out /\
         CReach.chunked_major_field_zero_no_minor
          minor r.capacity_major_out))
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_full_policy_and_post_reachable_image_single_chunk_from_dense_minor_collect_preconditions_no_expansion
    minor major fp base_roots fresh

let spot_chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
        CheneyGraphReadiness.chunked_major_objects_are_pointer_fields major /\
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
        CheneyGraphReadiness.chunked_live_selected_graph_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph_from_chunk_bases
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_chunks_above_zero_addr major /\
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
        CheneyGraphReadiness.chunked_live_selected_graph_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_live_selected_graph_maps_to_major_graph_from_chunk_bases
    minor major fp roots alloc_fuel fresh

let spot_chunked_graph_edge_maps_to_major_selected_ready_implies_reachable_targets_ready
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_selected_ready
          minor major roots u v)
      (ensures
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_reachable_targets_ready
          minor major fp roots alloc_fuel fresh u v)
  =
  CheneyGraphReadiness.chunked_graph_edge_maps_to_major_selected_ready_implies_reachable_targets_ready
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edge_selected_maps_to_major_edge
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  (u v: CG.combined_vertex)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_edge_maps_to_major_selected_ready
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
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_edge_selected_maps_to_major_edge
    minor major fp roots alloc_fuel fresh u v

let spot_chunked_cheney_gc_correct_after_preflight_graph_edges_selected_map_to_major_edges
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_edges_selected_map_to_major_edges_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_edges_selected_map_to_major_edges
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_graph_selected_ready_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_graph_selected_ready_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_graph_selected_ready_maps_to_major_graph
    minor major fp roots alloc_fuel fresh

let spot_chunked_cheney_gc_correct_after_preflight_selected_graph_maps_to_major_graph
  (minor: minor_state) (major: MH.major_heap) (fp: U64.t)
  (roots: Seq.seq U64.t) (alloc_fuel: nat) (fresh: MH.heap_chunk)
  : Lemma
      (requires
        minor_wf minor /\
        alloc_fuel > 1 /\
        GenInv.chunked_collection_heap_shape minor major fp alloc_fuel /\
        SpecMajorAlloc.major_fl_chain_terminates
          major fp alloc_fuel = true /\
        GenInv.chunked_chain_objects_blue major fp alloc_fuel /\
        CheneyGraphReadiness.chunked_major_objects_above_minor major /\
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
        CheneyGraphReadiness.chunked_selected_graph_maps_to_major_graph_prop
          minor major fp roots alloc_fuel fresh)
  =
  CheneyGraphReadiness.chunked_cheney_gc_correct_after_preflight_selected_graph_maps_to_major_graph
    minor major fp roots alloc_fuel fresh
