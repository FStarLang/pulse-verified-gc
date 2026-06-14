module GC.Spec.ChunkedMark.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap

module Header = GC.Lib.Header
module MH = GC.Spec.MajorHeap

val stack_objects_in_major
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : GTot prop

val stack_objects_in_major_elim
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  : Lemma
      (requires
        stack_objects_in_major mh st /\
        Seq.mem obj st)
      (ensures Seq.mem obj (MH.major_objects mh))

val stack_objects_in_major_tail
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        stack_objects_in_major mh st)
      (ensures stack_objects_in_major mh (Seq.tail st))

val stack_objects_in_major_preserved_by_major_objects
  (mh mh': MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        stack_objects_in_major mh st /\
        MH.major_objects mh' == MH.major_objects mh)
      (ensures stack_objects_in_major mh' st)

val chunked_set_object_color_member_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color) ==
        MH.major_objects mh)

val chunked_make_gray_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj) ==
        MH.major_objects mh)

val chunked_make_black_preserves_major_objects
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.major_objects (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj) ==
        MH.major_objects mh)

val chunked_set_object_color_member_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  (color: Header.color_sem)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_set_object_color
            mh obj color))

val chunked_make_gray_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMark.Defs.chunked_make_gray mh obj))

val chunked_make_black_preserves_well_formed
  (mh: MH.major_heap)
  (obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem obj (MH.major_objects mh))
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj))

val chunked_push_children_preservation_ready
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : GTot prop

val chunked_push_children_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMark.Defs.chunked_push_children mh st obj i ws in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_push_children_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMark.Defs.chunked_push_children mh st obj i ws in
         MH.well_formed_major_heap mh'))

val chunked_mark_step_empty_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires Seq.length st = 0)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_empty_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st = 0 /\
        MH.well_formed_major_heap mh)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))

val chunked_mark_step_empty_preserves_stack_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st = 0 /\
        stack_objects_in_major mh st)
      (ensures
        (let (mh', st') = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         stack_objects_in_major mh' st'))

val chunked_mark_step_no_scan_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_no_scan_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))

val chunked_mark_step_no_scan_preserves_stack_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        stack_objects_in_major mh st /\
        GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st))
      (ensures
        (let (mh', st') = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         stack_objects_in_major mh' st'))

val chunked_mark_step_scan_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st)) /\
        (let obj = Seq.head st in
         let mh' = GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj in
         let ws =
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object mh obj in
         chunked_push_children_preservation_ready mh' obj 1UL ws))
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_scan_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        Seq.mem (Seq.head st) (MH.major_objects mh) /\
        ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st)) /\
        (let obj = Seq.head st in
         let mh' = GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj in
         let ws =
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object mh obj in
         chunked_push_children_preservation_ready mh' obj 1UL ws))
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))

val chunked_mark_step_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : GTot prop

val chunked_mark_step_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_preservation_ready mh st)
      (ensures
        (let (mh', _) = GC.Spec.ChunkedMark.Defs.chunked_mark_step mh st in
         MH.well_formed_major_heap mh'))

val chunked_mark_aux_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : GTot prop

val chunked_mark_aux_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_aux_preservation_ready mh st fuel)
      (ensures
        MH.major_objects (GC.Spec.ChunkedMark.Defs.chunked_mark_aux mh st fuel) ==
        MH.major_objects mh)

val chunked_mark_aux_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_aux_preservation_ready mh st fuel)
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMark.Defs.chunked_mark_aux mh st fuel))

val chunked_mark_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : GTot prop

val chunked_mark_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_preservation_ready mh st)
      (ensures
        MH.major_objects (GC.Spec.ChunkedMark.Defs.chunked_mark mh st) ==
        MH.major_objects mh)

val chunked_mark_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_preservation_ready mh st)
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMark.Defs.chunked_mark mh st))
