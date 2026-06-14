module GC.Spec.ChunkedMarkBounded.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap

val chunked_push_children_bounded_preservation_ready
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : GTot prop

val chunked_push_children_bounded_preservation_ready_child
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        chunked_push_children_bounded_preservation_ready mh obj i ws /\
        (let v = GC.Spec.ChunkedMark.Defs.chunked_get_field mh obj i in
         GC.Spec.ChunkedMark.Defs.chunked_is_pointer_field mh v /\
         (let child_raw =
            GC.Spec.ChunkedMark.Defs.chunked_pointer_field_as_obj_addr mh v in
          let child =
            GC.Spec.ChunkedMark.Defs.chunked_resolve_object mh child_raw in
          GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh child)))
      (ensures
        (let v = GC.Spec.ChunkedMark.Defs.chunked_get_field mh obj i in
         let child_raw =
           GC.Spec.ChunkedMark.Defs.chunked_pointer_field_as_obj_addr mh v in
         let child =
           GC.Spec.ChunkedMark.Defs.chunked_resolve_object mh child_raw in
         Seq.mem child (MH.major_objects mh)))

val chunked_push_children_bounded_preservation_ready_next
  (mh: MH.major_heap)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  : Lemma
      (requires
        U64.v i <= U64.v ws /\
        U64.v i < U64.v ws /\
        chunked_push_children_bounded_preservation_ready mh obj i ws)
      (ensures
        (let v = GC.Spec.ChunkedMark.Defs.chunked_get_field mh obj i in
         let mh' =
           if GC.Spec.ChunkedMark.Defs.chunked_is_pointer_field mh v then
             let child_raw =
               GC.Spec.ChunkedMark.Defs.chunked_pointer_field_as_obj_addr mh v in
             let child =
               GC.Spec.ChunkedMark.Defs.chunked_resolve_object mh child_raw in
             if GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_white mh child then
               GC.Spec.ChunkedMark.Defs.chunked_make_gray mh child
             else
               mh
           else
             mh in
         chunked_push_children_bounded_preservation_ready
           mh' obj (U64.add i 1UL) ws))

val chunked_push_children_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_bounded_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_push_children_bounded
            mh st obj i ws cap in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_push_children_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_bounded_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_push_children_bounded
            mh st obj i ws cap in
         MH.well_formed_major_heap mh'))

val chunked_push_children_bounded_preserves_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        chunked_push_children_bounded_preservation_ready mh obj i ws /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_push_children_bounded
            mh st obj i ws cap in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' target))

val chunked_push_children_bounded_preserves_black_status
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (obj target: obj_addr)
  (i: U64.t{U64.v i >= 1})
  (ws: U64.t)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_push_children_bounded_preservation_ready mh obj i ws)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_push_children_bounded
            mh st obj i ws cap in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' target ==
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target))

val chunked_mark_step_bounded_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : GTot prop

val chunked_mark_step_bounded_preservation_ready_scan
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        chunked_mark_step_bounded_preservation_ready mh st cap /\
        ~(GC.Spec.ChunkedMark.Defs.chunked_is_no_scan mh (Seq.head st)))
      (ensures
        (let obj = Seq.head st in
         let mh' = GC.Spec.ChunkedMark.Defs.chunked_make_black mh obj in
         let ws =
           GC.Spec.ChunkedSweepCoalesce.Defs.chunked_wosize_of_object mh obj in
         chunked_push_children_bounded_preservation_ready mh' obj 1UL ws))

val chunked_mark_step_bounded_marks_head_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_step_bounded
            mh st cap in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' (Seq.head st)))

val chunked_mark_step_bounded_preserves_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_step_bounded
            mh st cap in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' target))

val chunked_mark_step_bounded_preserves_other_black_status
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (target: obj_addr)
  : Lemma
      (requires
        Seq.length st > 0 /\
        target <> Seq.head st /\
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_step_bounded
            mh st cap in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' target ==
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target))

val chunked_mark_step_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_step_bounded
            mh st cap in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_step_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_step_bounded
            mh st cap in
         MH.well_formed_major_heap mh'))

val chunked_mark_inner_loop_preservation_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : GTot prop

val chunked_mark_inner_loop_preserves_major_objects
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_inner_loop
            mh st cap fuel in
         MH.major_objects mh' == MH.major_objects mh))

val chunked_mark_inner_loop_preserves_well_formed
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_inner_loop
            mh st cap fuel in
         MH.well_formed_major_heap mh'))

val chunked_mark_inner_loop_preserves_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_inner_loop
            mh st cap fuel in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' target))

val chunked_mark_inner_loop_marks_target_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : GTot prop

val chunked_mark_inner_loop_marks_black_ready
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        chunked_mark_inner_loop_marks_target_ready mh st cap fuel target)

val chunked_mark_inner_loop_marks_head_ready
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
        chunked_mark_inner_loop_preservation_ready mh st cap fuel)
      (ensures
        chunked_mark_inner_loop_marks_target_ready mh st cap fuel target)

val chunked_mark_inner_loop_marks_tail_ready_from_step
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
        chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        (let (mh', st') =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_step_bounded
            mh st cap in
         chunked_mark_inner_loop_marks_target_ready
           mh' st' cap (fuel - 1) target))
      (ensures
        chunked_mark_inner_loop_marks_target_ready mh st cap fuel target)

val chunked_mark_inner_loop_marks_target_black
  (mh: MH.major_heap)
  (st: Seq.seq obj_addr)
  (cap: nat)
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        chunked_mark_inner_loop_marks_target_ready mh st cap fuel target)
      (ensures
        (let (mh', _) =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_inner_loop
            mh st cap fuel in
         GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh' target))

val chunked_mark_bounded_preservation_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : GTot prop

val chunked_mark_bounded_preserves_major_objects
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        MH.major_objects
          (GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_bounded
            mh cap fuel) ==
        MH.major_objects mh)

val chunked_mark_bounded_preserves_well_formed
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        MH.well_formed_major_heap
          (GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_bounded
            mh cap fuel))

val chunked_mark_bounded_preserves_black
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel /\
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_bounded
            mh cap fuel) target)

val chunked_mark_bounded_marks_target_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : GTot prop

val chunked_mark_bounded_marks_black_ready
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target)
      (ensures
        chunked_mark_bounded_marks_target_ready mh cap fuel target)

val chunked_mark_bounded_marks_rescan_head_ready_from_inner_fuel
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        chunked_mark_bounded_preservation_ready mh cap fuel /\
        (let st =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_rescan_heap
            mh Seq.empty cap in
         Seq.length st > 0 /\
         target == Seq.head st /\
         GC.Spec.ChunkedMarkBounded.Defs.chunked_count_non_black mh > 0))
      (ensures
        chunked_mark_bounded_marks_target_ready mh cap fuel target)

val chunked_mark_bounded_marks_target_ready_from_later_rescan
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        fuel > 0 /\
        ~ (GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black mh target) /\
        chunked_mark_bounded_preservation_ready mh cap fuel /\
        (let st =
          GC.Spec.ChunkedMarkBounded.Defs.chunked_rescan_heap
            mh Seq.empty cap in
         Seq.length st > 0 /\
         (let inner_fuel =
           GC.Spec.ChunkedMarkBounded.Defs.chunked_count_non_black mh in
          let (mh', _) =
            GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_inner_loop
              mh st cap inner_fuel in
          ~ (chunked_mark_inner_loop_marks_target_ready
              mh st cap inner_fuel target) /\
          chunked_mark_bounded_marks_target_ready
            mh' cap (fuel - 1) target)))
      (ensures
        chunked_mark_bounded_marks_target_ready mh cap fuel target)

val chunked_mark_bounded_marks_target_black
  (mh: MH.major_heap)
  (cap: nat{cap > 0})
  (fuel: nat)
  (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel /\
        chunked_mark_bounded_marks_target_ready mh cap fuel target)
      (ensures
        GC.Spec.ChunkedSweepCoalesce.Defs.chunked_is_black
          (GC.Spec.ChunkedMarkBounded.Defs.chunked_mark_bounded
            mh cap fuel) target)
