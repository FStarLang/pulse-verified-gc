module GC.Spec.ChunkedMarkBounded.Preservation

module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base

module MH = GC.Spec.MajorHeap
module Header = GC.Lib.Header
module MarkDefs = GC.Spec.ChunkedMark.Defs
module MarkPres = GC.Spec.ChunkedMark.Preservation
module SweepDefs = GC.Spec.ChunkedSweepCoalesce.Defs
module BDefs = GC.Spec.ChunkedMarkBounded.Defs

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let rec chunked_push_children_bounded_preservation_ready
    (mh: MH.major_heap)
    (obj: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
  : Tot prop
    (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then True
  else
    let v = MarkDefs.chunked_get_field mh obj i in
    let mh' =
      if MarkDefs.chunked_is_pointer_field mh v then
        let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
        let child = MarkDefs.chunked_resolve_object mh child_raw in
        if SweepDefs.chunked_is_white mh child then
          MarkDefs.chunked_make_gray mh child
        else
          mh
      else
        mh in
    (if MarkDefs.chunked_is_pointer_field mh v then
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      SweepDefs.chunked_is_white mh child ==>
        Seq.mem child (MH.major_objects mh)
     else
      True) /\
    (if U64.v i < U64.v ws then
      chunked_push_children_bounded_preservation_ready
        mh' obj (U64.add i 1UL) ws
     else
      True)

let rec chunked_push_children_bounded_preserves_major_objects
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
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         MH.major_objects mh' == MH.major_objects mh))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        let st' =
          if Seq.length st < cap then Seq.cons child st else st in
        assert (Seq.mem child (MH.major_objects mh));
        MarkPres.chunked_make_gray_preserves_major_objects mh child;
        MarkPres.chunked_make_gray_preserves_well_formed mh child;
        if U64.v i < U64.v ws then
          chunked_push_children_bounded_preserves_major_objects
            (MarkDefs.chunked_make_gray mh child)
            st'
            obj (U64.add i 1UL) ws cap
      end else if U64.v i < U64.v ws then
        chunked_push_children_bounded_preserves_major_objects
          mh st obj (U64.add i 1UL) ws cap
    end else if U64.v i < U64.v ws then
      chunked_push_children_bounded_preserves_major_objects
        mh st obj (U64.add i 1UL) ws cap
  end

let rec chunked_push_children_bounded_preserves_well_formed
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
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         MH.well_formed_major_heap mh'))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        let st' =
          if Seq.length st < cap then Seq.cons child st else st in
        assert (Seq.mem child (MH.major_objects mh));
        MarkPres.chunked_make_gray_preserves_well_formed mh child;
        if U64.v i < U64.v ws then
          chunked_push_children_bounded_preserves_well_formed
            (MarkDefs.chunked_make_gray mh child)
            st'
            obj (U64.add i 1UL) ws cap
      end else if U64.v i < U64.v ws then
        chunked_push_children_bounded_preserves_well_formed
          mh st obj (U64.add i 1UL) ws cap
    end else if U64.v i < U64.v ws then
      chunked_push_children_bounded_preserves_well_formed
        mh st obj (U64.add i 1UL) ws cap
  end

let rec chunked_push_children_bounded_preserves_black
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (obj target: obj_addr)
    (i: U64.t{U64.v i >= 1})
    (ws: U64.t)
    (cap: nat)
  : Lemma
      (requires
        chunked_push_children_bounded_preservation_ready mh obj i ws /\
        SweepDefs.chunked_is_black mh target)
      (ensures
        (let (mh', _) =
          BDefs.chunked_push_children_bounded mh st obj i ws cap in
         SweepDefs.chunked_is_black mh' target))
      (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then
    BDefs.chunked_push_children_bounded_done mh st obj i ws cap
  else begin
    BDefs.chunked_push_children_bounded_step mh st obj i ws cap;
    let v = MarkDefs.chunked_get_field mh obj i in
    if MarkDefs.chunked_is_pointer_field mh v then begin
      let child_raw = MarkDefs.chunked_pointer_field_as_obj_addr mh v in
      let child = MarkDefs.chunked_resolve_object mh child_raw in
      if SweepDefs.chunked_is_white mh child then begin
        let st' =
          if Seq.length st < cap then Seq.cons child st else st in
        if child = target then begin
          SweepDefs.chunked_is_white_not_black mh target;
          assert False
        end else begin
          MarkPres.chunked_make_gray_preserves_other_black mh child target;
          if U64.v i < U64.v ws then
            chunked_push_children_bounded_preserves_black
              (MarkDefs.chunked_make_gray mh child)
              st'
              obj target (U64.add i 1UL) ws cap
        end
      end else if U64.v i < U64.v ws then
        chunked_push_children_bounded_preserves_black
          mh st obj target (U64.add i 1UL) ws cap
    end else if U64.v i < U64.v ws then
      chunked_push_children_bounded_preserves_black
        mh st obj target (U64.add i 1UL) ws cap
  end

let chunked_mark_step_bounded_preservation_ready
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : GTot prop
  =
  if Seq.length st = 0 then True
  else
    let obj = Seq.head st in
    Seq.mem obj (MH.major_objects mh) /\
    (if MarkDefs.chunked_is_no_scan mh obj then
      True
     else
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      chunked_push_children_bounded_preservation_ready mh' obj 1UL ws)

let chunked_mark_step_bounded_marks_head_black
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        Seq.length st > 0 /\
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         SweepDefs.chunked_is_black mh' (Seq.head st)))
  =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  assert (Seq.mem obj (MH.major_objects mh));
  if MarkDefs.chunked_is_no_scan mh obj then begin
    BDefs.chunked_mark_step_bounded_no_scan mh st cap;
    MarkPres.chunked_make_black_makes_black mh obj
  end else begin
    let mh_black = MarkDefs.chunked_make_black mh obj in
    let ws = SweepDefs.chunked_wosize_of_object mh obj in
    BDefs.chunked_mark_step_bounded_scan mh st cap;
    MarkPres.chunked_make_black_makes_black mh obj;
    chunked_push_children_bounded_preserves_black mh_black st' obj obj 1UL ws cap
  end

let chunked_mark_step_bounded_preserves_black
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap /\
        SweepDefs.chunked_is_black mh target)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         SweepDefs.chunked_is_black mh' target))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    nat_nonzero_pos (Seq.length st);
    let obj = Seq.head st in
    let st' = Seq.tail st in
    assert (Seq.mem obj (MH.major_objects mh));
    let mh_black = MarkDefs.chunked_make_black mh obj in
    if obj = target then begin
      if MarkDefs.chunked_is_no_scan mh obj then begin
        BDefs.chunked_mark_step_bounded_no_scan mh st cap;
        MarkPres.chunked_make_black_makes_black mh obj
      end else begin
        let ws = SweepDefs.chunked_wosize_of_object mh obj in
        BDefs.chunked_mark_step_bounded_scan mh st cap;
        MarkPres.chunked_make_black_makes_black mh obj;
        chunked_push_children_bounded_preserves_black
          mh_black st' obj target 1UL ws cap
      end
    end else begin
      MarkDefs.chunked_make_black_step mh obj;
      MarkPres.chunked_set_object_color_preserves_other_black
        mh obj target Header.Black;
      if MarkDefs.chunked_is_no_scan mh obj then
        BDefs.chunked_mark_step_bounded_no_scan mh st cap
      else begin
        let ws = SweepDefs.chunked_wosize_of_object mh obj in
        BDefs.chunked_mark_step_bounded_scan mh st cap;
        chunked_push_children_bounded_preserves_black
          mh_black st' obj target 1UL ws cap
      end
    end
  end

let chunked_mark_step_bounded_preserves_major_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         MH.major_objects mh' == MH.major_objects mh))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    let obj = Seq.head st in
    assert (Seq.mem obj (MH.major_objects mh));
    if MarkDefs.chunked_is_no_scan mh obj then begin
      assert (MarkDefs.chunked_is_no_scan mh (Seq.head st));
      BDefs.chunked_mark_step_bounded_no_scan mh st cap;
      MarkPres.chunked_make_black_preserves_major_objects mh obj
    end else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      assert (~(MarkDefs.chunked_is_no_scan mh (Seq.head st)));
      assert (chunked_push_children_bounded_preservation_ready mh' obj 1UL ws);
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      MarkPres.chunked_make_black_preserves_major_objects mh obj;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      chunked_push_children_bounded_preserves_major_objects
        mh' (Seq.tail st) obj 1UL ws cap
    end
  end

let chunked_mark_step_bounded_preserves_well_formed
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_step_bounded_preservation_ready mh st cap)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_step_bounded mh st cap in
         MH.well_formed_major_heap mh'))
  =
  if Seq.length st = 0 then
    BDefs.chunked_mark_step_bounded_empty mh st cap
  else begin
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    let obj = Seq.head st in
    assert (Seq.mem obj (MH.major_objects mh));
    if MarkDefs.chunked_is_no_scan mh obj then begin
      assert (MarkDefs.chunked_is_no_scan mh (Seq.head st));
      BDefs.chunked_mark_step_bounded_no_scan mh st cap;
      MarkPres.chunked_make_black_preserves_well_formed mh obj
    end else begin
      let mh' = MarkDefs.chunked_make_black mh obj in
      let ws = SweepDefs.chunked_wosize_of_object mh obj in
      assert (~(MarkDefs.chunked_is_no_scan mh (Seq.head st)));
      assert (chunked_push_children_bounded_preservation_ready mh' obj 1UL ws);
      BDefs.chunked_mark_step_bounded_scan mh st cap;
      MarkPres.chunked_make_black_preserves_well_formed mh obj;
      chunked_push_children_bounded_preserves_well_formed
        mh' (Seq.tail st) obj 1UL ws cap
    end
  end

let rec chunked_mark_inner_loop_preservation_ready
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then True
  else
    let fuel_pred : n:nat{n < fuel} = fuel - 1 in
    chunked_mark_step_bounded_preservation_ready mh st cap /\
    (let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
     chunked_mark_inner_loop_preservation_ready mh' st' cap fuel_pred)

let rec chunked_mark_inner_loop_preserves_major_objects
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         MH.major_objects mh' == MH.major_objects mh))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (chunked_mark_step_bounded_preservation_ready mh st cap);
    chunked_mark_step_bounded_preserves_major_objects mh st cap;
    chunked_mark_step_bounded_preserves_well_formed mh st cap;
    assert (MH.major_objects mh' == MH.major_objects mh);
    assert (MH.well_formed_major_heap mh');
    assert (chunked_mark_inner_loop_preservation_ready mh' st' cap (fuel - 1));
    chunked_mark_inner_loop_preserves_major_objects mh' st' cap (fuel - 1)
  end

let rec chunked_mark_inner_loop_preserves_well_formed
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         MH.well_formed_major_heap mh'))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (chunked_mark_step_bounded_preservation_ready mh st cap);
    chunked_mark_step_bounded_preserves_well_formed mh st cap;
    assert (MH.well_formed_major_heap mh');
    assert (chunked_mark_inner_loop_preservation_ready mh' st' cap (fuel - 1));
    chunked_mark_inner_loop_preserves_well_formed mh' st' cap (fuel - 1)
  end

let rec chunked_mark_inner_loop_preserves_black
    (mh: MH.major_heap)
    (st: Seq.seq obj_addr)
    (cap: nat)
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_inner_loop_preservation_ready mh st cap fuel /\
        SweepDefs.chunked_is_black mh target)
      (ensures
        (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap fuel in
         SweepDefs.chunked_is_black mh' target))
      (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then
    BDefs.chunked_mark_inner_loop_base mh st cap fuel
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    assert (Seq.length st <> 0);
    nat_nonzero_pos (Seq.length st);
    BDefs.chunked_mark_inner_loop_step mh st cap fuel;
    let (mh', st') = BDefs.chunked_mark_step_bounded mh st cap in
    assert (chunked_mark_step_bounded_preservation_ready mh st cap);
    chunked_mark_step_bounded_preserves_black mh st cap target;
    chunked_mark_step_bounded_preserves_well_formed mh st cap;
    assert (SweepDefs.chunked_is_black mh' target);
    assert (MH.well_formed_major_heap mh');
    assert (chunked_mark_inner_loop_preservation_ready mh' st' cap (fuel - 1));
    chunked_mark_inner_loop_preserves_black mh' st' cap (fuel - 1) target
  end

let rec chunked_mark_bounded_preservation_ready
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Tot prop
    (decreases fuel)
  =
  if fuel = 0 then True
  else
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then True
    else
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let fuel_pred : n:nat{n < fuel} = fuel - 1 in
      chunked_mark_inner_loop_preservation_ready mh st cap inner_fuel /\
      (let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
       chunked_mark_bounded_preservation_ready mh' cap fuel_pred)

let rec chunked_mark_bounded_preserves_major_objects
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        MH.major_objects (BDefs.chunked_mark_bounded mh cap fuel) ==
        MH.major_objects mh)
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then ()
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (chunked_mark_inner_loop_preservation_ready mh st cap inner_fuel);
      chunked_mark_inner_loop_preserves_major_objects mh st cap inner_fuel;
      chunked_mark_inner_loop_preserves_well_formed mh st cap inner_fuel;
      assert (MH.major_objects mh' == MH.major_objects mh);
      assert (MH.well_formed_major_heap mh');
      assert (chunked_mark_bounded_preservation_ready mh' cap (fuel - 1));
      chunked_mark_bounded_preserves_major_objects mh' cap (fuel - 1)
    end
  end

let rec chunked_mark_bounded_preserves_well_formed
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel)
      (ensures
        MH.well_formed_major_heap (BDefs.chunked_mark_bounded mh cap fuel))
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then ()
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (chunked_mark_inner_loop_preservation_ready mh st cap inner_fuel);
      chunked_mark_inner_loop_preserves_well_formed mh st cap inner_fuel;
      assert (MH.well_formed_major_heap mh');
      assert (chunked_mark_bounded_preservation_ready mh' cap (fuel - 1));
      chunked_mark_bounded_preserves_well_formed mh' cap (fuel - 1)
    end
  end

let rec chunked_mark_bounded_preserves_black
    (mh: MH.major_heap)
    (cap: nat{cap > 0})
    (fuel: nat)
    (target: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        chunked_mark_bounded_preservation_ready mh cap fuel /\
        SweepDefs.chunked_is_black mh target)
      (ensures
        SweepDefs.chunked_is_black
          (BDefs.chunked_mark_bounded mh cap fuel) target)
      (decreases fuel)
  =
  if fuel = 0 then
    BDefs.chunked_mark_bounded_base mh cap
  else begin
    assert (fuel <> 0);
    nat_nonzero_pos fuel;
    BDefs.chunked_mark_bounded_step mh cap fuel;
    let st = BDefs.chunked_rescan_heap mh Seq.empty cap in
    if Seq.length st = 0 then ()
    else begin
      let inner_fuel = BDefs.chunked_count_non_black mh in
      let (mh', _) = BDefs.chunked_mark_inner_loop mh st cap inner_fuel in
      assert (chunked_mark_inner_loop_preservation_ready mh st cap inner_fuel);
      chunked_mark_inner_loop_preserves_black mh st cap inner_fuel target;
      chunked_mark_inner_loop_preserves_well_formed mh st cap inner_fuel;
      assert (SweepDefs.chunked_is_black mh' target);
      assert (MH.well_formed_major_heap mh');
      assert (chunked_mark_bounded_preservation_ready mh' cap (fuel - 1));
      chunked_mark_bounded_preserves_black mh' cap (fuel - 1) target
    end
  end
