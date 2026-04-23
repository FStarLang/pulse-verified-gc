/// ---------------------------------------------------------------------------
/// GC.Spec.MarkBounded — Mark phase with bounded (overflow-tolerant) stack
/// ---------------------------------------------------------------------------

module GC.Spec.MarkBounded

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Graph
open GC.Spec.Fields
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Spec.Mark
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header
module SweepInv = GC.Spec.SweepInv

/// ---------------------------------------------------------------------------
/// Bounded Stack Properties (no gray_objects_on_stack)
/// ---------------------------------------------------------------------------

let bounded_stack_props (g: heap) (st: seq obj_addr) : prop =
  stack_elements_valid g st /\
  stack_points_to_gray g st /\
  stack_no_dups st

val bounded_from_full (g: heap) (st: seq obj_addr)
  : Lemma (requires stack_props g st)
          (ensures bounded_stack_props g st)

/// ---------------------------------------------------------------------------
/// Counting non-black objects (termination measure)
/// ---------------------------------------------------------------------------

let rec count_non_black_in (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else
      let obj = Seq.head objs in
      let rest = count_non_black_in g (Seq.tail objs) in
      if is_black obj g then rest
      else rest + 1

let count_non_black (g: heap) : GTot nat =
  count_non_black_in g (objects 0UL g)

/// ---------------------------------------------------------------------------
/// Push children with bounded stack capacity
/// ---------------------------------------------------------------------------

let rec push_children_bounded
  (g: heap) (st: seq obj_addr) (obj: obj_addr)
  (i: U64.t{U64.v i >= 1}) (ws: U64.t) (cap: nat)
  : GTot (heap & seq obj_addr) (decreases (U64.v ws - U64.v i))
  =
  if U64.v i > U64.v ws then (g, st)
  else
    let v = HeapGraph.get_field g obj i in
    let (g', st') =
      if HeapGraph.is_pointer_field v then begin
        HeapGraph.is_pointer_field_is_obj_addr v;
        let child_raw : obj_addr = v in
        let child = resolve_object child_raw g in
        if is_white child g then
          let g' = makeGray child g in
          if Seq.length st < cap then
            (g', Seq.cons child st)
          else
            (g', st)  // overflow: child gray in heap, not on stack
        else
          (g, st)
      end else
        (g, st)
    in
    if U64.v i < U64.v ws then
      push_children_bounded g' st' obj (U64.add i 1UL) ws cap
    else
      (g', st')

val push_children_bounded_heap_eq
  (g: heap) (st_b: seq obj_addr) (st_u: seq obj_addr)
  (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t) (cap: nat)
  : Lemma (ensures fst (push_children_bounded g st_b obj i ws cap) ==
                   fst (push_children g st_u obj i ws))
          (decreases (U64.v ws - U64.v i))

/// ---------------------------------------------------------------------------
/// Bounded mark step
/// ---------------------------------------------------------------------------

let mark_step_bounded (g: heap) (st: seq obj_addr) (cap: nat)
  : GTot (heap & seq obj_addr)
  =
  if Seq.length st = 0 then (g, st)
  else
    let obj = Seq.head st in
    let st' = Seq.tail st in
    let g' = makeBlack obj g in
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then
      (g', st')
    else
      push_children_bounded g' st' obj 1UL ws cap

val mark_step_bounded_heap_eq (g: heap) (st_b: seq obj_addr) (st_u: seq obj_addr) (cap: nat)
  : Lemma (requires Seq.length st_b > 0 /\ Seq.length st_u > 0 /\
                    Seq.head st_b == Seq.head st_u)
          (ensures fst (mark_step_bounded g st_b cap) ==
                   fst (mark_step g st_u))

/// ---------------------------------------------------------------------------
/// Inner mark loop (drain stack)
/// ---------------------------------------------------------------------------

let rec mark_inner_loop (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : GTot (heap & seq obj_addr) (decreases fuel)
  =
  if fuel = 0 || Seq.length st = 0 then (g, st)
  else
    let (g', st') = mark_step_bounded g st cap in
    mark_inner_loop g' st' cap (fuel - 1)

/// ---------------------------------------------------------------------------
/// Heap rescan: linear scan for remaining gray objects
/// ---------------------------------------------------------------------------

let rec rescan_heap (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : GTot (seq obj_addr) (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then st
  else
    let obj = Seq.head objs in
    let st' =
      if is_gray obj g && not (Seq.mem obj st) && Seq.length st < cap then
        Seq.cons obj st
      else
        st
    in
    rescan_heap g (Seq.tail objs) st' cap

/// ---------------------------------------------------------------------------
/// Top-level bounded mark: outer loop
/// ---------------------------------------------------------------------------

let rec mark_bounded (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : GTot heap (decreases fuel)
  = if fuel = 0 then g
    else
      let st = rescan_heap g (objects 0UL g) Seq.empty cap in
      if Seq.length st = 0 then g
      else
        let inner_fuel = count_non_black g in
        let (g', _) = mark_inner_loop g st cap inner_fuel in
        mark_bounded g' cap (fuel - 1)

/// ---------------------------------------------------------------------------
/// Lemmas
/// ---------------------------------------------------------------------------

val push_children_bounded_cap :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (ensures Seq.length (snd (push_children_bounded g st obj i ws cap)) <= (if Seq.length st > cap then Seq.length st else cap))
        (decreases (U64.v ws - U64.v i))

val spg_preserved_other_color (g g': heap) (st: seq obj_addr) (child: obj_addr) (c: color)
  : Lemma (requires g' == set_object_color child g c /\
                   stack_points_to_gray g st /\
                   ~(Seq.mem child st))
          (ensures stack_points_to_gray g' st)

val push_children_bounded_preserves_bsp :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (requires well_formed_heap g /\ is_black obj g /\
                  Seq.mem obj (objects 0UL g) /\
                  bounded_stack_props g st /\
                  ~(Seq.mem obj st) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  U64.v (hd_address obj) + U64.v mword + U64.v ws * U64.v mword <= heap_size)
        (ensures (let (g', st') = push_children_bounded g st obj i ws cap in
                  bounded_stack_props g' st' /\ well_formed_heap g'))
        (decreases (U64.v ws - U64.v i))

val bounded_stack_head_is_gray (g: heap) (st: seq obj_addr)
  : Lemma (requires bounded_stack_props g st /\ Seq.length st > 0)
          (ensures (let obj = Seq.head st in
                    is_gray obj g /\
                    Seq.mem obj (objects 0UL g)))

val mark_step_bounded_preserves_bsp
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  Seq.length (objects 0UL g) > 0 /\ SweepInv.heap_objects_dense g)
        (ensures (let (g', st') = mark_step_bounded g st cap in
                  well_formed_heap g' /\ bounded_stack_props g' st'))

val push_children_bounded_preserves_objects :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (ensures objects 0UL (fst (push_children_bounded g st obj i ws cap)) == objects 0UL g)
        (decreases (U64.v ws - U64.v i))

val mark_step_bounded_preserves_objects
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st)
        (ensures objects 0UL (fst (mark_step_bounded g st cap)) == objects 0UL g)

val push_children_bounded_preserves_density :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (requires SweepInv.heap_objects_dense g)
        (ensures SweepInv.heap_objects_dense (fst (push_children_bounded g st obj i ws cap)))
        (decreases (U64.v ws - U64.v i))

val mark_step_bounded_preserves_density
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   SweepInv.heap_objects_dense g)
          (ensures SweepInv.heap_objects_dense (fst (mark_step_bounded g st cap)))

val count_non_black_monotone (g g': heap) (objs: seq obj_addr)
  : Lemma (requires (forall (x: obj_addr). is_black x g ==> is_black x g'))
          (ensures count_non_black_in g' objs <= count_non_black_in g objs)
          (decreases Seq.length objs)

val makeBlack_preserves_other_black (obj x: obj_addr) (g: heap)
  : Lemma (requires is_black x g)
          (ensures is_black x (makeBlack obj g))

val count_non_black_in_has_nonblack (g: heap) (obj: obj_addr) (objs: seq obj_addr)
  : Lemma (requires Seq.mem obj objs /\ ~(is_black obj g))
          (ensures count_non_black_in g objs > 0)
          (decreases Seq.length objs)

val count_non_black_makeBlack (g: heap) (obj: obj_addr) (objs: seq obj_addr)
  : Lemma (requires is_gray obj g /\ Seq.mem obj objs)
          (ensures count_non_black_in (makeBlack obj g) objs < count_non_black_in g objs)
          (decreases Seq.length objs)

val makeGray_white_preserves_black (child x: obj_addr) (g: heap)
  : Lemma (requires is_white child g /\ is_black x g)
          (ensures is_black x (makeGray child g))

val makeGray_white_preserves_nonblack (child x: obj_addr) (g: heap)
  : Lemma (requires is_white child g /\ ~(is_black x g))
          (ensures ~(is_black x (makeGray child g)))

val count_non_black_makeGray_white (g: heap) (child: obj_addr) (objs: seq obj_addr)
  : Lemma (requires is_white child g)
          (ensures count_non_black_in (makeGray child g) objs == count_non_black_in g objs)
          (decreases Seq.length objs)

val push_children_bounded_count_non_black :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (ensures (let (g', _) = push_children_bounded g st obj i ws cap in
                  count_non_black_in g' (objects 0UL g) == count_non_black_in g (objects 0UL g)))
        (decreases (U64.v ws - U64.v i))

val mark_step_bounded_decreases_non_black
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  Seq.length (objects 0UL g) > 0 /\ SweepInv.heap_objects_dense g)
        (ensures count_non_black (fst (mark_step_bounded g st cap)) < count_non_black g)

val cons_gray_preserves_bsp (g: heap) (obj: obj_addr) (st: seq obj_addr)
  : Lemma (requires bounded_stack_props g st /\ is_gray obj g /\
                   Seq.mem obj (objects 0UL g) /\ ~(Seq.mem obj st))
          (ensures bounded_stack_props g (Seq.cons obj st))

val rescan_heap_bsp_gen
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_stack_props g st /\
                   (forall (x: obj_addr). Seq.mem x objs ==> Seq.mem x (objects 0UL g)))
          (ensures bounded_stack_props g (rescan_heap g objs st cap))
          (decreases Seq.length objs)

val empty_bounded_stack_props (g: heap)
  : Lemma (bounded_stack_props g Seq.empty)

val rescan_heap_bounded_stack_props
  (g: heap) (objs: seq obj_addr) (cap: nat)
  : Lemma (requires (forall (x: obj_addr). Seq.mem x objs ==> Seq.mem x (objects 0UL g)))
          (ensures bounded_stack_props g (rescan_heap g objs Seq.empty cap))

val rescan_heap_monotone
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : Lemma (ensures Seq.length (rescan_heap g objs st cap) >= Seq.length st)
          (decreases Seq.length objs)

val rescan_heap_cap_bound
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : Lemma (requires Seq.length st <= cap)
          (ensures Seq.length (rescan_heap g objs st cap) <= cap)
          (decreases Seq.length objs)

val rescan_complete_gen
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : Lemma (requires cap > 0)
          (ensures (Seq.length (rescan_heap g objs st cap) = 0 ==>
                    (Seq.length st = 0 /\
                     (forall (obj: obj_addr). Seq.mem obj objs ==> ~(is_gray obj g)))))
          (decreases Seq.length objs)

val rescan_complete
  (g: heap) (cap: nat)
  : Lemma (requires cap > 0)
          (ensures (let st = rescan_heap g (objects 0UL g) Seq.empty cap in
                  Seq.length st = 0 ==>
                  (forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_gray obj g))))

val mark_inner_loop_preserves_inv
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   Seq.length st <= cap /\ cap > 0)
          (ensures (let (g', st') = mark_inner_loop g st cap fuel in
                    well_formed_heap g' /\ bounded_stack_props g' st' /\
                    Seq.length (objects 0UL g') > 0 /\
                    SweepInv.heap_objects_dense g' /\
                    Seq.length st' <= cap))
          (decreases fuel)

val mark_inner_loop_preserves_objects
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g)
          (ensures objects 0UL (fst (mark_inner_loop g st cap fuel)) == objects 0UL g)
          (decreases fuel)

val mark_inner_loop_count_non_increasing
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g)
          (ensures count_non_black (fst (mark_inner_loop g st cap fuel)) <= count_non_black g)
          (decreases fuel)

val mark_inner_loop_count_decreases
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   Seq.length st > 0 /\ fuel > 0)
          (ensures count_non_black (fst (mark_inner_loop g st cap fuel)) < count_non_black g)

val mark_inner_loop_drains
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   fuel >= count_non_black g)
          (ensures Seq.length (snd (mark_inner_loop g st cap fuel)) = 0)
          (decreases fuel)

val mark_bounded_preserves_inv (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g)
          (ensures (let g' = mark_bounded g cap fuel in
                    well_formed_heap g' /\
                    Seq.length (objects 0UL g') > 0 /\
                    SweepInv.heap_objects_dense g'))
          (decreases fuel)

val mark_bounded_preserves_objects (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g)
          (ensures objects 0UL (mark_bounded g cap fuel) == objects 0UL g)
          (decreases fuel)

val mark_bounded_count_decreases (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\ fuel > 0 /\
                   Seq.length (rescan_heap g (objects 0UL g) Seq.empty cap) > 0)
          (ensures count_non_black (mark_bounded g cap fuel) < count_non_black g)
          (decreases fuel)

val count_non_black_zero_not_gray (g: heap) (obj: obj_addr) (objs: seq obj_addr)
  : Lemma (requires count_non_black_in g objs = 0 /\ Seq.mem obj objs)
          (ensures ~(is_gray obj g))
          (decreases Seq.length objs)

val count_non_black_zero_no_gray (g: heap)
  : Lemma (requires count_non_black g = 0)
          (ensures SweepInv.no_gray_objects g)

val mark_bounded_completes (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   fuel >= count_non_black g)
          (ensures SweepInv.no_gray_objects (mark_bounded g cap fuel))
          (decreases fuel)
