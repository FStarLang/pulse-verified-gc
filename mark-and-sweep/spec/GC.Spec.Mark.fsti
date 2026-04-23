/// ---------------------------------------------------------------------------
/// GC.Spec.Mark - Mark phase specification (interface)
/// ---------------------------------------------------------------------------
///
/// Uses obj_addr convention from common/. Stack stores obj_addr directly.
/// Color operations, field access, and graph construction all use obj_addr.

module GC.Spec.Mark

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
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header
module SweepInv = GC.Spec.SweepInv

/// ---------------------------------------------------------------------------
/// Gray Stack Properties
/// ---------------------------------------------------------------------------

/// Stack contains valid object addresses
let rec stack_elements_valid (g: heap) (st: seq obj_addr) 
  : Tot prop (decreases Seq.length st)
  =
  if Seq.length st = 0 then True
  else
    let obj = Seq.head st in
    Seq.mem obj (objects 0UL g) /\
    stack_elements_valid g (Seq.tail st)

/// All gray objects are on the stack
let gray_objects_on_stack (g: heap) (st: seq obj_addr) : prop =
  forall (obj: obj_addr). 
    Seq.mem obj (objects 0UL g) /\ is_gray obj g ==> Seq.mem obj st

/// Stack elements point to gray objects
let stack_points_to_gray (g: heap) (st: seq obj_addr) : prop =
  forall (obj: obj_addr). 
    Seq.mem obj st ==> is_gray obj g

/// Stack has no duplicate elements
let rec stack_no_dups (st: seq obj_addr)
  : Tot prop (decreases Seq.length st)
  = if Seq.length st = 0 then True
    else ~ (Seq.mem (Seq.head st) (Seq.tail st)) /\ stack_no_dups (Seq.tail st)

/// Complete stack properties
let stack_props (g: heap) (st: seq obj_addr) : prop =
  stack_elements_valid g st /\
  gray_objects_on_stack g st /\
  stack_points_to_gray g st /\
  stack_no_dups st

/// Helper: stack head is gray
val stack_head_is_gray : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires stack_props g st /\ Seq.length st > 0)
        (ensures (let obj = Seq.head st in
                  is_gray obj g /\
                  Seq.mem obj (objects 0UL g)))

/// Transfer stack_elements_valid when objects are equal
val sev_transfer : (g: heap) -> (g': heap) -> (st: seq obj_addr) ->
  Lemma (requires objects 0UL g == objects 0UL g' /\ stack_elements_valid g st)
        (ensures stack_elements_valid g' st)

/// White element not in gray stack (colors exclusive)
val white_not_in_gray_stack : (g: heap) -> (st: seq obj_addr) -> (child: obj_addr) ->
  Lemma (requires stack_points_to_gray g st /\ is_white child g)
        (ensures ~(Seq.mem child st))

/// stack_points_to_gray after makeGray step
val pc_step_spg : (g: heap) -> (child: obj_addr) -> (st: seq obj_addr) -> (g': heap) ->
  Lemma (requires g' == set_object_color child g Header.Gray /\
                 is_white child g /\ stack_points_to_gray g st)
        (ensures stack_points_to_gray g' (Seq.cons child st))

/// obj not in cons child st when obj ≠ child and obj ∉ st
val obj_not_in_cons : (obj: obj_addr) -> (child: obj_addr) -> (st: seq obj_addr) ->
  Lemma (requires obj <> child /\ ~(Seq.mem obj st))
        (ensures ~(Seq.mem obj (Seq.cons child st)))

/// stack_elements_valid implies subset of objects
val sev_mem_objects : (g: heap) -> (st: seq obj_addr) -> (x: obj_addr) ->
  Lemma (requires stack_elements_valid g st /\ Seq.mem x st)
        (ensures Seq.mem x (objects 0UL g))

/// Stack length is bounded by number of objects
val stack_length_bound : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires stack_elements_valid g st /\ stack_no_dups st)
        (ensures Seq.length st <= Seq.length (objects 0UL g))

/// ---------------------------------------------------------------------------
/// Root Properties
/// ---------------------------------------------------------------------------

/// Roots are valid heap pointers to objects (gray or black)
let root_props (g: heap) (roots: seq obj_addr) : prop =
  forall (r: obj_addr). Seq.mem r roots ==>
    (Seq.mem r (objects 0UL g) /\
     (is_gray r g \/ is_black r g))

/// ---------------------------------------------------------------------------
/// Mark Step: Process One Gray Object
/// ---------------------------------------------------------------------------

/// Push children of object onto stack (make white children gray)
let rec push_children (g: heap) (st: seq obj_addr) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
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
          let st' = Seq.cons child st in
          (g', st')
        else
          (g, st)
      end else
        (g, st)
    in
    if U64.v i < U64.v ws then
      push_children g' st' obj (U64.add i 1UL) ws
    else
      (g', st')

/// push_children only grows the stack (or leaves it unchanged)
val push_children_stack_monotone : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
                                    (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (ensures Seq.length st <= Seq.length (snd (push_children g st obj i ws)))

/// ---------------------------------------------------------------------------
/// Well-Formedness Preservation
/// ---------------------------------------------------------------------------

val color_change_preserves_wf : (g: heap) -> (obj: obj_addr) -> (c: color) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
        (ensures well_formed_heap (set_object_color obj g c))

val push_children_preserves_wf : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
                                  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures well_formed_heap (fst (push_children g st obj i ws)))

val push_children_preserves_stack_props :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\
                  is_black obj g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  ~(Seq.mem obj st))
        (ensures (let (g', st') = push_children g st obj i ws in stack_props g' st'))

/// Process one gray object: make it black and push children
let mark_step (g: heap) (st: seq obj_addr) 
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
    push_children g' st' obj 1UL ws

/// Unfold what mark_step computes
val mark_step_unfold : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires stack_elements_valid g st)
        (ensures (let obj = Seq.head st in
         let st' = Seq.tail st in
         let g' = makeBlack obj g in
         let ws = wosize_of_object obj g in
         (if is_no_scan obj g then mark_step g st == (g', st')
          else mark_step g st == push_children g' st' obj 1UL ws)))

/// mark_step preserves stack_props
val mark_step_preserves_stack_props : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures (let (g', st') = mark_step g st in
                  stack_props g' st'))

/// mark_step preserves well-formedness
val mark_step_preserves_wf : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures well_formed_heap (fst (mark_step g st)))

/// ---------------------------------------------------------------------------
/// Mark Phase: Iterate Until Stack Empty
/// ---------------------------------------------------------------------------

let rec mark_aux (g: heap) (st: seq obj_addr) (fuel: nat)
  : GTot heap (decreases fuel)
  =
  if Seq.length st = 0 then g
  else if fuel = 0 then g
  else begin
    let (g', st') = mark_step g st in
    mark_aux g' st' (fuel - 1)
  end

let mark (g: heap) (st: seq obj_addr) : GTot heap =
  mark_aux g st (heap_size / U64.v mword)

/// mark_aux unfolds one step
val mark_aux_unfold : (g: heap) -> (st: seq obj_addr) -> (fuel: nat) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ Seq.length st > 0)
        (ensures (let (g', st') = mark_step g st in
                  well_formed_heap g' /\ stack_props g' st' /\
                  mark_aux g st (fuel + 1) == mark_aux g' st' fuel))

/// mark_aux on empty stack is identity
val mark_aux_empty : (g: heap) -> (st: seq obj_addr) -> (fuel: nat) ->
  Lemma (requires Seq.length st = 0)
        (ensures mark_aux g st fuel == g)

/// ---------------------------------------------------------------------------
/// Mark Phase Invariants
/// ---------------------------------------------------------------------------

/// Tri-color invariant: no black object points to a white (resolved) object
let tri_color_invariant (g: heap) : prop =
  let objs = objects 0UL g in
  forall (obj: obj_addr) (child: obj_addr). 
    Seq.mem obj objs ==>
    is_black obj g ==>
    ~(is_no_scan obj g) ==>
    points_to g obj child ==>
    ~(is_white (resolve_object child g) g)

/// After marking, no gray objects remain
let noGreyObjects (g: heap) : prop =
  let objs = objects 0UL g in
  forall (obj: obj_addr). Seq.mem obj objs ==>
    not (is_gray obj g)

/// No black objects initially
let no_black_objects (g: heap) : prop =
  forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_black obj g)

/// No blue objects
let no_blue_objects (g: heap) : prop =
  forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_blue obj g)

/// No non-blue object points to a blue object
let no_pointer_to_blue (g: heap) : prop =
  forall (src dst: obj_addr).
    Seq.mem src (objects 0UL g) /\ ~(is_blue src g) /\ points_to g src dst ==>
    ~(is_blue dst g)

/// ---------------------------------------------------------------------------
/// Mark Aux/Mark Lemmas
/// ---------------------------------------------------------------------------

/// Fuel must be positive when stack is non-empty and mark_aux converges
val mark_aux_fuel_pos : (g: heap) -> (st: seq obj_addr) -> (fuel: nat) ->
  Lemma (requires stack_props g st /\ Seq.length st > 0 /\
                  noGreyObjects (mark_aux g st fuel))
        (ensures fuel > 0)

/// ---------------------------------------------------------------------------
/// Mark Preserves Well-Formedness
/// ---------------------------------------------------------------------------

val push_children_preserves_parent_black : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
                                            (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires is_black obj g)
        (ensures is_black obj (fst (push_children g st obj i ws)))

val push_children_preserves_other_black : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
                                           (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires is_black x g /\ x <> obj)
        (ensures is_black x (fst (push_children g st obj i ws)))

val push_children_not_blackens : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
                                 (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires ~(is_black x g))
        (ensures ~(is_black x (fst (push_children g st obj i ws))))

val mark_preserves_wf : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures well_formed_heap (mark g st))

/// ---------------------------------------------------------------------------
/// Color Exhaustiveness and Exclusivity
/// ---------------------------------------------------------------------------

val color_exhaustive : (obj: obj_addr) -> (g: heap) ->
  Lemma (is_white obj g \/ is_gray obj g \/ is_black obj g \/ is_blue obj g)

val colors_exclusive : (obj: obj_addr) -> (g: heap) ->
  Lemma (
    (is_white obj g ==> ~(is_gray obj g) /\ ~(is_black obj g) /\ ~(is_blue obj g)) /\
    (is_gray obj g ==> ~(is_white obj g) /\ ~(is_black obj g) /\ ~(is_blue obj g)) /\
    (is_black obj g ==> ~(is_white obj g) /\ ~(is_gray obj g) /\ ~(is_blue obj g)) /\
    (is_blue obj g ==> ~(is_white obj g) /\ ~(is_gray obj g) /\ ~(is_black obj g)))

/// ---------------------------------------------------------------------------
/// Mark Correctness: Black = Reachable
/// ---------------------------------------------------------------------------

val empty_stack_no_grey : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires stack_props g st /\ Seq.length st = 0)
        (ensures noGreyObjects g)

val mark_no_grey_remains : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures noGreyObjects (mark g st))

/// ---------------------------------------------------------------------------
/// Push Children Color/Structure Preservation
/// ---------------------------------------------------------------------------

val push_children_no_new_white : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires ~(is_white x g) /\ Seq.mem x (objects 0UL g) /\ 
                  well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures ~(is_white x (fst (push_children g st obj i ws))))

val push_children_obj_children_non_white : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (child: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  points_to g obj child)
        (ensures (let ws = wosize_of_object obj g in
                  let (g', _) = push_children g st obj 1UL ws in
                  ~(is_white (resolve_object child g) g')))

val push_children_preserves_points_to : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (b: obj_addr) -> (child: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  Seq.mem b (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures (let (g', _) = push_children g st obj i ws in
                  points_to g' b child == points_to g b child))

val push_children_black_backward : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (b: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  is_black b (fst (push_children g st obj i ws)))
        (ensures is_black b g)

val push_children_preserves_is_no_scan : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (b: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  Seq.mem b (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures (let (g', _) = push_children g st obj i ws in
                  is_no_scan b g' == is_no_scan b g))

val push_children_preserves_objects : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures (let (g', _) = push_children g st obj i ws in
                  objects 0UL g' == objects 0UL g))

val mark_step_preserves_objects : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures objects 0UL (fst (mark_step g st)) == objects 0UL g)

val mark_step_preserves_density : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ SweepInv.heap_objects_dense g)
        (ensures SweepInv.heap_objects_dense (fst (mark_step g st)))

/// ---------------------------------------------------------------------------
/// Mark/Mark_aux Preservation
/// ---------------------------------------------------------------------------

val mark_preserves_density : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ SweepInv.heap_objects_dense g)
        (ensures SweepInv.heap_objects_dense (mark g st))

val push_children_preserves_resolve : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (addr: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures (let (g', _) = push_children g st obj i ws in
                  resolve_object addr g' == resolve_object addr g))

val mark_preserves_tri_color : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ tri_color_invariant g)
        (ensures noGreyObjects (mark g st) ==> tri_color_invariant (mark g st))

val mark_aux_preserves_objects : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  (fuel: nat) ->
  Lemma (ensures objects 0UL (mark_aux g st fuel) == objects 0UL g)

val mark_preserves_objects_gt0 : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ Seq.length (objects 0UL g) > 0)
        (ensures Seq.length (objects 0UL (mark g st)) > 0)

val push_children_no_new_blue : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ ~(is_blue x g) /\
                  Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures ~(is_blue x (fst (push_children g st obj i ws))))

val push_children_preserves_blue : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ is_blue x g /\
                  Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures is_blue x (fst (push_children g st obj i ws)))

val black_successor_is_black : (g: heap) -> (src: obj_addr) -> (dst: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ tri_color_invariant g /\
                  no_pointer_to_blue g /\
                  Seq.mem src (objects 0UL g) /\ Seq.mem dst (objects 0UL g) /\
                  is_black src g /\ mem_graph_edge (create_graph g) src dst)
        (ensures is_black dst g)

val vertex_is_obj_addr : (g: heap) -> (x: vertex_id) ->
  Lemma (requires mem_graph_vertex (create_graph g) x)
        (ensures U64.v x >= 8)

val black_reach_is_black : (graph: graph_state{graph_wf graph}) -> (g: heap{well_formed_heap g}) ->
  (r: obj_addr{mem_graph_vertex graph r}) ->
  (x: obj_addr{mem_graph_vertex graph x}) ->
  (p: reach graph r x) ->
  Lemma (requires noGreyObjects g /\ tri_color_invariant g /\ no_pointer_to_blue g /\
                  graph == create_graph g /\
                  is_black r g)
        (ensures is_black x g)

/// ---------------------------------------------------------------------------
/// Color Change Graph Preservation
/// ---------------------------------------------------------------------------

val color_preserves_get_field :
  (target: obj_addr) -> (h: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) -> (i: U64.t{U64.v i >= 1}) ->
  Lemma (requires Seq.mem target (objects 0UL g) /\ Seq.mem h (objects 0UL g) /\
                  U64.v i <= U64.v (wosize_of_object h g))
        (ensures HeapGraph.get_field (set_object_color target g c) h i == HeapGraph.get_field g h i)

val color_preserves_create_graph :
  (obj: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) ->
  Lemma (requires Seq.mem obj (objects 0UL g))
        (ensures create_graph (set_object_color obj g c) == create_graph g)

/// ---------------------------------------------------------------------------
/// Bridge Lemmas for Implementation
/// ---------------------------------------------------------------------------

/// push_children preserves create_graph
val push_children_preserves_create_graph : (g: heap{well_formed_heap g}) -> (st: seq obj_addr) -> 
                                           (obj: obj_addr{Seq.mem obj (objects 0UL g)}) ->
                                           (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures create_graph (fst (push_children g st obj i ws)) == create_graph g)

val mark_preserves_create_graph : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  Lemma (ensures create_graph (mark g st) == create_graph g)

/// well_formed_heap implies object_fits_in_heap
val wf_implies_object_fits : (g: heap) -> (hd: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem hd (objects 0UL g))
        (ensures HeapGraph.object_fits_in_heap hd g)

/// color change preserves object_fits_in_heap
val color_preserves_object_fits : (target: obj_addr) -> (hd: obj_addr) -> (g: heap) -> (c: Header.color_sem) ->
  Lemma (requires HeapGraph.object_fits_in_heap hd g /\ Seq.mem target (objects 0UL g) /\
                  U64.v (wosize_of_object target g) < pow2 54)
        (ensures HeapGraph.object_fits_in_heap hd (set_object_color target g c))

/// push_children preserves wosize
val push_children_preserves_wosize : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  Seq.mem x (objects 0UL g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  ws == wosize_of_object obj g /\
                  HeapGraph.object_fits_in_heap obj g)
        (ensures wosize_of_object x (fst (push_children g st obj i ws)) == wosize_of_object x g)

val push_children_preserves_get_field : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) -> (j: U64.t{U64.v j >= 1}) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  Seq.mem x (objects 0UL g) /\ U64.v j <= U64.v (wosize_of_object x g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  ws == wosize_of_object obj g /\
                  HeapGraph.object_fits_in_heap obj g)
        (ensures HeapGraph.get_field (fst (push_children g st obj i ws)) x j == 
                 HeapGraph.get_field g x j)

/// ---------------------------------------------------------------------------
/// Mark Step Preservation
/// ---------------------------------------------------------------------------

val mark_preserves_get_field : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  (x: obj_addr) -> (i: U64.t{U64.v i >= 1}) ->
  Lemma (requires Seq.mem x (objects 0UL g) /\ U64.v i <= U64.v (wosize_of_object x g))
        (ensures HeapGraph.get_field (mark g st) x i == HeapGraph.get_field g x i)

val mark_preserves_wosize : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  (x: obj_addr) ->
  Lemma (requires Seq.mem x (objects 0UL g))
        (ensures wosize_of_object x (mark g st) == wosize_of_object x g)

val mark_preserves_no_pointer_to_blue : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  Lemma (requires no_pointer_to_blue g)
        (ensures no_pointer_to_blue (mark g st))

/// ---------------------------------------------------------------------------
/// Graph / DFS Lemmas
/// ---------------------------------------------------------------------------

val mark_reachable_is_black : (g: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  no_black_objects g /\ no_pointer_to_blue g /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
        (ensures (forall (x: obj_addr). 
                   (let graph = create_graph g in
                    let roots' = HeapGraph.coerce_to_vertex_list roots in
                    graph_wf graph /\ is_vertex_set roots' /\ 
                    subset_vertices roots' graph.vertices /\
                    mem_graph_vertex graph x /\
                    Seq.mem x (reachable_set graph roots')) ==> 
                   is_black x (mark g st)))

val mark_black_is_reachable : (g: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  no_black_objects g /\
                  (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r st) /\
                  (let graph = create_graph g in
                   let roots' = HeapGraph.coerce_to_vertex_list roots in
                   graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
        (ensures (let graph = create_graph g in
                  let roots' = HeapGraph.coerce_to_vertex_list roots in
                  forall (x: obj_addr). 
                    mem_graph_vertex graph x /\ is_black x (mark g st) ==> 
                    Seq.mem x (reachable_set graph roots')))

/// ---------------------------------------------------------------------------
/// No Grey Remains After Mark
/// ---------------------------------------------------------------------------

/// check_and_darken_field preserves well_formed_heap
val check_and_darken_field_preserves_wf :
  (g: heap) -> (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (wz: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v wz <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  Seq.length g == heap_size /\
                  U64.v i <= U64.v wz /\
                  HeapGraph.is_pointer_field (HeapGraph.get_field g obj i))
        (ensures (let v = HeapGraph.get_field g obj i in
                  let target : obj_addr = v in
                  Seq.mem target (objects 0UL g) /\
                  (is_white target g ==>
                    (well_formed_heap (set_object_color target g Header.Gray) /\
                     Seq.mem obj (objects 0UL (set_object_color target g Header.Gray)) /\
                     U64.v wz <= U64.v (wosize_of_object obj (set_object_color target g Header.Gray)) /\
                     U64.v (wosize_of_object obj (set_object_color target g Header.Gray)) < pow2 54))))

/// pointer field values resolve to themselves in well-formed heaps
val pointer_field_resolve_identity :
  (g: heap) -> (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (wz: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v wz <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  Seq.length g == heap_size /\
                  U64.v i <= U64.v wz /\
                  HeapGraph.is_pointer_field (HeapGraph.get_field g obj i))
        (ensures resolve_object (HeapGraph.get_field g obj i) g == HeapGraph.get_field g obj i)
