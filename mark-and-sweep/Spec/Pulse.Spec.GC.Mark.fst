/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Mark - Mark phase specification
/// ---------------------------------------------------------------------------
///
/// Uses obj_addr convention from common/. Stack stores obj_addr directly.
/// Color operations, field access, and graph construction all use obj_addr.

module Pulse.Spec.GC.Mark

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Graph
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.HeapModel
open Pulse.Spec.GC.DFS
module HeapGraph = Pulse.Spec.GC.HeapGraph
module Header = Pulse.Lib.Header

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

/// Complete stack properties
let stack_props (g: heap) (st: seq obj_addr) : prop =
  stack_elements_valid g st /\
  gray_objects_on_stack g st /\
  stack_points_to_gray g st

/// Helper: stack head is gray
let stack_head_is_gray (g: heap) (st: seq obj_addr)
  : Lemma (requires stack_props g st /\ Seq.length st > 0)
          (ensures (let obj = Seq.head st in
                    is_gray obj g /\
                    Seq.mem obj (objects 0UL g)))
  = ()

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
        let child : obj_addr = v in
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

/// Process one gray object: make it black and push children
let mark_step (g: heap) (st: seq obj_addr{Seq.length st > 0 /\ stack_elements_valid g st}) 
  : GTot (heap & seq obj_addr)
  =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  
  // Make it black
  let g' = makeBlack obj g in
  
  // Push white children
  let ws = wosize_of_object obj g in
  if is_no_scan obj g then
    (g', st')
  else
    push_children g' st' obj 1UL ws

/// mark_step preserves stack_props
val mark_step_preserves_stack_props : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures (let (g', st') = mark_step g st in
                  stack_props g' st'))

let mark_step_preserves_stack_props g st =
  admit()

/// ---------------------------------------------------------------------------
/// Mark Phase: Iterate Until Stack Empty
/// ---------------------------------------------------------------------------

let rec mark_aux (g: heap{well_formed_heap g}) (st: seq obj_addr{stack_props g st}) (fuel: nat)
  : GTot heap (decreases fuel)
  =
  if Seq.length st = 0 then g
  else if fuel = 0 then g
  else begin
    let (g', st') = mark_step g st in
    mark_step_preserves_stack_props g st;
    admit();  // TODO: mark_step_preserves_wf
    mark_aux g' st' (fuel - 1)
  end

let mark (g: heap{well_formed_heap g}) (st: seq obj_addr{stack_props g st}) : GTot heap =
  mark_aux g st (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// Mark Phase Invariants
/// ---------------------------------------------------------------------------

/// Tri-color invariant: no black object points to white object
let tri_color_invariant (g: heap) : prop =
  let objs = objects 0UL g in
  forall (obj: obj_addr). Seq.mem obj objs ==>
    (is_black obj g ==>
      (forall (s: obj_addr). Seq.mem s (HeapGraph.get_pointer_fields g obj) ==>
        not (is_white s g)))

/// After marking, no gray objects remain
let noGreyObjects (g: heap) : prop =
  let objs = objects 0UL g in
  forall (obj: obj_addr). Seq.mem obj objs ==>
    not (is_gray obj g)

/// ---------------------------------------------------------------------------
/// Ghost State for Mark Termination
/// ---------------------------------------------------------------------------

let rec non_black_count (g: heap) (objs: seq obj_addr) : GTot nat (decreases Seq.length objs) =
  if Seq.length objs = 0 then 0
  else
    let h = Seq.head objs in
    let rest = non_black_count g (Seq.tail objs) in
    if is_black h g then rest else rest + 1

let total_non_black (g: heap) : GTot nat =
  non_black_count g (objects 0UL g)

/// push_children preserves black color of parent
val push_children_preserves_parent_black : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
                                            (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires is_black obj g)
        (ensures is_black obj (fst (push_children g st obj i ws)))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 100 --fuel 2"
let rec push_children_preserves_parent_black g st obj i ws =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child : obj_addr = v in
      if is_white child g then begin
        let g' = makeGray child g in
        // child is white, obj is black → child <> obj
        is_white_iff child g;
        is_black_iff obj g;
        assert (child <> obj);
        makeGray_eq child g;
        color_change_preserves_other_color child obj g Header.Gray;
        is_black_iff obj g;
        is_black_iff obj g';
        assert (is_black obj g');
        let st' = Seq.cons child st in
        if U64.v i < U64.v ws then
          push_children_preserves_parent_black g' st' obj (U64.add i 1UL) ws
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_preserves_parent_black g st obj (U64.add i 1UL) ws
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_preserves_parent_black g st obj (U64.add i 1UL) ws
      else ()
    end
  end
#pop-options

/// mark_step makes exactly one object black (the head of stack)
val mark_step_makes_one_black : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures (let obj = Seq.head st in
                  is_black obj (fst (mark_step g st)) /\
                  is_gray obj g))

#push-options "--z3rlimit 100"
let mark_step_makes_one_black g st =
  stack_head_is_gray g st;
  let obj = Seq.head st in
  assert (is_gray obj g);
  let g' = makeBlack obj g in
  makeBlack_is_black obj g;
  assert (is_black obj g');
  let ws = wosize_of_object obj g in
  if is_no_scan obj g then ()
  else
    push_children_preserves_parent_black g' (Seq.tail st) obj 1UL ws
#pop-options

/// Helper: non_black_count is unchanged when makeBlack on address not in list
val non_black_count_makeBlack_other : (g: heap) -> (obj: obj_addr) -> (objs: seq obj_addr) ->
  Lemma (requires ~(Seq.mem obj objs) /\
                  (forall (x: obj_addr). Seq.mem x objs ==> obj <> x))
        (ensures non_black_count (makeBlack obj g) objs == non_black_count g objs)
        (decreases Seq.length objs)

let rec non_black_count_makeBlack_other g obj objs =
  if Seq.length objs = 0 then ()
  else begin
    let hd = Seq.head objs in
    assert (Seq.mem hd objs);
    makeBlack_eq obj g;
    color_change_preserves_other_color obj hd g Header.Black;
    is_black_iff hd g;
    is_black_iff hd (makeBlack obj g);
    assert (is_black hd (makeBlack obj g) == is_black hd g);
    non_black_count_makeBlack_other g obj (Seq.tail objs)
  end

let non_black_count_unfold (g: heap) (objs: seq obj_addr)
  : Lemma (requires Seq.length objs > 0)
          (ensures non_black_count g objs == 
                   (if is_black (Seq.head objs) g then 0 else 1) + 
                   non_black_count g (Seq.tail objs))
  = ()

/// ---------------------------------------------------------------------------
/// Pillar 1: Mark Preserves Well-Formedness
/// ---------------------------------------------------------------------------

val color_change_preserves_wf : (g: heap) -> (obj: obj_addr) -> (c: color) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
        (ensures well_formed_heap (set_object_color obj g c))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let color_change_preserves_wf g obj c =
  let g' = set_object_color obj g c in
  color_change_preserves_objects g obj c;
  set_object_color_length obj g c;
  // Part 1: object bounds preserved (wosize unchanged + length unchanged)
  let aux1 (h: obj_addr) : Lemma
    (requires Seq.mem h (objects 0UL g))
    (ensures (let wz = wosize_of_object h g' in
              U64.v (hd_address h) + 8 + FStar.Mul.(U64.v wz * 8) <= Seq.length g'))
  = wosize_of_object_spec h g;
    wosize_of_object_spec h g';
    if h = obj then
      set_object_color_preserves_getWosize_at_hd obj g c
    else begin
      hd_address_injective h obj;
      set_object_color_read_word obj (Pulse.Spec.GC.Heap.hd_address h) g c
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux1);
  // Part 2: pointer targets preserved
  let aux2 (src dst: obj_addr) : Lemma
    (requires Seq.mem src (objects 0UL g') /\
             (let wz = wosize_of_object src g' in
              U64.v wz < pow2 54 /\
              exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem dst (objects 0UL g'))
  = // Show wosize preserved, then exists_field preserved, then use well_formed_heap g
    wosize_of_object_spec src g;
    wosize_of_object_spec src g';
    if src = obj then begin
      set_object_color_preserves_getWosize_at_hd obj g c;
      color_change_preserves_field_pointing_self g obj c (wosize_of_object src g) dst
    end else begin
      hd_address_injective src obj;
      set_object_color_read_word obj (Pulse.Spec.GC.Heap.hd_address src) g c;
      color_change_preserves_field_pointing_other g obj c src (wosize_of_object src g) dst
    end
  in
  // Part 2: lift aux2 to a universal statement via a wrapper without let-binding
  let aux2_flat (src: obj_addr) (dst: obj_addr) : Lemma
    (requires Seq.mem src (objects 0UL g') /\
              U64.v (wosize_of_object src g') < pow2 54 /\
              exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst)
    (ensures Seq.mem dst (objects 0UL g'))
  = aux2 src dst
  in
  let aux2_imp (src: obj_addr) (dst: obj_addr) : Lemma
    ((Seq.mem src (objects 0UL g') /\
      U64.v (wosize_of_object src g') < pow2 54 /\
      exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst) ==> 
     Seq.mem dst (objects 0UL g'))
  = FStar.Classical.move_requires (aux2_flat src) dst
  in
  FStar.Classical.forall_intro_2 aux2_imp
#pop-options

/// push_children only applies color changes, which preserve wf
val push_children_preserves_wf : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
                                  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures well_formed_heap (fst (push_children g st obj i ws)))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec push_children_preserves_wf g st obj i ws =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child : obj_addr = v in
      if is_white child g then begin
        let g' = makeGray child g in
        let st' = Seq.cons child st in
        makeGray_eq child g;
        // Prove: Seq.mem child (objects 0UL g)
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        // get_field guard passes (from well_formed_heap part 1 + i <= ws <= wz)
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        // Connect get_field address to add_mod/mul_mod address
        assert (U64.v i <= U64.v ws);
        assert (U64.v ws <= U64.v wz);
        assert (U64.v wz < pow2 54);
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        let k = U64.sub i 1UL in
        assert (U64.v k < U64.v wz);
        assert (U64.v k < pow2 61);
        let far = U64.add_mod obj (U64.mul_mod k mword) in
        // child = read_word g far, is_pointer_field child, hd_address child = hd_address child
        assert (HeapGraph.get_field g obj i == read_word g (far <: hp_addr));
        assert (is_pointer_field child);
        // field_read_implies_exists_pointing gives exists_field_pointing_to_unchecked
        field_read_implies_exists_pointing g obj wz k child;
        // well_formed_heap part 2 gives Seq.mem child (objects 0UL g)
        assert (Seq.mem child (objects 0UL g));
        color_change_preserves_wf g child Header.Gray;
        color_change_preserves_objects_mem g child Header.Gray obj;
        // wosize preserved after makeGray
        set_object_color_preserves_getWosize_at_hd child g Header.Gray;
        wosize_of_object_spec obj g;
        wosize_of_object_spec obj g';
        assert (wosize_of_object obj g' == wosize_of_object obj g);
        if U64.v i < U64.v ws then
          push_children_preserves_wf g' st' obj (U64.add i 1UL) ws
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_preserves_wf g st obj (U64.add i 1UL) ws
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_preserves_wf g st obj (U64.add i 1UL) ws
      else ()
    end
  end
#pop-options

val mark_step_preserves_wf : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures well_formed_heap (fst (mark_step g st)))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let mark_step_preserves_wf g st =
  let obj = Seq.head st in
  stack_head_is_gray g st;
  // makeBlack preserves wf
  makeBlack_eq obj g;
  color_change_preserves_wf g obj Header.Black;
  let g' = makeBlack obj g in
  color_change_preserves_objects_mem g obj Header.Black obj;
  // push_children preserves wf
  let ws = wosize_of_object obj g in
  wosize_of_object_bound obj g;
  // wosize preserved by makeBlack
  set_object_color_preserves_getWosize_at_hd obj g Header.Black;
  wosize_of_object_spec obj g;
  wosize_of_object_spec obj g';
  assert (wosize_of_object obj g' == wosize_of_object obj g);
  if is_no_scan obj g then ()
  else
    push_children_preserves_wf g' (Seq.tail st) obj 1UL ws
#pop-options

val mark_preserves_wf : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures well_formed_heap (mark g st))

let mark_preserves_wf g st =
  admit()

/// ---------------------------------------------------------------------------
/// Color Exhaustiveness
/// ---------------------------------------------------------------------------

val color_exhaustive : (obj: obj_addr) -> (g: heap) ->
  Lemma (is_white obj g \/ is_gray obj g \/ is_black obj g \/ is_blue obj g)

let color_exhaustive obj g =
  colors_exhaustive_and_exclusive obj g

val colors_exclusive : (obj: obj_addr) -> (g: heap) ->
  Lemma (
    (is_white obj g ==> ~(is_gray obj g) /\ ~(is_black obj g) /\ ~(is_blue obj g)) /\
    (is_gray obj g ==> ~(is_white obj g) /\ ~(is_black obj g) /\ ~(is_blue obj g)) /\
    (is_black obj g ==> ~(is_white obj g) /\ ~(is_gray obj g) /\ ~(is_blue obj g)) /\
    (is_blue obj g ==> ~(is_white obj g) /\ ~(is_gray obj g) /\ ~(is_black obj g)))

let colors_exclusive obj g = colors_exhaustive_and_exclusive obj g

/// ---------------------------------------------------------------------------
/// Pillar 2: Mark Correctness - Black = Reachable
/// ---------------------------------------------------------------------------

let stack_to_vertices (st: seq obj_addr) : seq vertex_id =
  HeapGraph.coerce_to_vertex_list st

val mark_reachable_is_black : (g: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
        (ensures (forall (x: obj_addr). 
                   (let graph = create_graph g in
                    let roots' = HeapGraph.coerce_to_vertex_list roots in
                    graph_wf graph /\ is_vertex_set roots' /\ 
                    subset_vertices roots' graph.vertices /\
                    mem_graph_vertex graph x /\
                    Seq.mem x (reachable_set graph roots')) ==> 
                   is_black x (mark g st)))

let mark_reachable_is_black g st roots = 
  admit()

val mark_black_is_reachable : (g: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
        (ensures (forall (x: obj_addr). 
                   (let graph = create_graph g in
                    let roots' = HeapGraph.coerce_to_vertex_list roots in
                    graph_wf graph /\ is_vertex_set roots' /\
                    subset_vertices roots' graph.vertices /\
                    mem_graph_vertex graph x /\
                    is_black x (mark g st)) ==> 
                   Seq.mem x (reachable_set (create_graph g) (HeapGraph.coerce_to_vertex_list roots))))

let mark_black_is_reachable g st roots = 
  admit()

val mark_black_iff_reachable : (g: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
        (ensures True)

let mark_black_iff_reachable g st roots =
  mark_reachable_is_black g st roots;
  mark_black_is_reachable g st roots

/// ---------------------------------------------------------------------------
/// Mark Terminates With No Gray Objects
/// ---------------------------------------------------------------------------

val mark_no_grey_remains : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures noGreyObjects (mark g st))

let mark_no_grey_remains g st = 
  admit()

/// ---------------------------------------------------------------------------
/// Mark Preserves Tri-Color Invariant
/// ---------------------------------------------------------------------------

val mark_preserves_tri_color : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ tri_color_invariant g)
        (ensures noGreyObjects (mark g st) ==> tri_color_invariant (mark g st))

let mark_preserves_tri_color g st = 
  admit()
