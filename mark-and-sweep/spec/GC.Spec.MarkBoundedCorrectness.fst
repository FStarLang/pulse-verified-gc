/// ---------------------------------------------------------------------------
/// GC.Spec.MarkBoundedCorrectness — Correctness of bounded-stack mark phase
/// ---------------------------------------------------------------------------
///
/// Proves that `mark_bounded` satisfies all properties required by `mark_post`,
/// enabling the downstream sweep/coalesce correctness proofs to work with
/// the bounded-stack mark implementation.
///
/// Strategy: The heap produced by mark_step_bounded is identical to that of
/// mark_step (by mark_step_bounded_heap_eq). We exploit this to transfer
/// per-step properties proved for the unbounded mark (push_children_preserves_*)
/// to the bounded mark, then lift through the inner loop and outer rescan loop.

module GC.Spec.MarkBoundedCorrectness

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
open GC.Spec.MarkBounded
module HeapGraph = GC.Spec.HeapGraph
module Header = GC.Lib.Header
module SweepInv = GC.Spec.SweepInv
module Correctness = GC.Spec.Correctness

/// =========================================================================
/// Part 1: Bundled color invariant
/// =========================================================================

let mark_color_inv (h_init h_cur: heap) : prop =
  well_formed_heap h_cur /\
  Seq.length (objects 0UL h_cur) > 0 /\
  SweepInv.heap_objects_dense h_cur /\
  objects 0UL h_cur == objects 0UL h_init /\
  tri_color_invariant h_cur /\
  no_pointer_to_blue h_cur /\
  create_graph h_cur == create_graph h_init /\
  (forall (x: obj_addr). Seq.mem x (objects 0UL h_init) ==>
    wosize_of_object x h_cur == wosize_of_object x h_init) /\
  (forall (x: obj_addr) (i: U64.t). Seq.mem x (objects 0UL h_init) /\
    U64.v i >= 1 /\ U64.v i <= U64.v (wosize_of_object x h_init) ==>
    HeapGraph.get_field h_cur x i == HeapGraph.get_field h_init x i)

/// =========================================================================
/// Part 2: Per-step property preservation via heap equality
/// =========================================================================

/// mark_step_bounded preserves create_graph
let mark_step_bounded_preserves_create_graph
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st)
          (ensures create_graph (fst (mark_step_bounded g st cap)) == create_graph g)
  = mark_step_bounded_heap_eq g st st cap;
    let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    let g1 = makeBlack obj g in
    color_preserves_create_graph obj g Header.Black;
    color_change_preserves_wf g obj Header.Black;
    color_change_preserves_objects g obj Header.Black;
    color_preserves_wosize obj g Header.Black;
    wosize_of_object_bound obj g;
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_objects_mem g obj Header.Black obj;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_preserves_create_graph g1 (Seq.tail st) obj 1UL ws
    end

/// mark_step_bounded preserves wosize_of_object
let mark_step_bounded_preserves_wosize
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem x (objects 0UL g))
          (ensures wosize_of_object x (fst (mark_step_bounded g st cap)) ==
                   wosize_of_object x g)
  = mark_step_bounded_heap_eq g st st cap;
    let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    let g1 = makeBlack obj g in
    (if obj = x then color_preserves_wosize x g Header.Black
     else color_change_preserves_other_wosize obj x g Header.Black);
    wosize_of_object_spec x g; wosize_of_object_spec x g1;
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black obj;
      color_change_preserves_objects_mem g obj Header.Black x;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      wf_implies_object_fits g obj;
      wosize_of_object_bound obj g;
      color_preserves_object_fits obj obj g Header.Black;
      push_children_preserves_wosize g1 (Seq.tail st) obj 1UL ws x
    end

/// mark_step_bounded preserves get_field
let mark_step_bounded_preserves_get_field
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  (x: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem x (objects 0UL g) /\
                   U64.v j <= U64.v (wosize_of_object x g))
          (ensures HeapGraph.get_field (fst (mark_step_bounded g st cap)) x j ==
                   HeapGraph.get_field g x j)
  = mark_step_bounded_heap_eq g st st cap;
    let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    let g1 = makeBlack obj g in
    color_preserves_get_field obj x g Header.Black j;
    color_change_preserves_wf g obj Header.Black;
    color_change_preserves_objects g obj Header.Black;
    color_change_preserves_objects_mem g obj Header.Black x;
    color_change_preserves_objects_mem g obj Header.Black obj;
    set_object_color_preserves_getWosize_at_hd obj g Header.Black;
    wosize_of_object_spec x g; wosize_of_object_spec x g1;
    wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then ()
    else begin
      wf_implies_object_fits g obj;
      wosize_of_object_bound obj g;
      color_preserves_object_fits obj obj g Header.Black;
      push_children_preserves_get_field g1 (Seq.tail st) obj 1UL ws x j
    end

/// =========================================================================
/// Part 3: mark_step_bounded preserves tri_color_invariant
/// =========================================================================

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
val mark_step_bounded_preserves_tri_color :
  (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) -> (cap: nat) ->
  Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  tri_color_invariant g)
        (ensures tri_color_invariant (fst (mark_step_bounded g st cap)))

let mark_step_bounded_preserves_tri_color g st cap =
  mark_step_bounded_heap_eq g st st cap;
  let obj = Seq.head st in
  let st' = Seq.tail st in
  bounded_stack_head_is_gray g st;
  let g1 = makeBlack obj g in
  makeBlack_eq obj g;
  makeBlack_is_black obj g;
  color_change_preserves_objects g obj Header.Black;
  color_change_preserves_wf g obj Header.Black;
  let ws = wosize_of_object obj g in
  let (g_final, _) = mark_step g st in
  let objs = objects 0UL g in
  wosize_of_object_bound obj g;
  if is_no_scan obj g then
    assert (objects 0UL g_final == objs)
  else begin
    color_change_preserves_objects_mem g obj Header.Black obj;
    set_object_color_preserves_getWosize_at_hd obj g Header.Black;
    wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
    push_children_preserves_objects g1 st' obj 1UL ws
  end;
  assert (objects 0UL g_final == objs);
  let aux (b: obj_addr) (child: obj_addr) : Lemma
    (requires Seq.mem b objs /\ is_black b g_final /\
             ~(is_no_scan b g_final) /\ points_to g_final b child)
    (ensures ~(is_white (resolve_object child g_final) g_final))
  = color_change_preserves_resolve obj child g Header.Black;
    assert (resolve_object child g1 == resolve_object child g);
    let rc = resolve_object child g in
    if is_no_scan obj g then begin
      if b = obj then begin
        color_preserves_is_no_scan obj g Header.Black;
        assert False
      end else begin
        hd_address_injective b obj;
        color_change_preserves_other_color obj b g Header.Black;
        is_black_iff b g; is_black_iff b g1;
        color_change_preserves_points_to_other g obj Header.Black b child;
        color_change_preserves_other_is_no_scan obj b g Header.Black;
        assert (~(is_white rc g));
        if rc = obj then begin
          is_black_iff obj g1; is_white_iff obj g1;
          colors_exhaustive_and_exclusive obj g1
        end else begin
          hd_address_injective rc obj;
          color_change_preserves_other_color obj rc g Header.Black;
          is_white_iff rc g; is_white_iff rc g1
        end
      end
    end else begin
      color_change_preserves_objects_mem g obj Header.Black obj;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_preserves_resolve g1 st' obj 1UL ws child;
      assert (resolve_object child g_final == rc);
      if b = obj then begin
        push_children_preserves_points_to g1 st' obj 1UL ws obj child;
        color_change_preserves_points_to_self g obj Header.Black child;
        assert (points_to g obj child);
        color_change_preserves_objects_mem g obj Header.Black obj;
        push_children_obj_children_non_white g1 st' obj child;
        assert (~(is_white rc g_final))
      end else begin
        hd_address_injective b obj;
        color_change_preserves_objects_mem g obj Header.Black b;
        push_children_black_backward g1 st' obj 1UL ws b;
        color_change_preserves_other_color obj b g Header.Black;
        is_black_iff b g; is_black_iff b g1;
        assert (is_black b g);
        push_children_preserves_points_to g1 st' obj 1UL ws b child;
        color_change_preserves_points_to_other g obj Header.Black b child;
        assert (points_to g b child);
        push_children_preserves_is_no_scan g1 st' obj 1UL ws b;
        color_change_preserves_other_is_no_scan obj b g Header.Black;
        assert (~(is_no_scan b g));
        assert (~(is_white rc g));
        wosize_of_object_bound b g;
        points_to_target_in_objects g b child;
        assert (Seq.mem child (objects 0UL g));
        wf_infix_wf g;
        resolve_object_in_objects child g (objects 0UL g);
        assert (Seq.mem rc (objects 0UL g));
        if rc = obj then begin
          push_children_preserves_parent_black g1 st' obj 1UL ws;
          is_black_iff obj g_final; is_white_iff obj g_final;
          colors_exhaustive_and_exclusive obj g_final
        end else begin
          hd_address_injective rc obj;
          color_change_preserves_other_color obj rc g Header.Black;
          is_white_iff rc g; is_white_iff rc g1;
          assert (~(is_white rc g1));
          color_change_preserves_objects_mem g obj Header.Black rc;
          push_children_no_new_white g1 st' obj 1UL ws rc
        end
      end
    end
  in
  let aux2 (b: obj_addr) (child: obj_addr) : Lemma
    (Seq.mem b objs ==> is_black b g_final ==> ~(is_no_scan b g_final) ==> 
     points_to g_final b child ==> ~(is_white (resolve_object child g_final) g_final))
  = FStar.Classical.move_requires (aux b) child
  in
  FStar.Classical.forall_intro_2 aux2
#pop-options

/// =========================================================================
/// Part 4: mark_step_bounded preserves no_pointer_to_blue
/// =========================================================================

let mark_step_bounded_preserves_points_to
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  (src dst: obj_addr)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem src (objects 0UL g))
          (ensures points_to (fst (mark_step_bounded g st cap)) src dst ==
                   points_to g src dst)
  = mark_step_bounded_heap_eq g st st cap;
    let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    let g1 = makeBlack obj g in
    if src = obj then
      color_change_preserves_points_to_self g obj Header.Black dst
    else begin
      hd_address_injective src obj;
      color_change_preserves_points_to_other g obj Header.Black src dst
    end;
    assert (points_to g1 src dst == points_to g src dst);
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black obj;
      color_change_preserves_objects_mem g obj Header.Black src;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      wosize_of_object_bound obj g;
      push_children_preserves_points_to g1 (Seq.tail st) obj 1UL ws src dst
    end

let mark_step_bounded_preserves_blue
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem x (objects 0UL g) /\ is_blue x g)
          (ensures is_blue x (fst (mark_step_bounded g st cap)))
  = mark_step_bounded_heap_eq g st st cap;
    let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    let g1 = makeBlack obj g in
    is_gray_iff obj g; is_blue_iff x g;
    colors_exhaustive_and_exclusive obj g;
    assert (obj <> x);
    hd_address_injective x obj;
    color_change_preserves_other_color obj x g Header.Black;
    is_blue_iff x g; is_blue_iff x g1;
    assert (is_blue x g1);
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black x;
      color_change_preserves_objects_mem g obj Header.Black obj;
      wosize_of_object_bound obj g;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_preserves_blue g1 (Seq.tail st) obj 1UL ws x
    end

let mark_step_bounded_no_new_blue
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat) (x: obj_addr)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.mem x (objects 0UL g) /\ ~(is_blue x g))
          (ensures ~(is_blue x (fst (mark_step_bounded g st cap))))
  = mark_step_bounded_heap_eq g st st cap;
    let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    let g1 = makeBlack obj g in
    set_color_preserves_not_blue obj x g Header.Black;
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black obj;
      wosize_of_object_bound obj g;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_no_new_blue g1 (Seq.tail st) obj 1UL ws x
    end

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let mark_step_bounded_preserves_no_pointer_to_blue
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   no_pointer_to_blue g)
          (ensures no_pointer_to_blue (fst (mark_step_bounded g st cap)))
  = let g' = fst (mark_step_bounded g st cap) in
    mark_step_bounded_preserves_objects g st cap;
    let aux (src dst: obj_addr) : Lemma
      (requires Seq.mem src (objects 0UL g') /\ ~(is_blue src g') /\ points_to g' src dst)
      (ensures ~(is_blue dst g'))
    = assert (Seq.mem src (objects 0UL g));
      mark_step_bounded_preserves_points_to g st cap src dst;
      assert (points_to g src dst);
      if is_blue src g then
        mark_step_bounded_preserves_blue g st cap src
      else begin
        assert (~(is_blue dst g));
        wosize_of_object_bound src g;
        points_to_target_in_objects g src dst;
        mark_step_bounded_no_new_blue g st cap dst
      end
    in
    let aux2 (src dst: obj_addr) : Lemma
      (Seq.mem src (objects 0UL g') ==> ~(is_blue src g') ==> points_to g' src dst ==>
       ~(is_blue dst g'))
    = FStar.Classical.move_requires (aux src) dst
    in
    FStar.Classical.forall_intro_2 aux2
#pop-options

/// =========================================================================
/// Part 5: mark_step_bounded preserves mark_color_inv
/// =========================================================================

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let mark_step_bounded_preserves_color_inv
  (h_init: heap) (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires mark_color_inv h_init g /\ bounded_stack_props g st)
          (ensures mark_color_inv h_init (fst (mark_step_bounded g st cap)))
  = let g' = fst (mark_step_bounded g st cap) in
    mark_step_bounded_preserves_bsp g st cap;
    mark_step_bounded_preserves_objects g st cap;
    mark_step_bounded_preserves_density g st cap;
    bounded_stack_head_is_gray g st;
    makeBlack_eq (Seq.head st) g;
    color_change_preserves_wf g (Seq.head st) Header.Black;
    mark_step_bounded_heap_eq g st st cap;
    let obj = Seq.head st in
    let g1 = makeBlack obj g in
    let ws = wosize_of_object obj g in
    (if is_no_scan obj g then ()
     else begin
       color_change_preserves_objects_mem g obj Header.Black obj;
       set_object_color_preserves_getWosize_at_hd obj g Header.Black;
       wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
       wosize_of_object_bound obj g;
       push_children_preserves_wf g1 (Seq.tail st) obj 1UL ws
     end);
    mark_step_bounded_preserves_tri_color g st cap;
    mark_step_bounded_preserves_no_pointer_to_blue g st cap;
    mark_step_bounded_preserves_create_graph g st cap;
    let aux_ws (x: obj_addr) : Lemma
      (requires Seq.mem x (objects 0UL h_init))
      (ensures wosize_of_object x g' == wosize_of_object x h_init)
    = mark_step_bounded_preserves_wosize g st cap x
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_ws);
    let aux_gf (x: obj_addr) (i: U64.t) : Lemma
      (Seq.mem x (objects 0UL h_init) /\ U64.v i >= 1 /\
       U64.v i <= U64.v (wosize_of_object x h_init) ==>
       HeapGraph.get_field g' x i == HeapGraph.get_field h_init x i)
    = if Seq.mem x (objects 0UL h_init) && U64.v i >= 1 &&
         U64.v i <= U64.v (wosize_of_object x h_init)
      then begin
        assert (wosize_of_object x g == wosize_of_object x h_init);
        mark_step_bounded_preserves_get_field g st cap x i
      end
    in
    FStar.Classical.forall_intro_2 aux_gf
#pop-options

/// =========================================================================
/// Part 6: mark_inner_loop preserves mark_color_inv
/// =========================================================================

let rec mark_inner_loop_preserves_color_inv
  (h_init: heap) (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires mark_color_inv h_init g /\ bounded_stack_props g st)
          (ensures mark_color_inv h_init (fst (mark_inner_loop g st cap fuel)))
          (decreases fuel)
  = if fuel = 0 || Seq.length st = 0 then ()
    else begin
      mark_step_bounded_preserves_color_inv h_init g st cap;
      mark_step_bounded_preserves_bsp g st cap;
      let (g', st') = mark_step_bounded g st cap in
      mark_inner_loop_preserves_color_inv h_init g' st' cap (fuel - 1)
    end

/// =========================================================================
/// Part 7: mark_bounded preserves mark_color_inv
/// =========================================================================

let rec mark_bounded_preserves_color_inv
  (h_init: heap) (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires mark_color_inv h_init g)
          (ensures mark_color_inv h_init (mark_bounded g cap fuel))
          (decreases fuel)
  = if fuel = 0 then ()
    else begin
      let st = rescan_heap g (objects 0UL g) Seq.empty cap in
      rescan_heap_bounded_stack_props g (objects 0UL g) cap;
      rescan_heap_cap_bound g (objects 0UL g) Seq.empty cap;
      if Seq.length st = 0 then ()
      else begin
        let inner_fuel = count_non_black g in
        mark_inner_loop_preserves_color_inv h_init g st cap inner_fuel;
        mark_inner_loop_preserves_inv g st cap inner_fuel;
        mark_inner_loop_preserves_objects g st cap inner_fuel;
        let (g', _) = mark_inner_loop g st cap inner_fuel in
        mark_bounded_preserves_color_inv h_init g' cap (fuel - 1)
      end
    end

/// =========================================================================
/// Part 8: Forward reachability (reachable → black)
/// =========================================================================

val mark_step_bounded_gray_becomes_black :
  (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) -> (cap: nat) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  Seq.mem x (objects 0UL g) /\
                  (is_gray x g \/ is_black x g))
        (ensures (is_gray x (fst (mark_step_bounded g st cap)) \/
                  is_black x (fst (mark_step_bounded g st cap))))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let mark_step_bounded_gray_becomes_black g st cap x =
  mark_step_bounded_heap_eq g st st cap;
  let obj = Seq.head st in
  bounded_stack_head_is_gray g st;
  makeBlack_eq obj g;
  let g1 = makeBlack obj g in
  let ws = wosize_of_object obj g in
  if x = obj then begin
    makeBlack_is_black obj g;
    assert (is_black x g1);
    if is_no_scan obj g then begin
      is_black_iff x g1
    end else begin
      push_children_preserves_parent_black g1 (Seq.tail st) obj 1UL ws;
      is_black_iff x (fst (push_children g1 (Seq.tail st) obj 1UL ws))
    end
  end else begin
    hd_address_injective x obj;
    color_change_preserves_other_color obj x g Header.Black;
    if is_gray x g then begin
      is_gray_iff x g; is_gray_iff x g1;
      if is_no_scan obj g then ()
      else begin
        color_change_preserves_wf g obj Header.Black;
        color_change_preserves_objects g obj Header.Black;
        color_change_preserves_objects_mem g obj Header.Black obj;
        color_change_preserves_objects_mem g obj Header.Black x;
        wosize_of_object_bound obj g;
        set_object_color_preserves_getWosize_at_hd obj g Header.Black;
        wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
        colors_exclusive x g1;
        push_children_no_new_white g1 (Seq.tail st) obj 1UL ws x;
        push_children_no_new_blue g1 (Seq.tail st) obj 1UL ws x;
        push_children_not_blackens g1 (Seq.tail st) obj 1UL ws x;
        is_gray_iff x g1; is_black_iff x g1;
        let g_final = fst (push_children g1 (Seq.tail st) obj 1UL ws) in
        color_change_preserves_objects g obj Header.Black;
        color_change_preserves_objects_mem g obj Header.Black x;
        push_children_preserves_objects g1 (Seq.tail st) obj 1UL ws;
        assert (Seq.mem x (objects 0UL g_final));
        color_exhaustive x g_final
      end
    end else begin
      is_black_iff x g; is_black_iff x g1;
      if is_no_scan obj g then ()
      else
        push_children_preserves_other_black g1 (Seq.tail st) obj 1UL ws x
    end
  end
#pop-options

val mark_inner_loop_gray_or_black_preserved :
  (g: heap) -> (st: seq obj_addr) -> (cap: nat) -> (fuel: nat) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  Seq.length (objects 0UL g) > 0 /\
                  SweepInv.heap_objects_dense g /\
                  Seq.mem x (objects 0UL g) /\
                  (is_gray x g \/ is_black x g))
        (ensures (let g' = fst (mark_inner_loop g st cap fuel) in
                  is_gray x g' \/ is_black x g'))
        (decreases fuel)

let rec mark_inner_loop_gray_or_black_preserved g st cap fuel x =
  if fuel = 0 || Seq.length st = 0 then ()
  else begin
    mark_step_bounded_gray_becomes_black g st cap x;
    mark_step_bounded_preserves_bsp g st cap;
    mark_step_bounded_preserves_objects g st cap;
    mark_step_bounded_preserves_density g st cap;
    let (g', st') = mark_step_bounded g st cap in
    mark_inner_loop_gray_or_black_preserved g' st' cap (fuel - 1) x
  end

val mark_bounded_gray_or_black_preserved :
  (g: heap) -> (cap: nat{cap > 0}) -> (fuel: nat) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  Seq.length (objects 0UL g) > 0 /\
                  SweepInv.heap_objects_dense g /\
                  Seq.mem x (objects 0UL g) /\
                  (is_gray x g \/ is_black x g))
        (ensures (let g' = mark_bounded g cap fuel in
                  is_gray x g' \/ is_black x g'))
        (decreases fuel)

let rec mark_bounded_gray_or_black_preserved g cap fuel x =
  if fuel = 0 then ()
  else begin
    let st = rescan_heap g (objects 0UL g) Seq.empty cap in
    rescan_heap_bounded_stack_props g (objects 0UL g) cap;
    rescan_heap_cap_bound g (objects 0UL g) Seq.empty cap;
    if Seq.length st = 0 then ()
    else begin
      let inner_fuel = count_non_black g in
      mark_inner_loop_gray_or_black_preserved g st cap inner_fuel x;
      mark_inner_loop_preserves_inv g st cap inner_fuel;
      mark_inner_loop_preserves_objects g st cap inner_fuel;
      let (g', _) = mark_inner_loop g st cap inner_fuel in
      mark_bounded_gray_or_black_preserved g' cap (fuel - 1) x
    end
  end

let noGreyObjects_from_no_gray (g: heap)
  : Lemma (requires SweepInv.no_gray_objects g)
          (ensures noGreyObjects g)
  = let aux (obj: obj_addr) : Lemma
      (requires Seq.mem obj (objects 0UL g))
      (ensures not (is_gray obj g))
    = SweepInv.no_gray_elim obj g;
      is_gray_iff obj g
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// Forward: reachable objects are black after mark_bounded completes
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let mark_bounded_reachable_is_black
  (h_init: heap) (roots: seq obj_addr) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Seq.length (objects 0UL h_init) > 0 /\
      SweepInv.heap_objects_dense h_init /\
      root_props h_init roots /\
      mark_color_inv h_init h_init /\
      fuel >= count_non_black h_init /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures
      (let h_mark = mark_bounded h_init cap fuel in
       let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices ==>
       (forall (x: obj_addr). mem_graph_vertex graph x /\
         Seq.mem x (reachable_set graph roots') ==> is_black x h_mark)))
  = let h_mark = mark_bounded h_init cap fuel in
    let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    mark_bounded_preserves_color_inv h_init h_init cap fuel;
    mark_bounded_completes h_init cap fuel;
    mark_bounded_preserves_objects h_init cap fuel;
    mark_bounded_preserves_inv h_init cap fuel;
    let root_black (r: obj_addr) : Lemma
      (requires Seq.mem r roots) (ensures is_black r h_mark)
    = assert (is_gray r h_init \/ is_black r h_init);
      assert (Seq.mem r (objects 0UL h_init));
      mark_bounded_gray_or_black_preserved h_init cap fuel r;
      SweepInv.no_gray_elim r h_mark
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires root_black);
    let prove_x (x: obj_addr) : Lemma
      (requires graph_wf graph /\ is_vertex_set roots' /\
               subset_vertices roots' graph.vertices /\
               mem_graph_vertex graph x /\
               Seq.mem x (reachable_set graph roots'))
      (ensures is_black x h_mark)
    = assert (create_graph h_mark == graph);
      noGreyObjects_from_no_gray h_mark;
      assert (noGreyObjects h_mark);
      assert (tri_color_invariant h_mark);
      assert (no_pointer_to_blue h_mark);
      reachable_set_correct graph roots';
      FStar.Classical.exists_elim (is_black x h_mark) ()
        (fun (r: vertex_id{mem_graph_vertex graph r /\
                            Seq.mem r roots' /\ reachable graph r x}) ->
          vertex_is_obj_addr h_init r;
          let r' : obj_addr = r in
          HeapGraph.coerce_mem_lemma roots r';
          root_black r';
          FStar.Classical.exists_elim (is_black x h_mark) ()
            (fun (p: reach graph r x) ->
              black_reach_is_black graph h_mark r' x p))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_x)
#pop-options

/// =========================================================================
/// Part 9: Backward reachability (black → reachable)
/// =========================================================================

/// mark_step_bounded only blackens the head
val mark_step_bounded_black_origin :
  (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) -> (cap: nat) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  is_black x (fst (mark_step_bounded g st cap)) /\ ~(is_black x g))
        (ensures x == Seq.head st)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let mark_step_bounded_black_origin g st cap x =
  mark_step_bounded_heap_eq g st st cap;
  let obj = Seq.head st in
  bounded_stack_head_is_gray g st;
  makeBlack_eq obj g;
  let g' = makeBlack obj g in
  let ws = wosize_of_object obj g in
  if is_no_scan obj g then begin
    if x = obj then ()
    else begin
      color_change_preserves_other_color obj x g Header.Black;
      is_black_iff x g;
      is_black_iff x g'
    end
  end else begin
    if x = obj then ()
    else begin
      color_change_preserves_other_color obj x g Header.Black;
      is_black_iff x g;
      is_black_iff x g';
      assert (~(is_black x g'));
      push_children_not_blackens g' (Seq.tail st) obj 1UL ws x
    end
  end
#pop-options

/// push_children_bounded output stack elements are reachable
val push_children_bounded_stack_reachable :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  (graph: graph_state) -> (roots': vertex_set) ->
  Lemma
    (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
             is_vertex_set (HeapGraph.coerce_to_vertex_list (objects 0UL g)) /\
             ws == wosize_of_object obj g /\
             U64.v (wosize_of_object obj g) < pow2 54 /\
             graph == create_graph g /\ graph_wf graph /\
             is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
             Seq.mem obj (reachable_set graph roots') /\
             (forall y. Seq.mem y st ==> Seq.mem y (reachable_set graph roots')) /\
             ~(is_no_scan obj g) /\ HeapGraph.object_fits_in_heap obj g)
    (ensures (forall y. Seq.mem y (snd (push_children_bounded g st obj i ws cap)) ==>
                        Seq.mem y (reachable_set graph roots')))
    (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let rec push_children_bounded_stack_reachable g st obj i ws cap graph roots' =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child_raw : obj_addr = v in
      let child = resolve_object child_raw g in
      if is_white child g then begin
        objects_is_vertex_set g;
        HeapGraph.pointer_field_is_graph_edge g (objects 0UL g) obj i;
        graph_vertices_mem g child_raw;
        wf_resolve_identity g child_raw;
        assert (child == child_raw);
        graph_vertices_mem g obj;
        reachable_successor_closed graph roots' obj child;
        let g' = makeGray child g in
        let st'_b =
          if Seq.length st < cap then Seq.cons child st
          else st
        in
        let prove_st' (y: obj_addr) : Lemma
          (requires Seq.mem y st'_b)
          (ensures Seq.mem y (reachable_set graph roots'))
        = if Seq.length st < cap then
            Seq.mem_cons child st
          else ()
        in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_st');
        if U64.v i < U64.v ws then begin
          makeGray_eq child g;
          color_preserves_create_graph child g Header.Gray;
          color_change_preserves_wf g child Header.Gray;
          color_change_preserves_objects g child Header.Gray;
          if child = obj then begin
            color_preserves_wosize obj g Header.Gray;
            color_preserves_is_no_scan obj g Header.Gray
          end else begin
            color_change_preserves_other_wosize child obj g Header.Gray;
            color_change_preserves_other_is_no_scan child obj g Header.Gray
          end;
          objects_is_vertex_set g';
          wosize_of_object_bound child g;
          color_preserves_object_fits child obj g Header.Gray;
          push_children_bounded_stack_reachable g' st'_b obj (U64.add i 1UL) ws cap graph roots'
        end else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_bounded_stack_reachable g st obj (U64.add i 1UL) ws cap graph roots'
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_bounded_stack_reachable g st obj (U64.add i 1UL) ws cap graph roots'
      else ()
    end
  end
#pop-options

/// push_children newly gray objects are children of the parent
val push_children_newly_gray_is_child :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma
    (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
             ~(is_no_scan obj g) /\
             ws == wosize_of_object obj g /\
             U64.v (wosize_of_object obj g) < pow2 54 /\
             graph_wf (create_graph g) /\
             is_white x g /\
             is_gray x (fst (push_children g st obj i ws)))
    (ensures mem_graph_edge (create_graph g) obj x)
    (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let rec push_children_newly_gray_is_child g st obj i ws x =
  if U64.v i > U64.v ws then begin
    is_gray_iff x g; is_white_iff x g;
    colors_exhaustive_and_exclusive x g
  end else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child_raw : obj_addr = v in
      let child = resolve_object child_raw g in
      if is_white child g then begin
        let g' = makeGray child g in
        let st' = Seq.cons child st in
        makeGray_eq child g;
        if child = x then begin
          objects_is_vertex_set g;
          wf_implies_object_fits g obj;
          HeapGraph.pointer_field_is_graph_edge g (objects 0UL g) obj i;
          assert (mem_graph_edge (create_graph g) obj child_raw);
          assert (Seq.mem child_raw (create_graph g).vertices);
          graph_vertices_mem g child_raw;
          wf_resolve_identity g child_raw
        end else begin
          hd_address_injective x child;
          color_change_preserves_other_color child x g Header.Gray;
          is_white_iff x g; is_white_iff x g';
          if U64.v i < U64.v ws then begin
            // Derive Seq.mem child (objects 0UL g) via graph_wf
            objects_is_vertex_set g;
            wf_implies_object_fits g obj;
            HeapGraph.pointer_field_is_graph_edge g (objects 0UL g) obj i;
            assert (Seq.mem child_raw (create_graph g).vertices);
            graph_vertices_mem g child_raw;
            wf_resolve_identity g child_raw;
            assert (child == child_raw);
            assert (Seq.mem child (objects 0UL g));
            color_change_preserves_wf g child Header.Gray;
            color_change_preserves_objects g child Header.Gray;
            color_change_preserves_objects_mem g child Header.Gray obj;
            if child = obj then begin
              color_preserves_wosize obj g Header.Gray;
              color_preserves_is_no_scan obj g Header.Gray
            end else begin
              color_change_preserves_other_wosize child obj g Header.Gray;
              color_change_preserves_other_is_no_scan child obj g Header.Gray
            end;
            wosize_of_object_spec obj g; wosize_of_object_spec obj g';
            color_preserves_create_graph child g Header.Gray;
            push_children_newly_gray_is_child g' st' obj (U64.add i 1UL) ws x
          end else begin
            is_gray_iff x g'; is_white_iff x g';
            colors_exhaustive_and_exclusive x g'
          end
        end
      end else begin
        if U64.v i < U64.v ws then
          push_children_newly_gray_is_child g st obj (U64.add i 1UL) ws x
        else begin
          is_gray_iff x g; is_white_iff x g;
          colors_exhaustive_and_exclusive x g
        end
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_newly_gray_is_child g st obj (U64.add i 1UL) ws x
      else begin
        is_gray_iff x g; is_white_iff x g;
        colors_exhaustive_and_exclusive x g
      end
    end
  end
#pop-options

/// If x is newly gray after mark_step_bounded, it's reachable
let mark_step_bounded_makes_gray_reachable
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  (x: obj_addr) (graph: graph_state) (roots': vertex_set)
  : Lemma
    (requires well_formed_heap g /\ bounded_stack_props g st /\
             graph == create_graph g /\ graph_wf graph /\
             is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
             is_white x g /\
             is_gray x (fst (mark_step_bounded g st cap)) /\
             Seq.mem (Seq.head st) (reachable_set graph roots'))
    (ensures Seq.mem x (reachable_set graph roots'))
  = mark_step_bounded_heap_eq g st st cap;
    let hd = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq hd g;
    let g1 = makeBlack hd g in
    let ws = wosize_of_object hd g in
    is_white_iff x g; is_gray_iff hd g;
    assert (x <> hd);
    hd_address_injective x hd;
    color_change_preserves_other_color hd x g Header.Black;
    is_white_iff x g; is_white_iff x g1;
    if is_no_scan hd g then begin
      is_gray_iff x g1;
      colors_exhaustive_and_exclusive x g1
    end else begin
      wosize_of_object_bound hd g;
      color_change_preserves_wf g hd Header.Black;
      color_change_preserves_objects g hd Header.Black;
      color_change_preserves_objects_mem g hd Header.Black hd;
      set_object_color_preserves_getWosize_at_hd hd g Header.Black;
      wosize_of_object_spec hd g; wosize_of_object_spec hd g1;
      color_preserves_is_no_scan hd g Header.Black;
      color_preserves_create_graph hd g Header.Black;
      push_children_newly_gray_is_child g1 (Seq.tail st) hd 1UL ws x;
      graph_vertices_mem g hd;
      graph_vertices_mem g x;
      reachable_successor_closed graph roots' hd x
    end

/// Combined gray-or-black backward invariant for mark_inner_loop
val mark_inner_loop_gray_or_black_backward :
  (h_init: heap) -> (g: heap) -> (st: seq obj_addr) -> (cap: nat) -> (fuel: nat) ->
  (graph: graph_state) -> (roots': vertex_set) ->
  Lemma
    (requires well_formed_heap g /\ bounded_stack_props g st /\
             Seq.length (objects 0UL g) > 0 /\
             SweepInv.heap_objects_dense g /\
             mark_color_inv h_init g /\
             graph == create_graph h_init /\ graph_wf graph /\
             is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
             (forall x. Seq.mem x (objects 0UL g) /\ (is_gray x g \/ is_black x g) ==>
                        Seq.mem x (reachable_set graph roots')) /\
             (forall x. Seq.mem x st ==> Seq.mem x (reachable_set graph roots')))
    (ensures (let g' = fst (mark_inner_loop g st cap fuel) in
             (forall x. Seq.mem x (objects 0UL g) /\ (is_gray x g' \/ is_black x g') ==>
                        Seq.mem x (reachable_set graph roots'))))
    (decreases fuel)

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
let rec mark_inner_loop_gray_or_black_backward h_init g st cap fuel graph roots' =
  if fuel = 0 || Seq.length st = 0 then ()
  else begin
    let (g', st') = mark_step_bounded g st cap in
    let hd = Seq.head st in
    mark_step_bounded_preserves_objects g st cap;
    let prove_gb_in_g' (x: obj_addr)
      : Lemma (requires Seq.mem x (objects 0UL g') /\ (is_gray x g' \/ is_black x g'))
              (ensures Seq.mem x (reachable_set graph roots'))
    = assert (Seq.mem x (objects 0UL g));
      if is_gray x g || is_black x g then ()
      else begin
        if is_blue x g then begin
          mark_step_bounded_preserves_blue g st cap x;
          is_blue_iff x g'; is_gray_iff x g'; is_black_iff x g';
          colors_exhaustive_and_exclusive x g'
        end else begin
          if is_black x g' then begin
            mark_step_bounded_black_origin g st cap x;
            bounded_stack_head_is_gray g st;
            is_gray_iff hd g; is_white_iff hd g;
            colors_exhaustive_and_exclusive hd g
          end else begin
            // x is not gray/black/blue in g, so white
            color_exhaustive x g;
            assert (is_white x g);
            // x is gray or black in g', but not black, so gray
            assert (is_gray x g');
            mark_step_bounded_makes_gray_reachable g st cap x graph roots'
          end
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_gb_in_g');
    bounded_stack_head_is_gray g st;
    makeBlack_eq hd g;
    let g1 = makeBlack hd g in
    let ws = wosize_of_object hd g in
    if is_no_scan hd g then begin
      let prove_tail (y: obj_addr) : Lemma
        (requires Seq.mem y st')
        (ensures Seq.mem y (reachable_set graph roots'))
      = Seq.lemma_mem_inversion st
      in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_tail)
    end else begin
      color_preserves_create_graph hd g Header.Black;
      color_change_preserves_wf g hd Header.Black;
      color_change_preserves_objects g hd Header.Black;
      color_preserves_is_no_scan hd g Header.Black;
      color_preserves_wosize hd g Header.Black;
      wosize_of_object_bound hd g;
      objects_is_vertex_set g1;
      wf_implies_object_fits g hd;
      color_preserves_object_fits hd hd g Header.Black;
      let prove_tail (y: obj_addr) : Lemma
        (requires Seq.mem y (Seq.tail st))
        (ensures Seq.mem y (reachable_set graph roots'))
      = Seq.lemma_mem_inversion st
      in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_tail);
      push_children_bounded_stack_reachable g1 (Seq.tail st) hd 1UL ws cap graph roots'
    end;
    mark_step_bounded_preserves_bsp g st cap;
    mark_step_bounded_preserves_density g st cap;
    mark_step_bounded_preserves_color_inv h_init g st cap;
    mark_inner_loop_gray_or_black_backward h_init g' st' cap (fuel - 1) graph roots'
  end
#pop-options

/// Backward for mark_inner_loop (black only)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
val mark_inner_loop_backward_inv :
  (h_init: heap) -> (g: heap) -> (st: seq obj_addr) -> (cap: nat) -> (fuel: nat) ->
  (graph: graph_state) -> (roots': vertex_set) ->
  Lemma
    (requires well_formed_heap g /\ bounded_stack_props g st /\
             Seq.length (objects 0UL g) > 0 /\
             SweepInv.heap_objects_dense g /\
             mark_color_inv h_init g /\
             graph == create_graph h_init /\ graph_wf graph /\
             is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
             (forall x. is_black x g /\ Seq.mem x (objects 0UL g) ==>
                        Seq.mem x (reachable_set graph roots')) /\
             (forall x. Seq.mem x st ==> Seq.mem x (reachable_set graph roots')))
    (ensures (forall x. Seq.mem x (objects 0UL g) /\
                        is_black x (fst (mark_inner_loop g st cap fuel)) ==>
                        Seq.mem x (reachable_set graph roots')))
    (decreases fuel)

let rec mark_inner_loop_backward_inv h_init g st cap fuel graph roots' =
  if fuel = 0 || Seq.length st = 0 then ()
  else begin
    let (g', st') = mark_step_bounded g st cap in
    let hd = Seq.head st in
    let prove_black_in_g' (x: obj_addr)
      : Lemma (requires Seq.mem x (objects 0UL g') /\ is_black x g')
              (ensures Seq.mem x (reachable_set graph roots'))
    = mark_step_bounded_preserves_objects g st cap;
      if is_black x g then ()
      else begin
        mark_step_bounded_black_origin g st cap x;
        assert (Seq.mem hd st)
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_black_in_g');
    mark_step_bounded_preserves_objects g st cap;
    bounded_stack_head_is_gray g st;
    makeBlack_eq hd g;
    let g1 = makeBlack hd g in
    let ws = wosize_of_object hd g in
    if is_no_scan hd g then begin
      let prove_tail (y: obj_addr) : Lemma
        (requires Seq.mem y st') (ensures Seq.mem y (reachable_set graph roots'))
      = Seq.lemma_mem_inversion st
      in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_tail)
    end else begin
      color_preserves_create_graph hd g Header.Black;
      color_change_preserves_wf g hd Header.Black;
      color_change_preserves_objects g hd Header.Black;
      color_preserves_is_no_scan hd g Header.Black;
      color_preserves_wosize hd g Header.Black;
      wosize_of_object_bound hd g;
      objects_is_vertex_set g1;
      wf_implies_object_fits g hd;
      color_preserves_object_fits hd hd g Header.Black;
      let prove_tail (y: obj_addr) : Lemma
        (requires Seq.mem y (Seq.tail st)) (ensures Seq.mem y (reachable_set graph roots'))
      = Seq.lemma_mem_inversion st
      in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_tail);
      push_children_bounded_stack_reachable g1 (Seq.tail st) hd 1UL ws cap graph roots'
    end;
    mark_step_bounded_preserves_bsp g st cap;
    mark_step_bounded_preserves_density g st cap;
    mark_step_bounded_preserves_color_inv h_init g st cap;
    mark_inner_loop_backward_inv h_init g' st' cap (fuel - 1) graph roots'
  end
#pop-options

/// rescan_heap output stack elements are reachable
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let rec rescan_heap_stack_reachable
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  (graph: graph_state{graph_wf graph}) (roots': vertex_set{subset_vertices roots' graph.vertices})
  : Lemma
    (requires (forall (x: obj_addr). Seq.mem x objs ==> Seq.mem x (objects 0UL g)) /\
             (forall x. Seq.mem x st ==> Seq.mem x (reachable_set graph roots')) /\
             (forall x. Seq.mem x (objects 0UL g) /\ (is_gray x g \/ is_black x g) ==>
                        Seq.mem x (reachable_set graph roots')))
    (ensures (forall x. Seq.mem x (rescan_heap g objs st cap) ==>
                        Seq.mem x (reachable_set graph roots')))
    (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let st' =
        if is_gray obj g && not (Seq.mem obj st) && Seq.length st < cap then
          Seq.cons obj st
        else st
      in
      let prove_st' (y: obj_addr) : Lemma
        (requires Seq.mem y st') (ensures Seq.mem y (reachable_set graph roots'))
      = if is_gray obj g && not (Seq.mem obj st) && Seq.length st < cap then begin
          Seq.mem_cons obj st;
          if y = obj then begin
            Seq.mem_cons (Seq.head objs) (Seq.tail objs);
            assert (Seq.mem obj (objects 0UL g))
          end
        end
      in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_st');
      let prove_tail_subset (y: obj_addr) : Lemma
        (requires Seq.mem y (Seq.tail objs)) (ensures Seq.mem y (objects 0UL g))
      = Seq.mem_cons (Seq.head objs) (Seq.tail objs);
        assert (Seq.mem y objs)
      in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_tail_subset);
      rescan_heap_stack_reachable g (Seq.tail objs) st' cap graph roots'
    end
#pop-options

/// Full backward for mark_bounded
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
val mark_bounded_backward_inv :
  (h_init: heap) -> (g: heap) -> (cap: nat{cap > 0}) -> (fuel: nat) ->
  (graph: graph_state) -> (roots': vertex_set) ->
  Lemma
    (requires well_formed_heap g /\
             Seq.length (objects 0UL g) > 0 /\
             SweepInv.heap_objects_dense g /\
             mark_color_inv h_init g /\
             graph == create_graph h_init /\ graph_wf graph /\
             is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
             (forall x. Seq.mem x (objects 0UL g) /\ is_black x g ==>
                        Seq.mem x (reachable_set graph roots')) /\
             (forall x. Seq.mem x (objects 0UL g) /\ (is_gray x g \/ is_black x g) ==>
                        Seq.mem x (reachable_set graph roots')))
    (ensures (forall x. Seq.mem x (objects 0UL g) /\
                        is_black x (mark_bounded g cap fuel) ==>
                        Seq.mem x (reachable_set graph roots')))
    (decreases fuel)

let rec mark_bounded_backward_inv h_init g cap fuel graph roots' =
  if fuel = 0 then ()
  else begin
    let st = rescan_heap g (objects 0UL g) Seq.empty cap in
    rescan_heap_bounded_stack_props g (objects 0UL g) cap;
    rescan_heap_cap_bound g (objects 0UL g) Seq.empty cap;
    if Seq.length st = 0 then ()
    else begin
      rescan_heap_stack_reachable g (objects 0UL g) Seq.empty cap graph roots';
      let inner_fuel = count_non_black g in
      mark_inner_loop_backward_inv h_init g st cap inner_fuel graph roots';
      mark_inner_loop_preserves_inv g st cap inner_fuel;
      mark_inner_loop_preserves_objects g st cap inner_fuel;
      mark_inner_loop_preserves_color_inv h_init g st cap inner_fuel;
      mark_inner_loop_gray_or_black_backward h_init g st cap inner_fuel graph roots';
      let (g', _) = mark_inner_loop g st cap inner_fuel in
      mark_bounded_backward_inv h_init g' cap (fuel - 1) graph roots'
    end
  end
#pop-options

/// Backward: black after mark_bounded implies reachable
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let mark_bounded_black_is_reachable
  (h_init: heap) (roots: seq obj_addr) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Seq.length (objects 0UL h_init) > 0 /\
      SweepInv.heap_objects_dense h_init /\
      root_props h_init roots /\
      no_black_objects h_init /\
      mark_color_inv h_init h_init /\
      fuel >= count_non_black h_init /\
      (forall (x: obj_addr). Seq.mem x (objects 0UL h_init) /\
        (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures
      (let h_mark = mark_bounded h_init cap fuel in
       let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices ==>
       (forall (x: obj_addr). mem_graph_vertex graph x /\
         is_black x h_mark ==> Seq.mem x (reachable_set graph roots'))))
  = let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    let prove_gb_init (x: obj_addr) : Lemma
      (requires Seq.mem x (objects 0UL h_init) /\ (is_gray x h_init \/ is_black x h_init))
      (ensures Seq.mem x (reachable_set graph roots'))
    = assert (Seq.mem x roots);
      HeapGraph.coerce_mem_lemma roots x;
      graph_vertices_mem h_init x;
      reach_refl graph x;
      reachable_set_correct graph roots'
    in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_gb_init);
    mark_bounded_backward_inv h_init h_init cap fuel graph roots';
    mark_bounded_preserves_objects h_init cap fuel;
    let h_mark = mark_bounded h_init cap fuel in
    let prove_vertex (x: obj_addr) : Lemma
      (mem_graph_vertex graph x <==> Seq.mem x (objects 0UL h_init))
    = graph_vertices_mem h_init x
    in FStar.Classical.forall_intro prove_vertex
#pop-options

/// =========================================================================
/// Part 10: Assembly — mark_bounded satisfies mark_post
/// =========================================================================

let mark_color_inv_init (h_init: heap)
  : Lemma (requires well_formed_heap h_init /\
                    Seq.length (objects 0UL h_init) > 0 /\
                    SweepInv.heap_objects_dense h_init /\
                    no_black_objects h_init /\
                    no_pointer_to_blue h_init)
          (ensures mark_color_inv h_init h_init)
  = assert (tri_color_invariant h_init)

/// Main theorem: mark_bounded satisfies mark_post
///
/// Requires one additional precondition vs mark_satisfies_mark_post:
///   gray_iff_root — initially, the only gray/black objects are the roots.
/// This is naturally satisfied when roots are made gray from an all-white heap.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let mark_bounded_satisfies_mark_post
  (h_init: heap) (roots: seq obj_addr) (fp: U64.t)
  (cap: nat{cap > 0}) (fuel: nat)
  : Lemma
    (requires
      well_formed_heap h_init /\
      Seq.length (objects 0UL h_init) > 0 /\
      SweepInv.heap_objects_dense h_init /\
      root_props h_init roots /\
      GC.Spec.Sweep.fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init /\
      fuel >= count_non_black h_init /\
      (forall (x: obj_addr). Seq.mem x (objects 0UL h_init) /\
        (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures Correctness.mark_post h_init (mark_bounded h_init cap fuel) roots fp)
  = let h_mark = mark_bounded h_init cap fuel in
    mark_color_inv_init h_init;
    mark_bounded_preserves_color_inv h_init h_init cap fuel;
    assert (mark_color_inv h_init h_mark);
    mark_bounded_completes h_init cap fuel;
    noGreyObjects_from_no_gray h_mark;
    mark_bounded_reachable_is_black h_init roots cap fuel;
    mark_bounded_black_is_reachable h_init roots cap fuel;
    let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    // Combine forward + backward into biconditional
    // The forward direction is already in mark_bounded_reachable_is_black
    // The backward direction is in mark_bounded_black_is_reachable
    // Both are under the implication: graph_wf /\ is_vertex_set /\ subset_vertices ==> ...
    // mark_post_intro needs the biconditional
    Correctness.mark_post_intro h_init h_mark roots fp
#pop-options

/// =========================================================================
/// Part 11: Standalone spec-level lemmas
/// =========================================================================

/// Backward reachability invariant: gray/black objects are reachable from roots
let gray_black_reachable (h_init: heap) (h: heap) (roots: seq obj_addr) : prop =
    let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
    (forall (x: obj_addr). Seq.mem x (objects 0UL h) /\ (is_gray x h \/ is_black x h) ==>
      Seq.mem x (reachable_set graph roots'))

/// Color monotonicity: initially gray objects (that are tracked) stay gray or blacker
let gray_stays (h_init h: heap) : prop =
    forall (x: obj_addr). Seq.mem x (objects 0UL h_init) /\ is_gray x h_init ==>
      is_gray x h \/ is_black x h

/// Stack elements are all reachable from roots in the initial graph
let stack_elems_reachable (h_init: heap) (st: seq obj_addr) (roots: seq obj_addr) : prop =
    let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices /\
    (forall (x: obj_addr). Seq.mem x st ==> Seq.mem x (reachable_set graph roots'))

/// ---------------------------------------------------------------------------
/// Initial establishment
/// ---------------------------------------------------------------------------

/// Initially, gray_black_reachable holds when gray/black objects are exactly roots
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let gray_black_reachable_init
  (h_init: heap) (roots: seq obj_addr)
  : Lemma
    (requires
      well_formed_heap h_init /\
      root_props h_init roots /\
      no_black_objects h_init /\
      (forall (x: obj_addr). Seq.mem x (objects 0UL h_init) /\
        (is_gray x h_init \/ is_black x h_init) ==> Seq.mem x roots) /\
      (let graph = create_graph h_init in
       let roots' = HeapGraph.coerce_to_vertex_list roots in
       graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures gray_black_reachable h_init h_init roots)
  = let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    let prove_gb (x: obj_addr) : Lemma
      (requires Seq.mem x (objects 0UL h_init) /\ (is_gray x h_init \/ is_black x h_init))
      (ensures Seq.mem x (reachable_set graph roots'))
    = assert (Seq.mem x roots);
      HeapGraph.coerce_mem_lemma roots x;
      graph_vertices_mem h_init x;
      reach_refl graph x;
      reachable_set_correct graph roots'
    in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_gb)
#pop-options

/// gray_stays trivially holds initially
let gray_stays_init (h: heap)
  : Lemma (ensures gray_stays h h)
  = ()

/// Bridge: bounded_stack_props + gray_black_reachable → stack_elems_reachable
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let stack_reachable_from_bsp_gbr
  (h_init: heap) (g: heap) (st: seq obj_addr) (roots: seq obj_addr)
  : Lemma
    (requires bounded_stack_props g st /\
             gray_black_reachable h_init g roots /\
             objects 0UL g == objects 0UL h_init)
    (ensures stack_elems_reachable h_init st roots)
  = let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    let prove_x (x: obj_addr) : Lemma
      (requires Seq.mem x st) (ensures Seq.mem x (reachable_set graph roots'))
    = // bounded_stack_props: x is valid (in objects g) and gray
      sev_mem_objects g st x;
      assert (Seq.mem x (objects 0UL g));
      assert (is_gray x g);
      // gray_black_reachable: gray in objects → reachable
      assert (Seq.mem x (objects 0UL g) /\ (is_gray x g \/ is_black x g))
    in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_x)
#pop-options

/// stack_elems_reachable trivially holds for empty stack
let stack_elems_reachable_empty (h_init: heap) (roots: seq obj_addr)
  : Lemma
    (requires (let graph = create_graph h_init in
               let roots' = HeapGraph.coerce_to_vertex_list roots in
               graph_wf graph /\ is_vertex_set roots' /\ subset_vertices roots' graph.vertices))
    (ensures stack_elems_reachable h_init Seq.empty roots)
  = ()

/// ---------------------------------------------------------------------------
/// Per-step preservation
/// ---------------------------------------------------------------------------

/// mark_step_bounded preserves gray_black_reachable AND stack reachability
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
let mark_step_bounded_preserves_gbr
  (h_init: heap) (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  (roots: seq obj_addr)
  : Lemma
    (requires well_formed_heap g /\ bounded_stack_props g st /\
             Seq.length (objects 0UL g) > 0 /\
             SweepInv.heap_objects_dense g /\
             mark_color_inv h_init g /\
             gray_black_reachable h_init g roots /\
             (forall x. Seq.mem x st ==> Seq.mem x (reachable_set (create_graph h_init) (HeapGraph.coerce_to_vertex_list roots))))
    (ensures (let (g', st') = mark_step_bounded g st cap in
             gray_black_reachable h_init g' roots /\
             (forall x. Seq.mem x st' ==> Seq.mem x (reachable_set (create_graph h_init) (HeapGraph.coerce_to_vertex_list roots)))))
  = let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    let (g', st') = mark_step_bounded g st cap in
    let hd = Seq.head st in
    mark_step_bounded_preserves_objects g st cap;
    // Part 1: Prove gray_black_reachable h_init g' roots
    let prove_gb_in_g' (x: obj_addr)
      : Lemma (requires Seq.mem x (objects 0UL g') /\ (is_gray x g' \/ is_black x g'))
              (ensures Seq.mem x (reachable_set graph roots'))
    = assert (Seq.mem x (objects 0UL g));
      if is_gray x g || is_black x g then ()
      else begin
        if is_blue x g then begin
          mark_step_bounded_preserves_blue g st cap x;
          is_blue_iff x g'; is_gray_iff x g'; is_black_iff x g';
          colors_exhaustive_and_exclusive x g'
        end else begin
          if is_black x g' then begin
            // x not gray/black/blue in g, but black in g'
            // mark_step_bounded_black_origin: x == hd
            // bounded_stack_head_is_gray: hd is gray in g
            // Contradiction: x is not gray in g but x == hd which IS gray
            mark_step_bounded_black_origin g st cap x;
            bounded_stack_head_is_gray g st;
            is_gray_iff hd g; is_white_iff hd g;
            colors_exhaustive_and_exclusive hd g
          end else begin
            // x is not black in g', so must be gray in g' (from precondition)
            // x not gray/black/blue in g, so white
            color_exhaustive x g;
            assert (is_white x g);
            assert (is_gray x g');
            mark_step_bounded_makes_gray_reachable g st cap x graph roots'
          end
        end
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_gb_in_g');
    // Part 2: Prove stack reachability for st'
    bounded_stack_head_is_gray g st;
    makeBlack_eq hd g;
    let g1 = makeBlack hd g in
    let ws = wosize_of_object hd g in
    if is_no_scan hd g then begin
      let prove_tail (y: obj_addr) : Lemma
        (requires Seq.mem y st')
        (ensures Seq.mem y (reachable_set graph roots'))
      = Seq.lemma_mem_inversion st
      in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_tail)
    end else begin
      color_preserves_create_graph hd g Header.Black;
      color_change_preserves_wf g hd Header.Black;
      color_change_preserves_objects g hd Header.Black;
      color_preserves_is_no_scan hd g Header.Black;
      color_preserves_wosize hd g Header.Black;
      wosize_of_object_bound hd g;
      objects_is_vertex_set g1;
      wf_implies_object_fits g hd;
      color_preserves_object_fits hd hd g Header.Black;
      let prove_tail (y: obj_addr) : Lemma
        (requires Seq.mem y (Seq.tail st))
        (ensures Seq.mem y (reachable_set graph roots'))
      = Seq.lemma_mem_inversion st
      in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_tail);
      push_children_bounded_stack_reachable g1 (Seq.tail st) hd 1UL ws cap graph roots'
    end
#pop-options

/// mark_step_bounded preserves gray_stays
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let mark_step_bounded_preserves_gray_stays
  (h_init: heap) (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma
    (requires well_formed_heap g /\ bounded_stack_props g st /\
             mark_color_inv h_init g /\
             gray_stays h_init g)
    (ensures gray_stays h_init (fst (mark_step_bounded g st cap)))
  = let g' = fst (mark_step_bounded g st cap) in
    let prove_x (x: obj_addr) : Lemma
      (requires Seq.mem x (objects 0UL h_init) /\ is_gray x h_init)
      (ensures is_gray x g' \/ is_black x g')
    = // gray_stays h_init g: x is gray or black in g
      assert (is_gray x g \/ is_black x g);
      // mark_color_inv: objects 0UL g == objects 0UL h_init
      assert (Seq.mem x (objects 0UL g));
      // mark_step_bounded preserves gray/black
      mark_step_bounded_gray_becomes_black g st cap x
    in FStar.Classical.forall_intro (FStar.Classical.move_requires prove_x)
#pop-options

/// ---------------------------------------------------------------------------
/// Assembly bridge
/// ---------------------------------------------------------------------------

/// Assemble mark_post from bounded mark invariants
#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"
let mark_post_from_bounded_mark
  (h_init: heap) (h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      well_formed_heap h_init /\
      mark_color_inv h_init h_mark /\
      SweepInv.no_gray_objects h_mark /\
      gray_black_reachable h_init h_mark roots /\
      gray_stays h_init h_mark /\
      root_props h_init roots /\
      GC.Spec.Sweep.fp_in_heap fp h_init /\
      no_black_objects h_init /\
      no_pointer_to_blue h_init)
    (ensures Correctness.mark_post h_init h_mark roots fp)
  = let graph = create_graph h_init in
    let roots' = HeapGraph.coerce_to_vertex_list roots in
    // From mark_color_inv
    assert (well_formed_heap h_mark);
    assert (objects 0UL h_mark == objects 0UL h_init);
    assert (SweepInv.heap_objects_dense h_mark);
    assert (Seq.length (objects 0UL h_mark) > 0);
    assert (no_pointer_to_blue h_mark);
    assert (tri_color_invariant h_mark);
    assert (create_graph h_mark == create_graph h_init);
    // noGreyObjects from no_gray_objects
    noGreyObjects_from_no_gray h_mark;
    // Show roots are black in h_mark
    let root_black (r: obj_addr) : Lemma
      (requires Seq.mem r roots) (ensures is_black r h_mark)
    = // root_props: r ∈ objects 0UL h_init, is_gray r h_init \/ is_black r h_init
      assert (Seq.mem r (objects 0UL h_init));
      assert (is_gray r h_init \/ is_black r h_init);
      // no_black_objects: ~(is_black r h_init)
      assert (is_gray r h_init);
      // gray_stays: is_gray r h_mark \/ is_black r h_mark
      assert (is_gray r h_mark \/ is_black r h_mark);
      // no_gray_objects: ~(is_gray r h_mark)
      SweepInv.no_gray_elim r h_mark
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires root_black);
    // Forward: reachable ==> black
    let prove_forward (x: obj_addr) : Lemma
      (requires mem_graph_vertex graph x /\ Seq.mem x (reachable_set graph roots'))
      (ensures is_black x h_mark)
    = assert (create_graph h_mark == graph);
      assert (noGreyObjects h_mark);
      assert (tri_color_invariant h_mark);
      assert (no_pointer_to_blue h_mark);
      reachable_set_correct graph roots';
      FStar.Classical.exists_elim (is_black x h_mark) ()
        (fun (r: vertex_id{mem_graph_vertex graph r /\
                            Seq.mem r roots' /\ reachable graph r x}) ->
          vertex_is_obj_addr h_init r;
          let r' : obj_addr = r in
          HeapGraph.coerce_mem_lemma roots r';
          root_black r';
          FStar.Classical.exists_elim (is_black x h_mark) ()
            (fun (p: reach graph r x) ->
              black_reach_is_black graph h_mark r' x p))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_forward);
    // Backward: black ==> reachable
    let prove_backward (x: obj_addr) : Lemma
      (requires mem_graph_vertex graph x /\ is_black x h_mark)
      (ensures Seq.mem x (reachable_set graph roots'))
    = graph_vertices_mem h_init x;
      assert (Seq.mem x (objects 0UL h_init));
      assert (Seq.mem x (objects 0UL h_mark));
      assert (is_gray x h_mark \/ is_black x h_mark)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires prove_backward);
    // Combine: mark_post_intro needs the biconditional under implication
    Correctness.mark_post_intro h_init h_mark roots fp
#pop-options
