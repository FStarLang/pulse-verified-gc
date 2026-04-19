/// ---------------------------------------------------------------------------
/// GC.Spec.MarkBounded — Mark phase with bounded (overflow-tolerant) stack
/// ---------------------------------------------------------------------------
///
/// Extends the mark specification to handle a fixed-capacity mark stack.
/// When the stack is full during push_children, the child is made gray
/// but not pushed — it will be rediscovered by a linear heap rescan.
///
/// The outer loop repeats: drain stack → rescan heap → until no grays remain.
/// Termination: count_non_black(g) strictly decreases each outer iteration.

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

/// Stack properties without the "all grays on stack" requirement.
/// With overflow, gray objects may exist in the heap but not on the stack.
let bounded_stack_props (g: heap) (st: seq obj_addr) : prop =
  stack_elements_valid g st /\
  stack_points_to_gray g st /\
  stack_no_dups st

/// bounded_stack_props is weaker than stack_props
let bounded_from_full (g: heap) (st: seq obj_addr)
  : Lemma (requires stack_props g st)
          (ensures bounded_stack_props g st)
  = ()

/// ---------------------------------------------------------------------------
/// Counting non-black objects (termination measure)
/// ---------------------------------------------------------------------------

/// Count objects that are NOT black in a sequence.
let rec count_non_black_in (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs)
  = if Seq.length objs = 0 then 0
    else
      let obj = Seq.head objs in
      let rest = count_non_black_in g (Seq.tail objs) in
      if is_black obj g then rest
      else rest + 1

/// Count non-black objects in the full objects list.
let count_non_black (g: heap) : GTot nat =
  count_non_black_in g (objects 0UL g)

/// ---------------------------------------------------------------------------
/// Push children with bounded stack capacity
/// ---------------------------------------------------------------------------

/// Like push_children, but skips push when stack is at capacity.
/// The child is still made gray — it stays gray in the heap for later rescan.
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

/// ---------------------------------------------------------------------------
/// Bounded mark step
/// ---------------------------------------------------------------------------

/// Process one gray object with bounded stack: pop, blacken, push children (bounded).
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

/// Walk the objects list, collecting gray objects onto the stack (up to cap).
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
/// Key lemmas: push_children_bounded preserves bounded_stack_props
/// ---------------------------------------------------------------------------

/// push_children_bounded respects stack capacity.
val push_children_bounded_cap :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (ensures Seq.length (snd (push_children_bounded g st obj i ws cap)) <= (if Seq.length st > cap then Seq.length st else cap))
        (decreases (U64.v ws - U64.v i))

let rec push_children_bounded_cap g st obj i ws cap =
  if U64.v i > U64.v ws then ()
  else begin
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
            (g', st)
        else (g, st)
      end else (g, st)
    in
    if U64.v i < U64.v ws then
      push_children_bounded_cap g' st' obj (U64.add i 1UL) ws cap
    else ()
  end

/// Helper: stack_points_to_gray preserved when changing a NON-stack object's color
let spg_preserved_other_color (g g': heap) (st: seq obj_addr) (child: obj_addr) (c: color)
  : Lemma (requires g' == set_object_color child g c /\
                   stack_points_to_gray g st /\
                   ~(Seq.mem child st))
          (ensures stack_points_to_gray g' st)
  = let aux (x: obj_addr) : Lemma (requires Seq.mem x st) (ensures is_gray x g')
    = assert (x <> child);
      is_gray_iff x g;
      hd_address_injective x child;
      set_object_color_read_word child (hd_address x) g c;
      color_of_object_spec x g; color_of_object_spec x g';
      is_gray_iff x g'
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// Combined push_children_bounded preserves bounded_stack_props
/// Proved by induction on field index, mirroring push_children_preserves_stack_props.
#push-options "--z3rlimit 800 --fuel 2 --ifuel 1"
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

let rec push_children_bounded_preserves_bsp g st obj i ws cap =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child_raw : obj_addr = v in
      let child = resolve_object child_raw g in
      if is_white child g then begin
        let g' = makeGray child g in
        makeGray_eq child g;
        is_white_iff child g; is_black_iff obj g;

        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g; hd_address_spec obj;
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        wf_object_size_bound g obj;
        field_read_implies_exists_pointing g obj wz (U64.sub i 1UL) child_raw;
        wf_field_target_in_objects g obj child_raw;
        wf_infix_wf g;
        resolve_object_in_objects child_raw g (objects 0UL g);

        color_change_preserves_wf g child Header.Gray;
        color_change_preserves_objects g child Header.Gray;

        if Seq.length st < cap then begin
          // Push case: same as unbounded
          let st' = Seq.cons child st in
          sev_transfer g g' st;
          pc_step_spg g child st g';
          white_not_in_gray_stack g st child;

          assert (Seq.head st' == child);
          Seq.lemma_tl child st;
          assert (Seq.tail st' == st);
          assert (Seq.mem child (objects 0UL g'));
          assert (stack_elements_valid g' st);
          assert (stack_elements_valid g' st');
          assert (~(Seq.mem child st));
          assert (stack_no_dups st);
          assert (stack_no_dups st');

          hd_address_injective child obj;
          color_change_preserves_other_color child obj g Header.Gray;
          is_black_iff obj g';
          obj_not_in_cons obj child st;
          set_object_color_preserves_getWosize_at_hd child g Header.Gray;
          wosize_of_object_spec obj g; wosize_of_object_spec obj g';
          color_change_preserves_objects_mem g child Header.Gray obj;

          if U64.v i < U64.v ws then
            push_children_bounded_preserves_bsp g' st' obj (U64.add i 1UL) ws cap
          else ()
        end else begin
          // Overflow case: child gray in heap, NOT pushed to stack
          // st unchanged, just need to show bounded_stack_props g' st
          sev_transfer g g' st;
          // stack_points_to_gray: child not on st (white_not_in_gray_stack)
          // so all stack elems are unchanged by makeGray child
          white_not_in_gray_stack g st child;
          spg_preserved_other_color g g' st child Header.Gray;
          // stack_no_dups unchanged

          hd_address_injective child obj;
          color_change_preserves_other_color child obj g Header.Gray;
          is_black_iff obj g';
          set_object_color_preserves_getWosize_at_hd child g Header.Gray;
          wosize_of_object_spec obj g; wosize_of_object_spec obj g';
          color_change_preserves_objects_mem g child Header.Gray obj;

          if U64.v i < U64.v ws then
            push_children_bounded_preserves_bsp g' st obj (U64.add i 1UL) ws cap
          else ()
        end
      end else begin
        if U64.v i < U64.v ws then
          push_children_bounded_preserves_bsp g st obj (U64.add i 1UL) ws cap
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_bounded_preserves_bsp g st obj (U64.add i 1UL) ws cap
      else ()
    end
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Key lemma: mark_step_bounded preserves bounded_stack_props
/// ---------------------------------------------------------------------------

/// Helper: head of bounded stack is gray and valid
let bounded_stack_head_is_gray (g: heap) (st: seq obj_addr)
  : Lemma (requires bounded_stack_props g st /\ Seq.length st > 0)
          (ensures (let obj = Seq.head st in
                    is_gray obj g /\
                    Seq.mem obj (objects 0UL g)))
  = ()

#push-options "--z3rlimit 800 --fuel 2 --ifuel 1"
let mark_step_bounded_preserves_bsp
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  Seq.length (objects 0UL g) > 0 /\ SweepInv.heap_objects_dense g)
        (ensures (let (g', st') = mark_step_bounded g st cap in
                  well_formed_heap g' /\ bounded_stack_props g' st'))
  = let obj = Seq.head st in
    let st_tail = Seq.tail st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    let g1 = makeBlack obj g in
    let ws = wosize_of_object obj g in

    color_change_preserves_objects g obj Header.Black;
    color_change_preserves_wf g obj Header.Black;

    // stack_no_dups st_tail (from stack_no_dups st)
    assert (stack_no_dups st_tail);

    // stack_elements_valid g1 st_tail
    sev_transfer g g1 st_tail;

    // stack_points_to_gray g1 st_tail
    // obj was head, not in tail (stack_no_dups). obj is now black.
    // All other elements: still gray (color unchanged since element ≠ obj)
    let sp_aux (x: obj_addr) : Lemma
      (requires Seq.mem x st_tail) (ensures is_gray x g1)
    = assert (Seq.mem x st);
      assert (is_gray x g);
      assert (x <> obj);
      hd_address_injective x obj;
      set_object_color_read_word obj (hd_address x) g Header.Black;
      color_of_object_spec x g;
      color_of_object_spec x g1;
      is_gray_iff x g;
      is_gray_iff x g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sp_aux);

    // obj not in st_tail
    assert (~(Seq.mem obj st_tail));

    if is_no_scan obj g then begin
      // Result: (g1, st_tail) — bounded_stack_props already proved above
      ()
    end else begin
      // push_children_bounded case
      makeBlack_is_black obj g;
      assert (is_black obj g1);
      wosize_of_object_bound obj g;
      wosize_of_object_spec obj g;
      wosize_of_object_spec obj g1;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      assert (wosize_of_object obj g1 == ws);
      wf_object_size_bound g obj;
      color_change_preserves_objects_mem g obj Header.Black obj;
      push_children_bounded_preserves_bsp g1 st_tail obj 1UL ws cap
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Key lemma: mark_step_bounded preserves objects
/// ---------------------------------------------------------------------------

/// push_children_bounded preserves the objects list (only does makeGray)
val push_children_bounded_preserves_objects :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (ensures objects 0UL (fst (push_children_bounded g st obj i ws cap)) == objects 0UL g)
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec push_children_bounded_preserves_objects g st obj i ws cap =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child_raw : obj_addr = v in
      let child = resolve_object child_raw g in
      if is_white child g then begin
        let g' = makeGray child g in
        makeGray_eq child g;
        color_change_preserves_objects g child Header.Gray;
        if Seq.length st < cap then begin
          let st' = Seq.cons child st in
          if U64.v i < U64.v ws then
            push_children_bounded_preserves_objects g' st' obj (U64.add i 1UL) ws cap
          else ()
        end else begin
          if U64.v i < U64.v ws then
            push_children_bounded_preserves_objects g' st obj (U64.add i 1UL) ws cap
          else ()
        end
      end else begin
        if U64.v i < U64.v ws then
          push_children_bounded_preserves_objects g st obj (U64.add i 1UL) ws cap
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_bounded_preserves_objects g st obj (U64.add i 1UL) ws cap
      else ()
    end
  end
#pop-options

let mark_step_bounded_preserves_objects
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st)
        (ensures objects 0UL (fst (mark_step_bounded g st cap)) == objects 0UL g)
  = let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    color_change_preserves_objects g obj Header.Black;
    let g1 = makeBlack obj g in
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then ()
    else push_children_bounded_preserves_objects g1 (Seq.tail st) obj 1UL ws cap

/// ---------------------------------------------------------------------------
/// Density preservation through mark_step_bounded
/// ---------------------------------------------------------------------------

val push_children_bounded_preserves_density :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (requires SweepInv.heap_objects_dense g)
        (ensures SweepInv.heap_objects_dense (fst (push_children_bounded g st obj i ws cap)))
        (decreases (U64.v ws - U64.v i))

let rec push_children_bounded_preserves_density g st obj i ws cap =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child_raw : obj_addr = v in
      let child = resolve_object child_raw g in
      if is_white child g then begin
        let g' = makeGray child g in
        makeGray_eq child g;
        SweepInv.color_change_preserves_density child g Header.Gray;
        let st' = if Seq.length st < cap then Seq.cons child st else st in
        if U64.v i < U64.v ws then
          push_children_bounded_preserves_density g' st' obj (U64.add i 1UL) ws cap
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_bounded_preserves_density g st obj (U64.add i 1UL) ws cap
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_bounded_preserves_density g st obj (U64.add i 1UL) ws cap
      else ()
    end
  end

let mark_step_bounded_preserves_density
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   SweepInv.heap_objects_dense g)
          (ensures SweepInv.heap_objects_dense (fst (mark_step_bounded g st cap)))
  = let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    SweepInv.color_change_preserves_density obj g Header.Black;
    let g1 = makeBlack obj g in
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then ()
    else push_children_bounded_preserves_density g1 (Seq.tail st) obj 1UL ws cap

/// ---------------------------------------------------------------------------
/// Key lemma: mark_step_bounded decreases count_non_black
/// ---------------------------------------------------------------------------

/// Helper: count_non_black_in decreases when a non-black object becomes black
/// and all other objects keep their color.

/// General monotonicity: if g' has at least as many black objects as g,
/// then count_non_black_in g' <= count_non_black_in g
let rec count_non_black_monotone (g g': heap) (objs: seq obj_addr)
  : Lemma (requires (forall (x: obj_addr). is_black x g ==> is_black x g'))
          (ensures count_non_black_in g' objs <= count_non_black_in g objs)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else count_non_black_monotone g g' (Seq.tail objs)

/// makeBlack preserves blackness of all objects
let makeBlack_preserves_other_black (obj x: obj_addr) (g: heap)
  : Lemma (requires is_black x g)
          (ensures is_black x (makeBlack obj g))
  = makeBlack_eq obj g;
    if x = obj then begin
      makeBlack_is_black obj g
    end else begin
      hd_address_injective x obj;
      set_object_color_read_word obj (hd_address x) g Header.Black;
      color_of_object_spec x g;
      color_of_object_spec x (makeBlack obj g);
      is_black_iff x g;
      is_black_iff x (makeBlack obj g)
    end

/// count_non_black_in strictly decreases when a non-black object exists and becomes black
let rec count_non_black_in_has_nonblack (g: heap) (obj: obj_addr) (objs: seq obj_addr)
  : Lemma (requires Seq.mem obj objs /\ ~(is_black obj g))
          (ensures count_non_black_in g objs > 0)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else if Seq.head objs = obj then ()
    else count_non_black_in_has_nonblack g obj (Seq.tail objs)

/// count_non_black_in strictly decreases when obj goes from non-black to black.
/// Proved by induction: split into prefix before first occurrence + tail.
let rec count_non_black_makeBlack (g: heap) (obj: obj_addr) (objs: seq obj_addr)
  : Lemma (requires is_gray obj g /\ Seq.mem obj objs)
          (ensures count_non_black_in (makeBlack obj g) objs < count_non_black_in g objs)
          (decreases Seq.length objs)
  = let g' = makeBlack obj g in
    is_gray_iff obj g; is_black_iff obj g;
    if Seq.length objs = 0 then ()
    else begin
      let hd = Seq.head objs in
      let tl = Seq.tail objs in
      makeBlack_eq obj g;
      if hd = obj then begin
        // hd is gray in g (non-black), becomes black in g'
        // count g objs  = 1 + count g tl  (hd non-black in g)
        // count g' objs = 0 + count g' tl (hd black in g')
        makeBlack_is_black obj g;
        is_black_iff obj g';
        // Need: count g' tl <= count g tl
        let aux (x: obj_addr) : Lemma (is_black x g ==> is_black x g')
          = FStar.Classical.move_requires (makeBlack_preserves_other_black obj x) g
        in FStar.Classical.forall_intro aux;
        count_non_black_monotone g g' tl
        // count g' objs = count g' tl <= count g tl < 1 + count g tl = count g objs ✓
      end else begin
        // hd ≠ obj: hd's color unchanged
        hd_address_injective hd obj;
        set_object_color_read_word obj (hd_address hd) g Header.Black;
        color_of_object_spec hd g; color_of_object_spec hd g';
        is_black_iff hd g; is_black_iff hd g';
        // count for hd is same in g and g'
        // IH: count g' tl < count g tl (obj must be in tl since mem obj objs and hd ≠ obj)
        count_non_black_makeBlack g obj tl
        // If hd was black: count g objs = 0 + count g tl, count g' objs = 0 + count g' tl
        //   count g' objs = count g' tl < count g tl = count g objs ✓
        // If hd non-black: count g objs = 1 + count g tl, count g' objs = 1 + count g' tl
        //   count g' objs = 1 + count g' tl < 1 + count g tl = count g objs ✓
      end
    end

/// push_children_bounded only makes white objects gray — doesn't change
/// count_non_black (white→gray are both non-black, so count unchanged).

/// makeGray of a WHITE child preserves count_non_black_in (white→gray both non-black)
let makeGray_white_preserves_black (child x: obj_addr) (g: heap)
  : Lemma (requires is_white child g /\ is_black x g)
          (ensures is_black x (makeGray child g))
  = makeGray_eq child g;
    if x = child then begin
      is_black_iff x g; is_white_iff child g;
      // x = child, is_black x g and is_white child g = is_white x g
      // But black and white are exclusive colors → contradiction
      colors_exhaustive_and_exclusive x g
    end else begin
      hd_address_injective x child;
      set_object_color_read_word child (hd_address x) g Header.Gray;
      color_of_object_spec x g;
      color_of_object_spec x (makeGray child g);
      is_black_iff x g;
      is_black_iff x (makeGray child g)
    end

/// Similarly, makeGray of white child preserves NON-blackness
let makeGray_white_preserves_nonblack (child x: obj_addr) (g: heap)
  : Lemma (requires is_white child g /\ ~(is_black x g))
          (ensures ~(is_black x (makeGray child g)))
  = makeGray_eq child g;
    if x = child then begin
      // child was white, becomes gray. gray ≠ black
      makeGray_is_gray child g;
      is_gray_iff child (makeGray child g);
      is_black_iff child (makeGray child g);
      colors_exhaustive_and_exclusive child (makeGray child g)
    end else begin
      hd_address_injective x child;
      set_object_color_read_word child (hd_address x) g Header.Gray;
      color_of_object_spec x g;
      color_of_object_spec x (makeGray child g);
      is_black_iff x g;
      is_black_iff x (makeGray child g)
    end

/// makeGray of white child preserves count_non_black_in exactly
let rec count_non_black_makeGray_white (g: heap) (child: obj_addr) (objs: seq obj_addr)
  : Lemma (requires is_white child g)
          (ensures count_non_black_in (makeGray child g) objs == count_non_black_in g objs)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let hd = Seq.head objs in
      let g' = makeGray child g in
      // is_black hd g <==> is_black hd g'
      (if is_black hd g then makeGray_white_preserves_black child hd g
       else makeGray_white_preserves_nonblack child hd g);
      count_non_black_makeGray_white g child (Seq.tail objs)
    end

val push_children_bounded_count_non_black :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (cap: nat) ->
  Lemma (ensures (let (g', _) = push_children_bounded g st obj i ws cap in
                  count_non_black_in g' (objects 0UL g) == count_non_black_in g (objects 0UL g)))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec push_children_bounded_count_non_black g st obj i ws cap =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child_raw : obj_addr = v in
      let child = resolve_object child_raw g in
      if is_white child g then begin
        let g' = makeGray child g in
        makeGray_eq child g;
        color_change_preserves_objects g child Header.Gray;
        count_non_black_makeGray_white g child (objects 0UL g);
        let st' = if Seq.length st < cap then Seq.cons child st else st in
        if U64.v i < U64.v ws then
          push_children_bounded_count_non_black g' st' obj (U64.add i 1UL) ws cap
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_bounded_count_non_black g st obj (U64.add i 1UL) ws cap
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_bounded_count_non_black g st obj (U64.add i 1UL) ws cap
      else ()
    end
  end
#pop-options

let mark_step_bounded_decreases_non_black
  (g: heap) (st: seq obj_addr{Seq.length st > 0}) (cap: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                  Seq.length (objects 0UL g) > 0 /\ SweepInv.heap_objects_dense g)
        (ensures count_non_black (fst (mark_step_bounded g st cap)) < count_non_black g)
  = let obj = Seq.head st in
    bounded_stack_head_is_gray g st;
    makeBlack_eq obj g;
    let g1 = makeBlack obj g in
    let ws = wosize_of_object obj g in
    // obj is gray → non-black → count > 0
    is_gray_iff obj g; is_black_iff obj g;
    // objects preserved by makeBlack
    color_change_preserves_objects g obj Header.Black;
    assert (objects 0UL g1 == objects 0UL g);
    // makeBlack: count drops
    count_non_black_makeBlack g obj (objects 0UL g);
    assert (count_non_black_in g1 (objects 0UL g) < count_non_black_in g (objects 0UL g));
    if is_no_scan obj g then begin
      // g_final = g1, objects unchanged
      assert (count_non_black g1 == count_non_black_in g1 (objects 0UL g1));
      assert (count_non_black g == count_non_black_in g (objects 0UL g));
      ()
    end else begin
      push_children_bounded_count_non_black g1 (Seq.tail st) obj 1UL ws cap;
      push_children_bounded_preserves_objects g1 (Seq.tail st) obj 1UL ws cap;
      let (g_final, _) = push_children_bounded g1 (Seq.tail st) obj 1UL ws cap in
      assert (count_non_black_in g_final (objects 0UL g1) == count_non_black_in g1 (objects 0UL g1));
      assert (objects 0UL g_final == objects 0UL g1);
      assert (objects 0UL g1 == objects 0UL g);
      ()
    end

/// ---------------------------------------------------------------------------
/// Rescan produces bounded_stack_props
/// ---------------------------------------------------------------------------

/// Helper: adding a gray object to a bounded stack preserves bounded_stack_props
let cons_gray_preserves_bsp (g: heap) (obj: obj_addr) (st: seq obj_addr)
  : Lemma (requires bounded_stack_props g st /\ is_gray obj g /\
                   Seq.mem obj (objects 0UL g) /\ ~(Seq.mem obj st))
          (ensures bounded_stack_props g (Seq.cons obj st))
  = let st' = Seq.cons obj st in
    // stack_elements_valid: obj ∈ objects, plus st was valid → cons valid
    assert (Seq.head st' == obj);
    Seq.lemma_tl obj st;
    assert (Seq.tail st' == st);
    // stack_points_to_gray: obj is gray, elements of st are gray
    let spg_aux (x: obj_addr) : Lemma (requires Seq.mem x st') (ensures is_gray x g)
    = Seq.mem_cons obj st
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires spg_aux);
    // stack_no_dups: obj ∉ st, plus st has no dups
    assert (~(Seq.mem obj st));
    assert (stack_no_dups st')

/// Helper: rescan_heap with general initial stack preserves bounded_stack_props
let rec rescan_heap_bsp_gen
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : Lemma (requires bounded_stack_props g st /\
                   (forall (x: obj_addr). Seq.mem x objs ==> Seq.mem x (objects 0UL g)))
          (ensures bounded_stack_props g (rescan_heap g objs st cap))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let st' =
        if is_gray obj g && not (Seq.mem obj st) && Seq.length st < cap then begin
          cons_gray_preserves_bsp g obj st;
          Seq.cons obj st
        end else
          st
      in
      rescan_heap_bsp_gen g (Seq.tail objs) st' cap
    end

/// Empty stack satisfies bounded_stack_props
let empty_bounded_stack_props (g: heap)
  : Lemma (bounded_stack_props g Seq.empty)
  = ()

let rescan_heap_bounded_stack_props
  (g: heap) (objs: seq obj_addr) (cap: nat)
  : Lemma (requires (forall (x: obj_addr). Seq.mem x objs ==> Seq.mem x (objects 0UL g)))
          (ensures bounded_stack_props g (rescan_heap g objs Seq.empty cap))
  = empty_bounded_stack_props g;
    rescan_heap_bsp_gen g objs Seq.empty cap

/// rescan never shrinks the stack
let rec rescan_heap_monotone
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : Lemma (ensures Seq.length (rescan_heap g objs st cap) >= Seq.length st)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let st' =
        if is_gray obj g && not (Seq.mem obj st) && Seq.length st < cap then
          Seq.cons obj st
        else st
      in
      rescan_heap_monotone g (Seq.tail objs) st' cap
    end

/// rescan never exceeds cap
let rec rescan_heap_cap_bound
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : Lemma (requires Seq.length st <= cap)
          (ensures Seq.length (rescan_heap g objs st cap) <= cap)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let st' =
        if is_gray obj g && not (Seq.mem obj st) && Seq.length st < cap then
          Seq.cons obj st
        else st
      in
      rescan_heap_cap_bound g (Seq.tail objs) st' cap
    end

/// If rescan returns empty with cap > 0, it started empty and no grays in objs
#push-options "--z3rlimit 50"
let rec rescan_complete_gen
  (g: heap) (objs: seq obj_addr) (st: seq obj_addr) (cap: nat)
  : Lemma (requires cap > 0)
          (ensures (Seq.length (rescan_heap g objs st cap) = 0 ==>
                    (Seq.length st = 0 /\
                     (forall (obj: obj_addr). Seq.mem obj objs ==> ~(is_gray obj g)))))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let obj = Seq.head objs in
      let st' =
        if is_gray obj g && not (Seq.mem obj st) && Seq.length st < cap then
          Seq.cons obj st
        else st
      in
      rescan_complete_gen g (Seq.tail objs) st' cap;
      rescan_heap_monotone g (Seq.tail objs) st' cap
    end
#pop-options

/// rescan finds all grays when cap > 0
let rescan_complete
  (g: heap) (cap: nat)
  : Lemma (requires cap > 0)
          (ensures (let st = rescan_heap g (objects 0UL g) Seq.empty cap in
                  Seq.length st = 0 ==>
                  (forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_gray obj g))))
  = rescan_complete_gen g (objects 0UL g) Seq.empty cap

/// ---------------------------------------------------------------------------
/// Inner loop invariants
/// ---------------------------------------------------------------------------

/// mark_inner_loop preserves bounded_stack_props
let rec mark_inner_loop_preserves_inv
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
  = if fuel = 0 || Seq.length st = 0 then ()
    else begin
      mark_step_bounded_preserves_bsp g st cap;
      mark_step_bounded_preserves_objects g st cap;
      mark_step_bounded_preserves_density g st cap;
      let obj = Seq.head st in
      let ws = wosize_of_object obj g in
      let g1 = makeBlack obj g in
      if is_no_scan obj g then begin
        let (g', st') = mark_step_bounded g st cap in
        assert (g' == g1);
        assert (st' == Seq.tail st);
        mark_inner_loop_preserves_inv g' st' cap (fuel - 1)
      end else begin
        push_children_bounded_cap g1 (Seq.tail st) obj 1UL ws cap;
        let (g', st') = mark_step_bounded g st cap in
        mark_inner_loop_preserves_inv g' st' cap (fuel - 1)
      end
    end

/// mark_inner_loop preserves objects list
let rec mark_inner_loop_preserves_objects
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g)
          (ensures objects 0UL (fst (mark_inner_loop g st cap fuel)) == objects 0UL g)
          (decreases fuel)
  = if fuel = 0 || Seq.length st = 0 then ()
    else begin
      mark_step_bounded_preserves_bsp g st cap;
      mark_step_bounded_preserves_objects g st cap;
      mark_step_bounded_preserves_density g st cap;
      let (g', st') = mark_step_bounded g st cap in
      mark_inner_loop_preserves_objects g' st' cap (fuel - 1)
    end

/// count_non_black is non-increasing through the inner loop
let rec mark_inner_loop_count_non_increasing
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g)
          (ensures count_non_black (fst (mark_inner_loop g st cap fuel)) <= count_non_black g)
          (decreases fuel)
  = if fuel = 0 || Seq.length st = 0 then ()
    else begin
      mark_step_bounded_preserves_bsp g st cap;
      mark_step_bounded_preserves_objects g st cap;
      mark_step_bounded_preserves_density g st cap;
      mark_step_bounded_decreases_non_black g st cap;
      let (g', st') = mark_step_bounded g st cap in
      mark_inner_loop_count_non_increasing g' st' cap (fuel - 1);
      // count_non_black g' < count_non_black g
      // count_non_black (fst (mark_inner_loop g' st' cap (fuel-1))) <= count_non_black g'
      // therefore count_non_black result < count_non_black g
      ()
    end

/// count_non_black strictly decreases if stack is non-empty
let mark_inner_loop_count_decreases
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   Seq.length st > 0 /\ fuel > 0)
          (ensures count_non_black (fst (mark_inner_loop g st cap fuel)) < count_non_black g)
  = mark_step_bounded_preserves_bsp g st cap;
    mark_step_bounded_preserves_objects g st cap;
    mark_step_bounded_preserves_density g st cap;
    mark_step_bounded_decreases_non_black g st cap;
    let (g', st') = mark_step_bounded g st cap in
    mark_inner_loop_count_non_increasing g' st' cap (fuel - 1)

/// mark_inner_loop drains stack (with sufficient fuel)
let rec mark_inner_loop_drains
  (g: heap) (st: seq obj_addr) (cap: nat) (fuel: nat)
  : Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   fuel >= count_non_black g)
          (ensures Seq.length (snd (mark_inner_loop g st cap fuel)) = 0)
          (decreases fuel)
  = if Seq.length st = 0 then ()
    else if fuel = 0 then begin
      // st non-empty but fuel = 0 → count_non_black g >= 1 but fuel >= count_non_black g
      // => fuel >= 1, contradiction
      bounded_stack_head_is_gray g st;
      let obj = Seq.head st in
      is_gray_iff obj g; is_black_iff obj g;
      count_non_black_in_has_nonblack g obj (objects 0UL g);
      ()
    end else begin
      mark_step_bounded_preserves_bsp g st cap;
      mark_step_bounded_preserves_objects g st cap;
      mark_step_bounded_preserves_density g st cap;
      mark_step_bounded_decreases_non_black g st cap;
      let (g', st') = mark_step_bounded g st cap in
      mark_inner_loop_drains g' st' cap (fuel - 1)
    end

/// ---------------------------------------------------------------------------
/// Top-level bounded mark: outer loop
/// ---------------------------------------------------------------------------

/// The full bounded mark: rescan → drain → rescan → ... until no grays.
/// Termination: count_non_black strictly decreases each non-trivial iteration.
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

/// mark_bounded preserves well-formedness and density
let rec mark_bounded_preserves_inv (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g)
          (ensures (let g' = mark_bounded g cap fuel in
                    well_formed_heap g' /\
                    Seq.length (objects 0UL g') > 0 /\
                    SweepInv.heap_objects_dense g'))
          (decreases fuel)
  = if fuel = 0 then ()
    else begin
      let st = rescan_heap g (objects 0UL g) Seq.empty cap in
      rescan_heap_bounded_stack_props g (objects 0UL g) cap;
      rescan_heap_cap_bound g (objects 0UL g) Seq.empty cap;
      if Seq.length st = 0 then ()
      else begin
        let inner_fuel = count_non_black g in
        mark_inner_loop_preserves_inv g st cap inner_fuel;
        mark_inner_loop_preserves_objects g st cap inner_fuel;
        let (g', _) = mark_inner_loop g st cap inner_fuel in
        mark_bounded_preserves_inv g' cap (fuel - 1)
      end
    end

/// mark_bounded preserves objects list
let rec mark_bounded_preserves_objects (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g)
          (ensures objects 0UL (mark_bounded g cap fuel) == objects 0UL g)
          (decreases fuel)
  = if fuel = 0 then ()
    else begin
      let st = rescan_heap g (objects 0UL g) Seq.empty cap in
      rescan_heap_bounded_stack_props g (objects 0UL g) cap;
      rescan_heap_cap_bound g (objects 0UL g) Seq.empty cap;
      if Seq.length st = 0 then ()
      else begin
        let inner_fuel = count_non_black g in
        mark_inner_loop_preserves_inv g st cap inner_fuel;
        mark_inner_loop_preserves_objects g st cap inner_fuel;
        let (g', _) = mark_inner_loop g st cap inner_fuel in
        mark_bounded_preserves_objects g' cap (fuel - 1)
      end
    end

/// count_non_black strictly decreases per non-trivial iteration
let rec mark_bounded_count_decreases (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\ fuel > 0 /\
                   Seq.length (rescan_heap g (objects 0UL g) Seq.empty cap) > 0)
          (ensures count_non_black (mark_bounded g cap fuel) < count_non_black g)
          (decreases fuel)
  = let st = rescan_heap g (objects 0UL g) Seq.empty cap in
    rescan_heap_bounded_stack_props g (objects 0UL g) cap;
    rescan_heap_cap_bound g (objects 0UL g) Seq.empty cap;
    // st non-empty: head is gray (from bsp), gray is non-black → count_non_black > 0
    bounded_stack_head_is_gray g st;
    let obj = Seq.head st in
    is_gray_iff obj g; is_black_iff obj g;
    count_non_black_in_has_nonblack g obj (objects 0UL g);
    let inner_fuel = count_non_black g in
    mark_inner_loop_preserves_inv g st cap inner_fuel;
    mark_inner_loop_preserves_objects g st cap inner_fuel;
    mark_inner_loop_count_decreases g st cap inner_fuel;
    let (g', _) = mark_inner_loop g st cap inner_fuel in
    if fuel = 1 then ()
    else begin
      let st' = rescan_heap g' (objects 0UL g') Seq.empty cap in
      if Seq.length st' = 0 then ()
      else begin
        mark_bounded_count_decreases g' cap (fuel - 1)
      end
    end

/// When count_non_black_in = 0, no element in the list is gray
let rec count_non_black_zero_not_gray (g: heap) (obj: obj_addr) (objs: seq obj_addr)
  : Lemma (requires count_non_black_in g objs = 0 /\ Seq.mem obj objs)
          (ensures ~(is_gray obj g))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else if Seq.head objs = obj then begin
      if is_black obj g then begin
        is_black_iff obj g; is_gray_iff obj g
      end else ()
    end else begin
      Seq.mem_cons (Seq.head objs) (Seq.tail objs);
      count_non_black_zero_not_gray g obj (Seq.tail objs)
    end

/// Helper: when count_non_black g = 0, no gray objects exist
let count_non_black_zero_no_gray (g: heap)
  : Lemma (requires count_non_black g = 0)
          (ensures SweepInv.no_gray_objects g)
  = let aux (obj: obj_addr) : Lemma (requires Seq.mem obj (objects 0UL g))
                                    (ensures ~(is_gray obj g))
    = count_non_black_zero_not_gray g obj (objects 0UL g)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    SweepInv.no_gray_intro g

/// With sufficient fuel, mark_bounded produces no gray objects
let rec mark_bounded_completes (g: heap) (cap: nat{cap > 0}) (fuel: nat)
  : Lemma (requires well_formed_heap g /\
                   Seq.length (objects 0UL g) > 0 /\
                   SweepInv.heap_objects_dense g /\
                   fuel >= count_non_black g)
          (ensures SweepInv.no_gray_objects (mark_bounded g cap fuel))
          (decreases fuel)
  = if fuel = 0 then begin
      count_non_black_zero_no_gray g
    end else begin
      let st = rescan_heap g (objects 0UL g) Seq.empty cap in
      rescan_heap_bounded_stack_props g (objects 0UL g) cap;
      rescan_heap_cap_bound g (objects 0UL g) Seq.empty cap;
      rescan_complete g cap;
      if Seq.length st = 0 then
        SweepInv.no_gray_intro g
      else begin
        // st non-empty → count_non_black g > 0
        bounded_stack_head_is_gray g st;
        is_gray_iff (Seq.head st) g; is_black_iff (Seq.head st) g;
        count_non_black_in_has_nonblack g (Seq.head st) (objects 0UL g);
        let inner_fuel = count_non_black g in
        mark_inner_loop_preserves_inv g st cap inner_fuel;
        mark_inner_loop_preserves_objects g st cap inner_fuel;
        mark_inner_loop_count_decreases g st cap inner_fuel;
        let (g', _) = mark_inner_loop g st cap inner_fuel in
        // count_non_black g' < count_non_black g <= fuel
        // so fuel - 1 >= count_non_black g'
        mark_bounded_completes g' cap (fuel - 1)
      end
    end
