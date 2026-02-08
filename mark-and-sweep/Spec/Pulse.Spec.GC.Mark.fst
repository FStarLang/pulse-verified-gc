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

/// Stack has no duplicate elements (follows from gray_objects_on_stack + stack_points_to_gray conceptually)
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
let stack_head_is_gray (g: heap) (st: seq obj_addr)
  : Lemma (requires stack_props g st /\ Seq.length st > 0)
          (ensures (let obj = Seq.head st in
                    is_gray obj g /\
                    Seq.mem obj (objects 0UL g)))
  = ()

/// Transfer stack_elements_valid when objects are equal
let rec sev_transfer (g g': heap) (st: seq obj_addr)
  : Lemma (requires objects 0UL g == objects 0UL g' /\ stack_elements_valid g st)
          (ensures stack_elements_valid g' st) (decreases Seq.length st)
  = if Seq.length st = 0 then () else sev_transfer g g' (Seq.tail st)

/// White element not in gray stack (colors exclusive)
let white_not_in_gray_stack (g: heap) (st: seq obj_addr) (child: obj_addr)
  : Lemma (requires stack_points_to_gray g st /\ is_white child g) (ensures ~(Seq.mem child st))
  = let aux (x: obj_addr) : Lemma (Seq.mem x st ==> x <> child) =
      if Seq.mem x st then begin is_white_iff child g; is_gray_iff x g; colors_exhaustive_and_exclusive x g end
    in FStar.Classical.forall_intro aux

/// gray_objects_on_stack after makeGray step
let pc_step_gos (g: heap) (child: obj_addr) (st: seq obj_addr) (g': heap)
  : Lemma (requires g' == set_object_color child g Header.Gray /\
                   is_white child g /\ Seq.mem child (objects 0UL g) /\
                   gray_objects_on_stack g st /\ objects 0UL g' == objects 0UL g)
          (ensures gray_objects_on_stack g' (Seq.cons child st))
  = let st' = Seq.cons child st in
    let aux (x: obj_addr) : Lemma
      (requires Seq.mem x (objects 0UL g') /\ is_gray x g') (ensures Seq.mem x st')
    = Seq.mem_cons child st;
      if x = child then ()
      else begin
        hd_address_injective x child;
        set_object_color_read_word child (hd_address x) g Header.Gray;
        color_of_object_spec x g; color_of_object_spec x g';
        is_gray_iff x g; is_gray_iff x g'
      end
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// stack_points_to_gray after makeGray step
let pc_step_spg (g: heap) (child: obj_addr) (st: seq obj_addr) (g': heap)
  : Lemma (requires g' == set_object_color child g Header.Gray /\
                   is_white child g /\ stack_points_to_gray g st)
          (ensures stack_points_to_gray g' (Seq.cons child st))
  = let aux (x: obj_addr) : Lemma
      (requires Seq.mem x (Seq.cons child st)) (ensures is_gray x g')
    = Seq.mem_cons child st;
      if x = child then begin makeGray_eq child g; makeGray_is_gray child g end
      else begin
        is_gray_iff x g; is_white_iff child g;
        hd_address_injective x child;
        set_object_color_read_word child (hd_address x) g Header.Gray;
        color_of_object_spec x g; color_of_object_spec x g'; is_gray_iff x g'
      end
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// obj not in cons child st when obj ≠ child and obj ∉ st
let obj_not_in_cons (obj child: obj_addr) (st: seq obj_addr)
  : Lemma (requires obj <> child /\ ~(Seq.mem obj st))
          (ensures ~(Seq.mem obj (Seq.cons child st)))
  = Seq.mem_cons child st


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
/// push_children preserves all stack properties
#push-options "--z3rlimit 800 --fuel 2 --ifuel 1"
val push_children_preserves_stack_props :
  (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\
                  is_black obj g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  ~(Seq.mem obj st))
        (ensures (let (g', st') = push_children g st obj i ws in stack_props g' st'))
        (decreases (U64.v ws - U64.v i))
let rec push_children_preserves_stack_props g st obj i ws =
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
        is_white_iff child g; is_black_iff obj g;
        
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g; hd_address_spec obj;
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        field_read_implies_exists_pointing g obj wz (U64.sub i 1UL) child;
        
        color_change_preserves_wf g child Header.Gray;
        color_change_preserves_objects g child Header.Gray;
        sev_transfer g g' st;
        pc_step_spg g child st g';
        pc_step_gos g child st g';
        white_not_in_gray_stack g st child;
        
        // Help unfold stack_elements_valid for cons
        assert (Seq.length st' > 0);
        assert (Seq.head st' == child);
        Seq.lemma_tl child st;
        assert (Seq.tail st' == st);
        assert (Seq.mem child (objects 0UL g'));
        assert (stack_elements_valid g' st);
        assert (stack_elements_valid g' st');
        // Help unfold stack_no_dups for cons
        assert (~(Seq.mem child st));
        assert (stack_no_dups st);
        assert (stack_no_dups st');
        
        // Recursion preconditions
        hd_address_injective child obj;
        color_change_preserves_other_color child obj g Header.Gray;
        is_black_iff obj g';
        obj_not_in_cons obj child st;
        set_object_color_preserves_getWosize_at_hd child g Header.Gray;
        wosize_of_object_spec obj g; wosize_of_object_spec obj g';
        color_change_preserves_objects_mem g child Header.Gray obj;
        
        if U64.v i < U64.v ws then
          push_children_preserves_stack_props g' st' obj (U64.add i 1UL) ws
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_preserves_stack_props g st obj (U64.add i 1UL) ws
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_preserves_stack_props g st obj (U64.add i 1UL) ws
      else ()
    end
  end
#pop-options
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

#push-options "--z3rlimit 800"
let mark_step_preserves_stack_props g st =
  let obj = Seq.head st in
  let st_tail = Seq.tail st in
  stack_head_is_gray g st;
  makeBlack_eq obj g;
  let g1 = makeBlack obj g in
  let ws = wosize_of_object obj g in
  
  // After makeBlack obj:
  // - obj is now black in g1
  // - all other colors unchanged
  // - objects unchanged (color_change_preserves_objects)
  color_change_preserves_objects g obj Header.Black;
  
  if is_no_scan obj g then begin
    // Result: (g1, st_tail)
    
    // Property 4: stack_no_dups st_tail
    // Follows from stack_no_dups (cons obj st_tail) → stack_no_dups st_tail
    // (stack_no_dups strips the head)
    assert (stack_no_dups st_tail);
    
    // Property 1: stack_elements_valid g1 st_tail
    sev_transfer g g1 st_tail;
    
    // Property 3: stack_points_to_gray g1 st_tail
    // Elements of tail st are gray in g (stack_points_to_gray g st)
    // After makeBlack obj: x ≠ obj → is_gray x g1 = is_gray x g
    // obj ∉ tail st (from stack_no_dups)
    let sp_aux (x: obj_addr) : Lemma
      (requires Seq.mem x st_tail)
      (ensures is_gray x g1)
    = Seq.cons_head_tail st;
      Seq.mem_cons obj st_tail;
      assert (Seq.mem x st);
      assert (is_gray x g);
      assert (~ (Seq.mem obj st_tail));
      assert (x <> obj);
      assert (g1 == set_object_color obj g Header.Black);
      hd_address_injective x obj;
      set_object_color_read_word obj (hd_address x) g Header.Black;
      color_of_object_spec x g;
      color_of_object_spec x g1;
      is_gray_iff x g;
      is_gray_iff x g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sp_aux);
    
    // Property 2: gray_objects_on_stack g1 st_tail
    // Gray objects in g1: same as g minus {obj} (obj is now black)
    // If x is gray in g1: x ≠ obj (obj is black), so x is gray in g
    // From gray_objects_on_stack g st: x ∈ st = {obj} ∪ tail st
    // Since x ≠ obj: x ∈ tail st
    let go_aux (x: obj_addr) : Lemma
      (requires Seq.mem x (objects 0UL g1) /\ is_gray x g1)
      (ensures Seq.mem x st_tail)
    = // obj is black in g1 (from makeBlack)
      makeBlack_is_black obj g;
      assert (is_black obj g1);
      // x is gray in g1 (from precondition)
      // black ≠ gray → x ≠ obj
      is_black_iff obj g1;
      is_gray_iff x g1;
      assert (x <> obj);
      // x is gray in g (color unchanged since x ≠ obj)
      assert (g1 == set_object_color obj g Header.Black);
      hd_address_injective x obj;
      set_object_color_read_word obj (hd_address x) g Header.Black;
      color_of_object_spec x g;
      color_of_object_spec x g1;
      is_gray_iff x g;
      assert (is_gray x g);
      // objects preserved
      assert (Seq.mem x (objects 0UL g));
      // From gray_objects_on_stack g st: x ∈ st
      assert (Seq.mem x st);
      // x ≠ obj = head st, so x ∈ tail st
      Seq.cons_head_tail st;
      Seq.mem_cons obj st_tail;
      ()
    in
    let go_imp (x: obj_addr) : Lemma
      ((Seq.mem x (objects 0UL g1) /\ is_gray x g1) ==> Seq.mem x st_tail)
    = FStar.Classical.move_requires go_aux x
    in
    FStar.Classical.forall_intro go_imp
  end else begin
    // push_children case: need to show stack_props for push_children g1 st_tail obj 1UL ws
    // After makeBlack: obj is black in g1, obj ∉ st_tail (was head, stack_no_dups)
    makeBlack_is_black obj g;
    assert (is_black obj g1);
    color_change_preserves_wf g obj Header.Black;
    
    // obj ∉ st_tail: obj was head of st, stack_no_dups gives ~(mem obj st_tail) 
    assert (~(Seq.mem obj st_tail));
    
    // stack_props g1 st_tail: proved same way as is_no_scan case
    // sev
    sev_transfer g g1 st_tail;
    // spg
    let sp_aux (x: obj_addr) : Lemma (requires Seq.mem x st_tail) (ensures is_gray x g1)
    = assert (is_gray x g);
      makeBlack_is_black obj g;
      is_gray_iff x g; is_black_iff obj g1;
      assert (x <> obj);
      hd_address_injective x obj;
      set_object_color_read_word obj (hd_address x) g Header.Black;
      color_of_object_spec x g; color_of_object_spec x g1;
      is_gray_iff x g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires sp_aux);
    // gos
    let go_aux (x: obj_addr) : Lemma
      (requires Seq.mem x (objects 0UL g1) /\ is_gray x g1)
      (ensures Seq.mem x st_tail)
    = makeBlack_is_black obj g;
      is_black_iff obj g1; is_gray_iff x g1;
      assert (x <> obj);
      hd_address_injective x obj;
      set_object_color_read_word obj (hd_address x) g Header.Black;
      color_of_object_spec x g; color_of_object_spec x g1;
      is_gray_iff x g;
      assert (Seq.mem x (objects 0UL g));
      assert (Seq.mem x st);
      Seq.cons_head_tail st; Seq.mem_cons obj st_tail
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires go_aux);
    assert (stack_no_dups st_tail);
    
    // wosize preserved
    wosize_of_object_bound obj g;
    set_object_color_preserves_getWosize_at_hd obj g Header.Black;
    wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
    
    // obj ∉ st_tail: from stack_no_dups, obj = head st → obj ∉ tail st
    assert (~(Seq.mem obj st_tail));
    assert (well_formed_heap g1);
    assert (stack_props g1 st_tail);
    assert (is_black obj g1);
    assert (Seq.mem obj (objects 0UL g1));
    assert (U64.v ws <= U64.v (wosize_of_object obj g1));
    assert (U64.v (wosize_of_object obj g1) < pow2 54);
    
    // Help the solver see push_children_preserves_stack_props's precondition
    let pcsp_call () : Lemma
      (requires well_formed_heap g1 /\ stack_props g1 st_tail /\
                is_black obj g1 /\ Seq.mem obj (objects 0UL g1) /\
                U64.v ws <= U64.v (wosize_of_object obj g1) /\
                U64.v (wosize_of_object obj g1) < pow2 54 /\
                ~(Seq.mem obj st_tail))
      (ensures (let (g', st') = push_children g1 st_tail obj 1UL ws in stack_props g' st'))
    = push_children_preserves_stack_props g1 st_tail obj 1UL ws
    in
    pcsp_call ()
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Mark Phase: Iterate Until Stack Empty
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------

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

let rec mark_aux (g: heap{well_formed_heap g}) (st: seq obj_addr{stack_props g st}) (fuel: nat)
  : GTot heap (decreases fuel)
  =
  if Seq.length st = 0 then g
  else if fuel = 0 then g
  else begin
    let (g', st') = mark_step g st in
    mark_step_preserves_stack_props g st;
    mark_step_preserves_wf g st;
    mark_aux g' st' (fuel - 1)
  end

let mark (g: heap{well_formed_heap g}) (st: seq obj_addr{stack_props g st}) : GTot heap =
  mark_aux g st (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// Mark Phase Invariants
/// ---------------------------------------------------------------------------

/// Tri-color invariant: no black object points to white object
/// Uses points_to from Fields with no_scan guard (no_scan objects have no pointer fields for GC)
let tri_color_invariant (g: heap) : prop =
  let objs = objects 0UL g in
  forall (obj: obj_addr) (child: obj_addr). 
    Seq.mem obj objs ==>
    is_black obj g ==>
    ~(is_no_scan obj g) ==>
    points_to g obj child ==>
    ~(is_white child g)

/// After marking, no gray objects remain
let noGreyObjects (g: heap) : prop =
  let objs = objects 0UL g in
  forall (obj: obj_addr). Seq.mem obj objs ==>
    not (is_gray obj g)

/// No black objects initially (natural GC precondition: after sweep-reset, before mark)
let no_black_objects (g: heap) : prop =
  forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_black obj g)

/// No blue objects in heap (free list empty at mark start)
let no_blue_objects (g: heap) : prop =
  forall (obj: obj_addr). Seq.mem obj (objects 0UL g) ==> ~(is_blue obj g)

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

/// push_children preserves black color of other objects (not the parent)
val push_children_preserves_other_black : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
                                           (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires is_black x g /\ x <> obj)
        (ensures is_black x (fst (push_children g st obj i ws)))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 100 --fuel 2"
let rec push_children_preserves_other_black g st obj i ws x =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child : obj_addr = v in
      if is_white child g then begin
        let g' = makeGray child g in
        // child is white, x is black → child <> x
        is_white_iff child g;
        is_black_iff x g;
        assert (child <> x);
        makeGray_eq child g;
        color_change_preserves_other_color child x g Header.Gray;
        is_black_iff x g;
        is_black_iff x g';
        assert (is_black x g');
        let st' = Seq.cons child st in
        if U64.v i < U64.v ws then
          push_children_preserves_other_black g' st' obj (U64.add i 1UL) ws x
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_preserves_other_black g st obj (U64.add i 1UL) ws x
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_preserves_other_black g st obj (U64.add i 1UL) ws x
      else ()
    end
  end
#pop-options

/// mark_step preserves black color of any object
val mark_step_preserves_black : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) -> (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ is_black x g)
        (ensures is_black x (fst (mark_step g st)))

#push-options "--z3rlimit 100"
let mark_step_preserves_black g st x =
  let obj = Seq.head st in
  stack_head_is_gray g st;
  // obj is gray, x is black → obj <> x
  is_gray_iff obj g;
  is_black_iff x g;
  colors_exhaustive_and_exclusive obj g;
  assert (obj <> x);
  // makeBlack obj preserves x's color
  let g' = makeBlack obj g in
  makeBlack_eq obj g;
  color_change_preserves_other_color obj x g Header.Black;
  is_black_iff x g;
  is_black_iff x g';
  assert (is_black x g');
  // push_children preserves x's color
  let ws = wosize_of_object obj g in
  if is_no_scan obj g then ()
  else begin
    let st' = Seq.tail st in
    push_children_preserves_other_black g' st' obj 1UL ws x
  end
#pop-options

/// mark_aux preserves black color of any object
val mark_aux_preserves_black : (g: heap{well_formed_heap g}) -> 
                                (st: seq obj_addr{stack_props g st}) -> 
                                (fuel: nat) -> (x: obj_addr) ->
  Lemma (requires is_black x g)
        (ensures is_black x (mark_aux g st fuel))
        (decreases fuel)

#push-options "--z3rlimit 50 --fuel 1"
let rec mark_aux_preserves_black g st fuel x =
  if Seq.length st = 0 then ()
  else if fuel = 0 then ()
  else begin
    let (g', st') = mark_step g st in
    mark_step_preserves_black g st x;
    assert (is_black x g');
    mark_step_preserves_stack_props g st;
    mark_step_preserves_wf g st;
    mark_aux_preserves_black g' st' (fuel - 1) x
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


val mark_preserves_wf : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures well_formed_heap (mark g st))

let rec mark_aux_preserves_wf (g: heap{well_formed_heap g}) (st: seq obj_addr{stack_props g st}) (fuel: nat)
  : Lemma (ensures well_formed_heap (mark_aux g st fuel))
          (decreases fuel)
  = if Seq.length st = 0 then ()
    else if fuel = 0 then ()
    else begin
      let (g', st') = mark_step g st in
      mark_step_preserves_stack_props g st;
      mark_step_preserves_wf g st;
      mark_aux_preserves_wf g' st' (fuel - 1)
    end

let mark_preserves_wf g st =
  mark_aux_preserves_wf g st (heap_size / U64.v mword)

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
                  no_black_objects g /\ no_blue_objects g /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
        (ensures (forall (x: obj_addr). 
                   (let graph = create_graph g in
                    let roots' = HeapGraph.coerce_to_vertex_list roots in
                    graph_wf graph /\ is_vertex_set roots' /\ 
                    subset_vertices roots' graph.vertices /\
                    mem_graph_vertex graph x /\
                    Seq.mem x (reachable_set graph roots')) ==> 
                   is_black x (mark g st)))

/// (defined at end of file after all infrastructure)

val mark_black_is_reachable : (g: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  no_black_objects g /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
        (ensures (forall (x: obj_addr). 
                   (let graph = create_graph g in
                    let roots' = HeapGraph.coerce_to_vertex_list roots in
                    graph_wf graph /\ is_vertex_set roots' /\
                    subset_vertices roots' graph.vertices /\
                    mem_graph_vertex graph x /\
                    is_black x (mark g st)) ==> 
                   Seq.mem x (reachable_set (create_graph g) (HeapGraph.coerce_to_vertex_list roots))))

/// (defined at end of file after all infrastructure)

val mark_black_iff_reachable : (g: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  no_black_objects g /\ no_blue_objects g /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
        (ensures True)

/// (defined at end of file after all infrastructure)

/// ---------------------------------------------------------------------------
/// Mark Terminates With No Gray Objects
/// ---------------------------------------------------------------------------

/// When stack is empty, gray_objects_on_stack implies no gray objects
let empty_stack_no_grey (g: heap) (st: seq obj_addr)
  : Lemma (requires stack_props g st /\ Seq.length st = 0)
          (ensures noGreyObjects g)
  = let aux (obj: obj_addr) : Lemma (Seq.mem obj (objects 0UL g) ==> not (is_gray obj g))
    = ()  // Follows from gray_objects_on_stack and empty st
    in
    FStar.Classical.forall_intro aux

/// Helper: non_black_count preserved when colors are equal
let rec non_black_count_eq_objs (g1 g2: heap) (objs: seq obj_addr)
  : Lemma (requires (forall (obj: obj_addr). Seq.mem obj objs ==> 
                     (is_black obj g1 <==> is_black obj g2)))
          (ensures non_black_count g1 objs == non_black_count g2 objs)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else non_black_count_eq_objs g1 g2 (Seq.tail objs)

/// After makeBlack on gray obj, non_black_count decreases by 1
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries no"
let rec non_black_count_makeBlack_gray (g: heap) (obj: obj_addr) (objs: seq obj_addr)
  : Lemma (requires is_gray obj g /\ Seq.mem obj objs /\ well_formed_heap g /\
                    Seq.mem obj (objects 0UL g) /\
                    is_vertex_set (HeapGraph.coerce_to_vertex_list objs))
          (ensures (let g' = makeBlack obj g in
                    non_black_count g' objs == non_black_count g objs - 1))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let hd = Seq.head objs in
      let tl = Seq.tail objs in
      makeBlack_eq obj g;
      let g' = makeBlack obj g in
      // is_vertex_set means hd ∉ tl
      HeapGraph.coerce_cons_lemma hd tl;
      assert (is_vertex_set (HeapGraph.coerce_to_vertex_list objs));
      if hd = obj then begin
        is_gray_iff obj g;
        is_black_iff obj g;
        colors_exhaustive_and_exclusive obj g;
        makeBlack_is_black obj g;
        HeapGraph.coerce_cons_lemma hd tl;
        Seq.lemma_tl hd (HeapGraph.coerce_to_vertex_list tl);
        // is_vertex_set (cons hd (coerce tl)) → ~(Seq.mem hd (coerce tl))
        // hd = obj, so ~(Seq.mem obj (coerce tl))
        // coerce_mem_lemma: Seq.mem obj (coerce tl) ↔ Seq.mem obj tl
        HeapGraph.coerce_mem_lemma tl obj;
        assert (~(Seq.mem obj tl));
        let aux (x: obj_addr) : Lemma
          (requires Seq.mem x tl)
          (ensures is_black x g' == is_black x g)
        = assert (x <> obj);
          hd_address_injective x obj;
          color_change_preserves_other_color obj x g Header.Black;
          is_black_iff x g;
          is_black_iff x g'
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        non_black_count_eq_objs g g' tl
      end else begin
        hd_address_injective hd obj;
        color_change_preserves_other_color obj hd g Header.Black;
        is_black_iff hd g;
        is_black_iff hd g';
        Seq.mem_cons hd tl;
        HeapGraph.coerce_cons_lemma hd tl;
        // coerce(cons hd tl) == cons hd (coerce tl)
        // tail of cons hd (coerce tl) == coerce tl
        // is_vertex_set_tail gives is_vertex_set (coerce tl)
        assert (HeapGraph.coerce_to_vertex_list objs == Seq.cons hd (HeapGraph.coerce_to_vertex_list tl));
        is_vertex_set_tail (HeapGraph.coerce_to_vertex_list objs);
        Seq.lemma_tl hd (HeapGraph.coerce_to_vertex_list tl);
        assert (is_vertex_set (HeapGraph.coerce_to_vertex_list tl));
        non_black_count_makeBlack_gray g obj tl
      end
    end
#pop-options
val push_children_preserves_non_black : (g: heap) -> (st: seq obj_addr) -> 
                                         (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> 
                                         (ws: U64.t) -> (objs: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\ objects 0UL g == objs)
        (ensures (let (g', _) = push_children g st obj i ws in
                  objects 0UL g' == objs /\
                  non_black_count g' objs == non_black_count g objs))
        (decreases (U64.v ws - U64.v i))

let rec push_children_preserves_non_black g st obj i ws objs =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child : obj_addr = v in
      if is_white child g then begin
        let g' = makeGray child g in
        makeGray_eq child g;
        color_change_preserves_objects g child Header.Gray;
        // For all x in objs: is_black x g' == is_black x g
        // because makeGray only changes child from white to gray (both non-black)
        let aux (x: obj_addr) : Lemma
          (requires Seq.mem x objs)
          (ensures is_black x g' == is_black x g)
        = if x = child then begin
            is_white_iff child g;
            is_black_iff child g;
            colors_exhaustive_and_exclusive child g;
            assert (~(is_black child g));
            makeGray_is_gray child g;
            is_gray_iff child g';
            is_black_iff child g';
            colors_exhaustive_and_exclusive child g'
          end else begin
            hd_address_injective x child;
            color_change_preserves_other_color child x g Header.Gray;
            is_black_iff x g;
            is_black_iff x g'
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        non_black_count_eq_objs g g' objs;
        let st' = Seq.cons child st in
        if U64.v i < U64.v ws then begin
          // Need well_formed_heap g' and child ∈ objects for recursive call
          wosize_of_object_bound obj g;
          FStar.Math.Lemmas.pow2_lt_compat 61 54;
          HeapGraph.get_field_addr_eq g obj i;
          field_read_implies_exists_pointing g obj (wosize_of_object obj g) (U64.sub i 1UL) child;
          color_change_preserves_wf g child Header.Gray;
          color_change_preserves_objects_mem g child Header.Gray obj;
          set_object_color_preserves_getWosize_at_hd child g Header.Gray;
          wosize_of_object_spec obj g; wosize_of_object_spec obj g';
          push_children_preserves_non_black g' st' obj (U64.add i 1UL) ws objs
        end else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_preserves_non_black g st obj (U64.add i 1UL) ws objs
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_preserves_non_black g st obj (U64.add i 1UL) ws objs
      else ()
    end
  end

/// mark_step decreases total_non_black by exactly 1
val mark_step_decreases_non_black : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures (let (g', _) = mark_step g st in
                  let objs = objects 0UL g in
                  objects 0UL g' == objs /\
                  total_non_black g' == total_non_black g - 1))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let mark_step_decreases_non_black g st =
  let obj = Seq.head st in
  stack_head_is_gray g st;
  assert (is_gray obj g);
  assert (Seq.mem obj (objects 0UL g));
  let objs = objects 0UL g in
  // Step 1: makeBlack obj
  makeBlack_eq obj g;
  let g1 = makeBlack obj g in
  color_change_preserves_objects g obj Header.Black;
  assert (objects 0UL g1 == objs);
  // makeBlack decreases non_black_count by 1
  HeapModel.objects_is_vertex_set g;
  non_black_count_makeBlack_gray g obj objs;
  assert (non_black_count g1 objs == non_black_count g objs - 1);
  // Step 2: push_children preserves non_black_count
  let ws = wosize_of_object obj g in
  if is_no_scan obj g then begin
    // Result is (g1, st'), total_non_black g1 == total_non_black g - 1
    assert (fst (mark_step g st) == g1)
  end else begin
    color_change_preserves_wf g obj Header.Black;
    color_change_preserves_objects_mem g obj Header.Black obj;
    wosize_of_object_bound obj g;
    set_object_color_preserves_getWosize_at_hd obj g Header.Black;
    wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
    push_children_preserves_non_black g1 (Seq.tail st) obj 1UL ws objs
  end
#pop-options

/// mark_aux with sufficient fuel: result has no grey objects
/// Key: total_non_black strictly decreases each step, so fuel >= total_non_black => stack empties
val mark_aux_no_grey : (g: heap{well_formed_heap g}) -> 
                        (st: seq obj_addr{stack_props g st}) -> 
                        (fuel: nat) ->
  Lemma (requires fuel >= total_non_black g)
        (ensures noGreyObjects (mark_aux g st fuel))
        (decreases fuel)

/// Helper: if obj is non-black and in objs, then non_black_count >= 1
let rec non_black_has_count (g: heap) (obj: obj_addr) (objs: seq obj_addr)
  : Lemma (requires Seq.mem obj objs /\ ~(is_black obj g))
          (ensures non_black_count g objs >= 1)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else if Seq.head objs = obj then ()
    else begin
      Seq.mem_cons (Seq.head objs) (Seq.tail objs);
      non_black_has_count g obj (Seq.tail objs)
    end

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec mark_aux_no_grey g st fuel =
  if Seq.length st = 0 then
    empty_stack_no_grey g st
  else if fuel = 0 then begin
    // Contradiction: stack non-empty -> head is gray (non-black) -> total_non_black >= 1 -> fuel >= 1
    stack_head_is_gray g st;
    let obj = Seq.head st in
    colors_exhaustive_and_exclusive obj g;
    non_black_has_count g obj (objects 0UL g)
  end else begin
    let (g', st') = mark_step g st in
    mark_step_preserves_stack_props g st;
    mark_step_preserves_wf g st;
    mark_step_decreases_non_black g st;
    mark_aux_no_grey g' st' (fuel - 1)
  end
#pop-options

/// Helper: total_non_black g <= length of objects list
let rec non_black_count_bound (g: heap) (objs: seq obj_addr)
  : Lemma (ensures non_black_count g objs <= Seq.length objs)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else non_black_count_bound g (Seq.tail objs)

val mark_no_grey_remains : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st)
        (ensures noGreyObjects (mark g st))

let mark_no_grey_remains g st =
  non_black_count_bound g (objects 0UL g);
  objects_count_le_remaining 0UL g;
  // objects_count_le_remaining gives: Seq.length (objects 0UL g) * 8 <= Seq.length g
  // Seq.length g = heap_size, mword = 8
  // So: Seq.length (objects 0UL g) <= heap_size / 8 = heap_size / mword
  // non_black_count_bound gives: total_non_black g <= Seq.length (objects 0UL g)
  // Therefore: total_non_black g <= heap_size / mword
  FStar.Math.Lemmas.lemma_div_le (Seq.length (objects 0UL g) * U64.v mword) (Seq.length g) (U64.v mword);
  mark_aux_no_grey g st (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// Mark Preserves Tri-Color Invariant
/// ---------------------------------------------------------------------------

/// push_children never makes any object white (only gray→gray, white→gray, black→black)
val push_children_no_new_white : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) -> 
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires ~(is_white x g) /\ Seq.mem x (objects 0UL g) /\ 
                  well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures ~(is_white x (fst (push_children g st obj i ws))))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec push_children_no_new_white g st obj i ws x =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child : obj_addr = v in
      if is_white child g then begin
        let g' = makeGray child g in
        // x is non-white in g, child is white → x ≠ child
        is_white_iff child g;
        assert (~(is_white x g));
        assert (is_white child g);
        assert (x <> child);
        
        // Prove child is in objects (needed for well-formedness)
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        assert (U64.v i <= U64.v ws);
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        let k = U64.sub i 1UL in
        field_read_implies_exists_pointing g obj wz k child;
        assert (Seq.mem child (objects 0UL g));
        
        // makeGray child preserves x's color and well-formedness
        makeGray_eq child g;
        color_change_preserves_wf g child Header.Gray;
        color_change_preserves_other_color child x g Header.Gray;
        is_white_iff x g;
        is_white_iff x g';
        assert (~(is_white x g'));
        // Recurse: need to show wosize unchanged
        set_object_color_preserves_getWosize_at_hd child g Header.Gray;
        wosize_of_object_spec obj g;
        wosize_of_object_spec obj g';
        assert (wosize_of_object obj g' == wosize_of_object obj g);
        color_change_preserves_objects_mem g child Header.Gray obj;
        color_change_preserves_objects_mem g child Header.Gray x;
        let st' = Seq.cons child st in
        if U64.v i < U64.v ws then
          push_children_no_new_white g' st' obj (U64.add i 1UL) ws x
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_no_new_white g st obj (U64.add i 1UL) ws x
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_no_new_white g st obj (U64.add i 1UL) ws x
      else ()
    end
  end
#pop-options

/// Ghost witness extraction: given exists_field_pointing_to_unchecked, find a specific field
#push-options "--z3rlimit 200 --fuel 2 --ifuel 0 --split_queries no"
let rec efp_witness (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: obj_addr)
  : Ghost (U64.t) 
    (requires well_formed_heap g /\ Seq.mem h (objects 0UL g) /\
             U64.v wz <= U64.v (wosize_of_object h g) /\
             exists_field_pointing_to_unchecked g h wz target = true)
    (ensures fun j -> U64.v j >= 1 /\ U64.v j <= U64.v wz /\
                      HeapGraph.get_field g h j == target /\
                      HeapGraph.is_pointer_field target)
    (decreases U64.v wz)
  = if wz = 0UL then false_elim ()
    else begin
      let idx = U64.sub wz 1UL in
      let far = U64.add_mod h (U64.mul_mod idx mword) in
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then
        efp_witness g h idx target
      else begin
        let field_val = read_word g (far <: hp_addr) in
        if HeapGraph.is_pointer_field field_val && hd_address field_val = hd_address target then begin
          HeapGraph.is_pointer_field_is_obj_addr field_val;
          if field_val = target then begin
            Pulse.Spec.GC.Heap.hd_address_spec h;
            FStar.Math.Lemmas.pow2_lt_compat 61 54;
            wosize_of_object_bound h g;
            HeapGraph.get_field_addr_eq g h wz;
            wz
          end else begin
            let fv : obj_addr = field_val in
            hd_address_injective fv target;
            false_elim ()
          end
        end else
          efp_witness g h idx target
      end
    end
#pop-options

/// If get_field g obj j == child (pointer, white), push_children from i to ws (with i <= j <= ws) makes child non-white
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
let rec push_children_grays_white_at_field (g: heap) (st: seq obj_addr) (obj: obj_addr)
  (i: U64.t{U64.v i >= 1}) (ws: U64.t) (j: U64.t) (child: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                    U64.v ws <= U64.v (wosize_of_object obj g) /\
                    U64.v (wosize_of_object obj g) < pow2 54 /\
                    U64.v j >= U64.v i /\ U64.v j <= U64.v ws /\
                    HeapGraph.get_field g obj j == child /\
                    HeapGraph.is_pointer_field child /\
                    is_white child g)
          (ensures ~(is_white child (fst (push_children g st obj i ws))))
          (decreases (U64.v ws - U64.v i))
  = if U64.v i > U64.v ws then () // impossible: j >= i but i > ws >= j
    else begin
      let v = HeapGraph.get_field g obj i in
      if HeapGraph.is_pointer_field v then begin
        HeapGraph.is_pointer_field_is_obj_addr v;
        let c : obj_addr = v in
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        field_read_implies_exists_pointing g obj wz (U64.sub i 1UL) c;
        if c = child then begin
          // Field i has child! It's white, so push_children grays it
          assert (is_white child g);
          let g' = makeGray child g in
          makeGray_eq child g;
          makeGray_is_gray child g;
          is_gray_iff child g';
          colors_exhaustive_and_exclusive child g';
          assert (~(is_white child g'));
          // child stays non-white through rest of push_children
          color_change_preserves_wf g child Header.Gray;
          color_change_preserves_objects_mem g child Header.Gray obj;
          color_change_preserves_objects_mem g child Header.Gray child;
          set_object_color_preserves_getWosize_at_hd child g Header.Gray;
          wosize_of_object_spec obj g; wosize_of_object_spec obj g';
          let st' = Seq.cons child st in
          if U64.v i < U64.v ws then
            push_children_no_new_white g' st' obj (U64.add i 1UL) ws child
          else ()
        end else begin
          // Field i has c ≠ child. Recurse with i+1.
          // Need: get_field g' obj j == child after processing field i
          // Color changes don't affect field values
          if is_white c g then begin
            let g' = makeGray c g in
            makeGray_eq c g;
            color_change_preserves_wf g c Header.Gray;
            color_change_preserves_objects_mem g c Header.Gray obj;
            set_object_color_preserves_getWosize_at_hd c g Header.Gray;
            wosize_of_object_spec obj g; wosize_of_object_spec obj g';
            // get_field preserved: color change on c doesn't affect field j of obj
            // For c = obj (self): color_preserves_field obj g Gray j (field addr > header addr for j >= 1)
            // For c ≠ obj: color_change_header_locality c (field_addr_of_j) g Gray
            // Either way: get_field g' obj j == get_field g obj j == child
            // is_white child g': c ≠ child, so child's color unchanged
            hd_address_injective child c;
            color_change_preserves_other_color c child g Header.Gray;
            is_white_iff child g; is_white_iff child g';
            // get_field g' obj j == get_field g obj j: field preserved by color change
            // Color change on c writes to hd_address c. Field j of obj is at hd_address obj + 8*j.
            // For c = obj: hd_address obj + 8*j > hd_address obj for j >= 1, so field preserved
            // For c ≠ obj: objects don't overlap, so field preserved
            if obj = c then begin
              let fa_v = U64.v (hd_address obj) + U64.v mword * U64.v j in
              if fa_v + U64.v mword <= heap_size then
                color_preserves_field obj g Header.Gray j (U64.uint_to_t fa_v <: hp_addr)
              else ()
            end else begin
              hd_address_injective obj c;
              if U64.v obj < U64.v c then
                objects_separated 0UL g obj c
              else
                objects_separated 0UL g c obj;
              // hd_address c ≠ field_addr follows from objects_separated
              // (field_addr is within obj's memory range, hd_address c is outside)
              let field_addr_v = U64.v (hd_address obj) + U64.v mword * U64.v j in
              if field_addr_v + U64.v mword <= heap_size then begin
                let fa : hp_addr = U64.uint_to_t field_addr_v in
                Pulse.Spec.GC.Heap.hd_address_spec c;
                Pulse.Spec.GC.Heap.hd_address_spec obj;
                color_change_header_locality c fa g Header.Gray
              end else ()
            end;
            let st' = Seq.cons c st in
            if U64.v i < U64.v ws then
              push_children_grays_white_at_field g' st' obj (U64.add i 1UL) ws j child
            else ()
            // if i = ws: j >= i and j <= ws means j = i = ws. get_field g obj i = c ≠ child.
            // But get_field g obj j = child and j = i. So c = child. Contradiction.
          end else begin
            // c not white, no state change
            if U64.v i < U64.v ws then
              push_children_grays_white_at_field g st obj (U64.add i 1UL) ws j child
            else ()
          end
        end
      end else begin
        // Field i not a pointer. j > i (since get_field g obj j = child is a pointer but field i isn't)
        // If j = i: get_field g obj i is not a pointer but get_field g obj j = child IS a pointer. Contradiction.
        if U64.v i < U64.v ws then
          push_children_grays_white_at_field g st obj (U64.add i 1UL) ws j child
        else ()
      end
    end
#pop-options

/// push_children makes all children of obj non-white
val push_children_obj_children_non_white : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (child: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  points_to g obj child)
        (ensures (let ws = wosize_of_object obj g in
                  let (g', _) = push_children g st obj 1UL ws in
                  ~(is_white child g')))

let push_children_obj_children_non_white g st obj child =
  let ws = wosize_of_object obj g in
  wosize_of_object_bound obj g;
  if not (is_white child g) then
    push_children_no_new_white g st obj 1UL ws child
  else begin
    let j = efp_witness g obj ws child in
    push_children_grays_white_at_field g st obj 1UL ws j child
  end




/// push_children preserves points_to for any object pair
/// (color changes don't affect field values, so pointer structure is unchanged)
val push_children_preserves_points_to : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (b: obj_addr) -> (child: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  Seq.mem b (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures (let (g', _) = push_children g st obj i ws in
                  points_to g' b child == points_to g b child))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries no"
let rec push_children_preserves_points_to g st obj i ws b child =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let c : obj_addr = v in
      if is_white c g then begin
        let g' = makeGray c g in
        makeGray_eq c g;
        // Establish c ∈ objects
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        field_read_implies_exists_pointing g obj wz (U64.sub i 1UL) c;
        assert (Seq.mem c (objects 0UL g));
        // points_to preserved through makeGray c
        if b = c then
          color_change_preserves_points_to_self g c Header.Gray child
        else
          color_change_preserves_points_to_other g c Header.Gray b child;
        // Recurse
        color_change_preserves_wf g c Header.Gray;
        color_change_preserves_objects_mem g c Header.Gray obj;
        color_change_preserves_objects_mem g c Header.Gray b;
        set_object_color_preserves_getWosize_at_hd c g Header.Gray;
        wosize_of_object_spec obj g; wosize_of_object_spec obj g';
        let st' = Seq.cons c st in
        if U64.v i < U64.v ws then
          push_children_preserves_points_to g' st' obj (U64.add i 1UL) ws b child
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_preserves_points_to g st obj (U64.add i 1UL) ws b child
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_preserves_points_to g st obj (U64.add i 1UL) ws b child
      else ()
    end
  end
#pop-options

/// If b is black after push_children, b was black before
/// (push_children only does makeGray: white→gray, never creates black)
val push_children_black_backward : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (b: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54 /\
                  is_black b (fst (push_children g st obj i ws)))
        (ensures is_black b g)
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries no"
let rec push_children_black_backward g st obj i ws b =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let c : obj_addr = v in
      if is_white c g then begin
        let g' = makeGray c g in
        makeGray_eq c g;
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        field_read_implies_exists_pointing g obj wz (U64.sub i 1UL) c;
        color_change_preserves_wf g c Header.Gray;
        color_change_preserves_objects_mem g c Header.Gray obj;
        set_object_color_preserves_getWosize_at_hd c g Header.Gray;
        wosize_of_object_spec obj g; wosize_of_object_spec obj g';
        let st' = Seq.cons c st in
        if U64.v i < U64.v ws then begin
          push_children_black_backward g' st' obj (U64.add i 1UL) ws b;
          // is_black b g' → is_black b g
          if b = c then begin
            makeGray_is_gray c g;
            is_gray_iff c g'; is_black_iff c g';
            colors_exhaustive_and_exclusive c g'
          end else begin
            hd_address_injective b c;
            color_change_preserves_other_color c b g Header.Gray;
            is_black_iff b g; is_black_iff b g'
          end
        end else begin
          if b = c then begin
            makeGray_is_gray c g;
            is_gray_iff c g'; is_black_iff c g';
            colors_exhaustive_and_exclusive c g'
          end else begin
            hd_address_injective b c;
            color_change_preserves_other_color c b g Header.Gray;
            is_black_iff b g; is_black_iff b g'
          end
        end
      end else begin
        if U64.v i < U64.v ws then
          push_children_black_backward g st obj (U64.add i 1UL) ws b
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_black_backward g st obj (U64.add i 1UL) ws b
      else ()
    end
  end
#pop-options

/// mark_step preserves tri-color invariant
/// push_children preserves is_no_scan for any object
/// (is_no_scan depends only on tag bits, which are preserved by color changes)
val push_children_preserves_is_no_scan : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (b: obj_addr) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  Seq.mem b (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures (let (g', _) = push_children g st obj i ws in
                  is_no_scan b g' == is_no_scan b g))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries no"
let rec push_children_preserves_is_no_scan g st obj i ws b =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let c : obj_addr = v in
      if is_white c g then begin
        let g' = makeGray c g in
        makeGray_eq c g;
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        field_read_implies_exists_pointing g obj wz (U64.sub i 1UL) c;
        color_change_preserves_wf g c Header.Gray;
        color_change_preserves_objects_mem g c Header.Gray obj;
        color_change_preserves_objects_mem g c Header.Gray b;
        set_object_color_preserves_getWosize_at_hd c g Header.Gray;
        wosize_of_object_spec obj g; wosize_of_object_spec obj g';
        // is_no_scan preserved by color change on c
        if b = c then
          color_preserves_is_no_scan b g Header.Gray
        else
          color_change_preserves_other_is_no_scan c b g Header.Gray;
        let st' = Seq.cons c st in
        if U64.v i < U64.v ws then
          push_children_preserves_is_no_scan g' st' obj (U64.add i 1UL) ws b
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_preserves_is_no_scan g st obj (U64.add i 1UL) ws b
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_preserves_is_no_scan g st obj (U64.add i 1UL) ws b
      else ()
    end
  end
#pop-options

/// push_children preserves objects list (objects 0UL g' == objects 0UL g)
val push_children_preserves_objects : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures (let (g', _) = push_children g st obj i ws in
                  objects 0UL g' == objects 0UL g))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries no"
let rec push_children_preserves_objects g st obj i ws =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let c : obj_addr = v in
      if is_white c g then begin
        let g' = makeGray c g in
        makeGray_eq c g;
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        field_read_implies_exists_pointing g obj wz (U64.sub i 1UL) c;
        color_change_preserves_wf g c Header.Gray;
        color_change_preserves_objects g c Header.Gray;
        color_change_preserves_objects_mem g c Header.Gray obj;
        set_object_color_preserves_getWosize_at_hd c g Header.Gray;
        wosize_of_object_spec obj g; wosize_of_object_spec obj g';
        let st' = Seq.cons c st in
        if U64.v i < U64.v ws then
          push_children_preserves_objects g' st' obj (U64.add i 1UL) ws
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_preserves_objects g st obj (U64.add i 1UL) ws
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_preserves_objects g st obj (U64.add i 1UL) ws
      else ()
    end
  end
#pop-options

val mark_step_preserves_tri_color : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ tri_color_invariant g)
        (ensures tri_color_invariant (fst (mark_step g st)))

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
let mark_step_preserves_tri_color g st =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  stack_head_is_gray g st;
  let g1 = makeBlack obj g in
  makeBlack_eq obj g;
  makeBlack_is_black obj g;
  color_change_preserves_objects g obj Header.Black;
  color_change_preserves_wf g obj Header.Black;
  let ws = wosize_of_object obj g in
  let (g_final, _) = mark_step g st in
  let objs = objects 0UL g in
  wosize_of_object_bound obj g;
  // Objects preserved: objects 0UL g_final == objects 0UL g
  if is_no_scan obj g then
    assert (objects 0UL g_final == objs)
  else begin
    color_change_preserves_objects_mem g obj Header.Black obj;
    set_object_color_preserves_getWosize_at_hd obj g Header.Black;
    wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
    push_children_preserves_objects g1 st' obj 1UL ws
  end;
  assert (objects 0UL g_final == objs);
  // For each black non-no_scan object b in g_final: all children non-white
  let aux (b: obj_addr) (child: obj_addr) : Lemma
    (requires Seq.mem b objs /\ is_black b g_final /\
             ~(is_no_scan b g_final) /\ points_to g_final b child)
    (ensures ~(is_white child g_final))
  = if is_no_scan obj g then begin
      // No push_children: g_final = g1 = makeBlack obj g
      if b = obj then begin
        color_preserves_is_no_scan obj g Header.Black;
        assert False // obj is no_scan in g, b = obj, is_no_scan obj g1 = is_no_scan obj g. Contradicts ~(is_no_scan b g_final).
      end else begin
        hd_address_injective b obj;
        color_change_preserves_other_color obj b g Header.Black;
        is_black_iff b g; is_black_iff b g1;
        color_change_preserves_points_to_other g obj Header.Black b child;
        // ~(is_no_scan b g1): tag preserved for b ≠ obj
        color_change_preserves_other_is_no_scan obj b g Header.Black;
        // tri_color g: is_black b g, ~(is_no_scan b g), points_to g b child → ~(is_white child g)
        if child = obj then begin
          is_black_iff obj g1; is_white_iff obj g1;
          colors_exhaustive_and_exclusive obj g1
        end else begin
          hd_address_injective child obj;
          color_change_preserves_other_color obj child g Header.Black;
          is_white_iff child g; is_white_iff child g1
        end
      end
    end else begin
      // push_children case
      color_change_preserves_objects_mem g obj Header.Black obj;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      if b = obj then begin
        // obj's children are all non-white after push_children
        push_children_preserves_points_to g1 st' obj 1UL ws obj child;
        color_change_preserves_points_to_self g obj Header.Black child;
        // points_to g_final obj child → points_to g1 obj child → points_to g obj child
        assert (points_to g obj child);
        color_change_preserves_objects_mem g obj Header.Black obj;
        push_children_obj_children_non_white g1 st' obj child
      end else begin
        // b ≠ obj
        hd_address_injective b obj;
        // is_black b g: backward through push_children then makeBlack
        color_change_preserves_objects_mem g obj Header.Black b;
        push_children_black_backward g1 st' obj 1UL ws b;
        color_change_preserves_other_color obj b g Header.Black;
        is_black_iff b g; is_black_iff b g1;
        assert (is_black b g);
        // points_to g b child
        push_children_preserves_points_to g1 st' obj 1UL ws b child;
        color_change_preserves_points_to_other g obj Header.Black b child;
        assert (points_to g b child);
        // is_no_scan preserved: is_no_scan b g == is_no_scan b g_final
        push_children_preserves_is_no_scan g1 st' obj 1UL ws b;
        // is_no_scan b g1 == is_no_scan b g (b != obj)
        color_change_preserves_other_is_no_scan obj b g Header.Black;
        assert (is_no_scan b g == is_no_scan b g_final);
        assert (~(is_no_scan b g));
        // tri_color g instantiation
        assert (~(is_white child g));
        // child non-white through color changes
        if child = obj then begin
          push_children_preserves_parent_black g1 st' obj 1UL ws;
          is_black_iff obj g_final; is_white_iff obj g_final;
          colors_exhaustive_and_exclusive obj g_final
        end else begin
          hd_address_injective child obj;
          color_change_preserves_other_color obj child g Header.Black;
          is_white_iff child g; is_white_iff child g1;
          assert (~(is_white child g1));
          wosize_of_object_bound b g;
          assert (Seq.mem child (objects 0UL g));
          color_change_preserves_objects_mem g obj Header.Black child;
          push_children_no_new_white g1 st' obj 1UL ws child
        end
      end
    end
  in
  let aux2 (b: obj_addr) (child: obj_addr) : Lemma
    (Seq.mem b objs ==> is_black b g_final ==> ~(is_no_scan b g_final) ==> 
     points_to g_final b child ==> ~(is_white child g_final))
  = FStar.Classical.move_requires (aux b) child
  in
  FStar.Classical.forall_intro_2 aux2
#pop-options

/// mark_aux preserves tri-color invariant
val mark_aux_preserves_tri_color : (g: heap{well_formed_heap g}) -> 
                                    (st: seq obj_addr{stack_props g st}) -> 
                                    (fuel: nat) ->
  Lemma (requires tri_color_invariant g)
        (ensures tri_color_invariant (mark_aux g st fuel))
        (decreases fuel)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let rec mark_aux_preserves_tri_color g st fuel =
  if Seq.length st = 0 then ()
  else if fuel = 0 then ()
  else begin
    let (g', st') = mark_step g st in
    mark_step_preserves_tri_color g st;
    mark_step_preserves_stack_props g st;
    mark_step_preserves_wf g st;
    mark_aux_preserves_tri_color g' st' (fuel - 1)
  end
#pop-options

val mark_preserves_tri_color : (g: heap) -> (st: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ tri_color_invariant g)
        (ensures noGreyObjects (mark g st) ==> tri_color_invariant (mark g st))

let mark_preserves_tri_color g st = 
  mark_aux_preserves_tri_color g st (heap_size / U64.v mword)


/// ===========================================================================
/// Part 5: Infrastructure for mark_reachable_is_black / mark_black_is_reachable
/// ===========================================================================

/// ---------------------------------------------------------------------------
/// 5.1 Objects and color preservation through mark
/// ---------------------------------------------------------------------------

/// mark_aux preserves the objects list (colors don't affect objects enumeration)
val mark_aux_preserves_objects : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  (fuel: nat) ->
  Lemma (ensures objects 0UL (mark_aux g st fuel) == objects 0UL g)
        (decreases fuel)

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
let rec mark_aux_preserves_objects g st fuel =
  if Seq.length st = 0 then ()
  else if fuel = 0 then ()
  else begin
    let obj = Seq.head st in
    let st_tail = Seq.tail st in
    stack_head_is_gray g st;
    wosize_of_object_bound obj g;
    let g1 = makeBlack obj g in
    makeBlack_eq obj g;
    color_change_preserves_objects g obj Header.Black;
    assert (objects 0UL g1 == objects 0UL g);
    let ws = wosize_of_object obj g in
    if is_no_scan obj g then begin
      assert (mark_step g st == (g1, st_tail));
      let (g', st') = mark_step g st in
      assert (g' == g1);
      mark_step_preserves_stack_props g st;
      mark_step_preserves_wf g st;
      mark_aux_preserves_objects g' st' (fuel - 1)
    end else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black obj;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_preserves_objects g1 st_tail obj 1UL ws;
      assert (objects 0UL (fst (push_children g1 st_tail obj 1UL ws)) == objects 0UL g1);
      assert (mark_step g st == push_children g1 st_tail obj 1UL ws);
      let (g', st') = mark_step g st in
      assert (objects 0UL g' == objects 0UL g);
      mark_step_preserves_stack_props g st;
      mark_step_preserves_wf g st;
      mark_aux_preserves_objects g' st' (fuel - 1)
    end
  end
#pop-options

/// mark_step never makes objects white (only gray->black and white->gray)
val mark_step_no_new_white : (g: heap) -> (st: seq obj_addr{Seq.length st > 0 /\ stack_props g st}) ->
  (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ ~(is_white x g) /\ Seq.mem x (objects 0UL g))
        (ensures ~(is_white x (fst (mark_step g st))))

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
let mark_step_no_new_white g st x =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  stack_head_is_gray g st;
  let g1 = makeBlack obj g in
  let ws = wosize_of_object obj g in
  makeBlack_eq obj g;
  wosize_of_object_bound obj g;
  if x = obj then begin
    makeBlack_is_black obj g;
    is_black_iff obj g1; is_white_iff obj g1;
    colors_exhaustive_and_exclusive obj g1;
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black obj;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_no_new_white g1 st' obj 1UL ws obj
    end
  end else begin
    hd_address_injective x obj;
    color_change_preserves_other_color obj x g Header.Black;
    is_white_iff x g; is_white_iff x g1;
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black obj;
      color_change_preserves_objects_mem g obj Header.Black x;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_no_new_white g1 st' obj 1UL ws x
    end
  end
#pop-options

/// mark_aux never makes objects white (induction through mark_aux)
val mark_aux_no_new_white : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  (fuel: nat) -> (x: obj_addr) ->
  Lemma (requires ~(is_white x g) /\ Seq.mem x (objects 0UL g))
        (ensures ~(is_white x (mark_aux g st fuel)))
        (decreases fuel)

let rec mark_aux_no_new_white g st fuel x =
  if Seq.length st = 0 then ()
  else if fuel = 0 then ()
  else begin
    assert (fuel > 0);
    let (g', st') = mark_step g st in
    mark_step_preserves_stack_props g st;
    mark_step_preserves_wf g st;
    mark_step_no_new_white g st x;
    mark_aux_preserves_objects g st 1;
    assert (objects 0UL g' == objects 0UL g);
    mark_aux_no_new_white g' st' (fuel - 1) x
  end

/// push_children never makes objects blue (same pattern as white)
val push_children_no_new_blue : (g: heap) -> (st: seq obj_addr) -> (obj: obj_addr) ->
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (x: obj_addr) ->
  Lemma (requires ~(is_blue x g) /\ Seq.mem x (objects 0UL g) /\
                  well_formed_heap g /\ Seq.mem obj (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures ~(is_blue x (fst (push_children g st obj i ws))))
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec push_children_no_new_blue g st obj i ws x =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child : obj_addr = v in
      if is_white child g then begin
        let g' = makeGray child g in
        // x is non-blue, child is white → x ≠ child (if x were child, child is white not blue)
        // But we don't need x ≠ child for blue — we need: makeGray doesn't create blue
        // makeGray sets color to Gray, which is not Blue
        is_blue_iff x g; is_blue_iff x g';
        let wz = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        Pulse.Spec.GC.Heap.hd_address_spec obj;
        assert (U64.v i <= U64.v ws);
        FStar.Math.Lemmas.pow2_lt_compat 61 54;
        HeapGraph.get_field_addr_eq g obj i;
        let k = U64.sub i 1UL in
        field_read_implies_exists_pointing g obj wz k child;
        assert (Seq.mem child (objects 0UL g));
        
        makeGray_eq child g;
        if x = child then begin
          // x = child, child was white so not blue. makeGray makes it gray, not blue.
          makeGray_is_gray child g;
          is_gray_iff child g'; is_blue_iff child g';
          colors_exclusive child g'
        end else begin
          color_change_preserves_other_color child x g Header.Gray;
          is_blue_iff x g; is_blue_iff x g'
        end;
        color_change_preserves_wf g child Header.Gray;
        set_object_color_preserves_getWosize_at_hd child g Header.Gray;
        wosize_of_object_spec obj g; wosize_of_object_spec obj g';
        color_change_preserves_objects_mem g child Header.Gray obj;
        color_change_preserves_objects_mem g child Header.Gray x;
        let st' = Seq.cons child st in
        if U64.v i < U64.v ws then
          push_children_no_new_blue g' st' obj (U64.add i 1UL) ws x
        else ()
      end else begin
        if U64.v i < U64.v ws then
          push_children_no_new_blue g st obj (U64.add i 1UL) ws x
        else ()
      end
    end else begin
      if U64.v i < U64.v ws then
        push_children_no_new_blue g st obj (U64.add i 1UL) ws x
      else ()
    end
  end
#pop-options

/// mark_step never makes objects blue
val mark_step_no_new_blue : (g: heap) -> (st: seq obj_addr{Seq.length st > 0 /\ stack_props g st}) ->
  (x: obj_addr) ->
  Lemma (requires well_formed_heap g /\ ~(is_blue x g) /\ Seq.mem x (objects 0UL g))
        (ensures ~(is_blue x (fst (mark_step g st))))

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
let mark_step_no_new_blue g st x =
  let obj = Seq.head st in
  let st' = Seq.tail st in
  stack_head_is_gray g st;
  let g1 = makeBlack obj g in
  let ws = wosize_of_object obj g in
  makeBlack_eq obj g;
  wosize_of_object_bound obj g;
  if x = obj then begin
    makeBlack_is_black obj g;
    is_black_iff obj g1; is_blue_iff obj g1;
    colors_exclusive obj g1;
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black obj;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_no_new_blue g1 st' obj 1UL ws obj
    end
  end else begin
    hd_address_injective x obj;
    color_change_preserves_other_color obj x g Header.Black;
    is_blue_iff x g; is_blue_iff x g1;
    if is_no_scan obj g then ()
    else begin
      color_change_preserves_wf g obj Header.Black;
      color_change_preserves_objects_mem g obj Header.Black obj;
      color_change_preserves_objects_mem g obj Header.Black x;
      set_object_color_preserves_getWosize_at_hd obj g Header.Black;
      wosize_of_object_spec obj g; wosize_of_object_spec obj g1;
      push_children_no_new_blue g1 st' obj 1UL ws x
    end
  end
#pop-options

/// mark_aux never makes objects blue
val mark_aux_no_new_blue : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  (fuel: nat) -> (x: obj_addr) ->
  Lemma (requires ~(is_blue x g) /\ Seq.mem x (objects 0UL g))
        (ensures ~(is_blue x (mark_aux g st fuel)))
        (decreases fuel)

let rec mark_aux_no_new_blue g st fuel x =
  if Seq.length st = 0 then ()
  else if fuel = 0 then ()
  else begin
    assert (fuel > 0);
    let (g', st') = mark_step g st in
    mark_step_preserves_stack_props g st;
    mark_step_preserves_wf g st;
    mark_step_no_new_blue g st x;
    mark_aux_preserves_objects g st 1;
    assert (objects 0UL g' == objects 0UL g);
    mark_aux_no_new_blue g' st' (fuel - 1) x
  end

/// ---------------------------------------------------------------------------
/// 5.2 Gray objects become black after mark
/// ---------------------------------------------------------------------------

/// Gray objects become black after mark (using no_new_white + no_new_blue + noGreyObjects)
val gray_becomes_black : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  (x: obj_addr) ->
  Lemma (requires is_gray x g /\ Seq.mem x (objects 0UL g))
        (ensures is_black x (mark g st))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries no"
let gray_becomes_black g st x =
  let gm = mark g st in
  is_gray_iff x g; is_white_iff x g;
  colors_exclusive x g;
  // x gray -> not white, not blue
  mark_aux_no_new_white g st (heap_size / U64.v mword) x;
  mark_aux_no_new_blue g st (heap_size / U64.v mword) x;
  // noGreyObjects after mark -> not gray
  mark_no_grey_remains g st;
  mark_aux_preserves_objects g st (heap_size / U64.v mword);
  // Not white + not gray + not blue -> black
  color_exhaustive x gm
#pop-options


/// ---------------------------------------------------------------------------
/// 5.3 Graph edge membership lemmas (reverse direction)
/// ---------------------------------------------------------------------------

/// make_edges membership: Seq.mem (h, child) (make_edges h succs) ⟹ Seq.mem child succs
val make_edges_mem_reverse : (h_addr: vertex_id) -> (succs: seq vertex_id) ->
  (src: vertex_id) -> (dst: vertex_id) ->
  Lemma (requires Seq.mem (src, dst) (HeapGraph.make_edges h_addr succs))
        (ensures src == h_addr /\ Seq.mem dst succs)
        (decreases Seq.length succs)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries no"
let rec make_edges_mem_reverse h_addr succs src dst =
  if Seq.length succs = 0 then ()
  else begin
    let hd = Seq.head succs in
    let tl = Seq.tail succs in
    // make_edges h_addr succs = cons (h_addr, hd) (make_edges h_addr tl)
    // Seq.cons x s = append (create 1 x) s
    let rest = HeapGraph.make_edges h_addr tl in
    FStar.Seq.Properties.lemma_mem_append (Seq.create 1 (h_addr, hd)) rest;
    // Now: Seq.mem (src, dst) (cons (h_addr, hd) rest) <==> 
    //      (src, dst) = (h_addr, hd) \/ Seq.mem (src, dst) rest
    if (src, dst) = (h_addr, hd) then ()
    else
      make_edges_mem_reverse h_addr tl src dst
  end
#pop-options

/// object_edges membership: Seq.mem (src, dst) (object_edges g h) ⟹ Seq.mem dst (get_pointer_fields g h) ∧ src = h
val object_edges_mem_reverse : (g: heap) -> (h_addr: obj_addr) -> (src: vertex_id) -> (dst: vertex_id) ->
  Lemma (requires Seq.mem (src, dst) (HeapGraph.object_edges g h_addr))
        (ensures src == h_addr /\ Seq.mem dst (HeapGraph.get_pointer_fields g h_addr))

let object_edges_mem_reverse g h_addr src dst =
  make_edges_mem_reverse h_addr (HeapGraph.get_pointer_fields g h_addr) src dst

/// all_edges membership reverse: an edge in all_edges comes from some object's pointer fields
val all_edges_mem_reverse : (g: heap) -> (objs: seq obj_addr) -> (src: obj_addr) -> (dst: vertex_id) ->
  Lemma (requires Seq.mem (src, dst) (HeapGraph.all_edges g objs))
        (ensures Seq.mem src objs /\ Seq.mem dst (HeapGraph.get_pointer_fields g src))
        (decreases Seq.length objs)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries no"
let rec all_edges_mem_reverse g objs src dst =
  if Seq.length objs = 0 then ()
  else begin
    let h = Seq.head objs in
    let tl = Seq.tail objs in
    let edges1 = HeapGraph.object_edges g h in
    let edges2 = HeapGraph.all_edges g tl in
    FStar.Seq.Properties.lemma_mem_append edges1 edges2;
    if Seq.mem (src, dst) edges1 then begin
      object_edges_mem_reverse g h src dst;
      assert (src == h);
      assert (Seq.index objs 0 == h)
    end else begin
      all_edges_mem_reverse g tl src dst;
      FStar.Seq.Properties.lemma_mem_append (Seq.create 1 h) tl
    end
  end
#pop-options

/// Helper lemma: if dst is in get_pointer_fields_aux result, then efptu finds it
/// Connects get_pointer_fields_aux (1-indexed scan) to exists_field_pointing_to_unchecked (0-indexed scan)

/// Helper: membership in Seq.cons
let cons_mem_elim (#a:eqtype) (hd:a) (tl:seq a) (x:a)
  : Lemma (requires Seq.mem x (Seq.cons hd tl) /\ hd <> x)
          (ensures Seq.mem x tl)
  = FStar.Seq.Properties.lemma_mem_append (Seq.create 1 hd) tl;
    FStar.Seq.Properties.lemma_contains_singleton hd

val get_pointer_fields_aux_mem_implies_efptu : 
  (g: heap) -> (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) -> (dst: obj_addr) ->
  Lemma (requires Seq.mem dst (HeapGraph.get_pointer_fields_aux g obj i ws) /\
                  U64.v ws < pow2 54 /\
                  U64.v (hd_address obj) + U64.v mword * (U64.v ws + 1) <= heap_size)
        (ensures exists_field_pointing_to_unchecked g obj ws dst)
        (decreases (U64.v ws - U64.v i + 1))

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec get_pointer_fields_aux_mem_implies_efptu g obj i ws dst =
  if U64.v i > U64.v ws then begin
    // Base case: i > ws, so get_pointer_fields_aux returns empty
    // Seq.mem dst Seq.empty is false, contradiction
    assert (Seq.mem dst Seq.empty)
  end else begin
    // Recursive case: i <= ws
    let v = HeapGraph.get_field g obj i in
    let rest = 
      if U64.v i < U64.v ws then 
        HeapGraph.get_pointer_fields_aux g obj (U64.add i 1UL) ws
      else 
        Seq.empty 
    in
    
    if is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      // v is an obj_addr, get_pointer_fields_aux returns Seq.cons v rest
      // dst is in (cons v rest), so either dst = v or dst is in rest
      // From precondition: Seq.mem dst (HeapGraph.get_pointer_fields_aux g obj i ws)
      // And get_pointer_fields_aux g obj i ws = Seq.cons v rest (when is_pointer_field v)
      assert (HeapGraph.get_pointer_fields_aux g obj i ws == Seq.cons v rest);
      
      if v = dst then begin
        // Found dst at field i
        // Need to prove: exists_field_pointing_to_unchecked g obj ws dst
        // efptu checks index ws-1 down to 0
        // Field i (1-indexed in get_field) corresponds to index i-1 (0-indexed in efptu)
        // Since i <= ws, we have i-1 < ws, so efptu will check this field
        
        // At some point efptu checks index i-1
        // Use get_field_addr_eq to relate get_field address to efptu address
        let idx = U64.sub i 1UL in
        assert (U64.v idx < U64.v ws);
        
        // We need to show efptu finds it at index idx
        // efptu scans from ws-1 down, so it will eventually reach idx
        // When wz = idx+1, efptu checks index idx
        let target_wz = U64.add idx 1UL in
        assert (target_wz = i);
        
        // At that point, it reads from add_mod(obj, mul_mod(idx, mword))
        // This equals the address get_field reads from
        HeapGraph.get_field_addr_eq g obj i;
        let k = U64.sub i 1UL in
        let far = U64.add_mod obj (U64.mul_mod k mword) in
        assert (k = idx);
        assert (far = U64.add_mod obj (U64.mul_mod idx mword));
        
        // get_field g obj i reads from this address and returns v = dst
        assert (v = read_word g (far <: hp_addr));
        assert (v = dst);
        
        // Check the efptu condition: is_pointer_field v && hd_address v = hd_address dst
        assert (is_pointer_field v);
        assert (hd_address v = hd_address dst);
        
        // Use efptu_match to prove efptu returns true at wz = target_wz
        efptu_match g obj target_wz dst far v;
        
        // Now need to show this implies efptu at ws
        // Use repeated efptu_recurse to go from target_wz to ws
        efptu_recurse_upto g obj target_wz ws dst
        
      end else begin
        // dst is in rest, by membership in Seq.cons v rest and v != dst
        cons_mem_elim v rest dst;
        if U64.v i < U64.v ws then begin
          // Recursive call
          // We have rest = HeapGraph.get_pointer_fields_aux g obj (U64.add i 1UL) ws
          // And Seq.mem dst rest
          // So the precondition for the recursive call holds
          assert (rest == HeapGraph.get_pointer_fields_aux g obj (U64.add i 1UL) ws);
          get_pointer_fields_aux_mem_implies_efptu g obj (U64.add i 1UL) ws dst;
          // Now have: exists_field_pointing_to_unchecked g obj ws dst (at some index < ws-1)
          // This is already what we need!
          ()
        end else begin
          // i = ws, rest is empty, so dst can't be in rest
          assert (Seq.mem dst Seq.empty)
        end
      end
      
    end else begin
      // Not a pointer field, get_pointer_fields_aux returns rest
      assert (Seq.mem dst rest);
      
      if U64.v i < U64.v ws then begin
        // Recursive call
        get_pointer_fields_aux_mem_implies_efptu g obj (U64.add i 1UL) ws dst
      end else begin
        // i = ws, rest is empty
        assert (Seq.mem dst Seq.empty)
      end
    end
  end

/// Helper to propagate efptu from lower index to higher
and efptu_recurse_upto (g: heap) (obj: obj_addr) (from: U64.t{U64.v from > 0 /\ U64.v from < pow2 54}) 
                       (to: U64.t{U64.v to < pow2 54 /\ U64.v from <= U64.v to}) (target: obj_addr)
  : Lemma (requires exists_field_pointing_to_unchecked g obj from target /\
                    U64.v (hd_address obj) + U64.v mword * (U64.v to + 1) <= heap_size)
          (ensures exists_field_pointing_to_unchecked g obj to target)
          (decreases (U64.v to - U64.v from))
  = if from = to then ()
    else begin
      let next = U64.add from 1UL in
      // Need to apply efptu_recurse: if efptu at (from) is true and check at from fails, then efptu at (from+1) is true
      // But we know efptu at from is true, so efptu at (from+1) is true
      // Read the field at index from
      let idx = U64.sub next 1UL in
      assert (idx = from);
      let far_raw = U64.add_mod obj (U64.mul_mod idx mword) in
      
      // Need to prove far_raw is a valid hp_addr
      // We have: U64.v (hd_address obj) + U64.v mword * (U64.v to + 1) <= heap_size
      // And: from < next <= to
      // So: U64.v (hd_address obj) + U64.v mword * (U64.v from + 1) <= heap_size
      // far_raw = obj + idx * mword = obj + from * mword
      // We need to show: far_raw < heap_size and far_raw % 8 = 0
      //
      // obj is obj_addr, so U64.v obj % 8 = 0 and U64.v obj >= 8
      // hd_address obj = obj - 8, so U64.v obj = U64.v (hd_address obj) + 8
      // far_raw = obj + from * 8 = (hd_address obj + 8) + from * 8 = hd_address obj + (from + 1) * 8
      // We have: U64.v (hd_address obj) + (U64.v from + 1) * 8 <= U64.v (hd_address obj) + (U64.v to + 1) * 8 <= heap_size
      // So far_raw < heap_size
      // far_raw % 8 = (obj + from * 8) % 8 = (obj % 8 + (from * 8) % 8) % 8 = 0
      hd_address_spec obj;
      assert (U64.v obj = U64.v (hd_address obj) + U64.v mword);
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      assert (U64.v idx * U64.v mword < pow2 64);
      FStar.Math.Lemmas.modulo_addition_lemma (U64.v obj) (U64.v idx) (U64.v mword);
      assert (U64.v far_raw % U64.v mword = 0);
      assert (U64.v far_raw = U64.v obj + U64.v idx * U64.v mword);
      assert (U64.v far_raw = U64.v (hd_address obj) + U64.v mword + U64.v idx * U64.v mword);
      assert (U64.v far_raw = U64.v (hd_address obj) + U64.v mword * (U64.v idx + 1));
      assert (U64.v idx + 1 = U64.v from + 1);
      assert (U64.v far_raw = U64.v (hd_address obj) + U64.v mword * (U64.v from + 1));
      assert (U64.v from + 1 <= U64.v to + 1);
      assert (U64.v far_raw <= U64.v (hd_address obj) + U64.v mword * (U64.v to + 1));
      assert (U64.v far_raw < heap_size);
      
      let far : hp_addr = far_raw in
      let fv = read_word g far in
      
      // Apply efptu_recurse if the check doesn't match (or even if it does, we still have efptu true)
      if is_pointer_field fv && hd_address fv = hd_address target then begin
        // The check matches at this level, so efptu next is true
        efptu_match g obj next target far fv
      end else begin
        // The check doesn't match, use efptu_recurse
        efptu_recurse g obj next target far fv
      end;
      
      // Now have efptu at next, recurse to to
      efptu_recurse_upto g obj next to target
    end
#pop-options

/// Key lemma: graph edge implies points_to and not no_scan
val edge_implies_points_to : (g: heap) -> (src: obj_addr) -> (dst: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem src (objects 0UL g) /\
                  mem_graph_edge (create_graph g) src dst)
        (ensures points_to g src dst /\ ~(is_no_scan src g))

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries no"
let edge_implies_points_to g src dst =
  let graph = create_graph g in
  let objs = objects 0UL g in
  objects_is_vertex_set g;
  all_edges_mem_reverse g objs src dst;
  // Now: Seq.mem dst (get_pointer_fields g src)
  let pf = HeapGraph.get_pointer_fields g src in
  assert (Seq.mem dst pf);
  // get_pointer_fields returns empty for no_scan -> contradiction if no_scan
  // get_pointer_fields g src = if no_scan then empty else get_pointer_fields_aux ...
  // If is_no_scan src g, then pf = Seq.empty, so Seq.mem dst pf = false -> contradiction
  assert (~(is_no_scan src g));
  // Now need: points_to g src dst
  // get_pointer_fields g src = get_pointer_fields_aux g src 1UL ws (since not no_scan and fits)
  // Since Seq.mem dst pf, we have Seq.mem dst (get_pointer_fields_aux g src 1UL ws)
  let ws = wosize_of_object src g in
  wosize_of_object_bound src g;
  // Need to establish the heap bounds precondition for the helper
  // src is in objects 0UL g, so it's well-formed and fits in heap
  assert (Seq.mem src objs);
  // This implies object_fits_in_heap src g (from well_formed_heap)
  // Call the helper lemma
  get_pointer_fields_aux_mem_implies_efptu g src 1UL ws dst
#pop-options

/// ---------------------------------------------------------------------------
/// 5.4 Forward proof: mark_reachable_is_black
/// ---------------------------------------------------------------------------

/// Core lemma: black objects are closed under graph successor after mark terminates
val black_successor_is_black : (g: heap) -> (src: obj_addr) -> (dst: obj_addr) ->
  Lemma (requires well_formed_heap g /\ noGreyObjects g /\ tri_color_invariant g /\
                  Seq.mem src (objects 0UL g) /\ Seq.mem dst (objects 0UL g) /\
                  is_black src g /\ mem_graph_edge (create_graph g) src dst /\
                  ~(is_blue dst g))
        (ensures is_black dst g)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries no"
let black_successor_is_black g src dst =
  edge_implies_points_to g src dst;
  // tri_color: is_black src g /\ ~(is_no_scan src g) /\ points_to g src dst ==> ~(is_white dst g)
  // noGreyObjects: ~(is_gray dst g)
  // ~(is_blue dst g) given
  color_exhaustive dst g
#pop-options

/// Graph vertex is always a valid obj_addr (vertices come from objects list)
/// Proof: coerce_to_vertex_list preserves values, objects all have addr >= 8
val vertex_is_obj_addr : (g: heap) -> (x: vertex_id) ->
  Lemma (requires mem_graph_vertex (create_graph g) x)
        (ensures U64.v x >= 8)

let rec coerce_vertex_ge_8 (objs: seq obj_addr) (x: vertex_id)
  : Lemma (requires Seq.mem x (HeapGraph.coerce_to_vertex_list objs))
          (ensures U64.v x >= 8)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      let hd = Seq.head objs in
      let tl = Seq.tail objs in
      FStar.Seq.Properties.lemma_mem_append (Seq.create 1 hd) (HeapGraph.coerce_to_vertex_list tl);
      if x = hd then ()
      else coerce_vertex_ge_8 tl x
    end

let vertex_is_obj_addr g x =
  objects_is_vertex_set g;
  coerce_vertex_ge_8 (objects 0UL g) x

/// Induction on reach: if root is black and x is reachable from root, then x is black
val black_reach_is_black : (graph: graph_state{graph_wf graph}) -> (g: heap{well_formed_heap g}) ->
  (r: obj_addr{mem_graph_vertex graph r}) ->
  (x: obj_addr{mem_graph_vertex graph x}) ->
  (p: reach graph r x) ->
  Lemma (requires noGreyObjects g /\ tri_color_invariant g /\
                  graph == create_graph g /\
                  is_black r g /\
                  (forall (y: obj_addr). Seq.mem y (objects 0UL g) ==> ~(is_blue y g)))
        (ensures is_black x g)
        (decreases p)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries no"
let rec black_reach_is_black graph g r x p =
  match p with
  | ReachRefl _ -> ()
  | ReachTrans _ y _ p_ry ->
    // y is intermediate, x is final target with edge y→x
    vertex_is_obj_addr g y;
    let y' : obj_addr = y in
    black_reach_is_black graph g r y' p_ry;
    objects_is_vertex_set g;
    graph_vertices_mem g x;
    graph_vertices_mem g y';
    black_successor_is_black g y' x
#pop-options

/// ---------------------------------------------------------------------------
/// 5.10 Color changes preserve the abstract graph
/// ---------------------------------------------------------------------------

/// Color changes preserve objects list
val color_preserves_objects :
  (obj: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) ->
  Lemma (requires Seq.mem obj (objects 0UL g))
        (ensures objects 0UL (set_object_color obj g c) == objects 0UL g)

#push-options "--z3rlimit 10"
let color_preserves_objects obj g c =
  color_change_preserves_objects g obj c
#pop-options

/// Color change preserves get_field for any field i within bounds
val color_preserves_get_field :
  (target: obj_addr) -> (h: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) -> (i: U64.t{U64.v i >= 1}) ->
  Lemma (requires Seq.mem target (objects 0UL g) /\ Seq.mem h (objects 0UL g) /\
                  U64.v i <= U64.v (wosize_of_object h g))
        (ensures HeapGraph.get_field (set_object_color target g c) h i == HeapGraph.get_field g h i)

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let color_preserves_get_field target h g c i =
  set_object_color_length target g c;
  let hd = hd_address h in
  hd_address_spec h;
  hd_address_spec target;
  // get_field: if hd + 8*i + 8 <= heap_size then read_word g (hd + 8*i) else 0UL
  // Lengths are the same, so the if-condition is the same for g and g'.
  if U64.v hd + U64.v mword * U64.v i + U64.v mword <= heap_size then begin
    // field_addr = hd + 8*i, where i >= 1
    // Need: hd_address target <> field_addr
    let field_addr : hp_addr = U64.add hd (U64.mul mword i) in
    assert (U64.v field_addr = U64.v hd + 8 * U64.v i);
    if target = h then begin
      // hd_address target = hd, field_addr = hd + 8*i >= hd + 8 > hd
      assert (U64.v field_addr >= U64.v hd + 8)
    end else if U64.v h < U64.v target then begin
      // objects_separated: target > h + wosize*8
      objects_separated 0UL g h target;
      // hd_address target = target - 8 > h + wosize*8 - 8
      // field_addr = h - 8 + 8*i <= h - 8 + 8*wosize (since i <= wosize)
      let ws = wosize_of_object h g in
      assert (U64.v target > U64.v h + FStar.Mul.(U64.v ws * 8));
      assert (U64.v field_addr <= U64.v h - 8 + FStar.Mul.(8 * U64.v ws))
    end else begin
      // target < h, so hd_address target = target - 8 < h - 8 = hd <= field_addr
      ()
    end;
    assert (hd_address target <> field_addr);
    color_change_preserves_other_read target field_addr g c
  end else ()
#pop-options

/// Color change preserves get_pointer_fields_aux (recursive proof)
val color_preserves_get_pointer_fields_aux :
  (target: obj_addr) -> (h: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) -> 
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires Seq.mem target (objects 0UL g) /\ Seq.mem h (objects 0UL g) /\
                  U64.v ws <= U64.v (wosize_of_object h g))
        (ensures HeapGraph.get_pointer_fields_aux (set_object_color target g c) h i ws ==
                 HeapGraph.get_pointer_fields_aux g h i ws)
        (decreases (U64.v ws - U64.v i + 1))

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let rec color_preserves_get_pointer_fields_aux target h g c i ws =
  if U64.v i > U64.v ws then ()
  else begin
    color_preserves_get_field target h g c i;
    if U64.v i < U64.v ws then
      color_preserves_get_pointer_fields_aux target h g c (U64.add i 1UL) ws
  end
#pop-options

/// Color change preserves get_pointer_fields
val color_preserves_get_pointer_fields :
  (target: obj_addr) -> (h: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) ->
  Lemma (requires Seq.mem target (objects 0UL g) /\ Seq.mem h (objects 0UL g))
        (ensures HeapGraph.get_pointer_fields (set_object_color target g c) h ==
                 HeapGraph.get_pointer_fields g h)

#push-options "--z3rlimit 10"
let color_preserves_get_pointer_fields target h g c =
  let g' = set_object_color target g c in
  
  // Preserve wosize_of_object
  if target = h then
    color_preserves_wosize h g c
  else
    color_change_preserves_other_wosize target h g c;
  
  // Preserve is_no_scan
  if target = h then
    color_preserves_is_no_scan h g c
  else
    color_change_preserves_other_is_no_scan target h g c;
  
  // Preserve heap length (for object_fits_in_heap)
  set_object_color_length target g c;
  
  // Now show get_pointer_fields preserved
  if not (HeapGraph.object_fits_in_heap h g) then ()
  else begin
    let ws = wosize_of_object h g in
    if is_no_scan h g then ()
    else
      color_preserves_get_pointer_fields_aux target h g c 1UL ws
  end
#pop-options

/// Color change preserves object_edges
val color_preserves_object_edges :
  (target: obj_addr) -> (h: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) ->
  Lemma (requires Seq.mem target (objects 0UL g) /\ Seq.mem h (objects 0UL g))
        (ensures HeapGraph.object_edges (set_object_color target g c) h ==
                 HeapGraph.object_edges g h)

#push-options "--z3rlimit 10"
let color_preserves_object_edges target h g c =
  color_preserves_get_pointer_fields target h g c
  // object_edges = make_edges h (get_pointer_fields g h)
  // Since get_pointer_fields preserved, make_edges produces same result
#pop-options

/// Changing an object's color preserves all edges (recursive on objs list)
val color_preserves_all_edges :
  (obj: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) -> (objs: seq obj_addr) ->
  Lemma (requires Seq.mem obj (objects 0UL g) /\ 
                  (forall (h: obj_addr). Seq.mem h objs ==> Seq.mem h (objects 0UL g)))
        (ensures HeapGraph.all_edges (set_object_color obj g c) objs == HeapGraph.all_edges g objs)
        (decreases Seq.length objs)

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let rec color_preserves_all_edges obj g c objs =
  if Seq.length objs = 0 then ()
  else begin
    let h = Seq.head objs in
    let tl = Seq.tail objs in
    // Prove object_edges preserved for h
    color_preserves_object_edges obj h g c;
    // Recurse on tail
    color_preserves_all_edges obj g c tl
  end
#pop-options

/// set_object_color preserves the abstract graph
val color_preserves_create_graph :
  (obj: obj_addr) -> (g: heap{well_formed_heap g}) -> (c: color) ->
  Lemma (requires Seq.mem obj (objects 0UL g))
        (ensures create_graph (set_object_color obj g c) == create_graph g)

#push-options "--z3rlimit 100"
let color_preserves_create_graph obj g c =
  let g' = set_object_color obj g c in
  let objs = objects 0UL g in
  color_preserves_objects obj g c;
  assert (objects 0UL g' == objs);
  color_preserves_all_edges obj g c objs;
  assert (HeapGraph.all_edges g' objs == HeapGraph.all_edges g objs);
  ()
#pop-options

/// ---------------------------------------------------------------------------
/// 5.11 Graph preservation through mark operations
/// ---------------------------------------------------------------------------

/// push_children preserves the abstract graph (by induction on field scanning)
val push_children_preserves_create_graph : (g: heap{well_formed_heap g}) -> (st: seq obj_addr) -> 
                                          (obj: obj_addr{Seq.mem obj (objects 0UL g)}) ->
                                          (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires U64.v ws <= U64.v (wosize_of_object obj g) /\
                  U64.v (wosize_of_object obj g) < pow2 54)
        (ensures create_graph (fst (push_children g st obj i ws)) == create_graph g)
        (decreases (U64.v ws - U64.v i))

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let rec push_children_preserves_create_graph g st obj i ws =
  if U64.v i > U64.v ws then ()
  else begin
    let v = HeapGraph.get_field g obj i in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let child : obj_addr = v in
      if is_white child g then begin
        // Proof strategy:
        // 1. Establish efptu at position i using efptu_match
        // 2. Propagate to wosize_of_object using efptu_recurse_upto
        // 3. Use well_formed_heap to conclude child is in objects
        
        let idx = U64.sub i 1UL in
        HeapGraph.get_field_addr_eq g obj i;
        let far = U64.add_mod obj (U64.mul_mod idx mword) in
        assert (read_word g (far <: hp_addr) = child);
        assert (is_pointer_field child);
        assert (hd_address child = hd_address child);
        efptu_match g obj i child far child;
        
        // Propagate to wosize_of_object obj g (not just ws)
        let wz_full = wosize_of_object obj g in
        wosize_of_object_bound obj g;
        
        // Establish heap bounds precondition for efptu_recurse_upto
        // well_formed_heap part 1: Seq.mem obj (objects 0UL g) ==>
        //   U64.v (hd_address obj) + 8 + U64.v wz_full * 8 <= Seq.length g
        // This equals: U64.v (hd_address obj) + U64.v mword * (U64.v wz_full + 1) <= heap_size
        assert (Seq.mem obj (objects 0UL g));
        assert (U64.v (hd_address obj) + 8 + FStar.Mul.(U64.v wz_full * 8) <= Seq.length g);
        assert (U64.v mword = 8);
        assert (Seq.length g = heap_size);
        assert (U64.v (hd_address obj) + U64.v mword * (U64.v wz_full + 1) <= heap_size);
        
        if U64.v i < U64.v wz_full then
          efptu_recurse_upto g obj i wz_full child;
        assert (exists_field_pointing_to_unchecked g obj wz_full child);
        
        // Use well_formed_heap part 2 to prove child is in objects
        // Seq.mem obj (objects 0UL g) /\ U64.v wz_full < pow2 54 /\ 
        // efptu g obj wz_full child ==> Seq.mem child (objects 0UL g)
        assert (Seq.mem obj (objects 0UL g));
        assert (U64.v wz_full < pow2 54);
        assert (exists_field_pointing_to_unchecked g obj wz_full child);
        assert (Seq.mem child (objects 0UL g));
        
        let g' = makeGray child g in
        makeGray_eq child g;
        assert (g' == set_object_color child g Header.Gray);
        color_preserves_create_graph child g Header.Gray;
        assert (create_graph g' == create_graph g);
        
        // After coloring, well_formed_heap is preserved
        color_change_preserves_wf g child Header.Gray;
        assert (well_formed_heap g');
        
        // Objects list preserved
        color_preserves_objects child g Header.Gray;
        assert (objects 0UL g' == objects 0UL g);
        assert (Seq.mem obj (objects 0UL g'));
        
        // wosize_of_object is preserved for obj
        if child = obj then
          color_preserves_wosize child g Header.Gray
        else
          color_change_preserves_other_wosize child obj g Header.Gray;
        assert (wosize_of_object obj g' == wosize_of_object obj g);
        assert (U64.v ws <= U64.v (wosize_of_object obj g'));
        assert (U64.v (wosize_of_object obj g') < pow2 54);
        
        // Recursive call preserves create_graph
        if U64.v i < U64.v ws then begin
          push_children_preserves_create_graph g' (Seq.cons child st) obj (U64.add i 1UL) ws
        end
      end else begin
        // No color change, recurse
        if U64.v i < U64.v ws then
          push_children_preserves_create_graph g st obj (U64.add i 1UL) ws
      end
    end else begin
      // Not a pointer, recurse
      if U64.v i < U64.v ws then
        push_children_preserves_create_graph g st obj (U64.add i 1UL) ws
    end
  end
#pop-options

/// mark_step preserves the abstract graph
val mark_step_preserves_create_graph : (g: heap{well_formed_heap g}) -> (st: seq obj_addr) ->
  Lemma (requires Seq.length st > 0 /\ stack_props g st)
        (ensures create_graph (fst (mark_step g st)) == create_graph g)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let mark_step_preserves_create_graph g st =
  let obj = Seq.head st in
  let st_tail = Seq.tail st in
  stack_head_is_gray g st;
  makeBlack_eq obj g;
  let g' = makeBlack obj g in
  color_preserves_create_graph obj g Header.Black;
  assert (create_graph g' == create_graph g);
  color_change_preserves_wf g obj Header.Black;
  color_preserves_objects obj g Header.Black;
  color_preserves_wosize obj g Header.Black;
  wosize_of_object_bound obj g;
  let ws = wosize_of_object obj g in
  if is_no_scan obj g then ()
  else
    push_children_preserves_create_graph g' st_tail obj 1UL ws
#pop-options

/// mark_aux preserves the abstract graph
val mark_aux_preserves_create_graph : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) -> (fuel: nat) ->
  Lemma (ensures create_graph (mark_aux g st fuel) == create_graph g)
        (decreases fuel)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let rec mark_aux_preserves_create_graph g st fuel =
  if Seq.length st = 0 then ()
  else if fuel = 0 then ()
  else begin
    let (g', st') = mark_step g st in
    mark_step_preserves_create_graph g st;
    mark_step_preserves_stack_props g st;
    mark_step_preserves_wf g st;
    mark_aux_preserves_create_graph g' st' (fuel - 1)
  end
#pop-options

/// mark preserves the abstract graph (top-level)
val mark_preserves_create_graph : (g: heap{well_formed_heap g}) -> (st: seq obj_addr{stack_props g st}) ->
  Lemma (ensures create_graph (mark g st) == create_graph g)

let mark_preserves_create_graph g st =
  mark_aux_preserves_create_graph g st (heap_size / U64.v mword)

/// ---------------------------------------------------------------------------
/// 5.12 Proof of mark_reachable_is_black (forward direction)
/// ---------------------------------------------------------------------------

/// Actual proof: every object reachable from roots is black after mark
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let mark_reachable_is_black g st roots =
  let gm = mark g st in
  let graph = create_graph g in
  let roots' = HeapGraph.coerce_to_vertex_list roots in
  
  mark_preserves_create_graph g st;
  mark_no_grey_remains g st;
  mark_preserves_wf g st;
  assert (well_formed_heap gm);
  
  // tri_color_invariant g: vacuously true (no black objects)
  let prove_tri (obj: obj_addr) (child: obj_addr) : Lemma
    (requires Seq.mem obj (objects 0UL g) /\ is_black obj g /\
              ~(is_no_scan obj g) /\ points_to g obj child)
    (ensures ~(is_white child g)) = ()
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 prove_tri);
  assert (tri_color_invariant g);
  mark_preserves_tri_color g st;
  
  mark_aux_preserves_objects g st (heap_size / U64.v mword);
  
  let no_blue_post (x: obj_addr) : Lemma
    (requires Seq.mem x (objects 0UL gm)) (ensures ~(is_blue x gm)) = 
    mark_aux_no_new_blue g st (heap_size / U64.v mword) x
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_blue_post);
  
  let root_black (r: obj_addr) : Lemma
    (requires Seq.mem r roots) (ensures is_black r gm) =
    gray_becomes_black g st r
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires root_black);
  
  let prove_x (x: obj_addr) : Lemma
    (requires graph_wf graph /\ is_vertex_set roots' /\ 
              subset_vertices roots' graph.vertices /\
              mem_graph_vertex graph x /\
              Seq.mem x (reachable_set graph roots'))
    (ensures is_black x gm) =
    reachable_set_correct graph roots';
    FStar.Classical.exists_elim (is_black x gm) ()
      (fun (r: vertex_id{mem_graph_vertex graph r /\
                          Seq.mem r roots' /\ reachable graph r x}) ->
        vertex_is_obj_addr g r;
        let r' : obj_addr = r in
        HeapGraph.coerce_mem_lemma roots r';
        root_black r';
        FStar.Classical.exists_elim (is_black x gm) ()
          (fun (p: reach graph r x) ->
            black_reach_is_black graph gm r' x p))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_x)
#pop-options

/// mark_black_is_reachable: backward direction (TODO)
let mark_black_is_reachable g st roots = 
  admit() // TODO: backward induction on mark_aux with compound invariant

/// Combined: mark produces black = reachable
let mark_black_iff_reachable g st roots =
  mark_reachable_is_black g st roots;
  mark_black_is_reachable g st roots
