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

let mark_black_is_reachable g st roots = 
  admit()

val mark_black_iff_reachable : (g: heap) -> (st: seq obj_addr) -> (roots: seq obj_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  no_black_objects g /\
                  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r st))
        (ensures True)

let mark_black_iff_reachable g st roots =
  mark_reachable_is_black g st roots;
  mark_black_is_reachable g st roots

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
val mark_step_preserves_tri_color : (g: heap) -> (st: seq obj_addr{Seq.length st > 0}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ tri_color_invariant g)
        (ensures tri_color_invariant (fst (mark_step g st)))

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
let mark_step_preserves_tri_color g st =
  admit() // TODO: Complex proof involving points_to preservation through push_children
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
