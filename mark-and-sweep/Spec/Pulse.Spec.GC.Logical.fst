/// Logical GC Spec: mark, sweep, collect, and reachability on heap_l
///
/// These are the "obviously correct" definitions that operate on the logical
/// heap type. Each is ~10 lines. The bridge to raw byte-level specs is in
/// separate lemmas.
module Pulse.Spec.GC.Logical

open FStar.Seq
open FStar.List.Tot
open FStar.UInt64
module U64 = FStar.UInt64
module Header = Pulse.Lib.Header

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap

/// ---------------------------------------------------------------------------
/// L4: push_children_l, mark_step_l, mark_l
/// ---------------------------------------------------------------------------

/// Push white pointer children onto the gray stack, graying them.
let rec push_children_l (hl: heap_l) (st: list obj_addr) (flds: list U64.t)
  : GTot (heap_l & list obj_addr)
         (decreases flds)
  = match flds with
    | [] -> (hl, st)
    | f :: rest ->
      if U64.v f >= 8 && U64.v f < heap_size && U64.v f % 8 = 0 then
        match lookup hl f with
        | Some ol ->
          if ol.color = Header.White then
            let hl' = update_color_l hl f Header.Gray in
            push_children_l hl' (f :: st) rest
          else push_children_l hl st rest
        | None -> push_children_l hl st rest
      else push_children_l hl st rest

/// One mark step: pop object from stack, blacken it, push white children.
let mark_step_l (hl: heap_l) (st: list obj_addr{length st > 0})
  : GTot (heap_l & list obj_addr)
  = let obj = hd st in
    let tl = tl st in
    match lookup hl obj with
    | Some ol ->
      let hl' = update_color_l hl obj Header.Black in
      if U64.v ol.tag >= 251 then  // no_scan_tag = 251
        (hl', tl)
      else
        push_children_l hl' tl (seq_to_list ol.fields)
    | None -> (hl, tl)

/// Mark loop with explicit fuel (termination by fuel).
/// In practice, fuel = number of objects suffices since each step
/// blackens one gray object (reducing the gray count).
let rec mark_l (fuel: nat) (hl: heap_l) (st: list obj_addr)
  : GTot heap_l
         (decreases fuel)
  = if fuel = 0 then hl
    else match st with
    | [] -> hl
    | _ -> 
      let (hl', st') = mark_step_l hl st in
      mark_l (fuel - 1) hl' st'

/// Convenience: mark with fuel = domain size (always enough)
let mark (hl: heap_l) (st: list obj_addr) : GTot heap_l =
  mark_l (length (heap_l_domain hl)) hl st

/// ---------------------------------------------------------------------------
/// L5: sweep_object_l, sweep_l
/// ---------------------------------------------------------------------------

/// Sweep one object:
///   White → link into free list (write fp into field 0), object becomes new fp
///   Black → reset to White, keep current fp
///
/// fp_valid: fp is either 0 (null/initial) or a valid object in domain.
/// This ensures update_field_l precondition (pointer closure) is met.
let sweep_object_l (hl: heap_l) (obj: obj_addr) (fp: U64.t)
  : Ghost (heap_l & U64.t)
    (requires (U64.v fp = 0 \/ 
               (U64.v fp >= 8 /\ U64.v fp < heap_size /\ U64.v fp % 8 = 0 /\
                mem fp (heap_l_domain hl))))
    (ensures fun _ -> True)
  = match lookup hl obj with
    | Some ol ->
      if ol.color = Header.White then
        if U64.v ol.wz > 0 then
          let hl' = update_field_l hl obj 0 fp in
          (hl', U64.uint_to_t (U64.v obj))
        else
          (hl, U64.uint_to_t (U64.v obj))
      else begin
        let hl' = update_color_l hl obj Header.White in
        (hl', fp)
      end
    | None -> (hl, fp)

/// Domain preservation for sweep_object_l
let sweep_object_l_preserves_domain (hl: heap_l) (obj: obj_addr) (fp: U64.t)
  : Lemma
    (requires (U64.v fp = 0 \/ 
               (U64.v fp >= 8 /\ U64.v fp < heap_size /\ U64.v fp % 8 = 0 /\
                mem fp (heap_l_domain hl))))
    (ensures heap_l_domain (fst (sweep_object_l hl obj fp)) == heap_l_domain hl)
  = match lookup hl obj with
    | Some ol ->
      if ol.color = Header.White then
        if U64.v ol.wz > 0 then
          update_field_l_preserves_domain hl obj 0 fp
        else ()
      else
        update_color_l_preserves_domain hl obj Header.White
    | None -> ()

/// fp validity after sweep_object_l: fp' is either obj or the old fp
let sweep_object_l_fp_valid (hl: heap_l) (obj: obj_addr) (fp: U64.t)
  : Lemma
    (requires (U64.v fp = 0 \/ 
               (U64.v fp >= 8 /\ U64.v fp < heap_size /\ U64.v fp % 8 = 0 /\
                mem fp (heap_l_domain hl))) /\
              mem obj (heap_l_domain hl))
    (ensures (let (hl', fp') = sweep_object_l hl obj fp in
              U64.v fp' = 0 \/
              (U64.v fp' >= 8 /\ U64.v fp' < heap_size /\ U64.v fp' % 8 = 0 /\
               mem fp' (heap_l_domain hl'))))
  = sweep_object_l_preserves_domain hl obj fp;
    match lookup hl obj with
    | Some ol ->
      if ol.color = Header.White then begin
        // fp' = U64.uint_to_t (U64.v obj) = obj (since U64.uint_to_t (U64.v x) = x)
        // obj is in domain, domain is preserved → fp' ∈ domain
        if U64.v ol.wz > 0 then
          update_field_l_preserves_domain hl obj 0 fp
        else ()
      end
      else
        update_color_l_preserves_domain hl obj Header.White
    | None -> ()

/// Sweep all objects in order.
/// All objects must be in the domain for fp validity.
let rec sweep_l (hl: heap_l) (objs: list obj_addr) (fp: U64.t)
  : Ghost (heap_l & U64.t)
    (requires (U64.v fp = 0 \/
               (U64.v fp >= 8 /\ U64.v fp < heap_size /\ U64.v fp % 8 = 0 /\
                mem fp (heap_l_domain hl))) /\
             (forall x. mem x objs ==> mem x (heap_l_domain hl)))
    (ensures fun _ -> True)
    (decreases objs)
  = match objs with
    | [] -> (hl, fp)
    | obj :: rest ->
      let (hl', fp') = sweep_object_l hl obj fp in
      sweep_object_l_preserves_domain hl obj fp;
      sweep_object_l_fp_valid hl obj fp;
      assert (heap_l_domain hl' == heap_l_domain hl);
      sweep_l hl' rest fp'

/// ---------------------------------------------------------------------------
/// L6: collect_l
/// ---------------------------------------------------------------------------

/// Gray all roots
let rec gray_roots (hl: heap_l) (roots: list obj_addr)
  : GTot heap_l
         (decreases roots)
  = match roots with
    | [] -> hl
    | r :: rest -> gray_roots (update_color_l hl r Header.Gray) rest

/// Domain preservation for gray_roots
let rec gray_roots_preserves_domain (hl: heap_l) (roots: list obj_addr)
  : Lemma (ensures heap_l_domain (gray_roots hl roots) == heap_l_domain hl)
          (decreases roots)
  = match roots with
    | [] -> ()
    | r :: rest -> 
      update_color_l_preserves_domain hl r Header.Gray;
      gray_roots_preserves_domain (update_color_l hl r Header.Gray) rest

/// Domain preservation for push_children_l
let rec push_children_l_preserves_domain (hl: heap_l) (st: list obj_addr) (flds: list U64.t)
  : Lemma (ensures heap_l_domain (fst (push_children_l hl st flds)) == heap_l_domain hl)
          (decreases flds)
  = match flds with
    | [] -> ()
    | f :: rest ->
      if U64.v f >= 8 && U64.v f < heap_size && U64.v f % 8 = 0 then
        match lookup hl f with
        | Some ol ->
          if ol.color = Header.White then begin
            update_color_l_preserves_domain hl f Header.Gray;
            push_children_l_preserves_domain (update_color_l hl f Header.Gray) (f :: st) rest
          end
          else push_children_l_preserves_domain hl st rest
        | None -> push_children_l_preserves_domain hl st rest
      else push_children_l_preserves_domain hl st rest

/// Domain preservation for mark_step_l
let mark_step_l_preserves_domain (hl: heap_l) (st: list obj_addr{length st > 0})
  : Lemma (heap_l_domain (fst (mark_step_l hl st)) == heap_l_domain hl)
  = let obj = hd st in
    match lookup hl obj with
    | Some ol ->
      update_color_l_preserves_domain hl obj Header.Black;
      let hl' = update_color_l hl obj Header.Black in
      if U64.v ol.tag >= 251 then ()
      else push_children_l_preserves_domain hl' (tl st) (seq_to_list ol.fields)
    | None -> ()

/// Domain preservation for mark_l
let rec mark_l_preserves_domain (fuel: nat) (hl: heap_l) (st: list obj_addr)
  : Lemma (ensures heap_l_domain (mark_l fuel hl st) == heap_l_domain hl)
          (decreases fuel)
  = if fuel = 0 then ()
    else match st with
    | [] -> ()
    | _ ->
      mark_step_l_preserves_domain hl st;
      let (hl', st') = mark_step_l hl st in
      mark_l_preserves_domain (fuel - 1) hl' st'

/// Domain preservation for mark
let mark_preserves_domain (hl: heap_l) (st: list obj_addr)
  : Lemma (heap_l_domain (mark hl st) == heap_l_domain hl)
  = mark_l_preserves_domain (length (heap_l_domain hl)) hl st

/// Full GC cycle: gray roots, mark, sweep.
let collect_l (hl: heap_l) (roots: list obj_addr) (fp: U64.t)
  : Ghost (heap_l & U64.t)
    (requires (U64.v fp = 0 \/
               (U64.v fp >= 8 /\ U64.v fp < heap_size /\ U64.v fp % 8 = 0 /\
                mem fp (heap_l_domain hl))))
    (ensures fun _ -> True)
  = let hl_grayed = gray_roots hl roots in
    gray_roots_preserves_domain hl roots;
    let hl_marked = mark hl_grayed roots in
    mark_preserves_domain hl_grayed roots;
    assert (heap_l_domain hl_marked == heap_l_domain hl);
    sweep_l hl_marked (heap_l_domain hl_marked) fp

/// ---------------------------------------------------------------------------
/// L7: Reachability on heap_l
/// ---------------------------------------------------------------------------

/// Reachability via DFS from roots following pointer children.
/// Uses explicit fuel for termination (fuel = domain size suffices).
let rec reachable_l (hl: heap_l) (visited: list obj_addr) (stack: list obj_addr) (fuel: nat)
  : GTot (list obj_addr)
    (decreases fuel)
  = if fuel = 0 then visited
    else match stack with
    | [] -> visited
    | x :: rest ->
      if mem x visited then 
        reachable_l hl visited rest (fuel - 1)
      else
        let kids = children hl x in
        reachable_l hl (x :: visited) (kids @ rest) (fuel - 1)

/// Compute the set of all objects reachable from roots
/// Fuel = domain size * (domain size + 1) suffices for full DFS
let reachable_set_l (hl: heap_l) (roots: list obj_addr) : GTot (list obj_addr) =
  let n = length (heap_l_domain hl) in
  reachable_l hl [] roots (FStar.Mul.(n * (n + 1)))

/// ---------------------------------------------------------------------------
/// Key properties (stated, proofs TODO)
/// ---------------------------------------------------------------------------

/// Stack properties on heap_l
let stack_props_l (hl: heap_l) (st: list obj_addr) : prop =
  (forall x. mem x st ==> mem x (heap_l_domain hl) /\
             (match lookup hl x with Some ol -> ol.color = Header.Gray | None -> False)) /\
  (forall x. mem x (heap_l_domain hl) /\
             (match lookup hl x with Some ol -> ol.color = Header.Gray | None -> False) ==>
             mem x st) /\
  noRepeats st

/// Mark invariant on heap_l
let mark_inv_l (hl: heap_l) (st: list obj_addr) : prop =
  stack_props_l hl st /\ length (heap_l_domain hl) > 0

/// No black-to-white edges (tri-color invariant, used during marking)
let no_black_to_white (hl: heap_l) : prop =
  forall (addr: obj_addr). 
    mem addr (heap_l_domain hl) ==>
    (match lookup hl addr with
     | Some ol -> ol.color = Header.Black ==>
       (forall child. mem child (children_of ol) ==>
         (match lookup hl child with
          | Some col -> col.color <> Header.White
          | None -> True))
     | None -> True)

/// All objects white
let all_white (hl: heap_l) : prop =
  forall (addr: obj_addr).
    mem addr (heap_l_domain hl) ==>
    (match lookup hl addr with
     | Some ol -> ol.color = Header.White
     | None -> True)
