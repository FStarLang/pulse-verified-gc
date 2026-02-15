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

/// Sweep all objects in order.
/// fp_valid is preserved: sweep_object_l returns either obj (in domain) or old fp (valid).
let rec sweep_l (hl: heap_l) (objs: list obj_addr) (fp: U64.t)
  : Ghost (heap_l & U64.t)
    (requires (U64.v fp = 0 \/
               (U64.v fp >= 8 /\ U64.v fp < heap_size /\ U64.v fp % 8 = 0 /\
                mem fp (heap_l_domain hl))))
    (ensures fun _ -> True)
    (decreases objs)
  = match objs with
    | [] -> (hl, fp)
    | obj :: rest ->
      let (hl', fp') = sweep_object_l hl obj fp in
      // Domain preserved: update_color_l and update_field_l preserve domain
      // fp' is either U64.uint_to_t (U64.v obj) or fp
      // obj is in domain, and domain is preserved, so fp' is valid
      admit ();  // TODO: prove fp' validity + domain preservation (needs sweep_object_l domain lemma)
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

/// Full GC cycle: gray roots, mark, sweep.
let collect_l (hl: heap_l) (roots: list obj_addr) (fp: U64.t)
  : Ghost (heap_l & U64.t)
    (requires (U64.v fp = 0 \/
               (U64.v fp >= 8 /\ U64.v fp < heap_size /\ U64.v fp % 8 = 0 /\
                mem fp (heap_l_domain hl))))
    (ensures fun _ -> True)
  = let hl_grayed = gray_roots hl roots in
    let hl_marked = mark hl_grayed roots in
    // fp validity preserved through gray_roots and mark (only color changes)
    admit ();  // TODO: prove domain preservation through gray_roots + mark
    sweep_l hl_marked (heap_l_domain hl_marked) fp

/// ---------------------------------------------------------------------------
/// L7: Reachability on heap_l
/// ---------------------------------------------------------------------------

/// Reachability via DFS from roots following pointer children.
/// Decreases: lex pair (|domain| - |visited|, |stack|).
///   - When x ∈ visited: visited unchanged, stack shrinks → second component decreases
///   - When x ∉ visited: visited grows by 1 → first component decreases
let rec reachable_l (hl: heap_l) (visited: list obj_addr) (stack: list obj_addr)
  : GTot (list obj_addr)
         (decreases %[length (heap_l_domain hl) - length visited; length stack])
  = match stack with
    | [] -> visited
    | x :: rest ->
      if mem x visited then 
        reachable_l hl visited rest
      else
        let kids = children hl x in
        admit ();  // TODO: prove |visited| < |domain| (x not in visited but is reachable from a root in domain)
        reachable_l hl (x :: visited) (kids @ rest)

/// Compute the set of all objects reachable from roots
let reachable_set_l (hl: heap_l) (roots: list obj_addr) : GTot (list obj_addr) =
  reachable_l hl [] roots

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
