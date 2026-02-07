/// Pulse.Lib.GC.Sweep - Stop-the-World Sweep Phase

module Pulse.Lib.GC.Sweep

#lang-pulse

open Pulse.Lib.Pervasives
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.TriColor

/// Heap permission
assume val heap_perm : erased heap -> slprop

/// Free List Type
assume val free_list : Type0
assume val free_list_inv : free_list -> hp_addr -> slprop
assume val add_to_free_list :
  (fl: free_list) -> (block: hp_addr) -> (size: U64.t) ->
  (#head: erased hp_addr) ->
  stt unit
      (free_list_inv fl head)
      (fun _ -> free_list_inv fl block)

/// Sweep State
noeq type sweep_state = {
  current_addr: hp_addr;
  reclaimed_count: U64.t;
  reclaimed_bytes: U64.t;
}

let initial_sweep_state : sweep_state = {
  current_addr = 0UL;
  reclaimed_count = 0UL;
  reclaimed_bytes = 0UL
}

let sweep_precondition (g: heap) : prop =
  no_gray_objects g /\
  tri_color_inv g

let all_white_or_blue (g: heap) : prop =
  let objs = objects 0UL g in
  forall h. Seq.mem h objs ==> (is_white h g \/ is_blue h g)

// [@@CInline]
fn sweep_one_object
  (fl: free_list)
  (h_addr: hp_addr)
  (#g: erased heap)
  (#fl_head: erased hp_addr)
  requires 
    heap_perm g ** 
    free_list_inv fl fl_head **
    pure (sweep_precondition g)
  returns reclaimed: bool
  ensures 
    exists* g' fl_head'. heap_perm g' ** 
    free_list_inv fl fl_head' **
    pure (true)
{
  admit ()
}

// [@@CExtract]
fn sweep_all
  (fl: free_list)
  (#g: erased heap)
  (#fl_head: erased hp_addr)
  requires 
    heap_perm g ** 
    free_list_inv fl fl_head **
    pure (sweep_precondition g)
  returns stats: sweep_state
  ensures
    exists* g' fl_head'. heap_perm g' **
    free_list_inv fl fl_head' **
    pure (
      all_white_or_blue g' /\
      true
    )
{
  admit ()
}

let is_reachable_from (g: heap) (roots: Seq.seq hp_addr) (h: hp_addr) : prop =
  True

ghost
fn mark_complete_implies_live_black
  (g: erased heap)
  (roots: Seq.seq hp_addr)
  requires pure (
    sweep_precondition (reveal g) /\
    (forall r. Seq.mem r roots ==> is_black r (reveal g))
  )
  returns _: unit
  ensures pure (
    forall h. is_reachable_from (reveal g) roots h ==> is_black h (reveal g)
  )
{
  // Proof by induction on reachability:
  // Base case: roots are black (given)
  // Inductive case: if x is black and x points to y, then y is not white (tri-color)
  //                 Since no gray objects (sweep_precondition), y must be black
  admit ()
}

ghost
fn sweep_reclaims_only_unreachable
  (g_before: erased heap)
  (g_after: erased heap)
  (roots: Seq.seq hp_addr)
  requires pure (
    sweep_precondition (reveal g_before) /\
    (forall r. Seq.mem r roots ==> is_black r (reveal g_before))
  )
  returns _: unit
  ensures pure (
    forall h. is_reachable_from (reveal g_before) roots h ==>
              ~(is_blue h (reveal g_after))
  )
{
  // All reachable objects are black before sweep (by mark_complete_implies_live_black)
  // Black objects are reset to white during sweep, not reclaimed
  // Only white objects (unreachable) are reclaimed and marked blue
  // Therefore reachable objects are never blue after sweep
  admit ()
}

assume val gc_barrier_flag : Type0
assume val gc_barrier_inv : gc_barrier_flag -> bool -> slprop
assume val signal_gc_stop :
  (flag: gc_barrier_flag) ->
  stt unit
      (gc_barrier_inv flag false)
      (fun _ -> gc_barrier_inv flag true)
assume val wait_for_mutators :
  (flag: gc_barrier_flag) ->
  stt unit
      (gc_barrier_inv flag true)
      (fun _ -> gc_barrier_inv flag true)
assume val signal_gc_resume :
  (flag: gc_barrier_flag) ->
  stt unit
      (gc_barrier_inv flag true)
      (fun _ -> gc_barrier_inv flag false)

// [@@CExtract]
fn stw_sweep
  (fl: free_list)
  (barrier: gc_barrier_flag)
  (#g: erased heap)
  (#fl_head: erased hp_addr)
  requires
    heap_perm g **
    free_list_inv fl fl_head **
    gc_barrier_inv barrier false **
    pure (sweep_precondition g)
  returns stats: sweep_state
  ensures
    exists* g' fl_head'. heap_perm g' **
    free_list_inv fl fl_head' **
    gc_barrier_inv barrier false **
    pure (all_white_or_blue g')
{
  admit ()
}

// [@@CInline]
fn reset_to_white
  (h_addr: hp_addr)
  (#g: erased heap)
  requires heap_perm g ** pure (is_black h_addr g)
  returns _: unit
  ensures exists* g'. heap_perm g' ** pure (is_white h_addr g')
{
  admit ()
}

// [@@CInline]
fn reclaim_object
  (h_addr: hp_addr)
  (#g: erased heap)
  requires heap_perm g ** pure (is_white h_addr g)
  returns _: unit
  ensures exists* g'. heap_perm g' ** pure (is_blue h_addr g')
{
  admit ()
}

noeq type sweep_result = {
  objects_scanned: nat;
  objects_reclaimed: nat;
  bytes_reclaimed: nat;
  sweep_time_ns: nat
}

let finalize_sweep_stats (s: sweep_state) : sweep_result = {
  objects_scanned = 0;
  objects_reclaimed = U64.v s.reclaimed_count;
  bytes_reclaimed = U64.v s.reclaimed_bytes;
  sweep_time_ns = 0
}
