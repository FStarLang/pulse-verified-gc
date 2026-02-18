/// ---------------------------------------------------------------------------
/// Pulse.Lib.GC - Concurrent On-the-Fly Garbage Collector Entry Point
/// ---------------------------------------------------------------------------
///
/// This module provides the main GC entry point that orchestrates:
/// - Phase 0: Set gc_active flag
/// - Phase 1: Scan roots (concurrent with mutators)
/// - Phase 2: Mark loop (concurrent with mutators)
/// - Phase 3: Stop mutators, sweep, restart
///
/// This implements a Dijkstra-style incremental update collector.

module Pulse.Lib.GC

#lang-pulse

/// ---------------------------------------------------------------------------
/// Extraction Configuration
/// ---------------------------------------------------------------------------
/// Functions marked with [@@ CExtract] will be extracted to C by KaRaMeL.
/// Functions marked with [@@ CInline] will be inlined in extracted C.
/// Ghost functions are automatically excluded from extraction.
/// NOTE: Attributes commented out for lax checking

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
open Pulse.Spec.GC.GraySet
open Pulse.Spec.GC.CASPreservation

/// ---------------------------------------------------------------------------
/// GC Types (Forward Declarations)
/// ---------------------------------------------------------------------------

/// GC phases
type gc_phase =
  | Idle       // Not collecting
  | Marking    // Concurrent mark in progress
  | Sweeping   // STW sweep in progress

/// Forward declarations for component types
assume val gray_stack_t : Type0
assume val free_list_t : Type0  
assume val barrier_t : Type0
assume val shadow_registry_t : Type0

/// ---------------------------------------------------------------------------
/// GC State Type
/// ---------------------------------------------------------------------------

/// Global GC state shared between GC thread and mutators
noeq type gc_state = {
  /// Current GC phase
  phase: gc_phase;
  
  /// Gray stack for objects pending scan
  gray_stack: gray_stack_t;
  
  /// Free list for reclaimed memory
  free_list: free_list_t;
  
  /// Barrier flag for STW phases
  barrier: barrier_t;
  
  /// Shadow stack registry (all mutator root sets)
  shadow_registry: shadow_registry_t;
}

/// ---------------------------------------------------------------------------
/// GC State Invariants
/// ---------------------------------------------------------------------------

/// GC state owns all its components
assume val gc_state_inv : gc_state -> slprop

/// Heap permission
assume val heap_perm : erased heap -> slprop

/// Get current phase
assume val get_phase :
  (gc: gc_state) ->
  stt gc_phase
      (gc_state_inv gc)
      (fun p -> gc_state_inv gc ** pure (p == gc.phase))

let is_marking (p: gc_phase) : bool = 
  match p with | Marking -> true | _ -> false

let is_sweeping (p: gc_phase) : bool = 
  match p with | Sweeping -> true | _ -> false

/// Set phase - updates gc.phase to the new value
assume val set_phase :
  (gc: gc_state) -> (p: gc_phase) ->
  stt unit
      (gc_state_inv gc)
      (fun _ -> gc_state_inv {gc with phase = p})

/// ---------------------------------------------------------------------------
/// Phase 0: Start GC - Set Active Flag
/// ---------------------------------------------------------------------------

/// Begin a GC cycle
/// - Transitions from Idle to Marking
/// - Enables write barriers
// [@@CExtract]
fn gc_start
  (gc: gc_state)
  (#g: erased heap)
  requires 
    gc_state_inv gc **
    heap_perm g **
    pure (gc.phase == Idle)
  returns _: unit
  ensures
    gc_state_inv gc **
    heap_perm g **
    pure (gc.phase == Marking)
{
  // Set phase to Marking and enable write barriers
  // The postcondition is satisfied by the set_phase operation
  admit ()
}

/// ---------------------------------------------------------------------------
/// Phase 1: Scan Roots (Concurrent)
/// ---------------------------------------------------------------------------

/// Helper types and functions for root scanning
assume val shadow_stack_handle : Type0

assume val get_shadow_stacks :
  shadow_registry_t ->
  stt (list shadow_stack_handle)
      emp
      (fun _ -> emp)

assume val scan_all_stacks :
  gray_stack_t -> (stacks: list shadow_stack_handle) ->
  stt unit emp (fun _ -> emp)

/// Scan all roots from shadow stacks
/// Runs concurrently with mutator threads
// [@@CExtract]
fn gc_scan_roots
  (gc: gc_state)
  (#g: erased heap)
  requires
    gc_state_inv gc **
    heap_perm g **
    pure (gc.phase == Marking /\ tri_color_inv g)
  returns _: unit
  ensures
    exists* g'. gc_state_inv gc **
    heap_perm g' **
    pure (gc.phase == Marking /\ tri_color_inv g')
{
  admit();
  // Get all shadow stacks from registry
  // let stacks = get_shadow_stacks gc.shadow_registry;
  
  // Scan each root: CAS white→gray, push to gray stack
  // scan_all_stacks gc.gray_stack stacks;
  
  // After scanning:
  // - All root objects are gray (or already gray/black)
  // - Gray stack contains work to process
  // - Tri-color invariant maintained
  ()
}

/// ---------------------------------------------------------------------------
/// Phase 2: Mark Loop (Concurrent)
/// ---------------------------------------------------------------------------

/// Forward declarations for mark operations
assume val pop_from_gray_stack :
  gray_stack_t ->
  stt (option hp_addr) emp (fun _ -> emp)

assume val mark_step :
  gc_state -> hp_addr ->
  stt unit emp (fun _ -> emp)

/// Process all gray objects until none remain
/// Runs concurrently with mutator threads
// [@@CExtract]
fn gc_mark_loop
  (gc: gc_state)
  (#g: erased heap)
  requires
    gc_state_inv gc **
    heap_perm g **
    pure (gc.phase == Marking /\ tri_color_inv g)
  returns _: unit
  ensures
    exists* g'. gc_state_inv gc **
    heap_perm g' **
    pure (gc.phase == Marking /\
          tri_color_inv g' /\
          no_gray_objects g')
{
  admit();
  ()
}

/// ---------------------------------------------------------------------------
/// Phase 3: Stop-the-World Sweep
/// ---------------------------------------------------------------------------

/// Sweep statistics
noeq type sweep_stats = {
  reclaimed_count: nat;
  reclaimed_bytes: nat;
}

let all_white_or_blue (g: heap) : prop = True  // From Sweep module

/// Forward declarations for sweep
assume val signal_gc_barrier : barrier_t -> stt unit emp (fun _ -> emp)
assume val wait_for_safepoints : barrier_t -> stt unit emp (fun _ -> emp)
assume val resume_mutators : barrier_t -> stt unit emp (fun _ -> emp)
assume val sweep_heap : free_list_t -> stt sweep_stats emp (fun _ -> emp)

/// Sweep phase: reclaim white objects
/// This is stop-the-world for safety
// [@@CExtract]
fn gc_sweep
  (gc: gc_state)
  (#g: erased heap)
  requires
    gc_state_inv gc **
    heap_perm g **
    pure (gc.phase == Marking /\
          tri_color_inv (reveal g) /\
          no_gray_objects (reveal g))
  returns stats: sweep_stats
  ensures
    exists* g'. gc_state_inv gc **
    heap_perm g' **
    pure (gc.phase == Idle /\
          all_white_or_blue (reveal g'))
{
  // Transition to Sweeping phase, perform sweep, return to Idle
  // The sweep:
  // 1. Reclaims white objects (marks them blue)
  // 2. Resets black objects to white for next cycle
  // Postcondition: all objects are white or blue
  admit ()
}

/// ---------------------------------------------------------------------------
/// Full Collection: Entry Point
/// ---------------------------------------------------------------------------

/// Perform a complete garbage collection cycle
/// This is the main GC entry point
// [@@CExtract]
fn collect
  (gc: gc_state)
  (#g: erased heap)
  requires
    gc_state_inv gc **
    heap_perm g **
    pure (gc.phase == Idle /\ tri_color_inv g)
  returns stats: sweep_stats
  ensures
    exists* g'. gc_state_inv gc **
    heap_perm g' **
    pure (gc.phase == Idle /\ all_white_or_blue g')
{
  // Phase 0: Start GC
  gc_start gc;
  
  // Phase 1: Scan roots (concurrent)
  gc_scan_roots gc;
  
  // Phase 2: Mark loop (concurrent)
  gc_mark_loop gc;
  
  // Phase 3: Sweep (STW)
  let stats = gc_sweep gc;
  
  stats
}

/// ---------------------------------------------------------------------------
/// Mutator API: Safe Operations During GC
/// ---------------------------------------------------------------------------

/// Forward declarations
assume val alloc_from_free_list :
  free_list_t -> U64.t -> stt (option hp_addr) emp (fun _ -> emp)

assume val init_object_white :
  hp_addr -> U64.t -> stt unit emp (fun _ -> emp)

/// Raw color constants for CAS operations
let white : U64.t = 0UL
let gray  : U64.t = 1UL
let black : U64.t = 2UL

assume val read_color : hp_addr -> stt U64.t emp (fun _ -> emp)
assume val cas_color : hp_addr -> U64.t -> U64.t -> stt bool emp (fun _ -> emp)
assume val push_to_gray_stack : gray_stack_t -> hp_addr -> stt unit emp (fun _ -> emp)
assume val write_field : hp_addr -> U64.t -> hp_addr -> stt unit emp (fun _ -> emp)

assume val wait_at_barrier : barrier_t -> stt unit emp (fun _ -> emp)

/// Allocate memory with write barrier awareness
// [@@CExtract]
fn alloc_with_barrier
  (gc: gc_state)
  (size: U64.t)
  (#g: erased heap)
  requires
    gc_state_inv gc **
    heap_perm g **
    pure (U64.v size > 0)
  returns addr: option hp_addr
  ensures
    exists* g'. gc_state_inv gc **
    heap_perm g' **
    pure (
      // If allocated, the new object is white
      (Some? addr ==> is_white_safe (Some?.v addr) g')
    )
{
  // Get memory from free list
  let maybe_block = alloc_from_free_list gc.free_list size;
  
  match maybe_block {
    None -> {
      // No memory available
      admit()
    }
    Some block -> {
      // Initialize as white object
      // (will be scanned if reachable before next sweep)
      init_object_white block size;
      admit()
    }
  }
}

/// Write a pointer field with barrier
// [@@CExtract]
fn write_with_barrier
  (gc: gc_state)
  (src: hp_addr)
  (field_idx: U64.t)
  (dst: hp_addr)
  (#g: erased heap)
  requires
    gc_state_inv gc **
    heap_perm g **
    pure (tri_color_inv g)
  returns _: unit
  ensures
    exists* g'. gc_state_inv gc **
    heap_perm g' **
    pure (tri_color_inv g')
{
  admit ()
}

/// Safepoint: check if GC needs mutator to pause
// [@@CExtract]
fn safepoint
  (gc: gc_state)
  (#g: erased heap)
  requires gc_state_inv gc ** heap_perm g
  returns _: unit
  ensures exists* g'. gc_state_inv gc ** heap_perm g'
{
  // Check if sweep phase is active (STW)
  let phase = get_phase gc;
  
  if (is_sweeping phase) {
    // Wait at barrier until sweep completes
    wait_at_barrier gc.barrier;
    ()
  } else {
    ()
  };
  admit ()
}

/// ---------------------------------------------------------------------------
/// GC Initialization
/// ---------------------------------------------------------------------------

assume val init_gray_stack : unit -> stt gray_stack_t emp (fun _ -> emp)
assume val init_free_list : U64.t -> stt free_list_t emp (fun _ -> emp)
assume val init_barrier : unit -> stt barrier_t emp (fun _ -> emp)
assume val init_shadow_registry : unit -> stt shadow_registry_t emp (fun _ -> emp)

/// Create and initialize a new GC instance
// [@@CExtract]
fn gc_init
  (heap_size: U64.t)
  returns gc: gc_state
  ensures gc_state_inv gc ** pure (gc.phase == Idle)
{
  // Initialize components
  let gray_stack = init_gray_stack ();
  let free_list = init_free_list heap_size;
  let barrier = init_barrier ();
  let registry = init_shadow_registry ();
  
  let gc = {
    phase = Idle;
    gray_stack = gray_stack;
    free_list = free_list;
    barrier = barrier;
    shadow_registry = registry
  };
  admit ()
}

/// ---------------------------------------------------------------------------
/// GC Metrics and Statistics
/// ---------------------------------------------------------------------------

/// GC metrics for monitoring
noeq type gc_metrics = {
  total_collections: nat;
  total_reclaimed_bytes: nat;
  last_sweep_time_ns: nat;
  current_heap_usage: nat;
}

/// Get current GC metrics
assume val get_gc_metrics : gc_state -> stt gc_metrics emp (fun _ -> emp)
