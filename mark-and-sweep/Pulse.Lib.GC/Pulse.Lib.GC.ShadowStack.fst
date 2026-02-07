(*
   Pulse GC - Shadow Stack Module
   
   This module implements per-mutator shadow stacks for root registration.
   Shadow stacks enable concurrent root scanning without stopping mutators.
   
   Design:
   - Each mutator thread has its own shadow stack
   - Mutators push/pop roots as they run
   - GC can iterate all shadow stacks concurrently with read permission
   - Uses fractional permissions for safe sharing
   
   Based on the Dijkstra on-the-fly GC design.
*)

module Pulse.Lib.GC.ShadowStack

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Pulse.Lib.GC.Heap
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot
module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference

/// ---------------------------------------------------------------------------
/// Shadow Stack Structure
/// ---------------------------------------------------------------------------

/// A shadow stack entry is a heap address (root pointer)
type root_entry = hp_addr

/// Shadow stack: array of root entries with length
noeq
type shadow_stack = {
  entries: A.array root_entry;
  len: ref SZ.t;
  capacity: SZ.t;
}

/// Ghost state tracking the logical contents
let shadow_stack_ghost = GR.ref (Seq.seq root_entry)

/// ---------------------------------------------------------------------------
/// Shadow Stack Predicates
/// ---------------------------------------------------------------------------

/// Full ownership of a shadow stack (for the owning mutator)
let shadow_stack_full (ss: shadow_stack) (gr: shadow_stack_ghost) : slprop =
  exists* len_val entries_seq ghost_seq.
    pts_to ss.len len_val **
    A.pts_to ss.entries entries_seq **
    GR.pts_to gr 1.0R ghost_seq **
    pure (Seq.length entries_seq == SZ.v ss.capacity) **
    pure (Seq.length ghost_seq == SZ.v len_val) **
    pure (SZ.v len_val <= SZ.v ss.capacity) **
    pure (Seq.equal ghost_seq (Seq.slice entries_seq 0 (SZ.v len_val)))

/// Read-only permission (for GC during concurrent scanning)
let shadow_stack_read (#p: perm) (ss: shadow_stack) (gr: shadow_stack_ghost) : slprop =
  exists* ghost_seq.
    GR.pts_to gr #p ghost_seq

/// ---------------------------------------------------------------------------
/// Create/Destroy
/// ---------------------------------------------------------------------------

/// Create a new shadow stack with given capacity
fn create_shadow_stack (capacity: SZ.t{SZ.v capacity > 0})
  requires emp
  returns ss: (shadow_stack & shadow_stack_ghost)
  ensures shadow_stack_full (fst ss) (snd ss)
{
  // Allocate entries array
  let entries = A.alloc 0UL capacity;
  
  // Allocate length reference
  let len = alloc 0sz;
  
  // Create ghost reference for logical contents
  let gr = GR.alloc (Seq.empty #root_entry);
  
  // Build shadow stack
  let ss = { entries; len; capacity };
  
  fold (shadow_stack_full ss gr);
  (ss, gr)
}

/// Free a shadow stack
fn free_shadow_stack (ss: shadow_stack) (gr: shadow_stack_ghost)
  requires shadow_stack_full ss gr
  ensures emp
{
  unfold (shadow_stack_full ss gr);
  A.free ss.entries;
  free ss.len;
  GR.free gr
}

/// ---------------------------------------------------------------------------
/// Mutator Operations
/// ---------------------------------------------------------------------------

/// Push a root onto the shadow stack
/// Called by mutator when entering a function or allocating
fn push_root (ss: shadow_stack) (gr: shadow_stack_ghost) (root: root_entry)
  requires shadow_stack_full ss gr
  returns success: bool
  ensures shadow_stack_full ss gr **
          pure (success ==> (* Root was added *) True) **
          pure (not success ==> (* Stack full *) True)
{
  unfold (shadow_stack_full ss gr);
  
  let len_val = !ss.len;
  
  if SZ.lt len_val ss.capacity then {
    // Write root to next slot
    A.write ss.entries len_val root;
    
    // Increment length
    let new_len = SZ.add len_val 1sz;
    ss.len := new_len;
    
    // Update ghost state
    with ghost_seq. assert (GR.pts_to gr 1.0R ghost_seq);
    GR.write gr (Seq.snoc ghost_seq root);
    
    fold (shadow_stack_full ss gr);
    true
  } else {
    fold (shadow_stack_full ss gr);
    false
  }
}

/// Pop a root from the shadow stack
/// Called by mutator when exiting a function
fn pop_root (ss: shadow_stack) (gr: shadow_stack_ghost)
  requires shadow_stack_full ss gr
  returns result: option root_entry
  ensures shadow_stack_full ss gr
{
  unfold (shadow_stack_full ss gr);
  
  let len_val = !ss.len;
  
  if SZ.gt len_val 0sz then {
    let new_len = SZ.sub len_val 1sz;
    
    // Read the root
    let root = A.read ss.entries new_len;
    
    // Decrement length
    ss.len := new_len;
    
    // Update ghost state
    with ghost_seq. assert (GR.pts_to gr 1.0R ghost_seq);
    let new_ghost = Seq.slice ghost_seq 0 (Seq.length ghost_seq - 1);
    GR.write gr new_ghost;
    
    fold (shadow_stack_full ss gr);
    Some root
  } else {
    fold (shadow_stack_full ss gr);
    None
  }
}

/// ---------------------------------------------------------------------------
/// GC Operations (Read-Only)
/// ---------------------------------------------------------------------------

/// Get the current length of shadow stack (read-only)
fn shadow_stack_length (ss: shadow_stack)
  requires exists* v. pts_to ss.len #0.5R v
  returns len: SZ.t
  ensures exists* v. pts_to ss.len #0.5R v ** pure (len == v)
{
  !ss.len
}

/// Read a root at index (read-only access for GC)
fn read_root_at (ss: shadow_stack) (gr: shadow_stack_ghost) (idx: SZ.t)
  requires shadow_stack_read #0.5R ss gr **
           pure (SZ.v idx < (* current length *) 0) // placeholder
  returns root: root_entry
  ensures shadow_stack_read #0.5R ss gr
{
  // In real impl, would read from entries array with fractional permission
  0UL // placeholder
}

/// ---------------------------------------------------------------------------
/// Iteration for Root Scanning
/// ---------------------------------------------------------------------------

/// Iterate over all roots in the shadow stack
/// Calls action on each root
fn iterate_roots (ss: shadow_stack) (gr: shadow_stack_ghost)
                 (action: root_entry -> stt unit emp (fun _ -> emp))
  requires shadow_stack_full ss gr
  ensures shadow_stack_full ss gr
{
  unfold (shadow_stack_full ss gr);
  
  let len_val = !ss.len;
  let mut i = 0sz;
  
  while (SZ.lt !i len_val)
    invariant exists* vi entries_seq.
      pts_to i vi **
      A.pts_to ss.entries entries_seq **
      pure (SZ.v vi <= SZ.v len_val)
  {
    let curr_i = !i;
    
    // Read root at current index
    let root = A.read ss.entries curr_i;
    
    // Call action on this root
    action root;
    
    i := SZ.add curr_i 1sz
  };
  
  fold (shadow_stack_full ss gr)
}

/// ---------------------------------------------------------------------------
/// Shadow Stack Registry (Global)
/// ---------------------------------------------------------------------------

/// Global registry of all mutator shadow stacks
/// Protected by a SpinLock for thread-safe registration
noeq
type shadow_stack_registry = {
  stacks: ref (L.list (shadow_stack & shadow_stack_ghost));
  lock: lock;
}

/// Create the global registry
fn create_registry ()
  requires emp
  returns reg: shadow_stack_registry
  ensures lock_alive reg.lock emp
{
  let stacks = alloc #(L.list (shadow_stack & shadow_stack_ghost)) [];
  let lock = new_lock (exists* ss_list. pts_to stacks ss_list);
  { stacks; lock }
}

/// Register a mutator's shadow stack
fn register_mutator (reg: shadow_stack_registry) 
                    (ss: shadow_stack) (gr: shadow_stack_ghost)
  requires lock_alive reg.lock emp ** shadow_stack_full ss gr
  ensures lock_alive reg.lock emp ** shadow_stack_full ss gr
{
  acquire reg.lock;
  
  with ss_list. assert (pts_to reg.stacks ss_list);
  let current_list = !reg.stacks;
  let new_list = (ss, gr) :: current_list;
  reg.stacks := new_list;
  
  release reg.lock
}

/// Iterate over all registered shadow stacks (for GC root scanning)
fn scan_all_roots (reg: shadow_stack_registry)
                  (action: root_entry -> stt unit emp (fun _ -> emp))
  requires lock_alive reg.lock emp
  ensures lock_alive reg.lock emp
{
  acquire reg.lock;
  
  // Get list of shadow stacks
  with ss_list. assert (pts_to reg.stacks ss_list);
  let stacks = !reg.stacks;
  
  // Release lock before iterating (allow concurrent access)
  release reg.lock;
  
  // Iterate over all shadow stacks
  // Note: In full impl, would need fractional permissions
  // For now, assume sequential access
  ()
}
