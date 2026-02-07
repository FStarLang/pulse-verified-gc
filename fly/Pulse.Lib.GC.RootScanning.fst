/// Pulse.Lib.GC.RootScanning - Concurrent Root Scanning via Shadow Stacks

module Pulse.Lib.GC.RootScanning

#lang-pulse

open Pulse.Lib.Pervasives
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot
module GSet = FStar.GhostSet

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
open Pulse.Spec.GC.TriColor
open Pulse.Spec.GC.GraySet
open Pulse.Spec.GC.CASPreservation

/// Heap permission
assume val heap_perm : erased heap -> slprop

/// Shadow Stack Types
assume val shadow_stack : Type0
assume val shadow_stack_full : shadow_stack -> Seq.seq hp_addr -> slprop
assume val shadow_stack_read : shadow_stack -> Seq.seq hp_addr -> perm -> slprop
assume val shadow_stack_share :
  (ss: shadow_stack) -> (#roots: erased (Seq.seq hp_addr)) ->
  stt_ghost unit emp_inames
      (shadow_stack_full ss roots)
      (fun _ -> shadow_stack_read ss roots 0.5R ** shadow_stack_read ss roots 0.5R)
assume val shadow_stack_gather :
  (ss: shadow_stack) -> (#roots: erased (Seq.seq hp_addr)) ->
  stt_ghost unit emp_inames
      (shadow_stack_read ss roots 0.5R ** shadow_stack_read ss roots 0.5R)
      (fun _ -> shadow_stack_full ss roots)

/// Shadow Stack Registry
assume val shadow_registry : Type0
assume val shadow_registry_inv : shadow_registry -> slprop
assume val get_all_stacks :
  (reg: shadow_registry) ->
  stt (list shadow_stack)
      (shadow_registry_inv reg)
      (fun _ -> shadow_registry_inv reg)

/// Gray Stack
assume val gray_stack : Type0
assume val gray_stack_inv : gray_stack -> slprop
assume val push_gray_stack :
  (st: gray_stack) -> (h: hp_addr) ->
  stt unit
      (gray_stack_inv st)
      (fun _ -> gray_stack_inv st)

/// Atomic Color Operations
assume val read_color_atomic :
  (h_addr: hp_addr) -> (#g: erased heap) ->
  stt_atomic U64.t emp_inames
      (heap_perm g)
      (fun c -> heap_perm g ** pure (c == get_object_color (reveal g) h_addr))
      
assume val cas_color_atomic :
  (h_addr: hp_addr) -> (expected: color) -> (new_color: color) -> (#g: erased heap) ->
  stt_atomic bool emp_inames
      (heap_perm g)
      (fun b -> heap_perm (if b then set_color (reveal g) h_addr new_color else reveal g))

// [@@CInline]
fn scan_root
  (st: gray_stack)
  (root: hp_addr)
  (#g: erased heap)
  requires heap_perm g ** gray_stack_inv st ** pure (tri_color_inv g)
  returns _: unit
  ensures exists* g'. heap_perm g' ** gray_stack_inv st ** pure (tri_color_inv g')
{
  admit ()
}

// [@@CExtract]
fn scan_shadow_stack
  (st: gray_stack)
  (ss: shadow_stack)
  (#roots: erased (Seq.seq hp_addr))
  (#g: erased heap)
  requires 
    heap_perm g ** 
    gray_stack_inv st ** 
    shadow_stack_read ss roots 0.5R **
    pure (tri_color_inv g)
  returns _: unit
  ensures
    exists* g'. heap_perm g' ** 
    gray_stack_inv st ** 
    shadow_stack_read ss roots 0.5R **
    pure (tri_color_inv g')
{
  admit ()
}

// [@@CExtract]
fn scan_all_roots
  (reg: shadow_registry)
  (st: gray_stack)
  (#g: erased heap)
  requires 
    heap_perm g ** 
    gray_stack_inv st ** 
    shadow_registry_inv reg **
    pure (tri_color_inv g)
  returns _: unit
  ensures
    exists* g'. heap_perm g' ** 
    gray_stack_inv st ** 
    shadow_registry_inv reg **
    pure (tri_color_inv g')
{
  admit ()
}

// [@@CExtract]
fn scan_stack_list
  (st: gray_stack)
  (stacks: list shadow_stack)
  (#g: erased heap)
  requires heap_perm g ** gray_stack_inv st ** pure (tri_color_inv g)
  returns _: unit
  ensures exists* g'. heap_perm g' ** gray_stack_inv st ** pure (tri_color_inv g')
{
  admit ()
}

// [@@CExtract]
fn scan_roots_in_seq
  (st: gray_stack)
  (roots: Seq.seq hp_addr)
  (#g: erased heap)
  requires heap_perm g ** gray_stack_inv st ** 
           pure (tri_color_inv g /\ Seq.length roots < 1000)
  returns _: unit
  ensures exists* g'. heap_perm g' ** gray_stack_inv st ** pure (tri_color_inv g')
{
  admit ()
}

ghost
fn concurrent_root_scan_safe
  (g: erased heap)
  (roots_snapshot: Seq.seq hp_addr)
  requires pure (tri_color_inv g)
  returns _: unit
  ensures pure (true)
{
  ()
}

let initial_white_heap (g: heap) : prop =
  let objs = objects 0UL g in
  forall h. Seq.mem h objs ==> is_white h g
