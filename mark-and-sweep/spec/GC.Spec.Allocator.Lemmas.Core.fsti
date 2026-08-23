module GC.Spec.Allocator.Lemmas.Core

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Header = GC.Lib.Header
module AllocCommon = GC.Spec.Allocator.Lemmas.Common
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
/// getWosize of make_header returns the original wosize
val make_header_getWosize : (wz: U64.t{U64.v wz < pow2 54}) ->
                            (c: U64.t{U64.v c < 4}) ->
                            (t: U64.t{U64.v t < 256}) ->
  Lemma (getWosize (make_header wz c t) == wz)

/// Free-list validity: each node is a valid object with wosize >= 1,
/// no self-loops, and the successor (if any) is also fl_valid.
let fl_valid = AllocCommon.fl_valid

/// fl_valid extractors
let fl_valid_gives_mem = AllocCommon.fl_valid_gives_mem

let fl_valid_gives_wosize = AllocCommon.fl_valid_gives_wosize

/// fl_valid introduction: null pointer terminates the free list.
let fl_valid_null = AllocCommon.fl_valid_null

/// fl_valid introduction: a valid node with a valid successor.
let fl_valid_step = AllocCommon.fl_valid_step

/// fl_valid eliminator: extract all components from fl_valid.
let fl_valid_elim = AllocCommon.fl_valid_elim

/// fl_valid base case: fuel = 0 makes fl_valid trivially true.
let fl_valid_zero = AllocCommon.fl_valid_zero

/// fl_valid terminal case: out of bounds, unaligned, or null pointer.
let fl_valid_terminal = AllocCommon.fl_valid_terminal

/// Free-list chain termination: the chain from fp reaches a terminal node
/// (0UL, out of bounds, or unaligned) within the given number of steps.
let fl_chain_terminates = AllocChain.fl_chain_terminates

/// Terminal base cases: 0UL, out of bounds, or misaligned -> always terminates.
val fl_chain_terminates_terminal (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fp = 0UL \/ U64.v fp < U64.v mword \/ U64.v fp >= heap_size \/ U64.v fp % U64.v mword <> 0)
          (ensures fl_chain_terminates g fp steps = true)

/// Step case: fp is valid, hd + 16 <= heap_size, and the tail terminates.
val fl_chain_terminates_step (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    (let hd = hd_address (fp <: obj_addr) in
                     U64.v hd + 16 <= heap_size ==>
                     fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1)))
          (ensures fl_chain_terminates g fp steps)

/// Elimination: if fl_chain_terminates and fp is valid with hd+16 <= heap_size,
/// then the tail also terminates.
val fl_chain_terminates_elim (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fl_chain_terminates g fp steps /\
                    steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1) = true)

/// Valid fp with 0 steps never terminates.
val fl_chain_terminates_valid_zero (g: heap) (fp: U64.t)
  : Lemma (requires U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0)
          (ensures fl_chain_terminates g fp 0 = false)

/// chain_avoids: boolean test for "fp chain does not visit excl".
let chain_avoids = AllocChain.chain_avoids

/// chain_avoids_head_ne: if chain_avoids is true and fp is a valid chain node with fuel > 0,
/// then fp ≠ excl.
val chain_avoids_head_ne (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ fuel > 0)
          (ensures fp <> excl)

/// chain_avoids_tail: one-step decomposition of chain_avoids.
/// When chain_avoids is true at a valid node with hd+16 <= heap_size,
/// the successor chain also avoids excl.
val chain_avoids_tail (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ fuel > 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures chain_avoids g (read_word g (fp <: obj_addr)) excl (fuel - 1) = true)

/// chain_avoids_transfer: transfer chain_avoids between heaps when link reads are preserved
/// for chain nodes (objects in objects(g) with wosize >= 1).
val chain_avoids_transfer (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                      U64.v (wosize_of_object a g) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      a <> excl ==>
                        read_word g' a == read_word g a))
          (ensures chain_avoids g' fp excl fuel = true)

/// Transfer chain_avoids when link reads are preserved on the actual fp-chain
/// nodes (characterized by chain_avoids g fp a fuel = false), excluding excl.
val chain_avoids_transfer_on_chain (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                      U64.v (wosize_of_object a g) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      a <> excl /\
                      chain_avoids g fp a fuel = false ==>
                        read_word g' a == read_word g a))
          (ensures chain_avoids g' fp excl fuel = true)

/// get_color of make_header returns the original color bits
val make_header_getColor : (wz: U64.t{U64.v wz < pow2 54}) ->
                           (c: U64.t{U64.v c < 4}) ->
                           (t: U64.t{U64.v t < 256}) ->
  Lemma (Header.get_color (U64.v (make_header wz c t)) == U64.v c)

/// chain_avoids_transfer_excl2: transfer chain_avoids when reads preserved except at excl or excl2.
val chain_avoids_transfer_excl2 (g g': heap) (fp excl excl2: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    chain_avoids g fp excl2 fuel = true /\
                    fl_valid g fp fuel /\
                    (forall (a: U64.t).
                       (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                        Seq.mem a (objects zero_addr g) /\ a <> excl /\ a <> excl2) ==>
                       (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                        U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                          read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
          (ensures chain_avoids g' fp excl fuel = true)

/// **Theorem**: alloc_spec preserves object membership under just well_formed_heap_part1.
/// (Weaker precondition than alloc_spec_preserves_objects.)
val alloc_spec_preserves_objects_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp heap_words /\
                  fl_chain_terminates g fp heap_words)
        (ensures (let r = alloc_spec g fp requested_wz in
                  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                    Seq.mem x (objects zero_addr r.heap_out))))
