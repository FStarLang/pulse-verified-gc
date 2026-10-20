/// ---------------------------------------------------------------------------
/// GC.Gen.AllocExact - the free list stays exact, so the first attempt succeeds
/// ---------------------------------------------------------------------------
///
/// A full collection leaves the free list exact (`fused_exact`): it holds
/// exactly the blue blocks that can carry a link.  This module shows that
/// everything that changes the major heap keeps it that way -- allocation,
/// promotion, the pointer rewrite after a minor collection, and the program's
/// own field writes to live objects -- and concludes that an allocation
/// succeeds whenever some free block is big enough
/// (`first_attempt_succeeds_between_collections`).  `fl_complete` is part of
/// the collector's invariant `GC.Gen.HeapInvariant.major_heap_shape`, which
/// both collections re-establish.
///
/// The free-list predicates in `GC.Spec.FreeList` speak of reachability with
/// an existential number of steps; the allocator's own preservation lemmas
/// (`GC.Spec.Allocator.Lemmas`) speak of `chain_avoids` within `heap_words`
/// steps.  The first section bridges the two.  With the bridge, *soundness*
/// after allocation follows from what the allocator proofs already show
/// (nothing new joins the chain, and the allocated object is not on it).
/// *Completeness* needs the converse -- nothing that was on the chain, other
/// than the block the allocation unlinks, falls off it.

module GC.Gen.AllocExact

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Lib.Header

module U64 = FStar.UInt64
module FL = GC.Spec.FreeList
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocChain = GC.Spec.Allocator.Lemmas.Chain
module AllocProps = GC.Gen.AllocProps
module P1 = GC.Spec.Allocator.Lemmas.Part1
module P2 = GC.Spec.Allocator.Lemmas.Part2
module Oom = GC.Spec.Allocator.Oom
module Coalesce = GC.Spec.Coalesce
module CD = GC.Spec.Coalesce.Descending
module CC = GC.Spec.Coalesce.Complete
module SI = GC.Spec.SweepInv
module Corr = GC.Spec.Correctness
module SC = GC.Spec.SweepCoalesce
module SCD = GC.Spec.SweepCoalesce.Defs
module SpecSweep = GC.Spec.Sweep
module Promote = GC.Gen.Promote
module WB = GC.Gen.WriteBodyLemmas
module MH = GC.Gen.MinorHeap
module Fwd = GC.Gen.CheneyPreservation.Forwarding
module PU = GC.Gen.PromoteUpdate
module Cheney = GC.Gen.Cheney
module GenInv = GC.Gen.HeapInvariant

/// ---------------------------------------------------------------------------
/// Bridge: reachable_on_fl <=> the walk meets the address
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let rec on_fl_not_avoids (g: heap) (fp y: U64.t) (n: nat)
  : Lemma (requires FL.on_fl g fp y n)
          (ensures AllocLemmas.chain_avoids g fp y n = false)
          (decreases n)
  = if fp = y then begin
      if AllocLemmas.chain_avoids g fp y n then AllocLemmas.chain_avoids_head_ne g fp y n
    end
    else begin
      hd_address_spec (fp <: obj_addr);
      on_fl_not_avoids g (FL.fl_next g fp) y (n - 1);
      AllocChain.chain_avoids_unfold_step g fp y n
    end

private let rec not_avoids_on_fl (g: heap) (fp y: U64.t) (n: nat)
  : Lemma (requires AllocLemmas.chain_avoids g fp y n = false /\ FL.fl_node y)
          (ensures FL.on_fl g fp y n)
          (decreases n)
  = if n = 0 then AllocChain.chain_avoids_zero g fp y
    else if fp = y then ()
    else if not (FL.fl_node fp) then begin
      if U64.v fp >= U64.v mword && U64.v fp % U64.v mword = 0 && U64.v fp < heap_size
      then hd_address_spec (fp <: obj_addr);
      AllocChain.chain_avoids_terminal g fp y n
    end
    else begin
      hd_address_spec (fp <: obj_addr);
      AllocChain.chain_avoids_unfold_step g fp y n;
      not_avoids_on_fl g (FL.fl_next g fp) y (n - 1)
    end
#pop-options

/// On a terminating chain, being reachable is the same as being met within
/// `heap_words` steps.
let reachable_iff_met (g: heap) (fp y: U64.t)
  : Lemma (requires AllocLemmas.fl_chain_terminates g fp heap_words)
          (ensures FL.reachable_on_fl g fp y <==>
                   (FL.fl_node y /\ AllocLemmas.chain_avoids g fp y heap_words = false))
  = introduce FL.reachable_on_fl g fp y ==>
              (FL.fl_node y /\ AllocLemmas.chain_avoids g fp y heap_words = false)
    with begin
      FL.reachable_is_node g fp y;
      eliminate exists (n: nat). FL.on_fl g fp y n
      with begin
        on_fl_not_avoids g fp y n;
        if AllocLemmas.chain_avoids g fp y heap_words then begin
          if n <= heap_words then AllocChain.chain_avoids_weaken g fp y heap_words n
          else AllocChain.chain_avoids_strengthen g fp y heap_words n
        end
      end
    end;
    introduce (FL.fl_node y /\ AllocLemmas.chain_avoids g fp y heap_words = false) ==>
              FL.reachable_on_fl g fp y
    with not_avoids_on_fl g fp y heap_words

/// A reachable cell of a valid chain is a heap object with room for a link.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let rec on_fl_valid_cell (g: heap) (fp: U64.t) (y: obj_addr) (n: nat)
  : Lemma (requires FL.on_fl g fp (y <: U64.t) n /\ AllocLemmas.fl_valid g fp n)
          (ensures Seq.mem y (objects zero_addr g) /\
                   U64.v (wosize_of_object y g) >= 1)
          (decreases n)
  = hd_address_spec (fp <: obj_addr);
    AllocLemmas.fl_valid_elim g fp n;
    if fp = (y <: U64.t) then ()
    else on_fl_valid_cell g (FL.fl_next g fp) y (n - 1)
#pop-options

let reachable_valid_cell (g: heap) (fp: U64.t) (y: U64.t)
  : Lemma (requires FL.reachable_on_fl g fp y /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words)
          (ensures FL.fl_node y /\
                   (FL.fl_node y ==>
                     (Seq.mem (y <: obj_addr) (objects zero_addr g) /\
                      U64.v (wosize_of_object (y <: obj_addr) g) >= 1)))
  = FL.reachable_is_node g fp y;
    eliminate exists (n: nat). FL.on_fl g fp y n
    with begin
      AllocChain.fl_valid_any_fuel g fp heap_words n;
      on_fl_valid_cell g fp (y <: obj_addr) n
    end

/// ---------------------------------------------------------------------------
/// Meeting an address, step by step
/// ---------------------------------------------------------------------------
///
/// `chain_avoids` only ever transfers in one direction ("still avoided"), so
/// the completeness proof needs its own tools for "still met".  Three are
/// enough: the walk meets an address at an exact first step; that first
/// meeting survives a heap whose links agree on the nodes before it; and two
/// meetings compose across one link.

let meets_at (g: heap) (fp y: U64.t) (n: nat) : bool =
  AllocLemmas.chain_avoids g fp y n && not (AllocLemmas.chain_avoids g fp y (n + 1))

/// If the walk meets `y` within `m` steps, it does so first at some step `n < m`.
let rec first_meeting (g: heap) (fp y: U64.t)
  (m: nat{AllocLemmas.chain_avoids g fp y m = false})
  : GTot (n: nat{n < m /\ meets_at g fp y n}) (decreases m)
  = AllocChain.chain_avoids_zero g fp y;
    if AllocLemmas.chain_avoids g fp y (m - 1) then m - 1
    else first_meeting g fp y (m - 1)

/// A walk that goes on after `fp` must have been at a cell.
private let continues_is_node (g: heap) (fp e: U64.t) (k: nat)
  : Lemma (requires AllocLemmas.chain_avoids g fp e k = false /\ fp <> e)
          (ensures U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                   U64.v fp % U64.v mword = 0 /\
                   U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size /\
                   U64.v fp + U64.v mword <= heap_size)
  = if U64.v fp >= U64.v mword && U64.v fp < heap_size && U64.v fp % U64.v mword = 0
    then begin
      hd_address_spec (fp <: obj_addr);
      if U64.v (hd_address (fp <: obj_addr)) + 16 > heap_size
      then AllocChain.chain_avoids_terminal g fp e k
    end
    else AllocChain.chain_avoids_terminal g fp e k

/// The walk is at `fp` itself after zero steps.
private let meets_here (g: heap) (fp: U64.t) (k: nat)
  : Lemma (requires U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ k > 0)
          (ensures AllocLemmas.chain_avoids g fp fp k = false)
  = if AllocLemmas.chain_avoids g fp fp k then AllocLemmas.chain_avoids_head_ne g fp fp k

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
/// A first meeting survives a heap that agrees on the links of every cell met
/// before it, other than two excluded addresses that the walk has not met by
/// then either.
let rec meeting_transfer (g g': heap) (fp y e1 e2: U64.t) (n: nat)
  : Lemma (requires meets_at g fp y n /\
                    AllocLemmas.chain_avoids g fp e1 n = true /\
                    AllocLemmas.chain_avoids g fp e2 n = true /\
                    AllocLemmas.fl_valid g fp (n + 1) /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                       U64.v (wosize_of_object a g) >= 1 /\
                       (a <: U64.t) <> e1 /\ (a <: U64.t) <> e2 ==>
                       read_word g' a == read_word g a))
          (ensures meets_at g' fp y n)
          (decreases n)
  = AllocChain.chain_avoids_zero g fp y;
    AllocChain.chain_avoids_zero g' fp y;
    if fp = y then begin
      if U64.v fp >= U64.v mword && U64.v fp < heap_size && U64.v fp % U64.v mword = 0 then begin
        if n > 0 then meets_here g fp n;
        meets_here g' fp (n + 1)
      end
      else AllocChain.chain_avoids_terminal g fp y (n + 1)
    end
    else begin
      continues_is_node g fp y (n + 1);
      let o : obj_addr = fp in
      if n = 0 then begin
        AllocChain.chain_avoids_unfold_step g fp y 1;
        AllocChain.chain_avoids_zero g (read_word g o) y
      end
      else begin
        AllocLemmas.chain_avoids_head_ne g fp e1 n;
        AllocLemmas.chain_avoids_head_ne g fp e2 n;
        AllocLemmas.fl_valid_elim g fp (n + 1);
        assert (read_word g' o == read_word g o);
        let nx = read_word g o in
        AllocChain.chain_avoids_unfold_step g fp y n;
        AllocChain.chain_avoids_unfold_step g fp y (n + 1);
        AllocChain.chain_avoids_unfold_step g' fp y n;
        AllocChain.chain_avoids_unfold_step g' fp y (n + 1);
        AllocLemmas.chain_avoids_tail g fp e1 n;
        AllocLemmas.chain_avoids_tail g fp e2 n;
        meeting_transfer g g' nx y e1 e2 (n - 1)
      end
    end

/// Meeting `p` first at step `d`, then following one link from `p`, then
/// meeting `y` within `m` more steps: `y` is met within `d + 1 + m` steps.
let rec meeting_concat (g: heap) (fp p y: U64.t) (d m: nat)
  : Lemma (requires meets_at g fp p d /\
                    U64.v p >= U64.v mword /\ U64.v p < heap_size /\
                    U64.v p % U64.v mword = 0 /\
                    U64.v (hd_address (p <: obj_addr)) + 16 <= heap_size /\
                    AllocLemmas.chain_avoids g (read_word g (p <: obj_addr)) y m = false)
          (ensures AllocLemmas.chain_avoids g fp y (d + 1 + m) = false)
          (decreases d)
  = AllocChain.chain_avoids_zero g fp p;
    if fp = p then begin
      if fp = y then meets_here g fp (d + 1 + m)
      else begin
        if d > 0 then meets_here g fp d;
        AllocChain.chain_avoids_unfold_step g fp y (d + 1 + m);
        if d > 0 then begin
          // a first meeting of p at d > 0 is impossible when fp = p
          ()
        end
      end
    end
    else begin
      continues_is_node g fp p (d + 1);
      if fp = y then meets_here g fp (d + 1 + m)
      else if d = 0 then begin
        AllocChain.chain_avoids_unfold_step g fp p 1;
        AllocChain.chain_avoids_zero g (read_word g (fp <: obj_addr)) p
      end
      else begin
        let nx = read_word g (fp <: obj_addr) in
        AllocChain.chain_avoids_unfold_step g fp p d;
        AllocChain.chain_avoids_unfold_step g fp p (d + 1);
        AllocChain.chain_avoids_unfold_step g fp y (d + 1 + m);
        meeting_concat g nx p y (d - 1) m
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Facts about meetings
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
/// A meeting at step `n` fixes the answer for every other number of steps.
let meets_at_mono (g: heap) (fp y: U64.t) (n m: nat)
  : Lemma (requires meets_at g fp y n)
          (ensures (m <= n ==> AllocLemmas.chain_avoids g fp y m = true) /\
                   (m > n ==> AllocLemmas.chain_avoids g fp y m = false))
  = if m <= n then AllocChain.chain_avoids_weaken g fp y n m
    else if AllocLemmas.chain_avoids g fp y m then AllocChain.chain_avoids_weaken g fp y m (n + 1)

/// Met within `fuel` steps.
let meets_at_within (g: heap) (fp y: U64.t) (n fuel: nat)
  : Lemma (requires meets_at g fp y n /\ n < fuel)
          (ensures AllocLemmas.chain_avoids g fp y fuel = false)
  = meets_at_mono g fp y n fuel

/// Only one address is met first at a given step.
let rec meets_at_unique (g: heap) (fp y z: U64.t) (n: nat)
  : Lemma (requires meets_at g fp y n /\ meets_at g fp z n)
          (ensures y == z)
          (decreases n)
  = AllocChain.chain_avoids_zero g fp y;
    AllocChain.chain_avoids_zero g fp z;
    if fp = y && fp = z then ()
    else if n = 0 then begin
      (if fp <> y then begin
         continues_is_node g fp y 1; AllocChain.chain_avoids_unfold_step g fp y 1;
         AllocChain.chain_avoids_zero g (read_word g (fp <: obj_addr)) y end);
      (if fp <> z then begin
         continues_is_node g fp z 1; AllocChain.chain_avoids_unfold_step g fp z 1;
         AllocChain.chain_avoids_zero g (read_word g (fp <: obj_addr)) z end)
    end
    else begin
      (if fp = y then begin continues_is_node g fp z (n + 1); meets_here g fp n end);
      (if fp = z then begin continues_is_node g fp y (n + 1); meets_here g fp n end);
      continues_is_node g fp y (n + 1);
      let nx = read_word g (fp <: obj_addr) in
      AllocChain.chain_avoids_unfold_step g fp y n;
      AllocChain.chain_avoids_unfold_step g fp y (n + 1);
      AllocChain.chain_avoids_unfold_step g fp z n;
      AllocChain.chain_avoids_unfold_step g fp z (n + 1);
      meets_at_unique g nx y z (n - 1)
    end

/// The node the walk is at after `k` steps is met first at step `k`, provided
/// the walk had not met it before.
let at_depth_meets (g: heap) (fp: U64.t) (k: nat)
  : Lemma (requires AllocChain.walk_chain_valid g fp k /\
                    (let c = AllocChain.walk_chain g fp k in
                     U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword = 0 /\
                     AllocLemmas.chain_avoids g fp c k = true))
          (ensures meets_at g fp (AllocChain.walk_chain g fp k) k)
  = let c = AllocChain.walk_chain g fp k in
    AllocChain.chain_avoids_unfold_steps g fp c k (k + 1);
    meets_here g c 1

/// A meeting further down the walk, seen from `m` steps in.
let meets_at_shift (g: heap) (fp y: U64.t) (n m: nat)
  : Lemma (requires meets_at g fp y n /\ m <= n /\ AllocChain.walk_chain_valid g fp m)
          (ensures meets_at g (AllocChain.walk_chain g fp m) y (n - m))
  = meets_at_mono g fp y n m;
    AllocChain.chain_avoids_unfold_steps g fp y m n;
    AllocChain.chain_avoids_unfold_steps g fp y m (n + 1)
#pop-options

/// ---------------------------------------------------------------------------
/// What one block's allocation writes
/// ---------------------------------------------------------------------------

/// Two distinct heap objects: neither's address is the other's header word,
/// and their link words are a whole word apart.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
private let two_objects_apart (g: heap) (a b: obj_addr)
  : Lemma (requires Seq.mem a (objects zero_addr g) /\ Seq.mem b (objects zero_addr g) /\
                    a <> b /\ U64.v (wosize_of_object a g) >= 1)
          (ensures (U64.v a <> U64.v (hd_address b)) /\
                   (U64.v a + U64.v mword <= U64.v b \/ U64.v b + U64.v mword <= U64.v a) /\
                   (U64.v a + U64.v mword <= U64.v (hd_address b) \/
                    U64.v (hd_address b) + U64.v mword <= U64.v a))
  = hd_address_spec a; hd_address_spec b;
    if U64.v a < U64.v b then objects_separated zero_addr g a b
    else objects_separated zero_addr g b a
#pop-options

/// The allocator's frame, block-local form: allocating from `obj` changes no
/// other object's link word, and at a split not even `obj`'s.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let block_frame (g: heap) (obj: obj_addr) (wz: nat) (next: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\ Seq.mem obj (objects zero_addr g) /\ wz >= 1 /\
                    U64.v (wosize_of_object obj g) >= wz /\
                    Seq.mem a (objects zero_addr g) /\ U64.v (wosize_of_object a g) >= 1 /\
                    (U64.v (wosize_of_object obj g) - wz >= 2 \/ a <> obj))
          (ensures read_word (fst (alloc_from_block g obj wz next)) a == read_word g a)
  = wosize_of_object_spec obj g;
    hd_address_spec a;
    assert (U64.v (hd_address a) + 16 <= heap_size);
    if U64.v (wosize_of_object obj g) - wz >= 1
    then P2.alloc_split_fl_transfer_pre_part1 g obj wz next a
    else P2.alloc_exact_fl_transfer_pre_part1 g obj wz next a
#pop-options

/// The same, after the search has first relinked the predecessor `prev`:
/// the only link words that differ from `g` are `prev`'s, which now holds
/// `new_fp`, and -- at a one-word leftover -- `obj`'s.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let relinked_frame (g: heap) (prev obj: obj_addr) (wz: nat) (next new_fp: U64.t) (a: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\ Seq.mem obj (objects zero_addr g) /\ wz >= 1 /\
                    U64.v (wosize_of_object obj g) >= wz /\
                    Seq.mem prev (objects zero_addr g) /\ U64.v (wosize_of_object prev g) >= 1 /\
                    prev <> obj /\
                    Seq.mem a (objects zero_addr g) /\ U64.v (wosize_of_object a g) >= 1 /\
                    (U64.v (wosize_of_object obj g) - wz >= 2 \/ a <> obj))
          (ensures (let gw = write_word g (prev <: hp_addr) new_fp in
                    let g2 = fst (alloc_from_block gw obj wz next) in
                    well_formed_heap_part1 gw /\
                    objects zero_addr gw == objects zero_addr g /\
                    wosize_of_object obj gw == wosize_of_object obj g /\
                    read_word g2 (prev <: hp_addr) == new_fp /\
                    ((a <: U64.t) <> (prev <: U64.t) ==> read_word g2 a == read_word g a)))
  = let gw = write_word g (prev <: hp_addr) new_fp in
    P1.write_body_preserves_objects_local zero_addr g prev (prev <: hp_addr) new_fp;
    P1.write_body_preserves_wfh_part1 g prev (prev <: hp_addr) new_fp;
    two_objects_apart g prev obj;
    read_write_different g (prev <: hp_addr) (hd_address obj) new_fp;
    wosize_of_object_spec obj g; wosize_of_object_spec obj gw;
    read_write_same g (prev <: hp_addr) new_fp;
    hd_address_spec prev;
    wosize_of_object_spec prev g; wosize_of_object_spec prev gw;
    read_write_different g (prev <: hp_addr) (hd_address prev) new_fp;
    block_frame gw obj wz next prev;
    if (a <: U64.t) <> (prev <: U64.t) then begin
      two_objects_apart g prev a;
      read_write_different g (prev <: hp_addr) (a <: hp_addr) new_fp;
      read_write_different g (prev <: hp_addr) (hd_address a) new_fp;
      wosize_of_object_spec a g; wosize_of_object_spec a gw;
      block_frame gw obj wz next a
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The search keeps everything it did not unlink
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
/// Met within fewer steps is met within more.
let met_more (g: heap) (fp y: U64.t) (m m': nat)
  : Lemma (requires AllocLemmas.chain_avoids g fp y m = false /\ m <= m')
          (ensures AllocLemmas.chain_avoids g fp y m' = false)
  = if AllocLemmas.chain_avoids g fp y m' then AllocChain.chain_avoids_weaken g fp y m' m

/// `meeting_transfer`, packaged with its fuel bookkeeping.
let meets_transfer_within (g g': heap) (fp y e1 e2: U64.t) (n fuel: nat)
  : Lemma (requires meets_at g fp y n /\ n < fuel /\
                    AllocLemmas.chain_avoids g fp e1 n = true /\
                    AllocLemmas.chain_avoids g fp e2 n = true /\
                    AllocLemmas.fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                       U64.v (wosize_of_object a g) >= 1 /\
                       (a <: U64.t) <> e1 /\ (a <: U64.t) <> e2 ==>
                       read_word g' a == read_word g a))
          (ensures meets_at g' fp y n /\ AllocLemmas.chain_avoids g' fp y fuel = false)
  = GC.Spec.Allocator.Lemmas.Common.fl_valid_weaken g fp fuel (n + 1);
    meeting_transfer g g' fp y e1 e2 n;
    meets_at_within g' fp y n fuel
#pop-options

/// The search's view of the chain at the block it allocates from: `cur` is the
/// node at depth `k`, `prev` the one before it (or 0 at the head), and `next`
/// the one after.
let at_block (g: heap) (head prev cur: U64.t) (k: nat) : prop =
  AllocChain.walk_chain_valid g head k /\
  AllocChain.walk_chain g head k == cur /\
  (prev == 0UL ==> k == 0) /\
  (prev <> 0UL ==> k >= 1 /\ AllocChain.walk_chain g head (k - 1) == prev)

/// Where the search stands: `cur` is met first at its own depth `k`, `prev`
/// at `k - 1`, and `next` is the node at depth `k + 1`.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let depth_facts (g: heap) (head prev cur: U64.t) (k: nat)
  : Lemma (requires at_block g head prev cur k /\ k <= heap_words /\
                    AllocLemmas.fl_valid g head heap_words /\
                    AllocLemmas.fl_chain_terminates g head heap_words /\
                    U64.v cur >= U64.v mword /\ U64.v cur < heap_size /\ U64.v cur % U64.v mword = 0 /\
                    U64.v (hd_address (cur <: obj_addr)) + 16 <= heap_size)
          (ensures meets_at g head cur k /\
                   AllocChain.walk_chain_valid g head (k + 1) /\
                   AllocChain.walk_chain g head (k + 1) == read_word g (cur <: obj_addr) /\
                   (prev <> 0UL ==> meets_at g head prev (k - 1)))
  = (if k > 0 then AllocChain.fl_chain_no_early_repeat g head k heap_words
     else AllocChain.chain_avoids_zero g head cur);
    at_depth_meets g head k;
    AllocChain.walk_chain_valid_snoc g head k;
    AllocChain.walk_chain_append g head k 1;
    AllocChain.walk_chain_one_step g cur;
    if prev <> 0UL then begin
      AllocChain.walk_chain_valid_prefix g head k (k - 1);
      AllocChain.walk_chain_valid_at g head k (k - 1);
      (if k - 1 > 0 then AllocChain.fl_chain_no_early_repeat g head (k - 1) heap_words
       else AllocChain.chain_avoids_zero g head prev);
      at_depth_meets g head (k - 1)
    end
#pop-options

/// The two disjuncts that excuse a node from staying on the chain: it is the
/// allocated object, or the one-word fragment the allocation leaves behind.
let unlinked (g': heap) (obj_out: U64.t) (y: obj_addr) : prop =
  (y <: U64.t) == obj_out \/ U64.v (wosize_of_object y g') = 0

/// The search allocates from the head of the list (`prev = 0`).
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let found_head (g: heap) (obj: obj_addr) (wz: nat) (y: obj_addr) (n: nat)
  : Lemma (requires well_formed_heap_part1 g /\ wz >= 1 /\
                    AllocLemmas.fl_valid g obj heap_words /\
                    AllocLemmas.fl_chain_terminates g obj heap_words /\
                    U64.v (wosize_of_object obj g) >= wz /\
                    meets_at g obj (y <: U64.t) n /\ n < heap_words)
          (ensures (let next = read_word g obj in
                    let bwz = U64.v (wosize_of_object obj g) in
                    let g' = fst (alloc_from_block g obj wz next) in
                    let fp' = alloc_replacement_fp g obj wz next in
                    let obj_out = U64.v obj + (bwz - wz) * 8 in
                    AllocLemmas.chain_avoids g' fp' (y <: U64.t) heap_words = false \/
                    U64.v y == obj_out \/ U64.v (wosize_of_object y g') = 0))
  = let hd = hd_address obj in
    hd_address_spec obj;
    AllocLemmas.fl_valid_elim g (obj <: U64.t) heap_words;
    wosize_of_object_spec obj g;
    let bwz = U64.v (wosize_of_object obj g) in
    assert (U64.v hd + 8 + bwz * 8 <= heap_size);
    let next = read_word g obj in
    let g' = fst (alloc_from_block g obj wz next) in
    let lo = bwz - wz in
    // the walk is at obj after 0 steps, at next after 1
    AllocChain.walk_chain_zero g (obj <: U64.t);
    AllocChain.walk_chain_valid_zero g (obj <: U64.t);
    depth_facts g (obj <: U64.t) 0UL (obj <: U64.t) 0;
    if lo >= 2 then begin
      // the chain is unchanged and still starts at obj
      let fr (a: obj_addr) : Lemma
        (requires Seq.mem a (objects zero_addr g) /\ U64.v (wosize_of_object a g) >= 1 /\
                  (a <: U64.t) <> (y <: U64.t))
        (ensures read_word g' a == read_word g a)
        = block_frame g obj wz next a in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
      AllocChain.chain_avoids_zero g (obj <: U64.t) (y <: U64.t);
      meets_at_mono g (obj <: U64.t) (y <: U64.t) n n;
      meets_transfer_within g g' (obj <: U64.t) (y <: U64.t) (y <: U64.t) (y <: U64.t) n heap_words
    end
    else if n = 0 then begin
      // y is obj itself
      meets_at_unique g (obj <: U64.t) (y <: U64.t) (obj <: U64.t) 0;
      if lo = 1 then begin
        P1.alloc_split_facts_part1 g obj wz next;
        wosize_of_object_spec obj g'
      end
    end
    else begin
      // y lies past obj: the new chain is the old one from next
      meets_at_shift g (obj <: U64.t) (y <: U64.t) n 1;
      GC.Spec.Allocator.Lemmas.Common.fl_valid_next g (obj <: U64.t) heap_words;
      AllocChain.fl_chain_predecessor_not_in_suffix_b g (obj <: U64.t) heap_words;
      AllocChain.not_in_fl_chain_b_is_chain_avoids g next (obj <: U64.t) (heap_words - 1);
      AllocChain.chain_avoids_weaken g next (obj <: U64.t) (heap_words - 1) (n - 1);
      GC.Spec.Allocator.Lemmas.Common.fl_valid_weaken g next (heap_words - 1) n;
      let fr (a: obj_addr) : Lemma
        (requires Seq.mem a (objects zero_addr g) /\ U64.v (wosize_of_object a g) >= 1 /\
                  (a <: U64.t) <> (obj <: U64.t))
        (ensures read_word g' a == read_word g a)
        = block_frame g obj wz next a in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
      meets_transfer_within g g' next (y <: U64.t) (obj <: U64.t) (obj <: U64.t) (n - 1) n;
      met_more g' next (y <: U64.t) n heap_words
    end
#pop-options

/// The search allocates from a block past the head, relinking `prev` first.
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let found_rest (g: heap) (head: U64.t) (prev obj: obj_addr) (wz: nat) (fuel: nat) (y: obj_addr) (n: nat)
  : Lemma (requires well_formed_heap_part1 g /\ wz >= 1 /\
                    fuel > 0 /\ fuel < heap_words /\
                    AllocLemmas.fl_valid g obj fuel /\
                    AllocLemmas.fl_chain_terminates g obj fuel /\
                    AllocLemmas.fl_valid g head heap_words /\
                    AllocLemmas.fl_chain_terminates g head heap_words /\
                    U64.v (wosize_of_object obj g) >= wz /\
                    prev <> obj /\
                    Seq.mem prev (objects zero_addr g) /\
                    U64.v (wosize_of_object prev g) >= 1 /\
                    U64.v (hd_address prev) + 16 <= heap_size /\
                    read_word g prev == (obj <: U64.t) /\
                    at_block g head (prev <: U64.t) (obj <: U64.t) (heap_words - fuel) /\
                    meets_at g head (y <: U64.t) n /\ n < heap_words)
          (ensures (let next = read_word g obj in
                    let bwz = U64.v (wosize_of_object obj g) in
                    let new_fp = alloc_replacement_fp g obj wz next in
                    let gw = write_word g (prev <: hp_addr) new_fp in
                    let g2 = fst (alloc_from_block gw obj wz next) in
                    let obj_out = U64.v obj + (bwz - wz) * 8 in
                    AllocLemmas.chain_avoids g2 head (y <: U64.t) heap_words = false \/
                    U64.v y == obj_out \/ U64.v (wosize_of_object y g2) = 0))
  = let k = heap_words - fuel in
    let hd = hd_address obj in
    hd_address_spec obj;
    AllocLemmas.fl_valid_elim g (obj <: U64.t) fuel;
    wosize_of_object_spec obj g;
    let bwz = U64.v (wosize_of_object obj g) in
    assert (U64.v hd + 8 + bwz * 8 <= heap_size);
    let next = read_word g obj in
    let lo = bwz - wz in
    let new_fp = alloc_replacement_fp g obj wz next in
    let gw = write_word g (prev <: hp_addr) new_fp in
    let g2 = fst (alloc_from_block gw obj wz next) in
    depth_facts g head (prev <: U64.t) (obj <: U64.t) k;
    // links: every object but prev (and, at a one-word leftover, obj) keeps
    // its link word; prev's now holds new_fp
    let fr (a: obj_addr) : Lemma
      (requires Seq.mem a (objects zero_addr g) /\ U64.v (wosize_of_object a g) >= 1 /\
                (lo >= 2 \/ a <> obj))
      (ensures read_word g2 (prev <: hp_addr) == new_fp /\
               ((a <: U64.t) <> (prev <: U64.t) ==> read_word g2 a == read_word g a))
      = relinked_frame g prev obj wz next new_fp a in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
    fr prev;
    if lo >= 2 then begin
      // new_fp is obj, which prev already linked to: no link changes at all
      assert (new_fp == (obj <: U64.t));
      AllocChain.chain_avoids_zero g head (y <: U64.t);
      meets_at_mono g head (y <: U64.t) n n;
      meets_transfer_within g g2 head (y <: U64.t) (y <: U64.t) (y <: U64.t) n heap_words
    end
    else if n = k then begin
      meets_at_unique g head (y <: U64.t) (obj <: U64.t) k;
      if lo = 1 then begin
        relinked_frame g prev obj wz next new_fp prev;
        wosize_of_object_spec obj gw;
        P1.alloc_split_facts_part1 gw obj wz next;
        wosize_of_object_spec obj g2
      end
    end
    else if n < k then begin
      // y comes before obj: the walk to it reads no changed link
      meets_at_mono g head (obj <: U64.t) k n;
      meets_at_mono g head (prev <: U64.t) (k - 1) n;
      meets_transfer_within g g2 head (y <: U64.t) (prev <: U64.t) (obj <: U64.t) n heap_words
    end
    else begin
      // y comes after obj: head .. prev, then prev's new link to next, then
      // the old chain from next
      assert (new_fp == next);
      meets_at_shift g head (y <: U64.t) n (k + 1);
      GC.Spec.Allocator.Lemmas.Common.fl_valid_next g (obj <: U64.t) fuel;
      AllocLemmas.fl_chain_terminates_elim g (obj <: U64.t) fuel;
      AllocChain.fl_chain_predecessor_not_in_suffix_b g (obj <: U64.t) fuel;
      AllocChain.not_in_fl_chain_b_is_chain_avoids g next (obj <: U64.t) (fuel - 1);
      AllocChain.chain_avoids_weaken g next (obj <: U64.t) (fuel - 1) (n - k - 1);
      AllocChain.chain_avoids_prev g (prev <: U64.t) (obj <: U64.t) next (fuel - 1);
      AllocChain.chain_avoids_weaken g next (prev <: U64.t) (fuel - 1) (n - k - 1);
      GC.Spec.Allocator.Lemmas.Common.fl_valid_weaken g next (fuel - 1) (n - k);
      meets_transfer_within g g2 next (y <: U64.t) (prev <: U64.t) (obj <: U64.t) (n - k - 1) (n - k);
      // prev is still met first at k - 1 in the new heap
      meets_at_mono g head (obj <: U64.t) k (k - 1);
      GC.Spec.Allocator.Lemmas.Common.fl_valid_weaken g head heap_words k;
      meeting_transfer g g2 head (prev <: U64.t) (prev <: U64.t) (obj <: U64.t) (k - 1);
      meeting_concat g2 head (prev <: U64.t) (y <: U64.t) (k - 1) (n - k);
      met_more g2 head (y <: U64.t) n heap_words
    end
#pop-options

/// The search, step by step: whichever block it allocates from, every node it
/// met on the old chain is still met, unless it is the allocated object or the
/// fragment.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 0"
private let rec search_keeps
  (g: heap) (head prev cur: U64.t) (wz: nat) (fuel: nat) (y: obj_addr) (n: nat)
  : Lemma (requires well_formed_heap_part1 g /\ wz >= 1 /\
                    AllocLemmas.fl_valid g cur fuel /\
                    AllocLemmas.fl_chain_terminates g cur fuel /\
                    AllocLemmas.fl_valid g head heap_words /\
                    AllocLemmas.fl_chain_terminates g head heap_words /\
                    fuel <= heap_words /\
                    (prev <> 0UL ==>
                      (prev <> cur /\
                       U64.v prev >= U64.v mword /\ U64.v prev < heap_size /\
                       U64.v prev % U64.v mword = 0 /\
                       Seq.mem prev (objects zero_addr g) /\
                       U64.v (wosize_of_object (prev <: obj_addr) g) >= 1 /\
                       U64.v (hd_address (prev <: obj_addr)) + 16 <= heap_size /\
                       read_word g (prev <: obj_addr) = cur)) /\
                    at_block g head prev cur (heap_words - fuel) /\
                    meets_at g head (y <: U64.t) n /\ n < heap_words)
          (ensures (let r = alloc_search g head prev cur wz fuel in
                    r.obj_out <> 0UL ==>
                    (AllocLemmas.chain_avoids r.heap_out r.fp_out (y <: U64.t) heap_words = false \/
                     U64.v y == U64.v r.obj_out \/
                     U64.v (wosize_of_object y r.heap_out) = 0)))
          (decreases fuel)
  = if fuel = 0 then ()
    else if U64.v cur < U64.v zero_addr + U64.v mword then ()
    else if U64.v cur >= heap_size then ()
    else if U64.v cur % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = cur in
      let hd = hd_address obj in
      hd_address_spec obj;
      AllocLemmas.fl_valid_elim g cur fuel;
      wosize_of_object_spec obj g;
      let bwz = U64.v (wosize_of_object obj g) in
      assert (U64.v hd + 8 + bwz * 8 <= heap_size);
      assert (U64.v hd + 16 <= heap_size);
      let next = read_word g obj in
      if bwz >= wz then begin
        let lo = bwz - wz in
        let ahn = U64.v hd + lo * 8 in
        if ahn + 8 >= heap_size || ahn >= pow2 64 || ahn % 8 <> 0 then ()
        else begin
          assert (U64.v (U64.add cur (U64.uint_to_t (lo * 8))) == U64.v cur + lo * 8);
          if prev = 0UL then begin
            AllocChain.walk_chain_zero g head;
            assert (cur == head);
            assert (fuel == heap_words);
            found_head g obj wz y n
          end
          else begin
            let p : obj_addr = prev in
            two_objects_apart g p obj;
            assert (U64.v prev <> U64.v hd);
            found_rest g head p obj wz fuel y n
          end
        end
      end
      else begin
        let k = heap_words - fuel in
        depth_facts g head prev cur k;
        GC.Spec.Allocator.Lemmas.Common.fl_valid_next g cur fuel;
        AllocLemmas.fl_chain_terminates_elim g cur fuel;
        assert (at_block g head cur next (heap_words - (fuel - 1)));
        search_keeps g head cur next wz (fuel - 1) y n
      end
    end
#pop-options

/// **Allocation keeps everything on the chain except the block it unlinks.**
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let alloc_spec_keeps (g: heap) (fp: U64.t) (wz: nat) (y: obj_addr)
  : Lemma (requires well_formed_heap_part1 g /\ wz >= 1 /\
                    AllocLemmas.fl_valid g fp heap_words /\
                    AllocLemmas.fl_chain_terminates g fp heap_words /\
                    AllocLemmas.chain_avoids g fp (y <: U64.t) heap_words = false)
          (ensures (let r = alloc_spec g fp wz in
                    r.obj_out <> 0UL ==>
                    (AllocLemmas.chain_avoids r.heap_out r.fp_out (y <: U64.t) heap_words = false \/
                     U64.v y == U64.v r.obj_out \/
                     U64.v (wosize_of_object y r.heap_out) = 0)))
  = let n = first_meeting g fp (y <: U64.t) heap_words in
    AllocChain.walk_chain_zero g fp;
    AllocChain.walk_chain_valid_zero g fp;
    assert (at_block g fp 0UL fp 0);
    search_keeps g fp 0UL fp wz heap_words y n
#pop-options

/// ---------------------------------------------------------------------------
/// Soundness after allocation
/// ---------------------------------------------------------------------------

/// The allocator's entry conditions, as every lemma below assumes them.
let alloc_pre (g: heap) (fp: U64.t) (wz: nat) : prop =
  well_formed_heap_part1 g /\ wz >= 1 /\
  AllocLemmas.fl_valid g fp heap_words /\
  AllocLemmas.fl_chain_terminates g fp heap_words

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let alloc_spec_preserves_fl_sound (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires alloc_pre g fp wz /\ FL.fl_sound g fp /\
                    (alloc_spec g fp wz).obj_out <> 0UL)
          (ensures (let r = alloc_spec g fp wz in FL.fl_sound r.heap_out r.fp_out))
  = let r = alloc_spec g fp wz in
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 g fp wz;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 g fp wz;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 g fp wz;
    AllocLemmas.alloc_spec_only_new_is_obj_out_part1 g fp wz;
    let aux (y: U64.t)
      : Lemma (requires FL.reachable_on_fl r.heap_out r.fp_out y)
              (ensures FL.fl_node y /\
                       (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
                       Seq.mem (y <: obj_addr) (objects zero_addr r.heap_out) /\
                       is_blue (y <: obj_addr) r.heap_out /\
                       U64.v (wosize_of_object (y <: obj_addr) r.heap_out) >= 1)
      = reachable_valid_cell r.heap_out r.fp_out y;
        reachable_iff_met r.heap_out r.fp_out y;
        let yo : obj_addr = y in
        // y is not the allocated object, which the new chain avoids ...
        assert (y <> r.obj_out);
        // ... so it was already an object ...
        assert (Seq.mem yo (objects zero_addr g));
        // ... and it was on the old chain: anything off it stays off it.
        if AllocLemmas.chain_avoids g fp y heap_words then
          AllocLemmas.alloc_spec_preserves_chain_avoids_other g fp wz y;
        reachable_iff_met g fp y;
        // So it was blue, and it is not the allocated object, so it still is.
        AllocProps.alloc_spec_preserves_blue_part1 g fp wz yo
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Completeness after allocation
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let alloc_spec_preserves_fl_complete (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires alloc_pre g fp wz /\ FL.fl_complete g fp /\
                    (alloc_spec g fp wz).obj_out <> 0UL)
          (ensures (let r = alloc_spec g fp wz in FL.fl_complete r.heap_out r.fp_out))
  = let r = alloc_spec g fp wz in
    AllocLemmas.alloc_spec_preserves_wfh_part1 g fp wz;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 g fp wz;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 g fp wz;
    AllocLemmas.alloc_spec_only_new_is_obj_out_part1 g fp wz;
    AllocProps.alloc_spec_obj_not_blue_part1 g fp wz;
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr r.heap_out) /\ is_blue x r.heap_out /\
                        U64.v (wosize_of_object x r.heap_out) >= 1)
              (ensures FL.reachable_on_fl r.heap_out r.fp_out x)
      = // x is not the allocated object, which is white ...
        is_blue_iff x r.heap_out;
        assert ((x <: U64.t) <> r.obj_out);
        // ... so it was already an object.
        assert (Seq.mem x (objects zero_addr g));
        // It was on the old chain: had it not been, its header would be
        // unchanged, so it would have been a blue cell, which fl_complete puts
        // on the chain.
        if AllocLemmas.chain_avoids g fp (x <: U64.t) heap_words then begin
          AllocProps.alloc_spec_read_header_other_part1 g fp wz x;
          color_of_object_spec x g; color_of_object_spec x r.heap_out;
          wosize_of_object_spec x g; wosize_of_object_spec x r.heap_out;
          is_blue_iff x g;
          FL.fl_complete_elim g fp x;
          reachable_iff_met g fp (x <: U64.t)
        end;
        // So it is still on the new one.
        alloc_spec_keeps g fp wz x;
        hd_address_spec x;
        assert (U64.v (hd_address x) + 8 + U64.v (wosize_of_object x r.heap_out) * 8 <= heap_size);
        reachable_iff_met r.heap_out r.fp_out (x <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// **Allocation keeps the free list exact.**
let alloc_spec_preserves_fl_exact (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires alloc_pre g fp wz /\ FL.fl_exact g fp /\
                    (alloc_spec g fp wz).obj_out <> 0UL)
          (ensures (let r = alloc_spec g fp wz in FL.fl_exact r.heap_out r.fp_out))
  = alloc_spec_preserves_fl_sound g fp wz;
    alloc_spec_preserves_fl_complete g fp wz

/// ---------------------------------------------------------------------------
/// The first attempt succeeds
/// ---------------------------------------------------------------------------

/// What every allocation needs of the heap, and keeps: the allocator's entry
/// conditions and an exact free list.
let alloc_entry (g: heap) (fp: U64.t) : prop =
  well_formed_heap_part1 g /\
  AllocLemmas.fl_valid g fp heap_words /\
  AllocLemmas.fl_chain_terminates g fp heap_words /\
  FL.fl_exact g fp

/// With an exact free list, an allocation succeeds whenever some free block
/// is big enough.
let alloc_spec_fits_succeeds (g: heap) (fp: U64.t) (wz: nat) (x: obj_addr)
  : Lemma (requires alloc_entry g fp /\ wz >= 1 /\
                    Seq.mem x (objects zero_addr g) /\ is_blue x g /\
                    U64.v (wosize_of_object x g) >= wz)
          (ensures (alloc_spec g fp wz).obj_out <> 0UL)
  = if (alloc_spec g fp wz).obj_out = 0UL then Oom.alloc_spec_oom_no_fit g fp wz

/// Every allocation, successful or not, keeps the entry conditions.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let alloc_spec_preserves_entry (g: heap) (fp: U64.t) (wz: nat)
  : Lemma (requires alloc_entry g fp /\ wz >= 1)
          (ensures (let r = alloc_spec g fp wz in alloc_entry r.heap_out r.fp_out))
  = let r = alloc_spec g fp wz in
    if r.obj_out = 0UL then AllocProps.alloc_spec_oom_unchanged g fp wz
    else begin
      AllocLemmas.alloc_spec_preserves_wfh_part1 g fp wz;
      AllocLemmas.alloc_spec_preserves_fl_valid_part1 g fp wz;
      AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 g fp wz;
      alloc_spec_preserves_fl_exact g fp wz
    end
#pop-options

/// A run of allocations, each of at least one word.
let rec allocs (g: heap) (fp: U64.t) (ws: list pos) : GTot (heap & U64.t) (decreases ws) =
  match ws with
  | [] -> (g, fp)
  | w :: rest -> let r = alloc_spec g fp w in allocs r.heap_out r.fp_out rest

let rec allocs_preserve_entry (g: heap) (fp: U64.t) (ws: list pos)
  : Lemma (requires alloc_entry g fp)
          (ensures (let r = allocs g fp ws in alloc_entry (fst r) (snd r)))
          (decreases ws)
  = match ws with
    | [] -> ()
    | w :: rest ->
      alloc_spec_preserves_entry g fp w;
      let r = alloc_spec g fp w in
      allocs_preserve_entry r.heap_out r.fp_out rest

/// A full collection establishes the entry conditions.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let fused_entry (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      Corr.mark_post h_init h_mark roots fp /\
      well_formed_heap h_mark /\
      SI.heap_objects_dense h_mark /\
      SpecSweep.fp_in_heap fp h_mark /\
      (forall (x: obj_addr). Seq.mem x (objects zero_addr h_mark) ==> ~(is_gray x h_mark)))
    (ensures (let r = SCD.fused_sweep_coalesce h_mark in alloc_entry (fst r) (snd r)))
  = SC.fused_eq_sweep_coalesce h_mark fp;
    Corr.sweep_post_sweep_strong_gen h_init h_mark roots fp;
    let gs = fst (SpecSweep.sweep h_mark fp) in
    Coalesce.coalesce_preserves_wf gs;
    wf_parts ();
    CD.coalesce_fl_entry gs;
    CC.fused_exact h_init h_mark roots fp
#pop-options

/// **After a full collection, and after any run of allocations that follows
/// it, an allocation succeeds whenever some free block is big enough.**
///
/// This is the allocator's side of "the first attempt succeeds": the runtime's
/// retry after a collection is needed only when no single free block fits.
let first_attempt_succeeds
  (h_init h_mark: heap) (roots: seq obj_addr) (fp: U64.t) (ws: list pos) (wz: nat) (x: obj_addr)
  : Lemma
    (requires
      Corr.mark_post h_init h_mark roots fp /\
      well_formed_heap h_mark /\
      SI.heap_objects_dense h_mark /\
      SpecSweep.fp_in_heap fp h_mark /\
      (forall (y: obj_addr). Seq.mem y (objects zero_addr h_mark) ==> ~(is_gray y h_mark)) /\
      wz >= 1 /\
      (let c = SCD.fused_sweep_coalesce h_mark in
       let r = allocs (fst c) (snd c) ws in
       Seq.mem x (objects zero_addr (fst r)) /\ is_blue x (fst r) /\
       U64.v (wosize_of_object x (fst r)) >= wz))
    (ensures (let c = SCD.fused_sweep_coalesce h_mark in
              let r = allocs (fst c) (snd c) ws in
              (alloc_spec (fst r) (snd r) wz).obj_out <> 0UL))
  = let c = SCD.fused_sweep_coalesce h_mark in
    fused_entry h_init h_mark roots fp;
    allocs_preserve_entry (fst c) (snd c) ws;
    let r = allocs (fst c) (snd c) ws in
    alloc_spec_fits_succeeds (fst r) (snd r) wz x

/// ---------------------------------------------------------------------------
/// Promotion keeps the free list complete
/// ---------------------------------------------------------------------------

/// Promotion writes only inside the promoted object's block: its fields, its
/// padding (none, now that allocation is exact) and its header.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
let promote_writes_frame (minor: MH.minor_state) (g1: heap) (obj: U64.t)
  (dst: obj_addr) (wosize: nat{wosize > 0}) (tag: nat{tag < 256}) (w: hp_addr)
  : Lemma (requires U64.v (wosize_of_object dst g1) == wosize /\
                    U64.v dst + wosize * 8 <= heap_size /\
                    (U64.v w + 8 <= U64.v (hd_address dst) \/ U64.v dst + wosize * 8 <= U64.v w))
          (ensures (let copied = WB.copy_fields minor g1 obj dst 0 wosize in
                    let padded = Promote.zero_promote_padding copied dst wosize in
                    read_word (Promote.set_promoted_tag padded dst tag) w == read_word g1 w))
  = hd_address_spec dst;
    let copied = WB.copy_fields minor g1 obj dst 0 wosize in
    WB.copy_fields_preserves_other minor g1 obj (dst <: U64.t) 0 wosize w;
    WB.copy_fields_preserves_other minor g1 obj (dst <: U64.t) 0 wosize (hd_address dst);
    wosize_of_object_spec dst g1; wosize_of_object_spec dst copied;
    assert (Promote.zero_promote_padding copied dst wosize == copied);
    Promote.set_promoted_tag_read_frame copied dst tag w
#pop-options

/// **One promotion keeps the free list complete.**
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let promote_object_preserves_fl_complete (minor: MH.minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    FL.fl_complete major fp /\ wosize < pow2 54 /\
                    (Promote.promote_object minor major obj fp wosize).new_addr <> 0UL)
          (ensures (let res = Promote.promote_object minor major obj fp wosize in
                    FL.fl_complete res.Promote.major_out res.Promote.fp_out))
  = let ar = alloc_spec major fp wosize in
    let g1 = ar.heap_out in
    let fp1 = ar.fp_out in
    let res = Promote.promote_object minor major obj fp wosize in
    Promote.promote_object_success minor major obj fp wosize;
    AllocProps.alloc_spec_obj_wosize_exact_part1 major fp wosize;
    let dst : obj_addr = ar.obj_out in
    MH.minor_tag_bound minor obj;
    let tag = MH.minor_tag minor obj in
    // the allocation alone keeps the list complete (stage 4) ...
    alloc_spec_preserves_fl_complete major fp wosize;
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wosize;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
    AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    // ... and the writes that follow stay inside the promoted object
    Promote.promote_object_preserves_alloc_invariants minor major obj fp wosize;
    Fwd.promote_object_new_addr_in_objects_not_blue minor major obj fp wosize;
    let copied = WB.copy_fields minor g1 obj dst 0 wosize in
    WB.copy_fields_preserves_objects_aux minor g1 obj dst 0 wosize;
    wosize_of_object_spec dst g1;
    hd_address_spec dst;
    assert (U64.v (hd_address dst) + 8 + wosize * 8 <= heap_size);
    WB.copy_fields_preserves_other minor g1 obj (dst <: U64.t) 0 wosize (hd_address dst);
    wosize_of_object_spec dst copied;
    assert (Promote.zero_promote_padding copied dst wosize == copied);
    Promote.set_promoted_tag_preserves_objects copied dst tag;
    assert (objects zero_addr res.Promote.major_out == objects zero_addr g1);
    let fr (a: obj_addr) : Lemma
      (requires Seq.mem a (objects zero_addr g1) /\ (a <: U64.t) <> (dst <: U64.t))
      (ensures (U64.v (wosize_of_object a g1) >= 1 ==>
                  read_word res.Promote.major_out a == read_word g1 a) /\
               read_word res.Promote.major_out (hd_address a) == read_word g1 (hd_address a))
      = hd_address_spec a;
        wosize_of_object_spec a g1;
        (if U64.v a < U64.v dst then objects_separated zero_addr g1 a dst
         else objects_separated zero_addr g1 dst a);
        (if U64.v (wosize_of_object a g1) >= 1
         then promote_writes_frame minor g1 obj dst wosize tag (a <: hp_addr));
        promote_writes_frame minor g1 obj dst wosize tag (hd_address a)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fr);
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr res.Promote.major_out) /\
                        is_blue x res.Promote.major_out /\
                        U64.v (wosize_of_object x res.Promote.major_out) >= 1)
              (ensures FL.reachable_on_fl res.Promote.major_out res.Promote.fp_out x)
      = assert ((x <: U64.t) <> (dst <: U64.t));
        fr x;
        color_of_object_spec x g1; color_of_object_spec x res.Promote.major_out;
        is_blue_iff x g1; is_blue_iff x res.Promote.major_out;
        wosize_of_object_spec x g1; wosize_of_object_spec x res.Promote.major_out;
        FL.fl_complete_elim g1 fp1 x;
        reachable_iff_met g1 fp1 (x <: U64.t);
        let n = first_meeting g1 fp1 (x <: U64.t) heap_words in
        AllocChain.chain_avoids_weaken g1 fp1 (dst <: U64.t) heap_words n;
        meets_transfer_within g1 res.Promote.major_out fp1 (x <: U64.t)
          (dst <: U64.t) (dst <: U64.t) n heap_words;
        hd_address_spec x;
        reachable_iff_met res.Promote.major_out res.Promote.fp_out (x <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Pointer updates keep the free list complete
/// ---------------------------------------------------------------------------

/// `meeting_transfer` for a heap that agrees only on the links of *blue*
/// cells -- enough when every cell the walk meets is blue.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let rec meeting_transfer_blue (g g': heap) (fp y: U64.t) (n: nat)
  : Lemma (requires meets_at g fp y n /\
                    AllocLemmas.fl_valid g fp (n + 1) /\
                    (forall (o: obj_addr). Seq.mem o (objects zero_addr g) /\ is_blue o g = false ==>
                       AllocLemmas.chain_avoids g fp (o <: U64.t) (n + 1) = true) /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\ is_blue a g /\
                       U64.v (wosize_of_object a g) >= 1 ==>
                       read_word g' a == read_word g a))
          (ensures meets_at g' fp y n)
          (decreases n)
  = AllocChain.chain_avoids_zero g fp y;
    AllocChain.chain_avoids_zero g' fp y;
    if fp = y then begin
      if U64.v fp >= U64.v mword && U64.v fp < heap_size && U64.v fp % U64.v mword = 0 then begin
        if n > 0 then meets_here g fp n;
        meets_here g' fp (n + 1)
      end
      else AllocChain.chain_avoids_terminal g fp y (n + 1)
    end
    else begin
      continues_is_node g fp y (n + 1);
      let o : obj_addr = fp in
      if n = 0 then begin
        AllocChain.chain_avoids_unfold_step g fp y 1;
        AllocChain.chain_avoids_zero g (read_word g o) y
      end
      else begin
        AllocLemmas.fl_valid_elim g fp (n + 1);
        // fp is on the chain, so it is blue
        (if is_blue o g = false then meets_here g fp (n + 1));
        assert (read_word g' o == read_word g o);
        let nx = read_word g o in
        AllocChain.chain_avoids_unfold_step g fp y n;
        AllocChain.chain_avoids_unfold_step g fp y (n + 1);
        AllocChain.chain_avoids_unfold_step g' fp y n;
        AllocChain.chain_avoids_unfold_step g' fp y (n + 1);
        let tl (q: obj_addr) : Lemma
          (requires Seq.mem q (objects zero_addr g) /\ is_blue q g = false)
          (ensures AllocLemmas.chain_avoids g nx (q <: U64.t) n = true)
          = AllocLemmas.chain_avoids_tail g fp (q <: U64.t) (n + 1) in
        FStar.Classical.forall_intro (FStar.Classical.move_requires tl);
        meeting_transfer_blue g g' nx y (n - 1)
      end
    end
#pop-options

/// **Pointer updates keep the free list complete**: they rewrite fields of
/// live objects only, never a header and never a field of a blue block.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let update_major_pointers_preserves_fl_complete (major: heap) (fwd: Promote.forwarding_map) (fp: U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words /\
                    Promote.chain_objects_blue major fp /\
                    FL.fl_complete major fp)
          (ensures FL.fl_complete (Promote.update_major_pointers major fwd) fp)
  = let m' = Promote.update_major_pointers major fwd in
    PU.update_major_pointers_preserves_objects major fwd;
    Cheney.update_major_pointers_preserves_fl_valid major fwd fp;
    reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue major fp);
    let bf (a: obj_addr) : Lemma
      (requires Seq.mem a (objects zero_addr major) /\ is_blue a major /\
                U64.v (wosize_of_object a major) >= 1)
      (ensures read_word m' a == read_word major a)
      = hd_address_spec a;
        PU.update_major_pointers_preserves_blue_field major fwd a 0 in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bf);
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr m') /\ is_blue x m' /\
                        U64.v (wosize_of_object x m') >= 1)
              (ensures FL.reachable_on_fl m' fp x)
      = PU.update_major_pointers_preserves_header major fwd x;
        color_of_object_spec x major; color_of_object_spec x m';
        is_blue_iff x major; is_blue_iff x m';
        wosize_of_object_spec x major; wosize_of_object_spec x m';
        FL.fl_complete_elim major fp x;
        reachable_iff_met major fp (x <: U64.t);
        let n = first_meeting major fp (x <: U64.t) heap_words in
        GC.Spec.Allocator.Lemmas.Common.fl_valid_weaken major fp heap_words (n + 1);
        let av (o: obj_addr) : Lemma
          (requires Seq.mem o (objects zero_addr major) /\ is_blue o major = false)
          (ensures AllocLemmas.chain_avoids major fp (o <: U64.t) (n + 1) = true)
          = AllocChain.chain_avoids_weaken major fp (o <: U64.t) heap_words (n + 1) in
        FStar.Classical.forall_intro (FStar.Classical.move_requires av);
        meeting_transfer_blue major m' fp (x <: U64.t) n;
        meets_at_within m' fp (x <: U64.t) n heap_words;
        hd_address_spec x;
        reachable_iff_met m' fp (x <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// The program's field writes keep the entry conditions
/// ---------------------------------------------------------------------------

/// A word inside a non-blue object's body is no object's header and no free
/// cell's link word.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
private let body_word_apart (g: heap) (a b: obj_addr) (w: hp_addr)
  : Lemma (requires well_formed_heap_part1 g /\
                    Seq.mem a (objects zero_addr g) /\ Seq.mem b (objects zero_addr g) /\
                    U64.v w >= U64.v a /\
                    U64.v w < U64.v a + U64.v (wosize_of_object a g) * 8)
          (ensures (U64.v (hd_address b) + 8 <= U64.v w \/ U64.v w + 8 <= U64.v (hd_address b)) /\
                   ((b <> a /\ U64.v (wosize_of_object b g) >= 1) ==>
                     (U64.v b + 8 <= U64.v w \/ U64.v w + 8 <= U64.v b)))
  = hd_address_spec a; hd_address_spec b;
    if U64.v b < U64.v a then objects_separated zero_addr g b a
    else if U64.v a < U64.v b then objects_separated zero_addr g a b
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
/// **A write to a field of a live (non-blue) object keeps the free list
/// exact**, and the allocator's other entry conditions with it.
let field_write_preserves_entry (g: heap) (fp: U64.t) (a: obj_addr) (w: hp_addr) (v: U64.t)
  : Lemma (requires alloc_entry g fp /\
                    Seq.mem a (objects zero_addr g) /\ is_blue a g = false /\
                    U64.v w >= U64.v a /\
                    U64.v w < U64.v a + U64.v (wosize_of_object a g) * 8)
          (ensures alloc_entry (write_word g w v) fp)
  = let g' = write_word g w v in
    P1.write_body_preserves_objects_local zero_addr g a w v;
    P1.write_body_preserves_wfh_part1 g a w v;
    let hdr (b: obj_addr) : Lemma
      (requires Seq.mem b (objects zero_addr g))
      (ensures read_word g' (hd_address b) == read_word g (hd_address b) /\
               ((b <> a /\ U64.v (wosize_of_object b g) >= 1) ==> read_word g' b == read_word g b))
      = body_word_apart g a b w;
        read_write_different g w (hd_address b) v;
        if b <> a && U64.v (wosize_of_object b g) >= 1
        then read_write_different g w (b <: hp_addr) v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires hdr);
    let same_sz (b: obj_addr) : Lemma
      (requires Seq.mem b (objects zero_addr g))
      (ensures wosize_of_object b g' == wosize_of_object b g /\ is_blue b g' == is_blue b g)
      = hdr b;
        wosize_of_object_spec b g; wosize_of_object_spec b g';
        color_of_object_spec b g; color_of_object_spec b g';
        is_blue_iff b g; is_blue_iff b g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires same_sz);
    // a is not on the chain: it is not blue, and every cell is
    hd_address_spec a;
    (if not (AllocLemmas.chain_avoids g fp (a <: U64.t) heap_words) then
       reachable_iff_met g fp (a <: U64.t));
    assert (AllocLemmas.chain_avoids g fp (a <: U64.t) heap_words = true);
    AllocChain.fl_valid_transfer_excl g g' fp (a <: U64.t) heap_words;
    AllocChain.fl_chain_terminates_transfer_excl g g' fp (a <: U64.t) heap_words;
    // soundness: anything on the new chain was on the old one
    let snd (y: U64.t) : Lemma
      (requires FL.reachable_on_fl g' fp y)
      (ensures FL.fl_node y /\
               (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
               Seq.mem (y <: obj_addr) (objects zero_addr g') /\
               is_blue (y <: obj_addr) g' /\
               U64.v (wosize_of_object (y <: obj_addr) g') >= 1)
      = FL.reachable_is_node g' fp y;
        reachable_iff_met g' fp y;
        (if AllocLemmas.chain_avoids g fp y heap_words then
           AllocChain.chain_avoids_transfer_excl2 g g' fp y (a <: U64.t) heap_words);
        reachable_iff_met g fp y;
        same_sz (y <: obj_addr)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires snd);
    // completeness: every blue cell is still met
    let cmp (x: obj_addr) : Lemma
      (requires Seq.mem x (objects zero_addr g') /\ is_blue x g' /\
                U64.v (wosize_of_object x g') >= 1)
      (ensures FL.reachable_on_fl g' fp x)
      = same_sz x;
        FL.fl_complete_elim g fp x;
        reachable_iff_met g fp (x <: U64.t);
        let n = first_meeting g fp (x <: U64.t) heap_words in
        AllocChain.chain_avoids_weaken g fp (a <: U64.t) heap_words n;
        meets_transfer_within g g' fp (x <: U64.t) (a <: U64.t) (a <: U64.t) n heap_words;
        hd_address_spec x;
        reachable_iff_met g' fp (x <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires cmp)
#pop-options

/// ---------------------------------------------------------------------------
/// The first attempt succeeds, from any heap the collector hands back
/// ---------------------------------------------------------------------------

/// The collector's invariant gives the allocator's entry conditions.  `fl_sound`
/// is not a separate conjunct of `major_heap_shape`: it follows from `fl_valid`
/// (every cell is an object with room for a link) and `chain_objects_blue`
/// (every cell is blue).
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let major_heap_shape_gives_entry (major: heap) (fp: U64.t)
  : Lemma (requires GenInv.major_heap_shape major fp)
          (ensures alloc_entry major fp)
  = GenInv.major_heap_shape_elim major fp;
    wf_parts ();
    reveal_opaque (`%Promote.chain_objects_blue) (Promote.chain_objects_blue major fp);
    let snd (y: U64.t) : Lemma
      (requires FL.reachable_on_fl major fp y)
      (ensures FL.fl_node y /\
               (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
               Seq.mem (y <: obj_addr) (objects zero_addr major) /\
               is_blue (y <: obj_addr) major /\
               U64.v (wosize_of_object (y <: obj_addr) major) >= 1)
      = reachable_valid_cell major fp y;
        reachable_iff_met major fp y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires snd)
#pop-options

/// What the program may do to the major heap between collections: allocate,
/// or write a field of a live object.
noeq type event =
  | EAlloc : wz:pos -> event
  | EWrite : a:obj_addr -> w:hp_addr -> v:U64.t -> event

/// A write is only to a field of a live (non-blue) object -- the runtime's side
/// of the contract; allocation is always allowed.
let event_ok (g: heap) (e: event) : prop =
  match e with
  | EAlloc _ -> True
  | EWrite a w _ ->
    Seq.mem a (objects zero_addr g) /\ is_blue a g = false /\
    U64.v w >= U64.v a /\ U64.v w < U64.v a + U64.v (wosize_of_object a g) * 8

let step (g: heap) (fp: U64.t) (e: event) : GTot (heap & U64.t) =
  match e with
  | EAlloc wz -> let r = alloc_spec g fp wz in (r.heap_out, r.fp_out)
  | EWrite _ w v -> (write_word g w v, fp)

let rec run (g: heap) (fp: U64.t) (es: list event) : GTot (heap & U64.t) (decreases es) =
  match es with
  | [] -> (g, fp)
  | e :: rest -> let s = step g fp e in run (fst s) (snd s) rest

let rec run_ok (g: heap) (fp: U64.t) (es: list event) : Tot prop (decreases es) =
  match es with
  | [] -> True
  | e :: rest -> event_ok g e /\ (let s = step g fp e in run_ok (fst s) (snd s) rest)

let rec run_preserves_entry (g: heap) (fp: U64.t) (es: list event)
  : Lemma (requires alloc_entry g fp /\ run_ok g fp es)
          (ensures (let r = run g fp es in alloc_entry (fst r) (snd r)))
          (decreases es)
  = match es with
    | [] -> ()
    | e :: rest ->
      (match e with
       | EAlloc wz -> alloc_spec_preserves_entry g fp wz
       | EWrite a w v -> field_write_preserves_entry g fp a w v);
      let s = step g fp e in
      run_preserves_entry (fst s) (snd s) rest

/// **From any heap the collector hands back, and after any run of allocations
/// and field writes to live objects, an allocation succeeds whenever some free
/// block is big enough.**
///
/// `collection_heap_shape` is what `GC.Gen.Impl.gen_gc` and
/// `minor_collect_full` establish of the heap they return, so this covers the
/// runtime between collections: the second, post-collection attempt in
/// `verified_allocate` is needed only when no single free block fits.
let first_attempt_succeeds_between_collections
  (minor: MH.minor_state) (major: heap) (fp: U64.t) (es: list event) (wz: nat) (x: obj_addr)
  : Lemma (requires GenInv.collection_heap_shape minor major fp /\
                    run_ok major fp es /\ wz >= 1 /\
                    (let r = run major fp es in
                     Seq.mem x (objects zero_addr (fst r)) /\ is_blue x (fst r) /\
                     U64.v (wosize_of_object x (fst r)) >= wz))
          (ensures (let r = run major fp es in (alloc_spec (fst r) (snd r) wz).obj_out <> 0UL))
  = GenInv.collection_heap_shape_elim minor major fp;
    major_heap_shape_gives_entry major fp;
    run_preserves_entry major fp es;
    let r = run major fp es in
    alloc_spec_fits_succeeds (fst r) (snd r) wz x

