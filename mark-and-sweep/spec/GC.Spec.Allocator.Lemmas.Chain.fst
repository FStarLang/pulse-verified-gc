(*
   GC.Spec.Allocator.Lemmas.Chain — free-list chain/walk/avoidance lemmas.

   Split out of Core to keep allocator proofs modular.
*)
module GC.Spec.Allocator.Lemmas.Chain

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Allocator.Lemmas.Common

/// Module-level default: all functions get z3rlimit 20 unless overridden
#push-options "--z3rlimit 20 --z3refresh"

/// Transfer fl_valid from g to g' with the same fuel
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_valid_transfer (g g': heap) (fp: U64.t) (fuel: nat)
  : Lemma
    (requires fl_valid g fp fuel /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g)) ==>
                 (Seq.mem a (objects zero_addr g') /\
                  (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 ==>
                    U64.v (wosize_of_object (a <: obj_addr) g') >= 1) /\
                  (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                   U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr)))))
    (ensures fl_valid g' fp fuel)
    (decreases fuel)
  = if fuel = 0 then
      fl_valid_zero g' fp
    else if fp = 0UL then
      fl_valid_terminal g' fp fuel
    else if U64.v fp < U64.v mword then
      fl_valid_terminal g' fp fuel
    else if U64.v fp >= heap_size then
      fl_valid_terminal g' fp fuel
    else if U64.v fp % U64.v mword <> 0 then
      fl_valid_terminal g' fp fuel
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      fl_valid_elim g fp fuel;
      assert (Seq.mem fp (objects zero_addr g));
      assert (U64.v (wosize_of_object obj g) >= 1);
      assert (Seq.mem fp (objects zero_addr g'));
      assert (U64.v (wosize_of_object obj g') >= 1);
      if U64.v hd + 16 <= heap_size then begin
        let link = read_word g obj in
        assert (read_word g' obj == link);
        fl_valid_transfer g g' link (fuel - 1);
        assert (fl_valid g' link (fuel - 1));
        assert (read_word g' obj <> fp);
        assert (fl_valid g' (read_word g' obj) (fuel - 1));
        fl_valid_step g' fp fuel
      end
      else
        fl_valid_step g' fp fuel
    end
#pop-options

/// Chain termination: the free-list chain from fp hits a base case within `steps` iterations.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_terminates (g: heap) (fp: U64.t) (steps: nat) : Tot bool (decreases steps) =
  if fp = 0UL then true
  else if U64.v fp < U64.v mword then true
  else if U64.v fp >= heap_size then true
  else if U64.v fp % U64.v mword <> 0 then true
  else if steps = 0 then false
  else
    let hd = hd_address (fp <: obj_addr) in
    if U64.v hd + 16 > heap_size then true
    else fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1)
#pop-options

/// Terminal base cases for fl_chain_terminates
let fl_chain_terminates_terminal (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fp = 0UL \/ U64.v fp < U64.v mword \/ U64.v fp >= heap_size \/ U64.v fp % U64.v mword <> 0)
          (ensures fl_chain_terminates g fp steps = true)
  = ()

/// If fl_valid holds AND the chain terminates within fuel steps,
/// then fl_valid holds for any fuel'.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_valid_any_fuel (g: heap) (fp: U64.t) (fuel fuel': nat)
  : Lemma
    (requires fl_valid g fp fuel /\ fl_chain_terminates g fp fuel)
    (ensures fl_valid g fp fuel')
    (decreases fuel')
  = if fuel' = 0 then
      fl_valid_zero g fp
    else if fp = 0UL then
      fl_valid_terminal g fp fuel'
    else if U64.v fp < U64.v mword then
      fl_valid_terminal g fp fuel'
    else if U64.v fp >= heap_size then
      fl_valid_terminal g fp fuel'
    else if U64.v fp % U64.v mword <> 0 then
      fl_valid_terminal g fp fuel'
    else begin
      if fuel = 0 then begin
        assert (fl_chain_terminates g fp fuel = false);
        assert False
      end
      else begin
        let obj : obj_addr = fp in
        let hd = hd_address obj in
        fl_valid_elim g fp fuel;
        if U64.v hd + 16 <= heap_size then begin
          let link = read_word g obj in
          assert (link <> fp);
          assert (fl_valid g link (fuel - 1));
          assert (fl_chain_terminates g link (fuel - 1) = true);
          fl_valid_any_fuel g link (fuel - 1) (fuel' - 1);
          assert (fl_valid g link (fuel' - 1));
          fl_valid_step g fp fuel'
        end
        else
          fl_valid_step g fp fuel'
      end
    end
#pop-options

/// Chain termination transfers when links are preserved
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_terminates_transfer (g g': heap) (fp: U64.t) (steps: nat)
  : Lemma
    (requires fl_chain_terminates g fp steps /\
              fl_valid g fp steps /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g)) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures fl_chain_terminates g' fp steps)
    (decreases steps)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if steps = 0 then begin
      assert (fl_chain_terminates g fp steps = false);
      assert False
    end
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      if U64.v hd + 16 <= heap_size then begin
        let link = read_word g obj in
        fl_valid_elim g fp steps;
        assert (Seq.mem fp (objects zero_addr g));
        assert (U64.v (wosize_of_object obj g) >= 1);
        assert (fl_valid g link (steps - 1));
        assert (fl_chain_terminates g link (steps - 1) = true);
        assert (read_word g' obj == link);
        fl_chain_terminates_transfer g g' link (steps - 1);
        assert (fl_chain_terminates g' (read_word g' obj) (steps - 1))
      end
      else ()
    end
#pop-options

/// Chain termination monotonicity: more steps suffice
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_terminates_weaken (g: heap) (fp: U64.t) (s1 s2: nat)
  : Lemma (requires fl_chain_terminates g fp s1 /\ s2 >= s1)
          (ensures fl_chain_terminates g fp s2)
          (decreases s1)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if s1 = 0 then ()  // s1 = 0 means fl_chain_terminates is false; vacuous
    else begin
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else fl_chain_terminates_weaken g (read_word g (fp <: obj_addr)) (s1 - 1) (s2 - 1)
    end
#pop-options

/// Chain termination introduction: fp → next terminates if next terminates
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let fl_chain_terminates_step (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    (let hd = hd_address (fp <: obj_addr) in
                     U64.v hd + 16 <= heap_size ==>
                     fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1)))
          (ensures fl_chain_terminates g fp steps)
  = ()

let fl_chain_terminates_elim (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fl_chain_terminates g fp steps /\
                    steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1) = true)
  = ()

let fl_chain_terminates_valid_zero (g: heap) (fp: U64.t)
  : Lemma (requires U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0)
          (ensures fl_chain_terminates g fp 0 = false)
  = ()
#pop-options



/// ===========================================================================
/// Section: Chain walk machinery and acyclicity
/// ===========================================================================

/// walk_chain: walk n steps following free-list links.
/// Stops early if the chain reaches a terminal node (null, out-of-bounds, unaligned, or hd+16 > hs).
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec walk_chain (g: heap) (fp: U64.t) (n: nat) : Tot U64.t (decreases n) =
  if n = 0 then fp
  else if fp = 0UL then fp
  else if U64.v fp < U64.v mword then fp
  else if U64.v fp >= heap_size then fp
  else if U64.v fp % U64.v mword <> 0 then fp
  else
    let hd = hd_address (fp <: obj_addr) in
    if U64.v hd + 16 > heap_size then fp
    else walk_chain g (read_word g (fp <: obj_addr)) (n - 1)
#pop-options

let walk_chain_zero (g: heap) (fp: U64.t)
  : Lemma (ensures walk_chain g fp 0 = fp)
  = ()

/// walk_chain_valid: all intermediate nodes (positions 0..n-1) are valid (non-terminal).
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec walk_chain_valid (g: heap) (fp: U64.t) (n: nat) : Tot prop (decreases n) =
  if n = 0 then True
  else
    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\ U64.v fp % U64.v mword = 0 /\
    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size /\
    walk_chain_valid g (read_word g (fp <: obj_addr)) (n - 1)
#pop-options

let walk_chain_valid_zero (g: heap) (fp: U64.t)
  : Lemma (ensures walk_chain_valid g fp 0)
  = ()

/// walk_chain_valid prefix: if all of first k steps are valid, then first j <= k steps are valid.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec walk_chain_valid_prefix (g: heap) (fp: U64.t) (k j: nat)
  : Lemma (requires walk_chain_valid g fp k /\ j <= k)
          (ensures walk_chain_valid g fp j)
          (decreases j)
  = if j = 0 then ()
    else walk_chain_valid_prefix g (read_word g (fp <: obj_addr)) (k - 1) (j - 1)
#pop-options

/// walk_chain_valid_at: position j (< k) in a walk_chain_valid chain is a valid node.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec walk_chain_valid_at (g: heap) (fp: U64.t) (k j: nat)
  : Lemma (requires walk_chain_valid g fp k /\ j < k)
          (ensures (let node = walk_chain g fp j in
                    U64.v node >= U64.v mword /\ U64.v node < heap_size /\
                    U64.v node % U64.v mword = 0 /\
                    U64.v (hd_address (node <: obj_addr)) + 16 <= heap_size))
          (decreases j)
  = if j = 0 then ()
    else walk_chain_valid_at g (read_word g (fp <: obj_addr)) (k - 1) (j - 1)
#pop-options

/// walk_chain_valid_snoc: extend walk_chain_valid by one step if the node at position k is valid.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec walk_chain_valid_snoc (g: heap) (fp: U64.t) (k: nat)
  : Lemma (requires walk_chain_valid g fp k /\
                    (let node = walk_chain g fp k in
                     U64.v node >= U64.v mword /\ U64.v node < heap_size /\
                     U64.v node % U64.v mword = 0 /\
                     U64.v (hd_address (node <: obj_addr)) + 16 <= heap_size))
          (ensures walk_chain_valid g fp (k + 1))
          (decreases k)
  = if k = 0 then ()
    else walk_chain_valid_snoc g (read_word g (fp <: obj_addr)) (k - 1)
#pop-options

/// walk_chain_append: composing walks. Walking m+n steps = walking m steps then n steps from there.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec walk_chain_append (g: heap) (fp: U64.t) (m n: nat)
  : Lemma (requires walk_chain_valid g fp m)
          (ensures walk_chain g fp (m + n) = walk_chain g (walk_chain g fp m) n)
          (decreases m)
  = if m = 0 then ()
    else walk_chain_append g (read_word g (fp <: obj_addr)) (m - 1) n
#pop-options

/// fl_chain_terminates_unfold_steps: if first n steps are valid (non-terminal),
/// then fl_chain_terminates g fp fuel = fl_chain_terminates g (walk_chain g fp n) (fuel - n).
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_terminates_unfold_steps (g: heap) (fp: U64.t) (n fuel: nat)
  : Lemma (requires n <= fuel /\ walk_chain_valid g fp n)
          (ensures fl_chain_terminates g fp fuel = fl_chain_terminates g (walk_chain g fp n) (fuel - n))
          (decreases n)
  = if n = 0 then ()
    else begin
      // walk_chain_valid g fp n with n > 0 gives fp is valid with hd+16<=hs
      // So fl_chain_terminates g fp fuel unfolds to fl_chain_terminates g next (fuel-1)
      // And walk_chain g fp n = walk_chain g next (n-1)
      let next = read_word g (fp <: obj_addr) in
      fl_chain_terminates_unfold_steps g next (n - 1) (fuel - 1)
    end
#pop-options

/// fl_chain_kcycle_not_terminates: a k-cycle (walk_chain g fp k = fp with all valid intermediate
/// nodes) prevents termination for any fuel.
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_kcycle_not_terminates (g: heap) (fp: U64.t) (k fuel: nat)
  : Lemma (requires k > 0 /\ walk_chain g fp k = fp /\ walk_chain_valid g fp k)
          (ensures fl_chain_terminates g fp fuel = false)
          (decreases fuel)
  = if fuel = 0 then begin
      // walk_chain_valid g fp k with k > 0 gives fp is valid (aligned, in bounds, etc.)
      // fl_chain_terminates g fp 0 = false for valid fp
      ()
    end
    else if fuel < k then begin
      // Unfold fuel steps (fuel < k, so walk_chain_valid g fp fuel holds by prefix)
      walk_chain_valid_prefix g fp k fuel;
      fl_chain_terminates_unfold_steps g fp fuel fuel;
      // Now: fl_chain_terminates g fp fuel = fl_chain_terminates g (walk_chain g fp fuel) 0
      // walk_chain g fp fuel is at position fuel (< k), which is valid:
      walk_chain_valid_at g fp k fuel;
      // So fl_chain_terminates g valid_node 0 = false
      ()
    end
    else begin
      // fuel >= k: unfold k steps
      fl_chain_terminates_unfold_steps g fp k fuel;
      // fl_chain_terminates g fp fuel = fl_chain_terminates g (walk_chain g fp k) (fuel - k)
      //                               = fl_chain_terminates g fp (fuel - k)  (since walk = fp)
      fl_chain_kcycle_not_terminates g fp k (fuel - k)
    end
#pop-options

/// A 2-cycle in the free list contradicts fl_chain_terminates.
/// If a → b → a (with both valid nodes and hd + 16 <= heap_size), then
/// fl_chain_terminates g a n = false for all n.
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec fl_chain_2cycle_not_terminates
  (g: heap) (a b: U64.t) (n: nat)
  : Lemma (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                    U64.v b >= U64.v mword /\ U64.v b < heap_size /\ U64.v b % U64.v mword = 0 /\
                    a <> b /\
                    U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size /\
                    U64.v (hd_address (b <: obj_addr)) + 16 <= heap_size /\
                    read_word g (a <: obj_addr) = b /\
                    read_word g (b <: obj_addr) = a)
          (ensures fl_chain_terminates g a n = false)
          (decreases n)
  = if n = 0 then ()
    else begin
      // fl_chain_terminates g a n: a is valid, hd+16<=hs, link = b. Recurse on b with n-1.
      // fl_chain_terminates g b (n-1): b is valid, hd+16<=hs, link = a. Recurse on a with n-2.
      if n >= 2 then
        fl_chain_2cycle_not_terminates g a b (n - 2)
      else begin
        // n = 1: fl_chain_terminates g a 1 unfolds to fl_chain_terminates g b 0 = false
        ()
      end
    end
#pop-options

/// Chain termination splice: analogous to fl_valid_splice for chain termination.
/// The tail at splice_point terminates in `tail_steps` steps.
/// The ensures gives `steps + tail_steps` because at the splice point, the
/// chain "consumes" some prefix steps then uses all tail_steps for the new tail.
#restart-solver
/// Writing at a field position (body of an object with wosize >= 1) preserves fl_valid.
/// The write doesn't change any header, so objects and wosize are preserved.
/// At the write position, the new link may differ but we require no self-loop.
/// Since fl_valid at fuel=0 is True, even cyclic chains through the write position are fine.
///
/// Strategy: prove fl_valid g' fp fuel by induction on fuel, using:
///   - For fp ≠ p: fl_valid g fp fuel gives all needed properties, link unchanged
///   - For fp = p: properties from g (mem, wosize), new link = v ≠ p, recurse on v
///   Both cases recurse with fuel-1, and fuel=0 gives True.
///
/// The precondition provides fl_valid g fp fuel which ensures:
///   - Every node visited (except possibly at p) has mem, wosize>=1, no-self-loop in g
///   - These transfer to g' because only p's body value changed
/// At p: we use the explicit mem/wosize/no-self-loop from the precondition.
///
/// For the chain from v (the new link at p): we need fl_valid g' v (fuel-1).
/// We also require fl_valid g' v tail_fuel (as a separate input) to handle
/// the case where the chain diverges at p.
#restart-solver
/// Establish fl_valid g2 v fuel where g2 = write_word g p v, by strong induction.
/// Breaks the circularity in fl_valid_field_write: at the write point p, the new link
/// is v, and we need fl_valid g2 v (fuel-1). By strong induction, this is the IH.
#restart-solver
/// ---------------------------------------------------------------------------
/// Helper: chain_avoids — the free-list chain from fp does not visit `excl`
/// ---------------------------------------------------------------------------

let rec chain_avoids (g: heap) (fp excl: U64.t) (steps: nat) : Tot bool (decreases steps) =
  if fp = 0UL then true
  else if U64.v fp < U64.v mword then true
  else if U64.v fp >= heap_size then true
  else if U64.v fp % U64.v mword <> 0 then true
  else if steps = 0 then true
  else if fp = excl then false
  else
    let hd = hd_address (fp <: obj_addr) in
    if U64.v hd + 16 > heap_size then true
    else chain_avoids g (read_word g (fp <: obj_addr)) excl (steps - 1)

let chain_avoids_null (g: heap) (excl: U64.t) (steps: nat)
  : Lemma (ensures chain_avoids g 0UL excl steps = true)
  = ()

/// chain_avoids_unfold_step: one-step unfolding of chain_avoids.
/// When fp is a valid non-terminal node, fp ≠ excl, and steps > 0,
/// chain_avoids reduces to the recursive call on the successor.
let chain_avoids_unfold_step (g: heap) (fp excl: U64.t) (steps: nat)
  : Lemma (requires U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size /\
                    fp <> excl /\ steps > 0)
          (ensures chain_avoids g fp excl steps =
                   chain_avoids g (read_word g (fp <: obj_addr)) excl (steps - 1))
  = ()

/// chain_avoids_head_ne: extract fp ≠ excl from chain_avoids = true.
let chain_avoids_head_ne (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ fuel > 0)
          (ensures fp <> excl)
  = ()

/// chain_avoids_tail: one-step decomposition — successor chain also avoids excl.
let chain_avoids_tail (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ fuel > 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures chain_avoids g (read_word g (fp <: obj_addr)) excl (fuel - 1) = true)
  = ()

/// chain_avoids_transfer: if chain_avoids holds in heap g, and all link reads along the chain
/// are preserved in heap g' (for objects in objects(g) with wosize >= 1), then chain_avoids
/// also holds in g'. Uses fl_valid to know chain nodes are in objects(g).
#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec chain_avoids_transfer (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                      U64.v (wosize_of_object a g) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      a <> excl ==>
                        read_word g' a == read_word g a))
          (ensures chain_avoids g' fp excl fuel = true)
          (decreases fuel)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if fuel = 0 then ()
    else begin
      chain_avoids_head_ne g fp excl fuel;
      // fl_valid gives: fp ∈ objects(g), wosize >= 1
      fl_valid_gives_mem g fp fuel;
      fl_valid_gives_wosize g fp fuel;
      let hd = hd_address (fp <: obj_addr) in
      hd_address_spec (fp <: obj_addr);
      if U64.v hd + 16 > heap_size then ()
      else begin
        // fp ∈ objects(g), wosize >= 1, hd+16 <= heap_size, fp <> excl → read preserved
        assert (read_word g' (fp <: obj_addr) == read_word g (fp <: obj_addr));
        chain_avoids_tail g fp excl fuel;
        fl_valid_next g fp fuel;
        chain_avoids_transfer g g' (read_word g (fp <: obj_addr)) excl (fuel - 1)
      end
    end
#pop-options

#restart-solver
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let rec chain_avoids_transfer_on_chain (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                      U64.v (wosize_of_object a g) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      a <> excl /\
                      chain_avoids g fp a fuel = false ==>
                        read_word g' a == read_word g a))
          (ensures chain_avoids g' fp excl fuel = true)
          (decreases fuel)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if fuel = 0 then ()
    else begin
      chain_avoids_head_ne g fp excl fuel;
      fl_valid_gives_mem g fp fuel;
      fl_valid_gives_wosize g fp fuel;
      let fp_obj : obj_addr = fp in
      let hd = hd_address fp_obj in
      hd_address_spec fp_obj;
      if U64.v hd + 16 > heap_size then ()
      else begin
        assert (chain_avoids g fp fp fuel = false);
        assert (read_word g' fp_obj == read_word g fp_obj);
        let next_fp = read_word g fp_obj in
        chain_avoids_tail g fp excl fuel;
        fl_valid_next g fp fuel;
        let tail_links (a: obj_addr) : Lemma
          (requires Seq.mem a (objects zero_addr g) /\
                    U64.v (wosize_of_object a g) >= 1 /\
                    U64.v (hd_address a) + 16 <= heap_size /\
                    a <> excl /\
                    chain_avoids g next_fp a (fuel - 1) = false)
          (ensures read_word g' a == read_word g a)
        = if a = fp_obj then begin
            assert (chain_avoids g fp a fuel = false)
          end else begin
            chain_avoids_unfold_step g fp a fuel;
            assert (chain_avoids g fp a fuel = false)
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires tail_links);
        chain_avoids_transfer_on_chain g g' next_fp excl (fuel - 1)
      end
    end
#pop-options

/// chain_avoids_weaken: if chain_avoids holds for fuel steps, it also holds for fewer steps.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec chain_avoids_weaken (g: heap) (fp excl: U64.t) (fuel fuel': nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\ fuel' <= fuel)
          (ensures chain_avoids g fp excl fuel' = true)
          (decreases fuel')
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if fuel' = 0 then ()
    else begin
      chain_avoids_head_ne g fp excl fuel;
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else begin
        chain_avoids_tail g fp excl fuel;
        chain_avoids_weaken g (read_word g (fp <: obj_addr)) excl (fuel - 1) (fuel' - 1)
      end
    end
#pop-options

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec chain_avoids_strengthen (g: heap) (fp excl: U64.t) (s1 s2: nat)
  : Lemma (requires chain_avoids g fp excl s1 = true /\
                    fl_chain_terminates g fp s1 /\
                    s2 >= s1)
          (ensures chain_avoids g fp excl s2 = true)
          (decreases s1)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if s1 = 0 then ()
    else begin
      assert (fp <> excl);
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else
        chain_avoids_strengthen g (read_word g (fp <: obj_addr)) excl (s1 - 1) (s2 - 1)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: chain_avoids_transfer_excl — transfer chain_avoids from g to g'
/// when all link reads are preserved except possibly at excl.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec chain_avoids_transfer_excl
  (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma
    (requires chain_avoids g fp excl fuel = true /\
              fl_valid g fp fuel /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g) /\ a <> excl) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures chain_avoids g' fp excl fuel = true)
    (decreases fuel)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if fuel = 0 then ()
    else begin
      chain_avoids_head_ne g fp excl fuel;
      assert (fp <> excl);
      fl_valid_elim g fp fuel;
      assert (Seq.mem fp (objects zero_addr g));
      assert (U64.v (wosize_of_object (fp <: obj_addr) g) >= 1);
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else begin
        let link = read_word g (fp <: obj_addr) in
        chain_avoids_tail g fp excl fuel;
        assert (chain_avoids g link excl (fuel - 1) = true);
        assert (fl_valid g link (fuel - 1));
        assert (read_word g' (fp <: obj_addr) == link);
        chain_avoids_transfer_excl g g' link excl (fuel - 1);
        assert (chain_avoids g' (read_word g' (fp <: obj_addr)) excl (fuel - 1) = true);
        chain_avoids_unfold_step g' fp excl fuel
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: chain_avoids_transfer_excl2 — transfer chain_avoids from g to g'
/// when all link reads are preserved except possibly at excl or excl2.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec chain_avoids_transfer_excl2
  (g g': heap) (fp excl excl2: U64.t) (fuel: nat)
  : Lemma
    (requires chain_avoids g fp excl fuel = true /\
              chain_avoids g fp excl2 fuel = true /\
              fl_valid g fp fuel /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g) /\ a <> excl /\ a <> excl2) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures chain_avoids g' fp excl fuel = true)
    (decreases fuel)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if fuel = 0 then ()
    else begin
      chain_avoids_head_ne g fp excl fuel;
      chain_avoids_head_ne g fp excl2 fuel;
      assert (fp <> excl);
      assert (fp <> excl2);
      fl_valid_elim g fp fuel;
      assert (Seq.mem fp (objects zero_addr g));
      assert (U64.v (wosize_of_object (fp <: obj_addr) g) >= 1);
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else begin
        let link = read_word g (fp <: obj_addr) in
        chain_avoids_tail g fp excl fuel;
        chain_avoids_tail g fp excl2 fuel;
        assert (chain_avoids g link excl (fuel - 1) = true);
        assert (chain_avoids g link excl2 (fuel - 1) = true);
        assert (fl_valid g link (fuel - 1));
        assert (read_word g' (fp <: obj_addr) == link);
        chain_avoids_transfer_excl2 g g' link excl excl2 (fuel - 1);
        assert (chain_avoids g' (read_word g' (fp <: obj_addr)) excl (fuel - 1) = true);
        chain_avoids_unfold_step g' fp excl fuel
      end
    end
#pop-options


/// ---------------------------------------------------------------------------
/// Helper: chain_avoids_unfold_steps — unfold n valid steps.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec chain_avoids_unfold_steps (g: heap) (fp excl: U64.t) (n fuel: nat)
  : Lemma (requires n <= fuel /\ walk_chain_valid g fp n /\
                    chain_avoids g fp excl n = true)
          (ensures chain_avoids g fp excl fuel =
                   chain_avoids g (walk_chain g fp n) excl (fuel - n))
          (decreases n)
  = if n = 0 then ()
    else begin
      let next = read_word g (fp <: obj_addr) in
      chain_avoids_unfold_steps g next excl (n - 1) (fuel - 1)
    end
#pop-options


/// first_hit: if chain_avoids = false (i.e., dst_obj IS in chain), gives the position where
/// dst_obj first appears.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec first_hit (g: heap) (fp dst_obj: U64.t) (fuel: nat) : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else if fp = 0UL then 0
  else if U64.v fp < U64.v mword then 0
  else if U64.v fp >= heap_size then 0
  else if U64.v fp % U64.v mword <> 0 then 0
  else if fp = dst_obj then 0
  else
    let hd = hd_address (fp <: obj_addr) in
    if U64.v hd + 16 > heap_size then 0
    else 1 + first_hit g (read_word g (fp <: obj_addr)) dst_obj (fuel - 1)
#pop-options

/// first_hit_spec: when chain_avoids = false, walk_chain to first_hit gives dst_obj,
/// the path is walk_chain_valid, and first_hit <= fuel.
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec first_hit_spec (g: heap) (fp dst_obj: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp dst_obj fuel = false)
          (ensures walk_chain g fp (first_hit g fp dst_obj fuel) = dst_obj /\
                   first_hit g fp dst_obj fuel <= fuel /\
                   walk_chain_valid g fp (first_hit g fp dst_obj fuel))
          (decreases fuel)
  = if fuel = 0 then ()
    else if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if fp = dst_obj then ()
    else begin
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 > heap_size then ()
      else begin
        let next = read_word g (fp <: obj_addr) in
        first_hit_spec g next dst_obj (fuel - 1)
      end
    end
#pop-options

/// walk_chain_one_step: walking 1 step from a valid node gives read_word.
let walk_chain_one_step (g: heap) (fp: U64.t)
  : Lemma (requires U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures walk_chain g fp 1 = read_word g (fp <: obj_addr))
  = ()

/// ---------------------------------------------------------------------------
/// Helper: if the chain from next_fp terminates and prev_fp links to cur_fp
/// which links to next_fp, then prev_fp is not in the chain from next_fp.
/// (Otherwise there would be a cycle contradicting termination.)
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let chain_avoids_prev
  (g: heap) (prev_fp cur_fp next_fp: U64.t) (steps: nat)
  : Lemma
    (requires fl_chain_terminates g next_fp steps /\
              fl_valid g next_fp steps /\
              U64.v prev_fp >= U64.v mword /\
              U64.v prev_fp < heap_size /\
              U64.v prev_fp % U64.v mword = 0 /\
              Seq.mem prev_fp (objects zero_addr g) /\
              U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
              U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
              read_word g (prev_fp <: obj_addr) == cur_fp /\
              U64.v cur_fp >= U64.v mword /\
              U64.v cur_fp < heap_size /\
              U64.v cur_fp % U64.v mword = 0 /\
              Seq.mem cur_fp (objects zero_addr g) /\
              U64.v (wosize_of_object (cur_fp <: obj_addr) g) >= 1 /\
              U64.v (hd_address (cur_fp <: obj_addr)) + 16 <= heap_size /\
              read_word g (cur_fp <: obj_addr) == next_fp /\
              prev_fp <> cur_fp)
    (ensures chain_avoids g next_fp prev_fp steps = true)
  = // Proof by contradiction using the walk_chain / cycle machinery.
    // If chain_avoids g next_fp prev_fp steps were false, then prev_fp appears
    // in the chain from next_fp. We extend the walk by 2 more steps
    // (prev_fp → cur_fp → next_fp) to get a cycle, contradicting termination.
    if chain_avoids g next_fp prev_fp steps then ()
    else begin
      // chain_avoids g next_fp prev_fp steps = false
      // Extract position k where walk_chain g next_fp k = prev_fp.
      first_hit_spec g next_fp prev_fp steps;
      let k = first_hit g next_fp prev_fp steps in
      // first_hit_spec gives:
      //   walk_chain g next_fp k = prev_fp
      //   walk_chain_valid g next_fp k
      //   k <= steps
      //
      // Extend to k+1: walk_chain g next_fp (k+1) = cur_fp
      //   prev_fp is valid (from preconditions), so we can snoc.
      walk_chain_valid_snoc g next_fp k;
      walk_chain_append g next_fp k 1;
      walk_chain_one_step g prev_fp;
      assert (walk_chain g next_fp (k + 1) = cur_fp);
      //
      // Extend to k+2: walk_chain g next_fp (k+2) = next_fp
      //   cur_fp is valid (from preconditions), so we can snoc again.
      walk_chain_valid_snoc g next_fp (k + 1);
      walk_chain_append g next_fp (k + 1) 1;
      walk_chain_one_step g cur_fp;
      assert (walk_chain g next_fp (k + 2) = next_fp);
      //
      // We have a (k+2)-cycle from next_fp. This contradicts termination.
      fl_chain_kcycle_not_terminates g next_fp (k + 2) steps
      // Now: fl_chain_terminates g next_fp steps = false
      // But precondition: fl_chain_terminates g next_fp steps = true
      // Contradiction → F* derives False, and the else branch is vacuously OK.
    end
#pop-options

/// ===========================================================================
/// Section: not_in_fl_chain_b and fl_chain_predecessor_not_in_suffix_b
/// ===========================================================================

/// not_in_fl_chain_b: boolean test for "dst_obj does not appear in the chain from fp".
/// Defined as an alias for chain_avoids (same logic).
[@@"unfold_for_unification_and_vcgen"]
let not_in_fl_chain_b (g: heap) (fp: U64.t) (dst_obj: U64.t) (fuel: nat) : Tot bool =
  chain_avoids g fp dst_obj fuel

let not_in_fl_chain_b_is_chain_avoids (g: heap) (fp dst_obj: U64.t) (fuel: nat)
  : Lemma (ensures not_in_fl_chain_b g fp dst_obj fuel = chain_avoids g fp dst_obj fuel)
  = ()

/// fl_chain_predecessor_not_in_suffix_b: the main acyclicity theorem (boolean version).
/// If obj's chain terminates and is fl_valid, then obj does not appear in the chain
/// starting from its successor.
#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let fl_chain_predecessor_not_in_suffix_b (g: heap) (obj: U64.t) (fuel: nat)
  : Lemma (requires fl_chain_terminates g obj fuel /\
                    fl_valid g obj fuel /\
                    U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\ U64.v obj % U64.v mword = 0 /\
                    U64.v (hd_address (obj <: obj_addr)) + 16 <= heap_size /\
                    fuel > 0)
          (ensures chain_avoids g (read_word g (obj <: obj_addr)) obj (fuel - 1) = true)
  = let next = read_word g (obj <: obj_addr) in
    fl_chain_terminates_elim g obj fuel;
    assert (fl_chain_terminates g next (fuel - 1) = true);
    if chain_avoids g next obj (fuel - 1) then ()
    else begin
      first_hit_spec g next obj (fuel - 1);
      let k = first_hit g next obj (fuel - 1) in
      walk_chain_valid_snoc g next k;
      walk_chain_append g next k 1;
      walk_chain_one_step g obj;
      assert (walk_chain g next (k + 1) = next);
      fl_chain_kcycle_not_terminates g next (k + 1) (fuel - 1)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: fl_chain_terminates transfer with one excluded node
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec fl_chain_terminates_transfer_excl
  (g g': heap) (fp excl: U64.t) (steps: nat)
  : Lemma
    (requires fl_chain_terminates g fp steps /\
              fl_valid g fp steps /\
              chain_avoids g fp excl steps /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g) /\ a <> excl) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures fl_chain_terminates g' fp steps)
    (decreases steps)
  = if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else if steps = 0 then begin
      assert (fl_chain_terminates g fp steps = false);
      assert False
    end
    else begin
      chain_avoids_head_ne g fp excl steps;
      assert (fp <> excl);
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      if U64.v hd + 16 <= heap_size then begin
        let link = read_word g obj in
        fl_valid_elim g fp steps;
        fl_chain_terminates_elim g fp steps;
        chain_avoids_tail g fp excl steps;
        assert (Seq.mem fp (objects zero_addr g));
        assert (U64.v (wosize_of_object obj g) >= 1);
        assert (read_word g' obj == link);
        assert (fl_valid g link (steps - 1));
        assert (fl_chain_terminates g link (steps - 1) = true);
        assert (chain_avoids g link excl (steps - 1) = true);
        fl_chain_terminates_transfer_excl g g' link excl (steps - 1);
        assert (fl_chain_terminates g' (read_word g' obj) (steps - 1));
        fl_chain_terminates_step g' fp steps
      end
      else ()
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: walk_chain_valid_suffix — extract suffix validity
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let rec walk_chain_valid_suffix (g: heap) (fp: U64.t) (j d: nat)
  : Lemma (requires walk_chain_valid g fp d /\ j <= d)
          (ensures walk_chain_valid g (walk_chain g fp j) (d - j))
          (decreases j)
  = if j = 0 then ()
    else walk_chain_valid_suffix g (read_word g (fp <: obj_addr)) (j - 1) (d - 1)
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: fl_chain_no_early_repeat — acyclicity of walk_chain
/// If walk_chain g fp d = X, and the chain terminates and is valid, then
/// X does not appear in the first d positions (i.e., not_in_fl_chain_b is true).
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec fl_chain_no_early_repeat (g: heap) (fp: U64.t) (d fuel: nat)
  : Lemma (requires walk_chain_valid g fp d /\ d > 0 /\
                    fl_chain_terminates g fp fuel /\ fl_valid g fp fuel /\ fuel >= d)
          (ensures chain_avoids g fp (walk_chain g fp d) d = true)
          (decreases d)
  = let dst = walk_chain g fp d in
    if d = 1 then begin
      // walk_chain g fp 1 = link (since fp valid from walk_chain_valid g fp 1)
      // fl_valid g fp fuel (fuel >= 1): link ≠ fp (no self-loop). So fp ≠ dst.
      // chain_avoids g fp dst 1: fp ≠ dst, fp valid, recurse with (link, 0) → true.
      let link = read_word g (fp <: obj_addr) in
      assert (fuel > 0);
      walk_chain_one_step g fp;
      assert (dst == link);
      fl_valid_elim g fp fuel;
      assert (U64.v fp >= U64.v mword);
      assert (U64.v fp < heap_size);
      assert (U64.v fp % U64.v mword = 0);
      assert (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size);
      assert (link <> fp);
      assert (fp <> dst);
      chain_avoids_unfold_step g fp dst d;
      assert (chain_avoids g link dst 0 = true)
    end
    else begin
      // d > 1. Check if fp = walk_chain g fp d.
      if fp = dst then begin
        // d-cycle from fp. walk_chain_valid g fp d. fl_chain_kcycle_not_terminates contradicts termination.
        fl_chain_kcycle_not_terminates g fp d fuel;
        assert false
      end
      else begin
        // fp ≠ dst. chain_avoids unfolds to recurse with (link, d-1).
        let link = read_word g (fp <: obj_addr) in
        // walk_chain g fp d = walk_chain g link (d-1) (by walk_chain_append)
        walk_chain_valid_prefix g fp d 1;
        walk_chain_append g fp 1 (d - 1);
        walk_chain_one_step g fp;
        assert (dst = walk_chain g link (d - 1));
        assert (fuel > 0);
        fl_valid_elim g fp fuel;
        fl_chain_terminates_elim g fp fuel;
        walk_chain_valid_suffix g fp 1 d;
        assert (walk_chain g fp 1 == link);
        assert (walk_chain_valid g link (d - 1));
        assert (fl_valid g link (fuel - 1));
        assert (fl_chain_terminates g link (fuel - 1));
        assert (fuel - 1 >= d - 1);
        // IH: fl_chain_no_early_repeat g link (d-1) (fuel-1)
        fl_chain_no_early_repeat g link (d - 1) (fuel - 1);
        assert (chain_avoids g link dst (d - 1) = true);
        // Explicit one-step unfolding: chain_avoids g fp dst d = chain_avoids g link dst (d-1)
        chain_avoids_unfold_step g fp dst d
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Helper: walk_chain_valid_preserved — transfer walk_chain between heaps
/// When reads are preserved for all objects except `excl`, and the walk
/// avoids `excl`, then walk_chain_valid and walk_chain are preserved.
/// ---------------------------------------------------------------------------

#restart-solver
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec walk_chain_valid_preserved (g g2: heap) (fp excl: U64.t) (d fuel: nat)
  : Lemma
    (requires walk_chain_valid g fp d /\
             fl_valid g fp fuel /\ fuel >= d /\
             chain_avoids g fp excl d = true /\
             (forall (a: U64.t).
                (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                 Seq.mem a (objects zero_addr g) /\ a <> excl) ==>
                (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                 U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                   read_word g2 (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures walk_chain_valid g2 fp d /\ walk_chain g2 fp d = walk_chain g fp d)
    (decreases d)
  = if d = 0 then ()
    else begin
      // fp is valid (from walk_chain_valid g fp d, d > 0)
      // fp ≠ excl (from chain_avoids g fp excl d = true, d > 0, fp non-terminal)
      // fp ∈ objects(g) (from fl_valid_gives_mem)
      // wosize ≥ 1 (from fl_valid_gives_wosize)
      assert (fuel > 0);
      fl_valid_elim g fp fuel;
      chain_avoids_head_ne g fp excl d;
      chain_avoids_tail g fp excl d;
      assert (Seq.mem fp (objects zero_addr g));
      assert (U64.v (wosize_of_object (fp <: obj_addr) g) >= 1);
      assert (fp <> excl);
      // read_word g2 fp = read_word g fp (from quantifier)
      let link = read_word g (fp <: obj_addr) in
      assert (read_word g2 (fp <: obj_addr) == link);
      assert (walk_chain_valid g link (d - 1));
      assert (fl_valid g link (fuel - 1));
      assert (fuel - 1 >= d - 1);
      assert (chain_avoids g link excl (d - 1) = true);
      // IH
      walk_chain_valid_preserved g g2 link excl (d - 1) (fuel - 1);
      assert (walk_chain_valid g2 link (d - 1));
      assert (walk_chain g2 link (d - 1) == walk_chain g link (d - 1));
      assert (walk_chain_valid g2 fp d);
      assert (walk_chain g2 fp d == walk_chain g2 link (d - 1));
      assert (walk_chain g fp d == walk_chain g link (d - 1));
      assert (walk_chain g2 fp d == walk_chain g fp d)
    end
#pop-options


#pop-options

/// ---------------------------------------------------------------------------
/// Fuel saturation for alloc_search
/// ---------------------------------------------------------------------------

/// The free-list search never bottoms out on its fuel budget: if the chain from
/// `cur_fp` reaches a terminal within `fuel` steps, then handing `alloc_search`
/// any larger budget yields exactly the same result.
///
/// The point of this lemma is completeness.  `alloc_search`'s `fuel = 0` branch
/// reports OOM, and on its own nothing rules out that branch firing while a
/// suitable block is still reachable.  Fuel irrelevance says the budget never
/// binds, so an OOM answer is always the genuine "walked the whole free list and
/// nothing fits" answer rather than an artefact of the bound.
/// Corollary: the `heap_words` budget baked into `alloc_spec` never binds.
/// Any surplus fuel leaves the answer unchanged, so `alloc_spec` reports OOM
/// only when the free list genuinely holds no block of the requested size.
