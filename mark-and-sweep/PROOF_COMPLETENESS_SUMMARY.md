# DFS Completeness Proof for Mark Phase

## Summary

This document describes the proof of DFS completeness for the mark phase garbage collector: `mark_black_is_reachable`.

**Location:** `Spec/Pulse.Spec.GC.Mark.fst`, lines 479-560

## What Was Implemented

### 1. Helper Lemma: `mark_aux_complete` (lines 383-477)

**Specification:**
```fstar
val mark_aux_complete : (g: heap) -> (st: seq U64.t) -> (fuel: nat) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ stack_elements_valid_addr st)
        (ensures (forall (x: hp_addr).
                   is_black x (mark_aux g st fuel) /\ ~(is_black x g) ==>
                   (exists (s: U64.t). Seq.mem s st /\ 
                    reachable (create_graph_from_heap g) (hd_address s) x)))
        (decreases fuel)
```

**Purpose:** 
Proves that if an object becomes black during `mark_aux`, it was reachable from some element on the initial stack. This is the key inductive invariant for completeness.

**Proof Structure:**
- **Base cases** (empty stack or fuel = 0): Trivial, no changes to heap
- **Inductive case**: Process head of stack
  1. Apply `mark_step` to process `h_addr = hd_address (Seq.head st)`
  2. Split into two cases for any newly black object `x`:
     - **Case 1**: `x` became black in `mark_step` 
       - Only `h_addr` becomes black in this step
       - `h_addr` is reachable from itself (reflexivity)
       - `h_addr` is the header of `hd`, which is in `st`
     - **Case 2**: `x` became black in recursive call
       - By IH: `x` is reachable from some `s'` in `st'`
       - Need to relate `st'` back to original `st`
       - `st'` = tail of `st` ∪ children of `h_addr`

**Status:** 
- ✅ Structure complete with proper specification
- ⚠️ Uses `admit()` for Case 2 technical details (line 472)
- ⚠️ Uses `assume()` for preservation lemmas (lines 413-418)

**What Remains for Case 2:**
1. Prove: `create_graph_from_heap g == create_graph_from_heap g'` (edges unchanged by color changes)
2. Prove: Elements of `st'` are either:
   - From `tail st` (already in `st`), OR
   - Children pushed by `push_children` (reachable in one step from `h_addr`)
3. Use transitivity: if `x` reachable from child of `h_addr`, and child reachable from `h_addr`, then `x` reachable from `h_addr`

### 2. Main Lemma: `mark_black_is_reachable` (lines 480-560)

**Specification:**
```fstar
val mark_black_is_reachable : (g: heap) -> (st: seq U64.t) -> (roots: seq hp_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  (forall (i: nat). i < Seq.length roots ==> 
                    (let r = Seq.index roots i in 
                     U64.v r + U64.v mword < heap_size /\
                     Seq.mem (f_address r) st)))
        (ensures (forall (x: hp_addr). 
                   is_black x (mark g st) ==> 
                   reachable_from_set (create_graph_from_heap g) (coerce_to_vertex_list roots) x))
```

**Purpose:**
Proves DFS completeness: all black objects after mark are reachable from roots.

**Proof Structure:**
1. Apply `mark_aux_complete` to get: newly black objects reachable from stack
2. For any black object `x` after mark:
   - **Case 1**: `x` was already black before mark
     - From `root_props`: initially black objects must be roots
     - `x` reachable from itself (reflexivity)
   - **Case 2**: `x` became black during mark
     - By `mark_aux_complete`: ∃`s ∈ st` with `x` reachable from `hd_address s`
     - From precondition: all roots `r` have `f_address r ∈ st`
     - Connect `s` to some root via `hd_address (f_address r) == r`
     - Conclude `x` reachable from roots

**Status:**
- ✅ Structure complete with proper specification
- ⚠️ Uses `assume()` for initially black objects (line 523)
- ⚠️ Uses `assume()`+`admit()` for stack-to-roots connection (lines 548-556)

**What Remains:**
1. **Initially black objects:** Need precondition that initially black objects are roots, OR prove from initial state invariant
2. **Stack-to-roots bijection:** Need to prove:
   - Precondition says: `∀r ∈ roots. f_address r ∈ st`
   - Need to add/prove: `∀s ∈ st. ∃r ∈ roots. s == f_address r` (stack only contains root addresses)
   - OR: strengthen precondition to: `st == {f_address r | r ∈ roots}`
3. **Connect the pieces:** Use `hd_f_roundtrip` lemma to show `hd_address (f_address r) == r`

### 3. Combined Lemma: `mark_black_iff_reachable` (lines 562-574)

**Specification:**
```fstar
val mark_black_iff_reachable : (g: heap) -> (st: seq U64.t) -> (roots: seq hp_addr) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ root_props g roots /\
                  (forall (i: nat). i < Seq.length roots ==> 
                    (let r = Seq.index roots i in 
                     U64.v r + U64.v mword < heap_size /\
                     Seq.mem (f_address r) st)))
        (ensures (forall (x: hp_addr). 
                   is_black x (mark g st) <==> 
                   reachable_from_set (create_graph_from_heap g) (coerce_to_vertex_list roots) x))
```

**Implementation:**
```fstar
let mark_black_iff_reachable g st roots =
  mark_reachable_is_black g st roots;   // Soundness: reachable ⟹ black
  mark_black_is_reachable g st roots    // Completeness: black ⟹ reachable
```

**Status:** ✅ Complete (modulo the admits in the component lemmas)

## Key Definitions Used

### From `Pulse.Spec.GC.Graph`
- `reachable g x y`: Inductive predicate for reachability in graph `g`
- `reach_refl`: Reflexivity lemma (every vertex reaches itself)
- `reach_trans`: Transitivity lemma
- `reachable_from_set g roots x`: `x` is reachable from some root in `roots`

### From `Pulse.Spec.GC.Heap`
- `hd_address f_addr`: Convert field address to header address (`f_addr - mword`)
- `f_address h_addr`: Convert header address to field address (`h_addr + mword`)
- `hd_f_roundtrip`: Lemma that these are inverses

### From `Pulse.Spec.GC.Object`
- `is_black h_addr g`: Predicate for black objects
- `makeBlack h_addr g`: Make object black

### From `Pulse.Spec.GC.Fields`
- `create_graph_from_heap g`: Extract graph structure from heap
- `coerce_to_vertex_list`: Convert sequence of hp_addr to vertex_list

### From `Pulse.Spec.GC.Mark`
- `mark_step g st`: Process one gray object (make black, push children)
- `mark_aux g st fuel`: Iterate mark_step with fuel
- `mark g st`: Main mark function with sufficient fuel
- `stack_props g st`: Gray stack invariant

## Next Steps to Complete Proof

### Priority 1: Foundational Lemmas (Dependencies for everything else)

1. **Graph preservation under color changes**
   ```fstar
   val color_preserves_graph : (g: heap) -> (g': heap) -> (h_addr: hp_addr) ->
     Lemma (requires g' == makeBlack h_addr g \/ g' == makeGray h_addr g)
           (ensures create_graph_from_heap g == create_graph_from_heap g')
   ```

2. **Mark step behavior**
   ```fstar
   val mark_step_only_blackens_head : (g: heap) -> (st: seq U64.t) ->
     Lemma (requires well_formed_heap g /\ stack_props g st /\ Seq.length st > 0)
           (ensures (let (g', _) = mark_step g st in
                     let h_addr = hd_address (Seq.head st) in
                     forall (y: hp_addr). is_black y g' /\ ~(is_black y g) ==> y == h_addr))
   ```

3. **Stack composition after mark_step**
   ```fstar
   val mark_step_stack_composition : (g: heap) -> (st: seq U64.t) ->
     Lemma (requires well_formed_heap g /\ stack_props g st /\ Seq.length st > 0)
           (ensures (let (g', st') = mark_step g st in
                     let h_addr = hd_address (Seq.head st) in
                     let children = get_pointer_fields g h_addr in
                     forall (s: U64.t). Seq.mem s st' <==>
                       (Seq.mem s (Seq.tail st) \/ 
                        exists (c: vertex_id). Seq.mem c children /\ 
                                               s == c /\ 
                                               is_white (hd_address c) g)))
   ```

### Priority 2: Complete `mark_aux_complete`

Replace `admit()` at line 472 with:
1. Extract witness `s'` from IH: `s' ∈ st'` and `x` reachable from `hd_address s'` in `g'`
2. Use `color_preserves_graph` to show reachability in `g'` equals reachability in `g`
3. Case split on `s'`:
   - If `s' ∈ tail st`: Done, since `tail st ⊆ st`
   - If `s'` is a child of `h_addr`: 
     * `s'` corresponds to edge `h_addr → hd_address s'` in graph
     * Use `edge_reach` to get `reachable g h_addr (hd_address s')`
     * Use `reach_trans` to compose with `reachable g (hd_address s') x`
     * Get `reachable g h_addr x`
     * `h_addr == hd_address hd`, and `hd ∈ st`
     * Done

### Priority 3: Strengthen Preconditions

Option A: Add to initial state invariant
```fstar
// In initial configuration before mark:
// - All roots are gray or black
// - No other objects are black
// - Stack contains exactly the roots' field addresses
```

Option B: Strengthen `mark_black_is_reachable` precondition
```fstar
requires ... /\
  // Stack contains exactly root field addresses
  (forall (s: U64.t). Seq.mem s st <==>
    exists (r: hp_addr). Seq.mem r roots /\ s == f_address r) /\
  // No initially black non-roots
  (forall (x: hp_addr). is_black x g ==> Seq.mem x roots)
```

### Priority 4: Complete `mark_black_is_reachable`

Replace `assume()`/`admit()` at lines 523, 548-556:
1. Use strengthened precondition to justify `is_black x g ==> Seq.mem x roots`
2. Extract witness `s` from `mark_aux_complete`
3. Use bijection from precondition to get root `r` with `s == f_address r`
4. Use `hd_f_roundtrip` to show `hd_address s == r`
5. Combine with reachability to conclude

### Priority 5: Preservation Lemmas

These are assumed at lines 413-415, 266-268:
```fstar
val mark_step_preserves_well_formed : (g: heap) -> (st: seq U64.t) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ Seq.length st > 0)
        (ensures (let (g', _) = mark_step g st in well_formed_heap g'))

val mark_step_preserves_stack_props : (g: heap) -> (st: seq U64.t) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ Seq.length st > 0)
        (ensures (let (g', st') = mark_step g st in stack_props g' st'))

val mark_step_preserves_valid_addr : (g: heap) -> (st: seq U64.t) ->
  Lemma (requires stack_elements_valid_addr st /\ Seq.length st > 0)
        (ensures (let (_, st') = mark_step g st in stack_elements_valid_addr st'))
```

## Verification Strategy

1. **Start with foundational lemmas** (Priority 1)
   - Verify each in isolation
   - Keep rlimits ≤ 10 by factoring into smaller lemmas

2. **Build up incrementally**
   - Complete `mark_aux_complete` using foundational lemmas
   - Verify with small test cases

3. **Strengthen preconditions** (Priority 3)
   - Choose Option A or B based on existing invariants
   - Update dependent lemmas

4. **Complete main lemma** (Priority 4)
   - Should be straightforward once helpers are proven

5. **Add preservation lemmas** (Priority 5)
   - These may already exist elsewhere in the codebase
   - Search for existing color-change preservation lemmas

## Testing

Suggested test cases to verify incrementally:
1. Empty heap, empty stack
2. Single root, no children (object with no pointer fields)
3. Root with one child (simple chain)
4. Root with multiple children (tree structure)
5. Cyclic structure (test transitivity)

## Related Work

- **Soundness lemma** `mark_reachable_is_black` (lines 303-375): Already has structure, uses `mark_aux_sound`
- **`mark_aux_sound`** (lines 226-300): Dual of `mark_aux_complete`, proves reachable ⟹ black
- Both follow similar inductive structure

## Contact

This proof structure was designed to match the DFS completeness pattern. The key insight is that objects can only become black via the DFS traversal, so if an object is black, it must have been visited, and therefore is reachable.
