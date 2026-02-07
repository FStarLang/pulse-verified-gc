# Proof Summary: mark_step Preserves stack_elements_valid_addr

## Overview

Successfully proved that `mark_step` preserves the `stack_elements_valid_addr` predicate, eliminating two `assume` statements in `Pulse.Spec.GC.Mark.fst`.

## Key Insight

The proof relies on the fundamental property that `push_children` only adds field addresses (`f_address` values) to the stack, and all field addresses are valid addresses by definition.

## Predicate Definition

```fstar
let stack_elements_valid_addr (st: seq U64.t) : prop =
  forall (i: nat{i < Seq.length st}). is_val_addr (Seq.index st i)
```

This states that every element in the stack sequence is a valid address (word-aligned, >= mword, < heap_size).

## Proof Structure

The proof is structured as a chain of four lemmas, each building on the previous:

### 1. `is_pointer_field_is_val_addr`

**Signature:**
```fstar
val is_pointer_field_is_val_addr : (v: U64.t) ->
  Lemma (requires is_pointer_field v)
        (ensures is_val_addr v)
```

**Purpose:** Establishes the fundamental relationship between pointer fields and valid addresses.

**Proof:** 
- `is_pointer_field v` requires: `v % mword = 0 && v > 0 && v < heap_size`
- `is_val_addr v` requires: `v % mword = 0 && v >= mword && v < heap_size`
- Since `v` is word-aligned and `> 0`, and `mword = 8`, we have `v >= mword`

### 2. `tail_preserves_valid_addr`

**Signature:**
```fstar
val tail_preserves_valid_addr : (st: seq U64.t{Seq.length st > 0}) ->
  Lemma (requires stack_elements_valid_addr st)
        (ensures stack_elements_valid_addr (Seq.tail st))
```

**Purpose:** Shows that removing the head element preserves validity.

**Proof:** 
- For all `i` in `[0, length(tail st))`, we have `index (tail st) i = index st (i+1)`
- Since `st` has all valid addresses, `index st (i+1)` is valid
- Therefore all elements in `tail st` are valid

### 3. `push_children_preserves_valid_addr`

**Signature:**
```fstar
val push_children_preserves_valid_addr : (g: heap) -> (st: seq U64.t) -> (h_addr: hp_addr) 
                                         -> (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires stack_elements_valid_addr st)
        (ensures stack_elements_valid_addr (snd (push_children g st h_addr i ws)))
        (decreases (U64.v ws - U64.v i + 1))
```

**Purpose:** Shows that pushing children onto the stack preserves validity.

**Proof (by recursion on field index):**
- Base case: `i > ws` → no children pushed, stack unchanged, trivially valid
- Recursive case: 
  - Get field `v = get_field g h_addr i`
  - If `v` is a pointer field to a white object:
    * Apply `is_pointer_field_is_val_addr v` to show `is_val_addr v`
    * Stack becomes `st' = cons v st`
    * For all `j < length st'`:
      - If `j = 0`: `index st' 0 = v`, which is valid (just proved)
      - If `j > 0`: `index st' j = index st (j-1)`, which is valid (precondition)
  - Otherwise: stack unchanged, trivially valid
  - Recurse on next field

### 4. `mark_step_preserves_stack_valid_addr`

**Signature:**
```fstar
val mark_step_preserves_stack_valid_addr : (g: heap) -> (st: seq U64.t{Seq.length st > 0 /\ is_val_addr (Seq.head st)}) ->
  Lemma (requires stack_elements_valid_addr st)
        (ensures stack_elements_valid_addr (snd (mark_step g st)))
```

**Purpose:** Main theorem showing `mark_step` preserves validity.

**Proof:**
1. Let `st' = tail st` (pop the head)
2. Apply `tail_preserves_valid_addr st` → `st'` has valid addresses
3. Make the object black: `g' = makeBlack h_addr g` (doesn't affect stack)
4. If object is no-scan: return `(g', st')` → already proved valid
5. Otherwise: return `push_children g' st' h_addr 1UL ws`
   - Apply `push_children_preserves_valid_addr` → result has valid addresses

## Impact

### Assumes Eliminated

1. **Line 134 (now 230)** in `mark_aux`:
   ```fstar
   - assume (stack_elements_valid_addr st');
   + mark_step_preserves_stack_valid_addr g st;
   ```

2. **Line 583 (now 679)** in `mark_aux_preserves_stack_props`:
   ```fstar
   - assume (stack_elements_valid_addr st');
   + mark_step_preserves_stack_valid_addr g st;
   ```

### Verification Status

✅ **All verification conditions discharged successfully**

```
Verified module: Pulse.Spec.GC.Mark
All verification conditions discharged successfully
```

## Technical Notes

### Proof Techniques Used

1. **Induction**: `push_children_preserves_valid_addr` uses structural recursion
2. **Universal quantifier introduction**: `FStar.Classical.forall_intro` to prove properties for all indices
3. **Case analysis**: Different cases for pointer/non-pointer fields, white/non-white objects
4. **Sequence properties**: `Seq.index`, `Seq.tail`, `Seq.cons` relationships

### Key F* Patterns

- **Forall introduction**: Convert local lemma to universal quantification
  ```fstar
  let aux (i: nat{...}) : Lemma (...) = ... in
  FStar.Classical.forall_intro aux
  ```

- **Explicit assertions**: Guide SMT solver through reasoning steps
  ```fstar
  assert (Seq.index st' 0 == v)
  ```

- **Decreases clause**: Prove termination of recursive lemma
  ```fstar
  (decreases (U64.v ws - U64.v i + 1))
  ```

## Files Modified

- `pulse-proofs/Spec/Pulse.Spec.GC.Mark.fst`
  - Added 4 new lemmas (96 lines of code + documentation)
  - Eliminated 2 assume statements
  - Total file: 709 lines

## Related Work

These lemmas support the larger correctness proof of the mark phase, specifically:
- `mark_aux` (iterative mark execution)
- `mark_aux_preserves_stack_props` (stack properties preservation)

The proofs integrate with existing lemmas about:
- `stack_props` (gray stack invariant)
- `tri_color_invariant` (no black→white pointers)
- Mark phase correctness (Pillar 2: Black ⟺ Reachable)
