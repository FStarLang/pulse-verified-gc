# Tri-Color Invariant Proof Summary

## Overview

This document summarizes the proof structure for `mark_step_preserves_tri_color` in `Spec/Pulse.Spec.GC.Mark.fst`.

## What Was Added

### 1. Helper Lemma: `push_children_preserves_tri_color`

**Location:** Lines 446-519

**Signature:**
```fstar
val push_children_preserves_tri_color : 
  (g: heap) -> (st: seq U64.t) -> (h_addr: hp_addr) -> 
  (i: U64.t{U64.v i >= 1}) -> (ws: U64.t) ->
  Lemma (requires well_formed_heap g /\ is_valid_header h_addr g /\
                  // Tri-color holds for all black objects EXCEPT possibly h_addr
                  (forall (b: hp_addr). Seq.mem b (objects 0UL g) /\ is_black b g /\ b <> h_addr ==>
                    (forall (s: vertex_id). Seq.mem s (get_pointer_fields g b) ==>
                      (U64.v s < heap_size /\ U64.v s % U64.v mword = 0 ==> not (is_white s g)))))
        (ensures tri_color_invariant (fst (push_children g st h_addr i ws)))
        (decreases (U64.v ws - U64.v i + 1))
```

**Key Insight:**
This lemma allows tri-color to be violated by ONE object (`h_addr`) temporarily. This is crucial because:
- After `makeBlack h_addr`, `h_addr` might point to white children (violating tri-color)
- But `push_children` will make those white children gray, restoring the invariant
- All OTHER black objects maintain tri-color throughout

**Proof Structure:**
- Base case (i > ws): All fields processed, tri-color restored
- Recursive case: For each field:
  - If pointer to white child: make it gray (one fewer violation)
  - Preserve "tri-color except h_addr" invariant
  - Recurse on remaining fields

**Current Status:** Uses `admit()` for final tri-color proof and assumes that `makeGray` preserves the partial tri-color invariant.

### 2. Main Lemma: `mark_step_preserves_tri_color`

**Location:** Lines 554-597

**Signature:**
```fstar
val mark_step_preserves_tri_color : 
  (g: heap) -> (st: seq U64.t{Seq.length st > 0 /\ is_val_addr (Seq.head st)}) ->
  Lemma (requires well_formed_heap g /\ stack_props g st /\ tri_color_invariant g)
        (ensures tri_color_invariant (fst (mark_step g st)))
```

**Proof Structure:**

#### Case 1: `is_no_scan h_addr g` (Lines 566-579)
- No-scan objects have NO pointer fields
- `get_pointer_fields g h_addr` returns empty sequence
- Therefore precondition of `makeBlack_preserves_tri_color_if_children_not_white` is trivially satisfied
- Making `h_addr` black preserves tri-color

**Status:** ✅ Complete (relies on existing `makeBlack_preserves_tri_color_if_children_not_white`)

#### Case 2: Normal object with children (Lines 580-595)
1. Make `h_addr` black: `g_black = makeBlack h_addr g`
   - At this point, tri-color MAY be violated (h_addr might point to white children)
   
2. Establish precondition for `push_children_preserves_tri_color`:
   - Need to show: tri-color holds for all black objects EXCEPT h_addr in g_black
   - This follows from: all black objects in `g` (except h_addr which was gray) still don't point to white
   
3. Call `push_children` to restore tri-color:
   - `push_children` makes all white children of `h_addr` gray
   - After this, `h_addr` no longer points to white
   - Result: full tri-color invariant restored

**Status:** Uses one `admit()` to establish that tri-color holds for all b ≠ h_addr after makeBlack.

## What Needs To Be Proven (TODOs)

### In `push_children_preserves_tri_color`:

1. **Final tri-color in base case** (Line 467):
   - After processing all fields (i > ws), prove `tri_color_invariant` holds
   - Need to show: all white children of h_addr have been made gray
   - Need to show: for all black objects b (including h_addr now), children are not white

2. **Preservation of partial tri-color after makeGray** (Line 488):
   - Currently uses `assume`
   - Need to prove: when we `makeGray child_hdr`, tri-color for b ≠ h_addr is preserved
   - This should follow from the existing `makeGray_preserves_tri_color` lemma, but needs adaptation

3. **Well-formedness preservation** (Lines 491-492):
   - Currently uses `assume (well_formed_heap g')`
   - Should be proven using existing color change lemmas

### In `mark_step_preserves_tri_color`:

4. **Tri-color for b ≠ h_addr after makeBlack** (Line 590):
   - Currently uses `admit()`
   - Need to prove: `makeBlack h_addr` preserves tri-color for all black objects b where b ≠ h_addr
   - Should factor out a lemma: `makeBlack_preserves_tri_color_for_other_objects`

### In `mark_preserves_tri_color`:

5. **Induction over mark** (Line 606):
   - Prove mark preserves tri-color by induction
   - Base case: empty stack → tri-color holds
   - Inductive step: use `mark_step_preserves_tri_color`

## Helper Lemmas That Would Be Useful

### 1. `makeBlack_preserves_tri_color_for_other_objects`
```fstar
val makeBlack_preserves_tri_color_for_other_objects : 
  (g: heap) -> (h_addr: hp_addr) ->
  Lemma (requires tri_color_invariant g)
        (ensures forall (b: hp_addr). b <> h_addr /\ is_black b (makeBlack h_addr g) ==>
                   (forall (s: vertex_id). Seq.mem s (get_pointer_fields (makeBlack h_addr g) b) ==>
                     not (is_white s (makeBlack h_addr g))))
```

This would help with the admit on line 590.

### 2. `makeGray_preserves_partial_tri_color`
```fstar
val makeGray_preserves_partial_tri_color : 
  (g: heap) -> (child_hdr: hp_addr) -> (h_addr: hp_addr) ->
  Lemma (requires (forall (b: hp_addr). b <> h_addr /\ is_black b g ==> 
                    (forall (s: vertex_id). Seq.mem s (get_pointer_fields g b) ==> not (is_white s g))))
        (ensures (forall (b: hp_addr). b <> h_addr /\ is_black b (makeGray child_hdr g) ==>
                   (forall (s: vertex_id). Seq.mem s (get_pointer_fields (makeGray child_hdr g) b) ==>
                     not (is_white s (makeGray child_hdr g)))))
```

This would replace the assume on lines 485-492.

## Proof Strategy for Remaining TODOs

### For TODO 1 (Final tri-color in base case):
- When i > ws, we've processed all fields from 1 to ws
- For each field that was a pointer to a white child, we made it gray
- Need to connect this to `get_pointer_fields g h_addr`
- Need to show: `forall s in get_pointer_fields g h_addr. not (is_white s (fst (push_children g st h_addr 1UL ws)))`

### For TODO 2 (Preservation after makeGray):
- Adapt the existing `makeGray_preserves_tri_color` lemma
- Key facts:
  - `makeGray` only changes color of `child_hdr`
  - Color changes don't affect `get_pointer_fields` (use existing lemmas)
  - For b ≠ h_addr: b's children colors unchanged except child_hdr (white → gray is OK)

### For TODO 4 (Tri-color for b ≠ h_addr after makeBlack):
- When we `makeBlack h_addr`:
  - h_addr was gray in g
  - All other objects' colors unchanged
  - For any b that was black in g (b ≠ h_addr):
    - b is still black in g_black
    - b's children colors unchanged (except possibly h_addr: gray → black is OK)
    - So b's children that were not white in g are still not white in g_black

### For TODO 5 (Induction over mark):
- Base case: st is empty → mark returns g unchanged → tri-color preserved trivially
- Inductive step:
  - Assume: mark preserves tri-color for stack of length n
  - Prove: mark preserves tri-color for stack of length n+1
  - Use: `mark_step_preserves_tri_color` for first step
  - Apply IH for remaining steps

## Verification Status

✅ **File typechecks successfully** with strategic `admit()` statements
✅ **Proof structure is sound** - the admits are in the right places
✅ **Key insights identified** - especially the "tri-color except h_addr" invariant
✅ **Clear path forward** - each TODO has a concrete proof strategy

## Testing

```bash
cd /home/eioannidis/git/verified_ocaml_gc/pulse-proofs
fstar.exe --include Spec --include Lib Spec/Pulse.Spec.GC.Mark.fst
```

Result: `Verified module: Pulse.Spec.GC.Mark` ✅

## Next Steps

1. Prove `makeBlack_preserves_tri_color_for_other_objects`
2. Prove `makeGray_preserves_partial_tri_color`  
3. Complete `push_children_preserves_tri_color` base case
4. Complete `mark_step_preserves_tri_color` case 2
5. Prove `mark_preserves_tri_color` by induction

Each of these can be tackled incrementally, replacing one `admit()` at a time.
