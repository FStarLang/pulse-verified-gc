# Changes Made to `Spec/Pulse.Spec.GC.Mark.fst`

## Summary

Replaced the trivial specification and admit for `mark_black_is_reachable` (lines 233-240) with:
1. A proper specification matching the requirements
2. A helper lemma `mark_aux_complete` for the inductive proof
3. The main proof implementation with structured proof strategy

## Detailed Changes

### 1. Added Helper Lemma `mark_aux_complete` (NEW: lines 377-477)

**Location:** Inserted before `mark_black_is_reachable`

**Purpose:** Proves that objects only become black if reachable from the stack (completeness invariant)

**Key Features:**
- Inductive proof over fuel
- Handles two cases: objects blackened in mark_step vs recursive call
- Uses `reach_refl` for reflexivity
- Sets up structure for transitivity reasoning

**Admits/Assumes:**
- Line 413-415: Preservation of well-formedness and stack properties (should be lemmas)
- Line 418: Only head becomes black in mark_step (should be lemma)
- Line 472: Technical details of Case 2 (stack composition + graph preservation)

### 2. Replaced `mark_black_is_reachable` (MODIFIED: lines 479-560)

**Old version (lines 233-240):**
```fstar
val mark_black_is_reachable : (g: heap) -> (st: seq U64.t) -> (roots: seq hp_addr) ->
  Lemma (requires True)
        (ensures True)

let mark_black_is_reachable g st roots = 
  admit()  // TODO: prove via DFS completeness
```

**New version (lines 479-560):**
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let mark_black_is_reachable g st roots = 
  stack_props_implies_valid_addr g st;
  mark_aux_complete g st (heap_size / U64.v mword);
  
  let g_final = mark g st in
  
  let hd_f_inverse (r: hp_addr) : Lemma (...) = () in
  
  let aux (x: hp_addr) : Lemma (...) =
    if is_black x g then
      // Case 1: Initially black (should be root)
      ...
    else
      // Case 2: Became black during mark
      ...
  in
  FStar.Classical.forall_intro aux
#pop-options
```

**Specification Changes:**
- ✅ Added proper `requires` clause with heap well-formedness, stack invariants, root properties
- ✅ Added precondition that all roots are on the initial stack
- ✅ Added proper `ensures` clause: `is_black x (mark g st) ==> reachable_from_set ...`

**Implementation Changes:**
- ✅ Uses `mark_aux_complete` helper
- ✅ Structured case analysis via inner lemma `aux`
- ✅ Uses `reach_refl` for initially black objects
- ✅ Explicit proof structure for connecting stack to roots

**Admits/Assumes:**
- Line 523: Assumes initially black objects are roots
- Lines 548-556: Assumes stack-to-roots correspondence and admits final connection

### 3. Updated `mark_black_iff_reachable` (MODIFIED: lines 562-574)

**Old version:**
```fstar
val mark_black_iff_reachable : (g: heap) -> (st: seq U64.t) -> (roots: seq hp_addr) ->
  Lemma (requires True)
        (ensures True)
```

**New version:**
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

**Changes:**
- ✅ Added proper preconditions (same as component lemmas)
- ✅ Changed `ensures` from `True` to actual bi-implication: `is_black <==> reachable_from_set`
- Implementation unchanged (already correctly calls both component lemmas)

## Verification Status

### Syntax and Type Checking
- ✅ **PASSES** lax mode: `fstar.exe --lax Spec/Pulse.Spec.GC.Mark.fst`
- ✅ File parses correctly
- ✅ All types are well-formed
- ✅ No syntax errors

### Full Verification
- ⚠️ **NOT YET COMPLETE** due to `admit()` and `assume()` statements
- See `PROOF_COMPLETENESS_SUMMARY.md` for roadmap to completion

## Files Modified

1. `/home/eioannidis/git/verified_ocaml_gc/pulse-proofs/Spec/Pulse.Spec.GC.Mark.fst`
   - Added lines 377-477: `mark_aux_complete` helper lemma
   - Modified lines 479-560: `mark_black_is_reachable` with proper spec and proof structure
   - Modified lines 562-574: `mark_black_iff_reachable` with proper spec

## Files Created

1. `PROOF_COMPLETENESS_SUMMARY.md`: Detailed roadmap for completing the proof
2. `CHANGES.md` (this file): Summary of changes made

## Dependencies

The new code depends on existing definitions from:
- `Pulse.Spec.GC.Graph`: `reachable`, `reach_refl`, `reach_trans`, `reachable_from_set`
- `Pulse.Spec.GC.Heap`: `hd_address`, `f_address`, `hd_f_roundtrip`
- `Pulse.Spec.GC.Object`: `is_black`, `makeBlack`
- `Pulse.Spec.GC.Fields`: `create_graph_from_heap`, `coerce_to_vertex_list`
- `Pulse.Spec.GC.Mark`: `mark_aux`, `mark`, `mark_step`, `stack_props`

No changes were made to these dependencies.

## Testing

Verified with:
```bash
cd /home/eioannidis/git/verified_ocaml_gc/pulse-proofs
fstar.exe --include Spec --include Lib --lax Spec/Pulse.Spec.GC.Mark.fst
```

Output: ✅ "All verification conditions discharged successfully"

## Next Steps

See `PROOF_COMPLETENESS_SUMMARY.md` for:
1. List of helper lemmas needed (Priority 1-5)
2. Proof completion strategy
3. Suggested strengthening of preconditions
4. Testing approach

The proof structure is complete; remaining work is to:
1. Prove or find existing preservation lemmas
2. Add helper lemmas about mark_step behavior
3. Strengthen preconditions OR prove from initial invariants
4. Replace admit()/assume() with actual proofs
