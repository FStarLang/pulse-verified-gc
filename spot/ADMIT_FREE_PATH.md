# Path to Fully Admit-Free 3-Object SPOT

## Current Status (After This Session)

- ✅ 1 lemma proven without admits: `slots_distinct_lemma` 
- ⚠️ 8 lemmas still have admits (precondition establishment)
- ⚠️ 0 postcondition property proofs

## Two Viable Paths Forward

### Path A: Concrete Heap Construction (Most Rigorous)

**Effort:** ~800-1200 lines, ~10-15 hours

Fully construct the 3-object heap byte-by-byte:

```fstar
// 1. Define headers
let hd_A : U64.t = make_header 1 White closure_tag  
let hd_B : U64.t = make_header 1 White closure_tag
let hd_C : U64.t = make_header 2 White closure_tag

// 2. Write to byte sequences  
let minor_with_A = write_word (Seq.create minor_heap_size 0uy) 0 hd_A
let minor_with_A_B = write_word minor_with_A 16 hd_B
// ... etc

// 3. Prove all heap invariants
let obj_A_is_valid () : Lemma (...) = ...
let obj_B_is_valid () : Lemma (...) = ...
let obj_C_is_valid () : Lemma (...) = ...
let obj_C_field_0_is_A () : Lemma (...) = ...
```

Then prove all 9 precondition lemmas from these concrete facts.

**Pros:**
- Maximum rigor - proves heap is actually constructible
- No assumes about heap structure
- Validates preconditions are truly not too strong

**Cons:**
- Very tedious
- Lots of low-level byte manipulation
- Not fundamentally different from what allocator already does

### Path B: Targeted Property Assumes (SPOT Pragmatic)

**Effort:** ~200-400 lines, ~3-5 hours

Keep heap as `assume val` but add specific, checkable assumes:

```fstar
// Clear, checkable properties
assume val obj_A_header_valid : unit -> Lemma (
  read_word three_obj_minor_data 0 == make_header 1 White closure_tag)

assume val obj_C_field_0_value : unit -> Lemma (
  read_word three_obj_major_data (U64.v obj_C + 8) == obj_A)

// ... etc
```

Then prove complex predicates from these simple properties:

```fstar
let ref_table_sound_lemma (...) : Lemma (...) =
  obj_C_is_obj_addr ();
  obj_C_field_0_value ();
  slot_addr_is_c_field_0 ();
  // Now SMT can prove ref_table_sound
  ()
```

**Pros:**
- Less tedious than byte-by-byte construction
- Still demonstrates what properties are needed
- Separates concerns (heap structure vs. predicate proofs)
- Standard SPOT methodology (fixture assumes + API tests)

**Cons:**
- Doesn't prove heap is constructible (assumes it)
- More assumes (but each is simple and checkable)

## Postcondition Property Proofs

Regardless of path chosen, need to add (~100-200 lines):

```pulse
// After GC call, use isomorphism to prove:
with md2 mb2 ms2 fp2. assert (is_gen_heap gh md2 mb2 ms2 fp2);

// Extract isomorphism witnesses  
with iso_witnesses. assert (isomorphism_property ...);

// Prove end-to-end properties:
// 1. A is promoted (in ms2, not in md2)
// 2. B is collected (not in md2 or ms2)  
// 3. C's field updated to promoted A
// 4. Minor bump reset to 0
```

This is the **critical part** that validates postconditions are useful.

## Recommendation

**Start with Path B** (pragmatic SPOT):
1. Add ~30 targeted property assumes
2. Prove 8 precondition lemmas from those (~100 lines)
3. Add postcondition property proofs (~150 lines)  
4. **Total:** ~250 lines, 3-5 hours

If needed later, can upgrade to Path A for maximum rigor.

## Why Path B Is Valid SPOT Methodology

SPOTs (Small Proof-Oriented Tests) from "Spotting Specs" blog:
- Goal: Test API is callable and usable
- Test fixtures can use assumes (like unit test setup)
- Key: Actual test code (GC call + property proofs) has NO admits
- Shows: Preconditions satisfiable, postconditions useful

Path B follows this - fixture uses assumes, but proves preconditions
are satisfiable and postconditions enable proving desired properties.
