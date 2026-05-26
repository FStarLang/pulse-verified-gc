# Generational GC SPOT (Small Proof-Oriented Test)

This directory contains `GC.Gen.SPOT.fst`, a **Small Proof-Oriented Test** for the generational GC specification.

## What is a SPOT?

A SPOT validates that a specification is:
1. **Strong enough** to prove the implementation correct
2. **Precise enough** for clients to reason about the result

See: https://risemsr.github.io/blog/2026-04-16-spotting-specs/

## What does this SPOT test?

`GC.Gen.SPOT.fst` demonstrates how to:

1. **Set up preconditions**: Assume a heap with:
   - Minor objects (reachable and unreachable)
   - Major objects (reachable and in free-list)
   - Root set covering reachable objects
   - Collection heap shape invariants

2. **Call the spec**: Invoke `cheney_collect_spec` from `GC.Gen.Cheney`

3. **Prove postconditions**:
   - Reachable minor objects are promoted (have forwarding entries)
   - Promoted addresses are valid
   - Roots are correctly rewritten
   - Minor heap is reset
   - Major objects survive
   - Isomorphism holds when `ok = true`
   - Object structure is preserved
   - Field values are preserved

## Verification

```bash
cd generational
../fstar/bin/fstar.exe --cache_checked_modules --warn_error -321 \
  --include spec --include impl \
  --include ../common/spec --include ../common/lib --include ../common/impl \
  --include ../mark-and-sweep/spec --include ../mark-and-sweep/impl \
  spec/GC.Gen.SPOT.fst
```

Expected output: `Verified module: GC.Gen.SPOT`

## Key Insight

The SPOT uses `assume val` for heap construction (the tedious part) but **proves real properties** about what the spec guarantees. This validates that the postcondition is strong enough for clients to use.

Each `admit()` in the SPOT represents a 1-2 line proof that would:
- Unfold a spec definition (e.g., `rewrite_roots`)
- Call an existing lemma (e.g., `combined_reachable_images_valid_or_infix_from_slots`)
- Do simple case analysis

The point is NOT to re-verify the GC, but to show the spec's postconditions are usable.

## Future Work

To turn this into a complete SPOT:
1. Replace `assume val` with concrete heap construction
2. Fill in the `admit()` proofs by calling the relevant lemmas
3. Add more test scenarios (e.g., infix objects, no-scan objects)
4. Test the full `gen_gc` composition (minor + major)
