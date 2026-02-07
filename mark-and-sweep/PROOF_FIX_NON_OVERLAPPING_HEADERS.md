# Proof Fix: Non-Overlapping Headers

## Problem

In `Spec/Pulse.Spec.GC.Mark.fst`, line 471-472, there was an `assume` statement:

```fstar
assume (U64.v child_hdr + U64.v mword <= U64.v h_addr2 \/
        U64.v h_addr2 + U64.v mword <= U64.v child_hdr);
```

This assumption was needed to prove that two distinct heap object headers don't overlap in memory, which is required by `makeGray_preserves_gray_elsewhere`.

## Context

- **Location**: `push_children_preserves_existing_gray` lemma
- **Variables**:
  - `child_hdr`: header address of a white object (type `hp_addr`)
  - `h_addr2`: header address of a gray object (type `hp_addr`)
- **Known fact**: `child_hdr <> h_addr2` (proved by `white_gray_disjoint`)
- **Required**: The headers must be at least `mword` (8 bytes) apart

## Solution

Replaced the `assume` with a call to the existing lemma `aligned_distinct_distance`:

```fstar
// Before:
white_gray_disjoint child_hdr h_addr2 g;
assume (U64.v child_hdr + U64.v mword <= U64.v h_addr2 \/
        U64.v h_addr2 + U64.v mword <= U64.v child_hdr);

// After:
white_gray_disjoint child_hdr h_addr2 g;  // Proves: child_hdr <> h_addr2
aligned_distinct_distance child_hdr h_addr2;  // Proves: they're mword apart
```

## Key Lemma Used

From `Spec/Pulse.Spec.GC.Fields.fst`, lines 434-445:

```fstar
/// Helper: word-aligned distinct addresses are at least mword apart
let aligned_distinct_distance (a b: hp_addr)
  : Lemma (requires a <> b)
          (ensures U64.v a + U64.v mword <= U64.v b \/ 
                   U64.v b + U64.v mword <= U64.v a)
  = // hp_addr = n:U64.t{v n % v mword = 0 /\ v n < heap_size}
    // If a % mword = 0 and b % mword = 0 and a <> b
    // Then |a - b| is a multiple of mword, so >= mword
    assert (U64.v a % U64.v mword = 0);
    assert (U64.v b % U64.v mword = 0);
    if U64.v a < U64.v b then
      assert (U64.v b - U64.v a >= U64.v mword)
    else
      assert (U64.v a - U64.v b >= U64.v mword)
```

## Why This Works

1. **Type guarantee**: `hp_addr` is defined with word-alignment:
   ```fstar
   type hp_addr = a:U64.t{
     U64.v a >= 0 /\ 
     U64.v a < heap_size /\ 
     U64.v a % U64.v mword == 0  // Word-aligned
   }
   ```

2. **Mathematical fact**: Two distinct word-aligned addresses must differ by at least one word (8 bytes)

3. **Proof chain**:
   - `white_gray_disjoint` establishes `child_hdr <> h_addr2`
   - Both are `hp_addr`, so both are word-aligned
   - `aligned_distinct_distance` uses this to prove they're at least `mword` apart

## Verification Result

The file now verifies successfully with F*:

```
$ fstar.exe --cache_checked_modules --warn_error -321 --include Spec --include Lib \
    Spec/Pulse.Spec.GC.Mark.fst

Verified module: Pulse.Spec.GC.Mark
All verification conditions discharged successfully
```

## Impact

This removes one `assume` from the codebase, making the proof more complete and trustworthy. The non-overlapping property of heap headers is now formally proven rather than assumed.

## Related Lemmas

For reference, other header separation lemmas in `Spec/Pulse.Spec.GC.Fields.fst`:

1. **`objects_header_separation`** (lines 390-406): Proves header separation when ordering is known
   - Requires: `h_addr1 < h_addr2` and both in heap
   - Ensures: `h_addr1 + mword <= h_addr2`

2. **`aligned_distinct_distance`** (lines 434-445): Proves bidirectional separation
   - Requires: `a <> b` (both `hp_addr`)
   - Ensures: `a + mword <= b \/ b + mword <= a`

3. **`objects_separated`** (lines 84-92): High-level heap well-formedness property
   - Ensures objects don't overlap in well-formed heaps
