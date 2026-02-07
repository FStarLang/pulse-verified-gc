# Proof Fix: push_children_preserves_parent_color

## Summary

Successfully removed the `assume` statements in the `push_children_preserves_parent_color` lemma in `Spec/Pulse.Spec.GC.Mark.fst` by providing complete formal proofs using color locality lemmas.

## Problem

The lemma had two `assume` statements at lines 239 and 243:
```fstar
assume (color_of_object h_addr g' == c);
```

These assumes were placeholders that needed to be proven.

## Key Insight

The proof relies on the following reasoning:

1. When `child_hdr` is white and `h_addr` has color `c ≠ white`, they must be different addresses
2. Different aligned addresses are at least `mword` apart (by `aligned_distinct_distance`)
3. Therefore, `color_change_locality` applies: changing the color at `child_hdr` doesn't affect `h_addr`
4. When we don't enter the inner conditional, `g' == g`, so the color is trivially preserved

## Solution

The fix places the proof logic directly in the control flow where `g'` is bound:

```fstar
let rec push_children_preserves_parent_color g st h_addr i ws c =
  if U64.v i > U64.v ws then ()
  else begin
    let v = get_field g h_addr i in
    let (g', st') =
      if is_pointer_field v then
        let child_hdr = hd_address v in
        if is_valid_header child_hdr g && is_white child_hdr g then begin
          // Proof that color is preserved when making child gray
          assert (is_white child_hdr g);
          assert (color_of_object h_addr g == c);
          assert (c <> white);
          assert (child_hdr <> h_addr);  // Different colors → different addresses
          aligned_distinct_distance child_hdr h_addr;  // Distance ≥ mword
          let g'' = makeGray child_hdr g in
          color_change_locality child_hdr h_addr g gray;  // Locality applies
          assert (color_of_object h_addr g'' == c);
          let st'' = Seq.cons v st in
          (g'', st'')
        end else
          (g, st)
      else
        (g, st)
    in
    // Now proven: color_of_object h_addr g' == c
    assert (color_of_object h_addr g' == c);
    if U64.v i < U64.v ws then
      push_children_preserves_parent_color g' st' h_addr (U64.add i 1UL) ws c
  end
```

## Lemmas Used

1. **`aligned_distinct_distance`** (from `Pulse.Spec.GC.Fields`):
   - Proves that distinct aligned addresses are at least `mword` apart
   ```fstar
   val aligned_distinct_distance : (a b: hp_addr) ->
     Lemma (requires a <> b)
           (ensures U64.v a + U64.v mword <= U64.v b \/ 
                    U64.v b + U64.v mword <= U64.v a)
   ```

2. **`color_change_locality`** (from `Pulse.Spec.GC.Object`):
   - Proves that color changes at one address don't affect other addresses
   ```fstar
   val color_change_locality : (h_addr1: hp_addr) -> (h_addr2: hp_addr) -> 
                               (g: heap) -> (c: U64.t{U64.v c < 4}) ->
     Lemma (requires h_addr1 <> h_addr2 /\
                     (U64.v h_addr1 + U64.v mword <= U64.v h_addr2 \/
                      U64.v h_addr2 + U64.v mword <= U64.v h_addr1))
           (ensures color_of_object h_addr2 (set_object_color h_addr1 g c) == 
                    color_of_object h_addr2 g)
   ```

3. **Implicit color disjointness**:
   - F* automatically proves that if `is_white x g` and `color_of_object y g == c` 
     with `c ≠ white`, then `x ≠ y`

## Verification Result

✅ **All verification conditions discharged successfully**

The file now verifies completely with F* without any assumes:
```
fstar.exe --cache_checked_modules --warn_error -321 --include Spec --include Lib \
  Spec/Pulse.Spec.GC.Mark.fst
```

Output: `Verified module: Pulse.Spec.GC.Mark` with all conditions discharged.

## Files Modified

- `Spec/Pulse.Spec.GC.Mark.fst`: Lines 219-253 (function `push_children_preserves_parent_color`)

## Impact

This completes the proof that `push_children` preserves the color of the parent object, which is essential for:
- Proving that `mark_step` correctly maintains the black color of the object being processed
- Establishing color monotonicity during the mark phase
- Supporting the tri-color invariant preservation
