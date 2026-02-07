# Proof Status: color_change_preserves_objects_aux

## Goal
Prove: `objects start (set_object_color obj g c) == objects start g`

## Challenge
`set_object_color` is opaque (defined only in .fsti), making it difficult for Z3 to reason about equality through recursive function calls.

## Current Proof Structure

```fstar
#push-options "--z3rlimit 800 --fuel 6 --ifuel 2"
let rec color_change_preserves_objects_aux start g obj c =
  set_object_color_length obj g c;
  let g' = set_object_color obj g c in
  if U64.v start + 8 >= Seq.length g then ()
  else begin
    let header = read_word g start in
    let header' = read_word g' start in
    
    // Case split on whether we're at obj's header
    if hd_address obj = start then begin
      color_preserves_wosize obj g c;
      wosize_of_object_spec obj g;
      wosize_of_object_spec obj g'
    end else begin
      color_change_header_locality obj start g c
    end;
    
    // Compute next position (same for both heaps)
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
    
    // Recurse with induction hypothesis
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else if next_start_nat >= heap_size then ()
    else begin
      let next_start : hp_addr = U64.uint_to_t next_start_nat in
      color_change_preserves_objects_aux next_start g obj c
    end
  end
```

## Status
**INCOMPLETE** - Fails with "unknown because (incomplete quantifiers)"

The proof is structurally correct and calls all necessary lemmas, but Z3 cannot automatically complete the quantifier instantiation to prove the recursive equality.

## Attempted Solutions
1. ✗ Explicit assertions guiding SMT
2. ✗ Higher fuel (3-6) and rlimit (500-2000)
3. ✗ Intermediate let-bindings
4. ✗ Helper congruence lemmas
5. ✗ Different proof orderings

## Working Reference
A similar proof (`color_change_preserves_objects_at`) exists in `fly/Pulse.Spec.GC.TriColor.fst` with nearly identical structure, suggesting this approach should work.

## Possible Next Steps
1. Check if there are differences in the opacity/inlining attributes between `set_color` (fly) and `set_object_color` (common)
2. Add intermediate lemmas about single-step unfolding of `objects`
3. Use Seq.equal + lemma_eq_elim for extensional equality
4. Add SMT pattern annotations to guide quantifier instantiation
5. Consult F* experts about handling opaque recursive functions

## Files
- Proof: `/home/eioannidis/ocaml-gc/common/Spec/Pulse.Spec.GC.Fields.fst` (lines 731-774)
- Opaque function: `/home/eioannidis/ocaml-gc/common/Spec/Pulse.Spec.GC.Object.fsti` (set_object_color)
- Reference proof: `/home/eioannidis/ocaml-gc/fly/Pulse.Spec.GC.TriColor.fst` (color_change_preserves_objects_at)
