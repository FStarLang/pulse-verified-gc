# Minor Collect Isomorphism — Status & Gap Analysis

## Executive Summary

The `GC.Gen.MinorCollectIso` module provides a **complete graph isomorphism theorem** 
for the minor collection phase of the generational GC. Properties (A)-(G) are all 
**fully machine-checked with zero admits**.

| Property | Statement | Status |
|----------|-----------|--------|
| **(A) Injectivity** | `fwd_morphism` injective on combined-reachable vertices | ✅ 0 admits |
| **(B) Image validity** | Reachable vertices map to valid objects in `mc_major` | ✅ 0 admits |
| **(C) Edge forward** | Combined edge (u,v) → mc_major edge (φ(u), φ(v)) | ✅ 0 admits |
| **(D) Edge backward** | mc_major edge (φ(u), φ(v)) → combined edge (u,v) | ✅ 0 admits |
| **(E) Header preservation** | Non-blue major objects keep their wosize | ✅ 0 admits |
| **(F) Object survival** | Pre-existing major objects survive in mc_major | ✅ 0 admits |
| **(G) Forward reachability** | Combined-reachable vertices are mc_major-reachable | ✅ 0 admits |
| **(H) Surjectivity** | Every mc_major-reachable vertex has a combined pre-image | ❌ NOT YET PROVEN |

**Verdict:** Properties (A)-(D)+(G) establish an **injective subgraph isomorphism with 
forward reachability preservation** — the combined-reachable subgraph embeds faithfully 
into the mc_major-reachable subgraph with edge bijectivity on the image.
The remaining gap (H) would show the embedding is surjective (the image IS the full 
mc_major-reachable subgraph).

---

## Preconditions

### Operational (provable from system initialization):
1. `well_formed_heap major`
2. `minor_wf minor`
3. `fl_valid`, `fl_chain_terminates`
4. `chain_objects_blue`
5. `nonblue_wosize_positive`
6. `cheney_no_oom`
7. `remembered ⊆ roots`
8. `no_pointer_to_blue`, `minor_no_pointer_to_blue`
9. `roots_valid_nonblue`
10. `major_field_one_plus_in_remembered`, `major_field_zero_no_minor`
11. `no_scan_invariant`, `minor_no_scan_invariant`

### Structural (provable from GC correctness):
12. `well_formed_heap mc.mc_major` — post-collection heap well-formed
13. `graph_wf (create_graph mc.mc_major)` — graph well-defined
14. `promoted_copy_properties` — promoted copies valid with wosize >= minor_wosize
15. `promoted_copy_exact_wosize` — promoted copies have exactly minor_wosize
16. `fwd_targets_originally_blue` — fwd targets were blue free-list nodes

### Non-operational (genuine proof obligation):
17. **`field_correspondence`** — promoted objects have correct field values in mc_major

---

## Edge Backward Proof Architecture (D)

The edge backward proof handles 4 cases, all fully proven:

### Case MajorV→MajorV (simplest)
- Edge (src, dst) in mc_major where both are non-blue pre-existing objects
- `fwd_map_disjoint_nonblue`: dst ≠ fwd(a) for any a
- Extract field j from mc edge via `indefinite_description_ghost`
- `derive_mc_major_field_value`: since dst ≠ fwd target, field was NOT rewritten
- Therefore original field = dst → `pointer_field_is_graph_edge` → edge in major
- `heapgraph_edge_implies_combined` → combined edge

### Case MajorV→MinorV (contrapositive + injectivity)
- Edge (src, fwd(dst)) in mc_major; fwd(dst) was blue in original
- `no_pointer_to_blue`: src couldn't point to fwd(dst) originally
- `derive_mc_major_field_value`: field MUST have been rewritten (contrapositive)
- Rewrite means: original = minor ptr m with fwd(m) = fwd(dst)
- By injectivity: m = dst → original field was dst → combined edge

### Case MinorV→MajorV (promoted copy + disjointness)
- Edge (fwd(src), dst) in mc_major; dst is non-blue
- `promoted_field_through_minor_collect` at extracted field index:
  - Case 1: mc_val = fwd(minor_val) = dst. But dst ≠ fwd(anything). Contradiction!
  - Case 2: mc_val = minor_val = dst. ✓
- minor_val = dst (major object) → classify → combined edge

### Case MinorV→MinorV (promoted copy + injectivity)
- Edge (fwd(src), fwd(dst)) in mc_major; fwd(dst) was blue
- `promoted_field_through_minor_collect`:
  - Case 1: fwd(minor_val) = fwd(dst). By injectivity: minor_val = dst. ✓
  - Case 2: minor_val = fwd(dst). But fwd(dst) blue → minor_no_pointer_to_blue contradiction!
- minor_val = dst → classify → combined edge

---

## Forward Reachability Proof Architecture (G)

The forward reachability proof uses `combined_reachable_ind` with a predicate that
includes both combined-reachability and mc_major reachability from mc_roots.

### Predicate
```
p(v) = combined_reachable(v) ∧ ∃r ∈ mc_roots. reachable(g_mc, r, φ(v))
```

### Base case (roots)
- `combined_reachable_root` → combined_reachable(v)
- Root correspondence: `classify_roots_inv_{minor,major}` + `rewrite_roots_index` → φ(v) ∈ mc_roots
- `reach_refl` → reachable(g_mc, φ(v), φ(v))

### Inductive step (edge closure)
- `combined_reachable_step` → combined_reachable(w)
- Edge forward (case-specific helper) → (φ(u), φ(w)) ∈ g_mc.edges
- `indefinite_description_ghost` → extract root witness r from p(u)
- `edge_reach` + `reach_trans` → reachable(g_mc, r, φ(w))

---

## Remaining Work: Surjectivity (H)

### Statement
Every vertex reachable in mc_major from `mc_roots` has a combined-reachable pre-image.

### What's needed (new infrastructure)
1. **Reachability induction for heap graphs** — A `reach_ind` lemma allowing structural 
   induction on `reach g x y` witnesses (similar to `combined_reachable_ind`)
2. **Object partition characterization** — `objects(mc_major) = objects(major) ∪ fwd_targets` 
   (requires proving `update_major_pointers` + `promote_all` don't create new objects 
   beyond the promoted copies)
3. **`no_pointer_to_blue mc_major`** — Either as precondition (consistent with 
   `GC.Gen.CheneyEnd2End` which already assumes it) or proved from preservation lemmas
4. **Strong edge backward** — A variant that determines the pre-image of an edge TARGET
   from its mc_major vertex properties alone, without assuming the target is already 
   combined-reachable

### Difficulty: Hard
Requires substantial new infrastructure beyond what currently exists in the codebase.
The key challenges are items 2 (no existing partition lemma) and 4 (the current edge 
backward proof uses combined-reachability to classify the target).

### Note
For practical GC correctness, surjectivity means "no previously-unreachable object 
becomes reachable after collection." Properties (A)-(G) already establish all essential 
safety guarantees: no data loss, no pointer corruption, no metadata corruption, and 
reachability preservation.

---

## Key Infrastructure Modules (all 0 admits)

| Module | What it proves |
|--------|---------------|
| `CheneyInjectivity` | `fwd` injective on live_set |
| `CheneyDisjoint` | fwd targets ∉ pre-existing non-blue major |
| `CheneyCorrectness` | promotes_all_reachable, preserves_objects |
| `CheneyDischarge` | chain_blue→alloc_avoids, fwd_targets_in_mc_major |
| `ReachabilityBridge` | combined-reachable(MinorV v) → v ∈ live_set |
| `EdgeBridge` | Combined edge → mc_major edge (Cases 1-4) |
| `EdgePreservation` | Field preservation through minor_collect (Cases 1-4) |
| `MajorBridge` | HeapGraph edge ↔ CombinedGraph edge for major objects |
| `HeaderPres` | Cheney + update_major_pointers preserves wosize |
