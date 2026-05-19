# Minor Collect Isomorphism — Status & Gap Analysis

## Executive Summary

The `GC.Gen.MinorCollectIso` module provides a **near-complete graph isomorphism theorem** 
for the minor collection phase of the generational GC. Properties (A)-(F) are all 
**fully machine-checked with zero admits**.

| Property | Statement | Status |
|----------|-----------|--------|
| **(A) Injectivity** | `fwd_morphism` injective on combined-reachable vertices | ✅ 0 admits |
| **(B) Image validity** | Reachable vertices map to valid objects in `mc_major` | ✅ 0 admits |
| **(C) Edge forward** | Combined edge (u,v) → mc_major edge (φ(u), φ(v)) | ✅ 0 admits |
| **(D) Edge backward** | mc_major edge (φ(u), φ(v)) → combined edge (u,v) | ✅ 0 admits |
| **(E) Header preservation** | Non-blue major objects keep their wosize | ✅ 0 admits |
| **(F) Object survival** | Pre-existing major objects survive in mc_major | ✅ 0 admits |
| **(C') Surjectivity** | Every reachable mc_major vertex has a combined pre-image | ❌ NOT YET PROVEN |

**Verdict:** We have an **injective graph isomorphism on the edge structure** — a bijective 
correspondence between combined-graph edges and mc_major edges for reachable vertices.
The remaining gap (C') would complete a full graph isomorphism.

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

## Remaining Work: Surjectivity (C')

### Statement
Every vertex reachable in mc_major from `mc_roots` has a combined-reachable pre-image.

### Approach
1. Prove `mc_major_objects_partition`: objects in mc_major are either pre-existing 
   or fwd targets
2. Pre-existing non-blue → pre-image MajorV, promoted → pre-image MinorV
3. Key difficulty: reconstruct combined-reachability from mc_major reachability
   (path induction using edge backward at each step)

### Difficulty: Medium-Hard
The main challenge is the inductive argument over mc_major paths. Edge backward (D) 
provides the single-step correspondence, but combining it into full path preservation 
requires an induction principle for `reachable_from` in the heap graph.

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
