# Minor Collect Isomorphism — Status & Gap Analysis

## Executive Summary

We have **two** isomorphism theorems with complementary strengths and weaknesses:

| Module | Postcondition | Preconditions | Status |
|--------|--------------|---------------|--------|
| **MinorCollectIso** | Partial (A+B+E+F) | Honest (operational + field_corr) | 0 admits ✅ |
| **Isomorphism.TopLevel** | Full (A+B+C+D) | Circular (assumes the conclusion) | 0 admits, but trivial ⚠️ |

**Neither proves a genuine isomorphism under honest preconditions.**

---

## What MinorCollectIso Actually Proves

Target: `mc_major` (post-Cheney BFS, pre-mark/sweep).

| Property | Statement | Proved? |
|----------|-----------|---------|
| **(A) Injectivity** | `fwd_morphism` injective on combined-reachable vertices | ✅ |
| **(B) Image validity** | Reachable vertices map to valid objects in `mc_major` | ✅ |
| **(C) Edge forward** | Combined edge (u,v) → mc_major edge (φ(u), φ(v)) | ❌ NOT PROVEN |
| **(D) Edge backward** | mc_major edge (φ(u), φ(v)) → combined edge (u,v) | ❌ NOT PROVEN |
| **(C') Surjectivity** | Every reachable mc_major vertex has a combined pre-image | ❌ NOT PROVEN |
| **(E) Header preservation** | Non-blue major objects keep their wosize | ✅ |
| **(F) Object survival** | Pre-existing major objects survive in mc_major | ✅ |

**Verdict:** We have an injective map with valid images — an *embedding*, not an isomorphism.
Without edge preservation (C/D) and surjectivity (C'), we cannot claim structural equivalence.

---

## What Isomorphism.TopLevel Proves

Target: `h_final` (post-mark/sweep — the fully collected heap).

It proves the full `reachable_subgraph_isomorphism` (A+B+C+D) **BUT** requires:

1. `iso_structural_preconditions` (7 sub-properties including injectivity, image, field_correspondence, reachability bridge, promoted disjoint, reachable major valid, morphism image preservation)
2. `iso_edge_bridge_forward` (combined edge → mc_major edge for all 4 cases)
3. `iso_surjectivity` (mc-reachable → has combined pre-image)
4. `iso_edge_backward` (mc edge → combined edge)

**These preconditions ARE the isomorphism!** The "theorem" is essentially:
```
If φ is an isomorphism, then φ is an isomorphism.
```

---

## The Infrastructure We Already Have (all 0 admits)

| Module | What it proves |
|--------|---------------|
| `CheneyInjectivity` | `fwd` injective on live_set |
| `CheneyDisjoint` | fwd targets ∉ pre-existing non-blue major |
| `CheneyCorrectness` | cheney_promotes_all_reachable, preserves_objects |
| `ReachabilityBridge` | combined-reachable(MinorV v) → v ∈ live_set |
| `Reachability` | minor_reachable_mono (monotonicity) |
| `EdgeBridge` | Combined edge → mc_major edge (Cases 1-4) |
| `EdgePreservation` | Field preservation through minor_collect (Cases 1-4) |
| `MajorBridge` | HeapGraph edge ↔ CombinedGraph edge for major objects |
| `MarkSweepFrame` | Mark/sweep preserves reachable-graph structure |
| `HeaderPres` | Cheney + update_major_pointers preserves wosize |
| `CheneyDischarge` | chain_blue → alloc_avoids, fwd_targets_in_mc_major |

---

## Gap Analysis: What's Missing for a Real Isomorphism

### Gap 1: Edge Preservation (C) — Combined edge → mc_major edge

**Infrastructure exists:** `EdgeBridge` already proves all 4 cases:
- Case 4 (Major→Major): `bridge_case_major_major`
- Case 3 (Major→Minor): `bridge_case_major_minor`
- Cases 1&2 (Minor→*): `bridge_case_minor`

**What's needed:** A top-level universal quantifier that:
1. Takes any combined edge (u,v) where both endpoints are reachable
2. Case-splits on (u,v) being (MajorV,MajorV), (MajorV,MinorV), (MinorV,MinorV), or (MinorV,MajorV)
3. Establishes the per-case preconditions of EdgeBridge from operational preconditions
4. Concludes (φ(u), φ(v)) is an edge in `create_graph mc_major`

**Key preconditions EdgeBridge needs (beyond operational):**
- `chain_avoids major fp src` — each source object avoids the free list
- `Seq.mem src (objects zero_addr prom_res.major_final)` — source survives promotion
- `wosize_of_object src prom_res.major_final == wosize_of_object src major` — header preserved
- `well_formed_heap mc.mc_major` — post-collection heap is well-formed
- `graph_wf (create_graph mc.mc_major)` — graph construction well-defined
- `field_correspondence` — (already a precondition in MinorCollectIso!)

**Difficulty:** Medium. The per-case lemmas exist. The main work is:
- Proving `chain_avoids` for all reachable non-blue objects (from `chain_objects_blue`)
- Proving source objects survive promotion with preserved headers (from Cheney preservation lemmas)
- Proving `well_formed_heap mc.mc_major` (exists as `cheney_collect_well_formed` or similar)
- Proving `graph_wf (create_graph mc.mc_major)` (follows from well_formed_heap)

### Gap 2: Surjectivity (C') — mc_major reachable → has pre-image

**Statement:** Every vertex in mc_major reachable from `post_gc_roots` is either:
- A pre-existing major object (pre-image = MajorV v), OR
- A promoted copy `fwd(m)` for some m (pre-image = MinorV m)

**Why this should be provable:**
- mc_major = major after (promote_all + update_major_pointers)
- `objects zero_addr mc_major` = `objects zero_addr major` ∪ {newly allocated by promote}
- The newly allocated = {fwd(m) | m ∈ live_set, fwd(m) ≠ 0}
- Pre-existing major objects have pre-image MajorV v (trivially)
- Promoted copies have pre-image MinorV m (by construction)
- Need: if w is reachable in mc_major, then w ∈ objects(mc_major) — YES, by graph construction

**What's needed:**
1. A lemma: `objects zero_addr mc_major ⊆ (objects zero_addr major) ∪ {fwd(m) | ...}`
2. Combined with: pre-existing → MajorV pre-image, promoted → MinorV pre-image
3. The reachability constraint: only reachable vertices from combined_roots can appear

**Difficulty:** Medium-Hard. The key difficulty is proving that `objects mc_major` is EXACTLY
the union (not just a superset). We need:
- `cheney_collect_preserves_objects` (pre-existing survive) ✅ have this
- A NEW lemma: objects in mc_major that are NOT in `objects major` must be fwd targets

### Gap 3: Edge Backward (D) — mc_major edge → combined edge

**Statement:** If (φ(u), φ(v)) is an edge in mc_major and u,v are both combined-reachable,
then (u,v) is an edge in the combined graph.

**Why this is the hardest gap:**
- For Major→Major (φ=identity): edge in mc_major → edge in major (pointer update preserves
  non-minor fields). Then edge in major → combined edge (MajorBridge).
- For Minor→*: the promoted copy's field equals fwd(original_field). Need to INVERT
  field_correspondence to go from "field in mc_major = fwd(x)" to "original minor field = x".
- Inversion of field_correspondence requires it to be a BIJECTION on the relevant domain,
  not just a forward implication.

**Difficulty:** Hard. This is genuinely new work because:
- field_correspondence gives forward direction only (minor field → mc_major field)
- We need the REVERSE: mc_major field → must come from a minor field
- This requires proving that NO OTHER mechanism could create edges in mc_major
  (i.e., the only edges are those arising from pre-existing fields + forwarding)

### Gap 4: Additional Preconditions Needed

To close Gaps 1-3 with honest preconditions, we need to add to
`minor_collect_operational_preconditions`:

| New Precondition | Why | Derivable? |
|-----------------|-----|-----------|
| `well_formed_heap mc.mc_major` | EdgeBridge needs it | Should be provable from Cheney correctness |
| `graph_wf (create_graph mc.mc_major)` | EdgeBridge needs it | Follows from well_formed_heap |
| `chain_avoids major fp obj` for reachable | EdgeBridge Cases 3&4 | Follows from chain_objects_blue + obj non-blue |
| `objects(mc_major) = objects(major) ∪ fwd_targets` | Surjectivity | Needs new Cheney characterization lemma |

---

## Recommended Plan

### Phase 1: Edge Forward (C) — Estimated ~200-300 lines

**Goal:** Add to MinorCollectIso:
```fstar
// (C) Edge preservation: combined edges map to mc_major edges
(forall (u v: combined_vertex).
  combined_reachable cg combined_roots u /\
  combined_reachable cg combined_roots v /\
  mem_ce (u, v) cg ==>
  Seq.mem ((Iso.fwd_morphism fwd u <: hp_addr),
           (Iso.fwd_morphism fwd v <: hp_addr))
          g_mc.edges)
```

**Approach:**
1. Create `GC.Gen.MinorCollectIso.EdgeForward.fst` helper module
2. For each case (Major→Major, Major→Minor, Minor→*), discharge the per-case
   preconditions of EdgeBridge from the operational preconditions
3. Compose via `Classical.forall_intro (Classical.move_requires aux)` pattern

**Key sub-lemmas needed:**
- `chain_objects_blue_implies_avoids`: non-blue obj → chain_avoids (likely in CheneyDischarge)
- `cheney_promote_preserves_major_objects`: src ∈ objects major → src ∈ objects major_final
  with same wosize (likely in Cheney or CheneyCorrectness)
- `cheney_collect_well_formed`: mc_major is well_formed (likely exists)
- `cheney_collect_graph_wf`: create_graph mc_major is graph_wf (follows from well_formed)

### Phase 2: Surjectivity (C') — Estimated ~150-250 lines

**Goal:** Add to MinorCollectIso:
```fstar
// (C') Surjectivity: mc_major reachable → has combined pre-image
(forall (w: vertex_id).
  Seq.mem w g_mc.vertices /\
  (exists (r: U64.t). Seq.mem r mc_roots /\
    Seq.mem r g_mc.vertices /\
    reachable g_mc r w) ==>
  (exists (v: combined_vertex).
    combined_reachable cg combined_roots v /\
    Iso.fwd_morphism fwd v == (w <: U64.t)))
```

**Approach:**
1. Prove `mc_major_objects_partition`: objects in mc_major are either pre-existing
   major OR fwd targets of live_set members
2. For pre-existing: pre-image is MajorV w (need to show w was combined-reachable)
3. For promoted: pre-image is MinorV m where fwd(m) = w (need to show m was combined-reachable)
4. The reachability reconstruction is the hard part — need that mc_major reachability
   implies combined reachability (essentially the reverse of what ReachabilityBridge gives)

### Phase 3: Edge Backward (D) — Estimated ~300-400 lines (hardest)

**Goal:** mc_major edge between morphism images → combined edge

**Approach:**
1. For Major→Major: use MajorBridge reverse direction + show update_major_pointers
   doesn't add new major→major edges
2. For promoted→*: invert field_correspondence
3. This may require strengthening field_correspondence to a biconditional

### Alternative: Prove at mc_major Level Without Edge Backward

A weaker but still useful property: **graph homomorphism** (not full isomorphism).
This gives: Injectivity + Image + Edge Forward + Surjectivity = **injective graph homomorphism
with surjective image**. This is stronger than what we have now and may be achievable
without the hard Edge Backward proof.

---

## Summary of Current Caller Obligations

For `minor_collect_iso_theorem` (what we have TODAY):

### Operational (provable from system initialization):
1. `well_formed_heap major`
2. `minor_wf minor`
3. `fl_valid`, `fl_chain_terminates`
4. `chain_objects_blue`
5. `nonblue_wosize_positive`
6. `cheney_no_oom` (enough free space)
7. `remembered ⊆ roots`
8. Live objects have positive wosize
9. `no_pointer_to_blue`, `minor_no_pointer_to_blue`
10. `roots_valid_nonblue`
11. `major_field_one_plus_in_remembered`, `major_field_zero_no_minor`
12. `no_scan_invariant`, `minor_no_scan_invariant`

### Non-operational (the genuine proof obligation):
13. **`field_correspondence`** — promoted objects have correct field values in mc_major

---

## What Would Make This a Real Isomorphism

To get a genuine isomorphism theorem under honest preconditions:

```
operational_preconditions + field_correspondence
  ==> A ∧ B ∧ C ∧ C' ∧ E ∧ F
```

We need to prove C (edge forward) and C' (surjectivity) from the same
preconditions MinorCollectIso already uses. Edge backward (D) would give
the full biconditional but is significantly harder.

**Priority order:**
1. **Edge Forward (C)** — highest value, most infrastructure already exists
2. **Surjectivity (C')** — needed for genuine isomorphism
3. **Edge Backward (D)** — nice to have, makes it a full isomorphism

With just C + C' we can claim: **the forwarding map is a surjective graph
homomorphism that is also injective** — which IS an isomorphism (injective +
surjective + edge-preserving = isomorphism for finite graphs, provided
we also have edge backward). So really we need all three for a proper claim.

However, C alone already gives a significant upgrade: an **injective graph
homomorphism** preserving all reachable structure.
