# Isomorphism-Based Generational GC Correctness

## Goal

State and prove an end-to-end theorem showing that the **graph of objects
reachable from the roots and major-to-minor pointers in the initial heap** is
*isomorphic* to the **graph of objects reachable from the updated roots after
the GC runs and the minor heap has been reset**.

This is a stronger statement than `generational_gc_end_to_end` (which proves
5 separate properties) because it captures the full structural equivalence
in a single graph-theoretic predicate.

---

## 1. Defining the Pre-GC Graph

### The "combined" graph

Currently, `create_graph` builds a graph from a *single* major heap
(`GC.Spec.HeapModel.create_graph`):

```fstar
let create_graph (g: heap) : GTot graph_state =
  HeapGraph.create_graph_from_heap g (objects zero_addr g)
```

Vertices = `objects zero_addr g` (major-heap object addresses).  
Edges = pointer fields that satisfy `is_pointer_field`.

The pre-GC combined graph must **also** include minor-heap objects and
inter-generational edges. We define:

```fstar
/// Vertex domain: union of major objects and live minor objects
let combined_vertices (gs: gen_state) (roots: seq U64.t) : GTot (seq U64.t) =
  let major_objs = objects zero_addr gs.gs_major in
  let minor_live = live_set_of gs.gs_minor gs.gs_major roots in
  (* NOTE: addresses are disjoint because minor_heap_size < heap_addr_base *)
  Seq.append (coerce minor_live) major_objs

/// Edge from v to w exists iff:
///   (a) v is a major object and field i of v in major heap is w (pointer field), OR
///   (b) v is a live minor object and minor_read_field(v, j) is w
///       where w is either another live minor object or a major object
type combined_edge (gs: gen_state) (roots: seq U64.t) = {
  src: U64.t;
  dst: U64.t;
  // either (src ∈ major_objs ∧ dst = get_field major src i ∧ is_pointer_field dst)
  //     or (src ∈ minor_live ∧ dst = minor_read_field src j ∧ is_pointer dst)
}
```

### Roots

The combined roots are:
- Program roots (`roots: seq U64.t`): each root may be a minor or major address.
- Remembered set targets (`minor_roots_from_major major`): already incorporated
  via `live_set_of`.

So the root set for the combined graph is `roots` (since remembered-set roots
are already handled by `minor_reachable` closure).

### Formalization challenge

The combined graph has **heterogeneous vertices** (minor addrs ∈ [8, minor_heap_size)
and major addrs ∈ [mword, heap_size)). Since `minor_heap_size` is small and
major addresses start at `mword ≥ 8`, these ranges overlap in principle. However,
`is_minor_pointer v` checks `v < minor_heap_size`, so in practice the address
spaces are distinguished by the `is_minor_pointer` predicate.

**Key insight**: Minor and major address spaces must be **disjoint** for
the combined graph to be well-formed. This is already an implicit assumption
(minor_heap_size < mword for major pointers), but should be made explicit as
a precondition.

---

## 2. Defining the Post-GC Graph

After GC:
- Minor heap is reset (`bump = 0`), so it has no objects.
- All surviving objects are in `mc_major` (post-minor) or `h_swept` (post-major).

The post-GC graph is simply:

```fstar
let post_gc_graph (h_final: heap) : GTot graph_state =
  create_graph h_final
```

Roots are `rewrite_roots roots fwd` (each minor pointer replaced by its
forwarded major address).

---

## 3. The Isomorphism

### Definition

A **graph isomorphism** φ from G_pre to G_post is a bijection φ: V(G_pre) → V(G_post) such that:
- (u, v) ∈ E(G_pre) ⟺ (φ(u), φ(v)) ∈ E(G_post)
- φ(root_i) = post_root_i for each root

In our case, the bijection is constructed from the **forwarding map**:

```fstar
let gc_morphism (fwd: forwarding_map) (v: U64.t) : GTot U64.t =
  if is_minor_pointer v then
    if fwd v <> 0UL then fwd v else v  (* unreachable case if all succeed *)
  else v  (* major objects keep their address *)
```

This is a bijection because:
1. Major objects are not moved (identity on major addrs).
2. `fwd` maps each live minor object to a distinct fresh major address
   (proven by `promote_all_spec` allocating distinct blocks).

### What we actually need: induced subgraph isomorphism

The full combined graph before GC may contain objects that are NOT reachable
from roots. The mark-and-sweep major GC reclaims unreachable objects. So the
isomorphism is between the **reachable subgraphs**:

```
φ : reachable_subgraph(G_pre, roots) ≅ reachable_subgraph(G_post, φ(roots))
```

### Formal statement

```fstar
val generational_gc_isomorphism
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t)
  (major_roots: seq obj_addr) (major_stack: seq obj_addr) (major_fp: U64.t)
  : Lemma
    (requires
      gen_wf gs /\ well_formed_heap gs.gs_major /\
      (* ... full_gc_preconditions as in generational_gc_end_to_end ... *)
      minor_fields_well_formed gs.gs_minor gs.gs_major roots /\
      all_promotions_succeed gs.gs_minor gs.gs_major fp roots /\
      allocated_objects_avoid_chain gs.gs_major fp /\
      post_promote_pointer_closure gs.gs_minor gs.gs_major fp roots /\
      (* Address disjointness precondition *)
      minor_major_addr_disjoint gs)
    (ensures
      (let g_pre = combined_graph gs roots in
       let fwd = (minor_collect_spec gs.gs_minor gs.gs_major fp roots).mc_fwd in
       let new_roots = rewrite_roots roots fwd in
       let h_final = (* ... post-sweep-coalesce heap ... *) in
       let g_post = create_graph h_final in
       let pre_reach = reachable_set g_pre (combined_roots roots) in
       let post_reach = reachable_set g_post (coerce new_roots) in
       // The morphism is a bijection on reachable sets
       (forall v. Seq.mem v pre_reach ==>
         Seq.mem (gc_morphism fwd v) post_reach) /\
       (forall v. Seq.mem v post_reach ==>
         exists u. Seq.mem u pre_reach /\ gc_morphism fwd u == v) /\
       // Edge preservation
       (forall u v. Seq.mem u pre_reach /\ mem_graph_edge g_pre u v ==>
         mem_graph_edge g_post (gc_morphism fwd u) (gc_morphism fwd v)) /\
       (forall u v. Seq.mem u post_reach /\ mem_graph_edge g_post u v ==>
         (exists u0 v0. gc_morphism fwd u0 == u /\ gc_morphism fwd v0 == v /\
                        mem_graph_edge g_pre u0 v0))))
```

---

## 4. Proof Strategy

### Step A: Build the combined graph infrastructure

| Task | Status | Difficulty |
|------|--------|------------|
| Define `combined_graph` (minor + major vertices/edges) | NEW | Medium |
| Prove `combined_graph` is well-formed (no dup vertices, edges valid) | NEW | Medium |
| Prove `reachable_set(combined_graph, roots)` = `live_set ∪ reachable major objs` | NEW | Hard |
| Prove address disjointness | NEW (trivial if parametrized correctly) | Easy |

### Step B: Forward direction (pre-reachable → post-reachable)

This decomposes into three sub-cases:

1. **Minor objects → promoted copies**: For each `v ∈ live_set`, show
   `fwd v ∈ objects(0, mc_major)`. This is already proven by
   `fwd_targets_in_objects` in `gen_gc_correct`.

2. **Major objects survive**: For each `v ∈ objects(0, major)` that is
   reachable, show `v ∈ objects(0, h_final)`. This follows from
   `full_gc_correctness` Pillar 3 (reachable objects survive).

3. **Roots map correctly**: Each root `r` maps to `rewrite_root r fwd`.
   This is already `cheney_collect_rewrites_roots`.

| Task | Status | Difficulty |
|------|--------|------------|
| Forward direction for minor objects | Partially proven (fwd_targets_in_objects) | Medium |
| Forward direction for major objects | Proven (full_gc_correctness Pillar 2/3) | Easy (composition) |
| Root mapping preserves reachability | Need bridge lemma | Medium |

### Step C: Edge preservation (the hard part)

This is the crux. We must show that `field_correspondence` + `update_major_pointers`
faithfully translates the combined graph's edges through the morphism.

**Sub-cases:**

1. **Minor→minor edge becomes major→major edge**: 
   - Pre: field j of minor obj `u` points to minor obj `v` (both in live_set)
   - Post: field j of major obj `fwd u` points to `fwd v`
   - Proof path: `copy_fields` copies the raw value, then `update_object_pointers`
     rewrites it from `v` to `fwd v`.
   - PARTIALLY PROVEN in `field_correspondence` predicate (line 135 of Correctness.fsti).

2. **Minor→major edge stays**: 
   - Pre: field j of minor obj `u` points to major obj `w`
   - Post: field j of `fwd u` points to `w` (unchanged, not a minor pointer)
   - PARTIALLY PROVEN: `field_correspondence` case `~(is_minor_pointer v) ==> major_val == v`.

3. **Major→minor edge becomes major→major edge**:
   - Pre: field j of major obj `w` points to minor obj `v`
   - Post: field j of `w` (still alive after sweep) points to `fwd v`
   - Proof path: `update_major_pointers` rewrites the field.
   - Need: `update_major_pointers_field_effect` (already exported from Promote).
   - But also need: mark/sweep doesn't modify fields of surviving objects
     (Pillar 5 of `full_gc_correctness`).

4. **Major→major edge stays**:
   - Pre: field j of major obj `w` points to major obj `x`
   - Post: same (not a minor pointer, so `update_major_pointers` leaves it alone)
   - Proven by: `update_object_pointers` skips non-minor-pointer fields + Pillar 5.

| Task | Status | Difficulty |
|------|--------|------------|
| Case 1 (minor→minor → major→major) | Needs field_correspondence + alloc frame | Hard |
| Case 2 (minor→major stays) | Needs field_correspondence proof | Medium |
| Case 3 (major→minor → major→major) | Needs update_major_pointers + sweep frame | Hard |
| Case 4 (major→major stays) | update_major_pointers no-op + Pillar 5 | Medium |

### Step D: Backward direction (post-reachable → pre-reachable)

This is the **injectivity** direction. Show that every vertex in the post-GC
reachable set has a pre-image in the pre-GC reachable set.

- Major objects that survive sweep were reachable pre-GC (Pillar 2: black ⟺ reachable).
- Promoted objects came from the live_set (which is defined as reachable from roots).
- No new objects are created (the GC only promotes existing minor objects).

| Task | Status | Difficulty |
|------|--------|------------|
| Sweep survivors were reachable | Follows from mark correctness (Pillar 2) | Easy |
| Promoted objects came from live_set | Trivial from promote_all_spec definition | Easy |
| fwd is injective on live_set | Need to prove (alloc gives distinct addrs) | Medium |

### Step E: Composition

Compose Steps B+C+D into the final theorem. This is primarily mechanical
(calling the sub-lemmas in the right order).

---

## 5. Feasibility Assessment

### What's already proven
- `fwd_targets_in_objects`: promoted objects exist in post-minor heap ✓
- `full_gc_correctness`: 5 pillars of mark-and-sweep ✓
- `field_correspondence`: pointer rewriting model (stated, not fully connected) ⚠️
- `update_major_pointers_field_effect`: major pointer rewriting correctness ✓
- `cheney_collect_rewrites_roots`: root rewriting ✓
- `minor_reachable_closed`: reachability closure in minor heap ✓
- `reachable_set_correct`: DFS = reachability ✓

### Key gaps
1. **No combined graph definition** — need to define and prove well-formedness
2. **`field_correspondence` not connected to graph edges** — the predicate
   exists but needs a bridge to `mem_graph_edge`
3. **Injectivity of fwd** — not explicitly proven (follows from `alloc_spec`
   returning distinct addresses, but needs to be stated)
4. **Sweep frame for edge preservation** — need to show sweep doesn't modify
   surviving objects' fields (Pillar 5 covers this but at the graph level,
   not field level)
5. **Combined reachability = live_set ∪ major_reachable** — need to prove this
   equivalence bridges the two notions of "reachable"

### Effort estimate

| Component | Lines of F* (est.) | Difficulty |
|-----------|-------------------|------------|
| Combined graph + well-formedness | 100-150 | Medium |
| Address disjointness precondition | 20-30 | Easy |
| Forward morphism (vertex survival) | 50-80 | Medium (mostly composition) |
| Edge preservation (4 cases) | 200-300 | Hard |
| Backward morphism (injectivity) | 80-120 | Medium |
| Reachability bridge lemma | 100-150 | Hard |
| Final composition | 30-50 | Easy |
| **Total** | **~600-900** | |

### Risk factors

1. **`field_correspondence` proof gap**: The comment at line 130 of Correctness.fsti
   notes that full field_correspondence requires an `alloc_spec_read_other` bridge.
   This is the single biggest blocker.

2. **Combined graph well-formedness**: The `is_vertex_set` requirement means we
   need to show that minor and major object addresses form a set with no
   duplicates. This depends on address disjointness.

3. **Interaction between update_major_pointers and mark/sweep**: The order is
   `promote → update_major_pointers → mark → sweep`. We need the sweep to
   preserve the already-rewritten fields of survivors. This should follow from
   Pillar 5 but requires careful sequencing.

4. **Quantifier complexity**: The combined graph has potentially large vertex/edge
   sets. SMT performance may degrade. Likely needs `opaque_to_smt` annotations
   and explicit lemma calls rather than quantifier triggers.

---

## 6. Recommended Approach

### Phase 1: Infrastructure (low risk, high value)
1. Define `combined_graph_state` in a new file `GC.Gen.CombinedGraph.fsti`
2. Prove well-formedness under address disjointness
3. Prove `combined_reachable ≡ live_set ∪ major_reachable` bridge

### Phase 2: Forward morphism
4. Prove vertex survival (compose existing lemmas)
5. Prove root mapping correctness

### Phase 3: Edge preservation (highest risk)
6. Prove the 4 edge cases, starting with Case 4 (easiest) and working up
7. Fill the `alloc_spec_read_other` gap if needed

### Phase 4: Backward morphism
8. Prove injectivity of `gc_morphism fwd` on the reachable set
9. Prove surjectivity (every post-GC reachable vertex has a pre-image)

### Phase 5: Final theorem
10. Compose into `generational_gc_isomorphism`

---

## 7. Alternative: Weak Homomorphism

If full isomorphism proves too expensive, a **weaker but still useful** theorem
is a graph homomorphism (surjective, edge-preserving map):

```fstar
val generational_gc_homomorphism
  (gs: gen_state) (roots: seq U64.t) (fp: U64.t) ...
  : Lemma (ensures
      // Every pre-GC reachable object has a surviving image
      (forall v. pre_reachable v ==> post_reachable (gc_morphism fwd v)) /\
      // Edges are preserved forward
      (forall u v. pre_reachable u /\ edge u v ==> edge (φ u) (φ v)))
```

This omits injectivity and the backward direction. It's approximately half
the proof effort (~300-500 lines) and captures the essential safety property:
**no reachable object is lost, and the pointer structure is faithfully preserved**.

---

## 8. Implementation Progress

### Phase 1: Infrastructure

| Task | Status | File | Notes |
|------|--------|------|-------|
| Define `combined_vertex` (tagged MinorV/MajorV) | ✅ Done | CombinedGraph.fsti | Handles overlapping addr spaces |
| Define `combined_graph` record type | ✅ Done | CombinedGraph.fsti | `cg_vertices + cg_edges` |
| Field classification (minor + major) | ✅ Done | CombinedGraph.fst | Both check Seq.mem for destinations |
| Edge construction from all objects | ✅ Done | CombinedGraph.fst | `all_minor_edges`, `all_major_edges` |
| Tag membership lemmas | ✅ Done | CombinedGraph.fst | Using `Seq.mem_cons` |
| Vertex characterization (minor/major) | ✅ Done | CombinedGraph.fst | `minor_vertex_char`, `major_vertex_char` |
| Well-formedness proof | ✅ Done | CombinedGraph.fst | 0 admits, all edge endpoints proven |
| Inductive reachability type | ✅ Done | CombinedGraph.fst | `combined_reach` with CR_root/CR_step |
| Reachability intro/elim lemmas | ✅ Done | CombinedGraph.fst | `combined_reachable_root/step/ind` |
| Root classification | ✅ Done | CombinedGraph.fst | `classify_roots_impl` |
| Reachability bridge (combined↔live_set) | TODO | — | Next step |

**Verification stats**: 0 admits, 3.5s verification time, z3rlimit ≤ 20.

### Commits
- `a02e9f8` — Fixed zero_addr abstraction (gen2 compatibility)
- `da68249` — CombinedGraph: fully verified (0 admits, 3.5s)

### Next steps
1. **Reachability bridge**: Prove `minor_reachable_implies_combined` and
   `major_reachable_implies_combined` — showing that objects reachable in
   the individual heaps are also reachable in the combined graph.
2. **Forward morphism** (Phase 2): Vertex survival through GC.
3. **Edge preservation** (Phase 3): The hard part — 4 cases.

The full isomorphism additionally guarantees **no spurious objects** appear in
the post-GC state (every post-GC reachable object came from a pre-GC reachable
object). This is also valuable but somewhat less critical.

---

## 8. Verdict

**Feasible but substantial.** The existing infrastructure covers ~60% of what's
needed. The remaining gaps (combined graph definition, field_correspondence
connection, fwd injectivity) are well-understood and bounded in scope. The
hardest part is edge preservation Case 1 and Case 3 (cross-generational pointer
rewriting), which depend on the `alloc_spec_read_other` bridge noted in
Correctness.fsti.

**Recommended starting point**: Define the combined graph and prove the
reachability bridge (Phase 1). This has value on its own (clarifies what
"reachable in the combined heap" means) and de-risks the full isomorphism.

**Timeline**: Phase 1 alone is 1-2 weeks. Full isomorphism (all 5 phases) is
4-8 weeks depending on the `alloc_spec_read_other` gap complexity.
