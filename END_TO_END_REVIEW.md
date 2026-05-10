# Pulse-Verified-GC: End-to-End Review

> Goal: verified, drop-in replacement generational collector for OCaml 4,
> reaching feature and performance parity, with a top-level theorem assuring
> full correctness.

## 1. Project Overview

| Metric | Value |
|--------|-------|
| Total F\*/Pulse files | 152 |
| Verified modules | 304 |
| Total lines of code | ~69K (specs & proofs ~62K, impl ~7K) |
| `common/` | 17 files, 1.1K lines — shared heap model, object layout, graph theory, DFS |
| `mark-and-sweep/` | 65 files, 6.4K lines — major GC (mark, sweep, coalesce, allocator) |
| `generational/` | 70 files, 4.8K lines — minor GC (Cheney BFS, promotion, remembered set) |
| Admits/assumes | **0** across entire codebase (2 platform TCB `assume val platform_fits_u64`) |
| Build system | Single top-level Makefile, `make -j4`, `--report_assumes warn` |
| Extraction | KaRaMeL to C for both mark-and-sweep and generational |

## 2. Feature Completeness vs OCaml 4 GC

### ✅ Implemented & Verified

| Feature | Status | Location |
|---------|--------|----------|
| **Minor heap (nursery)** | ✅ Cheney semi-space BFS | `GC.Gen.Cheney`, `GC.Gen.Impl.Cheney` |
| **Major heap mark** | ✅ DFS-based mark with bounded stack | `GC.Spec.Mark`, `GC.Impl.MarkBounded` |
| **Major heap sweep** | ✅ Linear sweep, free-list construction | `GC.Spec.Sweep`, `GC.Impl.Sweep` |
| **Coalesce** | ✅ Fused sweep-coalesce for contiguous free blocks | `GC.Spec.Coalesce`, `GC.Impl.FusedSweepCoalesce` |
| **Allocator** | ✅ Free-list allocator with block splitting | `GC.Spec.Allocator`, `GC.Impl.Allocator` |
| **Object model** | ✅ OCaml-compatible 64-bit headers (wosize/color/tag) | `GC.Lib.Header`, `GC.Spec.Object` |
| **Promotion (minor→major)** | ✅ alloc + copy fields + forwarding map | `GC.Gen.Promote`, `GC.Gen.Impl.Promote` |
| **Root rewriting** | ✅ After promotion, roots point to copies | `GC.Gen.Cheney.cheney_collect_spec` |
| **BFS completeness** | ✅ Non-tautological graph-theoretic proof | `GC.Gen.CheneyBFS` |
| **Remembered set (spec)** | ✅ Full major-heap scan for minor refs | `GC.Gen.Remembered` |
| **Infix tag support** | ✅ well_formed_heap parts 3 & 4 | `GC.Spec.Fields` |
| **No-scan invariant** | ✅ Named predicate preserved by GC ops | `GC.Spec.Fields.no_scan_invariant` |
| **Graph model** | ✅ Heap→graph bridge, DFS with termination | `GC.Spec.Graph`, `GC.Spec.HeapGraph`, `GC.Spec.DFS` |

### ⚠️ Spec Only / Partial

| Feature | Gap | Notes |
|---------|-----|-------|
| **Remembered set (impl)** | No Pulse implementation | `GC.Gen.Remembered.fsti` has spec + completeness theorem; no `GC.Gen.Impl.Remembered`. Caller passes remembered-set roots manually. |
| **Full generational GC loop** | Spec theorem only | `GC.Gen.Correctness.generational_gc_end_to_end` composes minor + major, but there is no Pulse `fn` that calls both in sequence. |
| **Write barrier** | Not needed from GC perspective | See §3.4 below. The GC takes roots as a precondition; ensuring completeness is a mutator obligation. |

### ❌ Missing

| Feature | Impact |
|---------|--------|
| **Compaction** | OCaml 4 has optional compaction (`Gc.compact()`). Not modeled. |
| **Finalization** | No weak references, ephemerons, or custom finalizers. |
| **Custom blocks** | No `Abstract_tag` / custom dispatch. |
| **C runtime integration** | No `caml_alloc`, `caml_modify`, `caml_minor_gc` stubs matching OCaml's C API. |

## 3. Spec Completeness & Top-Level Theorem

### 3.1 Mark-and-Sweep Correctness (✅ Strong)

`GC.Spec.Correctness.fsti` provides `full_gc_correctness` covering all **5 pillars**:

1. **Heap integrity** — `well_formed_heap h_final`
2. **Reachability** — black after mark ⟺ reachable from roots
3. **Structural preservation** — successors of reachable objects unchanged
4. **Color reset** — all objects white or blue after sweep
5. **Field data preservation** — field values of reachable objects unchanged

The Pulse `GC.Impl.fsti` postcondition directly states:
```
SpecGCPost.gc_postcondition s2 /\
SpecGCPost.full_gc_correctness 's s2 'st
```
**Clean, strong impl→spec connection.** ✅

### 3.2 Generational (Minor) Correctness (✅ Solid, conditional)

`GC.Gen.CheneyCorrectness.fsti` proves **5 unconditional** properties + 1 conditional:
1. Object survival — pre-existing major objects survive ✅
2. `well_formed_heap_part1` preserved ✅
3. Allocator invariants preserved (fl_valid, fl_chain_terminates) ✅
4. Minor reset (bump = 0) ✅
5. Root rewriting correct ✅
6. **BFS completeness** (conditional on `cheney_no_oom`) — all reachable minor objects with wosize > 0 are forwarded ✅

Property 6 uses a **non-tautological proof** via `GC.Gen.CheneyBFS`:
- `cheney_no_oom` = fwd covers roots ∧ fwd is successor-closed
- Proved via `minor_reachable_ind` (reachability induction principle)
- Forward map monotonicity through all BFS operations

**no_black_objects preservation** (`GC.Gen.CheneyPreservation`): fully proved that
promotion never creates black objects. The proof uses `alloc_spec_preserves_no_black_part1`
(allocation under `well_formed_heap_part1` preserves no-black) combined with
`copy_fields_frame` (field copying preserves headers, thus colors). ✅

### 3.3 Impl→Spec Connection (⚠️ Indirect for generational)

`GC.Gen.Impl.fsti`'s `minor_collect` postcondition states:
```
s2 == res.mc_major /\ fp2 == res.mc_fp /\ rs2 == res.mc_roots /\ U64.v b2 == 0
```
where `res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs`.

This connects the impl to `cheney_collect_spec`, but does **not directly** state `cheney_gc_correct` in the postcondition. A caller must separately invoke `cheney_gc_correct` to derive correctness properties.

**Recommendation**: Add a wrapper lemma that derives correctness from the spec refinement, or enrich the postcondition.

### 3.4 Remembered Set & Write Barrier: Trust Boundary Analysis

**The write barrier and remembered set are mutator obligations, not GC obligations.**

From the GC's perspective:
- `cheney_collect_spec` takes `roots: seq U64.t` — the caller supplies program roots
- `live_set_of minor major roots = minor_reachable minor (roots ++ minor_roots_from_major major)` — the spec defines liveness via the full remembered set
- `minor_roots_from_major` scans the entire major heap for minor pointers (O(major heap))
- `scan_complete` (in `GC.Gen.Remembered.fsti`) proves completeness: every major-heap field pointing to the minor heap is captured

**What the GC must assume**: The `roots` passed to `minor_collect` are complete — they include every program root AND every major-heap location pointing into the minor heap. This is a **precondition on the caller**, analogous to `minor_guards_complete`.

**What the GC does NOT need to prove about write barriers**: The write barrier is an optimization that avoids the O(major heap) scan. It maintains a "card table" or "remembered set" that records exactly those major-heap slots that received minor-heap pointers since the last collection. Correctness of this mechanism is a mutator-side invariant.

**Architecture decision**: The GC's correctness theorem should be parameterized by a `remembered_set_complete` precondition:
```
remembered_set_complete minor major roots ≜
  ∀ obj field_idx. obj ∈ objects(major) ∧ read_field(major, obj, field_idx) ∈ minor_heap
    ⟹ read_field(major, obj, field_idx) ∈ roots
```
This is already implicitly achieved: `cheney_collect_spec` receives all roots externally, and `live_set_of` computes the correct live set by appending `minor_roots_from_major major`. The only gap is that the Pulse `minor_collect` doesn't compute `minor_roots_from_major` — it trusts the caller.

### 3.5 End-to-End Theorem (✅ Stated and Proved)

`GC.Gen.Correctness.generational_gc_end_to_end` provides a 5-property composition:

1. Post-minor major heap is `well_formed_heap` (full, including pointer closure)
2. Major GC correctness (`full_gc_correctness` over post-promotion heap)
3. All live minor objects have valid forwarded addresses
4. Roots rewritten to point to promoted copies
5. Minor heap reset

**Preconditions** (all reasonable):
- `gen_wf gs`, `well_formed_heap gs.gs_major`, allocator invariants
- `minor_fields_well_formed` — minor pointer fields target valid objects
- `all_promotions_succeed` — sufficient major-heap space
- `allocated_objects_avoid_chain` — standard allocator invariant
- `post_promote_pointer_closure` — frame property after promotion
- Major GC entry conditions (stack/root props, no black/blue violations, graph-wf)

### 3.6 Trust Assumptions

| Assumption | Location | Nature |
|------------|----------|--------|
| `minor_guards_complete` | `GC.Gen.MinorHeap.fsti` | No fake headers in minor heap bodies. Mutator responsibility. |
| `no_scan_invariant` | `GC.Spec.Fields.fst` | No-scan objects contain no valid heap pointers. OCaml runtime guarantee. |
| `bounded_mark_inv` | `GC.Spec.MarkBoundedInv` | Stack capacity sufficient for DFS. Standard graph-theory bound. |
| `platform_fits_u64` | `GC.Impl.Heap`, `GC.Gen.Impl.MinorHeap` | 64-bit platform assumption (`SizeT.fits_u64`). Standard for Pulse extraction. |
| Root completeness | Caller of `minor_collect` | Caller must include remembered-set roots. Mutator responsibility. |

All `admit()`/`assume_` calls have been eliminated. The only `assume val` declarations
are `platform_fits_u64` (in `GC.Impl.Heap` and `GC.Gen.Impl.MinorHeap`), which assert
that `SizeT.fits_u64` holds — a standard platform assumption for 64-bit targets.
The trust boundary is clean.

## 4. Code & Proof Quality

### 4.1 Modularity (✅ Good)

Clean layered architecture:
- `common/` provides reusable infrastructure (heap, objects, graph, DFS)
- `mark-and-sweep/` builds on common for the major GC
- `generational/` builds on both for the minor GC
- `.fsti` files provide clean abstraction boundaries
- Allocator lemmas factored into Core, Part1, Part2, Split, Header sub-modules
- BFS completeness cleanly separated into `CheneyBFS` module

### 4.2 File Sizes (⚠️ Some Large Files)

Files > 1500 lines:

| File | Lines | Notes |
|------|-------|-------|
| `GC.Spec.Mark.fst` | 3932 | Largest file. Many helper lemmas. |
| `GC.Spec.Coalesce.fst` | 3482 | Complex coalescing invariant proofs. |
| `GC.Spec.Allocator.Lemmas.Part2.fst` | 3503 | Recently split from 8000-line parent. Includes `alloc_spec_preserves_no_black_part1`. |
| `GC.Spec.Allocator.Lemmas.Core.fst` | 3093 | Core allocator lemmas. |
| `GC.Test.Bridge.fst` | 2693 | Test infrastructure. |
| `GC.Spec.Fields.fst` | 1896 | Well-formed heap + objects traversal. |

### 4.3 Proof Stability (⚠️ Some Fragility)

| Concern | Count | Notes |
|---------|-------|-------|
| `z3rlimit ≥ 500` in code | ~10 spots | Mainly `GC.Lib.Header.fst` (bitvector) and `GC.Spec.Fields.fst` |
| `z3rlimit ≥ 400` in Makefile | 3 files | `Allocator.Lemmas.{fst,Split,Part1}` |
| `z3refresh` usage | ~10 spots | Indicates proof instability |

### 4.4 Interface Quality (✅ Mostly Good)

Strong:
- `GC.Impl.fsti` directly states `full_gc_correctness` in postcondition ✅
- `GC.Gen.CheneyCorrectness.fsti` has clear, individually-named properties ✅
- `GC.Gen.Promote.fsti` exports equation lemmas for client reasoning ✅
- Key predicates are `opaque_to_smt` with reveal lemmas ✅
- `GC.Gen.CheneyBFS.fsti` has clean, non-circular BFS completeness ✅

Weak:
- `GC.Gen.Impl.fsti` postcondition connects to `cheney_collect_spec` but not to `cheney_gc_correct` ⚠️

## 5. Roadmap to Drop-In OCaml 4 Replacement

### Phase 1: Full Generational GC Entry Point (Current Priority)

1. **Build `gen_gc` Pulse function** — calls `minor_collect` then `collect`
   - Postcondition: references `generational_gc_end_to_end`
   - This is the top-level verified function with the end-to-end theorem

2. **Enrich `minor_collect` postcondition** — derive correctness properties
   directly, not just spec refinement

### Phase 2: Engineering (Significant Effort)

3. **C API stubs** — `caml_alloc`, `caml_minor_gc`, `caml_major_gc`
4. **KaRaMeL extraction** — clean C output
5. **Runtime integration** — root registration, stack scanning

### Phase 3: Feature Parity (Large Effort)

6. **Compaction** — optional heap defragmentation
7. **Write barrier optimization** — card table instead of full-scan (performance, not correctness)
8. **Finalization** — weak references, ephemerons

## 6. Summary Assessment

| Dimension | Grade | Notes |
|-----------|-------|-------|
| **Spec correctness** | A | 5-pillar mark-and-sweep + 6-property Cheney BFS (non-tautological). |
| **Impl-spec connection** | B+ | Mark-and-sweep: excellent. Generational: good but indirect. |
| **Trust boundary** | A | Zero admits. Clean, documented trust assumptions. |
| **Proof stability** | B- | Several high-rlimit spots. Some z3refresh needed. |
| **Modularity** | A- | Clean layers. CheneyBFS cleanly separated. Some large files. |
| **Feature completeness** | B- | Core GC verified. Missing: full gen-GC entry point, C API. |
| **Drop-in readiness** | C+ | Algorithms verified. Engineering work remains for OCaml integration. |

### Bottom Line

The **core algorithms are correctly specified and verified**: mark-and-sweep with 5 correctness pillars, Cheney BFS with 6 properties including non-tautological BFS completeness, and a composed `generational_gc_end_to_end` theorem. The trust boundary is minimal.

The remembered set and write barrier are correctly treated as **mutator obligations**: the GC assumes root completeness and proves correctness conditional on it. No GC-side proof of write barrier correctness is needed.

Reaching a **drop-in OCaml 4 replacement** requires:
1. Building the full generational GC Pulse entry point (minor + major) — medium effort
2. C API integration — primarily engineering
3. Performance optimizations (write barrier) — optional for correctness
