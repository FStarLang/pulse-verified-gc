# Pulse-Verified-GC: End-to-End Review

> Goal: verified, drop-in replacement generational collector for OCaml 4,
> reaching feature and performance parity, with a top-level theorem assuring
> full correctness.

## 1. Project Overview

| Metric | Value |
|--------|-------|
| Total F\*/Pulse files | 146 |
| Total lines of code | ~67K (specs & proofs ~60K, impl ~7K) |
| `common/` | 17 files, 1.1K lines — shared heap model, object layout, graph theory, DFS |
| `mark-and-sweep/` | 65 files, 6.4K lines — major GC (mark, sweep, coalesce, allocator) |
| `generational/` | 64 files, 4.3K lines — minor GC (Cheney BFS, promotion, remembered set) |
| Admits/assumes | **0** across entire codebase |
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
| **Remembered set (scan)** | ✅ Spec: scan major heap for minor refs | `GC.Gen.Remembered` |
| **Infix tag support** | ✅ well_formed_heap parts 3 & 4 | `GC.Spec.Fields` |
| **No-scan invariant** | ✅ Named predicate preserved by GC ops | `GC.Spec.Fields.no_scan_invariant` |
| **Graph model** | ✅ Heap→graph bridge, DFS with termination | `GC.Spec.Graph`, `GC.Spec.HeapGraph`, `GC.Spec.DFS` |

### ⚠️ Spec Only / Incomplete

| Feature | Gap | Notes |
|---------|-----|-------|
| **Remembered set (impl)** | No Pulse implementation | `GC.Gen.Remembered.fsti` has the spec; no `GC.Gen.Impl.Remembered` exists. Currently the caller must pass remembered-set roots manually. |
| **Full generational GC loop** | Spec-only composition | `GC.Gen.Correctness.fsti` defines `generational_gc_end_to_end` (minor + major), but there is **no Pulse `fn` that calls `minor_collect` then `collect`** in sequence. |
| **Write barrier** | Placeholder only | `GC.Gen.Remembered.fsti` says "Future: write barrier that records stores into a card table." No spec or impl. |
| **Pointer-field rewriting (update_major_pointers)** | Spec proved, impl combined in Cheney | `GC.Gen.PromoteUpdate` proves preservation; the Pulse scan loop handles it. |

### ❌ Missing

| Feature | Impact |
|---------|--------|
| **Compaction** | OCaml 4 has optional compaction (`Gc.compact()`). Not modeled. |
| **Finalization** | No weak references, ephemerons, or custom finalizers. |
| **Custom blocks** | No `Abstract_tag` / custom `finalize`/`compare`/`hash` dispatch. |
| **Concurrent/incremental collection** | The `concurrent/` and `fly/` directories exist but are separate prototypes, not integrated. |
| **C runtime integration** | No `caml_alloc`, `caml_modify`, `caml_minor_gc` entry-point stubs matching OCaml's C API. |
| **Multiple minor-heap arenas** | OCaml 5 has per-domain minor heaps. Not applicable to OCaml 4 target, but worth noting. |

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
**This is a clean, strong impl→spec connection.** ✅

### 3.2 Generational (Minor) Correctness (⚠️ Gaps)

`GC.Gen.CheneyCorrectness.fsti` proves **5 unconditional** properties:
1. Object survival — pre-existing major objects survive
2. `well_formed_heap_part1` preserved
3. Allocator invariants preserved (fl_valid, fl_chain_terminates)
4. Minor reset (bump = 0)
5. Root rewriting correct

**Property 6 (BFS completeness)** is **weak** — the precondition assumes `fwd_map x ≠ 0UL` for all reachable objects, which is what the conclusion asserts. This is acknowledged in comments:
> "A stronger theorem would prove this from a SPACE precondition"

### 3.3 Impl→Spec Connection (⚠️ Indirect)

`GC.Gen.Impl.fsti`'s `minor_collect` postcondition states:
```
s2 == res.mc_major /\ fp2 == res.mc_fp /\ rs2 == res.mc_roots /\ U64.v b2 == 0
```
where `res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs`.

This connects the impl to `cheney_collect_spec`, but **does NOT directly state** `cheney_gc_correct` or `gen_gc_correct_full` in the postcondition. A caller must separately invoke `cheney_gc_correct` with the same preconditions to derive the correctness properties.

**Recommendation**: Add a spec-level lemma or richer postcondition that directly provides `cheney_gc_correct` to callers, avoiding the need to re-establish preconditions.

### 3.4 End-to-End Theorem (⚠️ Stated, Not Exercised)

`GC.Gen.Correctness.fsti` defines `generational_gc_end_to_end` composing minor + major, but:

- **No Pulse function exercises it** — there is no `full_gen_gc` that calls `minor_collect` then `collect`
- The theorem has **many preconditions** — some are structural (fine), but `all_promotions_succeed` and `post_promote_pointer_closure` are hard for a caller to establish in general
- `well_formed_heap` is only proved as `part1` by `cheney_gc_correct`; the full `well_formed_heap` (including part2 = pointer closure) requires `gen_gc_correct_full` which needs additional preconditions (`minor_fields_well_formed`, `all_promotions_succeed`, `allocated_objects_avoid_chain`, `post_promote_pointer_closure`)

### 3.5 Trust Assumptions

| Assumption | Location | Nature |
|------------|----------|--------|
| `minor_guards_complete` | `GC.Gen.MinorHeap.fsti:204` | Trusted: no fake headers in minor heap bodies. `[@@"opaque_to_smt"]`. Required at GC entry. Mutator responsibility. |
| `no_scan_invariant` | `GC.Spec.Fields.fst` | Trusted: no-scan objects don't contain valid heap pointers. Standard OCaml runtime guarantee. |
| `bounded_mark_inv` | `GC.Spec.MarkBoundedInv` | Stack capacity sufficient for DFS. Standard graph-theory bound. |
| Heap size configuration | `GC.Spec.Base.heap_size` | Configurable constant. |

All previous `admit()`/`assume_` calls have been eliminated. The remaining trust boundary is clean and well-documented.

## 4. Code & Proof Quality

### 4.1 Modularity (✅ Good)

The architecture is cleanly layered:
- **common/** provides reusable infrastructure (heap, objects, graph, DFS)
- **mark-and-sweep/** builds on common for the major GC
- **generational/** builds on both for the minor GC
- `.fsti` files provide clean abstraction boundaries
- Allocator lemmas were refactored from one 8000-line file into Core, Part1, Part2, Split, Header sub-modules

### 4.2 File Sizes (⚠️ Some Large Files)

Files > 1500 lines that could benefit from splitting:

| File | Lines | Notes |
|------|-------|-------|
| `GC.Spec.Mark.fst` | 3932 | Largest file. Many helper lemmas. |
| `GC.Spec.Coalesce.fst` | 3482 | Complex coalescing invariant proofs. |
| `GC.Spec.Allocator.Lemmas.Part2.fst` | 3250 | Recently split from 8000-line parent; could split further. |
| `GC.Spec.Allocator.Lemmas.Core.fst` | 3093 | Core allocator lemmas. |
| `GC.Test.Bridge.fst` | 2693 | Test infrastructure. |
| `GC.Spec.Fields.fst` | 1896 | Well-formed heap + objects traversal. |
| `GC.Spec.MarkBoundedCorrectness.fst` | 1576 | Bounded-mark correctness. |

### 4.3 Proof Stability (⚠️ Some Fragility)

| Concern | Count | Notes |
|---------|-------|-------|
| `z3rlimit ≥ 500` in code | ~10 spots | Mainly in `GC.Lib.Header.fst` (bitvector arithmetic) and `GC.Spec.Fields.fst` |
| `z3rlimit ≥ 400` in Makefile | 3 files | `Allocator.Lemmas.{fst,Split,Part1}` |
| `z3rlimit ≥ 300` in Makefile | 1 file | `GC.Impl.MarkBounded.fst` |
| `z3refresh` usage | ~10 spots | Mark, MarkBounded, Impl — indicates proof instability |
| `--retry 3` | 1 spot | `GC.Impl.MarkBounded.fst:801` — known fragile proof |

**High-rlimit hotspots** to address:
- `GC.Lib.Header.fst` (z3rlimit 800) — bitvector operations; consider `calc` proofs or `FStar.BV` lemmas
- `GC.Spec.Fields.fst:1243` (z3rlimit 800) — objects termination proof; may need explicit recursion metric

### 4.4 Duplication (⚠️ Moderate)

- `objects zero_addr` / `objects 0UL` appears 1825 times across the codebase — this is expected (core traversal function)
- `alloc_spec` is referenced in 35 files across mark-and-sweep and generational — good sharing via common modules
- The allocator is shared: generational's `GC.Gen.Allocator` wraps `GC.Spec.Allocator` — no duplication
- Mark-and-sweep's `GC.Impl.Mark.fst` (773 lines) and `GC.Impl.MarkBounded.fst` (1303 lines) have significant structural similarity — potential for shared abstractions

### 4.5 Interface Quality (✅ Mostly Good)

Strong points:
- `GC.Impl.fsti` directly states `full_gc_correctness` in postcondition ✅
- `GC.Gen.CheneyCorrectness.fsti` has clear, individually-named properties ✅
- `GC.Gen.Promote.fsti` exports equation lemmas (base/step/skip/oom) for client reasoning ✅
- Key predicates like `well_formed_heap` are `opaque_to_smt` with reveal lemmas ✅

Weak points:
- `GC.Gen.Impl.fsti` postcondition connects to `cheney_collect_spec` but not to `cheney_gc_correct` directly ⚠️
- `GC.Gen.Correctness.fsti` has complex preconditions that a full-gen-GC caller would struggle to establish ⚠️
- No `.fsti` for `GC.Gen.Impl.Cheney` — all functions are module-private (OK for encapsulation, but prevents unit testing) ⚠️

## 5. Roadmap to Drop-In OCaml 4 Replacement

### Phase 1: Close the Verification Gaps (Estimated: Medium Effort)

1. **Strengthen Property 6 (BFS completeness)**
   - Replace circular precondition with space precondition: "free-list capacity ≥ total size of reachable minor objects"
   - Prove: sufficient space ⟹ no OOM ⟹ all reachable objects forwarded
   - This completes the correctness story for liveness

2. **Connect impl to correctness theorem**
   - Either: enrich `minor_collect` postcondition with `cheney_gc_correct`
   - Or: provide a wrapper lemma in `GC.Gen.Impl.fsti` that derives correctness from the spec-refinement postcondition

3. **Prove `gen_gc_correct_full` preconditions are establishable**
   - Show that `well_formed_heap major ∧ minor_wf minor` is sufficient to derive `minor_fields_well_formed` and `post_promote_pointer_closure` (or strengthen `minor_wf` to include them)

### Phase 2: Build the Full Generational GC (Estimated: Significant Effort)

4. **Implement `GC.Gen.Impl.Remembered`**
   - Pulse implementation of major-heap scan for minor refs
   - Use existing `GC.Gen.Remembered.fsti` spec
   - Postcondition: result contains all inter-generational pointers (completeness)

5. **Implement full generational GC entry point**
   - New Pulse `fn gen_gc (...)`: calls `minor_collect`, then `collect`
   - Postcondition: `generational_gc_end_to_end`
   - This is the top-level function with the end-to-end theorem

6. **Write barrier (card table)**
   - Replace full-heap scan with write barrier for remembered set
   - Spec: `caml_modify(obj, field, new_val)` records obj in card table if new_val is minor pointer
   - Impl: Pulse atomic write + card-table update

### Phase 3: OCaml C API & Runtime Integration (Estimated: Large Effort)

7. **C API stubs**
   - `caml_alloc(wosize, tag)` → `gen_alloc`
   - `caml_minor_gc()` → `minor_collect`
   - `caml_major_gc()` → `collect`
   - `caml_modify(obj, field, val)` → write barrier + store
   - Match OCaml 4's `caml/memory.h` signatures

8. **Root registration**
   - `caml_register_global_root`, `caml_register_generational_global_root`
   - Stack scanning or explicit root set

9. **KaRaMeL extraction cleanup**
   - Ensure clean C output from both GCs
   - Minimize extern dependencies
   - Integrate into OCaml's build system

### Phase 4: Feature Parity (Estimated: Large Effort)

10. **Compaction** — optional heap compaction to reduce fragmentation
11. **Finalization** — weak references, ephemerons, custom finalizers
12. **Custom blocks** — Abstract_tag support

## 6. Summary Assessment

| Dimension | Grade | Notes |
|-----------|-------|-------|
| **Spec correctness** | A- | 5-pillar mark-and-sweep theorem is strong. Minor GC has BFS completeness gap. |
| **Impl-spec connection** | B+ | Mark-and-sweep: excellent (postcondition = theorem). Generational: good but indirect. |
| **Trust boundary** | A | Zero admits. Two clean, documented trust assumptions (minor_guards_complete, no_scan_invariant). |
| **Proof stability** | B- | Several high-rlimit spots (800). Some z3refresh/retry needed. Bitvector proofs are fragile. |
| **Modularity** | B+ | Clean layers. Some large files (Mark.fst 3.9K, Coalesce 3.5K) could be split. |
| **Feature completeness** | C+ | Core GC works. Missing: remembered set impl, write barrier, full gen-GC entry point, C API. |
| **Drop-in readiness** | D+ | Fundamental algorithms are verified, but significant engineering work remains for OCaml integration. |

### Bottom Line

The **core algorithms are correctly specified and verified**: mark-and-sweep with all 5 correctness pillars, and Cheney BFS minor collection with 5 unconditional properties. The trust boundary is minimal and clean. However, reaching a **drop-in OCaml 4 replacement** requires:

1. Closing the BFS completeness gap (Property 6) — pure spec work
2. Building the full generational GC entry point (minor + major composition) — Pulse engineering
3. Implementing the write barrier and remembered set — significant new verification
4. C API integration — primarily engineering, not verification

The project is approximately **60% of the way** to a verified drop-in replacement, with the hardest verification work (correctness theorems) already done. The remaining work is primarily engineering (Pulse implementations, C integration) rather than foundational specification.
