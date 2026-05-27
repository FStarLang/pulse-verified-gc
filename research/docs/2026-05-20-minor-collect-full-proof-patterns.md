# Minor collect full proof patterns

## 1) Modular preservation lemma files + `.fsti` interfaces

### Pattern 1: Thin wrapper `.fst` re-exporting split lemma modules
**Found in**: `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.fst:1-60`

This module is a wrapper that re-exports lemmas from split implementation files while keeping the existing interface stable.

```fstar
module GC.Spec.Allocator.Lemmas
open GC.Spec.Allocator.Lemmas.Core
open GC.Spec.Allocator.Lemmas.Part1
open GC.Spec.Allocator.Lemmas.Part2

let fl_valid = fl_valid
let fl_chain_terminates = fl_chain_terminates
let alloc_spec_preserves_wf = alloc_spec_preserves_wf
let alloc_spec_preserves_objects_part1 = alloc_spec_preserves_objects_part1
```

**Key aspects**:
- `Core`, `Part1`, `Part2`, `Split`, and `Header` are separated into smaller proof files.
- The wrapper keeps the API names stable for older callers and `.fsti` files.

### Pattern 2: Interface-only declarations for the Pulse-facing module
**Found in**: `generational/impl/GC.Gen.Impl.fsti:223-230`

```fstar
fn minor_collect_full (gh: gen_heap_t)
                      (roots: array U64.t) (nroots: SZ.t)
                      (fwd_arr: array U64.t)
                      (queue: larray U64.t Cheney.queue_size)
                      (slots: array U64.t) (nslots: SZ.t)
```

**Used for**:
- Exposing the verified Pulse entrypoint contract separately from the implementation.
- Keeping the interface small while the proof body stays in `GC.Gen.Impl.fst`.

### Pattern 3: Dedicated `.fsti` for a proof bundle split out of a larger spec file
**Found in**: `generational/spec/GC.Gen.PromoteUpdate.fsti:1-40`

```fstar
module GC.Gen.PromoteUpdate
open GC.Gen.Promote

val update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major)
```

**Key aspects**:
- The `.fsti` collects `val` declarations for update/promotion lemmas.
- The implementation is split into multiple files such as `Aux`, `Field`, `Header`, `Obj`, `Positional`, and `PromoteFields`.

### Pattern 4: Large proof bundle further split into named submodules
**Found in**: `generational/spec/GC.Gen.PromoteUpdate.PromoteFields.fsti:1-20`

```fstar
module GC.Gen.PromoteUpdate.PromoteFields
open GC.Gen.PromoteUpdate.PromoteFields.ChainInv
open GC.Gen.PromoteUpdate.PromoteFields.Step
open GC.Gen.PromoteUpdate.PromoteFields.FieldsPres
```

**Used for**:
- Isolating chain invariants, step lemmas, and field-preservation recursion in separate files.

---

## 2) Low-rlimit proof options and verification-order conventions

### Pattern 1: Small solver limits at module scope, then tighter per-lemma overrides
**Found in**: `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.Split.fst:13-20`

```fstar
/// Module-level default
#push-options "--z3rlimit 20 --z3refresh"

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let alloc_exact_preserves_wf ...
```

**Key aspects**:
- A low default rlimit is set for the whole module.
- Harder lemmas temporarily raise the limit and disable fuel.

### Pattern 2: Recursive proof with `#restart-solver` and fuel 0
**Found in**: `generational/spec/GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:1-70`

```fstar
#restart-solver
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --split_queries always --z3refresh"
private let rec promote_all_aux_preserves_fields ...
```

**Used for**:
- Preventing proof-context buildup across recursive induction.
- Making step cases explicit and local.

### Pattern 3: Very small limits for helper lemmas that only bridge one fact
**Found in**: `generational/spec/GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:1-40`

```fstar
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private let chain_all_inv_extend_skip ...

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
private let rec fields_match_minor_extend_zero ...
```

**Key aspects**:
- Small helper lemmas are kept cheap and local.
- Larger recursive lemma is separated from local invariant-bridging lemmas.

### Pattern 4: Pulse implementation uses low-rlimit proof block around a large fn
**Found in**: `generational/impl/GC.Gen.Impl.fst:716-717`

```fstar
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
fn minor_collect_full (gh: gen_heap_t) ...
```

**Verification-order convention**:
- The top-level verified implementation is wrapped in a lower rlimit than some supporting spec lemmas.
- The function body is structured as phases, with intermediate ghost facts asserted between phases.

---

## 3) Splitting large F* proofs into pure lemmas used from Pulse implementations

### Pattern 1: Pure recursive lemma proves preservation, then Pulse implementation calls it as a fact
**Found in**: `generational/spec/GC.Gen.Promote.fst:1131-1180` and `generational/impl/GC.Gen.Impl.fst:663-676`

Spec-side lemma:
```fstar
/// promote_all preserves well_formed_heap_part1
let rec promote_all_aux_preserves_objects ...
```

Pulse-side usage:
```fstar
// Promotion preserves well_formed_heap_part1
GC.Gen.Promote.promote_all_preserves_objects minor alloc_res.heap_out obj dst_obj wosize;
```

**Key aspects**:
- The pure proof is isolated in the spec module.
- Pulse uses the result as a trusted lemma step in a larger verified procedure.

### Pattern 2: Write-body preservation factored out of the main promotion proof
**Found in**: `generational/spec/GC.Gen.WriteBodyLemmas.fsti:1-70`

```fstar
val copy_fields_preserves_objects_aux ...
val write_body_preserves_fl_valid_aux ...
val write_body_preserves_not_in_fl_chain ...
val write_body_preserves_fl_chain_terminates ...
```

And the module is explicitly described as isolated to reduce solver pollution:
```fstar
/// These proofs are isolated here to limit Z3 context pollution in the main
/// GC.Gen.Promote module.
```

**Used for**:
- Small, reusable lemmas about writes inside object bodies.
- Keeping the main promotion proof focused on control flow, not arithmetic/frame details.

### Pattern 3: Main recursive proof decomposed into helper lemmas for one-step transitions
**Found in**: `generational/spec/GC.Gen.PromoteUpdate.PromoteFields.FieldsPres.fst:1-80`

```fstar
private let promote_all_step_case ... = promote_all_aux_step minor major fp live_set fwd idx
```

and:
```fstar
private let rec promote_all_aux_preserves_fields ...
```

**Key aspects**:
- A generic recursive lemma is supported by a helper that bridges exactly one inductive step.
- The helper avoids unfolding the whole recursion in the main proof.

### Pattern 4: Bridge lemmas that rewrite a high-level predicate into a concrete heap fact
**Found in**: `generational/spec/GC.Gen.PromoteUpdate.Aux.fsti:1-25`

```fstar
val update_all_objects_aux_preserves_objects ...
val update_major_pointers_preserves_wfh_part1 ...
val update_all_objects_aux_step ...
```

**Used for**:
- Allowing implementation code to call a lemma that directly matches the phase it is performing.

---

## 4) Existing major-GC precondition / heap well-formedness preservation lemmas

### Pattern 1: Major-GC precondition packaged as a named predicate
**Found in**: `generational/impl/GC.Gen.Impl.fst:45-77`

The file defines a top-level `gc_precondition` and references it in the post-minor/full-collection flow.

### Pattern 2: Full generational GC requires the major-GC precondition after minor collection
**Found in**: `generational/impl/GC.Gen.Impl.fst:717-780`

The `minor_collect_full` postcondition includes:

```fstar
SpecFields.well_formed_heap_part1 prom.major_final /\
(slots_pairwise_distinct 'sl (SZ.v nslots)
 ==> s2 == (CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs).mc_major)
```

and the nearby comments explicitly mention that the next step is to prove the major-GC precondition can be carried forward.

### Pattern 3: Mark-and-sweep uses well_formed_heap as the core preservation predicate
**Found in**: `mark-and-sweep/spec/GC.Spec.MarkBoundedInv.fst:5-58`

```fstar
/// Wraps well_formed_heap + bounded_stack_props (no gray_objects_on_stack)
...
: Lemma (requires well_formed_heap g /\ bounded_stack_props g st /\ ...)
   (ensures well_formed_heap g)
```

**Used for**:
- Capturing the heap invariant as a reusable pre/postcondition.
- Composing preservation lemmas with stack invariants.

### Pattern 4: Major-collection phase lemmas preserve `well_formed_heap`
**Found in**: `mark-and-sweep/spec/GC.Spec.SweepInv.fst:68-76` and `mark-and-sweep/spec/GC.Spec.SweepCoalesce.fst:48-117`

Examples:
```fstar
: Lemma (requires well_formed_heap g_post /\ ...)
        (ensures well_formed_heap g_post)
```

and multiple sweep/coalesce lemmas with `requires well_formed_heap g`.

### Pattern 5: Generational promotion proves `well_formed_heap_part1` preservation repeatedly
**Found in**: `generational/spec/GC.Gen.Promote.fst:1131-1180`, `generational/spec/GC.Gen.Promote.fst:1275-1334`

These top-level lemmas show that the promotion phase preserves the part-1 heap invariant, and the later phase preserves part-4 as well.

---

## 5) Existing admits / assumptions in analogous modules

### Pattern 1: Only explicit `assume val` found in the Pulse implementation heap/minor-heap modules
**Found in**:
- `common/impl/GC.Impl.Heap.fst:20-26`
- `generational/impl/GC.Gen.Impl.MinorHeap.fst:18-26`

```fstar
assume val platform_fits_u64 : squash SZ.fits_u64
```

**Observed context**:
- This is the platform-size assumption for 64-bit targets.
- It appears as the lone explicit assume in the implementation layer.

### Pattern 2: No `admit()` or `assume val` occurrences in spec bundles searched
**Found in**:
- `generational/spec/*.fst` — no matches for `admit\(|assume val`
- `mark-and-sweep/spec/*.fst` — no matches for `admit\(|assume val`

### Pattern 3: Opaque predicates are revealed locally rather than admitted
**Found in**:
- `generational/spec/GC.Gen.Promote.fst:1131-1180`
- `mark-and-sweep/spec/GC.Spec.Mark.fst:267`
- `mark-and-sweep/spec/GC.Spec.Coalesce.fst:2915`

Example:
```fstar
reveal_opaque (`%well_formed_heap) well_formed_heap;
```

**Used for**:
- Unlocking a predicate at exactly the proof points that need it.
- Avoiding global exposure of proof internals.

---

## 6) Most directly relevant `minor_collect_full` reference points

### Implementation contract and proof body
**Found in**: `generational/impl/GC.Gen.Impl.fsti:223-263`, `generational/impl/GC.Gen.Impl.fst:717-780`

The contract already encodes:
- `well_formed_heap`, `fl_valid`, `fl_chain_terminates`, dense heap, blue-chain invariants
- zeroed forwarding array
- minor heap guards/infix well-formedness
- ref-table soundness and completeness conditions
- post-state equality to the two-pass rewrite result

### Adjacent phase decomposition
**Found in**: `generational/impl/GC.Gen.Impl.fst:717-780`

The implementation is staged as:
1. `cheney_promote_phase`
2. `update_promoted_objects`
3. `rewrite_roots_impl`
4. `minor_heap_reset`

This mirrors the modular proof style used elsewhere: phase-specific lemmas plus a compact top-level orchestration.

