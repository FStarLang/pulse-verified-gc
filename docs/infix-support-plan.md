# Plan: supporting infix pointers in the heap model

Status: **proposal, not started.** Written for review.

## 1. The defect

`well_formed_heap` is the precondition of essentially every correctness theorem
in the repository (1,129 references across 105 files). Two of its four clauses
interact to exclude a class of real OCaml heaps.

`common/spec/GC.Spec.Fields.fst:507`:

```fstar
let well_formed_heap_part2 (g: heap) : prop =
  (forall (src dst: obj_addr).
    (Seq.mem src (objects zero_addr g) /\
     (let wz = wosize_of_object src g in
      U64.v wz < pow2 54 /\
      exists_field_pointing_to_unchecked g src wz dst)) ==>
    Seq.mem dst (objects zero_addr g))
```

`exists_field_pointing_to_unchecked` (`:79`) tests fields with `is_pointer_to`
(`:61`), which compares `hd_address fv` against `hd_address target` on the
**raw** stored word. Neither function calls `resolve_object`. So the `dst` that
part 2 requires to be an enumerated object is the literal field contents.

`common/spec/GC.Spec.Fields.fst:518`:

```fstar
let well_formed_heap_part4 (g: heap) : prop =
  (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==> ~(is_infix obj g))
```

Together: **no field of any major-heap object may point to a major-heap infix
object.** Mutually recursive OCaml closures produce exactly such fields. The
theorems are sound; their precondition is unsatisfiable for those heaps.

### Why the object list excludes infix objects

`objects` (`GC.Spec.Fields.fst:185`) walks the heap by `wosize`. A closure's
`wosize` spans its infix sub-objects, so the walk steps over them. Part 4 is
therefore consistent with the walk — but note it is *stipulated*, not derived:
`wf_objects_non_infix` (`:613`) has `reveal_opaque` as its entire body. It reads
part 4 back out; it does not prove anything about the walk.

## 2. Verified consequences

Confirmed against `gc_gen_impl_spec_tightening` @ `5c931eb`.

| Consequence | Evidence |
| --- | --- |
| Part 3 (`infix_wf`) is **vacuous** | `infix_wf` (`GC.Spec.Object.fst:717`) quantifies over `Seq.mem h objs /\ is_infix h g`; part 4 makes that unsatisfiable. `parent_closure_addr_nat`, `infix_wf_elim`, `infix_wf_intro` do no work inside `well_formed_heap`. |
| `resolve_object` is **provably the identity** in Mark | `GC.Spec.Mark.fst` calls it at ~60 sites; three are immediately followed by `wf_resolve_identity`, which derives `child == child_raw` from part 4. |
| The graph model **never resolves** | `get_pointer_fields_aux` (`GC.Spec.HeapGraph.fst:115`) conses the raw `v`. Grepping `GC.Spec.HeapGraph.fst` for `resolve_object` or `is_infix` returns **0** hits. |
| Part 2 is exactly what makes the graph well formed | `graph_wf` (`GC.Spec.Graph.fst:88`) requires both edge endpoints to be vertices; vertices are `objects` (`HeapGraph.fst:208`). An infix target would be an edge to a non-vertex, so `create_graph_wf_from_heap` (`GC.Spec.Mark.fsti:519`) would fail. |

## 3. Corrections and additions to the finding

The PDF is accurate on the core claim. Five points need amending or adding, and
the third one changes the shape of the fix.

1. **`wf_objects_non_infix` does not prove non-infixness.** The PDF says it
   "proves that no member of the object set is infix". Its body is
   `reveal_opaque`. Non-infixness is an assumption (part 4), not a theorem.

2. **Part 3 is vacuous.** Not mentioned. It matters: the parent-closure
   machinery already exists and is already wired into `well_formed_heap`, but
   currently guards an empty set. The fix repoints it rather than inventing it.

3. **The extracted mark/sweep C would corrupt the heap, not handle it.** The PDF
   says "the extracted C code checks for infix objects and would handle them."
   That is true of the *minor/Cheney* path only. The major mark path does not
   resolve, and would not merely mis-handle an infix target — it would lose the
   parent. In `generational/snapshot/GC_Gen_Impl.c`:

   ```c
   void check_and_darken_bounded(heap_t heap, gray_stack_rec st, uint64_t v) {
     bool is_ptr = is_pointer(v);
     if (is_ptr) {
       uint64_t target_hdr = v - 8ULL;        /* raw field value */
       darken_if_white_bounded(heap, st, target_hdr);
     }
   }
   ```

   Given an infix target this greys the **infix header** and pushes the infix
   address. `mark_step_bounded_impl` then pops it, reads `wz`/`tag` from the
   infix header, and since `tag == 249 < no_scan_tag` it *scans* `wz` words from
   the infix address — `wz` being the parent offset, not a field count. The
   parent closure is never darkened, stays white, and is reclaimed by the sweep,
   leaving the infix pointer dangling.

   **This is the load-bearing correction.** The gap is not "spec is narrower
   than the code". The precondition is currently the only thing preventing a
   real bug. Fixing the specification without fixing `check_and_darken_bounded`
   would turn an unsatisfiable precondition into an unsound collector.

4. **All four source/target combinations are excluded, not just major→major.**
   The generational layer forbids the rest by explicitly named preconditions in
   `GC.Gen.HeapInvariant.fsti`: `minor_fields_no_infix_targets` (minor→minor)
   and `major_minor_fields_no_infix_targets` (major→minor). Infix addresses
   survive only as *roots* and inside Cheney's promotion machinery.

5. **The two halves of the codebase disagree on how to compute an infix
   object's parent, and the major-heap one is wrong.** Not in the PDF; found
   while checking the phase 4 sketch below.

   Both read the *same* header word (`obj - 8`) and extract the *same* field
   (`hdr >> 10`), then interpret it differently:

   | | Formula | Source |
   | --- | --- | --- |
   | minor | `parent = infix - wosize*8` | `GC.Gen.MinorHeap.infix_parent` (`:230`) |
   | major | `parent = infix - 8 - wosize*8` | `GC.Spec.Object.parent_closure_addr_nat` (`:695`) |

   Their doc comments state the conflicting conventions outright — "word offset
   from infix val to parent val" versus "offset from parent's obj_addr to infix
   header". They differ by exactly one word, so at most one can be right.

   OCaml's runtime does `v -= Infix_offset_val(v)` with
   `Infix_offset_hd(hd) = Bosize_hd(hd) = Wosize_hd(hd) * sizeof(value)`, i.e.
   `parent = infix - wosize*8`. **The minor version is correct; the major
   version is off by 8 bytes.** The extracted C agrees with the minor version
   (`forward_if_minor_infix`: `uint64_t parent = addr - wosize * 8ULL;`).

   This is currently harmless *only* because part 3 is vacuous (§2), so
   `parent_closure_addr_nat` is unreachable — it is reached solely through
   `infix_wf`, which quantifies over an empty set, and through
   `resolve_object`, which is provably the identity. It is dead code that
   happens to be wrong.

   It is also exactly the definition phase 1 would build on. Fixing it is
   therefore a prerequisite, not a cleanup, and it belongs in phase 0 where it
   can be landed and verified in isolation while it is still dead.

6. **The minor heap's infix support is an over-approximation, and it is
   under-specified.** `find_infix_parents`
   (`generational/impl/GC.Gen.Impl.MinorHeap.fst:615`) pre-scans the minor heap
   and appends the *parent* of every embedded infix header to the root array.
   That is why the minor side can forbid infix field targets and still be
   correct — every closure containing an infix part is unconditionally rooted.
   It is sound but imprecise (it retains closures that are actually garbage),
   and the Pulse postcondition of `maybe_add_infix_parent` is purely structural
   (`Seq.length rs2 == SZ.v cap /\ SZ.v cnt2 >= SZ.v cnt`) — it does not say
   *which* parents were added, so nothing downstream can use it. The
   over-approximation is invisible to the proof.

## 4. Design options

### Option A — resolve only at the graph boundary

Change `get_pointer_fields_aux` to emit `resolve_object v g`; leave part 2 raw.

Rejected. Part 2 is what establishes `graph_wf`; leaving it raw means an infix
target still violates it before the graph is ever built. This fixes a symptom.

### Option B — resolve in the heap model (recommended)

Three coordinated changes, all behind the existing `opaque_to_smt` boundary:

- Part 2 requires the **resolved** target to be enumerated.
- Part 3 stops quantifying over `objs` (vacuous) and starts quantifying over
  **field targets that are infix**, which is where the parent-validity
  obligation actually belongs.
- The graph resolves, so vertices remain exactly `objects` and `graph_wf` is
  preserved by construction.

Sketch:

```fstar
(* target of a field, with interior pointers mapped to the enclosing closure *)
let field_target (g: heap) (fv: U64.t{is_pointer_field fv}) : GTot obj_addr =
  resolve_object (fv <: obj_addr) g

let well_formed_heap_part2 (g: heap) : prop =
  forall (src: obj_addr) (j: nat).
    Seq.mem src (objects zero_addr g) /\ j < U64.v (wosize_of_object src g) /\ ... ==>
    (let fv = read_word g (field_addr src j) in
     is_pointer_field fv ==> Seq.mem (field_target g fv) (objects zero_addr g))

let well_formed_heap_part3 (g: heap) : prop =
  forall (src: obj_addr) (j: nat).
    (* every infix field target has a valid, enumerated, closure-tagged parent *)
    ... is_infix (fv <: obj_addr) g ==>
    (let p = parent_closure_addr_nat (fv <: obj_addr) g in
     p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
     Seq.mem (U64.uint_to_t p) (objects zero_addr g) /\
     is_closure (U64.uint_to_t p) g)
```

Part 4 is unchanged: the object *list* still excludes infix objects, which is
what keeps the sweep and the allocator walk correct.

Note the safety argument this depends on. `resolve_object` computes the parent
from the infix object's own header (`parent_closure_addr_nat h g = h - 8 -
wosize(h) * 8`), i.e. from mutable heap data. Part 3 is what makes that read
trustworthy, which is precisely why part 3 must be repointed at field targets in
the same change that makes part 2 depend on `resolve_object`. Doing one without
the other yields a model that trusts an unvalidated heap word.

Reachability semantics become closure-level: marking is closure-granular, which
is what OCaml does and what the sweep requires (it frees whole blocks).

### Option C — admit infix objects as graph vertices

Rejected. It would make the vertex set disagree with `objects`, breaking the
sweep, the allocator free-list walk, and `coerce_to_vertex_list`, and it would
require edge-level reasoning about partial-block liveness. Much larger change
for a worse model.

## 5. Phased plan

Each phase ends at a green `make -k -j24 verify`. Phases 1–3 touch no
extractable code, so `generational/snapshot/` must stay byte-identical
throughout; phase 4 is the only one that changes C.

### Phase 0 — characterise the boundary, and fix the parent formula

Two deliverables, both semantically inert today.

**0a. Correct `parent_closure_addr_nat`.** Change it to `infix - wosize*8`,
matching OCaml, the minor heap, and the extracted C (§3.5). While part 3 is
vacuous this provably changes nothing, which is precisely why it should land
now, in isolation, rather than during phase 1 when it would be load-bearing and
entangled. Align the doc comment, and consider unifying with
`GC.Gen.MinorHeap.infix_parent` so the convention cannot drift again.

**0b. Characterise the part-2 access surface.**
The change is tractable only because `well_formed_heap` is `opaque_to_smt` and
part 2 is directly referenced in just 20 places across 9 files. Everything else
goes through a small lemma surface in `GC.Spec.Fields.fst`:

- reads: `wf_object_size_bound` (`:592`), `wf_object_bound` (`:599`),
  `wf_objects_non_infix` (`:613`), `wf_infix_wf` (`:627`),
  `wf_field_target_in_objects` (`:634`), `field_pointer_target_in_objects`
  (`:644`), `points_to_target_in_objects` (`:660`)
- writes: `well_formed_heap_part2_from_field_closure` (`:677`),
  `field_write_preserves_wf` (`:1485`)

Deliverable: confirm this is the complete surface, and add any missing accessor
so that no client reads part 2 directly. Verify unchanged. This phase is what
makes phases 1–3 mechanical rather than exploratory.

### Phase 1 — resolution-aware model in `common/spec`

1. `GC.Spec.Object`: keep `resolve_object`; add the lemmas the new clauses need
   (`resolve_idempotent`, `resolve_in_objects_of_part3`, and preservation of
   `resolve_object` under `set_object_color` — the last is required because Mark
   recolours as it goes and currently relies on `color_change_preserves_is_infix`).
2. `GC.Spec.Fields`: restate parts 2 and 3 as above. Re-prove the accessor
   surface from phase 0. `wf_field_target_in_objects` gains a `resolve_object`
   in its conclusion; `field_write_preserves_wf`'s precondition weakens from
   `Seq.mem v (objects ...)` to `Seq.mem (resolve_object v g) (objects ...)`.
3. `GC.Spec.HeapGraph`: `get_pointer_fields_aux` emits `resolve_object v g`.
   Re-prove `get_pointer_fields_aux_mem` (`:279`), `object_edges` (`:156`),
   `all_edges` (`:161`), and the `pointer_field_is_graph_edge` bridge.
4. Re-prove `create_graph_wf_from_heap`.

Highest-risk phase. `GC.Spec.Fields.fst` is 1,608 lines and the write-side
lemmas (`write_word_field_pointing_self_implies` at `:1338`, already at
`--z3rlimit 200 --fuel 4 --ifuel 2`) reason by induction over
`exists_field_pointing_to_unchecked`. Changing that predicate's shape will
disturb them. Mitigation: keep the raw predicate under its current name for the
induction, and define the resolved clause on top of it, so the existing
inductions are reused rather than redone.

### Phase 2 — mark-and-sweep specs

`GC.Spec.Mark` (3,693 lines) already threads `resolve_object` through ~60 sites,
so most call sites are shaped correctly; what changes is that
`wf_resolve_identity` is no longer available and the three sites that use it
(`:2598`, `:3456`, `:3693`) need the resolved-target fact instead. Also
`GC.Spec.MarkBounded`, `GC.Spec.MarkBoundedCorrectness`.

`GC.Spec.Sweep` should be unaffected: it walks `objects`, which still excludes
infix objects. The one interaction is `field_write_preserves_wf` at
`Sweep.fst:138` (free-list threading), whose precondition weakens.

### Phase 3 — generational layer

Drop `major_minor_fields_no_infix_targets`, then
`minor_fields_no_infix_targets`, from `collection_heap_shape`, replacing each
with the resolved-target obligation. Cheney's forwarding is already infix-aware
(`forward_if_minor_infix`, `synthesize_infix_forwarding`), so this is mostly
re-proving `GC.Gen.CheneyPreservation*` with the weaker hypothesis. Expect the
`normal_vertex_ready` hypothesis chain (`is_infix (fwd x) major_final = false`,
carried but never derived — see §6.9 of `PROOF_COMPLEXITY.md`) to finally need a
real proof here, since it is currently discharged by assumption.

Optionally retire `find_infix_parents` once resolution is real, or give it a
meaningful postcondition. Retiring it is a precision win: it currently roots
every closure with an infix part, garbage or not.

#### Phase 3 status

**Step 3a — done** (commit *"make the combined graph resolution-aware for major
fields"*).  `GC.Gen.CombinedGraph.classify_major_field` now returns
`MajorV (resolve_object v major)` whenever the *resolved* value is enumerated,
instead of dropping the edge when the raw value is interior.  Its guard also
strengthened from `is_val_addr v` to `is_val_addr v && is_pointer_field v`,
which is not a narrowing (every enumerated object lies above `zero_addr`, so any
`v` that passed the old test already satisfied `is_pointer_field`) and which buys
callers `points_to` for the raw target even when that target is interior.
`GC.Gen.ReachabilityBridge.major_edge_points_to` was restated to expose the raw
field value together with `dst == resolve_object raw major`, and
`no_infix_field_targets` was dropped from all three `ReachabilityBridge` lemmas
and from `combined_reachable_major_edge_forwarded`.  This removes the *graph*
obstruction: the combined graph no longer under-approximates the object graph in
the presence of interior pointers.

**Step 3b — not landed.**  `no_infix_field_targets major` is still a conjunct of
`GC.Gen.HeapInvariant.major_heap_shape`.  What remains is not graph reasoning
but the Cheney/allocator layer, and it splits into two parts.

*The tractable part.*  `GC.Gen.CheneyPreservation.fst:1479` and
`GC.Gen.CheneyPreservation.NoBlue.fst:71,72,187` consume the raw helpers
`GC.Gen.NoBlueUtil.field_pointer_target_in_objects_nat_raw` and
`field_pointer_no_blue_raw`.  Their goals are *already* resolved
(`~(is_blue (resolve_object dst h) h)`), so switching to the resolved
`NoBlueUtil` variants is the right move; what is then missing is header
stability for a possibly-interior `dst` across `cheney_promote` and
`update_major_pointers`.  That is exactly the job of the three private helpers
added to `GC.Gen.MinorCollectForwarding.Edges.fst` in step 3a
(`cheney_promote_frame_target_header`, `update_major_pointers_frame_target_header`,
`cheney_collect_frame_target_header`); they would have to be relocated into a
module upstream of `CheneyPreservation`.  Mechanical, but slow to iterate
(`GC.Gen.CheneyPreservation.fst` takes ~8 min per verify).

*The blocking part.*  `blue_fields_closed` (`GC.Gen.Promote.fsti:584`) is stated
raw — every pointer-looking field of a **blue** (free-list) object targets an
enumerated object — and is derived from `well_formed_heap_part2` by
`GC.Gen.PromoteUpdate.BlueAlloc.wfh_part2_implies_blue_fields_closed`, which
needs `no_infix_field_targets` for precisely that step.  Restating
`blue_fields_closed` in resolved form was tried and measured: it costs only
three broken sites (`PromoteUpdate.Header.fsti:52`, `BlueAlloc.fst:88`,
`BlueProm.fst:263`), the first two mechanical.  The third,
`promote_object_preserves_bfc_close`, does not go through.  It must transport
`Seq.mem (resolve_object v new_major) (objects new_major)` to
`Seq.mem (resolve_object v g') (objects g')`, where `g'` is `new_major` after
`copy_fields`, `zero_promote_padding` and `set_promoted_tag` on the freshly
carved block `dst_obj`.  Two cases arise that the raw statement did not have:

1. `v == dst_obj`.  Dischargeable: add `minor_tag minor obj <> infix_tag` to the
   requires, which callers already have — it is a precondition of the sibling
   `promote_object_preserves_wfh_part4` (`GC.Gen.Promote.fsti:526`).
2. `resolve_object v new_major == dst_obj` with `v` strictly interior to
   `dst_obj`.  **Not dischargeable today.**  `dst_obj` is a block just carved off
   the free list, so in `new_major` its fields still hold stale garbage; nothing
   rules out a *different* blue object holding a pointer into the middle of it,
   with the word at `hd_address v` happening to look like an infix header.
   `copy_fields` overwrites that word, so the resolution of `v` can change.

Closing case 2 needs a genuine new invariant — something like *no blue object's
field points strictly inside another blue object* — which must then be
established at allocator boundaries and preserved across the whole minor
collection.  That is a scope increase comparable to phase 1, not a clean-up, and
it is why step 3b is parked rather than half-landed.

Narrowing `no_infix_field_targets` to blue objects only was also considered and
rejected: `CheneyPreservation.NoBlue.fst:71` needs the clause for a **non-blue**
`src`, so the narrowed form is not strong enough, and preserving it across
`cheney_collect` is itself a fresh obligation of similar difficulty.

**Consequence.**  The heaps built by
`generational/ocaml-integration/tests/infix_closures.ml` run correctly under the
verified generational runtime, but they violate `no_infix_field_targets` and so
fall outside `major_heap_shape`; the composed `gen_gc` theorem does not yet
cover them.  The major-heap (mark-and-sweep) model *is* infix-correct after
phases 1–2.

### Phase 4 — implementation and extraction

Change `check_and_darken_bounded` (`GC.Impl.MarkBounded`) to resolve before
darkening:

```c
uint64_t hdr = read_word(heap, v - 8);
if ((hdr & 0xFF) == 249ULL)          /* infix_tag */
  v = v - (hdr >> 10U) * 8ULL;       /* parent closure; cf. §3.5 */
darken_if_white_bounded(heap, st, v - 8);
```

This is the only phase that changes extracted C, and it is mandatory — see
§3.3. Re-verify the Pulse proof, re-extract, and **deliberately update**
`generational/snapshot/`, reviewing the C diff. Then re-run
`generational/ocaml-integration/tests`.

### Phase 5 — audit

Extend the three-object SPOT fixture with a fourth object: a closure with an
infix part, pointed at from a major field. This is the fixture that cannot be
built today. (Deferred by request; listed for completeness.)

## 6. Risks

| Risk | Assessment |
| --- | --- |
| Phase 1 destabilises `GC.Spec.Fields.fst` write lemmas | Highest risk. Mitigated by layering the resolved clause over the existing raw predicate. |
| Proof-time regressions from an extra `resolve_object` unfolding on every field access | Real. `resolve_object` is a two-branch `GTot`; keep it opaque with explicit intro/elim lemmas rather than letting Z3 unfold it under a quantifier. |
| Phase 3 uncovers that `is_infix (fwd x) major_final = false` is not actually provable | Possible. It is assumed everywhere today. If it fails, Cheney's forwarding needs a genuine invariant, which would be a scope increase. |
| Extracted C changes | Certain, and intended (phase 4). Everything before phase 4 must leave the snapshot byte-identical, which is a useful checkpoint. |
| `parent_closure_addr_nat` trusts a heap word | Addressed by repointing part 3 at field targets — but only if phases 1.2 land together. |
| The major/minor parent-formula disagreement (§3.5) is discovered late | Eliminated by making it phase 0a, where it is still dead code. If left until phase 1 it would present as an inexplicable off-by-one in the middle of the hardest re-proof. |

## 7. Sequencing

Phases are strictly ordered; each is independently verifiable and committable.
Phase 0 is cheap and de-risks the rest. Phase 1 is the bulk of the work. If
phase 3 stalls on the `normal_vertex_ready` issue, phases 0–2 still stand on
their own: they would make the *major* heap model infix-correct while the
generational layer keeps its current preconditions.

## 8. Recommendation

Do phase 0 first and report. Both halves are small and semantically inert
today: 0a corrects a wrong formula while it is still unreachable, and 0b
converts the central open question — *is the part-2 access surface really only
nine lemmas?* — from an estimate into a fact. The size of phases 1–2 depends
entirely on that answer.

Note that §3.3 and §3.5 are independently worth acting on even if the rest of
this plan is declined: the first says the current precondition is the only thing
standing between the collector and a dangling-pointer bug, and the second says a
core address computation is wrong. Both are cheap to record and cheap to fix.
