# Dead-code inventory

**Generated** by `make depgraph && make depgraph-inventory` — do not edit by hand.

- Roots: `GC.Impl`, `GC.Impl.Allocator`, `GC.Impl.MarkBounded`, `GC.Gen.Impl`, `GC.Gen.Impl.Cheney`, `GC.Gen.Impl.MinorHeap`, `GC.Gen.Impl.UpdatePtrs`, `GC.Gen.Impl.Promote`, `GC.Spec.Correctness`, `GC.Spec.MarkBoundedCorrectness`, `GC.Gen.CheneyCorrectness`, `GC.Impl.MarkBoundedRootLemmas`, `GC.Spec.FreeList.Sweep`, `GC.SPOT.CallFull`, `GC.SPOT.CallMinor`, `GC.SPOT.ConcreteCallFull`, `GC.SPOT.ConcreteCallMinor`, `GC.SPOT.ConcreteForwarding`, `GC.SPOT.ConcreteFull`, `GC.SPOT.ConcreteMajor`, `GC.SPOT.ConcreteMinor`, `GC.SPOT.ConcreteScenarios`, `GC.SPOT.ConcreteSetup`, `GC.SPOT.Layout`, `GC.SPOT.Postconditions`, `GC.SPOT.Preconditions`, `GC.SPOT.ThreeObjects`

- 139 modules, 2922 definitions, 1118 module edges
- **6 definitions (0%) are unreachable from the roots**
- 2 definitions are reachable only implicitly (SMT pattern / instance / axiom)

## Why this set is safe to delete

Reachability is computed transitively from the roots over every reference in the
`.checked` files, so the unreachable set is **closed**: if a definition is
referenced only by unreachable code, it is itself unreachable and already
appears below. Deleting the whole set therefore cannot strand a live definition,
and one pass reaches the fixpoint — no iterate-until-stable loop is needed.

Three caveats the graph *does* account for:

- **Pulse `fn` bodies.** Pulse type-checks its own definitions and hands F* an
  opaque `magic ()` stub, keeping the elaborated term in a serialised
  `sigmeta_extension_data` blob that is not an F* term. The graph would
  therefore miss every lemma invoked from a `fn` body. For those definitions
  only, the tool re-reads the body from the source and treats each identifier
  as a possible reference; this over-approximates, which is the safe direction.

- **SMT-pattern lemmas.** A lemma carrying `[SMTPat ...]` is used by Z3 without
  ever being named. These are classified *implicitly live*, not unreachable, and
  are excluded from the tables below.
- **Pattern-matched constructors.** `Pat_cons` heads are harvested separately,
  so a constructor that is only ever matched on is not mistaken for dead.

One caveat it does **not** account for: deleting a definition changes the SMT
context of every module that `open`s its module, which can perturb unrelated
proofs. That is why the plan below re-verifies after each phase.


## Removal plan

`make depgraph-prune` deletes the whole set mechanically: it locates each
definition by name in its `.fst` and `.fsti`, takes the doc comment,
attributes and standalone qualifiers with it, and collapses any
`#push-options`/`#pop-options` pair it empties. The unreachable set is
closed, so one pass reaches the fixpoint.

Validate with the full build (`make -k -j24`), the SPOT build
(`make -C spot -j24`) and extraction (`make extract`, expecting C that is
byte-identical modulo the KaRaMeL invocation banner). Bisect by module if a
proof breaks: the graph cannot see that deleting a definition also shrinks
the SMT context of every module that `open`s it.

The pruner refuses three things, which is why this report may never reach
zero:

- **`let x : squash p = ...`** — nothing ever *names* such a definition, but
  its type sits in the SMT context of every later proof in the module, so it
  is a fact rather than a callee. Deleting one breaks proofs that never
  mention it.
- **A `let rec ... and ...` group with a live member** — the group is
  syntactically indivisible. If every member is dead the pruner takes the
  whole group; otherwise it leaves it alone.
- **A definition it cannot find by name** — reported so it can be handled by
  hand rather than silently skipped.

### 4 partially-dead modules (6 definitions)

| Module | Defs | Dead | % | Area |
| --- | ---: | ---: | ---: | --- |
| `GC.Gen.MinorCollectForwarding.Reflection` | 16 | 2 | 12 | generational |
| `GC.Gen.MinorHeap` | 83 | 2 | 2 | generational |
| `GC.Gen.CombinedGraph` | 100 | 1 | 1 | generational |
| `GC.Impl.Heap` | 25 | 1 | 4 | mark-and-sweep |

## Full inventory

Every one of the 6 unreachable definitions, grouped by module.

<details>
<summary><code>GC.Gen.MinorCollectForwarding.Reflection</code> — 2/16 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `mem_graph_vertex_at` | let | `GC.Gen.MinorCollectForwarding.Reflection.fst:44:0` |
| `remembered_targets_in_roots` | let | `GC.Gen.MinorCollectForwarding.Reflection.fst:40:0` |

</details>

<details>
<summary><code>GC.Gen.MinorHeap</code> — 2/83 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `minor_heap_size_bound` | let | `GC.Gen.MinorHeap.fsti:180:0` |
| `minor_pow2_bound` | let | `GC.Gen.MinorHeap.fst:276:0` |

</details>

<details>
<summary><code>GC.Gen.CombinedGraph</code> — 1/100 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `cv_eqtype` | let | `GC.Gen.CombinedGraph.fst:27:0` |

</details>

<details>
<summary><code>GC.Impl.Heap</code> — 1/25 dead</summary>

| Definition | Kind | Location |
| --- | --- | --- |
| `platform_fits_u64` | val | `GC.Impl.Heap.fst:40:7` |

</details>

