# Where the weight is

A measured answer to "92,600 lines of F\*/Pulse for 2,600 lines of C — where is
the bloat?".

Every number below is reproducible from the checked-in tooling; the method for
each is given so the analysis can be re-run after future changes.

---

## 1. The census

| tree | files | lines | what it is |
|---|---:|---:|---|
| `common/` | 19 | 7,694 | heap model, headers, graph theory |
| `mark-and-sweep/` | 69 | 35,345 | whole-heap collector + allocator |
| `generational/` | 93 | 43,171 | minor heap, Cheney, promotion — the shipped GC |
| `spot/` | 28 | 6,389 | concrete-scenario tests |
| **total** | **209** | **92,599** | |
| `generational/snapshot/` | | **2,613** | extracted C, 55 functions |

Nominal ratio: **35 : 1**.

That headline ratio is the wrong number to optimise, for two reasons developed
below: about a quarter of the repository is not code at all, and the parts that
*are* code are very unevenly distributed.

---

## 2. What the ratio is actually made of

Of the 92,599 lines:

| category | lines | share |
|---|---:|---:|
| blank | 6,699 | 7.2% |
| `///` doc comments | 7,624 | 8.2% |
| `//` inline comments | 10,917 | 11.8% |
| `(*  *)` block comments | 96 | 0.1% |
| **non-code subtotal** | **25,336** | **27.4%** |
| everything else | 67,263 | 72.6% |

Of the 10,917 `//` lines, only **76** are commented-out code. The comment
budget is genuine explanation, not rot, and it is not a trim target.

So the real figure is **≈67,000 lines of code and proof**, a 26 : 1 ratio. For
SMT-based verification of a garbage collector that is unremarkable.

Other markers, for orientation: 4,918 `assert` lines in `.fst` files (5.3%),
147 `assert_norm`, 0 `calc`, 4 `admit` and 6 `assume` (all in tooling/test
scaffolding, none on the correctness path).

---

## 3. The distribution is very skewed — and that is where the bloat lives

2,819 top-level definitions in `.fst` files (including Pulse `fn`):

- mean **25.7** lines
- median **16** lines
- 83 definitions of **≥ 100 lines** carry **13,130 lines — 14% of the whole repo**
- 16 definitions of ≥ 200 lines carry 4,273 lines

The median proof is short and healthy. The weight is concentrated in fewer
than a hundred monster proofs, and those same proofs are the ones carrying the
highest rlimits.

Largest single definitions:

| lines | definition | file |
|---:|---|---|
| 360 | `alloc_search_preserves_fl_valid_part1` | `GC.Spec.Allocator.Lemmas.Part2.fst:946` |
| 339 | `alloc_search_preserves_fl_chain_terminates_part1` | `GC.Spec.Allocator.Lemmas.Part2.fst:1322` |
| 335 | `alloc_search_preserves_bfc` | `GC.Gen.PromoteUpdate.BlueAlloc.fst:149` |
| 328 | `alloc_search_preserves_chain_avoids_other` | `GC.Spec.Allocator.Lemmas.Part2.fst:2203` |
| 305 | `coalesce_aux_blue_field0_valid` | `GC.Spec.Coalesce.fst:2221` |
| 294 | `alloc_search_obj_not_in_chain_part1` | `GC.Spec.Allocator.Lemmas.Part2.fst:1684` |
| 263 | `combined_proof` | `GC.Spec.SweepCoalesce.Induction.fst:719` |
| 246 | `scan_loop` | `GC.Gen.Impl.Cheney.fst:609` |
| 241 | `coalesce_aux_objects_subset` | `GC.Spec.Coalesce.fst:2864` |
| 240 | `coalesce_aux_walk_all_wb` | `GC.Spec.Coalesce.fst:1196` |

Look at the names.

---

## 4. The dominant idiom: one recursion, inducted over N times

The table above is not a list of ten hard theorems. It is **the same three
recursive functions, inducted over again and again, once per invariant**.
`coalesce_aux` is walked four separate times in the top ten alone, each walk
re-deriving the identical case analysis and differing only in the property
carried through it.

Grouping definitions by the recursion they induct over:

| lines | defs | family | module |
|---:|---:|---|---|
| 1,893 | 10 | `alloc_search*` | `GC.Spec.Allocator.Lemmas.Part2` |
| 1,464 | 15 | `coalesce_aux*` | `GC.Spec.Coalesce` |
| 1,313 | 24 | `push_children*` | `GC.Spec.Mark` |
| 1,065 | 52 | `cheney_forward*` | `GC.Gen.Cheney` |
| 953 | 17 | `cheney_forward*` | `GC.Gen.CheneyPreservation.Injectivity` |
| 939 | 19 | `cheney_forward*` | `GC.Gen.CheneyPreservation.Forwarding` |
| 761 | 13 | `cheney_forward*` | `GC.Gen.CheneyPreservation.Fields` |
| 665 | 16 | `sweep_aux*` | `GC.Spec.Sweep` |
| 646 | 16 | `mark_step*` | `GC.Spec.MarkBoundedCorrectness` |
| 606 | 3 | `alloc_search*` | `GC.Gen.PromoteUpdate.BlueAlloc` |
| 578 | 18 | `cheney_forward*` | `GC.Gen.CheneyPreservation.Frame` |
| 506 | 10 | `alloc_search*` | `GC.Gen.AllocProps` |
| 468 | 9 | `promote_object*` | `GC.Gen.Promote` |
| 466 | 13 | `cheney_forward*` | `GC.Gen.CheneyPreservation` |
| **12,323** | **235** | | **13% of the repository** |

`cheney_forward` alone is inducted over 132 times across six modules, for
4,762 lines. `alloc_search` costs 3,005 lines across three.

This is confirmed independently by textual duplicate detection: normalising
whitespace and stripping comments, **11,983 lines (13%) sit inside a ≥10-line
block that occurs more than once**. The two measurements agree almost exactly,
which is what one would expect if repeated induction is the cause.

### The fix

For each recursive function, prove **one** induction principle and derive the
rest as corollaries. Two standard shapes, both available today:

- a single lemma with a conjunctive postcondition, from which each individual
  property follows by projection; or
- an induction principle parameterised by the invariant — `inv` as a function
  argument, with the step case supplied by the caller — so the case analysis
  over the recursion is written exactly once.

The second is preferable where the invariants have genuinely different shapes.
Either way the per-property cost drops from ~250 lines to ~10.

**Estimated saving: 8,000–10,000 lines**, concentrated in six modules. This is
the single largest lever in the repository, and unlike the others it also
improves the proofs: each of these families currently has to be re-verified in
full whenever the underlying recursion changes.

### Worked example: `GC.Spec.Sweep`

Two of the `sweep_aux*` families have been merged, as a demonstration that the
estimate is real and that the merges go through without a fight.

`sweep_aux_black_survives`, `sweep_aux_white_in_objs_becomes_blue` and
`sweep_aux_blue_stays_blue` were three inductions with a
character-for-character identical skeleton — same preamble, same case split,
same recursion — differing only in the colour of `x` in the precondition, the
one step lemma used in the head case, and the colour in the conclusion. They
are now a single induction, `sweep_aux_member_color`, carrying all three
implications at once:

```fstar
(ensures (let gf = fst (sweep_aux g objs fp) in
          (is_black x g ==> is_white x gf) /\
          (is_white x g ==> is_blue  x gf) /\
          (is_blue  x g ==> is_blue  x gf)))
```

The conjunction is provable by one induction because the head case never
recurses: `is_vertex_set` puts `x` outside the tail, so the colour it acquires
is frozen by `sweep_aux_non_member_color`. In the non-head case the colour of
`x` is untouched, so the induction hypothesis applies unchanged. The three
original statements survive as three one-line corollaries.

Similarly `sweep_aux_preserves_{wosize,tag}_{nonmember,member}` were four
inductions over the same walk. Off the sweep list the *whole header word* is
untouched, which is a single stronger statement from which both fields follow;
on the list a black object has only its colour bits rewritten, so one induction
with a two-conjunct postcondition covers both. Four inductions became two, and
the four original statements became four corollaries.

Result: `GC.Spec.Sweep.fst` 1,325 → 1,187 lines (−10%), seven inductions over
`sweep_aux` reduced to four, no change to the interface, no change to any
caller, and the module verifies in 25 s. The remaining `sweep_aux*` lemmas
(`preserves_field_*`, `preserves_objects`, `preserves_wf`) are genuinely
different arguments and were left alone.

### Two more worked examples, and the criterion that decides them

`GC.Gen.CheneyPreservation.Injectivity.fst` (1,412 → 1,142, −270) had three
invariants each pushed separately through all four Cheney operations —
`forward_fields`, `forward_roots`, `scan`, `promote` — for **twelve**
near-identical inductions. They are now four, one per operation, each carrying
the conjunction. The shared `requires`/`ensures` blocks were factored into two
`unfold let ... : prop` abbreviations; `unfold` matters, because it keeps them
definitionally transparent so Z3 sees straight through them and the merged
proofs need no extra hints. Verified first try in 29.5 s.

`GC.Gen.AllocProps.fst` (1,239 → 1,086, −153) had three lower-bound /
upper-bound *pairs* — the same proof written twice, once for `>= wz` and once
for `<= wz + 1`. Two lessons:

* `write_prev_preserves_wosize{,_upper}` were byte-identical apart from those
  two lines. Both were really proving that the write lands on a word other than
  `obj`'s header, so the merged lemma states the **equality**
  `wosize_of_object obj g2 == wosize_of_object obj g_after_alloc` and drops the
  `wz` parameter entirely. When two lemmas bound the same quantity from both
  sides, look for the equality hiding underneath them.
* `alloc_from_block_wosize{,_upper}_lemma` and
  `alloc_search_obj_wosize{,_upper}_part1` genuinely need both bounds (the value
  is `bwz` on an exact fit and `wz` on a split), so those merged into a single
  two-conjunct postcondition, with the public `alloc_spec_*` wrappers retained
  verbatim to project whichever bound each caller wants.

**The criterion.** Textual similarity picks the candidates, but what decides
whether a merge is cheap is *whether the family members take the same
parameters*:

| situation | verdict |
|---|---|
| identical parameters, invariant differs | merge — mechanical, one conjunctive postcondition |
| identical parameters, bounds differ | merge — and check for an underlying equality first |
| **different extra parameters** | **do not merge** — needs a `forall` inside the induction |

Two families were rejected on the third row despite high similarity:
`push_children_preserves_{is_no_scan,objects,resolve}` and
`push_children_preserves_{wosize,get_field}` in `GC.Spec.Mark.fst` (0.83–0.88,
but the members take `b`, nothing, `addr`, and `x`/`j` respectively), and
`frame_field` / `frame_header` in `CheneyPreservation.Frame.fst` (0.76–0.83,
`frame_field` carries an extra `idx`). Introducing a bounded `forall` into a
50–250-line induction destabilises the SMT for a few hundred lines of saving;
that is a bad trade.

**Running total across the three merged modules: −561 lines**, no interface
change, no caller change, and every module verified on the first attempt.

---

## 5. Restated signatures — 7,645 lines

93 modules have both an `.fsti` and an `.fst`. Across them, 9,429 lines sit
inside `val` blocks in the interface — and **7,645 of those lines (81%) are
written out a second time as a type annotation on the corresponding `let` in
the `.fst`.**

For comparison, F\*'s own `ulib` restates the type in only **32%** of cases
(592 of 1,849 definitions with a `val`). This repository is well above the
convention of the language it is written in.

Worst offenders (lines of `.fst` annotation duplicating the `.fsti`):

| lines | module |
|---:|---|
| 312 | `GC.Spec.Mark` |
| 280 | `GC.Spec.Allocator.Lemmas.Chain` |
| 279 | `GC.Gen.Cheney` |
| 268 | `GC.Impl.Sweep.Lemmas` |
| 263 | `GC.Gen.MinorCollectForwarding.Edges` |
| 258 | `GC.Gen.Promote` |
| 255 | `GC.Spec.Object` |
| 236 | `GC.Gen.CheneyPreservation.Forwarding` |

Stripping a token-identical annotation is semantically inert — F\* checks the
definition against the interface type either way — and it is machine-checked:
if the build passes, the change is correct by construction.

**This is deliberately left undone.** For a `Lemma`, the statement sitting
immediately above its proof is the proof's primary documentation, and deleting
it makes the `.fst` unreadable on its own. The 7,645 lines are real
redundancy, but they are not obviously waste. Recommendation: leave as is, or
strip only where the annotation exceeds ~20 lines and the `.fsti` is the
natural place to read the statement. Flagged here so the number is known
rather than rediscovered.

A smaller, unambiguously wasteful cousin: **767 lines** of `val` blocks
restated *verbatim in a second `.fsti`*, where a facade re-exports a
sub-module's statement — `GC.Spec.Allocator.Lemmas.fsti` (252),
`GC.Gen.MinorCollectForwarding.fsti` (214), `GC.Gen.PromoteUpdate.fsti` (125).
These can be replaced by `include`.

---

## 6. What the shipped C actually needs

Priced with `make depgraph` by varying the root set (see
`.github/copilot-instructions.md` for the recipe):

| root set | lines | definitions |
|---|---:|---:|
| shipped generational GC only | 83,212 | 2,442 |
| \+ the five correctness theorems | 84,424 | 2,607 |
| \+ standalone mark-and-sweep collector | 86,315 | 2,742 |
| \+ SPOT concrete-scenario tests | 92,599 | 3,100 |

Three conclusions:

1. **The correctness theorems are nearly free: 1,212 lines, 1.3%.** The proofs
   of `GC.Spec.Correctness`, `GC.Spec.MarkBoundedCorrectness`,
   `GC.Gen.CheneyCorrectness`, `GC.Impl.MarkBoundedRootLemmas` and
   `GC.Spec.FreeList.Sweep` are not the weight. The weight is the *implementation's
   own* proof obligations — well-formedness preservation, framing, address
   arithmetic — which have to be discharged whether or not anyone states a
   top-level theorem.

2. **SPOT is 6,389 lines and shares no definition with the shipped C.** It is a
   test suite of concrete traces. It should be counted separately from "proof
   size", not deleted.

3. **The standalone mark-and-sweep collector costs 1,891 lines and 135
   definitions**, and nothing in the shipped generational C uses it. Dropping
   it as an extraction root would delete three modules outright —
   `GC.Impl.Mark` (806), `GC.Impl.Sweep` (740), `GC.Impl.Closure` (345) — plus
   30 definitions in `GC.Impl.Sweep.Lemmas`, 21 in `GC.Spec.SweepInv` and 8 in
   `GC.Spec.MarkInv`. **This is a product decision, not a cleanup**: it is a
   second, independently extractable collector with its own `Makefile`. Only
   `generational/snapshot/` is committed as a deliverable. If the standalone
   collector is not shipped, this is 1,891 lines of free weight.

---

## 7. Proof health: rlimits were 4× over-provisioned

Before this analysis the 1,175 in-source `z3rlimit` annotations had median 50,
p90 300 and max 5,000; 253 sites were ≥ 200 and 111 were ≥ 400.

Those numbers accumulated during the Z3 4.15.3 upgrade, when a class of trivial
goals would send the solver down a runaway search and the reflex was to raise
the limit. That failure mode is now handled properly — by the hard per-query
`smt.timeout`, the per-module `EAGER_QI` opt-in list, and `--retry`.

Experiment: quartering all 38 rlimit sites in `GC.Spec.Coalesce.fst` (which
ranged up to 600) still verifies the module, in the same wall time — 113 s
versus 120 s, i.e. noise. An rlimit is a *cap*, not a cost: a query that
succeeds quickly never charges it. An over-provisioned limit therefore buys
nothing and actively hides regressions.

Every site has since been divided by four (floor 10) wherever the proofs still
go through -- 11 modules needed to stay at half, and were left there -- taking
the distribution to median 20 / p90 75 / max 1,250, with only 30 sites above
200 and 12 above 400 (down from 253 and 111). The full build, SPOT and
extraction all still pass. This saves no lines, but it restores the signal: a
proof that suddenly needs four times the resources will now fail rather than
pass silently.

---

## 8. Things that turned out *not* to be bloat

Recorded so they are not re-investigated.

- **Commented-out code**: 76 lines in the whole repository.
- **Dead code**: 3 definitions, all `squash` facts that must be retained (see
  `docs/dead-code-inventory.md`). The 616 genuinely unreachable definitions
  were removed in commits `4efe355` and `79bdaaf`.
- **Facade modules**: exactly one survives (`GC.Spec.Allocator.Lemmas`, 31
  re-exports).
- **`_partN` proof splitting**: 38 families, of which 33 have only a `_part1`.
  The suffix is vestigial naming on 33 definitions, not a split-for-Z3
  artifact. Only `well_formed_heap` (4 parts) and
  `update_major_pointers_preserves_wfh` (3) are genuine conjunct splits, and
  both are load-bearing.
- **The comment budget**: 27% of the repository, and it is real explanation.

---

## 9. Ranked plan

| # | lever | lines | risk | notes |
|---:|---|---:|---|---|
| 1 | Factor the repeated inductions (§4) | 4,000–6,000 | medium | Real proof engineering. −561 done so far across `GC.Spec.Sweep`, `…Injectivity` and `GC.Gen.AllocProps` (§4). Estimate revised down from 8,000–10,000: screening the whole repo at ≥0.82 similarity found only ~20 mergeable pairs, and roughly half fail the same-parameters test. Next best: `coalesce_aux*` (three 240-line inductions at 0.84–0.92) and `GC.Spec.Allocator.Lemmas.Part2`'s `wfh_part1`/`wfh_part4` (0.94). |
| 2 | Drop the standalone mark-and-sweep collector (§6) | 1,891 | none, once decided | Pure product decision. Deletes three modules outright. |
| 3 | Replace facade `.fsti` restatement with `include` (§5) | 767 | low | Three modules. |
| 4 | Strip token-identical `.fst` annotations (§5) | 7,645 | low, mechanical | **Not recommended** — costs readability where it matters most. Listed for completeness. |
| 5 | Account for SPOT separately (§6) | 6,389 | none | Reporting change, not a deletion. |

Doing 1–3 takes the development from 92,599 to roughly **84,000 lines**, of
which ~6,400 is the SPOT test suite and ~22,000 is comments and blank lines —
about **56,000 lines of actual code and proof** for the shipped collector, a
21 : 1 ratio against the extracted C. The honest conclusion after acting on
lever 1 is that this development is not padded with copy-paste to the degree
the raw similarity numbers suggest: most of the near-duplicate *text* is
near-duplicate because the lemmas genuinely quantify over different things, and
only the same-parameter families collapse for free.

---

## 10. Reproducing these numbers

The definition-level and reachability figures come from the checked-in
dependency analyser:

```sh
make depgraph            # whole-development reachability
make depgraph-inventory  # regenerates docs/dead-code-inventory.md
```

Root sets are priced by overriding `DEPGRAPH_ROOTS` on the command line; the
groups (`DEPGRAPH_IFACE_ROOTS`, `DEPGRAPH_THEOREM_ROOTS`, `DEPGRAPH_SPOT_ROOTS`)
are defined in the top-level `Makefile`. The build prerequisites for the
analyser — matching cache version and OCaml ABI — are documented in
`.github/copilot-instructions.md`.

The line-composition, duplication, definition-size and signature-restatement
figures are direct textual measurements over `common/`, `mark-and-sweep/`,
`generational/` and `spot/`.
