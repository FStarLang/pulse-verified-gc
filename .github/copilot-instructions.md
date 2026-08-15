# Copilot Instructions

## Overview

Verified OCaml garbage collector formalized in **F\*** and **Pulse** (concurrent separation logic for F\*). Four directories share common infrastructure:

- **common/** — Foundations used by everything else. `spec/` holds the pure heap model
  (`GC.Spec.Base`, `GC.Spec.Heap`, `GC.Spec.Object`, `GC.Spec.Fields`, `GC.Spec.Graph`,
  `GC.Spec.DFS`, `GC.Spec.HeapGraph`, `GC.Spec.HeapModel`, `GC.Spec.ZeroAddr`);
  `lib/` holds bit-level header/address helpers (`GC.Lib.Header`, `GC.Lib.Address`);
  `impl/` holds the shared Pulse implementations (`GC.Impl.Heap`, `GC.Impl.Object`,
  `GC.Impl.Stack`, `GC.Impl.ArrayWord`). `.fsti` interfaces exist for Base, Heap, Object,
  ZeroAddr, Stack, ArrayWord.
- **mark-and-sweep/** — Sequential stop-the-world GC. `spec/` = `GC.Spec.Mark*`,
  `GC.Spec.Sweep*`, `GC.Spec.Coalesce`, `GC.Spec.SweepCoalesce.*`, the free-list
  `GC.Spec.Allocator*` family, and `GC.Spec.Correctness`. `impl/` = the Pulse
  implementation (`GC.Impl`, `GC.Impl.Mark`, `GC.Impl.Sweep`, `GC.Impl.Allocator`,
  `GC.Impl.Coalesce`, `GC.Impl.FusedSweepCoalesce`, `GC.Impl.Fields`, `GC.Impl.Closure`).
  Also has `ocaml-integration/` and a checked-in C `snapshot/`.
- **generational/** — Minor/major generational GC with Cheney copying collection.
  `spec/` = `GC.Gen.Base`, `GC.Gen.MinorHeap`, `GC.Gen.Cheney*`,
  `GC.Gen.CheneyPreservation.*`, `GC.Gen.Promote*`, `GC.Gen.MinorCollectForwarding.*`,
  `GC.Gen.Reachability*`, `GC.Gen.TwoPassEquiv*`, `GC.Gen.HeapInvariant`.
  `impl/` = `GC.Gen.Impl`, `GC.Gen.Impl.MinorHeap`, `GC.Gen.Impl.Cheney`,
  `GC.Gen.Impl.Promote`, `GC.Gen.Impl.UpdatePtrs`. Also `ocaml-integration/` + `snapshot/`.
- **spot/** — Small concrete "spot check" scenarios (`GC.SPOT.*`) that instantiate the
  specs on tiny fixed heaps to sanity-check pre/post-conditions. Flat layout, one `.fsti`
  per `.fst`. See `spot/SPOT_STATUS.md`.

All of `mark-and-sweep/`, `generational/` and `spot/` depend on `common/`; none of them
depend on each other.


## Build & Verification

### Toolchain

F\* and KaRaMeL live in `./fstar/` and are installed by `./setup.sh` (which pins a
specific nightly — see `VERSION` in that script). Z3 **4.15.3** ships with that
installation; every build passes `--z3version 4.15.3` explicitly.

```bash
./setup.sh          # download + unpack the pinned F* nightly and krml into ./fstar
```

### Top-level build

The root `Makefile` drives one unified `fstar.exe --dep full` scan across *all*
sources (common + mark-and-sweep + generational + spot), so the whole repo can be
verified incrementally and in parallel:

```bash
make -j24                # verify everything (default target)
make common -j24         # common/ only
make mark-and-sweep -j24 # common/ + mark-and-sweep/
make generational -j24   # common/ + mark-and-sweep/ + generational/ + spot/
make extract             # verify + extract both GCs to C via KaRaMeL
make clean
```

`make -k` is useful while fixing regressions: it keeps going after a failure so
one run enumerates every broken module.

Each subdirectory also keeps a standalone Makefile (`common/`, `mark-and-sweep/`,
`generational/`, `spot/`) with the same flags, for working on one GC in isolation.

### Checked-file cache

F\* writes `M.fst.checked` into `--cache_dir`, which defaults to the **current
working directory** — it no longer drops the file next to the source. Every
Makefile therefore points at one shared `_cache/` directory (`CACHE_DIR`). Stale
`.checked` files left elsewhere in the tree will poison `--dep full`; if
dependency scanning behaves oddly, `make clean` (or `rm -rf _cache`) and rebuild.

### Verifying a single module

```bash
./fstar/bin/fstar.exe --z3version 4.15.3 --retry 3 \
  --cache_checked_modules --cache_dir _cache --odir _output \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  generational/spec/GC.Gen.Cheney.fst
```

Verify a `.fsti` before its `.fst`, and never pass both to one invocation.

### Diagnostics
```bash
# Count admits/assumes
grep -c "admit()" mark-and-sweep/spec/GC.Spec.Correctness.fst
grep -rc "assume " common/spec/GC.Spec.Object.fst

# Find high rlimits
grep -rn "z3rlimit" --include="*.fst" --include="*.fsti" common mark-and-sweep generational spot

# SMT query performance analysis: append --query_stats to the single-module command
# above, then grep the output for "Query stats"

# Syntax-only check (skip SMT): append --admit_smt_queries true
```

## Architecture

### Module Dependency Chain
```
GC.Lib.Header             (bitvector operations on 64-bit object headers)
  ↓
GC.Lib.Address            (field/header separation lemmas)
  ↓
GC.Spec.Base              (core types: mword, heap, hp_addr, obj_addr, heap_words,
                           mk_hp_addr, aligned_plus_mul8)
  ↓
GC.Spec.Heap              (read_word, write_word on byte-addressable heap)
  ↓
GC.Spec.Object            (header fields, color predicates, color mutations)
  ↓
GC.Spec.Fields            (object enumeration, field traversal, objects_separated)
  ↓
GC.Spec.Graph             (vertex/edge types, reachability, DFS forest)
  ↓
GC.Spec.DFS               (DFS algorithm with termination proofs)
  ↓
GC.Spec.HeapGraph         (bridge: heap objects → graph edges)
  ↓
GC.Spec.HeapModel         (graph construction from heap, create_graph)
  ↓
  ├── mark-and-sweep/spec/ → mark-and-sweep/impl/
  ├── generational/spec/   → generational/impl/
  └── spot/
```

### Spec vs Impl Split
- **Spec modules** (`GC.Spec.*`, `GC.Gen.*` under `spec/`) — Pure F\* specifications and
  lemmas. Plain F\*; no Pulse needed.
- **Impl modules** (`GC.Impl.*`, `GC.Gen.Impl.*` under `impl/`) — Pulse implementations
  with separation logic. Use `#lang-pulse`. `fstar.exe` handles `#lang-pulse` natively.

Every impl function's postcondition should reference the corresponding spec function, and
that connection must be exposed in the `.fsti`.

### Header Layout (OCaml-compatible, 64-bit)
```
| wosize (54 bits) | color (2 bits) | tag (8 bits) |
  bits 10-63          bits 8-9         bits 0-7
```

Colors (`color_sem` in `GC.Lib.Header`): `White = 0`, `Gray = 1`, `Blue = 2`,
`Black = 3`. `Blue` marks free-list blocks, which is why the allocator and the collector
share the same colour field.

Important tags: `closure_tag = 247`, `infix_tag = 249`, `no_scan_tag = 251`
(`GC.Spec.Object`). Objects with `tag >= no_scan_tag` have no pointer fields and are
skipped during marking and during Cheney scanning.

### Mark-and-Sweep phases
1. Mark — DFS/BFS from roots, `White → Gray → Black` (`GC.Spec.Mark`,
   `GC.Spec.MarkBounded` for the fuel-bounded variant used by the implementation).
2. Sweep — reclaim `White` objects onto the free list, reset `Black → White`
   (`GC.Spec.Sweep`).
3. Coalesce — merge adjacent free (`Blue`) blocks (`GC.Spec.Coalesce`); the
   implementation fuses sweep and coalesce in one pass (`GC.Spec.SweepCoalesce`,
   `GC.Impl.FusedSweepCoalesce`).
4. Allocate — first-fit search of the free list with block splitting
   (`GC.Spec.Allocator` + the `GC.Spec.Allocator.Lemmas.*` family).

### Generational phases
1. Minor collection — Cheney copying from the minor heap (`GC.Gen.Cheney`,
   `GC.Gen.CheneyBFS`), forwarding pointers rewritten in place
   (`GC.Gen.MinorCollectForwarding.*`).
2. Promotion — surviving minor objects are allocated in the major heap
   (`GC.Gen.Promote`, `GC.Gen.PromoteUpdate.*`).
3. Remembered set — major→minor edges recorded by the write barrier
   (`GC.Gen.Remembered`).
4. Major collection — reuses the mark-and-sweep major heap machinery.

`GC.Gen.TwoPassEquiv` proves the single-pass implementation equals the two-pass
(copy then patch) specification; `GC.Gen.CheneyCorrectness` and
`GC.Gen.CheneyPreservation.*` carry the preservation invariants.

### End-to-End Correctness (mark-and-sweep/)
`GC.Spec.Correctness` proves five pillars: well-formedness preservation,
reachability-based survival, successor preservation, color reset, and field data
preservation.

## Key Conventions

### Naming
- `snake_case` for predicates and lemmas: `is_black`, `color_of_object`, `color_preserves_wosize`
- `CamelCase` for type constructors: `White`, `Gray`, `Black`
- `camelCase` for header operations: `getColor`, `getTag`, `getWosize`, `colorHeader`

### Address Types
- `hp_addr` — Word-aligned address within heap bounds
- `obj_addr` (alias `val_addr`) — `hp_addr` with `>= 8` (room for header before it)
- `hd_address` computes header address from object address (subtract `mword`)

### Interface Files
`GC.Spec.Base.fsti`, `GC.Spec.Heap.fsti`, `GC.Spec.Object.fsti` and
`GC.Spec.ZeroAddr.fsti` in `common/spec/` expose the public API. `GC.Spec.Fields.fst`,
`GC.Spec.Graph.fst`, `GC.Spec.DFS.fst`, `GC.Spec.HeapGraph.fst` and
`GC.Spec.HeapModel.fst` have no separate `.fsti`.

**Interface scoping is strict in the current F\* nightly.** An `.fsti`'s `open`
declarations and `#set-options` no longer scope over the corresponding `.fst`, so both
files must carry their own headers. Declaration order in an `.fsti` must also match the
dependency order of the definitions (otherwise: error 233). Always verify the `.fsti`
first, then the `.fst` — never both in one `fstar.exe` invocation.

### Extraction Annotations
- `inline_for_extraction` — inline the definition into its C callers
- `noextract` — keep out of the extracted code entirely
- Ghost/`erased` values and `Lemma`s are erased automatically

Extraction goes through KaRaMeL (`fstar/bin/krml`): `make extract` at the top level,
plus `make -C generational snapshot` / `make -C mark-and-sweep snapshot` to refresh the
checked-in C.

### SMT Tuning
Flags are set centrally in the Makefiles, not per file:
- Baseline: `--z3version 4.15.3 --retry 3 --warn_error -321-233-331` plus the
  shared `--include` list and `--cache_dir _cache`.
- Modules listed in `EAGER_QI_CHECKED` (root Makefile ~line 216, `generational/Makefile`
  ~line 120) additionally get `--z3smtopt '(set-option :smt.qi.eager_threshold 100)'`.
- The `GC.Spec.Allocator*` family also gets `--z3rlimit 100`.

Individual modules still carry their own `#set-options` / `#push-options` for local
fuel and rlimit tuning. Because interfaces no longer scope over implementations, an
`.fst` needs its own `#set-options` even when the `.fsti` already has one.

For stubborn proofs: add intermediate `assert` statements to guide the solver, factor the goal into a top-level helper lemma proved in an empty context, or increase `--z3rlimit`. `--split_queries` no longer exists in F\*; see "Z3 4.15.3 and `--retry`" below.

### Z3 4.15.3 and `--retry`
The project pins Z3 **4.15.3** (`--z3version 4.15.3`, bundled under `fstar/lib/fstar/z3-4.15.3/`). Under this version a number of otherwise trivial leaf goals — nat-ness side conditions (`fuel - 1 >= 0`), alignment facts (`x % 8 == 0`), `U64.uint_to_t` bounds — intermittently send the solver down a search path that exhausts the rlimit, even though a neighbouring identical goal is discharged in milliseconds.

Worse, some of these searches never terminate *and never charge the rlimit*, so
`--z3rlimit` cannot bound them: the module simply hangs. Four mitigations are in place,
the first three already wired into every Makefile:

- **`Z3_TIMEOUT` — a hard per-query Z3 wall-clock cap** (`--z3smtopt '(set-option :timeout 300000)'`). This is the single most important flag of the upgrade: it converts an unbounded hang into a normal, *localized* "SMT query timed out" error naming the offending source range. Without it a bad goal is invisible.

  **When a module hangs, re-run it with a short cap to find the culprit:**
  ```bash
  fstar.exe ... --z3smtopt '(set-option :timeout 60000)' <module>.fst
  ```
  A 60 s cap turned a 60-minute hang in `GC.Spec.Allocator.Lemmas.Part2.fst` into a
  3m43s run that named three precise line numbers. Always diagnose this way before
  guessing at asserts.
- **`--retry 3`** (`RETRY` variable) — re-runs a *failing* query up to 3 times and succeeds on the first one that goes through. Costs nothing on queries that succeed immediately, and clears the majority of these flakes. Note it multiplies the cost of a *genuine* failure by 4, and it is incompatible with `--quake`.
- **`EAGER_QI`** (`--z3smtopt '(set-option :smt.qi.eager_threshold 100)'`) — dramatic on quantifier-heavy modules (`GC.Gen.CheneyPreservation.Forwarding`: >90 min → 3m13s; `GC.Spec.Allocator`: >15 min → 81s) but it makes `GC.Spec.DFS` and `GC.Spec.Heap` diverge, so it **cannot** be global. Modules opt in through the `EAGER_QI_CHECKED` lists in the root and `generational/` Makefiles. **When verifying a module by hand, check whether it is on that list and pass the flag.**

  It also cuts the other way: `EAGER_QI` can be what makes a module hang. `GC.Gen.CheneyPreservation.Fields` went from a 28-minute hang to 19 s and `GC.Gen.Impl.MinorHeap` from a hard failure to verified, purely by *removing* them from the list. **If a listed module hangs, try it without the flag before touching the source.**
- **Empty-context helper lemmas** — when `--retry` isn't enough, lift the trivial fact out of the big context into a top-level `Lemma` (ideally under `--fuel 0 --ifuel 0`) and call it explicitly. `GC.Spec.Base` provides the most common ones:
  - `heap_words` — abbreviation for `heap_size / U64.v mword` (avoids re-deriving nat-ness at every use)
  - `mk_hp_addr a` — `U64.uint_to_t a` at type `hp_addr`, with `r == U64.uint_to_t a` in the postcondition
  - `aligned_plus_mul8 base k` — `(base + k * 8) % 8 == 0` from `base % 8 == 0`

  Goal shapes that reliably blow up, and their fixes:
  1. `n - 1 >= 0` / `n - 1 << n` at a recursive call → a helper carrying the facts in its *result type*, e.g. `dec_fuel (fuel: nat{fuel >= 1}) : (r: nat{r == fuel - 1 /\ r << fuel})` (`GC.Gen.Cheney`), or `dec_field_idx` (`GC.Gen.CheneyPreservation.Fields`) for an `if i < n then n - i else 0` measure.
  2. `UInt.size a 64` for `U64.uint_to_t a` → `GC.Spec.Base.mk_hp_addr`, or a module-local `Pure` wrapper such as `mk_u64_lt_heap`.
  3. `(base + k * 8) % 8 == 0` → `GC.Spec.Base.aligned_plus_mul8`; an `SMTPat`-carrying module-local wrapper works well when the coercion appears many times (`aligned_step`/`aligned_step8` in `GC.Gen.Cheney.Dense`). Note `(x + 8)` does *not* match a pattern written `(base + k * 8)`, so both variants are needed.
  4. Two distinct aligned addresses being at least a word apart → an `aligned_distinct`/`aligned_apart` helper, needed before nearly every `read_write_different`.
  5. A large local `aux` closure inside a big theorem → **hoist it to a top-level lemma over abstract parameters** (`two_pass_pointwise` in `GC.Gen.TwoPassEquiv`, `fwd_state_extend_infix` in `GC.Gen.CheneyPreservation.Fields`). The win comes from replacing huge terms with opaque variables.
  6. Composing two frame conditions → one helper doing both steps (`frame_excl_compose`); splitting it in two never sufficed.
  7. Assembling a multi-conjunct predicate → an `_intro` helper with the conjuncts as `requires`.
  8. **A branchy lemma whose every branch is individually fine but whose final postcondition times out** → end *each* branch with `assert (<the exact goal>)`. The final assembly then becomes pure propositional reasoning instead of congruence over a giant nested formula. This fixed `cheney_forward_one_preserves_fwd_target_not_no_scan_state`.
  9. **A boolean guard that will not bridge back to arithmetic.** Inside these contexts Z3 4.15.3 can burn an entire rlimit failing to derive `fuel >= 1` from the branch hypothesis `~(fuel = 0)`, or `ridx < Seq.length roots` from `~(ridx >= Seq.length roots)`. Two fixes, in order of preference:
     - Branch on a helper whose **result type carries both branch facts**, so neither branch needs arithmetic at all:
       ```fstar
       private let fuel_is_zero (fuel: nat)
         : (r: bool{(r ==> fuel == 0) /\
                    (not r ==> fuel >= 1 /\ (fuel - 1) >= 0 /\ (fuel - 1) << fuel)})
         = fuel = 0
       ```
     - Failing that, make the guard the **first statement of the branch** (`assert (i < wosize);`). Once proved it is a hypothesis for every later query in that branch — but it only works while the context is still small, so it must come before the branch's lemma calls.

  Two further tricks that reliably help: replace equality/disequality guards on `nat` (`x = 0`) with inequalities (`x < 1`), and split a lemma with a large conjunctive postcondition into one lemma per conjunct.

  **Adding `assert`s often makes things dramatically worse.** In `Part2.fst` three added asserts took a 5m57s run past 47 minutes. Prefer *removing* local reasoning and replacing it with a single helper call.

Things that were measured and did **not** help: `--ext context_pruning`, `smt.mbqi false`, `smt.arith.nl false`, `smt.case_split 3`, `smt.arith.solver 2`, and `--z3rlimit_factor`.

### Cross-Directory Dependencies
`mark-and-sweep/`, `generational/` and `spot/` all import from `common/`, and the whole
repository shares a single `_cache/` of `.checked` files. Editing anything in
`common/spec/` — especially `GC.Spec.Base` — therefore invalidates essentially the entire
cache and forces a multi-hour rebuild. Treat `common/spec/GC.Spec.Base.fsti` as frozen
unless a change is genuinely required.

To rebuild everything after such a change:
```bash
make clean && make -k -j24
make -C spot -j24
```

### Proof Gaps (Admits/Assumes)
Track proof completeness with:
```bash
grep -c "admit()" <file>       # Unproven goals (placeholder proofs)
grep -c "assume " <file>       # Unverified assumptions (axioms)
```
When eliminating admits: add intermediate `assert` statements to guide Z3, invoke helper lemmas explicitly, and verify incrementally. The goal for this repository is zero `admit`s and zero `assume`s.

### Key Pulse Primitives (impl modules)
- `slprop` — separation logic propositions; `**` is separating conjunction
- `Pulse.Lib.Reference` / `Pulse.Lib.Box` — stack (`let mut`) and heap references
- `Pulse.Lib.Vec` / `Pulse.Lib.Array` — heap and stack arrays (`arr.(i)`, `arr.(i) <- v`)
- `exists*` for existential slprops; `with x. _;` binds the (ghost) witness
- `Ghost.erased` / ghost functions — verification-only, erased at extraction

Loop invariants are written `while (cond) invariant exists* w. ... { body }`; do **not**
use the older `invariant b. exists* ...` form.

### Termination measures on `while` loops

Every `while` loop in a plain `fn` needs a `decreases` clause; only a `divergent fn`
(which elaborates to `stt_div` rather than `stt`) may omit one.  `divergent` is
contagious — a plain `fn` cannot call a `divergent fn` (Error 228) — so annotations must
be removed bottom-up through the call graph, and the `.fsti` declaration and the `.fst`
definition must be de-annotated together.  **No function outside `spot/` is `divergent`;
keep it that way.**

The clause goes *after* the `invariant`, immediately before the body:

```
while (U64.lte !i wz)
  invariant exists* vi. R.pts_to i vi ** pure (...)
  decreases (Prims.op_Subtraction (U64.v wz + 1) (U64.v !i))
{ ... }
```

Three rules that are easy to get wrong:

1. **The measure cannot mention the `exists*`-bound witnesses of the invariant.**
   Referring to `vi` above gives `Error 72: Identifier not found`.  Instead
   *dereference the mutable reference directly* (`!i`); Pulse elaborates the measure as
   a ghost expression, so `!i`, `R.op_Bang r` and `GR.op_Bang g` are all legal.
2. **Spell subtraction as `Prims.op_Subtraction`.**  `Pulse.Lib.BoundedIntegers` is in
   scope in most impl modules and rebinds `-`/`+` to bounded machine operators, which do
   not typecheck at `int`.  `Prims.op_Addition` likewise.
3. **`if` is allowed in the measure**, which is how loops with a `done`/`go` flag are
   handled: the flag contributes the final "one more iteration" unit.

Idioms used in this repository:

| Loop shape | Measure |
|---|---|
| `while (U64.lte !i wz)` counting up | `Prims.op_Subtraction (U64.v wz + 1) (U64.v !i)` |
| `while (SZ.lt !i n)` counting up | `Prims.op_Subtraction (SZ.v n) (SZ.v !i)` |
| heap walk `while (!current + 8 < heap_size)` | `Prims.op_Subtraction heap_size (U64.v !current)` |
| walk with a `done_` flag | `Prims.op_Addition (Prims.op_Subtraction minor_heap_size (U64.v !pos)) (if !done_ then 0 else 1)` |
| fuel-driven `while (!go)` | `Prims.op_Addition (U64.v !fuel_ref) (if !go then 1 else 0)` |

For a heap walk the loop body must be shown to *strictly* advance the cursor.  Where the
body is a separate `fn` (e.g. `GC.Impl.Sweep.sweep_loop_body`) the strict increase has to
be added to that function's postcondition (`U64.v v1 > U64.v 'v0`).

**Worklist loops with no concrete counter** (the bounded mark loops in
`GC.Impl.MarkBounded`) use a *ghost* measure: allocate a `Pulse.Lib.GhostReference` of
type `nat`, tie it to the spec measure in the invariant
(`GR.pts_to gm m ** pure (m == SpecMarkBounded.count_non_black s)`), update it with
`GR.write gm ...` after each step, `GR.free gm` after the loop, and write
`decreases (Prims.op_Addition (GR.op_Bang gm) (if !go then 1 else 0))`.  The strict
decrease comes from the spec lemmas `mark_step_bounded_decreases_non_black` /
`mark_inner_loop_count_decreases`.  Ghost references are erased at extraction, so the
generated C is unchanged.

To make an outer loop's measure work, an inner draining function must *expose* its
decrease in its postcondition — e.g. `mark_inner_loop_impl` ensures
`Seq.length 'st > 0 ==> count_non_black s2 < count_non_black 's`, proved from a loop
invariant of the form
`(m < count_non_black 's \/ (st_cur == 'st /\ s == 's))` ("either we made progress or
nothing happened yet").

### Proof-only fuel vs. load-bearing fuel

Several loops carry a counter called *fuel*. These are two different things and should
not be conflated:

* **Proof-only fuel** — `GC.Impl.Mark.mark_loop`. The loop guard is `!go` (the gray
  stack is empty); the fuel is never consulted at runtime. It exists only to index the
  fuel-recursive spec `GC.Spec.Mark.mark_aux` and to serve as the `decreases` measure.
  Exhaustion is *proved impossible*: `mark_aux_fuel_pos` derives `fv > 0` whenever the
  stack is non-empty, from an invariant seeded by `mark_no_grey_remains` (a real theorem,
  no admits/assumes, proved by the counting argument
  `total_non_black g <= |objects zero_addr g| <= heap_size / 8 == heap_words`).  The
  postcondition demands `Seq.length st2 == 0`, so exiting via the spec's
  `else if fuel = 0 then g` branch would be unprovable.  `mark_loop` is not reachable
  from the extracted entry points, so KaRaMeL drops it entirely.
* **Ghost measure** — `GC.Impl.MarkBounded.mark_inner_loop_impl` / `.mark_loop_bounded`,
  described above.  Preferred for new code: same guarantee, and it leaves *no* runtime
  residue.  The extracted C is just
  `while (go) { if (is_empty(st)) go = false; else mark_step_bounded_impl(heap, st); }`.
* **Load-bearing fuel** — `GC.Impl.Allocator.allocate` / `.allocate_part1`.  Here the
  counter *is* tested at runtime (`if (vfuel == 0ULL)` appears in `GC_Impl.c`) and
  running out returns OOM.  This is faithful to the spec, because `alloc_spec` is itself
  defined as `alloc_search g fp 0UL fp wz heap_words` — the budget is part of the
  specification.

  **The budget is provably sufficient — this is now machine-checked.**
  `AllocLemmas.alloc_search_fuel_irrelevant` (in `GC.Spec.Allocator.Lemmas.Chain`)
  proves

  ```fstar
  fl_chain_terminates g cur fuel /\ fuel' >= fuel ==>
    alloc_search g head prev cur wz fuel' == alloc_search g head prev cur wz fuel
  ```

  with the corollary `alloc_spec_fuel_irrelevant`: `alloc_spec g fp wz` is unchanged by
  any surplus budget beyond `heap_words`.  Since a spurious OOM would by definition be an
  answer that a larger budget would have improved on, fuel irrelevance *is* the
  no-spurious-OOM statement — the `fuel = 0` branch never fires while a suitable block is
  still reachable.

  The hypothesis `fl_chain_terminates g fp heap_words` ("the free-list chain reaches a
  terminal within `heap_words` steps") is not a new assumption: `GC.Impl.Allocator.
  allocate_part1` already requires it, and `GC.Gen.Impl.Cheney` carries it as a loop
  invariant.  So clients of `allocate_part1` can invoke the corollary directly with no
  interface change.  Plain `allocate` cannot yet: it is guarded by `well_formed_heap`,
  which constrains object layout and pointer closure but says *nothing* about the free
  list, so it would need `fl_chain_terminates` added to its precondition.

  Note where the bound really comes from.  `heap_words` is not a safety margin: an acyclic
  free list has at most one node per distinct 8-aligned heap address, i.e. at most
  `heap_words` of them.  The fuel is that pigeonhole bound inlined as a constant.  The
  proof above takes the *conditional* route (assume chain termination, conclude the budget
  never binds) rather than the unconditional pigeonhole route (derive termination from
  acyclicity via a no-repeat/visited-set argument), because chain termination is the
  invariant the codebase already maintains.

Do **not** "simplify" the allocator's fuel away, and do not assume a counter named
`fuel` is proof-only without checking whether the loop guard reads it.

## Troubleshooting

### "Subtyping check failed"
Missing refinement or lemma call. Invoke helper lemmas before usage (e.g., `hd_address_bounds f` before using `f_address (hd_address f)`).

### "SMT solver could not prove"
1. Add intermediate `assert` statements to narrow the gap
2. Invoke relevant lemmas explicitly
3. If the goal is trivial arithmetic, lift it into a top-level helper lemma (see "Z3 4.15.3 and `--retry`")
4. Try `--z3rlimit` increase to diagnose (then optimize)

### "Module X not found"
Check `--include` paths. Every module needs the full shared include list:
`--include common/spec --include common/lib --include common/impl` plus the includes for
its own directory. The Makefiles build this list once (`INCLUDES`); reuse it rather than
hand-rolling one.

### Cached file issues
The whole repository shares one `_cache/` directory (`--cache_dir _cache`). Run
`make clean`, or `rm -rf _cache` for a full reset. Never run a full `make` and a
single-module `fstar.exe` against `_cache/` at the same time: the single-module run can
see a half-written cache and silently re-verify its entire dependency chain. When
verifying one module by hand, point `--cache_dir` at a scratch copy of `_cache/` and copy
the resulting `.checked` back only on success.
