# minor_collect_full / generational GC proof failure inventory

Date: 2026-05-20  
Repo: `/home/nswamy/workspace/pulse-verified-gc`  
F*: `F* 2026.04.17~dev`, commit `276817c2e333b98b01347d6a6f738710fa497db4`, Z3 `4.13.3`

This was an inspect-only pass over the current dirty working tree. Source files already modified at the start of the pass:

```text
 M generational/Makefile
 M generational/impl/GC.Gen.Impl.UpdatePtrs.fsti
 M generational/impl/GC.Gen.Impl.fst
 M generational/impl/GC.Gen.Impl.fsti
 M generational/spec/GC.Gen.CheneyPreservation.fst
 M generational/spec/GC.Gen.CheneyPreservation.fsti
 M generational/spec/GC.Gen.TwoPassEquiv.fst
?? .atomic/
?? research/
```

## Intended verification commands discovered

### Root `Makefile`

Root verification targets:

- `make` / `make verify` verifies all common + mark-and-sweep + generational modules.
- `make generational` verifies `$(ALL_SRC)`, i.e. common + mark-and-sweep + generational.
- Important generational rules:
  - `generational/spec/GC.Gen.Promote.fst`: `$(FSTAR) --query_stats --split_queries always $<`
  - `generational/spec/GC.Gen.WriteBodyLemmas.fst`: `$(FSTAR) --query_stats --split_queries always $<`
  - `generational/spec/GC.Gen.MinorHeap.fst`: `$(FSTAR) --split_queries always $<`
  - `generational/spec/GC.Gen.AllocProps.fst`: `$(FSTAR) --query_stats $<`
  - `generational/spec/%.checked`: `$(FSTAR) $<`
  - `generational/impl/GC.Gen.Impl.fst`: `$(FSTAR) --z3rlimit 200 --split_queries always --z3refresh $<`
  - `generational/impl/%.checked`: `$(FSTAR) --z3rlimit 160 --split_queries always $<`

Root FSTAR base flags:

```text
--cache_checked_modules --odir _output --warn_error -321 --report_assumes warn
--already_cached 'Prims FStar Pulse PulseCore -GC'
--include common/spec --include common/lib --include common/impl
--include mark-and-sweep/spec --include mark-and-sweep/impl
--include generational/spec --include generational/impl
```

### `generational/Makefile`

Local generational verification target:

- `make -C generational verify` verifies only `generational/spec` + `generational/impl` sources, with common/M&S on the include path.
- Important local rules:
  - `spec/GC.Gen.Promote.fst`: `$(FSTAR) --split_queries always --z3rlimit_factor 3 $<`
  - `spec/%.checked`: `$(FSTAR) $<`
  - `impl/GC.Gen.Impl.fst`: `$(FSTAR) --z3rlimit 160 $<`
  - `impl/%.checked`: `$(FSTAR) --z3rlimit 160 --split_queries always $<`

Notable discrepancy: `generational/Makefile` explicitly says command-line `--split_queries always` conflicts with `derive_fwd_ptrs_classified`, while the root `Makefile` still verifies `generational/impl/GC.Gen.Impl.fst` with command-line `--split_queries always --z3refresh`.

## Commands run and results

### 1. Full root generational target

Command:

```sh
make -j1 generational
```

Result: **exit 2**.

First hard failure is not in the generational slice; root `make generational` tries to verify mark-and-sweep test modules first and fails here:

```text
/home/nswamy/workspace/pulse-verified-gc/fstar/bin/fstar.exe ... mark-and-sweep/spec/GC.Test.Bridge.fst
* Error 19 at mark-and-sweep/spec/GC.Test.Bridge.fst(161,4-161,24):
  - Assertion failed
  - The SMT solver could not prove the query. Use --query_stats for more
    details.
  - See also common/spec/GC.Spec.Heap.fsti(128,18-128,32)

make: *** [Makefile:117: mark-and-sweep/spec/GC.Test.Bridge.fst.checked] Error 1
EXIT_CODE=2
```

Targeted reproduction:

```sh
./fstar/bin/fstar.exe --cache_checked_modules --odir /tmp/pvgc-debug-out-bridge \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  mark-and-sweep/spec/GC.Test.Bridge.fst
```

Result: **exit 1**, same failure at `mark-and-sweep/spec/GC.Test.Bridge.fst:161`.

Relevant source locations:

- `mark-and-sweep/spec/GC.Test.Bridge.fst:161` calls `read_write_different g1 m zero_addr 0UL`.
- `common/spec/GC.Spec.Heap.fsti:128-130` requires address separation:
  `addr1 <> addr2 /\ (addr1 + mword <= addr2 \/ addr2 + mword <= addr1)`.

### 2. Local generational verify

Command:

```sh
timeout 90s make -C generational -j1 verify
```

Result: **exit 124** (timeout). It progressed through dependency generation and several early modules, then hung/was killed while verifying:

```text
... spec/GC.Gen.CheneyPreservation.fst
Thread 174 killed on uncaught exception Sys_error("Bad file descriptor")
make: *** [Makefile:74: spec/GC.Gen.CheneyPreservation.fst.checked] Error 130
EXIT_CODE=124
```

A longer earlier run with a 300s harness timeout also timed out in `spec/GC.Gen.CheneyPreservation.fst`.

Query-stats probe:

```sh
./fstar/bin/fstar.exe --cache_checked_modules --odir /tmp/pvgc-debug-out-pres-qs \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  --query_stats --split_queries always --z3rlimit 120 \
  generational/spec/GC.Gen.CheneyPreservation.fst
```

Result: **timeout at 120s**. Representative slow obligations before timeout:

```text
(GC.Gen.CheneyPreservation.fst(225,2-264,5))
  Query-stats (GC.Gen.CheneyPreservation.cheney_forward_one_preserves_no_black, 47)
  succeeded in 14548 milliseconds ...

(GC.Gen.CheneyPreservation.fst(374,2-386,5))
  Query-stats (GC.Gen.CheneyPreservation.cheney_scan_preserves_no_black, 25)
  succeeded in 45589 milliseconds ...
```

Current admitted lemma in this file:

- `generational/spec/GC.Gen.CheneyPreservation.fst:2424`: `cheney_promote_nonblue_origin = admit ()`.

### 3. `GC.Gen.TwoPassEquiv.fst`

Command:

```sh
./fstar/bin/fstar.exe --cache_checked_modules --odir /tmp/pvgc-debug-out-twopass \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  generational/spec/GC.Gen.TwoPassEquiv.fst
```

Result: **exit 0**.

```text
Verified module: GC.Gen.TwoPassEquiv
All verification conditions discharged successfully
EXIT_CODE=0
```

However, this success includes an admit:

- `generational/spec/GC.Gen.TwoPassEquiv.fst:1454`: `fwd_ptrs_classified_at = admit ()`.
- Nearby comment: `TODO: add field-membership precondition and prove from fwd_ptrs_classified.`

### 4. `GC.Gen.Impl.fsti` and `GC.Gen.Impl.UpdatePtrs.fsti`

Commands:

```sh
./fstar/bin/fstar.exe --cache_checked_modules --odir /tmp/pvgc-debug-out-impl-fsti \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  --z3rlimit 160 --split_queries always \
  generational/impl/GC.Gen.Impl.fsti

./fstar/bin/fstar.exe --cache_checked_modules --odir /tmp/pvgc-debug-out-upd-fsti \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  --z3rlimit 160 --split_queries always \
  generational/impl/GC.Gen.Impl.UpdatePtrs.fsti
```

Results: both **exit 0**.

```text
Verified i'face (or impl+i'face): GC.Gen.Impl
All verification conditions discharged successfully

Verified i'face (or impl+i'face): GC.Gen.Impl.UpdatePtrs
All verification conditions discharged successfully
```

This means the interface/spec for `minor_collect_full` currently verifies; the implementation proof is the blocker.

### 5. `GC.Gen.Impl.Cheney.fst` and `GC.Gen.Impl.UpdatePtrs.fst`

Commands used root-style impl flags:

```sh
./fstar/bin/fstar.exe --cache_checked_modules --odir /tmp/pvgc-debug-out-impl-cheney \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  --z3rlimit 160 --split_queries always \
  generational/impl/GC.Gen.Impl.Cheney.fst

./fstar/bin/fstar.exe --cache_checked_modules --odir /tmp/pvgc-debug-out-updateptrs \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  --z3rlimit 160 --split_queries always \
  generational/impl/GC.Gen.Impl.UpdatePtrs.fst
```

Results: both **exit 0**.

```text
Verified module: GC.Gen.Impl.Cheney
All verification conditions discharged successfully

Verified module: GC.Gen.Impl.UpdatePtrs
All verification conditions discharged successfully
```

### 6. `GC.Gen.Impl.fst` with root `Makefile` flags

Command:

```sh
./fstar/bin/fstar.exe --cache_checked_modules --odir /tmp/pvgc-debug-out-root-cache \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  --z3rlimit 200 --split_queries always --z3refresh \
  generational/impl/GC.Gen.Impl.fst
```

Result: **exit 1**.

First hard failure:

```text
* Error 276 at generational/impl/GC.Gen.Impl.fst(526,0-571,75):
  - Unexpected output from Z3:
      "ASSERTION VIOLATION
      File: ../src/math/lp/lar_solver.cpp
      Line: 1066
      Failed to verify: m_columns_with_changed_bounds.empty()

      Z3 4.13.3.0
      Please file an issue with this message and more detail about how you encountered it at https://github.com/Z3Prover/z3/issues/new"

Unexpected error: Failure("Parse error: </labels> not found")
1 error was reported (see above)
EXIT_CODE=1
```

Affected definition range:

- `generational/impl/GC.Gen.Impl.fst:526-566`: `derive_fwd_ptrs_classified_pointwise`.
- This is before the `minor_collect_full` body (`generational/impl/GC.Gen.Impl.fst:736-856`), so `minor_collect_full` is not reached under root flags.

### 7. `GC.Gen.Impl.fst` with local `generational/Makefile` flags

Command:

```sh
timeout 90s ./fstar/bin/fstar.exe --cache_checked_modules \
  --odir /tmp/pvgc-debug-out-impl-local-timeout \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl \
  --z3rlimit 160 \
  generational/impl/GC.Gen.Impl.fst
```

Result: **exit 124** (timeout), no diagnostic before timeout.

A query-stats probe of the same local command reached the helper sequence before timing out. Last representative completed obligations before timeout:

```text
(GC.Gen.Impl.fst(438,3-466,85)) Query-stats (GC.Gen.Impl.derive_fwd_case_a, 1)
  succeeded in 8321 milliseconds ...
(GC.Gen.Impl.fst(496,3-522,37)) Query-stats (GC.Gen.Impl.derive_fwd_case_b, 1)
  succeeded in 1556 milliseconds ...
```

The next proof region is `derive_fwd_ptrs_classified_pointwise` at `GC.Gen.Impl.fst:526-566`, the same region that crashes Z3 under root flags.

## Current admits / assumptions / incomplete-proof comments

Direct source admits/assumptions in relevant F*/Pulse files:

```text
common/impl/GC.Impl.Heap.fst:40: assume val platform_fits_u64 : squash SZ.fits_u64
generational/impl/GC.Gen.Impl.MinorHeap.fst:26: assume val platform_fits_u64 : squash SZ.fits_u64
generational/spec/GC.Gen.TwoPassEquiv.fst:1453: TODO: add field-membership precondition and prove from fwd_ptrs_classified.
generational/spec/GC.Gen.TwoPassEquiv.fst:1454: admit ()
generational/spec/GC.Gen.CheneyPreservation.fst:2424: = admit ()
```

Additional assumption-like warnings emitted by F* due interface-only modules:

```text
common/impl/GC.Impl.ArrayWord.fsti: Interface GC.Impl.ArrayWord is admitted without an implementation
common/spec/GC.Spec.ZeroAddr.fsti: Interface GC.Spec.ZeroAddr is admitted without an implementation
```

Also many Pulse/FStar library `.fsti` warnings are emitted under `--report_assumes warn`; those are upstream/library interfaces, not project proof holes.

Other incomplete/fragility comments found, but not current hard proof holes:

```text
mark-and-sweep/impl/GC.Impl.Coalesce.Lemmas.fst:192: Avoids universals that fail to instantiate with --split_queries always.
mark-and-sweep/spec/GC.Spec.Sweep.fst:991: isolated to avoid "incomplete quantifiers" failures.
mark-and-sweep/spec/GC.Spec.MarkBoundedCorrectness.fst:1212: avoids "incomplete quantifiers".
generational/spec/GC.Gen.PromoteUpdate.PromoteFields.Step.fst:672: avoids "incomplete quantifiers" from context pollution.
generational/impl/GC.Gen.Impl.Cheney.fst:373: comment says runtime bounds fail => noop; not a proof failure.
```

## Failure inventory summary

| Order seen | File / target | Command family | Exit | First failure / symptom | Relevance |
|---:|---|---|---:|---|---|
| 1 | `mark-and-sweep/spec/GC.Test.Bridge.fst` | root `make generational` | 2 / targeted 1 | Assertion failed at line 161, cannot prove `read_write_different` precondition from `GC.Spec.Heap.fsti:128` | Blocks root build before generational proof slice. |
| 2 | `generational/spec/GC.Gen.CheneyPreservation.fst` | `make -C generational verify` | 124 timeout | Verification does not complete within 90-300s; query-stats shows very slow `cheney_forward_one_preserves_no_black` and `cheney_scan_preserves_no_black` obligations | Blocks local full generational source verification; also contains admitted `cheney_promote_nonblue_origin`. |
| 3 | `generational/spec/GC.Gen.TwoPassEquiv.fst` | targeted F* | 0 | Verifies only because `fwd_ptrs_classified_at` is admitted | Needed by `minor_collect_full` full-update equivalence. |
| 4 | `generational/impl/GC.Gen.Impl.fst` | root rule flags | 1 | Z3 internal assertion at `derive_fwd_ptrs_classified_pointwise`, lines 526-571 | Direct implementation blocker before `minor_collect_full` body is reached. |
| 5 | `generational/impl/GC.Gen.Impl.fst` | local rule flags | 124 timeout | Query-stats reaches `derive_fwd_case_a/b`, then stalls around the same `derive_fwd_ptrs_classified_pointwise` region | Direct implementation blocker under local intended flags. |

## Likely dependency ordering for completion planning

1. **Root-build blocker outside generational slice:** `mark-and-sweep/spec/GC.Test.Bridge.fst:161`. Until this is addressed or bypassed by a narrower target, root `make generational` will not reach generational proof failures.
2. **Generational preservation proof file:** `generational/spec/GC.Gen.CheneyPreservation.fst`. Local `make -C generational verify` reaches this before later generational files and times out. It also contains the current admit `cheney_promote_nonblue_origin`, which is used by `GC.Gen.Impl.fst` via the interface lemma in `derive_fwd_case_b`.
3. **Two-pass equivalence hole:** `generational/spec/GC.Gen.TwoPassEquiv.fst:1454` (`fwd_ptrs_classified_at`). The file currently verifies with the admit, but full proof completion requires this lemma.
4. **Implementation bridge before `minor_collect_full`:** `generational/impl/GC.Gen.Impl.fst:526-566` (`derive_fwd_ptrs_classified_pointwise`). This is the first hard implementation failure/stall and must verify before F* reaches the `minor_collect_full` body.
5. **`minor_collect_full` body:** `generational/impl/GC.Gen.Impl.fst:736-856`. No direct body obligation was reached in current targeted runs because verification fails or times out earlier in helper lemmas.

No source edits or proof patches were made during this pass.
