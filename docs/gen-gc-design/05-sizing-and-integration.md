Status: design, pre-Stage-4 capture

## TL;DR

The verified minor heap currently defaults to a toy `minor_size = 256` bytes
(`common/spec/GC.Spec.MinorHeap.fst:34`), four orders of magnitude below
OCaml 4's 2 MiB. Stage 4 flips it from a `let` to a `val` (mirroring
`val heap_size` at `common/spec/GC.Spec.Base.fsti:29`), reads the size at
init time from a CLI flag on the OCaml-integration harness (default 2 MiB),
and instruments the snapshot smoke test with per-collect survival logging
so we can validate the default empirically. `Max_young_wosize = 256` words
already matches OCaml 4 and stays.

Reference: [Real World OCaml — Understanding the Garbage
Collector](https://dev.realworldocaml.org/garbage-collector.html).

## Why 256 bytes is a toy

OCaml 4's default minor heap is 262 144 words = 2 MiB on 64-bit. With a 256
byte minor heap, the verified GC triggers a minor collect roughly every
`256 / mword = 32` words allocated; OCaml triggers one roughly every
`262 144` words. For the same allocation volume that fills OCaml's minor
heap once, our verified-default configuration runs ~8192× more minor
collects. That overhead is acceptable (in fact desirable) during F*
verification — every CI run exercises the collect path many times — but it
makes the GC unsuitable for benchmarking against production OCaml until
`minor_size` is configurable.

The refinement at `common/spec/GC.Spec.MinorHeap.fst:34` requires
`minor_size >= 16` and 8-aligned. 256 B sits comfortably above the floor
(8 single-word allocations fit) while keeping verification examples small.

## Spec-level configuration mechanism

The existing major heap follows this pattern in
`common/spec/GC.Spec.Base.fsti:29-32`:

```fstar
val heap_size : n:pos{n % U64.v mword == 0 /\ n >= 16 /\
                      n < pow2 57 /\ n < pow2 64}
val heap_size_u64 : n:U64.t{U64.v n == heap_size}
```

`val` (not `let`) leaves the value abstract at the spec level so callers
prove against the refinement, never the literal. Extraction substitutes a
concrete value (currently hard-coded in the snapshot, eventually read from
`OCAMLRUNPARAM`).

When Stage 4 lands, we flip `common/spec/GC.Spec.MinorHeap.fst:34` from:

```fstar
let minor_size : n:pos{...} = 256
let minor_size_u64 : n:U64.t{U64.v n == minor_size} = 256UL
```

to:

```fstar
val minor_size : n:pos{n % U64.v mword == 0 /\ n >= 16 /\
                       n < pow2 57 /\ n < pow2 64}
val minor_size_u64 : n:U64.t{U64.v n == minor_size}
```

No existing proof in `GC.Spec.MinorHeap.fst` depends on
`minor_size == 256` — every lemma works against the refinement. The
Stage 4 PR will confirm with a `git grep -n '\b256\b'` audit of the spec
files; any hit outside the constant definition is a bug.

## Max_young_wosize stays at 256 words

OCaml 4's `Max_young_wosize` is 256 words = 2 KiB. Allocations strictly
larger go straight to the major heap (`alloc_shr`-equivalent path); smaller
ones land in the minor heap (`alloc_small`-equivalent). The plan already
adopts 256 words (`/home/eioannidis/.claude/plans/try-to-build-and-purring-cake.md`,
"max_young_wosize constant"). No change at Stage 4. We will, however, also
promote it to a `val` for symmetry — runtime tunability is cheap once the
mechanism is in place, and matches OCaml's `OCAMLRUNPARAM=l=<words>` knob.

## Stage 4 deliverable: OCAMLRUNPARAM-style init

OCaml's runtime parses `OCAMLRUNPARAM` (`s=<size>` for minor heap, `l=<words>`
for max_young_wosize, etc.) at `caml_init_gc` time. Our equivalent in the
integration harness:

- Add `--minor-size <bytes>` and `--max-young-wosize <words>` CLI flags to
  the harness binary in `mark-and-sweep/ocaml-integration/`.
- Defaults: `minor_size = 2 MiB`, `max_young_wosize = 256` words, both
  matching OCaml 4 on 64-bit.
- Validate at init: `minor_size` is 8-aligned and `>= 16`. These are
  refinements baked into the spec, so bad input is a contract bug — fail
  fast with a clear error rather than try to recover.
- Wire-up: today, extracted C consumes `heap_size` as a compile-time
  `#define` in `GC_Impl.h`. KaRaMeL extraction of a `val` instead emits
  an `extern` symbol, which the harness defines before calling `alloc_*`.
  A hand-written shim under `mark-and-sweep/ocaml-integration/verified_gc/`
  bridges the CLI flags to those symbols. No edits to the major-heap
  source modules.

## Survival-rate measurement plan

The right minor heap size is workload-dependent. OCaml's 2 MiB default was
tuned empirically against the OCaml self-compilation workload, where
roughly 5–10% of allocations survive a minor collect. If the survival rate
exceeds ~30% on representative workloads, the minor heap is too small —
the bump allocator effectively becomes a copying allocator into the major
heap and we pay full mark-and-sweep cost on every minor cycle.

Stage 4 will add a `--log-promotions` flag to the harness that, after each
minor collect, prints two numbers to stderr:

- `promoted_bytes` — sum over the collect of `(wosize + 1) * mword` for
  each object that survived.
- `minor_size` — the configured size (constant within a run).

The smoke test in `mark-and-sweep/snapshot/main.c` runs a small linked-list
+ array workload. Stage 4 extends it to:

1. Run with `--minor-size = 2 MiB`, `--log-promotions`.
2. Assert promotion ratio `< 30%` over a 64 MiB allocation budget.
3. Fail CI if the ratio exceeds threshold — protects against workload
   regressions that silently shift to a generationally-unfriendly pattern.

The 30% threshold is a soft heuristic; if it triggers on a workload that
is *expected* to have high survival (e.g. building a long-lived data
structure), we either raise it for that test or revisit `minor_size`. The
measurement is the deliverable; the threshold is advisory.

## Cross-references

- Integration harness: `mark-and-sweep/ocaml-integration/README.md`
  documents the existing major-only API.
- Snapshot smoke test gets the promotion-logging extension at Stage 4
  (`mark-and-sweep/snapshot/main.c`).
- Plan: gap F in `/home/eioannidis/.claude/plans/try-to-build-and-purring-cake.md`.

## Open questions

1. **2 MiB or 256 KiB default?** OCaml 4 ships 2 MiB on 64-bit; OCaml 5
   defaults to 256 KiB per-domain because there are many domains. We are
   sequential (`mark-and-sweep`, no domains), so OCaml 4's 2 MiB is the
   right reference — but if benchmarks at Stage 4 show 256 KiB is enough
   for our workloads, prefer the smaller default for cache friendliness.
2. **Should `Max_young_wosize` be `val` or `let`?** Verification cost is
   the same either way. The `val` flavour is more flexible but requires
   wiring an additional init parameter. Lean `val` for symmetry; revisit
   if the wiring is more than ~20 LOC of shim.
3. **Promotion logging format**: stderr human-readable or JSON to a
   sidecar file? Punt to Stage 4 — depends on whether anything downstream
   (e.g. a regression-tracking script) is consuming it.
