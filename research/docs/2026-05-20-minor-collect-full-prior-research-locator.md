# Local Research Locator: Generational GC / Minor Collect / Cheney Promotion

Date searched: 2026-05-20

I found no populated `research/tickets/` or `specs/` directories in this checkout. The `research/docs/` directory is empty, so the relevant material lives in top-level design/review docs and the `generational/` integration docs.

## Related Tickets

- _None found locally._

## Related Docs

- 🟢 `generational/ocaml-integration/verified_gc/OCAML_INTEGRATION.md` — `Verified Generational GC — OCaml 4.14 Integration`; most detailed integration/proof-status narrative, including minor GC (Cheney promotion), major GC, two-pass equivalence, and F* proof-status notes. **Current-looking** and appears to be the most up-to-date summary.
- 🟢 `generational/ocaml-integration/README.md` — `Verified Generational GC — OCaml 4.14 Integration`; shorter integration overview for the verified generational GC and runtime bridge. **Current-looking**.
- 🟢 `END_TO_END_REVIEW.md` — `Pulse-Verified-GC: End-to-End Review`; summarizes proof coverage for minor collection, promotion, BFS completeness, major GC correctness, and composition. **Current-looking**.
- 🟢 `PHASE2_PLAN.md` — `Phase 2: Generational GC — C Extraction, OCaml Integration & Benchmarking`; implementation/extraction plan with notes on `minor_collect`, `cheney_promote_phase`, and integration gaps. **Current-looking**, but some sections are clearly roadmap/planning rather than settled truth.
- 🟢 `GENERATIONAL_PLAN.md` — `Generational Garbage Collector — Revised Plan`; high-level revised plan with proof-status notes and design decisions around conservative promotion and composed correctness. **Current-looking**, but partially superseded by later integration/proof docs.
- 🟢 `generational/PATCHES.md` — hand-patch inventory for extraction/integration deltas; contains many notes on minor-field translation, infix handling, root rewriting, and promotion behavior. **Current-looking**, but several sections are explicitly marked done/eliminated and may be superseded by the verified integration docs.
- 🟡 `generational_gc.md` — original project brief for extending mark-and-sweep with a generational copying collector, including minor heap / major heap division and correctness goal. **Aged / likely superseded** by the more detailed `GENERATIONAL_PLAN.md` and integration docs.

## Related Specs

- _No standalone `specs/` directory exists in this checkout._
- The nearest spec-like material is embedded in the docs above, especially `generational/ocaml-integration/verified_gc/OCAML_INTEGRATION.md` and `END_TO_END_REVIEW.md`.

## Related Notes / Discussions

- 🟢 `END_TO_END_REVIEW.md` — contains proof-status style discussion of minor collection, Cheney BFS completeness, promotion, and major-GC preconditions.
- 🟢 `GENERATIONAL_PLAN.md` — includes design discussion, remaining proof obligations, and notes on promotion and composed correctness.
- 🟢 `PHASE2_PLAN.md` — includes integration discussion around `minor_collect`, root rewriting, and full-GC sequencing.

## Quick read on relevance

Most relevant to your target topics:
1. `generational/ocaml-integration/verified_gc/OCAML_INTEGRATION.md`
2. `END_TO_END_REVIEW.md`
3. `PHASE2_PLAN.md`
4. `GENERATIONAL_PLAN.md`
5. `generational/PATCHES.md`
6. `generational_gc.md`

Current vs superseded:
- The integration/proof-status docs in `generational/ocaml-integration/verified_gc/` and `END_TO_END_REVIEW.md` appear current.
- `GENERATIONAL_PLAN.md` and `PHASE2_PLAN.md` are useful but partly roadmap-oriented.
- `generational_gc.md` is likely the oldest/superseded high-level brief.
