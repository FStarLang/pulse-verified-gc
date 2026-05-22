# F* v2026.05.17 upgrade plan

## Goal

Upgrade the repository to the latest official F* binary release, currently
`v2026.05.17`, and restore a clean build, extraction, and verified GC
integration.

## Useful prior work

Commit `6958064` on `origin/generational` upgraded to `v2026.05.10` and fixed
several regressions from the newer F*/Z3 stack. Reuse its notes selectively:
duplicate top-level definitions against `.fsti`, NL arithmetic regressions,
and per-file SMT tuning changes may recur.

## Steps

1. Update `setup.sh` so the default install is the official `v2026.05.17`
   binary release, with a way to force reinstalling the local ignored `fstar/`
   toolchain.
2. Install the new toolchain with `./setup.sh --force` and confirm
   `./fstar/bin/fstar.exe --version` reports `F* 2026.05.17`.
3. Run a full clean top-level build with `make clean && make -j128 -k`.
4. For each regression, prefer small source fixes and targeted verification over
   broad rlimit increases. Check the `v2026.05.10` upgrade commit for analogous
   fixes before inventing new ones.
5. Once verification is clean, run extraction and integration checks:
   `make -j128 -k extract`,
   `cd generational/snapshot && make clean && make -j128 -k`, and
   `cd generational/ocaml-integration/verified_gc && make clean && make -j128 -k`.
6. Commit stable milestones as the upgrade progresses.

## Progress

- Identified latest release: `F* v2026.05.17`.
- Found prior related upgrade commit: `6958064` (`v2026.05.10`).
- Updated `setup.sh` to default to the official `v2026.05.17` binary release
  and added `--force` reinstall support.
- Installed and verified the local ignored toolchain:
  `F* 2026.05.17` / KaRaMeL `2fe560bbae17fe8a855b0dcf462db18ec37edc02`.
- Fixed verification regressions:
  - added `GC.Lib.Header` rlimit overrides in root/common/mark-and-sweep
    Makefiles;
  - removed duplicate top-level definitions now rejected when definitions are
    already provided in `.fsti` files;
  - added explicit arithmetic/branch facts in generational reachability and
    Cheney preservation proofs;
  - factored the infix-target forwarding injectivity proof;
  - removed an unused private BlueProm helper whose dead proof regressed.
- Fixed mark-and-sweep extraction by adding the interface-only
  `GC.Impl.ArrayWord` module to its KaRaMeL bundle.
- Refreshed mark-and-sweep and generational snapshots for the new extractor.
- Added mark-and-sweep snapshot `compat.c/h` for the extern word read/write
  primitives now emitted by extraction.
- Validation completed:
  `make clean && make -j128 -k`,
  `make -j128 -k extract`,
  mark-and-sweep and generational `snapshot` targets,
  both standalone snapshot builds/tests, and
  `generational/ocaml-integration/verified_gc` rebuild.

## Remaining note

- `mark-and-sweep/ocaml-integration/verified_gc` does not build standalone in
  this checkout unless its OCaml runtime setup has been created; it currently
  fails looking for `../caml/misc.h`. The generational `verified_gc`
  integration, which is the active integration for this branch, builds cleanly.
