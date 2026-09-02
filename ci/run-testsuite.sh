#!/bin/sh
# Run OCaml's own testsuite against the verified GC -- both the bytecode and the
# native variant of every test -- and report against the known-failure baseline.
#
# This is the local equivalent of .github/workflows/testsuite.yml. Same gate:
# "no NEW failures", not "zero failures". The verified GC has documented gaps
# (statmemprof, weak/ephemeron), so ci/expected-failures.txt is the baseline.
#
#   sh ci/run-testsuite.sh              the whole suite (~30 min)
#   sh ci/run-testsuite.sh tests/lib-hashtbl    one directory
#
# Requires ci/build-verified-toolchain.sh to have been run.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
TREE=$ROOT/generational/ocaml-integration/ocaml-4.14-verified-gen
LOG=$ROOT/testsuite.log
SUBDIR=${1:-}

[ -x "$TREE/ocamltest/ocamltest" ] || {
  echo "ocamltest is missing -- run: sh ci/build-verified-toolchain.sh" >&2; exit 1; }

echo "=== running the testsuite (both variants per test); log: $LOG"
cd "$TREE/testsuite"
set +e
if [ -n "$SUBDIR" ]; then
  OCAMLRUNPARAM=b,v=0 TIMEOUT=120 make one DIR="$SUBDIR" 2>&1 | tee "$LOG"
else
  OCAMLRUNPARAM=b,v=0 TIMEOUT=120 make all 2>&1 | tee "$LOG"
fi
set -e

# `make all` exits non-zero whenever any test fails, which is the normal state
# here. The verdict comes from the report, not from make.
if ! grep -q 'tests considered' "$LOG"; then
  echo "The suite produced no summary -- it aborted before running tests." >&2
  tail -40 "$LOG" >&2
  exit 1
fi

if [ -n "$SUBDIR" ]; then
  # No baseline comparison for a single directory: the baseline covers the whole
  # suite, so every failure outside this directory would be reported as "now
  # passing". Show the raw tally instead.
  echo
  grep -E 'tests considered|tests passed|tests failed|tests skipped' "$LOG" || true
  echo
  echo "Single directory: no baseline comparison. Run without an argument for the"
  echo "full suite and the regression gate."
  exit 0
fi

echo
echo "=== report against ci/expected-failures.txt"
cd "$ROOT"
set +e
python3 ci/testsuite_report.py \
  --log "$LOG" \
  --expected ci/expected-failures.txt \
  --html testsuite-report.html \
  --json testsuite-report.json \
  --title "OCaml testsuite - verified GC (local)"
rc=$?
set -e
echo
if [ $rc -ne 0 ]; then
  echo "NEW failures, not in the baseline. See testsuite-report.html."
else
  echo "No regressions against ci/expected-failures.txt."
fi
exit $rc
