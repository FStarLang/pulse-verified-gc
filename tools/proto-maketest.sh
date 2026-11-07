#!/bin/sh
# `make test` and `make test-native` (generational/ocaml-integration/tests) on
# one allocator-comparison runtime (tools/proto-build.sh) in one sweep mode:
#
#   tools/proto-maketest.sh VARIANT MODE [THREADS]
#
# The tests run in a copy of tests/ under _build/tests/VARIANT-MODE, so the
# native programs, which link the variant's libasmrun.a, do not replace the
# tree's own.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
INT=$ROOT/generational/ocaml-integration
V=$1; MODE=$2; THREADS=${3:-4}
RT=$INT/_build/proto/$V
DIR=$INT/_build/tests/$V-$MODE
rm -rf "$DIR"; mkdir -p "$DIR"
cp "$INT"/tests/*.ml "$INT"/tests/Makefile "$INT"/tests/*.sh "$DIR"/
cp -R "$INT"/tests/tiny_globals "$DIR"/
rm -f "$DIR"/tiny_globals/*.cm*
STOCK=$INT/ocaml-4.14-unchanged
export OCAMLLIB=$STOCK/_install/lib/ocaml
export VERGC_SWEEP=$MODE VERGC_PAR_SWEEP_THREADS=$THREADS
cd "$DIR"
make test \
  OCAMLC="$STOCK/_install/bin/ocamlc" \
  VERIFIED_GEN_OCAMLRUN="$RT/ocamlrun" \
  UNCHANGED_OCAMLRUN="$STOCK/runtime/ocamlrun"
make test-native \
  OCAMLC="$STOCK/_install/bin/ocamlc" OCAMLOPT="$STOCK/_install/bin/ocamlopt" \
  VERGC_NATIVE_RUNTIME_DIR="$RT" \
  VERIFIED_GEN_OCAMLRUN="$RT/ocamlrun" \
  UNCHANGED_OCAMLRUN="$STOCK/runtime/ocamlrun"
echo "=== make test and test-native passed: $V $MODE"
