#!/bin/sh
# Builds runtime variants for the parallel-sweep tests (docs/parallel-sweep-phase1.md,
# §9, Stage 3), out of tree under parallel-sweep/_build/rt/<variant>/:
#
#   ./build.sh check     ocamlrun and libasmrun.a with the test bridge
#                        (PAR_SWEEP_CHECK=1): every parallel sweep is compared
#                        with the sequential one
#
# The tree's own runtimes are rebuilt as the default build afterwards, so
# `make test` keeps testing what ships.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
INT=$HERE/../../generational/ocaml-integration
TREE=$INT/ocaml-4.14-verified-gen
OUT=$HERE/../_build/rt
V=${1:?usage: build.sh check}

runtimes() {   # build the tree's runtimes with the given make variables
  make -C "$INT/verified_gc" clean >/dev/null
  rm -f "$TREE/runtime/ocamlrun" "$TREE/runtime/libcamlrun.a" "$TREE/runtime/libasmrun.a"
  make -C "$TREE/runtime" "$@" ocamlrun libasmrun.a >/dev/null
}

case $V in
  check) runtimes PAR_SWEEP_CHECK=1 ;;
  *) echo "unknown variant $V" >&2; exit 2 ;;
esac
mkdir -p "$OUT/$V"
cp "$TREE/runtime/ocamlrun" "$TREE/runtime/libasmrun.a" "$TREE/runtime/libcamlrun.a" \
   "$TREE/runtime/prims.o" "$OUT/$V/"
runtimes PAR_SWEEP_CHECK=
echo "built $OUT/$V; tree runtimes rebuilt as the default build"
