#!/bin/sh
# Build what OCaml's own testsuite needs on the verified GC (15-40 min):
#
#   sh ci/build-verified-toolchain.sh
#
# ci/run-testsuite.sh runs ocamltest and the verified tree's own compilers, so
# those have to exist: this runs `make world.opt` + `make ocamltest` in the
# verified tree, rebuilding the whole toolchain ON the verified collector.
# Running your own programs does not need this -- `make -C
# generational/ocaml-integration setup` is enough for ci/run-verified.sh.
#
# It is a one-off. After a GC change, rebuilding the GC and the two runtimes is
# enough (see the README), because ocamltest runs every bytecode test with
# `-use-runtime <tree>/runtime/ocamlrun` and so picks up the new runtime by
# itself (ocamltest/ocaml_files.ml:36, ocaml_flags.ml:49).
#
# The reason to rerun it anyway is that the bootstrap is the broadest stress
# test available: a collector broken enough to matter cannot finish one. The
# infix bug surfaced exactly that way, with `make coldstart` dying on
# camlinternalFormat.ml. It also puts the compiler processes themselves back on
# the current collector -- ocamlc.opt/ocamlopt.opt link it statically.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
INT=$ROOT/generational/ocaml-integration
TREE=$INT/ocaml-4.14-verified-gen
LOG=$ROOT/build-verified-toolchain.log
[ "${1:-}" = "--help" ] && { awk 'NR>1 && /^#/ {sub(/^# ?/,""); print; next} NR>1 {exit}' "$0"; exit 0; }

say() { printf '\n=== %s\n' "$1"; }

say "OCaml trees, the verified GC and both runtimes"
# Only when missing: setup re-applies the runtime patch to an existing tree.
if [ ! -x "$INT/ocaml-4.14-unchanged/_install/bin/ocamlc" ] || [ ! -d "$TREE" ]; then
  make -C "$INT" setup
fi
make -C "$INT/verified_gc"
make -C "$TREE/runtime" ocamlrun libasmrun.a

say "world.opt -- the whole toolchain, on the verified GC"
echo "logging to $LOG"
cd "$TREE"
set -o pipefail 2>/dev/null || true
if ! make world.opt 2>&1 | tee "$LOG"; then
  echo
  echo "world.opt FAILED -- which is itself the interesting result. What was"
  echo "being compiled, and what the runtime said:"
  echo
  grep -nE 'Segmentation|Fatal error|Aborted|out of memory|internal error' "$LOG" | tail -20 || true
  grep -E 'ocamlc|ocamlopt|ocamlrun' "$LOG" | tail -5 || true
  exit 1
fi

say "ocamltest"
make ocamltest 2>&1 | tee -a "$LOG" >/dev/null

cat <<MSG

Ready for the testsuite:
  sh ci/run-testsuite.sh
MSG
