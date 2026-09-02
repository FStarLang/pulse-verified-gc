#!/bin/sh
# Build what you need to test against the verified GC.
#
#   sh ci/build-verified-toolchain.sh            runtimes only  (minutes)
#   sh ci/build-verified-toolchain.sh --full     + world.opt     (15-40 min)
#
# The default is enough for ci/run-verified.sh, because that swaps the *runtime*
# and compiles with the stock compiler:
#   - bytecode carries no collector; the collector is whichever ocamlrun runs it
#   - native links the collector out of the verified GC's libasmrun.a via -I
#
# --full additionally runs `make world.opt` + `make ocamltest`, which rebuilds
# the whole toolchain ON the verified collector. ci/run-testsuite.sh needs the
# compilers to EXIST, so this is a one-off; a later GC change needs only the
# default path, because ocamltest runs every bytecode test with
# `-use-runtime <tree>/runtime/ocamlrun` and so picks up the new runtime by
# itself (ocamltest/ocaml_files.ml:36, ocaml_flags.ml:49).
#
# The reason to rerun --full anyway is that the bootstrap is the broadest stress
# test available: a collector broken enough to matter cannot finish one. The
# infix bug surfaced exactly that way, with `make coldstart` dying on
# camlinternalFormat.ml. It also puts the compiler processes themselves back on
# the current collector -- ocamlc.opt/ocamlopt.opt link it statically.
#
# Rerun after any change to the F* source, the snapshot, or a hand patch.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
INT=$ROOT/generational/ocaml-integration
TREE=$INT/ocaml-4.14-verified-gen
LOG=$ROOT/build-verified-toolchain.log

FULL=no
[ "${1:-}" = "--full" ] && FULL=yes
[ "${1:-}" = "--help" ] && { awk 'NR>1 && /^#/ {sub(/^# ?/,""); print; next} NR>1 {exit}' "$0"; exit 0; }

say() { printf '\n=== %s\n' "$1"; }

say "OCaml trees (stock, installed + verified, patched)"
if [ ! -x "$INT/ocaml-4.14-unchanged/_install/bin/ocamlc" ] || [ ! -d "$TREE" ]; then
  make -C "$INT" setup
else
  echo "already present"
fi

say "the verified GC"
make -C "$INT/verified_gc"

say "the verified runtimes (bytecode ocamlrun + native libasmrun.a)"
make -C "$TREE/runtime" ocamlrun libasmrun.a

if [ "$FULL" = no ]; then
  cat <<EOF

Ready. Run your own code:

  sh ci/run-verified.sh prog.ml
  sh ci/run-verified.sh some/dir

For OCaml's own testsuite the tree's compilers have to exist -- if you have not
run --full before, do that once, then use ci/run-testsuite.sh. After a GC change
this fast path is enough; --full is worth rerunning as a stress test in itself.
EOF
  exit 0
fi

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

cat <<EOF

Ready, including the testsuite:

  sh ci/run-verified.sh prog.ml
  sh ci/run-testsuite.sh
EOF
