#!/usr/bin/env bash
# Mutation check for the rescan-skipping bounded mark.
#
#   tools/mutation-ov-never-set.sh [--proof-only]
#
# The mutant never sets the overflow flag in mark_inner_loop_impl
# (`ovr := (o || full)` becomes `ovr := o`), so `collect` would skip the heap
# rescan even after the gray stack overflowed.  Both halves must reject it:
#
#   1. proof:   GC.Impl.MarkBounded must FAIL to verify, on the invariant
#               `not vo ==> gray_objects_on_stack s st_cur`.
#   2. runtime: the same edit in the extracted C, built into a throwaway
#               verified-gen runtime, must FAIL tests/gray_overflow.ml.
#
# Nothing in the repository is modified: the mutants live in a temp dir, the
# proof check uses a scratch cache (tools/try-module.sh), and the runtime is
# built in a temporary worktree of ocaml-4.14-verified-gen, removed at exit.
# Exit 0 means both halves caught the mutant.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
INTEG="$ROOT/generational/ocaml-integration"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/ov-mutation.XXXXXX")"
WT=""
cleanup() {
  [ -n "$WT" ] && git -C "$INTEG/ocaml-4.14-verified-gen" worktree remove --force "$WT" >/dev/null 2>&1 || true
  rm -rf "$TMP"
}
trap cleanup EXIT

# mutate <src> <dst> <from> <to>: exactly one occurrence, or fail.
mutate() {
  local n; n=$(grep -cF -- "$3" "$1" || true)
  [ "$n" = 1 ] || { echo "mutation site '$3' found $n times in $1" >&2; exit 2; }
  awk -v from="$3" -v to="$4" '{ i = index($0, from); if (i) $0 = substr($0, 1, i-1) to substr($0, i+length(from)); print }' "$1" > "$2"
}

# --- 1. proof ---------------------------------------------------------------
mkdir -p "$TMP/fst"
mutate "$ROOT/mark-and-sweep/impl/GC.Impl.MarkBounded.fst" "$TMP/fst/GC.Impl.MarkBounded.fst" \
  'ovr := (o || full);' 'ovr := o;'
echo "=== proof: verifying GC.Impl.MarkBounded with the flag never set (must fail) ==="
if SCRATCH="$TMP/cache" FULL_LOG="$TMP/proof.log" "$ROOT/tools/try-module.sh" \
     "$TMP/fst/GC.Impl.MarkBounded.fst" --z3refresh; then
  echo "MUTANT SURVIVED: the proof accepted a mark loop that never sets ov" >&2; exit 1
fi
grep -q "Failed to prove: GC.Spec.Mark.gray_objects_on_stack" "$TMP/proof.log" || {
  echo "the mutant failed, but not on gray_objects_on_stack:" >&2
  grep -n "Error\|Failed to prove" "$TMP/proof.log" >&2 || true; exit 1; }
echo "proof: mutant rejected (gray_objects_on_stack not maintained)"

[ "${1:-}" = "--proof-only" ] && exit 0

# --- 2. runtime ---------------------------------------------------------------
echo "=== runtime: building a verified-gen runtime with the flag never set ==="
cp -R "$ROOT/generational/snapshot" "$TMP/snapshot"
mutate "$ROOT/generational/snapshot/GC_Gen_Impl.c" "$TMP/snapshot/GC_Gen_Impl.c" \
  'ovr = o || full;' 'ovr = o;'
WT="$TMP/ocaml-4.14-verified-gen"
git -C "$INTEG/ocaml-4.14-verified-gen" worktree add -q --detach "$WT" HEAD
(cd "$WT" && git apply "$INTEG/patches/runtime_gen.patch" 2>/dev/null \
   && ./configure -q --disable-naked-pointers >/dev/null)
mkdir -p "$TMP/verified_gc"
cp "$INTEG/verified_gc/alloc_gen.c" "$INTEG/verified_gc/Makefile" \
   "$INTEG/verified_gc/profiling_counters.h" "$TMP/verified_gc/"
ln -s "$INTEG/caml" "$TMP/caml"
ln -sfn "$TMP/verified_gc" "$WT/runtime/verified_gc"
make -s -C "$WT/runtime" -j8 SNAPSHOT="$TMP/snapshot" ocamlrun >"$TMP/build.log" 2>&1 \
  || { tail -20 "$TMP/build.log" >&2; exit 2; }

OCAMLC="$INTEG/ocaml-4.14-unchanged/_install/bin/ocamlc"
(cd "$TMP" && cp "$INTEG/tests/gray_overflow.ml" . && "$OCAMLC" -o gray_overflow.byte gray_overflow.ml)
WORDS=2000000
echo "--- gray_overflow under the mutant (must fail) ---"
if MIN_EXPANSION_WORDSIZE=$WORDS "$WT/runtime/ocamlrun" "$TMP/gray_overflow.byte" $WORDS; then
  echo "MUTANT SURVIVED: gray_overflow passed with the rescan skipped after overflow" >&2; exit 1
fi
echo "runtime: mutant rejected by gray_overflow"
echo "=== both halves caught the mutant ==="
