#!/usr/bin/env bash
# Negative controls for the object-start table (part A of
# docs/allocator-table-and-size-lists.md, section 8.6).
#
#   tools/mutation-object-table.sh [M6|M7|M8|M11 ...]
#
# Each mutant is applied to a copy of one Pulse module and, the same edit, to
# a copy of the extracted C.  Both halves must reject it:
#
#   1. proof:   the mutated module must FAIL to verify (scratch cache, via
#               tools/try-module.sh), with an error in the expected function;
#   2. runtime: the snapshot's directed tests (generational/snapshot, `make`)
#               built from the mutated C must FAIL.
#
#   M6   the sweep's cursor emits every visited header, not only the output
#        walk positions (a header a run absorbs becomes an entry)
#   M7   the allocator skips the first boundary inside a new object
#   M8   the allocator stores the object address (hd + 8), not its header
#   M11  the allocator writes without the guard (alloc_stale)
#
# Nothing in the repository is modified: the mutants live in a temp dir.
# Exit 0 means every mutant asked for was caught by both halves.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/ot-mutation.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
MUTANTS=("$@"); [ ${#MUTANTS[@]} -eq 0 ] && MUTANTS=(M6 M7 M8 M11)

# mutate <file> <from> <to> <count>: replace every occurrence, which must
# number exactly <count>.
mutate() {
  local n; n=$(grep -cF -- "$2" "$1" || true)
  [ "$n" = "$4" ] || { echo "mutation site '$2' found $n times in $1, expected $4" >&2; return 2; }
  python3 - "$1" "$2" "$3" <<'PY'
import sys
p, a, b = sys.argv[1:]
s = open(p).read()
open(p, 'w').write(s.replace(a, b))
PY
}

FUSED=mark-and-sweep/impl/GC.Impl.FusedSweepCoalesce.fst
OTI=mark-and-sweep/impl/GC.Impl.ObjectTable.fst

failed=0
for m in "${MUTANTS[@]}"; do
  D="$TMP/$m"; mkdir -p "$D/fst"
  cp -R "$ROOT/generational/snapshot" "$D/snapshot"
  C="$D/snapshot/GC_Gen_Impl.c"
  case $m in
    M6)  src=$FUSED
         cp "$ROOT/$src" "$D/fst/"
         mutate "$D/fst/$(basename $src)" 'let starts = U64.eq cur_rw 0UL;' 'let starts = true;' 1 &&
         mutate "$C" 'bool starts = cur_rw == 0ULL;' 'bool starts = true;' 1 ;;
    M7)  src=$OTI
         cp "$ROOT/$src" "$D/fst/"
         mutate "$D/fst/$(basename $src)" 'let mut k = j0;' 'let mut k = U64.add j0 1UL;' 1 &&
         mutate "$D/fst/$(basename $src)" 'let mut nb = nb0;' 'let mut nb = U64.add nb0 OT.window_bytes_u64;' 1 &&
         mutate "$C" 'uint64_t k = j0;' 'uint64_t k = j0 + 1ULL;' 2 &&
         mutate "$C" 'uint64_t nb = nb0;' 'uint64_t nb = nb0 + 0x10000ULL;' 2 ;;
    M8)  src=$OTI
         cp "$ROOT/$src" "$D/fst/"
         mutate "$D/fst/$(basename $src)" 'emit_impl tbl k nb hp lim;' 'emit_impl tbl k nb obj lim;' 1 &&
         mutate "$C" 'tbl[(size_t)vk] = hp;' 'tbl[(size_t)vk] = obj;' 2 ;;
    M11) src=$OTI
         cp "$ROOT/$src" "$D/fst/"
         mutate "$D/fst/$(basename $src)" 'if stale {' 'if false {' 1 &&
         mutate "$C" 'if (!__anf00)' 'if (1)' 2 ;;
    *)   echo "unknown mutant $m" >&2; exit 2 ;;
  esac || exit 2

  echo "=== $m: proof ($(basename $src), must fail) ==="
  if SCRATCH="$D/cache" FULL_LOG="$D/proof.log" "$ROOT/tools/try-module.sh" \
       "$D/fst/$(basename $src)" --z3refresh > "$D/proof.out"; then
    echo "$m MUTANT SURVIVED the proof"; failed=1
  else
    echo "$m proof: rejected"
    grep -E "^\* Error|Failed to prove" "$D/proof.log" | head -4 | sed 's/^/    /'
  fi

  echo "=== $m: snapshot tests (must fail) ==="
  if (cd "$D/snapshot" && make clean >/dev/null 2>&1; make > "$D/snap.log" 2>&1); then
    echo "$m MUTANT SURVIVED the snapshot tests"; failed=1
  else
    echo "$m snapshot: rejected"
    grep -E "^FAIL" "$D/snap.log" | head -4 | sed 's/^/    /'
  fi
done
exit $failed
