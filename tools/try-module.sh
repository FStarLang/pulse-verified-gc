#!/usr/bin/env bash
# Verify a single module with explicit extra flags, into a scratch cache.
#
#   tools/try-module.sh <path/to/Module.fst> [extra flags...]
#
# Uses a scratch cache dir seeded (by symlink) from _cache, so experiments
# never disturb the real build.  Prints "OK <secs>" or "FAIL <secs>" plus
# the failing locations.
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$1"; shift
MOD="$(basename "$SRC")"

FSTAR_EXE="${FSTAR_EXE:-$ROOT/fstar/bin/fstar.exe}"
SCRATCH="${SCRATCH:-$ROOT/_scratch_cache}"

mkdir -p "$SCRATCH"
# Seed with symlinks to every already-checked dependency, minus this module.
for f in "$ROOT"/_cache/*.checked; do
  b="$(basename "$f")"
  [ "$b" = "$MOD.checked" ] && continue
  [ -e "$SCRATCH/$b" ] || ln -sf "$f" "$SCRATCH/$b"
done
rm -f "$SCRATCH/$MOD.checked"

RETRY="${RETRY:---retry 3}"
start=$(date +%s.%N)
out=$("$FSTAR_EXE" \
  $RETRY \
  --z3smtopt '(set-option :timeout 300000)' \
  --cache_checked_modules --cache_dir "$SCRATCH" \
  --z3version 4.15.3 --odir "$ROOT/_output" \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include "$ROOT/common/spec" --include "$ROOT/common/lib" --include "$ROOT/common/impl" \
  --include "$ROOT/mark-and-sweep/spec" --include "$ROOT/mark-and-sweep/impl" \
  --include "$ROOT/generational/spec" --include "$ROOT/generational/impl" \
  "$@" "$SRC" 2>&1)
rc=$?
end=$(date +%s.%N)
secs=$(echo "$end - $start" | bc)

# FULL_LOG=<path> captures fstar's raw output (needed for --query_stats etc.)
[ -n "${FULL_LOG:-}" ] && printf '%s\n' "$out" > "$FULL_LOG"

if [ $rc -eq 0 ]; then
  printf 'OK %.1f %s\n' "$secs" "$MOD"
else
  printf 'FAIL %.1f %s\n' "$secs" "$MOD"
  echo "$out" | grep -E '^\S+\([0-9]+,[0-9]+-[0-9]+,[0-9]+\).*Error' | sed 's/^/  /'
  echo "$out" | grep -cE 'Error' | sed 's/^/  total error lines: /'
fi
exit $rc
