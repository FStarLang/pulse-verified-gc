#!/bin/sh
# Differential run of one test program: stock OCaml's output is the
# reference, and the verified runtime must print exactly the same thing.
#
#   run_differential.sh NAME 'STOCK COMMAND' 'VERIFIED COMMAND'
#
# The major mode is VERGC_MAJOR (VERGC_SWEEP is an alias).  Incremental, the
# verified command runs once per pacing --
#   - the default (4.14's pacing);
#   - small slices, often (VERGC_SLICE_MIN_WORDS=64
#     MINOR_HEAP_WORDS=32768): marking and the sweep each span many minor
#     collections, so the program runs mid-mark for long stretches;
#   - a tiny mark stack and back-to-back cycles
#     (VERGC_SLICE_MIN_WORDS=256 VERGC_MARK_STACK=8 VERGC_TRIGGER_MIN_WORDS=0):
#     root darkening and the barrier overflow the stack, so the slices rescan
#     the heap, and full collections are often requested mid-cycle
# -- and once otherwise.
#
# With REQUIRE_MID_SWEEP=1 / REQUIRE_MID_MARK=1, every incremental run but the
# default-paced one must also show (VERGC_MAJOR_STATS) that the test exercised
# what it is about: sweep slices ran and major allocations happened mid-sweep
# / marking spanned several slices and the program ran in between (minor
# collections, major allocations or barrier calls while marking).
set -eu
name=$1; stock=$2; verified=$3
out=${TMPDIR:-/tmp}/vergc-diff.$$
trap 'rm -f "$out".*' EXIT
mode=${VERGC_MAJOR:-${VERGC_SWEEP:-stw}}

sh -c "$stock" > "$out.expected"

if [ "$mode" = incremental ]; then
  set -- "" "VERGC_SLICE_MIN_WORDS=64 MINOR_HEAP_WORDS=32768" \
         "VERGC_SLICE_MIN_WORDS=256 VERGC_MARK_STACK=8 VERGC_TRIGGER_MIN_WORDS=0"
else
  set -- ""
fi

stat() { echo "$1" | sed -n "s/.* $2=\([0-9]*\).*/\1/p"; }

for pacing in "$@"; do
  label="$name (VERGC_MAJOR=$mode${pacing:+ $pacing})"
  echo "--- $label"
  if ! env $pacing VERGC_MAJOR=$mode VERGC_MAJOR_STATS=1 sh -c "$verified" > "$out.actual" 2> "$out.err"; then
    cat "$out.actual" "$out.err"
    echo "FAIL: $label exited non-zero" >&2
    exit 1
  fi
  if ! cmp -s "$out.expected" "$out.actual"; then
    diff "$out.expected" "$out.actual" || true
    echo "FAIL: $label differs from stock OCaml" >&2
    exit 1
  fi
  stats=$(grep '^vergc-major:' "$out.err" || true)
  grep -v '^vergc-major:\|^vergc-pauses:' "$out.err" >&2 || true
  echo "    $stats"
  if [ "$mode" = incremental ] && [ -n "$pacing" ]; then
    if [ "${REQUIRE_MID_SWEEP:-0}" = 1 ]; then
      slices=$(stat "$stats" sweep_slices); mid=$(stat "$stats" alloc_mid_sweep)
      if [ "${slices:-0}" -eq 0 ] || [ "${mid:-0}" -eq 0 ]; then
        echo "FAIL: $label never ran mid-sweep (sweep_slices=${slices:-?} alloc_mid_sweep=${mid:-?})" >&2
        exit 1
      fi
    fi
    if [ "${REQUIRE_MID_MARK:-0}" = 1 ]; then
      spanned=$(stat "$stats" marks_spanned)
      steps=$(( $(stat "$stats" minor_mid_mark) + $(stat "$stats" alloc_mid_mark) + $(stat "$stats" modify_mid_mark) ))
      if [ "${spanned:-0}" -eq 0 ] || [ "$steps" -eq 0 ]; then
        echo "FAIL: $label never ran mid-mark (marks_spanned=${spanned:-?} program steps=$steps)" >&2
        exit 1
      fi
    fi
  fi
done
echo "    same output as stock OCaml"
