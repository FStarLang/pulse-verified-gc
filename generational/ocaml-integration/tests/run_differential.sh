#!/bin/sh
# Differential run of one test program: stock OCaml's output is the
# reference, and the verified runtime must print exactly the same thing.
#
#   run_differential.sh NAME 'STOCK COMMAND' 'VERIFIED COMMAND'
#
# The verified command runs once per pacing when VERGC_SWEEP=incremental --
# the default slice budget, VERGC_SWEEP_K=1 (a sweep spans the next cycle's
# trigger, so full collections are requested mid-sweep) and tiny slices with a
# small nursery (VERGC_SWEEP_MIN_WORDS=256 VERGC_SWEEP_K=0
# MINOR_HEAP_WORDS=32768: a sweep spans thousands of minor collections) --
# and once otherwise. With REQUIRE_MID_SWEEP=1, an incremental run must also
# show (VERGC_SWEEP_STATS) that slices ran and that major allocations happened
# mid-sweep, i.e. that the test exercised what it is about.
set -eu
name=$1; stock=$2; verified=$3
out=${TMPDIR:-/tmp}/vergc-diff.$$
trap 'rm -f "$out".*' EXIT

sh -c "$stock" > "$out.expected"

if [ "${VERGC_SWEEP:-stw}" = incremental ]; then
  set -- "" "VERGC_SWEEP_K=1" \
         "VERGC_SWEEP_MIN_WORDS=256 VERGC_SWEEP_K=0 MINOR_HEAP_WORDS=32768"
else
  set -- ""
fi

for pacing in "$@"; do
  label="$name (VERGC_SWEEP=${VERGC_SWEEP:-stw}${pacing:+ $pacing})"
  echo "--- $label"
  if ! env $pacing VERGC_SWEEP_STATS=1 sh -c "$verified" > "$out.actual" 2> "$out.err"; then
    cat "$out.actual" "$out.err"
    echo "FAIL: $label exited non-zero" >&2
    exit 1
  fi
  if ! cmp -s "$out.expected" "$out.actual"; then
    diff "$out.expected" "$out.actual" || true
    echo "FAIL: $label differs from stock OCaml" >&2
    exit 1
  fi
  stats=$(grep '^vergc-sweep:' "$out.err" || true)
  grep -v '^vergc-sweep:' "$out.err" >&2 || true
  echo "    $stats"
  if [ "${VERGC_SWEEP:-stw}" = incremental ] && [ "${REQUIRE_MID_SWEEP:-0}" = 1 ]; then
    slices=$(echo "$stats" | sed -n 's/.* slices=\([0-9]*\).*/\1/p')
    mid=$(echo "$stats" | sed -n 's/.* alloc_mid_sweep=\([0-9]*\).*/\1/p')
    if [ "${slices:-0}" -eq 0 ] || [ "${mid:-0}" -eq 0 ]; then
      echo "FAIL: $label never ran mid-sweep (slices=${slices:-?} alloc_mid_sweep=${mid:-?})" >&2
      exit 1
    fi
  fi
done
echo "    same output as stock OCaml"
