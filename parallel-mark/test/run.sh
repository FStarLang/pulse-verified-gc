#!/usr/bin/env bash
# Stage 1 runs, in parallel.  Every run must end with an "ok: ..." line, and
# over all runs every mutant must be caught at least once.
#   run.sh [JOBS]
set -uo pipefail
B=$(cd "$(dirname "$0")/.." && pwd)/_build
T=$B/mark_par_test
L=$B/logs; rm -rf "$L"; mkdir -p "$L"
JOBS=${1:-8}

# "words heaps seed" per job; seeds differ per job.
jobs="40 hand 0
4 60 1
6 60 2
8 60 3
12 50 4
16 40 5
16 40 6
24 30 7
32 20 8
32 20 9
48 12 10
48 12 11
64 8 12
64 8 13
96 5 14
128 3 15"

echo "$jobs" | xargs -P "$JOBS" -L 1 bash -c '
  w=$0; n=$1; s=$2
  if [ "$n" = hand ]; then PS_WORDS=$w "'"$T"'" hand > "'"$L"'/hand-w$w.log" 2>&1
  else PS_WORDS=$w "'"$T"'" random $s $n > "'"$L"'/rand-w$w-s$s.log" 2>&1; fi'

fail=0
for f in "$L"/*.log; do
  if grep -q "^ok:" "$f"; then echo "ok    $(basename "$f")"; else echo "FAIL  $(basename "$f")"; fail=1; fi
done

# Totals over all runs.
cat "$L"/*.log | awk '
  /^ok:/ { h += $2; c += $4; r += $7; e += $10 }
  /^coverage:/ { s += $2; if ($7 > mx) mx = $7; o += $10; x += $13 }
  /^mutant/ { caught[$2] += $4; runs[$2] += $6 }
  END {
    printf "total: %d heaps, %d cut lists, %d model runs, %d events\n", h, c, r, e
    printf "total: %d messages sent, at most %d in transit, %d out-of-order deliveries, %d cut lists split a reachable closure from its infix header\n", s, mx, o, x
    for (m = 1; m <= 4; m++) printf "total: mutant %d caught %d of %d\n", m, caught[m], runs[m]
  }'
for m in 1 2 3 4; do
  n=$(cat "$L"/*.log | awk -v m=$m '$1 == "mutant" && $2 == m { s += $4 } END { print s + 0 }')
  if [ "$n" -eq 0 ]; then echo "FAIL  mutant $m was never caught"; fail=1; fi
done
exit $fail
