#!/usr/bin/env bash
# Stage 3 runs, in parallel.  Every run must end with an "ok: ..." line, and
# over all runs every mutant must be caught at least once.
#   run.sh [JOBS]
set -uo pipefail
B=$(cd "$(dirname "$0")/.." && pwd)/_build
T=$B/mark_par2_test
L=$B/logs2; rm -rf "$L"; mkdir -p "$L"
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
  /^coverage:/ { s += $2; d += $4; sf += $6; su += $13; fw += $18 }
  /^rounds:/ { fx += $2; if ($9 > mr) mr = $9; x += $14 }
  /^mutant/ { caught[$2] += $4; runs[$2] += $6; hp[$2] += $8; stk[$2] += $10; wr[$2] += $12; rd[$2] += $14; cn[$2] += $16 }
  /^checks:/ { sc += $2; z += $5 }
  /^idle:/ { sp += $2; lm += $9; is += $15 }
  END {
    printf "total: %d heaps, %d cut lists, %d model runs, %d events\n", h, c, r, e
    printf "total: %d sends, %d dropped, %d greys left off a full stack, %d setups filled a stack, %d forwards\n", s, d, sf, su, fw
    printf "total: %d fix-ups started a round, at most %d rounds in a run, %d cut lists split a reachable closure from its infix header\n", fx, mr, x
    printf "total: %d read checks, %d worker steps at count 0\n", sc, z
    printf "total: %d spin steps, %d Idle steps found a message had come in, %d Idle steps read 0 and stopped\n", sp, lm, is
    for (m = 1; m <= 6; m++) printf "total: mutant %d caught %d of %d (heap %d, stuck %d, write %d, read %d, count %d)\n", m, caught[m], runs[m], hp[m], stk[m], wr[m], rd[m], cn[m]
  }'
for m in 1 2 3 4 5 6; do
  n=$(cat "$L"/*.log | awk -v m=$m '$1 == "mutant" && $2 == m { s += $4 } END { print s + 0 }')
  if [ "$n" -eq 0 ]; then echo "FAIL  mutant $m was never caught"; fail=1; fi
done
exit $fail
