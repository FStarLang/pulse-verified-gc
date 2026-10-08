#!/usr/bin/env bash
# Stage B runs, in parallel.  Every run must end "ok: ...".
#   run.sh [JOBS]
set -uo pipefail
B=$(cd "$(dirname "$0")/.." && pwd)/_build
T=$B/sweep_par_test
L=$B/logs; rm -rf "$L"; mkdir -p "$L"
JOBS=${1:-8}

# "words heaps seed" per job; seeds differ per job.
jobs="40 hand 0
2 30 1
3 60 2
4 100 3
5 100 4
6 100 5
8 80 6
8 80 7
10 60 8
12 50 9
16 40 10
16 40 11
20 30 12
24 25 13
32 20 14
32 20 15
48 12 16
64 7 17
96 8 18"

echo "$jobs" | xargs -P "$JOBS" -L 1 bash -c '
  w=$0; n=$1; s=$2
  if [ "$n" = hand ]; then PS_WORDS=$w "'"$T"'" hand > "'"$L"'/hand-w$w.log" 2>&1
  else PS_WORDS=$w "'"$T"'" random $s $n > "'"$L"'/rand-w$w-s$s.log" 2>&1; fi'

fail=0
for f in "$L"/*.log; do
  if grep -q "^ok:" "$f"; then echo "ok    $(basename "$f")"; else echo "FAIL  $(basename "$f")"; fail=1; fi
done
exit $fail
