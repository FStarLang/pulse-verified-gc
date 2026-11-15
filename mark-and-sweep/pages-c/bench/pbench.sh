#!/bin/sh
# The parallel sweep (psweep10/50/90) at 1, 2 and 4 threads: the prototype
# and the verified build, each run in its own process, alternately, ROUNDS
# times; prints the medians.   pbench.sh [ROUNDS [REPS]]
# PSTATIC=0 runs the prototype with dynamic chunks (its default); the
# verified sweep's chunks are static.
ROUNDS=${1:-5}
REPS=${2:-15}
cd "$(dirname "$0")"
for k in 1 2 4; do
  for i in $(seq "$ROUNDS"); do
    VERGC_PSTATIC=${PSTATIC:-1} ./bench_pproto "$REPS" psweep "$k" | sed 's/^/proto /'
    ./bench_pverified "$REPS" psweep "$k" | sed 's/^/verified /'
  done
done | awk '
  { key = $1 " " $2; v[key] = v[key] " " $3; if (!($2 in seen)) { seen[$2] = 1; order[++n] = $2 } }
  END {
    printf "%-14s %10s %10s %8s\n", "workload", "prototype", "verified", "diff";
    for (i = 1; i <= n; i++) {
      w = order[i]; mp = med(v["proto " w]); mv = med(v["verified " w]);
      printf "%-14s %10.3f %10.3f %+7.1f%%  (ms/sweep)\n", w, mp, mv, (mv / mp - 1) * 100;
    }
  }
  function med(s,   a, n, i, j, t) {
    n = split(s, a, " ");
    for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) if (a[j] < a[i]) { t = a[i]; a[i] = a[j]; a[j] = t }
    return a[int((n + 1) / 2)];
  }'
