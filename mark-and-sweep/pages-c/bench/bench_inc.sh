#!/bin/sh
# The incremental workloads of bench.c (inc, incL, incS), each in its own
# process, alternating the prototype, the verified build and a second copy
# of the verified build (an A/A control for noise), ROUNDS times; print the
# medians, each relative to the prototype.
#   bench_inc.sh [ROUNDS [REPS [WORKLOADS]]]
ROUNDS=${1:-9}
REPS=${2:-9}
WS=${3:-"inc incL incS"}
cd "$(dirname "$0")"
cp bench_verified bench_verified_aa
for w in $WS; do
  for i in $(seq "$ROUNDS"); do
    ./bench_proto "$REPS" "$w" | sed 's/^/proto /'
    ./bench_verified "$REPS" "$w" | sed 's/^/verified /'
    ./bench_verified_aa "$REPS" "$w" | sed 's/^/aa /'
  done
done | awk '
  { key = $1 " " $2; v[key] = v[key] " " $3; if (!($2 in seen)) { seen[$2] = 1; ws[++n] = $2 } }
  END {
    printf "%-6s %10s %10s %8s %10s %8s\n", "workload", "prototype", "verified", "diff", "A/A copy", "diff";
    for (k = 1; k <= n; k++) {
      w = ws[k]; mp = med(v["proto " w]); mv = med(v["verified " w]); ma = med(v["aa " w]);
      printf "%-8s %10.2f %10.2f %+7.1f%% %10.2f %+7.1f%%   (ns/alloc)\n", w, mp, mv, (mv / mp - 1) * 100, ma, (ma / mp - 1) * 100;
    }
  }
  function med(s,   a, n, i, j, t) {
    n = split(s, a, " "); if (n == 0) return "";
    for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) if (a[j] < a[i]) { t = a[i]; a[i] = a[j]; a[j] = t }
    return a[int((n + 1) / 2)];
  }'
rm -f bench_verified_aa
