#!/bin/sh
# Run every workload of bench.c in its own process, alternating the
# prototype and the verified build, ROUNDS times; print each one's results
# and the median over the rounds.
#   bench.sh [ROUNDS [REPS]]
ROUNDS=${1:-5}
REPS=${2:-15}
cd "$(dirname "$0")"
for w in small mixed large sweep realloc reallocS; do
  for i in $(seq "$ROUNDS"); do
    ./bench_proto "$REPS" "$w" | sed 's/^/proto /'
    ./bench_verified "$REPS" "$w" | sed 's/^/verified /'
  done
done | awk '
  { key = $1 " " $2; v[key] = v[key] " " $3; unit[$2] = $4; order[$2] = ++n }
  END {
    split("small mixed large sweep10 sweep50 sweep90 realloc reallocS", ws, " ");
    printf "%-9s %12s %12s %8s\n", "workload", "prototype", "verified", "diff";
    for (k = 1; k <= 8; k++) {
      w = ws[k];
      mp = med(v["proto " w]); mv = med(v["verified " w]);
      if (mp == "") continue;
      printf "%-9s %12.3f %12.3f %+7.1f%%  (%s)\n", w, mp, mv, (mv / mp - 1) * 100, unit[w];
    }
  }
  function med(s,   a, n, i, j, t) {
    n = split(s, a, " "); if (n == 0) return "";
    for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) if (a[j] < a[i]) { t = a[i]; a[i] = a[j]; a[j] = t }
    return a[int((n + 1) / 2)];
  }'
