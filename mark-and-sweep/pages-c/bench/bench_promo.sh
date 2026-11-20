#!/bin/sh
# The promotion workloads of bench_promo.c, each in its own process,
# alternating main's build, ours and a second copy of ours (an A/A control
# for noise), ROUNDS times; print the medians, each relative to main's.
# Each workload runs on the fresh heap, then on the steady one (bench_promo.c).
#   bench_promo.sh [ROUNDS [REPS [WORKLOADS [HEAPS]]]]
ROUNDS=${1:-9}
REPS=${2:-7}
WS=${3:-"list tree mixed half infix"}
HS=${4:-"fresh steady"}
cd "$(dirname "$0")"
cp bench_promo_pages bench_promo_aa
for h in $HS; do
for w in $WS; do
  for i in $(seq "$ROUNDS"); do
    ./bench_promo_main "$REPS" "$w" "$h" | sed 's/^/main /'
    ./bench_promo_pages "$REPS" "$w" "$h" | sed 's/^/pages /'
    ./bench_promo_aa "$REPS" "$w" "$h" | sed 's/^/aa /'
  done
done
done | awk '
  { key = $1 " " $2; v[key] = v[key] " " $3; if (!($2 in seen)) { seen[$2] = 1; ws[++n] = $2 } }
  END {
    printf "%-8s %10s %10s %8s %10s %8s\n", "workload", "main", "pages", "diff", "A/A copy", "diff";
    for (k = 1; k <= n; k++) {
      w = ws[k]; mm = med(v["main " w]); mp = med(v["pages " w]); ma = med(v["aa " w]);
      printf "%-8s %10.2f %10.2f %+7.1f%% %10.2f %+7.1f%%   (ns/promoted object)\n", w, mm, mp, (mp / mm - 1) * 100, ma, (ma / mm - 1) * 100;
    }
  }
  function med(s,   a, n, i, j, t) {
    n = split(s, a, " "); if (n == 0) return "";
    for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) if (a[j] < a[i]) { t = a[i]; a[i] = a[j]; a[j] = t }
    return a[int((n + 1) / 2)];
  }'
rm -f bench_promo_aa
