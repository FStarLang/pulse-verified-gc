#!/bin/sh
# The promotion workloads of bench_promo.c, each in its own process, the
# builds alternating within each round, ROUNDS times; print the medians.
#   redirect   the reference: akhil's Cheney, allocate sent to the page
#              allocator (alloc_ph), unverified
#   aa         a second copy of redirect (an A/A control for noise)
#   white      redirect with sheera/pages-runtime's glue (alloc_white | tag)
#   pages      the verified promotion
#   main       main's design: the same Cheney with first-fit
# Table 1 is relative to redirect (the 5% rule); table 2, the design-level
# comparison, relative to main.  Each workload runs on the fresh heap, then
# on the steady one.
#   bench_promo.sh [ROUNDS [REPS [WORKLOADS [HEAPS]]]]
ROUNDS=${1:-9}
REPS=${2:-7}
WS=${3:-"list tree mixed half infix"}
HS=${4:-"fresh steady"}
cd "$(dirname "$0")"
cp bench_promo_redirect bench_promo_aa
for h in $HS; do
for w in $WS; do
  for i in $(seq "$ROUNDS"); do
    ./bench_promo_redirect "$REPS" "$w" "$h" | sed 's/^/redirect /'
    ./bench_promo_pages "$REPS" "$w" "$h" | sed 's/^/pages /'
    ./bench_promo_aa "$REPS" "$w" "$h" | sed 's/^/aa /'
    ./bench_promo_redirect_white "$REPS" "$w" "$h" | sed 's/^/white /'
    ./bench_promo_main "$REPS" "$w" "$h" | sed 's/^/main /'
  done
done
done | awk '
  { key = $1 " " $2; v[key] = v[key] " " $3; if (!($2 in seen)) { seen[$2] = 1; ws[++n] = $2 } }
  END {
    print "Same algorithm, same page allocator (ns/promoted object; diff vs redirect):";
    printf "%-8s %9s %9s %8s %9s %8s %9s %8s\n", "workload", "redirect", "pages", "diff", "A/A", "diff", "white", "diff";
    for (k = 1; k <= n; k++) {
      w = ws[k]; r = med(v["redirect " w]); p = med(v["pages " w]); a = med(v["aa " w]); x = med(v["white " w]);
      printf "%-8s %9.2f %9.2f %+7.1f%% %9.2f %+7.1f%% %9.2f %+7.1f%%\n", w, r, p, (p / r - 1) * 100, a, (a / r - 1) * 100, x, (x / r - 1) * 100;
    }
    print "";
    print "Design level, against first-fit (ns/promoted object; diff vs main):";
    printf "%-8s %9s %9s %8s %9s %8s\n", "workload", "main", "pages", "diff", "redirect", "diff";
    for (k = 1; k <= n; k++) {
      w = ws[k]; m = med(v["main " w]); p = med(v["pages " w]); r = med(v["redirect " w]);
      printf "%-8s %9.2f %9.2f %+7.1f%% %9.2f %+7.1f%%\n", w, m, p, (p / m - 1) * 100, r, (r / m - 1) * 100;
    }
  }
  function med(s,   a, n, i, j, t) {
    n = split(s, a, " "); if (n == 0) return "";
    for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) if (a[j] < a[i]) { t = a[i]; a[i] = a[j]; a[j] = t }
    return a[int((n + 1) / 2)];
  }'
rm -f bench_promo_aa
