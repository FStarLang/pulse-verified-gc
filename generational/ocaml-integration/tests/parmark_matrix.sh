#!/usr/bin/env bash
# The measurement matrix of docs/parallel-mark-prototype.md: per benchmark,
# the unchanged sequential path, the sequential mark timed, the design as
# written (Q=4096, S = sequential gray-stack capacity) and a tuned variant,
# each at k = 1, 2, 4, 8.  RUNS runs each (default 5).
#   ./parmark_matrix.sh OUT.csv [RUNS] [BENCH...]
set -u
cd "$(dirname "$0")"
OUT=$1; RUNS=${2:-5}; shift 2 2>/dev/null || shift $#
BENCHES=${*:-"livegraph livemap bt16 bt18"}
TUNED="VGC_PAR_Q=1048576,VGC_PAR_DEDUP=4096,VGC_PAR_BATCH=128,VGC_PAR_LOCAL=1"
for b in $BENCHES; do
  cfgs=("unset:unset" "seq:")
  for k in 1 2 4 8; do cfgs+=("design-k$k:VGC_PAR_MARK=$k"); done
  for k in 1 2 4 8; do cfgs+=("tuned-k$k:VGC_PAR_MARK=$k,$TUNED"); done
  ./parmark_bench.sh "$OUT" "$RUNS" "$b" "${cfgs[@]}"
done
