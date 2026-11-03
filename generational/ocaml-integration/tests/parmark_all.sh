#!/usr/bin/env bash
# The full measurement of docs/parallel-mark-prototype.md.  Every benchmark
# (binarytrees 16 and 18, livegraph, livemap): the unchanged sequential
# path, the sequential mark timed, and the tuned variant at k = 1, 2, 4, 8,
# 5 runs each.  The design as written (k = 1, 2, 4, 8) runs once, on
# binarytrees 16 and livegraph only: it takes minutes per run.
set -u
cd "$(dirname "$0")"
O=results_parmark/matrix.csv
TUNED="VGC_PAR_Q=1048576,VGC_PAR_DEDUP=4096,VGC_PAR_BATCH=128,VGC_PAR_LOCAL=1"
for b in bt16 livegraph livemap bt18; do
  cfg=("unset:unset" "seq:")
  for k in 1 2 4 8; do cfg+=("tuned-k$k:VGC_PAR_MARK=$k,$TUNED"); done
  TMO=1800 ./parmark_bench.sh $O 5 $b "${cfg[@]}"
  case $b in
    bt16|livegraph)
      d=(); for k in 1 2 4 8; do d+=("design-k$k:VGC_PAR_MARK=$k"); done
      TMO=1800 ./parmark_bench.sh $O 1 $b "${d[@]}" ;;
  esac
done
echo ALL-DONE
