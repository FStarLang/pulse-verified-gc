#!/usr/bin/env bash
# Short measurement: the sequential mark (timed) and the tuned variant
# (deduplicated sends, batching, local counting, live cuts; Q = 2^20) at
# k = 1, 2, 4, 8, on binarytrees 16 and livegraph, 3 runs each; then one
# run of each tuned configuration with VGC_PAR_PROF=1 for the breakdown.
set -u
cd "$(dirname "$0")"
O=results_parmark/short.csv
TUNED="VGC_PAR_Q=1048576,VGC_PAR_DEDUP=4096,VGC_PAR_BATCH=128,VGC_PAR_LOCAL=1,VGC_PAR_CUT=live"
for b in bt16 livegraph; do
  cfg=("seq:"); for k in 1 2 4 8; do cfg+=("tuned-k$k:VGC_PAR_MARK=$k,$TUNED"); done
  TMO=1800 ./parmark_bench.sh $O 3 $b "${cfg[@]}"
  p=(); for k in 1 2 4 8; do p+=("prof-k$k:VGC_PAR_MARK=$k,$TUNED,VGC_PAR_PROF=1"); done
  TMO=1800 ./parmark_bench.sh $O 1 $b "${p[@]}"
done
echo ALL-DONE
