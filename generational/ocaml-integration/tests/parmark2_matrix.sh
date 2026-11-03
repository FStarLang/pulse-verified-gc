#!/usr/bin/env bash
# The measurement of docs/parallel-mark-prototype2.md.  Per benchmark: the
# sequential mark (timed, with PR #40's rescan skip), the four variants of
# par_mark2.c (AP AS BP BS) and par_mark.c's tuned ownership variant (O:
# deduplicated sends, batching, local counting, live cuts), at k = 1, 2, 4,
# 8; RUNS runs each (default 3), interleaved by run so that a slow spell of
# the machine does not fall on one configuration.  Then one profiled run
# (VGC_PAR_PROF=1) of each variant at PROF_KS (default 2 4 8) for the
# breakdown of worker time.
#   ./parmark2_matrix.sh OUT_PREFIX [RUNS] [BENCH...]
# BENCH defaults to bt16 bt18 livemap livegraph and four Sandmark programs.
set -u
cd "$(dirname "$0")"
OUT=$1; RUNS=${2:-3}; shift 2 2>/dev/null || shift $#
if [ $# -gt 0 ]; then BENCHES="$*"
else
  # The Sandmark programs whose sequential mark is at least 1% of the run
  # and that do at least 3 major collections (docs/parallel-mark-prototype2.md).
  BENCHES="bt16 bt18 livemap livegraph sm:markbench sm:minilight sm:bdd sm:fft"
fi
KS=${KS:-"1 2 4 8"}
PROF_KS=${PROF_KS:-"2 4 8"}
O_ENV="VGC_PAR_Q=1048576,VGC_PAR_DEDUP=4096,VGC_PAR_BATCH=128,VGC_PAR_LOCAL=1,VGC_PAR_CUT=live"
cfg() {   # cfg VARIANT K
  if [ "$1" = O ]; then echo "O-k$2:VGC_PAR_MARK=$2,$O_ENV"
  else echo "$1-k$2:VGC_PAR_MARK=$2,VGC_PAR_VARIANT=$1"; fi
}
for b in $BENCHES; do
  cfgs=("seq:")
  for v in AP AS BP BS O; do for k in $KS; do cfgs+=("$(cfg $v $k)"); done; done
  for r in $(seq 1 "$RUNS"); do
    TMO=${TMO:-1800} ./parmark2_bench.sh "$OUT.jsonl" 1 "$b" "${cfgs[@]}"
  done
  p=()
  for v in AP AS BP BS O; do for k in $PROF_KS; do c=$(cfg $v $k); p+=("${c%%:*}:${c#*:},VGC_PAR_PROF=1"); done; done
  TMO=${TMO:-1800} ./parmark2_bench.sh "$OUT.prof.jsonl" 1 "$b" "${p[@]}"
done
echo ALL-DONE
