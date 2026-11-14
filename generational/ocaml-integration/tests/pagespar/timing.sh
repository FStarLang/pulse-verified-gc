#!/bin/sh
# Stage P0 timings (docs/pages-parallel-gc-design.md on sheera/pages-parallel):
# the combined prototype on the B2 runtime, interleaved by tools/proto-bench.py
# campaign (each run waits for the 1-minute load to fall below 2).
#   timing.sh TAG RUNS [PROG...]
# Run on mains power with the machine left alone:
#   caffeinate -dims tests/pagespar/timing.sh p0 3
cd "$(dirname "$0")/../../../.." || exit 1
TAG=${1:-p0}; RUNS=${2:-3}; shift 2 2>/dev/null
PROGS=${*:-"hamming bt16 bt18 livemap livegraph markbench minilight bdd fft"}
exec tools/proto-bench.py campaign "$TAG" \
  B2:seq:1 \
  B2:seq:1:VERGC_MARK=bm \
  B2:seq:1:VERGC_MARK=bm:VERGC_BM_CLEAR=bit \
  B2:seq:1:VERGC_MARK=bp \
  B2:par:2:VERGC_MARK=bp \
  B2:par:2:VERGC_MARK=bp:VERGC_CHUNKS=static \
  B2:par:4:VERGC_MARK=bp \
  B2:par:4:VERGC_MARK=bp:VERGC_CHUNKS=static \
  B2:par:4:VERGC_MARK=bp:VERGC_BP_FIX=0 \
  B2:par:4:VERGC_MARK=bp:VERGC_BP_FIX=1 \
  B2:par:4:VERGC_MARK=bp:VERGC_POOL_LOCK=spin:VERGC_CAS_COUNTER=1 \
  B2:par:4 \
  -- $PROGS --runs "$RUNS"
