#!/bin/sh
# Stage P0 checks (docs/pages-parallel-gc-design.md on sheera/pages-parallel):
# every configuration of the combined prototype, on the B2-check runtime,
# on the nine programs.  Each run compares the bitmap with the verified mark
# and the sweep with the verified sweep at every major collection, and the
# program's output with stock OCaml's.  Usage: check_matrix.sh [PROG...]
cd "$(dirname "$0")/../../../.." || exit 1
PROGS=${*:-"minilight bdd hamming livegraph livemap fft bt16 markbench bt18"}
CFGS="B2-check:seq:1
B2-check:par:4
B2-check:seq:1:VERGC_MARK=bm
B2-check:seq:1:VERGC_MARK=bm:VERGC_BM_CLEAR=bit
B2-check:seq:1:VERGC_MARK=bp
B2-check:par:2:VERGC_MARK=bp
B2-check:par:4:VERGC_MARK=bp
B2-check:par:4:VERGC_MARK=bp:VERGC_CHUNKS=static
B2-check:par:4:VERGC_MARK=bp:VERGC_BP_FIX=0
B2-check:par:4:VERGC_MARK=bp:VERGC_POOL_LOCK=spin:VERGC_CAS_COUNTER=1
B2-check:par:4:VERGC_MARK=bp:VERGC_PKT=4:VERGC_CHUNK=4
B2-check:par:4:VERGC_MARK=bp:VERGC_PKT=2:VERGC_CHUNK=1:VERGC_BM_CLEAR=bit"
for p in $PROGS; do
  echo "$CFGS" | while read -r c; do
    tools/proto-bench.py run "$c" "$p" --runs 1 --tag check 2>&1 | tail -1
  done
done
