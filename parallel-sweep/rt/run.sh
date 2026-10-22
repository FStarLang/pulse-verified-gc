#!/usr/bin/env bash
# Runs test programs on a runtime variant with the parallel sweep on, and on the
# tree's default runtime with it off, and checks for each program:
#   - both exit 0, with the same stdout once heap addresses are masked;
#   - check variant: the bridge's summary line, with at least one collection
#     compared (a difference aborts the run).
#
#   ./run.sh byte|native VARIANT THREADS [K]
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
MODE=$1; V=$2; N=$3; K=${4:-}
T=$HERE/../../generational/ocaml-integration/tests
TREE=$HERE/../../generational/ocaml-integration/ocaml-4.14-verified-gen
OPT=$HERE/../../generational/ocaml-integration/ocaml-4.14-unchanged/_install/bin/ocamlopt
B=$HERE/../_build/rt
O=$B/runs/$MODE-$V-t$N-k${K:-def}
mkdir -p "$O"
if [ "$MODE" = native ]; then   # link each program against both libasmrun.a
  mkdir -p "$B/native/ref" "$B/native/$V"
  cp "$TREE/runtime/libasmrun.a" "$B/native/ref/"
  cp "$B/$V/libasmrun.a" "$B/native/$V/"
  for p in infix_closures no_scan make_vect_barrier count_change binarytrees alloc_exact_promotion; do
    for d in ref $V; do
      ( cd "$B/native/$d" && cp "$T/$p.ml" . && "$OPT" -I . -o "$p" "$p.ml" ) >/dev/null 2>&1 \
        || { echo "native link of $p ($d) failed"; exit 1; }
    done
  done
  ref() { "$B/native/ref/$1" "${@:2}"; }
  run() { "$B/native/$V/$1" "${@:2}"; }
else
  ref() { "$TREE/runtime/ocamlrun" "$T/$1.byte" "${@:2}"; }
  run() { "$B/$V/ocamlrun" "$T/$1.byte" "${@:2}"; }
fi
mask() { sed -E 's/[0-9a-f]{9,}/ADDR/g' "$1"; }
fail=0
# program  major-heap-words  args   (Spike 3's sizes; they force major collections.
# nursery_no_scan_interior is left out: it does no major collection.)
while read -r p w a; do
  [ "$MODE" = native ] && [ "$p" = fasta ] && continue   # see SPIKE.md, Spike 3
  cd "$T"
  MIN_EXPANSION_WORDSIZE=$w ref $p $a >"$O/$p.ref" 2>"$O/$p.referr"; rv=$?
  export MIN_EXPANSION_WORDSIZE=$w VERGC_PAR_SWEEP_THREADS=$N
  if [ -n "$K" ]; then export VERGC_PAR_SWEEP_K=$K; fi
  run $p $a >"$O/$p.out" 2>"$O/$p.err"; rr=$?
  unset MIN_EXPANSION_WORDSIZE VERGC_PAR_SWEEP_THREADS VERGC_PAR_SWEEP_K
  cd "$HERE"
  same=$( [ "$(mask "$O/$p.out")" = "$(mask "$O/$p.ref")" ] && echo same || echo DIFF)
  summ=$(grep -a '^par-sweep check:' "$O/$p.err" | tail -1)
  n=$(echo "$summ" | sed -nE 's/^par-sweep check: ([0-9]+) collections.*/\1/p')
  echo "$p: rc $rv/$rr, stdout $same, ${summ:-no summary}"
  if [ $rv -ne 0 ] || [ $rr -ne 0 ] || [ "$same" != same ]; then fail=1; fi
  if [ "$V" = check ] && { [ -z "$n" ] || [ "$n" -eq 0 ]; }; then fail=1; fi
done <<'LIST'
infix_closures 300000
no_scan 4000000
make_vect_barrier 4000000
alloc_exact_promotion 4194304 4194304
fasta 300000 100000
count_change 2000000 100
binarytrees 1000000 10
LIST
[ $fail -eq 0 ] && echo "ok: all programs ($MODE, $V, $N threads, k ${K:-default})" \
  || { echo "FAIL ($MODE, $V, $N threads, k ${K:-default})"; exit 1; }
