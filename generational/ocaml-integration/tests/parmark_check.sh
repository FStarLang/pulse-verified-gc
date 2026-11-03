#!/usr/bin/env bash
# Prototype parallel mark (verified_gc/par_mark.c), correctness check.
# For each program, run it once on the sequential path (VGC_PAR_MARK unset)
# and then under VGC_PAR_MARK=k with VGC_PAR_MARK_CHECK=1 for every k and
# capacity setting below.  The check mode re-runs the verified sequential
# mark at every major collection and aborts on any differing header.  Each
# run must exit 0, print the same stdout as the sequential run, and report at
# least one checked collection; with a TSan runtime, no ThreadSanitizer report.
#
#   ./parmark_check.sh [OCAMLRUN] [KS] [EXTRA_ENV...]
set -u
cd "$(dirname "$0")"
R=${1:-../ocaml-4.14-verified-gen/runtime/ocamlrun}
KS=${2:-"1 2 4 8"}
shift 2 2>/dev/null || shift $#
EXTRA=("$@")
REF=../ocaml-4.14-verified-gen/runtime/ocamlrun
O=${OUT:-/tmp/parmark_check}
mkdir -p "$O"
# S/Q settings per program (last column, ';'-separated): default, small
# (overflow and fix-up rounds), tiny (S=1, Q=0: a fix-up round per object or
# so, affordable only on small heaps).  CAPS overrides them all.
mask() { sed -E 's/[0-9a-f]{9,}/ADDR/g' "$1"; }   # heap addresses differ between runs
fail=0; n=0
while IFS="|" read -r p w a caps; do
  caps=${CAPS:-${caps//;/ }}
  MIN_EXPANSION_WORDSIZE=$w $REF $p.byte $a >"$O/$p.ref" 2>"$O/$p.referr" || { echo "$p: reference run failed"; fail=1; continue; }
  for k in $KS; do
    for c in $caps; do
      envs=(VGC_PAR_MARK=$k VGC_PAR_MARK_CHECK=1 VGC_MARK_STATS=1 MIN_EXPANSION_WORDSIZE=$w)
      if [ "$c" != default ]; then
        IFS=, read -ra kv <<<"$c"; for x in "${kv[@]}"; do envs+=("VGC_PAR_$x"); done
      fi
      tag="$p-k$k-${c//[,=]/}"
      env "${envs[@]}" "${EXTRA[@]}" $R $p.byte $a >"$O/$tag.out" 2>"$O/$tag.err"; rc=$?
      same=$( [ "$(mask "$O/$tag.out")" = "$(mask "$O/$p.ref")" ] && echo same || echo DIFF)
      chk=$(grep -a '^vgc-par-mark-check:' "$O/$tag.err" | sed -E 's/^vgc-par-mark-check: ([0-9]+) collections.*/\1/')
      st=$(grep -a 'rounds' "$O/$tag.err" | sed -E 's/.*(rounds [0-9]+ fixups [0-9]+).*/\1/')
      dr=$(grep -a 'dropped' "$O/$tag.err" | sed -E 's/.*(dropped [0-9]+ stack_ovf [0-9]+).*/\1/')
      ts=$(grep -ac 'WARNING: ThreadSanitizer' "$O/$tag.err")
      n=$((n+1))
      line="$tag: rc $rc, stdout $same, checked ${chk:-0}, $st, $dr, tsan $ts"
      if [ $rc -ne 0 ] || [ "$same" != same ] || [ -z "$chk" ] || [ "$chk" -eq 0 ] || [ "$ts" -ne 0 ]; then
        echo "FAIL $line"; fail=1
      else
        echo "ok   $line"
      fi
    done
  done
done <<'LIST'
binarytrees|1000000|10|default;S=256,Q=64;S=16,Q=4
livemap|2000000|100000 1|default;S=256,Q=64;S=16,Q=4
livegraph|3200000|100000 4 4|default;S=256,Q=64;S=16,Q=4
count_change|2000000|100|default;S=256,Q=64;S=16,Q=4
infix_closures|300000||default;S=16,Q=4;S=1,Q=0
no_scan|4000000||default;S=16,Q=4;S=1,Q=0
make_vect_barrier|4000000||default;S=256,Q=64
alloc_exact_promotion|4194304|4194304|default;S=256,Q=64
gc_explicit|4000000||default;S=16,Q=4;S=1,Q=0
fasta|300000|100000|default;S=16,Q=4
LIST
[ $fail -eq 0 ] && echo "ALL OK ($n runs)" || { echo "SOME FAILED ($n runs)"; exit 1; }
