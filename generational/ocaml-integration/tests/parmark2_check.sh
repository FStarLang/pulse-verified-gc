#!/usr/bin/env bash
# par_mark2.c (VGC_PAR_VARIANT=AP|AS|BP|BS), correctness check, as
# parmark_check.sh: every program runs once on the unchanged sequential path,
# then for each variant, k and setting with VGC_PAR_MARK_CHECK=1, which
# re-runs the verified sequential mark at every major collection and aborts
# on any differing header (B: on any differing bitmap mark, and unless the
# bitmap sweep leaves the heap the verified sweep leaves).  Each run must exit
# 0, print the reference stdout, check at least one collection, and (with a
# TSan runtime) produce no ThreadSanitizer report.  Settings: default; small
# chunks and packets (CHUNK=4, PKT=4: splitting, sharing and stealing all the
# time); CHUNK=1, PKT=1.
#
#   ./parmark2_check.sh [OCAMLRUN] [KS] [VARIANTS] [EXTRA_ENV...]
set -u
cd "$(dirname "$0")"
R=${1:-../ocaml-4.14-verified-gen/runtime/ocamlrun}
KS=${2:-"1 2 4 8"}
VS=${3:-"AP AS BP BS"}
shift 3 2>/dev/null || shift $#
EXTRA=("$@")
REF=../ocaml-4.14-verified-gen/runtime/ocamlrun
O=${OUT:-/tmp/parmark2_check}
SETS=${SETS:-"default CHUNK=4,PKT=4 CHUNK=1,PKT=1"}
mkdir -p "$O"
mask() { sed -E 's/[0-9a-f]{9,}/ADDR/g' "$1"; }
fail=0; n=0
while IFS="|" read -r p w a; do
  MIN_EXPANSION_WORDSIZE=$w $REF $p.byte $a >"$O/$p.ref" 2>"$O/$p.referr" || { echo "$p: reference run failed"; fail=1; continue; }
  for v in $VS; do
    for k in $KS; do
      for c in $SETS; do
        envs=(VGC_PAR_VARIANT=$v VGC_PAR_MARK=$k VGC_PAR_MARK_CHECK=1 VGC_MARK_STATS=1 MIN_EXPANSION_WORDSIZE=$w)
        if [ "$c" != default ]; then
          IFS=, read -ra kv <<<"$c"; for x in "${kv[@]}"; do envs+=("VGC_PAR_$x"); done
        fi
        tag="$p-$v-k$k-${c//[,=]/}"
        env "${envs[@]}" "${EXTRA[@]}" $R $p.byte $a >"$O/$tag.out" 2>"$O/$tag.err"; rc=$?
        same=$( [ "$(mask "$O/$tag.out")" = "$(mask "$O/$p.ref")" ] && echo same || echo DIFF)
        chk=$(grep -a '^vgc-par-mark-check:' "$O/$tag.err" | sed -E 's/^vgc-par-mark-check: ([0-9]+) collections.*/\1/')
        sw=$(grep -ac 'bitmap sweep equal' "$O/$tag.err")
        st=$(grep -a 'steal_try' "$O/$tag.err" | sed -E 's/.*(steal_ok [0-9]+).*(pkt_pub [0-9]+).*(pkt_share [0-9]+).*/\1 \2 \3/')
        cf=$(grep -a 'cas_fail' "$O/$tag.err" | sed -E 's/.*(cas_fail [0-9]+).*/\1/')
        ts=$(grep -ac 'WARNING: ThreadSanitizer' "$O/$tag.err")
        n=$((n+1))
        line="$tag: rc $rc, stdout $same, checked ${chk:-0}, sweep-checked $sw, $st, $cf, tsan $ts"
        if [ $rc -ne 0 ] || [ "$same" != same ] || [ -z "$chk" ] || [ "$chk" -eq 0 ] || [ "$ts" -ne 0 ] ||
           { [ "${v:0:1}" = B ] && [ "$sw" -eq 0 ]; }; then
          echo "FAIL $line"; fail=1
        else
          echo "ok   $line"
        fi
      done
    done
  done
done <<LIST
${PROGS:-binarytrees|1000000|10
livemap|2000000|100000 1
livegraph|3200000|100000 4 4
count_change|2000000|100
infix_closures|300000|
no_scan|4000000|
make_vect_barrier|4000000|
alloc_exact_promotion|4194304|4194304
gc_explicit|4000000|
gray_overflow|2000000|2000000
fasta|300000|100000}
LIST
[ $fail -eq 0 ] && echo "ALL OK ($n runs)" || { echo "SOME FAILED ($n runs)"; exit 1; }
