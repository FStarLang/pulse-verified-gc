#!/usr/bin/env bash
# Prototype parallel mark (verified_gc/par_mark.c), timing runs.
#   ./parmark_bench.sh OUT.csv RUNS BENCH CONFIG...
# BENCH is one of bt16 bt18 livemap livegraph.  CONFIG is a name and a
# comma-separated list of VGC_* settings, as name:VAR=val,VAR=val, or
# "unset" for the unchanged sequential path (no statistics).  Each run
# appends one CSV row: wall time (seconds) and the vgc-mark-stats counters.
set -u
cd "$(dirname "$0")"
OUT=$1; RUNS=$2; B=$3; shift 3
R=${OCAMLRUN:-../ocaml-4.14-verified-gen/runtime/ocamlrun}
case $B in
  bt16)     W=67108864;  P="binarytrees.byte 16" ;;
  bt18)     W=536870912; P="binarytrees.byte 18" ;;
  livemap)  W=25165824;  P="livemap.byte 1000000 1" ;;
  livegraph) W=16777216; P="livegraph.byte 1000000 4 4" ;;
  *) echo "unknown bench $B"; exit 1 ;;
esac
[ -f "$OUT" ] || echo "bench,config,run,wall_s,majors,mark_us,seq_inner_us,seq_rescan_us,rounds,fixups,setup_us,round_us,fixup_us,create_us,start_lat_us,join_lat_us,roots_pushed,fixup_pushed,scanned,sent,dropped,stack_ovf,idle_spins,deduped,flushes,cut_us,per_worker_scanned" >"$OUT"
num() { grep -aoE "(^| )$1 [0-9.]+" "$2" | head -1 | awk '{print $2}'; }
for cfg in "$@"; do
  name=${cfg%%:*}; vars=${cfg#*:}
  envs=(MIN_EXPANSION_WORDSIZE=$W)
  if [ "$vars" != unset ]; then
    envs+=(VGC_MARK_STATS=1)
    IFS=, read -ra kv <<<"$vars"; for x in "${kv[@]}"; do [ -n "$x" ] && envs+=("$x"); done
  fi
  for r in $(seq 1 "$RUNS"); do
    e=$(mktemp)
    wall=$(perl -MTime::HiRes=time -e '$t=time; open(STDOUT,">/dev/null"); open(STDERR,">'"$e"'"); $rc=system(@ARGV); printf STDOUT ""; open(T,">&3"); printf T "%.3f %d\n", time-$t, $rc>>8' -- env "${envs[@]}" $R $P 3>&1)
    rc=${wall#* }; wall=${wall% *}
    if [ "$rc" != 0 ]; then echo "$B $name run $r: exit $rc" >&2; cat "$e" >&2; fi
    pw=$(grep -a 'per_worker_scanned' "$e" | sed 's/.*per_worker_scanned //' | tr ' ' '/')
    row="$B,$name,$r,$wall"
    for f in majors mark_us inner_us rescan_us rounds fixups setup_us round_us fixup_us create_us start_lat_us join_lat_us roots_pushed fixup_pushed scanned sent dropped stack_ovf idle_spins deduped flushes cut_us; do
      row="$row,$(num $f "$e")"
    done
    echo "$row,$pw" >>"$OUT"
    echo "$row" >&2
    rm -f "$e"
  done
done
