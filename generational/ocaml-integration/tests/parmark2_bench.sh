#!/usr/bin/env bash
# Timing runs for docs/parallel-mark-prototype2.md.
#   ./parmark2_bench.sh OUT.jsonl RUNS BENCH CONFIG...
# BENCH: bt16 bt18 livemap livegraph, or sm:<name> for a line of
# sandmark/benchmarks.txt (name|binary|heap_words|args|notes; run in sandmark/bin).
# CONFIG: name:VAR=val,VAR=val (VGC_MARK_STATS=1 is always added).  Each run
# appends one JSON object: bench, config, run, wall_s, rc, load1 before the
# run, and every "key number" pair of the vgc-* statistics lines (the first
# occurrence of each key).  Before each run it waits until no proof, model
# test or check job is running and the 1-minute load is at most LOADMAX
# (default 8; this machine idles near 4), and TMO=seconds bounds a run.
set -u
cd "$(dirname "$0")"
OUT=$1; RUNS=$2; B=$3; shift 3
R=${OCAMLRUN:-$PWD/../ocaml-4.14-verified-gen/runtime/ocamlrun}
DIR=.
case $B in
  bt16)      W=67108864;  P="binarytrees.byte 16" ;;
  bt18)      W=536870912; P="binarytrees.byte 18" ;;
  livemap)   W=25165824;  P="livemap.byte 1000000 1" ;;
  livegraph) W=16777216;  P="livegraph.byte 1000000 4 4" ;;
  sm:*)
    line=$(grep -E "^${B#sm:}\|" sandmark/benchmarks.txt | head -1)
    [ -n "$line" ] || { echo "unknown sandmark bench ${B#sm:}"; exit 1; }
    IFS="|" read -r n bin W A _ <<<"$line"
    P="$bin.byte $A"; DIR=sandmark/bin ;;
  *) echo "unknown bench $B"; exit 1 ;;
esac
for cfg in "$@"; do
  name=${cfg%%:*}; vars=${cfg#*:}
  envs=(MIN_EXPANSION_WORDSIZE=$W VGC_MARK_STATS=1)
  IFS=, read -ra kv <<<"$vars"; for x in "${kv[@]}"; do [ -n "$x" ] && envs+=("$x"); done
  for r in $(seq 1 "$RUNS"); do
    while ps aux | grep -E 'fstar.exe|z3-|z3 |parmark_check|parmark2_check|mark_par2_test' | grep -v grep >/dev/null; do sleep 20; done
    while [ "$(sysctl -n vm.loadavg | awk -v m="${LOADMAX:-8}" '{print ($2 > m)}')" = 1 ]; do sleep 10; done
    e=$(mktemp)
    load=$(sysctl -n vm.loadavg | awk '{print $2}')
    res=$(cd "$DIR" && perl -MTime::HiRes=time -e '$t=time; open(STDOUT,">/dev/null"); open(STDERR,">'"$e"'"); $rc=system(@ARGV); open(T,">&3"); printf T "%.3f %d\n", time-$t, $rc>>8' -- ${TMO:+timeout $TMO} env "${envs[@]}" $R $P 3>&1)
    rc=${res#* }; wall=${res% *}
    if [ "$rc" != 0 ]; then echo "$B $name run $r: exit $rc" >&2; tail -3 "$e" >&2; fi
    python3 - "$B" "$name" "$r" "$wall" "$rc" "$load" "$e" >>"$OUT" <<'PY'
import json, re, sys
b, c, r, wall, rc, load, path = sys.argv[1:]
d = {"bench": b, "config": c, "run": int(r), "wall_s": float(wall), "rc": int(rc), "load1": float(load)}
for line in open(path, errors="replace"):
    if not line.startswith("vgc-"):
        continue
    m = re.match(r"(vgc-[a-z0-9-]+): (.*)", line)
    tag, rest = m.group(1), m.group(2)
    if "per_worker" in rest:
        k, *vals = rest.split()
        d.setdefault(k, [int(v) for v in vals])
        continue
    toks = rest.split()
    for k, v in zip(toks, toks[1:]):
        if re.fullmatch(r"[a-z_0-9]+", k) and re.fullmatch(r"-?[0-9.]+", v):
            d.setdefault(k, float(v))
        elif k in ("mode", "variant") and k not in d:
            d[k] = v
print(json.dumps(d))
PY
    echo "$B,$name,$r,$wall,rc=$rc" >&2
    rm -f "$e"
  done
done
