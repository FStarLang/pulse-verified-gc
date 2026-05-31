#!/usr/bin/env sh
set -eu

if [ "$#" -lt 5 ]; then
  echo "usage: $0 OUT.csv BENCHMARK RUNTIME OCAMLRUN BYTECODE [ARGS...]" >&2
  exit 2
fi

out_csv=$1
benchmark=$2
runtime=$3
ocamlrun=$4
bytecode=$5
shift 5

tmp=${TMPDIR:-/tmp}/vergc-bench-stats.$$
trap 'rm -f "$tmp"' EXIT HUP INT TERM

set +e
"$ocamlrun" "$bytecode" "$@" >/dev/null 2>"$tmp"
status=$?
set -e

if [ "$status" -ne 0 ]; then
  cat "$tmp" >&2
  exit "$status"
fi

stats_line=$(grep '^BENCH_STATS,' "$tmp" | tail -n 1 || true)
if [ -z "$stats_line" ]; then
  echo "bench_stats: no BENCH_STATS line produced by $runtime $benchmark" >&2
  cat "$tmp" >&2
  exit 1
fi

if [ ! -f "$out_csv" ]; then
  printf '%s\n' \
    'benchmark,runtime,total_allocated_words,minor_words,major_words,promoted_words,minor_collections,major_collections,forced_major_collections,heap_words,top_heap_words,rss_mb' \
    > "$out_csv"
fi

printf '%s,%s,%s\n' "$benchmark" "$runtime" "${stats_line#BENCH_STATS,}" \
  >> "$out_csv"

