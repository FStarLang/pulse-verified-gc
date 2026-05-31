#!/usr/bin/env sh
set -eu

if [ "$#" -lt 6 ]; then
  echo "usage: $0 OUT.csv BENCHMARK CONFIGURED_WORDS VERIFIED_OCAMLRUN STOCK_OCAMLRUN BYTECODE [ARGS...]" >&2
  exit 2
fi

out_csv=$1
benchmark=$2
configured_words=$3
verified_ocamlrun=$4
stock_ocamlrun=$5
bytecode=$6
shift 6

unit_words=${HEAP_CALIBRATE_UNIT_WORDS:-131072}      # 1 MiB at 8 bytes/word.
max_words=${HEAP_CALIBRATE_MAX_WORDS:-268435456}    # 2 GiB at 8 bytes/word.
run_timeout=${HEAP_CALIBRATE_TIMEOUT:-}

tmp=${TMPDIR:-/tmp}/vergc-bench-min-heap.$$
trap 'rm -f "$tmp"' EXIT HUP INT TERM

ceil_div() {
  n=$1
  d=$2
  echo $(((n + d - 1) / d))
}

last_stats_line=
run_stock() {
  last_stats_line=
  set +e
  if [ -n "$run_timeout" ] && command -v timeout >/dev/null 2>&1; then
    timeout "$run_timeout" "$stock_ocamlrun" "$bytecode" "$@" >/dev/null 2>"$tmp"
  else
    "$stock_ocamlrun" "$bytecode" "$@" >/dev/null 2>"$tmp"
  fi
  status=$?
  set -e
  if [ "$status" -ne 0 ]; then
    cat "$tmp" >&2
    exit "$status"
  fi
  last_stats_line=$(grep '^BENCH_STATS,' "$tmp" | tail -n 1 || true)
  if [ -z "$last_stats_line" ]; then
    echo "bench_min_heap: no BENCH_STATS line produced by stock $benchmark" >&2
    cat "$tmp" >&2
    exit 1
  fi
}

run_verified() {
  words=$1
  shift
  last_stats_line=
  set +e
  if [ -n "$run_timeout" ] && command -v timeout >/dev/null 2>&1; then
    MIN_EXPANSION_WORDSIZE=$words \
      timeout "$run_timeout" "$verified_ocamlrun" "$bytecode" "$@" >/dev/null 2>"$tmp"
  else
    MIN_EXPANSION_WORDSIZE=$words \
      "$verified_ocamlrun" "$bytecode" "$@" >/dev/null 2>"$tmp"
  fi
  status=$?
  set -e
  if [ "$status" -ne 0 ]; then
    return 1
  fi
  last_stats_line=$(grep '^BENCH_STATS,' "$tmp" | tail -n 1 || true)
  [ -n "$last_stats_line" ]
}

run_stock "$@"
stock_stats_csv=${last_stats_line#BENCH_STATS,}
stock_rss_mb=$(printf '%s\n' "$stock_stats_csv" | awk -F, '{print $10}')
baseline_words=$(awk -v mb="$stock_rss_mb" -v unit="$unit_words" 'BEGIN {
  words = mb * 1048576 / 8
  units = int((words + unit - 1) / unit)
  if (units < 1) units = 1
  printf "%d", units * unit
}')

baseline_units=$(ceil_div "$baseline_words" "$unit_words")
high_units=$(ceil_div "$configured_words" "$unit_words")
max_units=$(ceil_div "$max_words" "$unit_words")
if [ "$high_units" -lt "$baseline_units" ]; then
  high_units=$baseline_units
fi
if [ "$high_units" -lt 1 ]; then
  high_units=1
fi

if run_verified "$baseline_words" "$@"; then
  best_words=$baseline_words
else
  while ! run_verified $((high_units * unit_words)) "$@"; do
    high_units=$((high_units * 2))
    if [ "$high_units" -gt "$max_units" ]; then
      echo "bench_min_heap: $benchmark did not pass below $max_words words" >&2
      cat "$tmp" >&2
      exit 1
    fi
  done

  lo=$((baseline_units + 1))
  hi=$high_units
  best=$high_units
  while [ "$lo" -le "$hi" ]; do
    mid=$(((lo + hi) / 2))
    words=$((mid * unit_words))
    if run_verified "$words" "$@"; then
      best=$mid
      hi=$((mid - 1))
    else
      lo=$((mid + 1))
    fi
  done

  best_words=$((best * unit_words))
  if ! run_verified "$best_words" "$@"; then
    echo "bench_min_heap: final run unexpectedly failed for $benchmark at $best_words words" >&2
    cat "$tmp" >&2
    exit 1
  fi
fi

if [ ! -f "$out_csv" ]; then
  printf '%s\n' \
    'benchmark,stock_rss_mb,baseline_major_heap_words,min_major_heap_words,min_major_heap_mb,major_heap_over_stock_rss,configured_major_heap_words,configured_major_heap_mb,configured_heap_over_stock_rss,granularity_words,total_allocated_words,minor_words,major_words,promoted_words,minor_collections,major_collections,forced_major_collections,heap_words,top_heap_words,rss_mb' \
    > "$out_csv"
fi

min_mb=$(awk -v words="$best_words" 'BEGIN { printf "%.3f", words * 8 / 1048576 }')
configured_mb=$(awk -v words="$configured_words" 'BEGIN { printf "%.3f", words * 8 / 1048576 }')
min_over_stock=$(awk -v mb="$min_mb" -v stock="$stock_rss_mb" 'BEGIN { printf "%.3f", mb / stock }')
configured_over_stock=$(awk -v mb="$configured_mb" -v stock="$stock_rss_mb" 'BEGIN { printf "%.3f", mb / stock }')
printf '%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s\n' \
  "$benchmark" "$stock_rss_mb" "$baseline_words" "$best_words" "$min_mb" \
  "$min_over_stock" "$configured_words" "$configured_mb" "$configured_over_stock" \
  "$unit_words" "${last_stats_line#BENCH_STATS,}" \
  >> "$out_csv"
