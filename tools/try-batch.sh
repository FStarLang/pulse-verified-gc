#!/usr/bin/env bash
# Run tools/try-module.sh over a list of sources, N at a time, each in its own
# scratch cache.  Usage:  tools/try-batch.sh <parallelism> <extra-flags> -- <srcs...>
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAR="$1"; shift
FLAGS=""
while [ "$1" != "--" ]; do FLAGS="$FLAGS $1"; shift; done
shift

run_one() {
  local src="$1"
  local id
  id=$(echo "$src" | md5sum | cut -c1-8)
  SCRATCH="$ROOT/_scratch/$id" "$ROOT/tools/try-module.sh" "$src" $FLAGS 2>&1 | head -12
}
export -f run_one
export ROOT FLAGS

mkdir -p "$ROOT/_scratch"
printf '%s\n' "$@" | xargs -P "$PAR" -I{} bash -c 'run_one "$@"' _ {}
