#!/bin/sh
# Build the allocator-comparison runtimes (docs/allocator-comparison-results.md):
#
#   tools/proto-build.sh VARIANT...          into _build/proto/VARIANT/
#   tools/proto-build.sh --install VARIANT   into the tree itself (for the OCaml
#                                            testsuite, which runs
#                                            <tree>/runtime/ocamlrun)
#   tools/proto-build.sh --restore           the tree's default runtime again
#
# VARIANT is one of
#   base     A as it stands (no hooks): the default build.  Variant names
#            must differ in more than case: macOS file systems ignore it
#   A        A with the parallel and incremental sweep baselines (PROTO=A)
#   B        B, pages by size class (PROTO=B)
#   A-check  A, every sweep compared with the verified one; A's own checker on
#   B-check  B, every sweep compared with the verified one; B's checker on
# Each lands in generational/ocaml-integration/_build/proto/VARIANT/ as
# ocamlrun and libasmrun.a (for ocamlopt -I).  Variants are built in a
# separate patched worktree of ocaml-4.14-verified-gen (_build/pb, set up on
# first use), so the tree's own runtime only changes with --install/--restore.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
INT=$ROOT/generational/ocaml-integration
OUT=$INT/_build/proto
PB=$INT/_build/pb

setup_pb() {
  [ -f "$PB/ocaml-4.14-verified-gen/Makefile.config" ] && return
  echo "=== setting up $PB"
  mkdir -p "$PB/verified_gc"
  git -C "$INT/ocaml-4.14-verified-gen" worktree add -q --detach "$PB/ocaml-4.14-verified-gen" HEAD
  (cd "$PB/ocaml-4.14-verified-gen" && git apply "$INT/patches/runtime_gen.patch" 2>/dev/null \
     && ./configure -q --disable-naked-pointers >/dev/null)
  for f in alloc_gen.c Makefile profiling_counters.h proto; do
    ln -sfn "$INT/verified_gc/$f" "$PB/verified_gc/$f"
  done
  ln -sfn "$INT/caml" "$PB/caml"
  rm -rf "$PB/ocaml-4.14-verified-gen/runtime/verified_gc"
  ln -sfn "$PB/verified_gc" "$PB/ocaml-4.14-verified-gen/runtime/verified_gc"
}

flags() {   # flags VARIANT -> "PROTO|EXTRA_CFLAGS"
  case $1 in
    base)    echo "|" ;;
    A)       echo "A|" ;;
    B)       echo "B|" ;;
    A-check) echo "A|-DVERGC_PROTO_CHECK -DVGC_CHECK_ALLOC" ;;
    B-check) echo "B|-DVERGC_PROTO_CHECK" ;;
    *) echo "unknown variant $1" >&2; exit 2 ;;
  esac
}

build() {   # build GC_DIR TREE PROTO EXTRA_CFLAGS
  make -s -C "$1" clean
  make -s -C "$1" PROTO="$3" VGC_EXTRA_CFLAGS="$4" all 2>&1 \
    | grep -E 'error|warning:' | grep -v -e minor_offset_to_abs || true
  make -s -C "$2/runtime" PROTO="$3" VGC_EXTRA_CFLAGS="$4" ocamlrun libasmrun.a >/dev/null
}

case "${1:-}" in
  --install)
    f=$(flags "$2")
    echo "=== installing $2 in the tree (PROTO=${f%%|*} VGC_EXTRA_CFLAGS=${f#*|})"
    build "$INT/verified_gc" "$INT/ocaml-4.14-verified-gen" "${f%%|*}" "${f#*|}"
    exit 0 ;;
  --restore)
    echo "=== restoring the tree's default runtime"
    build "$INT/verified_gc" "$INT/ocaml-4.14-verified-gen" "" ""
    exit 0 ;;
esac

setup_pb
for v in "$@"; do
  f=$(flags "$v")
  echo "=== $v (PROTO=${f%%|*} VGC_EXTRA_CFLAGS=${f#*|})"
  build "$PB/verified_gc" "$PB/ocaml-4.14-verified-gen" "${f%%|*}" "${f#*|}"
  mkdir -p "$OUT/$v"
  for f in ocamlrun libasmrun.a; do   # rename, so runs in progress keep theirs
    cp "$PB/ocaml-4.14-verified-gen/runtime/$f" "$OUT/$v/$f.new"
    mv -f "$OUT/$v/$f.new" "$OUT/$v/$f"
  done
done
