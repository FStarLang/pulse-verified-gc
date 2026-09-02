#!/bin/sh
# Compile and run OCaml code on the verified GC -- bytecode and native.
#
#   sh ci/run-verified.sh prog.ml               both variants
#   sh ci/run-verified.sh --byte prog.ml        one variant
#   sh ci/run-verified.sh --native prog.ml
#   sh ci/run-verified.sh --stock prog.ml       stock OCaml, for comparison
#   sh ci/run-verified.sh some/dir              every t*.ml there; if the
#                                               directory has expected_output.txt,
#                                               diff against it
#
# How this works, because it is simpler than it looks:
#
#   bytecode -- a .byte file is portable and contains no collector. The
#               collector is whichever ocamlrun you invoke. So compile with the
#               STOCK compiler and run with the verified runtime. The same
#               .byte runs on either, which is why --stock costs nothing.
#
#   native   -- the collector is archived inside libasmrun.a, so link against
#               the verified GC's copy: stock ocamlopt with -I pointed at
#               ocaml-4.14-verified-gen/runtime. No compiler rebuild needed.
#
# Same mechanism the benchmarks in generational/ocaml-integration/tests use.
# Needs only `make -C generational/ocaml-integration setup` plus a current
# runtime. Rebuild it after touching the collector with:
#   make -C generational/ocaml-integration/verified_gc
#   make -C generational/ocaml-integration/ocaml-4.14-verified-gen/runtime \
#        ocamlrun libasmrun.a
# NOTE: libasmrun.a is a SEPARATE target -- `make ocamlrun` refreshes only the
# bytecode runtime, so a native test would silently link a stale collector.
set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
INT=$ROOT/generational/ocaml-integration
STOCK=$INT/ocaml-4.14-unchanged/_install/bin
VRT=$INT/ocaml-4.14-verified-gen/runtime

MODE=both; WHICH=verified; TARGET=
while [ $# -gt 0 ]; do
  case $1 in
    --byte|--bytecode) MODE=byte ;;
    --native)          MODE=native ;;
    --stock)           WHICH=stock ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/,""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    -*) echo "run-verified: unknown option $1" >&2; exit 2 ;;
    *)  TARGET=$1 ;;
  esac
  shift
done
[ -n "$TARGET" ] || { echo "run-verified: nothing to run (--help)" >&2; exit 2; }

for f in "$STOCK/ocamlc" "$STOCK/ocamlopt"; do
  [ -x "$f" ] || { echo "run-verified: missing $f" >&2
                   echo "run: make -C generational/ocaml-integration setup" >&2; exit 1; }
done
if [ "$WHICH" = verified ]; then
  for f in "$VRT/ocamlrun" "$VRT/libasmrun.a"; do
    [ -e "$f" ] || { echo "run-verified: missing $f" >&2
                     echo "run: make -C generational/ocaml-integration setup" >&2; exit 1; }
  done
  RUNNER=$VRT/ocamlrun
  NATFLAGS="-I $VRT"
  LABEL=verified
else
  RUNNER=$INT/ocaml-4.14-unchanged/runtime/ocamlrun
  NATFLAGS=
  LABEL=stock
fi

WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT
pass=0; fail=0

run_one() {
  src=$1; exp=$2
  base=$(basename "$src" .ml)
  cp "$src" "$WORK/$base.ml"
  for m in byte native; do
    [ "$MODE" = both ] || [ "$MODE" = "$m" ] || continue
    if [ "$m" = byte ]; then
      ( cd "$WORK" && "$STOCK/ocamlc" -o "$base.byte" "$base.ml" ) 2>"$WORK/$base.$m.cerr"
      rc=$?; cmd="$RUNNER $WORK/$base.byte"
    else
      ( cd "$WORK" && "$STOCK/ocamlopt" $NATFLAGS -o "$base.exe" "$base.ml" ) 2>"$WORK/$base.$m.cerr"
      rc=$?; cmd="$WORK/$base.exe"
    fi
    if [ $rc -ne 0 ]; then
      printf '%-24s %-7s %-9s COMPILE FAIL\n' "$base" "$LABEL" "$m"
      sed 's/^/    /' "$WORK/$base.$m.cerr" | head -5; fail=$((fail+1)); continue
    fi
    $cmd >"$WORK/$base.$m.out" 2>"$WORK/$base.$m.err"; rc=$?
    if [ $rc -ne 0 ]; then
      printf '%-24s %-7s %-9s FAIL (exit %d%s)\n' "$base" "$LABEL" "$m" "$rc" \
        "$([ $rc -ge 128 ] && echo ", signal $((rc-128))")"
      sed 's/^/    /' "$WORK/$base.$m.err" | head -5; fail=$((fail+1)); continue
    fi
    if [ -n "$exp" ]; then
      if awk -v t="=== $base" '$0==t{f=1;next} /^=== /{f=0} f' "$exp" \
           | diff -q - "$WORK/$base.$m.out" >/dev/null 2>&1
      then printf '%-24s %-7s %-9s ok\n' "$base" "$LABEL" "$m"; pass=$((pass+1))
      else printf '%-24s %-7s %-9s OUTPUT DIFFERS\n' "$base" "$LABEL" "$m"
           printf '    expected: %s\n' "$(awk -v t="=== $base" '$0==t{f=1;next} /^=== /{f=0} f' "$exp" | tr '\n' ' ')"
           printf '    got:      %s\n' "$(tr '\n' ' ' <"$WORK/$base.$m.out")"
           fail=$((fail+1)); fi
    else
      printf '%-24s %-7s %-9s ok\n' "$base" "$LABEL" "$m"; pass=$((pass+1))
      sed 's/^/    /' "$WORK/$base.$m.out"
    fi
  done
}

if [ -d "$TARGET" ]; then
  exp=""; [ -f "$TARGET/expected_output.txt" ] && exp=$(cd "$TARGET" && pwd)/expected_output.txt
  found=no
  for f in "$TARGET"/t*.ml; do [ -e "$f" ] || continue; found=yes; run_one "$f" "$exp"; done
  [ "$found" = yes ] || { echo "run-verified: no t*.ml in $TARGET" >&2; exit 2; }
  echo; echo "passed $pass, failed $fail"
else
  [ -f "$TARGET" ] || { echo "run-verified: no such file: $TARGET" >&2; exit 2; }
  run_one "$TARGET" ""
fi
[ "$fail" -eq 0 ]
