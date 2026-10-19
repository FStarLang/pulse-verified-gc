#!/usr/bin/env bash
# Build the Stage B test driver from the Custard-extracted OCaml.
#
#   build.sh <extracted-ml-dir> <fstar --locate_lib>
#
# The F* OCaml runtime shipped with ./fstar was compiled with OCaml 5.3, so
# its .cmx files cannot be linked here (OCaml 4.14, opam switch fstar-gc).
# Instead the runtime's own .ml sources, under <locate_lib>/lib, are
# compiled: only the modules the extracted code reaches and Custard did not
# write itself.
set -euo pipefail

ML=$(cd "$1" && pwd)
RT_ROOT=$2/lib
HERE=$(cd "$(dirname "$0")" && pwd)
B=$(cd "$HERE/.." && pwd)/_build
OBJ=$B/obj
rm -rf "$OBJ"; mkdir -p "$OBJ"

PKGS=batteries,zarith,stdint,yojson,ppx_deriving.show,ppx_deriving_yojson

find_rt() {
  for d in "$RT_ROOT/app" "$RT_ROOT/app/ints"; do
    if [ -f "$d/$1.ml" ]; then echo "$d/$1.ml"; return; fi
  done
}

deps_of() { ocamlfind ocamldep -modules "$1" | cut -d: -f2 | tr ' ' '\n' | grep -v '^$' || true; }

# GC.Spec.ZeroAddr is an interface whose implementation is C (heap_size and
# zero_addr come from the runtime).  The test supplies it.
cp "$HERE/GC_Spec_ZeroAddr.ml" "$OBJ/"
cp "$ML"/*.ml "$OBJ/"

# Custard writes only real code: anything erased that is still used shows up
# as `Obj.magic ()`.  Fail loudly if the extracted GC code has one.
if grep -q 'Obj.magic ()' "$OBJ"/GC_*.ml; then
  echo "build.sh: an erased value is still used by extracted code:" >&2
  grep -n 'Obj.magic ()' "$OBJ"/GC_*.ml >&2; exit 1
fi

# Runtime modules reachable from the extracted code.
seen=" "
todo=$(for f in "$OBJ"/*.ml "$HERE/sweep_par_test.ml"; do deps_of "$f"; done | sort -u)
while [ -n "$todo" ]; do
  next=""
  for m in $todo; do
    case "$seen" in *" $m "*) continue;; esac
    seen="$seen$m "
    # Custard emits the F* library modules it compiles (FStar_Seq_Base, ...);
    # only the hand-written runtime is taken from <locate_lib>.
    f=$(find_rt "$m")
    if [ -n "$f" ] && [ ! -f "$OBJ/$(basename "$f")" ]; then cp "$f" "$OBJ/"; next="$next $(deps_of "$f")"; fi
  done
  todo=$next
done

cp "$HERE/sweep_par_test.ml" "$OBJ/"
cd "$OBJ"
order=$(ocamlfind ocamldep -sort *.ml)
ocamlfind ocamlopt -O3 -package $PKGS -linkpkg -w -a -g $order -o "$B/sweep_par_test" 2>/dev/null \
  || ocamlfind ocamlopt -package $PKGS -linkpkg -w -a -g $order -o "$B/sweep_par_test"
echo "built $B/sweep_par_test"
