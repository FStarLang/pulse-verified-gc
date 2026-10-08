#!/usr/bin/env bash
# Build the Stage B test driver from the F*-extracted OCaml.
#
#   build.sh <extracted-ml-dir> <fstar --locate_lib>
#
# The F* OCaml runtime shipped with ./fstar was compiled with OCaml 5.3, so
# its .cmx files cannot be linked here (OCaml 4.14, opam switch fstar-gc).
# Instead the runtime's own .ml sources, under <locate_lib>/lib, are
# compiled: only the modules the extracted code reaches.
set -euo pipefail

ML=$(cd "$1" && pwd)
RT_ROOT=$2/lib
HERE=$(cd "$(dirname "$0")" && pwd)
B=$(cd "$HERE/.." && pwd)/_build
OBJ=$B/obj
rm -rf "$OBJ"; mkdir -p "$OBJ"

PKGS=batteries,zarith,stdint,yojson,ppx_deriving.show,ppx_deriving_yojson

find_rt() {
  for d in "$RT_ROOT/app" "$RT_ROOT/app/ints" "$RT_ROOT/ulib.ml"; do
    if [ -f "$d/$1.ml" ]; then echo "$d/$1.ml"; return; fi
  done
}

deps_of() { ocamlfind ocamldep -modules "$1" | cut -d: -f2 | tr ' ' '\n' | grep -v '^$' || true; }

# GC.Spec.ZeroAddr is an interface whose implementation is C (heap_size and
# zero_addr come from the runtime).  The test supplies it.
cp "$HERE/GC_Spec_ZeroAddr.ml" "$OBJ/"
cp "$ML"/*.ml "$OBJ/"

# GC.Spec.Base.heap_size is `GC.Spec.ZeroAddr.heap_size`, which is noextract
# (`let heap_size = U64.v heap_size_u64`), so extraction leaves `Obj.magic ()`.
# Put the definition back; fail loudly if the extracted line ever changes.
want='let heap_size : Prims.pos= Obj.magic ()'
grep -qxF "$want" "$OBJ/GC_Spec_Base.ml" || { echo "build.sh: heap_size line not found in GC_Spec_Base.ml" >&2; exit 1; }
sed -i '' 's/^let heap_size : Prims.pos= Obj.magic ()$/let heap_size : Prims.pos= FStar_UInt64.v GC_Spec_ZeroAddr.heap_size_u64/' "$OBJ/GC_Spec_Base.ml"
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
    f=$(find_rt "$m")
    if [ -n "$f" ]; then cp "$f" "$OBJ/"; next="$next $(deps_of "$f")"; fi
  done
  todo=$next
done

cp "$HERE/sweep_par_test.ml" "$OBJ/"
cd "$OBJ"
order=$(ocamlfind ocamldep -sort *.ml)
ocamlfind ocamlopt -O3 -package $PKGS -linkpkg -w -a -g $order -o "$B/sweep_par_test" 2>/dev/null \
  || ocamlfind ocamlopt -package $PKGS -linkpkg -w -a -g $order -o "$B/sweep_par_test"
echo "built $B/sweep_par_test"
