#!/usr/bin/env bash
# ThreadSanitizer bytecode runtime for the combined prototype (stage P0 of
# docs/pages-parallel-gc-design.md): the page prototype B2 with
# par_mark_pages.c, after parmark_build_tsan.sh on sheera/parallel-mark-proto2.
# The whole runtime, the collector, the bridge and the prototype are
# instrumented, built out of tree in _build/tsan-pages/.  Run
# tools/proto-build.sh B2 first: it sets up the patched tree (_build/pb) and
# writes the hooked GC_Gen_Impl_proto.c.  CHECK=1 adds -DVERGC_PROTO_CHECK.
set -eu
GI=$(cd "$(dirname "$0")/../.." && pwd)
SNAP=$GI/../snapshot
PB=$GI/_build/pb
OC=$PB/ocaml-4.14-verified-gen
VG=$GI/verified_gc
TSAN_CC=${TSAN_CC:-/usr/local/opt/llvm@18/bin/clang}
B=$GI/_build/tsan-pages
TF="-O1 -g -fsanitize=thread"
W="-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function"
DEFS="-DVERGC_PROTO -DVERGC_PROTO_B -DVERGC_B_VARIANT=2 ${CHECK:+-DVERGC_PROTO_CHECK}"
GEN_INC="-include $SNAP/compat.h -I$SNAP -I$SNAP/internal -I$SNAP/krmllib -I$SNAP/krmllib/krml
         -I$SNAP/krmllib/krml/internal -I$VG/proto -I$GI -I$OC/runtime -I$OC"
GEN_SRC="$PB/verified_gc/GC_Gen_Impl_proto.c $SNAP/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c
         $SNAP/krmlinit.c $SNAP/compat.c $VG/alloc_gen.c $VG/proto/proto_common.c
         $VG/proto/proto_check.c $VG/proto/par_mark_pages.c $VG/proto/alloc_pages.c"
mkdir -p $B

T=$B/ocaml-tsan
if [ ! -f $T/.objs-built ]; then
  rm -rf $T && mkdir -p $T && cp -R $OC/. $T/
  rm -rf $T/runtime/verified_gc $T/runtime/*.o $T/runtime/*.a
  mkdir -p $T/runtime/verified_gc && cp $VG/alloc_gen.c $T/runtime/verified_gc/
  printf 'pm-byte: $(libcamlrun_OBJECTS) prims.$(O)\n' >$B/objs.mk
  make -C $T/runtime -f Makefile -f $B/objs.mk -j8 pm-byte CC="$TSAN_CC" \
    OC_CFLAGS="-O1 -g -fsanitize=thread -fno-strict-aliasing -fwrapv -pthread" >/dev/null
  touch $T/.objs-built
fi
objs() { make -s -C $T/runtime -f Makefile -f - print <<<"print: ; @echo \$($1)"; }

rm -rf $B/o-byte && mkdir -p $B/o-byte
for s in $GEN_SRC; do $TSAN_CC $TF $W $DEFS $GEN_INC -c "$s" -o "$B/o-byte/$(basename "${s%.c}").o"; done
rm -f $B/libcamlrun.a
(cd $T/runtime && ar rc $B/libcamlrun.a $(objs libcamlrun_OBJECTS)) && ranlib $B/libcamlrun.a
$TSAN_CC $TF -o $B/ocamlrun${CHECK:+-check} $B/o-byte/*.o $T/runtime/prims.o $B/libcamlrun.a -lm -lpthread
echo "built $B/ocamlrun${CHECK:+-check}"
