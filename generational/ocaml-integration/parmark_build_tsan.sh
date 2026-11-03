#!/usr/bin/env bash
# ThreadSanitizer bytecode runtime for the prototype parallel mark
# (verified_gc/par_mark.c and par_mark2.c), after parallel-sweep/rt/build_tsan.sh on
# sheera/parallel-sweep: the whole runtime, the collector, the bridge and
# par_mark.c instrumented, built out of tree in _build/tsan/.  Needs a
# TSan-capable clang (Apple clang 12's TSan runtime crashes on this macOS).
set -eu
GI=$(cd "$(dirname "$0")" && pwd)
SNAP=$GI/../snapshot
OC=$GI/ocaml-4.14-verified-gen
TSAN_CC=${TSAN_CC:-/usr/local/opt/llvm@18/bin/clang}
B=$GI/_build/tsan
TF="-O1 -g -fsanitize=thread"
W="-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function"
GEN_INC="-include $SNAP/compat.h -I$SNAP -I$SNAP/internal -I$SNAP/krmllib -I$SNAP/krmllib/krml
         -I$SNAP/krmllib/krml/internal -I$GI -I$OC/runtime -I$OC"
GEN_SRC="$GI/verified_gc/gc_gen_impl_proto.c $SNAP/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c
         $SNAP/krmlinit.c $SNAP/compat.c $GI/verified_gc/alloc_gen.c $GI/verified_gc/par_mark.c
         $GI/verified_gc/par_mark2.c"
mkdir -p $B

T=$B/ocaml-tsan
if [ ! -f $T/.objs-built ]; then
  rm -rf $T && mkdir -p $T && cp -R $OC/. $T/
  rm -f $T/runtime/verified_gc $T/runtime/*.o $T/runtime/*.a
  mkdir -p $T/runtime/verified_gc && cp $GI/verified_gc/alloc_gen.c $T/runtime/verified_gc/
  printf 'pm-byte: $(libcamlrun_OBJECTS) prims.$(O)\n' >$B/objs.mk
  make -C $T/runtime -f Makefile -f $B/objs.mk -j8 pm-byte CC="$TSAN_CC" \
    OC_CFLAGS="-O1 -g -fsanitize=thread -fno-strict-aliasing -fwrapv -pthread" >/dev/null
  touch $T/.objs-built
fi
objs() { make -s -C $T/runtime -f Makefile -f - print <<<"print: ; @echo \$($1)"; }

rm -rf $B/o-byte && mkdir -p $B/o-byte
for s in $GEN_SRC; do $TSAN_CC $TF $W $GEN_INC -c "$s" -o "$B/o-byte/$(basename "${s%.c}").o"; done
rm -f $B/libcamlrun.a
(cd $T/runtime && ar rc $B/libcamlrun.a $(objs libcamlrun_OBJECTS)) && ranlib $B/libcamlrun.a
$TSAN_CC $TF -o $B/ocamlrun $B/o-byte/*.o $T/runtime/prims.o $B/libcamlrun.a -lm -lpthread
echo "built $B/ocamlrun"
