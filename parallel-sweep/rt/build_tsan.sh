#!/usr/bin/env bash
# ThreadSanitizer runtimes for the parallel sweep (docs/parallel-sweep-phase1.md,
# §9, Stage 3, step 4), out of tree under parallel-sweep/_build/rt/tsan/:
#   ocamlrun      bytecode: the whole runtime, the collector, the parallel sweep
#                 and the test bridge (-DVERGC_PAR_SWEEP_CHECK), all instrumented
#   libasmrun.a   native: the same; OCaml-generated code and amd64.S are not
# The runtime objects are rebuilt in a copy of the tree (as in Spike 3), so the
# tree itself is not touched.  Needs the TSan-capable clang below: Apple clang
# 12's TSan runtime crashes on this macOS (SPIKE.md, Spike 2).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
GI=$HERE/../../generational/ocaml-integration
SNAP=$HERE/../../generational/snapshot
PSW=$HERE/../snapshot
OC=$GI/ocaml-4.14-verified-gen
TSAN_CC=${TSAN_CC:-/usr/local/opt/llvm@18/bin/clang}
B=$HERE/../_build/rt/tsan
TF="-O1 -g -fsanitize=thread"
W="-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function"
GEN_INC="-include $SNAP/compat.h -I$SNAP -I$SNAP/internal -I$SNAP/krmllib -I$SNAP/krmllib/krml
         -I$SNAP/krmllib/krml/internal -I$GI -I$OC/runtime -I$OC"
PSW_FLAGS="-I$PSW $GEN_INC -fno-common -Dkrmlinit_globals=sweep_par_krmlinit_globals -DVERGC_PAR_SWEEP_CHECK"
GEN_SRC="$SNAP/GC_Gen_Impl.c $SNAP/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c
         $SNAP/krmlinit.c $SNAP/compat.c $GI/verified_gc/alloc_gen.c"
PSW_SRC="$PSW/GC_SweepPar.c $PSW/GC_Spec_GC_Lib_Header_GC_Lib_Address.c $PSW/krmlinit.c
         $HERE/../c/par_sweep.c $GI/verified_gc/par_sweep_bridge.c"
mkdir -p $B

# collector OUTDIR FLAGS...: the generational collector, the parallel sweep and
# the test bridge, instrumented.
collector() {
  local out=$1; shift
  rm -rf "$out"; mkdir -p "$out"
  for s in $GEN_SRC; do $TSAN_CC $TF $W "$@" $GEN_INC -c "$s" -o "$out/gen_$(basename "${s%.c}").o"; done
  for s in $PSW_SRC; do $TSAN_CC $TF $W "$@" $PSW_FLAGS -c "$s" -o "$out/psw_$(basename "${s%.c}").o"; done
}

# The runtime's own objects, instrumented, in a copy of the tree.  Only the
# objects are built: the patched archive rules would rebuild verified_gc in place.
T=$B/ocaml-tsan
if [ ! -f $T/.objs-built ]; then
  rm -rf $T && mkdir -p $T && cp -R $OC/. $T/
  rm -f $T/runtime/verified_gc $T/runtime/*.o $T/runtime/*.a
  printf 'psw-byte: $(libcamlrun_OBJECTS) prims.$(O)\npsw-native: $(libasmrun_OBJECTS)\n' >$B/objs.mk
  make -C $T/runtime -f Makefile -f $B/objs.mk -j8 psw-byte psw-native CC="$TSAN_CC" \
    OC_CFLAGS="-O1 -g -fsanitize=thread -fno-strict-aliasing -fwrapv -pthread" >/dev/null
  touch $T/.objs-built
fi
objs() { make -s -C $T/runtime -f Makefile -f - print <<<"print: ; @echo \$($1)"; }

collector $B/o-byte
rm -f $B/libcamlrun.a
(cd $T/runtime && ar rc $B/libcamlrun.a $(objs libcamlrun_OBJECTS)) && ranlib $B/libcamlrun.a
$TSAN_CC $TF -o $B/ocamlrun $B/o-byte/*.o $T/runtime/prims.o $B/libcamlrun.a -lm -lpthread

collector $B/o-native -DNATIVE_CODE
rm -f $B/libasmrun.a
(cd $T/runtime && ar rc $B/libasmrun.a $(objs libasmrun_OBJECTS))
ar rs $B/libasmrun.a $B/o-native/*.o
echo "built $B/ocamlrun and $B/libasmrun.a"
