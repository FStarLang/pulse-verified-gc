#!/usr/bin/env bash
# Step 5 (docs/parallel-sweep-phase1.md, §9, Stage 3): fork_sweep.ml, in bytecode
# and native, with 1, 2, 4 and 8 workers, on
#   check    the test runtime (build.sh check): must pass
#   nofork   the same runtime with par_sweep.c replaced by the persistent pool
#            as first reviewed (b4be32e), before its fork fix: the child must
#            hang, showing the test can see a pool that does not survive fork
# and once on the tree's default runtime with the setting off.  Needs
# build.sh check, and ci/build-verified-toolchain.sh for the tree's compilers
# and its Unix library (built against the patched runtime headers).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
GI=$HERE/../../generational/ocaml-integration
TREE=$GI/ocaml-4.14-verified-gen
SNAP=$HERE/../../generational/snapshot
PSW=$HERE/../snapshot
B=$HERE/../_build/rt
F=$B/fork
TIMEOUT=${TIMEOUT:-60}
mkdir -p $F

# --- the control runtime: check, with b4be32e's pool in place of par_sweep.c ---
rm -rf $B/nofork && cp -R $B/check $B/nofork
git -C $HERE show b4be32e:parallel-sweep/c/par_sweep.c > $F/par_sweep_nofork.c || exit 1
CF="-O2 -I$PSW -include $SNAP/compat.h -I$SNAP -I$SNAP/krmllib -I$SNAP/krmllib/krml -fno-common"
cc $CF -Wno-unused-function -c $F/par_sweep_nofork.c -o $F/psw_par_sweep.o
cc $CF -Wno-unused-function -DNATIVE_CODE -c $F/par_sweep_nofork.c -o $F/psw_par_sweep.n.o
(cd $F && ar r $B/nofork/libcamlrun.a psw_par_sweep.o && ar r $B/nofork/libasmrun.a psw_par_sweep.n.o) 2>/dev/null
cc -O2 -flto -o $B/nofork/ocamlrun $B/nofork/prims.o $B/nofork/libcamlrun.a -lm -lpthread -Wl,-no_compact_unwind

# --- the program, bytecode once, native once per runtime ---
OCAMLC="$TREE/ocamlc.opt -nostdlib -I $TREE/stdlib -I $TREE/otherlibs/unix"
OCAMLOPT="$TREE/ocamlopt.opt -nostdlib"
cp $HERE/fork_sweep.ml $F/
(cd $F && $OCAMLC unix.cma fork_sweep.ml -o fork_sweep.byte) || exit 1
for v in check nofork; do
  (cd $F && $OCAMLOPT -I $B/$v -I $TREE/stdlib -I $TREE/otherlibs/unix unix.cmxa fork_sweep.ml \
     -o fork_sweep.$v) || exit 1
done
(cd $F && $OCAMLOPT -I $TREE/runtime -I $TREE/stdlib -I $TREE/otherlibs/unix unix.cmxa fork_sweep.ml \
   -o fork_sweep.default) || exit 1

# limited CMD...: run CMD in its own process group; after TIMEOUT seconds kill
# the whole group (a hung child would otherwise outlive its parent) and exit 124.
limited() {
  perl -e '
    my $t = shift; my $pid = fork;
    if ($pid == 0) { setpgrp(0, 0); exec @ARGV or exit 127 }
    local $SIG{ALRM} = sub { kill "KILL", -$pid; waitpid($pid, 0); exit 124 };
    alarm $t; waitpid($pid, 0); exit($? & 127 ? 128 + ($? & 127) : $? >> 8)' "$TIMEOUT" "$@"
}

export MIN_EXPANSION_WORDSIZE=300000 CAML_LD_LIBRARY_PATH=$TREE/otherlibs/unix
fail=0
run() {  # label expect(ok|hang) cmd...
  local label=$1 expect=$2; shift 2
  out=$(limited "$@" 2>&1); rc=$?
  verdict=$( { [ $expect = ok ] && [ $rc -eq 0 ]; } || { [ $expect = hang ] && [ $rc -eq 124 ]; } && echo as-expected || echo UNEXPECTED)
  echo "$label: rc $rc ($verdict) | $(echo "$out" | grep -E '^(child|parent|ok|FAIL)' | tr '\n' ' ')"
  [ $verdict = as-expected ] || { fail=1; echo "$out" | tail -5; }
}
unset VERGC_PAR_SWEEP_THREADS
run "default runtime, setting off, byte  " ok $TREE/runtime/ocamlrun $F/fork_sweep.byte
run "default runtime, setting off, native" ok $F/fork_sweep.default
for n in 1 2 4 8; do
  export VERGC_PAR_SWEEP_THREADS=$n
  run "check,  $n workers, byte  " ok   $B/check/ocamlrun $F/fork_sweep.byte
  run "check,  $n workers, native" ok   $F/fork_sweep.check
  run "nofork, $n workers, byte  " hang $B/nofork/ocamlrun $F/fork_sweep.byte
  run "nofork, $n workers, native" hang $F/fork_sweep.nofork
done
[ $fail -eq 0 ] && echo "ok: fork (runtime passes, control hangs)" || { echo "FAIL: fork"; exit 1; }
