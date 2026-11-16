#!/usr/bin/env bash
# check_unsupported.sh MESSAGE COMMAND...
#
# Runs COMMAND (an unsupported_features run under the verified runtime) and
# checks that it stopped where it should: non-zero exit, "before" printed but
# not "after", and "Fatal error: MESSAGE not supported by the verified GC" on
# stderr.  Issues #42 and #43.
set -u

msg="$1"; shift
out="$("$@" 2>"${TMPDIR:-/tmp}/check_unsupported.$$.err")"
rc=$?
err="$(cat "${TMPDIR:-/tmp}/check_unsupported.$$.err")"
rm -f "${TMPDIR:-/tmp}/check_unsupported.$$.err"

fail() {
    echo "FAIL: $*"
    echo "  exit code: $rc"
    echo "  stdout: $out"
    echo "  stderr: $err"
    exit 1
}

[ "$rc" -ne 0 ] || fail "expected a non-zero exit"
case "$out" in *before*) ;; *) fail "did not reach the feature (no \"before\")" ;; esac
case "$out" in *after*) fail "ran past the unsupported feature" ;; esac
case "$err" in
    *"Fatal error: $msg not supported by the verified GC"*) ;;
    *) fail "missing \"Fatal error: $msg not supported by the verified GC\"" ;;
esac
echo "OK: stopped with: $err"
