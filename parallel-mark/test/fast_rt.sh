#!/usr/bin/env bash
# Speed up two extracted F* library modules, for the Stage 3 test only.
#   fast_rt.sh <dir>
#
# Custard writes FStar.Seq as an OCaml list, with index and upd recursing on
# arbitrary-precision integers, and FStar.UInt's logand, logor, lognot and
# shifts through 64-element bit vectors.  The heap is a list of 2,000 to
# 3,000 bytes and every colour read goes through FStar.UInt, so these
# dominate the run time.  This rewrites them with native arithmetic that
# computes the same values (for FStar.UInt, the values its own lemmas give:
# logand_spec-style bitwise results, a * 2^s mod 2^n, a / 2^s, 2^n - 1 - a).
# The originals are kept as <name>_orig, and the test compares the two on
# random inputs before it starts (check_fast_rt in mark_par2_test.ml).
set -euo pipefail
python3 - "$1" <<'PY'
import sys
d = sys.argv[1]

def patch(path, subs):
    s = open(path).read()
    for old, new in subs:
        assert s.count(old) == 1, "unexpected shape in %s: %r" % (path, old[:40])
        s = s.replace(old, new)
    open(path, "w").write(s)

patch(d + "/FStar_Seq_Base.ml", [
  ("let index (s : ('a) list) (eta : Prims.int) : 'a =\n  (FStar_List_Tot_Base.index s eta)\n",
   "let index_orig (s : ('a) list) (eta : Prims.int) : 'a =\n  (FStar_List_Tot_Base.index s eta)\n"
   "let index (s : ('a) list) (eta : Prims.int) : 'a =\n  (List.nth s (Z.to_int eta))\n"),
  ("let upd (s : ('a) list) (n : Prims.int) (v : 'a) : ('a) list =\n  (upd' s n v)\n",
   "let upd_orig (s : ('a) list) (n : Prims.int) (v : 'a) : ('a) list =\n  (upd' s n v)\n"
   "let upd (s : ('a) list) (n : Prims.int) (v : 'a) : ('a) list =\n"
   "  (let rec go s n = match s with\n"
   "     | [] -> failwith \"upd\"\n"
   "     | x :: r -> if n = 0 then v :: r else x :: go r (n - 1) in\n"
   "   go s (Z.to_int n))\n"),
])

ops = {
  "logand": ("(n : Prims.int) (a : Prims.int) (b : Prims.int)", "(FStar_BitVector.logand_vec n (to_vec n a) (to_vec n b))", "(Z.logand a b)"),
  "shift_right": ("(n : Prims.int) (a : Prims.int) (s : Prims.int)", "(FStar_BitVector.shift_right_vec n (to_vec n a) s)", "(Z.shift_right a (Z.to_int s))"),
  "logor": ("(n : Prims.int) (a : Prims.int) (b : Prims.int)", "(FStar_BitVector.logor_vec n (to_vec n a) (to_vec n b))", "(Z.logor a b)"),
  "lognot": ("(n : Prims.int) (a : Prims.int)", "(FStar_BitVector.lognot_vec n (to_vec n a))", "(Z.sub (Z.sub (Z.shift_left Z.one (Z.to_int n)) Z.one) a)"),
  "shift_left": ("(n : Prims.int) (a : Prims.int) (s : Prims.int)", "(FStar_BitVector.shift_left_vec n (to_vec n a) s)",
                 "(if Z.geq s n then Z.zero else Z.erem (Z.shift_left a (Z.to_int s)) (Z.shift_left Z.one (Z.to_int n)))"),
}
subs = []
for name, (args, vec, fast) in ops.items():
    old = "let %s %s : Prims.int =\n  (from_vec n %s)\n" % (name, args, vec)
    new = ("let %s_orig %s : Prims.int =\n  (from_vec n %s)\n" % (name, args, vec) +
           "let %s %s : Prims.int =\n  %s\n" % (name, args, fast))
    subs.append((old, new))
patch(d + "/FStar_UInt.ml", subs)
PY
