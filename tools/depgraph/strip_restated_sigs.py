#!/usr/bin/env python3
"""Remove type ascriptions from .fst definitions that already have a `val` in the .fsti.

F* takes the type of a definition from its interface, so writing

    val foo : g:heap -> x:obj_addr -> Lemma (requires p g x) (ensures q g x)

in Foo.fsti and then

    let foo (g: heap) (x: obj_addr)
      : Lemma (requires p g x)
              (ensures q g x)
      = body

in Foo.fst states the same thing twice.  The second copy has to be kept in sync
by hand and is a routine source of drift.  This rewrites the definition to

    let foo (g: heap) (x: obj_addr)
      = body

leaving the binders alone -- only the `: <type>` ascription between the binder
list and the body's `=` is dropped.

Deliberately conservative.  A definition is left untouched when:

  * the enclosing .fst is a Pulse module (`#lang-pulse`) -- there the
    requires/ensures blocks are part of the `fn` syntax, not an ascription;
  * the ascription mentions `decreases` -- that is a termination measure, not a
    restatement, and the interface does not carry it;
  * no `val` of that name appears in the .fsti;
  * the definition has no ascription to begin with.

Usage:  strip_restated_sigs.py [--dry-run] [--only MODULE ...] [root]
"""

import argparse
import glob
import os
import re
import sys

QUAL = (r"(?:private\s+|noextract\s+|unfold\s+|inline_for_extraction\s+"
        r"|irreducible\s+|\[@@[^\]]*\]\s*)*")
LET = re.compile(r"^(" + QUAL + r")let(\s+rec)?\s+([A-Za-z0-9_']+)")
VAL = re.compile(r"^val\s+([A-Za-z0-9_']+)\s*[:(]", re.M)

SRC_DIRS = ("common/spec", "common/lib", "common/impl",
            "mark-and-sweep/spec", "mark-and-sweep/impl",
            "generational/spec", "generational/impl", "spot")


def scan_tokens(seg):
    """Yield (line, col, char) for every bracket-depth-0 character in seg.

    Skips string literals and `//` comments.  Depth counts (), [] and {}, so a
    `:` inside a binder like `(x: heap)` or a refinement `{U64.v a >= 8}` is
    never reported.
    """
    depth = 0
    instr = False
    for li, raw in enumerate(seg):
        s = raw
        if not instr:
            c = s.find("//")
            if c != -1:
                s = s[:c]
        i = 0
        while i < len(s):
            ch = s[i]
            if instr:
                if ch == "\\":
                    i += 2
                    continue
                if ch == '"':
                    instr = False
                i += 1
                continue
            if ch == '"':
                instr = True
                i += 1
                continue
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0:
                yield li, i, ch, s
            i += 1


def find_ascription(seg):
    """Return ((cl, cc), (el, ec)) for the ascription `:` and the body `=`."""
    colon = None
    for li, i, ch, s in scan_tokens(seg):
        if ch == ":":
            nxt = s[i + 1] if i + 1 < len(s) else ""
            if nxt == "=":            # `:=`
                continue
            if colon is None:
                colon = (li, i)
        elif ch == "=":
            nxt = s[i + 1] if i + 1 < len(s) else ""
            prv = s[i - 1] if i > 0 else ""
            # `x in y` is True for the empty string, so an `=` that ends a line
            # would be discarded as if it were `==`.  Test explicitly.
            if (nxt and nxt in "=>") or (prv and prv in "<>!:=+-*/|&^"):
                continue
            return (colon, (li, i)) if colon else (None, None)
    return (None, None)


def strip_file(fst, fsti, dry):
    txt = open(fst).read()
    if "#lang-pulse" in txt:
        return 0, 0
    vals = set(VAL.findall(open(fsti).read()))
    if not vals:
        return 0, 0

    lines = txt.split("\n")
    heads = [(i, m) for i, l in enumerate(lines) for m in [LET.match(l)] if m]
    ends = [h[0] for h in heads[1:]] + [len(lines)]

    edits = []   # (start_line, end_line, replacement_lines)
    for (i, m), e in zip(heads, ends):
        if m.group(3) not in vals:
            continue
        seg = lines[i:e]
        colon, eq = find_ascription(seg)
        if colon is None or eq is None:
            continue
        (cl, cc), (el, ec) = colon, eq
        asc = "\n".join(seg[cl:el + 1])
        if "decreases" in asc:
            continue
        head = seg[cl][:cc].rstrip()
        tail = seg[el][ec:]
        indent = re.match(r"\s*", seg[el]).group(0)
        new = ([] if not head else [head]) + [indent + tail.rstrip()]
        # nothing gained if the ascription was already on one line with the body
        if len(new) >= (el - cl + 1):
            continue
        edits.append((i + cl, i + el, new))

    if not edits:
        return 0, 0

    saved = sum((b - a + 1) - len(r) for a, b, r in edits)
    if not dry:
        out = []
        prev = 0
        for a, b, r in edits:
            out.extend(lines[prev:a])
            out.extend(r)
            prev = b + 1
        out.extend(lines[prev:])
        open(fst, "w").write("\n".join(out))
    return len(edits), saved


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--only", nargs="*", default=None,
                    help="restrict to these module basenames")
    args = ap.parse_args()
    os.chdir(args.root)

    tot_d = tot_l = tot_f = 0
    for d in SRC_DIRS:
        for fst in sorted(glob.glob(d + "/*.fst")):
            fsti = fst + "i"
            if not os.path.exists(fsti):
                continue
            if args.only and os.path.basename(fst)[:-4] not in args.only:
                continue
            n, saved = strip_file(fst, fsti, args.dry_run)
            if n:
                tot_f += 1
                tot_d += n
                tot_l += saved
                print(f"  {os.path.basename(fst):58s} {n:4d} defs  -{saved} lines")
    print(f"\nstripped {tot_d} restated signatures, {tot_l} lines, {tot_f} files"
          + (" (dry run)" if args.dry_run else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
