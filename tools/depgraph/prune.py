#!/usr/bin/env python3
"""Delete the definitions that `fstar_depgraph` reports unreachable.

Reads the viewer data emitted under `_depgraph/` and removes each unused
definition from its source file, using the line ranges the tool recorded for
the implementation (`l`..`e`) and the interface (`il`..`ie`).

The unreachable set is closed under references, so a single pass reaches the
fixpoint.  Deletions that would break a mutually recursive `let ... and ...`
group are skipped and reported instead.

Usage:
  prune.py <depgraph-dir> <repo-root> [--only MODULE ...] [--skip MODULE ...]
           [--dry-run]
"""

import os
import re
import sys
import json
import subprocess

DOC = re.compile(r"^\s*///")
ATTR = re.compile(r"^\s*\[@@")
AND = re.compile(r"^and\s")
QUAL_LINE = re.compile(
    r"^\s*(?:private|irreducible|unfold|inline_for_extraction|noextract|abstract"
    r"|total|noeq|unopteq)\s*$")
EMPTY_OPTS = re.compile(r"^#push-options")
QUALS = r"(?:private\s+|irreducible\s+|unfold\s+|inline_for_extraction\s+|noextract\s+|assume\s+|\[@@[^\]]*\]\s*)*"
# Pulse introduces its own definition forms.  They are ordinary top-level
# definitions as far as the dependence graph is concerned, but they are spelled
# `fn` / `ghost fn` / `atomic fn` / `unobservable fn` rather than `let`, so a
# `let|val|type`-only header regex silently refuses to delete any of them --
# which leaves a pruned module referring to helpers that are already gone.
PULSE_KW = r"(?:(?:ghost|atomic|unobservable)\s+)?fn"
# `let x : squash p = ...` is a *fact*, not a callee: nothing ever names it,
# but its type sits in the SMT context of every later proof in the module.
FACT = re.compile(QUALS + r"(?:val|let)\s+[A-Za-z0-9_\x27]+\s*:\s*squash\b")
TOP = re.compile(
    r"^(///|\(\*|\[@@"
    r"|(?:val|let|rec|and|type|open|module|include|friend|instance|effect|new_effect"
    r"|fn|ghost|atomic|unobservable"
    r"|assume|private|irreducible|unfold|inline_for_extraction|noextract|abstract"
    r"|total|noeq|unopteq|sub_effect|layered_effect|polymonadic_bind|exception"
    r"|splice|option)(?:\s|$)"
    r"|#(?:push-options|pop-options|restart-solver|set-options|reset-options))")


# `\b` is useless here: F* identifiers may end in a prime, which is not a
# word character, so the boundary has to be spelled out.
NOT_IDENT = r"(?![A-Za-z0-9_\x27])"


def header_re(name):
    return re.compile(
        QUALS + r"(?:val|let|type|" + PULSE_KW + r")(?:\s+rec)?\s+"
        + re.escape(name) + NOT_IDENT)


def and_re(name):
    return re.compile(r"^and\s+" + re.escape(name) + NOT_IDENT)


def and_name(line):
    m = re.match(r"^and\s+([A-Za-z0-9_\x27]+)", line)
    return m.group(1) if m else None


def load_data(dg):
    """Run the emitted JS through node and hand back the module records."""
    script = r"""
const path = require('path');
const dg = process.argv[1];
let IDX = null; const MODS = {};
global.DG = { setIndex: d => { IDX = d; }, setModule: (k, d) => { MODS[k] = d; } };
require(path.join(dg, 'data', 'index.js'));
for (let i = 0; i < IDX.mods.length; i++) require(path.join(dg, 'data', 'm', i + '.js'));
const out = IDX.mods.map((m, i) => ({
  name: m.n,
  impl: (IDX.files[m.s]||{}).n || null,
  iface: (IDX.files[m.i]||{}).n || null,
  defs: (MODS[i] ? MODS[i].defs : []).map(d => ({
    n: d.n, u: d.u || 0, g: d.g || 0, k: d.k, l: d.l || 0, e: d.e || 0,
    il: d.il || 0, ie: d.ie || 0,
  })),
}));
process.stdout.write(JSON.stringify(out));
"""
    res = subprocess.run(["node", "-e", script, os.path.abspath(dg)], capture_output=True, text=True)
    if res.returncode != 0:
        sys.exit("node failed:\n" + res.stderr)
    return json.loads(res.stdout)


def grow_up(lines, start):
    """Absorb the doc comment / attributes / blank line above `start`."""
    i = start
    while i > 0 and (
        DOC.match(lines[i - 1])
        or ATTR.match(lines[i - 1])
        or QUAL_LINE.match(lines[i - 1])
    ):
        i -= 1
    if i > 0 and i < start and lines[i - 1].strip() == "":
        i -= 1
    return i


def locate(lines, name):
    """Every declaration header for `name` in this file.

    A module with no separate `.fsti` often carries both a `val` and its
    defining `let` in the same file, so there can be more than one.
    """
    pat, apat = header_re(name), and_re(name)
    return [k for k, l in enumerate(lines) if pat.match(l) or apat.match(l)]


def drop_empty_option_blocks(lines):
    """Collapse a `#push-options` / `#pop-options` pair left with nothing in it."""
    out = []
    k = 0
    while k < len(lines):
        if EMPTY_OPTS.match(lines[k]):
            j = k + 1
            while j < len(lines) and lines[j].strip() == "":
                j += 1
            if j < len(lines) and lines[j].startswith("#pop-options"):
                k = j + 1
                while k < len(lines) and lines[k].strip() == "":
                    k += 1
                continue
        out.append(lines[k])
        k += 1
    return out


def prune_file(path, spans, dry):
    lines = open(path).read().split("\n")
    dead_names = {n for n, _, _ in spans}
    kill = set()
    skipped = []
    for name, _hint, _end in spans:
        heads = locate(lines, name)
        if not heads:
            skipped.append((name, "declaration not found"))
            continue
        for i in heads:
            if AND.match(lines[i]):
                skipped.append((name, "member of a `let ... and ...` group"))
                continue
            if FACT.match(lines[i]):
                skipped.append((name, "`squash` fact held in the SMT context"))
                continue
            j = i + 1
            while True:
                while j < len(lines) and not TOP.match(lines[j]):
                    j += 1
                # A `let rec ... and ...` group has to go all at once, so keep
                # extending while the next sibling is dead too.
                sib = and_name(lines[j]) if j < len(lines) else None
                if sib is None:
                    break
                if sib not in dead_names:
                    break
                j += 1
            if j < len(lines) and AND.match(lines[j]):
                skipped.append((name, "has a live `and` sibling"))
                continue
            s = grow_up(lines, i)
            while j < len(lines) and lines[j].strip() == "":
                j += 1
            kill.update(range(s, j))
    if not kill:
        return 0, skipped
    kept = [l for k, l in enumerate(lines) if k not in kill]
    kept = drop_empty_option_blocks(kept)
    if not dry:
        text = "\n".join(kept)
        if not text.endswith("\n"):
            text += "\n"
        open(path, "w").write(text)
    return len(kill), skipped


def index_sources(root):
    """Map each F* source basename to its path (module names are unique)."""
    table = {}
    for top in ("common", "mark-and-sweep", "generational", "spot"):
        for dirpath, _, names in os.walk(os.path.join(root, top)):
            for n in names:
                if n.endswith((".fst", ".fsti")):
                    table.setdefault(n, os.path.join(dirpath, n))
    return table


def main():
    args = sys.argv[1:]
    dry = "--dry-run" in args
    args = [a for a in args if a != "--dry-run"]
    only, skip = set(), set()
    bucket = None
    positional = []
    for a in args:
        if a == "--only":
            bucket = only
        elif a == "--skip":
            bucket = skip
        elif bucket is not None and a.startswith("GC."):
            bucket.add(a)
        else:
            positional.append(a)
    dg, root = positional[0], positional[1]

    mods = load_data(dg)
    sources = index_sources(root)
    total_defs = total_lines = 0
    all_skipped = []
    touched = []
    for m in mods:
        if only and m["name"] not in only:
            continue
        if m["name"] in skip:
            continue
        # u == 1 is "unreachable"; u == 2 is "implicitly live" (SMT pattern etc.)
        # and definitions the compiler generated (projectors, discriminators,
        # `haseq` axioms) have no source text of their own.
        dead = [d for d in m["defs"] if d["u"] == 1 and not d["g"]]
        if not dead:
            continue
        for attr, key in (("impl", ("l", "e")), ("iface", ("il", "ie"))):
            rel = m[attr]
            if not rel:
                continue
            path = sources.get(rel)
            if not path:
                continue
            # A missing line hint just means the tool had no range for this
            # file; still look the declaration up by name so that a `val` is
            # never left behind without its `let` (or vice versa).
            spans = [(d["n"], d[key[0]] or 1, d[key[1]]) for d in dead]
            if not spans:
                continue
            n, sk = prune_file(path, spans, dry)
            if n:
                touched.append(rel)
                total_lines += n
            all_skipped += [
                (m["name"], name, why) for name, why in sk
                if why != "declaration not found"
            ]
        total_defs += len(dead)

    print(f"pruned {total_defs} dead definitions, {total_lines} lines, "
          f"{len(touched)} files{' (dry run)' if dry else ''}")
    if all_skipped:
        print(f"skipped {len(all_skipped)}:")
        for mod, name, why in all_skipped:
            print(f"  {mod}.{name}: {why}")
    for f in sorted(set(touched)):
        print("  M", f)


if __name__ == "__main__":
    main()
