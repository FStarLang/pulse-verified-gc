#!/usr/bin/env python3
"""Turn a `make depgraph` run into a dead-code inventory + removal plan.

Reads the viewer package produced by fstar-depgraph (data/index.js and
unused-report.txt) and writes a Markdown inventory listing every definition
that is unreachable from the roots, grouped by module, together with a phased
removal plan ordered by risk.

Usage:  unused_inventory.py <depgraph-out-dir> <output.md>
"""

import json
import os
import re
import subprocess
import sys
from collections import defaultdict

# `data/index.js` is a JS object literal (unquoted keys), so let node parse it.
NODE_DUMP = """
global.DG = { setIndex: d => { global.IDX = d; } };
require(process.argv[1]);
process.stdout.write(JSON.stringify(global.IDX));
"""


def load_index(outdir):
    idx_js = os.path.join(outdir, "data", "index.js")
    raw = subprocess.run(
        ["node", "-e", NODE_DUMP, os.path.abspath(idx_js)],
        capture_output=True, text=True, check=True).stdout
    return json.loads(raw)


# "  GC.Mod.name        let rec      GC.Mod.fst:102:0"
ROW = re.compile(r"^  (GC\.\S+)\s+(.*?)\s+(\S+:\d+:\d+)\s*$")


def load_unused(outdir):
    """Return [(fqn, kind, location)] for section 1 of the report."""
    rows, in_sec1 = [], False
    with open(os.path.join(outdir, "unused-report.txt")) as f:
        for line in f:
            if line.startswith("1. Unreachable"):
                in_sec1 = True
                continue
            if re.match(r"^\d+\. ", line):
                in_sec1 = False
            if in_sec1:
                m = ROW.match(line.rstrip("\n"))
                if m:
                    rows.append((m.group(1), m.group(2).strip(), m.group(3)))
    return rows


def area(mod):
    if mod.startswith("GC.Gen"):
        return "generational"
    if mod.startswith("GC.SPOT"):
        return "spot"
    if mod.startswith(("GC.Spec.Base", "GC.Spec.Heap", "GC.Spec.Object",
                       "GC.Spec.Fields", "GC.Spec.Graph", "GC.Spec.DFS",
                       "GC.Spec.HeapGraph", "GC.Spec.HeapModel",
                       "GC.Lib.")):
        return "common"
    return "mark-and-sweep"


def split_mod(fqn, known):
    """Split a fully-qualified name into (module, definition)."""
    i = fqn.rfind(".")
    while i > 0:
        if fqn[:i] in known:
            return fqn[:i], fqn[i + 1:]
        i = fqn.rfind(".", 0, i)
    return fqn.rsplit(".", 1)


def main():
    outdir, dest = sys.argv[1], sys.argv[2]
    idx = load_index(outdir)
    rows = load_unused(outdir)
    known = {m["n"] for m in idx["mods"]}
    counts = {m["n"]: (m["nd"], m["nu"]) for m in idx["mods"]}

    by_mod = defaultdict(list)
    for fqn, kind, loc in rows:
        mod, name = split_mod(fqn, known)
        by_mod[mod].append((name, kind, loc))

    full_dead = sorted((m for m in by_mod if counts[m][0] == counts[m][1]),
                       key=lambda m: -counts[m][0])
    partial = sorted((m for m in by_mod if m not in set(full_dead)),
                     key=lambda m: (-counts[m][1], m))

    st = idx["stats"]
    o = []
    w = o.append
    w("# Dead-code inventory\n")
    w("**Generated** by `make depgraph && make depgraph-inventory` — do not edit by hand.\n")
    w(f"- Roots: `{'`, `'.join(idx['roots'])}`\n")
    w(f"- {st['modules']} modules, {st['defs']} definitions, {st['medges']} module edges")
    w(f"- **{st['dead']} definitions ({100*st['dead']//st['defs']}%) are unreachable from the roots**")
    w(f"- {st['implicit']} definitions are reachable only implicitly (SMT pattern / instance / axiom)\n")
    w("""## Why this set is safe to delete

Reachability is computed transitively from the roots over every reference in the
`.checked` files, so the unreachable set is **closed**: if a definition is
referenced only by unreachable code, it is itself unreachable and already
appears below. Deleting the whole set therefore cannot strand a live definition,
and one pass reaches the fixpoint — no iterate-until-stable loop is needed.

Three caveats the graph *does* account for:

- **Pulse `fn` bodies.** Pulse type-checks its own definitions and hands F* an
  opaque `magic ()` stub, keeping the elaborated term in a serialised
  `sigmeta_extension_data` blob that is not an F* term. The graph would
  therefore miss every lemma invoked from a `fn` body. For those definitions
  only, the tool re-reads the body from the source and treats each identifier
  as a possible reference; this over-approximates, which is the safe direction.

- **SMT-pattern lemmas.** A lemma carrying `[SMTPat ...]` is used by Z3 without
  ever being named. These are classified *implicitly live*, not unreachable, and
  are excluded from the tables below.
- **Pattern-matched constructors.** `Pat_cons` heads are harvested separately,
  so a constructor that is only ever matched on is not mistaken for dead.

One caveat it does **not** account for: deleting a definition changes the SMT
context of every module that `open`s its module, which can perturb unrelated
proofs. That is why the plan below re-verifies after each phase.

""")

    w("## Removal plan\n")
    w("`make depgraph-prune` deletes the whole set mechanically: it locates each")
    w("definition by name in its `.fst` and `.fsti`, takes the doc comment,")
    w("attributes and standalone qualifiers with it, and collapses any")
    w("`#push-options`/`#pop-options` pair it empties. The unreachable set is")
    w("closed, so one pass reaches the fixpoint.\n")
    w("Validate with the full build (`make -k -j24`), the SPOT build")
    w("(`make -C spot -j24`) and extraction (`make extract`, expecting C that is")
    w("byte-identical modulo the KaRaMeL invocation banner). Bisect by module if a")
    w("proof breaks: the graph cannot see that deleting a definition also shrinks")
    w("the SMT context of every module that `open`s it.\n")
    w("The pruner refuses three things, which is why this report may never reach")
    w("zero:\n")
    w("- **`let x : squash p = ...`** — nothing ever *names* such a definition, but")
    w("  its type sits in the SMT context of every later proof in the module, so it")
    w("  is a fact rather than a callee. Deleting one breaks proofs that never")
    w("  mention it.")
    w("- **A `let rec ... and ...` group with a live member** — the group is")
    w("  syntactically indivisible. If every member is dead the pruner takes the")
    w("  whole group; otherwise it leaves it alone.")
    w("- **A definition it cannot find by name** — reported so it can be handled by")
    w("  hand rather than silently skipped.\n")
    if full_dead:
        n_full = sum(counts[m][0] for m in full_dead)
        w(f"### {len(full_dead)} entirely-dead modules ({n_full} definitions)\n")
        w("Every definition in these is unreachable, so the whole `.fst`/`.fsti` pair")
        w("goes. Deleting files is *not* automated: remove them, drop every mention")
        w("from `Makefile` and `*/Makefile` (verification lists, `EAGER_QI_CHECKED`,")
        w("`EXTRACT_MODULES`), and delete the facade re-exports (`let f = Sub.f` plus")
        w("its `val`) that surviving parents keep for them. Those wrappers are")
        w("themselves dead and already listed below, but they are *syntactic*")
        w("references, so they have to go in the same commit as the module.\n")
        w("| Module | Defs | Area | Referenced in a Makefile |")
        w("| --- | ---: | --- | --- |")
        for m in full_dead:
            refs = subprocess.run(
                ["grep", "-rl", m, "Makefile"] +
                [p for p in ("common/Makefile", "mark-and-sweep/Makefile",
                             "generational/Makefile", "spot/Makefile")
                 if os.path.exists(p)],
                capture_output=True, text=True).stdout.split()
            w(f"| `{m}` | {counts[m][0]} | {area(m)} | "
              f"{', '.join(f'`{r}`' for r in refs) or '—'} |")
        w("")
    if partial:
        n_part = sum(counts[m][1] for m in partial)
        w(f"### {len(partial)} partially-dead modules ({n_part} definitions)\n")
        w("| Module | Defs | Dead | % | Area |")
        w("| --- | ---: | ---: | ---: | --- |")
        for m in partial:
            nd, nu = counts[m]
            w(f"| `{m}` | {nd} | {nu} | {100*nu//nd} | {area(m)} |")
        w("")

    w("## Full inventory\n")
    w(f"Every one of the {len(rows)} unreachable definitions, grouped by module.\n")
    for m in full_dead + partial:
        nd, nu = counts[m]
        tag = " — **entire module is dead**" if nd == nu else f" — {nu}/{nd} dead"
        w(f"<details>\n<summary><code>{m}</code>{tag}</summary>\n")
        w("| Definition | Kind | Location |")
        w("| --- | --- | --- |")
        for name, kind, loc in sorted(by_mod[m]):
            w(f"| `{name}` | {kind or '—'} | `{loc}` |")
        w("\n</details>\n")

    with open(dest, "w") as f:
        f.write("\n".join(o) + "\n")
    print(f"wrote {dest}: {len(rows)} dead definitions across {len(by_mod)} modules "
          f"({len(full_dead)} fully dead)")


if __name__ == "__main__":
    main()
