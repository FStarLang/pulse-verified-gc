#!/usr/bin/env python3
"""Check an OCaml testsuite (ocamltest) log against the expected failures.

Usage:
    testsuite_report.py --log LOG --expected FILE [--baseline-log LOG]
                        [--summary OUT.md] [--title TITLE] [--update-expected]

Prints the counts and every new failure. With --summary, also writes a
markdown summary (for $GITHUB_STEP_SUMMARY) listing every failed test, each
marked NEW or expected.

Exit status:
    0  every failure is in the expected-failures file
    1  new failures appeared
    2  the log has no ocamltest summary (the suite did not finish)

The gate is "no NEW failures", not "zero failures": the verified GC does not
implement weak pointers, ephemerons, finalisers, compaction or statmemprof, so
a known set of tests fails for understood reasons, and a zero-failure gate
would be permanently red.
"""

import argparse, os, re, sys

RE_DIR    = re.compile(r"Running tests from '([^']+)'")
RE_RESULT = re.compile(r"testing '([^']+)' with (\S+) \(([^)]+)\) => (.*)$")
RE_COUNT  = re.compile(r"^\s*(\d+) (tests? passed|tests? skipped|tests? failed|"
                       r"tests? not started|unexpected errors?|tests? considered)\s*$", re.M)
RE_ITEM   = re.compile(r"^\s+(tests/\S.*?)\s*$")


def parse_log(path):
    """Counts, the failed and errored tests, and each test's result line."""
    with open(path, errors="replace") as fh:
        text = fh.read()

    counts = {}
    for n, what in RE_COUNT.findall(text):
        key = "error" if what.startswith("unexpected") else what.split(" ", 1)[1]
        counts[key] = int(n)

    def listed(header):
        i = text.find(header)
        if i < 0:
            return set()
        items = set()
        for line in text[i + len(header):].splitlines()[1:]:
            m = RE_ITEM.match(line)
            if not m:
                break
            items.add(m.group(1))
        return items

    results, cur = {}, None
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = RE_DIR.search(line)
        if m:
            cur = m.group(1)
            continue
        m = RE_RESULT.search(line)
        if m and cur:
            f, var, kind, res = m.groups()
            # "Running program ... : command" carries its exit code on a
            # following line.
            if res.endswith("command"):
                for nxt in lines[i + 1:i + 4]:
                    e = re.search(r"exit code (\d+)", nxt)
                    if e:
                        res = f"exit code {e.group(1)}"
                        break
            results[f"{cur}/'{f}' with {var} ({kind})"] = res

    return {"counts": counts,
            "failed": listed("List of failed tests:"),
            "errors": listed("List of unexpected errors:"),
            "results": results,
            "complete": "tests considered" in text}


def short_result(res):
    """One readable phrase for the Result column."""
    if res.startswith("Timeout"):
        return "timeout"
    m = re.match(r"Process \d+ got signal (\d+)\(([^)]*)\)", res)
    if m:
        return f"crashed: signal {m.group(1)} ({m.group(2)})"
    if "differs from reference" in res:
        return "output differs from reference"
    if res in ("failed ()", "failed"):
        return "failed"
    res = re.sub(r"\S*/_ocamltest/\S*/", "", res)   # drop absolute build paths
    return res[:90] + "…" if len(res) > 90 else res


def read_expected(path):
    """(header, entries): the header is every line before the first entry."""
    header, entries = [], set()
    if os.path.exists(path):
        with open(path) as fh:
            for line in fh:
                s = line.strip()
                if s and not s.startswith("#"):
                    entries.add(s)
                elif not entries:
                    header.append(line.rstrip("\n"))
    return header, entries


def summary_md(title, data, observed, expected, new, fixed, stock):
    c = data["counts"]
    verdict = ("✅ **No new failures**" if not new
               else f"❌ **{len(new)} new failure{'s' if len(new) != 1 else ''}**")
    out = [f"## {title}", "",
           f"{verdict} — {c.get('passed', 0)} passed · {len(observed)} failed "
           f"({len(observed) - len(new)} expected, {len(new)} new) · "
           f"{c.get('skipped', 0)} skipped · {c.get('considered', 0)} considered"]
    if fixed:
        out += ["", f"{len(fixed)} expected failure{'s' if len(fixed) != 1 else ''} "
                    "passed this run. If that holds, remove them from `ci/expected-failures.txt`."]
    if not observed and not fixed:
        return "\n".join(out) + "\n"

    cols = ["Status", "Test", "Result"] + (["Stock OCaml"] if stock is not None else [])
    out += ["", "| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]

    def row(status, t, result):
        cells = [status, f"`{t}`", result.replace("|", "\\|")]
        if stock is not None:
            cells.append("fails too" if t in stock else "passes")
        out.append("| " + " | ".join(cells) + " |")

    for t in sorted(observed, key=lambda t: (t not in new, t)):
        default = "unexpected error" if t in data["errors"] else "failed"
        row("**NEW**" if t in new else "expected", t,
            short_result(data["results"].get(t, default)))
    for t in fixed:
        row("passed", t, "—")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True)
    ap.add_argument("--expected", required=True)
    ap.add_argument("--baseline-log", help="the same suite run on stock OCaml")
    ap.add_argument("--summary", help="append a markdown summary to this file")
    ap.add_argument("--title", default="OCaml testsuite — verified GC")
    ap.add_argument("--update-expected", action="store_true",
                    help="rewrite --expected's entries from this log, keeping its header")
    a = ap.parse_args()

    data = parse_log(a.log)
    if not data["complete"]:
        print(f"{a.log}: no ocamltest summary -- the suite did not finish", file=sys.stderr)
        return 2
    observed = data["failed"] | data["errors"]
    stock = None
    if a.baseline_log:
        b = parse_log(a.baseline_log)
        stock = b["failed"] | b["errors"]

    header, expected = read_expected(a.expected)
    if a.update_expected:
        with open(a.expected, "w") as fh:
            fh.writelines(line + "\n" for line in header + sorted(observed))
        print(f"wrote {len(observed)} entries to {a.expected}")
        expected = observed

    new = sorted(observed - expected)
    fixed = sorted(expected - observed)

    c = data["counts"]
    print(f"passed={c.get('passed', 0)} failed={c.get('failed', 0)} "
          f"errors={c.get('error', 0)} considered={c.get('considered', 0)}")
    print(f"expected: {len(expected)}  new: {len(new)}  now passing: {len(fixed)}")
    for t in new:
        print(f"  NEW FAILURE: {t}")
    for t in fixed:
        print(f"  now passing: {t}")

    if a.summary:
        with open(a.summary, "a") as fh:
            fh.write(summary_md(a.title, data, observed, expected, new, fixed, stock))

    return 1 if new else 0


if __name__ == "__main__":
    sys.exit(main())
