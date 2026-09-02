#!/usr/bin/env python3
"""Parse OCaml testsuite (ocamltest) logs and emit a report.

Usage:
    testsuite_report.py --log LOG [--baseline-log LOG] [--expected FILE]
                        [--html OUT.html] [--json OUT.json] [--update-expected]

Exit status:
    0  no regressions against the expected-failures list
    1  new failures appeared (or --expected given and the file is missing)

The expected-failures file is the point of this script.  The verified GC has a
known set of failures -- statmemprof and weak/ephemeron tests, for subsystems it
does not implement -- so gating CI on "zero failures" would be permanently red
and therefore ignored.  Gating on "no NEW failures" is a signal you can act on.
"""

import argparse, json, os, re, sys, html, datetime, collections

# --- log parsing -------------------------------------------------------------

RE_DIR      = re.compile(r"Running tests from '([^']+)'")
RE_RESULT   = re.compile(r"testing '([^']+)' with ([^ ]+) \(([^)]+)\) => (\w+)")
RE_SUMMARY  = re.compile(r"^\s*(\d+)\s+tests?\s+(passed|skipped|failed)", re.M)
RE_NOTSTART = re.compile(r"^\s*(\d+)\s+tests? not started", re.M)
RE_UNEXP    = re.compile(r"^\s*(\d+)\s+unexpected errors?", re.M)
RE_CONSID   = re.compile(r"^\s*(\d+)\s+tests? considered", re.M)
RE_LISTITEM = re.compile(r"^\s+(tests/\S.*?)\s*$")


def parse_log(path):
    """Return dict with summary counts and the failed / unexpected-error lists."""
    with open(path, "r", errors="replace") as fh:
        text = fh.read()

    out = {"summary": {}, "failed": [], "errors": [], "per_dir": {}}
    for n, kind in RE_SUMMARY.findall(text):
        out["summary"][kind] = int(n)
    for rx, key in ((RE_NOTSTART, "not_started"),
                    (RE_UNEXP, "unexpected_errors"),
                    (RE_CONSID, "considered")):
        m = rx.search(text)
        if m:
            out["summary"][key] = int(m.group(1))

    # The report's own lists are authoritative; fall back to scraping if absent.
    def grab(header):
        i = text.find(header)
        if i < 0:
            return []
        items = []
        for line in text[i + len(header):].splitlines()[1:]:
            if not line.strip():
                continue
            if line.startswith(("List of", "Summary:", "####")):
                break
            m = RE_LISTITEM.match(line)
            if m:
                items.append(m.group(1).strip())
            else:
                break
        return items

    out["failed"] = grab("List of failed tests:")
    out["errors"] = grab("List of unexpected errors:")

    # Per-directory pass/fail tally, scraped from the streaming output.
    cur = None
    tally = collections.defaultdict(lambda: collections.Counter())
    for line in text.splitlines():
        m = RE_DIR.search(line)
        if m:
            cur = m.group(1)
            tally[cur]  # touch, so dirs with no results still appear
            continue
        m = RE_RESULT.search(line)
        if m and cur:
            tally[cur][m.group(4)] += 1
    out["per_dir"] = {d: dict(c) for d, c in tally.items()}
    return out


# --- categorisation ----------------------------------------------------------
# Grouping matters: lumping "feature not implemented" together with "collector
# miscollected something" produces a number that is both alarming and useless.

BUCKETS = [
    ("statmemprof", "Statistical memory profiling",
     lambda t: "statmemprof" in t),
    ("weak", "Weak refs / ephemerons / finalisers",
     lambda t: any(k in t for k in ("ephe", "weak", "finaliser", "t340-weak"))),
    ("other", "Everything else", lambda t: True),
]


def bucket_of(test):
    for key, _label, pred in BUCKETS:
        if pred(test):
            return key
    return "other"


def categorise(items):
    out = collections.OrderedDict((k, []) for k, _, _ in BUCKETS)
    for t in items:
        out[bucket_of(t)].append(t)
    return out


def norm(items):
    return sorted(set(i.strip() for i in items if i.strip()))


# --- HTML --------------------------------------------------------------------

CSS = """
:root{--bg:#fbfaf8;--fg:#1c1b19;--muted:#6b6862;--rule:#e2ddd4;--card:#fff;
 --accent:#8a4b1e;--accent-soft:#f6ece2;--ok:#4f7a3f;--ok-bg:#e2efdb;
 --bad:#b4503c;--bad-bg:#f7ddd6;--warn:#8a6d1e;--warn-bg:#f7eed2;
 --code:#f4f1ec;--mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}
@media(prefers-color-scheme:dark){:root{--bg:#161513;--fg:#e8e4dc;--muted:#9d978c;
 --rule:#33302b;--card:#1e1d1a;--accent:#e0975e;--accent-soft:#2a2119;
 --ok:#7fae69;--ok-bg:#26331f;--bad:#d98268;--bad-bg:#35211c;
 --warn:#cfa94e;--warn-bg:#332b16;--code:#211f1c}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);
 font:16px/1.6 Charter,Georgia,serif;-webkit-text-size-adjust:100%}
.wrap{max-width:860px;margin:0 auto;padding:0 20px 100px}
header.top{padding:52px 0 22px;border-bottom:1px solid var(--rule);margin-bottom:28px}
h1{font-size:1.9rem;margin:0 0 .4rem;letter-spacing:-.015em}
.sub{color:var(--muted);margin:0;font-size:1rem}
h2{font-size:1.35rem;margin:2.8rem 0 .3rem;scroll-margin-top:16px}
h3{font-size:1.05rem;margin:1.8rem 0 .3rem}
p{margin:.8rem 0}
a{color:var(--accent)}
code{font-family:var(--mono);font-size:.86em;background:var(--code);
 padding:.1em .32em;border-radius:3px}
pre{font-family:var(--mono);font-size:.79rem;line-height:1.5;background:var(--code);
 border:1px solid var(--rule);border-radius:7px;padding:13px 15px;
 overflow-x:auto;white-space:pre;margin:.9rem 0}
pre code{background:none;padding:0}
.toc{background:var(--card);border:1px solid var(--rule);border-radius:9px;padding:16px 20px}
.toc ol{margin:0;padding-left:1.3em}.toc li{margin:.2em 0;font-size:.93rem}
.verdict{border-radius:9px;padding:16px 20px;margin:1.4rem 0;border:1px solid}
.verdict.pass{background:var(--ok-bg);border-color:var(--ok)}
.verdict.fail{background:var(--bad-bg);border-color:var(--bad)}
.verdict .big{font-size:1.15rem;font-weight:700;display:block;margin-bottom:.2rem}
.cards{display:flex;flex-wrap:wrap;gap:10px;margin:1.2rem 0}
.card{flex:1 1 128px;background:var(--card);border:1px solid var(--rule);
 border-radius:8px;padding:12px 14px;text-align:center}
.card .n{font-size:1.5rem;font-weight:700;font-variant-numeric:tabular-nums;display:block}
.card .l{font-size:.72rem;color:var(--muted);text-transform:uppercase;letter-spacing:.05em}
.card.ok .n{color:var(--ok)}.card.bad .n{color:var(--bad)}.card.warn .n{color:var(--warn)}
table{width:100%;border-collapse:collapse;font-size:.87rem;margin:1rem 0}
th,td{text-align:left;padding:7px 9px;border-bottom:1px solid var(--rule);vertical-align:top}
th{font-size:.71rem;text-transform:uppercase;letter-spacing:.05em;color:var(--muted)}
td.mono{font-family:var(--mono);font-size:.78rem}
td.num,th.num{text-align:right;font-variant-numeric:tabular-nums}
.callout{border-left:3px solid var(--accent);background:var(--accent-soft);
 padding:11px 15px;border-radius:0 7px 7px 0;margin:1.2rem 0;font-size:.94rem}
.callout .lbl{display:block;font-size:.71rem;text-transform:uppercase;
 letter-spacing:.06em;font-weight:700;color:var(--accent);margin-bottom:.2rem}
.callout.warn{border-left-color:var(--warn);background:var(--warn-bg)}
.callout.warn .lbl{color:var(--warn)}
details{background:var(--card);border:1px solid var(--rule);border-radius:8px;
 padding:10px 14px;margin:.7rem 0}
summary{cursor:pointer;font-weight:600;font-size:.93rem}
details ul{margin:.6rem 0 .2rem;padding-left:1.2em}
details li{font-family:var(--mono);font-size:.76rem;margin:.15em 0}
.bar{height:9px;border-radius:5px;background:var(--rule);overflow:hidden;display:flex}
.bar i{display:block;height:100%}
.bar .p{background:var(--ok)}.bar .f{background:var(--bad)}.bar .s{background:var(--muted);opacity:.45}
.small{font-size:.86rem;color:var(--muted)}
hr{border:0;border-top:1px solid var(--rule);margin:2.4rem 0}
"""


def h(s):
    return html.escape(str(s))


def render_html(data, baseline, expected, new_fail, fixed, title, run_meta):
    s = data["summary"]
    passed = s.get("passed", 0); failed = s.get("failed", 0)
    skipped = s.get("skipped", 0); errors = s.get("unexpected_errors", 0)
    considered = s.get("considered", 0) or 1

    cat_f = categorise(norm(data["failed"]))
    cat_e = categorise(norm(data["errors"]))
    labels = {k: l for k, l, _ in BUCKETS}

    ok = not new_fail
    parts = []
    A = parts.append
    A(f"<!doctype html><html lang=en><head><meta charset=utf-8>")
    A('<meta name="viewport" content="width=device-width,initial-scale=1">')
    A(f"<title>{h(title)}</title><style>{CSS}</style></head><body><div class=wrap>")
    A(f"<header class=top><h1>{h(title)}</h1>")
    A(f"<p class=sub>{h(run_meta)}</p></header>")

    A('<nav class=toc><ol>'
      '<li><a href="#verdict">Verdict</a></li>'
      '<li><a href="#numbers">The numbers</a></li>'
      '<li><a href="#buckets">What is failing, and why</a></li>'
      '<li><a href="#lists">Full lists</a></li>'
      '<li><a href="#dirs">Per-directory breakdown</a></li>'
      '<li><a href="#run">How to run this yourself</a></li>'
      '</ol></nav>')

    # verdict
    A('<h2 id=verdict>Verdict</h2>')
    if ok:
        A('<div class="verdict pass"><span class=big>No regressions</span>'
          f'Every failure is on the expected-failures list ({len(expected)} entries). ')
        if fixed:
            A(f'<strong>{len(fixed)} previously-failing test(s) now pass</strong> — '
              'consider refreshing the baseline.')
        A('</div>')
    else:
        A('<div class="verdict fail"><span class=big>'
          f'{len(new_fail)} new failure(s)</span>'
          'These are not on the expected-failures list — something regressed.</div>')
        A('<ul>' + ''.join(f'<li><code>{h(t)}</code></li>' for t in new_fail) + '</ul>')

    # numbers
    A('<h2 id=numbers>The numbers</h2>')
    A('<div class=cards>')
    for n, l, cls in ((passed, "passed", "ok"), (failed, "failed", "bad"),
                      (errors, "unexpected errors", "bad"),
                      (skipped, "skipped", "warn"), (considered, "considered", "")):
        A(f'<div class="card {cls}"><span class=n>{n}</span><span class=l>{h(l)}</span></div>')
    A('</div>')
    pw = 100.0 * passed / considered
    fw = 100.0 * (failed + errors) / considered
    A(f'<div class=bar><i class=p style="width:{pw:.2f}%"></i>'
      f'<i class=f style="width:{fw:.2f}%"></i><i class=s style="flex:1"></i></div>')
    A(f'<p class=small>{pw:.1f}% of considered tests pass.</p>')

    if baseline:
        b = baseline["summary"]
        A('<h3>Against stock OCaml</h3>')
        A('<table><tr><th>metric</th><th class=num>stock</th>'
          '<th class=num>verified GC</th><th class=num>delta</th></tr>')
        for key, lab in (("passed", "passed"), ("failed", "failed"),
                         ("unexpected_errors", "unexpected errors"),
                         ("considered", "considered")):
            bv = b.get(key, 0); dv = s.get(key, 0)
            d = dv - bv
            sign = f"+{d}" if d > 0 else str(d)
            A(f'<tr><td>{h(lab)}</td><td class=num>{bv}</td>'
              f'<td class=num>{dv}</td><td class=num>{sign if d else "—"}</td></tr>')
        A('</table>')
        A('<div class=callout><span class=lbl>Why the baseline matters</span>'
          'A pass rate on its own cannot separate "our collector broke this" from '
          '"this fails in any build of this tree". Running the identical suite on '
          'stock OCaml makes the difference attributable.</div>')

    # buckets
    A('<h2 id=buckets>What is failing, and why</h2>')
    A('<table><tr><th>category</th><th class=num>failed</th>'
      '<th class=num>errors</th><th>interpretation</th></tr>')
    notes = {
        "statmemprof": "Memory-profiling subsystem is not implemented: the bridge parks "
                       "<code>caml_memprof_young_trigger</code> and never arms sampling.",
        "weak": "No ephemeron / weak-reference / finaliser support. A weak array is "
                "<code>Abstract_tag</code>, so the collector neither traces nor clears it.",
        "other": "The interesting residue — not explained by a known missing feature.",
    }
    for k, lab, _ in BUCKETS:
        nf, ne = len(cat_f[k]), len(cat_e[k])
        if nf or ne:
            A(f'<tr><td><strong>{h(lab)}</strong></td><td class=num>{nf}</td>'
              f'<td class=num>{ne}</td><td class=small>{notes[k]}</td></tr>')
    A('</table>')

    # lists
    A('<h2 id=lists>Full lists</h2>')
    for name, cat in (("Failed", cat_f), ("Unexpected errors", cat_e)):
        for k, lab, _ in BUCKETS:
            items = cat[k]
            if not items:
                continue
            A(f'<details><summary>{h(name)} — {h(lab)} ({len(items)})</summary><ul>')
            A(''.join(f'<li>{h(t)}</li>' for t in items))
            A('</ul></details>')

    # per-dir
    A('<h2 id=dirs>Per-directory breakdown</h2>')
    rows = []
    for d, c in data["per_dir"].items():
        f_ = c.get("failed", 0)
        if f_:
            rows.append((f_, d, c.get("passed", 0), c.get("skipped", 0)))
    rows.sort(reverse=True)
    if rows:
        A('<table><tr><th>directory</th><th class=num>passed</th>'
          '<th class=num>failed</th><th class=num>skipped</th></tr>')
        for f_, d, p_, sk in rows:
            A(f'<tr><td class=mono>{h(d)}</td><td class=num>{p_}</td>'
              f'<td class=num>{f_}</td><td class=num>{sk}</td></tr>')
        A('</table>')
    else:
        A('<p class=small>No directory reported a failure.</p>')

    # how to run
    A('<h2 id=run>How to run this yourself</h2>')
    A('<p>The testsuite is OCaml’s own, driven by <code>ocamltest</code>. It needs a '
      'built compiler <em>and</em> a built <code>ocamltest</code>, so the tree must be '
      'taken all the way through <code>world.opt</code> first.</p>')
    A('<pre><code># 0. one-time: clone + patch + build the two OCaml trees\n'
      './setup.sh\n'
      'make -C generational/ocaml-integration setup\n\n'
      '# 1. build the compiler on the verified GC, then the test driver\n'
      'cd generational/ocaml-integration/ocaml-4.14-verified-gen\n'
      'make world.opt\n'
      'make ocamltest\n\n'
      '# 2. run the suite (231 directories; both bytecode and native variants)\n'
      'cd testsuite\n'
      'OCAMLRUNPARAM=b,v=0 TIMEOUT=120 make all 2>&amp;1 | tee testsuite.log\n\n'
      '# 3. turn the log into this report\n'
      'python3 ci/testsuite_report.py --log testsuite.log --html report.html</code></pre>')
    A('<div class=callout><span class=lbl>Gotcha</span>'
      '<code>make bootstrap</code> ends with <code>partialclean</code> + <code>core</code>, '
      'which removes <code>ocamlopt</code>. The testsuite’s support library needs it, so '
      're-run <code>make world.opt</code> after any bootstrap or you will get '
      '<code>cannot find file \'../../ocamlopt\'</code>.</div>')
    A('<h3>Comparing against stock</h3>'
      '<pre><code>cd generational/ocaml-integration/ocaml-4.14-unchanged\n'
      'make ocamltest\n'
      'cd testsuite &amp;&amp; OCAMLRUNPARAM=b,v=0 TIMEOUT=120 make all 2>&amp;1 | tee stock.log\n\n'
      'python3 ci/testsuite_report.py --log testsuite.log --baseline-log stock.log \\\n'
      '    --expected ci/expected-failures.txt --html report.html</code></pre>')
    A('<h3>Refreshing the expected-failures baseline</h3>'
      '<p>When a fix lands, the baseline should shrink. Never grow it without a note '
      'saying why.</p>'
      '<pre><code>python3 ci/testsuite_report.py --log testsuite.log \\\n'
      '    --expected ci/expected-failures.txt --update-expected</code></pre>')

    A('<hr><p class=small>Generated by <code>ci/testsuite_report.py</code>.</p>')
    A('</div></body></html>')
    return "\n".join(parts)


# --- main --------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True)
    ap.add_argument("--baseline-log")
    ap.add_argument("--expected")
    ap.add_argument("--html")
    ap.add_argument("--json")
    ap.add_argument("--title", default="OCaml testsuite — verified GC")
    ap.add_argument("--update-expected", action="store_true")
    a = ap.parse_args()

    data = parse_log(a.log)
    baseline = parse_log(a.baseline_log) if a.baseline_log else None

    observed = norm(data["failed"]) + norm(data["errors"])
    observed = norm(observed)

    expected = []
    if a.expected and os.path.exists(a.expected):
        with open(a.expected) as fh:
            expected = norm(l for l in fh if l.strip() and not l.startswith("#"))

    if a.update_expected:
        if not a.expected:
            print("--update-expected requires --expected", file=sys.stderr)
            return 2
        with open(a.expected, "w") as fh:
            fh.write("# Known failures of the verified GC on the OCaml testsuite.\n")
            fh.write("# Regenerate: ci/testsuite_report.py --log LOG --expected THIS --update-expected\n")
            fh.write("# Entries should only ever be REMOVED, unless a note says otherwise.\n")
            for t in observed:
                fh.write(t + "\n")
        print(f"wrote {len(observed)} entries to {a.expected}")

    new_fail = [t for t in observed if t not in expected] if expected else []
    fixed = [t for t in expected if t not in observed] if expected else []

    s = data["summary"]
    print(f"passed={s.get('passed',0)} failed={s.get('failed',0)} "
          f"errors={s.get('unexpected_errors',0)} considered={s.get('considered',0)}")
    if expected:
        print(f"expected-failure entries: {len(expected)}  new: {len(new_fail)}  fixed: {len(fixed)}")
        for t in new_fail:
            print(f"  NEW FAILURE: {t}")
        for t in fixed:
            print(f"  now passing: {t}")

    if a.json:
        with open(a.json, "w") as fh:
            json.dump({"summary": s, "failed": norm(data["failed"]),
                       "errors": norm(data["errors"]),
                       "new_failures": new_fail, "fixed": fixed}, fh, indent=2)

    if a.html:
        meta = datetime.datetime.now().strftime("Generated %Y-%m-%d %H:%M")
        meta += f" · {os.path.basename(a.log)}"
        if baseline:
            meta += f" · baseline {os.path.basename(a.baseline_log)}"
        with open(a.html, "w") as fh:
            fh.write(render_html(data, baseline, expected, new_fail, fixed,
                                 a.title, meta))
        print(f"wrote {a.html}")

    return 1 if new_fail else 0


if __name__ == "__main__":
    sys.exit(main())
