#!/usr/bin/env python3
"""Runs and measurements for the allocator comparison
(docs/allocator-comparison-results.md).

    tools/proto-bench.py ref                       stock outputs (the reference)
    tools/proto-bench.py run   CONFIG [PROG...] [--runs N] [--heap-scale X]
    tools/proto-bench.py minheap CONFIG [PROG...] [--rel R]
    tools/proto-bench.py campaign TAG CONFIG... -- [PROG...] [--runs N]
        interleaved: for each run, each program, each config in turn, after
        waiting (up to 120 s) for the 1-minute load average to fall below 2;
        PROG@SCALE runs PROG at SCALE x its usual heap
    tools/proto-bench.py summary TAG               markdown tables of medians

CONFIG is RUNTIME[:MODE[:THREADS]], RUNTIME a directory under
generational/ocaml-integration/_build/proto (base, A, B, A-check, B-check) or
`stock`; MODE seq | par | incremental.  Every run's stdout (and minilight's
image) must equal stock OCaml's, or the run counts as failed.  Results are
appended to _build/proto-results/runs.jsonl and minheap.jsonl.  Wall time is
measured here; collection times come from the runtime's own timers
(VERGC_PROTO_STATS).  No tool attaches to the process.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INT = os.path.join(ROOT, "generational", "ocaml-integration")
BENCH = os.path.join(INT, "_build", "bench")
RES = os.path.join(INT, "_build", "proto-results")
STOCK = os.path.join(INT, "ocaml-4.14-unchanged", "runtime", "ocamlrun")

# name: (major heap words, argv) -- the heaps used by the earlier notes
# (tests/Makefile bench-mark; tests/sandmark/benchmarks.txt).
PROGS = {
    "hamming":   (16777216,  ["hamming.byte", "10_000"]),
    "bt16":      (67108864,  ["binarytrees.byte", "16"]),
    "bt18":      (536870912, ["binarytrees.byte", "18"]),
    "livemap":   (25165824,  ["livemap.byte", "1000000", "1"]),
    "livegraph": (16777216,  ["livegraph.byte", "1000000", "4", "4"]),
    "markbench": (424673280, ["markbench.byte", "5"]),
    "minilight": (4194304,   ["minilight.byte", "roomfront5.ml.txt"]),
    "bdd":       (9437184,   ["bdd.byte", "26"]),
    "fft":       (116391936, ["fft.byte"]),
}
ORDER = list(PROGS)
SIDE_FILES = {"minilight": "roomfront5.ml.txt.ppm"}


def runtime(name):
    if name == "stock":
        return STOCK
    p = os.path.join(INT, "_build", "proto", name, "ocamlrun")
    if not os.path.exists(p):
        sys.exit(f"no runtime {p}: run tools/proto-build.sh {name}")
    return p


# Lines that are timings, masked before comparing (markbench prints its own
# seconds per collection).
MASK = {"markbench": re.compile(rb"^[0-9.]+ s/gc$", re.M)}


def digest(prog, out_bytes):
    if prog in MASK:
        out_bytes = MASK[prog].sub(b"<time> s/gc", out_bytes)
    h = hashlib.sha256(out_bytes)
    side = SIDE_FILES.get(prog)
    if side:
        with open(os.path.join(BENCH, side), "rb") as f:
            h.update(f.read())
    return h.hexdigest()


def parse_stats(err):
    for line in err.splitlines()[::-1]:
        if line.startswith("VERGC_PROTO_STATS "):
            d = {}
            for kv in line.split()[1:]:
                k, _, v = kv.partition("=")
                try:
                    d[k] = float(v) if "." in v else int(v)
                except ValueError:
                    d[k] = v
            return d
    return None


def run_one(cfg, prog, words, timeout=None):
    parts = cfg.split(":")
    rt, mode, threads = (parts + ["seq", "4"][len(parts) - 1:])[:3]
    env = dict(os.environ)
    env["MIN_EXPANSION_WORDSIZE"] = str(words)
    env["VERGC_SWEEP"] = mode
    env["VERGC_PAR_SWEEP_THREADS"] = threads
    env["VERGC_PROTO_STATS"] = "1"
    side = SIDE_FILES.get(prog)
    if side and os.path.exists(os.path.join(BENCH, side)):
        os.remove(os.path.join(BENCH, side))
    t0 = time.perf_counter()
    try:
        p = subprocess.run([runtime(rt)] + PROGS[prog][1], cwd=BENCH, env=env,
                           capture_output=True, timeout=timeout)
        rc, out, err = p.returncode, p.stdout, p.stderr.decode(errors="replace")
    except subprocess.TimeoutExpired:
        rc, out, err = "timeout", b"", ""
    wall = time.perf_counter() - t0
    dig = digest(prog, out) if rc == 0 else None
    return {"cfg": cfg, "prog": prog, "words": words, "rc": rc, "wall": wall,
            "digest": dig, "stats": parse_stats(err),
            "err_tail": err.strip().splitlines()[-3:] if rc != 0 else []}


def ref_digests():
    path = os.path.join(RES, "ref.json")
    return json.load(open(path)) if os.path.exists(path) else {}


def append(name, rec):
    os.makedirs(RES, exist_ok=True)
    with open(os.path.join(RES, name), "a") as f:
        f.write(json.dumps(rec) + "\n")


def cmd_ref(progs):
    refs = ref_digests()
    for prog in progs:
        r = run_one("stock", prog, PROGS[prog][0])
        if r["rc"] != 0:
            sys.exit(f"stock {prog} failed: {r['err_tail']}")
        refs[prog] = r["digest"]
        print(f"stock {prog}: {r['wall']:.2f} s", flush=True)
        os.makedirs(RES, exist_ok=True)
        json.dump(refs, open(os.path.join(RES, "ref.json"), "w"), indent=1)


def check_output(r, refs):
    ok = r["rc"] == 0 and r["digest"] == refs.get(r["prog"])
    r["output_ok"] = ok
    return ok


def cmd_run(cfg, progs, runs, scale, tag):
    refs = ref_digests()
    for prog in progs:
        words = int(PROGS[prog][0] * scale)
        for i in range(runs):
            r = run_one(cfg, prog, words)
            check_output(r, refs)
            r["tag"] = tag
            r["i"] = i
            append("runs.jsonl", r)
            s = r["stats"] or {}
            print(f"{cfg:22s} {prog:10s} run {i}: {r['wall']:8.3f} s  rc={r['rc']} "
                  f"out={'ok' if r['output_ok'] else 'DIFF'}  majors={s.get('majors')} "
                  f"sweep_ms={s.get('sweep_ms')} pause_max_ms={s.get('pause_max_ms')}"
                  + ("" if r["rc"] == 0 else f"  {r['err_tail']}"), flush=True)


def cmd_minheap(cfg, progs, rel):
    """Smallest MIN_EXPANSION_WORDSIZE that completes with the right output,
    by bisection to a relative precision `rel` (and a 64K-word floor), from
    the benchmark's usual heap downwards."""
    refs = ref_digests()
    for prog in progs:
        hi = PROGS[prog][0]
        base = run_one(cfg, prog, hi)
        lo = None
        while not check_output(base, refs):
            # fails at its usual heap: grow by 1/4 until it passes
            print(f"  {cfg} {prog} {hi}: fail at or above the usual heap", flush=True)
            if hi > 4 * PROGS[prog][0]:
                print(f"{cfg} {prog}: fails up to {hi} words", flush=True)
                break
            lo, hi = hi, hi + hi // 4
            base = run_one(cfg, prog, hi)
        if not check_output(base, refs):
            continue
        limit = max(120.0, 6 * base["wall"])
        if lo is not None:
            pass                         # bracket [lo fails, hi passes] found
        else:
            lo = hi // 16
        r = run_one(cfg, prog, lo, timeout=limit) if lo < PROGS[prog][0] // 8 else {"rc": 1, "digest": None, "prog": prog}
        if check_output(r, refs):
            print(f"{cfg} {prog}: passes at {lo}; lowering further", flush=True)
            while check_output(r, refs) and lo > 65536:
                hi, lo = lo, lo // 4
                r = run_one(cfg, prog, lo, timeout=limit)
            if check_output(r, refs):
                hi = lo
        steps = []
        while hi - lo > max(65536, int(rel * hi)):
            mid = (lo + hi) // 2
            r = run_one(cfg, prog, mid, timeout=limit)
            ok = check_output(r, refs)
            steps.append((mid, ok, round(r["wall"], 2), r["rc"]))
            if ok:
                hi = mid
            else:
                lo = mid
            print(f"  {cfg} {prog} {mid}: {'ok' if ok else 'fail'} ({r['wall']:.1f} s)", flush=True)
        rec = {"cfg": cfg, "prog": prog, "min_words": hi, "fail_words": lo,
               "usual_words": PROGS[prog][0], "steps": steps, "rel": rel}
        append("minheap.jsonl", rec)
        print(f"{cfg} {prog}: min heap {hi} words (fails at {lo})", flush=True)


def wait_quiet(limit=2.0, max_wait=120):
    t0 = time.time()
    while os.getloadavg()[0] >= limit and time.time() - t0 < max_wait:
        time.sleep(5)
    return os.getloadavg()[0]


def cmd_campaign(tag, cfgs, progs, runs):
    """PROG may be PROG@SCALE: run at SCALE x its usual heap."""
    refs = ref_digests()
    for i in range(runs):
        for spec in progs:
            prog, _, sc = spec.partition("@")
            words = int(PROGS[prog][0] * float(sc or 1))
            for cfg in cfgs:
                load = wait_quiet()
                r = run_one(cfg, prog, words)
                check_output(r, refs)
                r.update(tag=tag, i=i, load=round(load, 2))
                append("runs.jsonl", r)
                s = r["stats"] or {}
                print(f"[{i}] {cfg:16s} {prog:10s} {r['wall']:8.3f} s load={load:.2f} rc={r['rc']} "
                      f"out={'ok' if r['output_ok'] else 'DIFF'} majors={s.get('majors')} "
                      f"sweep_med_ms={s.get('sweep_med_ms')} pause_max_ms={s.get('pause_max_ms')}"
                      + ("" if r["rc"] == 0 else f"  {r['err_tail']}"), flush=True)


def med(xs):
    xs = sorted(x for x in xs if x is not None)
    if not xs:
        return None
    n = len(xs)
    return xs[n // 2] if n % 2 else (xs[n // 2 - 1] + xs[n // 2]) / 2


def cmd_summary(tag):
    """Markdown tables of medians from runs.jsonl (records with this tag)."""
    rows = {}
    for line in open(os.path.join(RES, "runs.jsonl")):
        r = json.loads(line)
        if r.get("tag") != tag:
            continue
        rows.setdefault((r["cfg"], r["prog"]), []).append(r)

    def get(cfg, prog, key):
        rs = rows.get((cfg, prog), [])
        if not rs or not all(x["output_ok"] for x in rs):
            return None
        if key == "wall":
            return med([x["wall"] for x in rs])
        if key == "coll_ms":
            return med([x["stats"]["minor_ms"] + x["stats"]["full_ms"] + x["stats"]["pause_total_ms"]
                        for x in rs])
        return med([x["stats"].get(key) for x in rs])

    def f(x, d=2):
        return "fail" if x is None else f"{x:.{d}f}"

    def pct(a, b):
        return "" if a is None or b is None else f"{100 * (b - a) / a:+.1f}%"

    progs = [p for p in ORDER if any(k[1] == p for k in rows)]
    words = {}
    for (cfg, prog), rs in rows.items():
        words[prog] = rs[0]["words"]
    out = []
    out.append("| Program | heap (M words) | A run s | B run s | B vs A | A coll s | B coll s | A majors | B majors | A mark ms | B mark ms | A sweep ms | B sweep ms |")
    out.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for p in progs:
        ra, rb = get("base", p, "wall"), get("B:seq", p, "wall")
        ca, cb = get("A:seq", p, "coll_ms"), get("B:seq", p, "coll_ms")
        out.append(f"| {p} | {words[p] / 1048576:.0f} | {f(ra)} | {f(rb)} | {pct(ra, rb)} | "
                   f"{f(ca and ca / 1000)} | {f(cb and cb / 1000)} | {f(get('A:seq', p, 'majors'), 0)} | "
                   f"{f(get('B:seq', p, 'majors'), 0)} | {f(get('A:seq', p, 'mark_med_ms'))} | "
                   f"{f(get('B:seq', p, 'mark_med_ms'))} | {f(get('A:seq', p, 'sweep_med_ms'))} | "
                   f"{f(get('B:seq', p, 'sweep_med_ms'))} |")
    out.append("")
    out.append("| Program | A seq | A 1 | A 2 | A 4 | A 4 speedup | A 4 balance | B seq | B 1 | B 2 | B 4 | B 4 speedup | B 4 balance | A4 / B4 |")
    out.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for p in progs:
        a = [get(c, p, "sweep_med_ms") for c in ("A:seq", "A:par:1", "A:par:2", "A:par:4")]
        b = [get(c, p, "sweep_med_ms") for c in ("B:seq", "B:par:1", "B:par:2", "B:par:4")]
        sa = a[0] / a[3] if a[0] and a[3] else None
        sb = b[0] / b[3] if b[0] and b[3] else None
        ab = a[3] / b[3] if a[3] and b[3] else None
        out.append(f"| {p} | " + " | ".join(f(x, 3) for x in a) + f" | {f(sa)}× | {f(get('A:par:4', p, 'par_imbalance'))} | "
                   + " | ".join(f(x, 3) for x in b) + f" | {f(sb)}× | {f(get('B:par:4', p, 'par_imbalance'))} | {f(ab)}× |")
    out.append("")
    out.append("| Program | A max ms | A p99 ms | A total ms | A burst max | A alloc max | A finishes | A run s | B max ms | B p99 ms | B total ms | B burst max | B alloc max | B finishes | B run s |")
    out.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for p in progs:
        cells = []
        for c in ("A:incremental", "B:incremental"):
            cells += [f(get(c, p, "pause_max_ms"), 3), f(get(c, p, "pause_p99_ms"), 3), f(get(c, p, "pause_total_ms"), 1),
                      f(get(c, p, "burst_max_ms"), 3), f(get(c, p, "alloc_max_ms"), 3),
                      f(get(c, p, "finish_n"), 0), f(get(c, p, "wall"))]
        out.append(f"| {p} | " + " | ".join(cells) + " |")
    print("\n".join(out))


def main():
    a = sys.argv[1:]
    if not a:
        sys.exit(__doc__)
    runs, scale, tag, rel = 1, 1.0, "", 0.02
    for flag in ("--runs", "--heap-scale", "--tag", "--rel"):
        if flag in a:
            i = a.index(flag)
            v = a[i + 1]
            del a[i:i + 2]
            if flag == "--runs": runs = int(v)
            elif flag == "--heap-scale": scale = float(v)
            elif flag == "--tag": tag = v
            else: rel = float(v)
    cmd = a[0]
    if cmd == "ref":
        cmd_ref(a[1:] or ORDER)
    elif cmd == "run":
        cmd_run(a[1], a[2:] or ORDER, runs, scale, tag)
    elif cmd == "summary":
        cmd_summary(a[1])
    elif cmd == "campaign":
        sep = a.index("--") if "--" in a else len(a)
        cmd_campaign(a[1], a[2:sep], a[sep + 1:] or ORDER, runs)
    elif cmd == "minheap":
        cmd_minheap(a[1], a[2:] or ORDER, rel)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
