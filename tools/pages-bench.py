#!/usr/bin/env python3
"""Benchmarks of the verified page allocator in the runtime (VERGC_ALLOC=pages)
against stock OCaml 4.14 and main's first-fit collector, bytecode and native.

    tools/pages-bench.py build                 compile every program: .byte with
                                               the stock ocamlc, native with the
                                               stock ocamlopt against each runtime
    tools/pages-bench.py ref                   stock outputs (the reference)
    tools/pages-bench.py campaign TAG [--runs N] [--modes byte,native]
                                  [--configs C,...] [--progs P,...]
        interleaved: for each run, each mode, each program, each config in
        turn, after waiting (up to 120 s) for the 1-minute load average to
        fall below 2.5 (VERGC_BENCH_LOAD)
    tools/pages-bench.py table TAG             markdown tables of the medians

Configs:
    stock          stock OCaml 4.14 (ocaml-4.14-unchanged)
    main-stw       origin/main's runtime, first-fit, VERGC_MAJOR=stw
    pages32        this tree's runtime, VERGC_ALLOC=pages, 32 KB pages
    pages16        this tree's runtime, VERGC_ALLOC=pages VERGC_PAGE_KB=16
    main-inc       origin/main's runtime, VERGC_MAJOR=incremental
    rt-ff          this tree's runtime, VERGC_ALLOC=firstfit (stw): a check
                   that the hook costs nothing against main-stw

main's tree is given by MAIN_INT (its generational/ocaml-integration, with
ocaml-4.14-verified-gen built); Sandmark's sources by SANDMARK (a checkout of
commit 5605805954a0).  Every run's stdout (and minilight's image) must equal
stock's in the same mode, or the run counts as failed.  Wall time is measured
here, peak memory is the child's ru_maxrss (os.wait4), GC time and pauses come
from the verified runtime's own timers (VERGC_MAJOR_STATS=1), stock's major
collections from OCAMLRUNPARAM=v=0x400.  No tool attaches to the process.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INT = os.path.join(ROOT, "generational", "ocaml-integration")
OUT = os.path.join(INT, "_build", "pages-bench")
RES = os.path.join(OUT, "results")
STOCK_BIN = os.path.join(INT, "ocaml-4.14-unchanged", "_install", "bin")
STOCK_RT = os.path.join(INT, "ocaml-4.14-unchanged", "runtime")
RT = os.path.join(INT, "ocaml-4.14-verified-gen", "runtime")
MAIN_INT = os.environ.get("MAIN_INT", "")
MAIN_RT = os.path.join(MAIN_INT, "ocaml-4.14-verified-gen", "runtime") if MAIN_INT else ""
SANDMARK = os.environ.get("SANDMARK", os.path.join(INT, "_build", "sandmark"))
TESTS = os.path.join(INT, "tests")

# name: (major heap words, args, sources, libs).  Sources are relative to
# Sandmark's benchmarks/ ("sm:dir/mod") or to tests/ ("t:mod"), in link order.
# The nine programs and their heaps are those of the allocator comparison
# (docs/allocator-comparison-results.md on sheera/alloc-pages-proto); the
# extras and their heaps are tests/sandmark/benchmarks.txt's on
# sheera/parallel-mark-proto2.
MINI = ["vector3f", "triangle", "spatialIndex", "surfacePoint", "scene",
        "rayTracer", "image", "camera", "minilight"]
PROGS = {
    "hamming":   (16777216,  ["10_000"], ["sm:hamming/hamming"], ""),
    "bt16":      (67108864,  ["16"], ["t:binarytrees"], ""),
    "bt18":      (536870912, ["18"], ["t:binarytrees"], ""),
    "livemap":   (25165824,  ["1000000", "1"], ["t:livemap"], ""),
    "livegraph": (16777216,  ["1000000", "4", "4"], ["t:livegraph"], ""),
    "markbench": (424673280, ["5"], ["sm:markbench/markbench"], "unix"),
    "minilight": (4194304,   ["roomfront5.ml.txt"],
                  ["sm:multicore-minilight/sequential/" + m for m in MINI], ""),
    "bdd":       (9437184,   ["26"], ["sm:bdd/bdd"], ""),
    "fft":       (116391936, [], ["sm:numerical-analysis/fft"], "unix"),
    # extra Sandmark programs
    "kb":            (4194304,  [], ["sm:kb/kb"], ""),
    "kb_no_exc":     (4194304,  [], ["sm:kb/kb_no_exc"], ""),
    "game_of_life":  (9437184,  ["64"], ["sm:multicore-numerical/game_of_life"], ""),
    "sequence_cps":  (4194304,  ["10000"], ["sm:sequence/sequence_cps"], ""),
    "alloc":         (4194304,  ["200_000"], ["sm:simple-tests/alloc"], ""),
    "durand-kerner-aberth": (4194304, ["75"],
                             ["sm:numerical-analysis/durand_kerner_aberth"], ""),
    "stress":        (4194304,  ["100000", "100"], ["sm:simple-tests/stress"], ""),
}
NINE = ["hamming", "bt16", "bt18", "livemap", "livegraph", "markbench",
        "minilight", "bdd", "fft"]
EXTRA = [p for p in PROGS if p not in NINE]
SIDE_FILES = {"minilight": "roomfront5.ml.txt.ppm"}
DATA_FILES = {"minilight": "roomfront5.ml.txt"}
MASK = {"markbench": re.compile(rb"^[0-9.]+ s/gc$", re.M)}

CONFIGS = {
    # name: (runtime, environment)
    "stock":    ("stock", {"OCAMLRUNPARAM": "v=0x400"}),
    "main-stw": ("main", {"VERGC_MAJOR": "stw"}),
    "pages32":  ("rt", {"VERGC_MAJOR": "stw", "VERGC_ALLOC": "pages", "VERGC_PAGE_KB": "32"}),
    "pages16":  ("rt", {"VERGC_MAJOR": "stw", "VERGC_ALLOC": "pages", "VERGC_PAGE_KB": "16"}),
    "main-inc": ("main", {"VERGC_MAJOR": "incremental"}),
    "rt-ff":    ("rt", {"VERGC_MAJOR": "stw", "VERGC_ALLOC": "firstfit"}),
}
DEFAULT_CONFIGS = ["stock", "main-stw", "pages32", "pages16", "main-inc"]


def binary(prog, mode, rt):
    name = "binarytrees" if prog in ("bt16", "bt18") else prog
    if mode == "byte":
        return os.path.join(OUT, "byte", name + ".byte")
    return os.path.join(OUT, "native-" + rt, name + ".exe")


def command(cfg, prog, mode):
    rt = CONFIGS[cfg][0]
    if mode == "byte":
        runner = {"stock": os.path.join(STOCK_RT, "ocamlrun"),
                  "main": os.path.join(MAIN_RT, "ocamlrun"),
                  "rt": os.path.join(RT, "ocamlrun")}[rt]
        return [runner, binary(prog, mode, rt)] + PROGS[prog][1]
    return [binary(prog, mode, rt)] + PROGS[prog][1]


# --- build -------------------------------------------------------------------

def source(spec):
    kind, _, rel = spec.partition(":")
    base = os.path.join(SANDMARK, "benchmarks", rel) if kind == "sm" else os.path.join(TESTS, rel)
    return base


def cmd_build():
    if not os.path.isdir(os.path.join(SANDMARK, "benchmarks")):
        sys.exit(f"no Sandmark checkout at {SANDMARK} (set SANDMARK)")
    if not MAIN_RT or not os.path.exists(os.path.join(MAIN_RT, "libasmrun.a")):
        sys.exit("set MAIN_INT to main's generational/ocaml-integration, runtime built")
    ocamlc = os.path.join(STOCK_BIN, "ocamlc")
    ocamlopt = os.path.join(STOCK_BIN, "ocamlopt")
    targets = [("byte", None), ("native", "stock"), ("native", "main"), ("native", "rt")]
    done = set()
    for prog, (_, _, srcs, libs) in PROGS.items():
        name = "binarytrees" if prog in ("bt16", "bt18") else prog
        if name in done:
            continue
        done.add(name)
        obj = os.path.join(OUT, "obj", name)
        shutil.rmtree(obj, ignore_errors=True)
        os.makedirs(obj)
        files = []
        for s in srcs:
            b = source(s)
            for ext in (".mli", ".ml"):
                if os.path.exists(b + ext):
                    shutil.copy(b + ext, obj)
                    if ext == ".ml":
                        files.append(os.path.basename(b) + ".ml")
        for mode, rt in targets:
            d = os.path.join(OUT, "byte" if mode == "byte" else "native-" + rt)
            os.makedirs(d, exist_ok=True)
            if mode == "byte":
                # dllunix.so from the stock stublibs, without ld.conf lookups
                stub = os.path.join(subprocess.run([ocamlc, "-where"], capture_output=True,
                                                   text=True).stdout.strip(), "stublibs")
                lib = [libs + ".cma", "-dllpath", stub] if libs else []
                cmd = [ocamlc, "-w", "-a"] + lib + ["-o", os.path.join(d, name + ".byte")] + files
            else:
                inc = {"stock": [], "main": ["-I", MAIN_RT], "rt": ["-I", RT]}[rt]
                lib = [libs + ".cmxa"] if libs else []
                cmd = [ocamlopt, "-w", "-a"] + inc + lib + ["-o", os.path.join(d, name + ".exe")] + files
            for f in os.listdir(obj):
                if f.endswith((".cmi", ".cmo", ".cmx", ".o")):
                    os.remove(os.path.join(obj, f))
            subprocess.run(cmd, cwd=obj, check=True)
        print(f"built {name}", flush=True)
    # minilight's 5-pass scene (Sandmark's roomfront.ml.txt with 5 passes),
    # in _build/data.
    for prog, data in DATA_FILES.items():
        src = os.path.join(INT, "_build", "data", data)
        for d in ["byte", "native-stock", "native-main", "native-rt"]:
            shutil.copy(src, os.path.join(OUT, d, data))


# --- runs --------------------------------------------------------------------

def digest(prog, cwd, out_bytes):
    if prog in MASK:
        out_bytes = MASK[prog].sub(b"<time> s/gc", out_bytes)
    h = hashlib.sha256(out_bytes)
    side = SIDE_FILES.get(prog)
    if side:
        with open(os.path.join(cwd, side), "rb") as f:
            h.update(f.read())
    return h.hexdigest()


def parse_stats(err):
    st = {}
    for line in err.splitlines():
        if line.startswith("vergc-major:"):
            for kv in line.split()[1:]:
                k, _, v = kv.partition("=")
                st[k] = int(v) if v.isdigit() else v
        elif line.startswith("vergc-pauses:"):
            pauses = {}
            for kv in line.split()[1:]:
                k, _, v = kv.partition("=")
                n, mean, mx = v.split("/")
                pauses[k] = (int(n), float(mean), float(mx))
            st["pauses"] = pauses
        m = re.match(r"\s*major_collections:\s*(\d+)", line)
        if m:
            st["stock_majors"] = int(m.group(1))
    return st


def run_one(cfg, prog, mode, timeout=1800):
    rt, extra = CONFIGS[cfg]
    cmd = command(cfg, prog, mode)
    cwd = os.path.dirname(cmd[1] if mode == "byte" else cmd[0])
    env = dict(os.environ)
    for k in ["VERGC_MAJOR", "VERGC_SWEEP", "VERGC_ALLOC", "VERGC_PAGE_KB", "OCAMLRUNPARAM"]:
        env.pop(k, None)
    env.update(extra)
    if rt != "stock":
        env["MIN_EXPANSION_WORDSIZE"] = str(PROGS[prog][0])
        env["VERGC_MAJOR_STATS"] = "1"
    side = SIDE_FILES.get(prog)
    if side and os.path.exists(os.path.join(cwd, side)):
        os.remove(os.path.join(cwd, side))
    errf = os.path.join(OUT, "stderr.tmp")
    outf = os.path.join(OUT, "stdout.tmp")
    t0 = time.perf_counter()
    with open(outf, "wb") as fo, open(errf, "wb") as fe:
        p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=fo, stderr=fe)
        deadline = t0 + timeout
        while True:
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid != 0:
                break
            if time.perf_counter() > deadline:
                p.kill()
                pid, status, ru = os.wait4(p.pid, 0)
                status = -1
                break
            time.sleep(0.002)
    wall = time.perf_counter() - t0
    rc = os.waitstatus_to_exitcode(status) if status != -1 else "timeout"
    out = open(outf, "rb").read()
    err = open(errf, "rb").read().decode(errors="replace")
    st = parse_stats(err)
    rec = {"cfg": cfg, "prog": prog, "mode": mode, "rc": rc, "wall": wall,
           "maxrss": ru.ru_maxrss, "stats": st,
           "digest": digest(prog, cwd, out) if rc == 0 else None,
           "err_tail": err.strip().splitlines()[-3:] if rc != 0 else []}
    if st.get("pauses"):
        ps = st["pauses"]
        rec["gc_s"] = sum(n * mean for n, mean, _ in ps.values()) / 1e6
        rec["pause_max_ms"] = max(mx for _, _, mx in ps.values()) / 1e3
        n_all = sum(n for n, _, _ in ps.values())
        rec["pause_mean_ms"] = (rec["gc_s"] * 1e3 / n_all) if n_all else 0.0
    rec["majors"] = st.get("cycles_done", st.get("stock_majors"))
    return rec


def append(name, rec):
    os.makedirs(RES, exist_ok=True)
    with open(os.path.join(RES, name), "a") as f:
        f.write(json.dumps(rec) + "\n")


def ref_digests():
    path = os.path.join(RES, "ref.json")
    return json.load(open(path)) if os.path.exists(path) else {}


def cmd_ref(progs, modes):
    refs = ref_digests()
    for mode in modes:
        for prog in progs:
            r = run_one("stock", prog, mode)
            if r["rc"] != 0:
                sys.exit(f"stock {prog} {mode} failed: {r['err_tail']}")
            refs[f"{prog}:{mode}"] = r["digest"]
            print(f"stock {prog} {mode}: {r['wall']:.2f} s", flush=True)
            os.makedirs(RES, exist_ok=True)
            json.dump(refs, open(os.path.join(RES, "ref.json"), "w"), indent=1)


def wait_idle():
    limit = float(os.environ.get("VERGC_BENCH_LOAD", "2.5"))
    t0 = time.time()
    while os.getloadavg()[0] > limit and time.time() - t0 < 120:
        time.sleep(5)
    return os.getloadavg()[0]


def on_mains():
    try:
        out = subprocess.run(["pmset", "-g", "batt"], capture_output=True, text=True).stdout
        return "AC Power" in out
    except OSError:
        return None


def cmd_campaign(tag, runs, modes, configs, progs):
    refs = ref_digests()
    for i in range(runs):
        for mode in modes:
            for prog in progs:
                for cfg in configs:
                    load = wait_idle()
                    r = run_one(cfg, prog, mode)
                    r.update({"tag": tag, "run": i, "load": load, "ac": on_mains(),
                              "output_ok": r["digest"] is not None and r["digest"] == refs.get(f"{prog}:{mode}")})
                    append("runs.jsonl", r)
                    print(f"[{tag} {i}] {mode:6} {prog:22} {cfg:9} rc={r['rc']} {r['wall']:7.2f} s "
                          f"rss={r['maxrss'] / 2**20:7.1f} MB gc={r.get('gc_s', float('nan')):.3f} s "
                          f"majors={r['majors']} out={'ok' if r['output_ok'] else 'DIFF'} "
                          f"load={load:.1f}", flush=True)


# --- tables ------------------------------------------------------------------

def med(xs):
    xs = sorted(xs)
    if not xs:
        return None
    n = len(xs)
    return xs[n // 2] if n % 2 else (xs[n // 2 - 1] + xs[n // 2]) / 2


def cmd_table(tag):
    rows = [json.loads(l) for l in open(os.path.join(RES, "runs.jsonl"))]
    rows = [r for r in rows if r.get("tag") == tag]
    cfgs = [c for c in list(CONFIGS) if any(r["cfg"] == c for r in rows)]
    progs = [p for p in PROGS if any(r["prog"] == p for r in rows)]
    modes = [m for m in ("native", "byte") if any(r["mode"] == m for r in rows)]
    bad = [r for r in rows if not r.get("output_ok")]
    for r in bad:
        print(f"FAILED: {r['mode']} {r['prog']} {r['cfg']} run {r['run']}: rc={r['rc']} {r['err_tail']}")

    def get(mode, p, c, key):
        xs = [r[key] for r in rows if r["mode"] == mode and r["prog"] == p and r["cfg"] == c
              and r.get("output_ok") and r.get(key) is not None]
        return med(xs), len(xs)

    def f(x, d=2):
        return "–" if x is None else f"{x:.{d}f}"

    for mode in modes:
        for title, key, scale, d, rel in [
                ("Run time, s", "wall", 1, 2, True),
                ("GC time, s (minor + major; stock not measured)", "gc_s", 1, 2, False),
                ("Peak memory (max RSS), MB", "maxrss", 1 / 2**20, 0, True),
                ("Major collections", "majors", 1, 0, False)]:
            print(f"\n### {mode}: {title}\n")
            print("| Program | " + " | ".join(cfgs) + " |")
            print("|---" * (len(cfgs) + 1) + "|")
            for p in progs:
                base = get(mode, p, "main-stw", key)[0]
                cells = []
                for c in cfgs:
                    v, n = get(mode, p, c, key)
                    v = None if v is None else v * scale
                    s = f(v, d)
                    if rel and base and v is not None and c in ("pages32", "pages16", "rt-ff"):
                        s += f" ({(v / (base * scale) - 1) * 100:+.1f}%)"
                    if n and n < 3:
                        s += f" [n={n}]"
                    cells.append(s)
                print(f"| {p} | " + " | ".join(cells) + " |")
        if "main-inc" in cfgs:
            print(f"\n### {mode}: main-inc pauses, ms (longest / mean of all pauses)\n")
            print("| Program | longest | mean |")
            print("|---|---|---|")
            for p in progs:
                print(f"| {p} | {f(get(mode, p, 'main-inc', 'pause_max_ms')[0], 3)} | "
                      f"{f(get(mode, p, 'main-inc', 'pause_mean_ms')[0], 3)} |")


def main():
    a = sys.argv[1:]
    if not a:
        sys.exit(__doc__)

    def opt(name, dflt):
        if name in a:
            i = a.index(name)
            v = a[i + 1]
            del a[i:i + 2]
            return v
        return dflt
    runs = int(opt("--runs", "3"))
    modes = opt("--modes", "native,byte").split(",")
    configs = opt("--configs", ",".join(DEFAULT_CONFIGS)).split(",")
    progs = opt("--progs", ",".join(PROGS)).split(",")
    if a[0] == "build":
        cmd_build()
    elif a[0] == "ref":
        cmd_ref(progs, modes)
    elif a[0] == "campaign":
        cmd_campaign(a[1], runs, modes, configs, progs)
    elif a[0] == "table":
        cmd_table(a[1])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
