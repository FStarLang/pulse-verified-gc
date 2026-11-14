#!/usr/bin/env python3
"""Tables for stage P0 (docs/pages-parallel-gc-design.md): medians over the
runs of one tag in _build/proto-results/runs.jsonl.

    summary.py TAG            per program: mark, sweep and whole collection in
                              ms per major collection, and wall time, with the
                              speed-up over the sequential page collector
                              (B2:seq:1, the header mark) in brackets
    summary.py TAG --stats    also BP's pool counters per collection
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "..", "..", "_build", "proto-results", "runs.jsonl")
BASE = os.environ.get("P0_BASE", "B2:seq:1")


def med(xs):
    xs = sorted(x for x in xs if x is not None)
    if not xs:
        return None
    n = len(xs)
    return xs[n // 2] if n % 2 else (xs[n // 2 - 1] + xs[n // 2]) / 2


def short(cfg):
    p = cfg.split(":")
    name = {"VERGC_MARK=bm": "bm", "VERGC_MARK=bp": "bp"}
    mark = "hdr"
    rest = []
    for kv in p[3:]:
        if kv in name:
            mark = name[kv]
        else:
            rest.append(kv.replace("VERGC_", "").lower())
    k = p[2] if p[1] == "par" else "1"
    return f"{mark} k={k}" + (" " + " ".join(rest) if rest else "")


def main():
    tag = sys.argv[1]
    want_stats = "--stats" in sys.argv
    rows = {}
    bad = []
    for line in open(RES):
        r = json.loads(line)
        if r.get("tag") != tag:
            continue
        if not r.get("output_ok"):
            bad.append((r["cfg"], r["prog"], r["rc"], r.get("err_tail")))
            continue
        s = r["stats"] or {}
        n = s.get("majors") or 0
        if not n:
            continue
        d = rows.setdefault(r["prog"], {}).setdefault(r["cfg"], [])
        d.append({"mark": s["mark_ms"] / n, "sweep": s["sweep_ms"] / n, "full": s["full_ms"] / n,
                  "wall": r["wall"], "majors": n, "bal": s.get("par_imbalance"),
                  "share": s.get("share", 0) / n, "pub": s.get("pub", 0) / n,
                  "lock_cont": s.get("lock_cont", 0) / n, "lock_n": s.get("lock_n", 0) / n,
                  "take_fail": s.get("take_fail", 0) / n})
    for prog, cfgs in rows.items():
        base = cfgs.get(BASE)
        bm = {k: med([x[k] for x in base]) for k in ("mark", "sweep", "full", "wall")} if base else {}
        nruns = sorted({len(v) for v in cfgs.values()})
        print(f"\n### {prog} (majors {med([x['majors'] for x in next(iter(cfgs.values()))]):.0f}, "
              f"runs {nruns})\n")
        hdr = "| config | mark ms | sweep ms | collection ms | wall s |"
        if want_stats:
            hdr += " balance | shares | published | lock cont/acq | failed takes |"
        print(hdr)
        print("|" + "---|" * (hdr.count("|") - 1))
        for cfg, xs in cfgs.items():
            m = {k: med([x[k] for x in xs]) for k in ("mark", "sweep", "full", "wall")}

            def cell(k, f="{:.2f}"):
                v = f.format(m[k])
                if bm.get(k):
                    v += f" ({bm[k] / m[k]:.2f})"
                return v
            line = f"| {short(cfg)} | {cell('mark')} | {cell('sweep')} | {cell('full')} | {cell('wall')} |"
            if want_stats:
                st = {k: med([x[k] for x in xs]) for k in ("bal", "share", "pub", "lock_cont", "lock_n", "take_fail")}
                line += (f" {st['bal'] or 0:.2f} | {st['share']:.0f} | {st['pub']:.0f} |"
                         f" {st['lock_cont']:.0f}/{st['lock_n']:.0f} | {st['take_fail']:.0f} |")
            print(line)
    if bad:
        print("\nFailed or wrong output:")
        for b in bad:
            print(" ", b)


main()
