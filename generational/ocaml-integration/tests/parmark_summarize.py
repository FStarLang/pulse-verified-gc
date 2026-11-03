#!/usr/bin/env python3
"""Summarise parmark_bench.sh CSVs: median, min and max per (bench, config).

    parmark_summarize.py results.csv [more.csv ...]
"""
import csv, statistics, sys
from collections import OrderedDict

rows = []
for p in sys.argv[1:]:
    with open(p) as f:
        rows += list(csv.DictReader(f))

groups = OrderedDict()
for r in rows:
    groups.setdefault((r["bench"], r["config"]), []).append(r)

def fl(r, k):
    v = r.get(k) or ""
    return float(v) if v else None

def mmm(vals, scale=1.0, fmt="{:.2f}"):
    vals = [v / scale for v in vals if v is not None]
    if not vals:
        return "-"
    return (fmt.format(statistics.median(vals)) + " (" + fmt.format(min(vals)) + "-" + fmt.format(max(vals)) + ")")

def med(vals):
    vals = [v for v in vals if v is not None]
    return statistics.median(vals) if vals else None

print("| bench | config | n | wall s | mark s | mark % of wall | majors | rounds | fix-ups | fix-up s | sent | dropped | stack ovf | deduped | thread create+start+join ms | max load1 |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for (b, c), rs in groups.items():
    wall = [fl(r, "wall_s") for r in rs]
    mark = [fl(r, "mark_us") for r in rs]
    pct = [m / 1e6 / w * 100 for m, w in zip(mark, wall) if m is not None and w]
    thr = [sum(x for x in (fl(r, "create_us"), fl(r, "start_lat_us"), fl(r, "join_lat_us")) if x is not None) / 1e3
           for r in rs] if rs[0].get("create_us") else []
    def m(k, f="{:.0f}"):
        v = med([fl(r, k) for r in rs])
        return "-" if v is None else f.format(v)
    load = max(fl(r, "load1_before") or 0 for r in rs)
    print(f"| {b} | {c} | {len(rs)} | {mmm(wall)} | {mmm(mark, 1e6)} | {mmm(pct, 1, '{:.0f}')} | {m('majors')} | {m('rounds')} | "
          f"{m('fixups')} | {mmm([fl(r, 'fixup_us') for r in rs], 1e6)} | {m('sent')} | {m('dropped')} | {m('stack_ovf')} | "
          f"{m('deduped')} | {mmm(thr, 1, '{:.1f}') if thr and any(thr) else '-'} | {load:.1f} |")
