#!/usr/bin/env python3
"""Summarise parmark2_bench.sh JSONL files for docs/parallel-mark-prototype2.md.

    parmark2_summarize.py [--prof] results.jsonl [more.jsonl ...]

Per (bench, config), medians over runs of: mark ms per collection, whole
collection ms (do_full_gc) per collection, sweep ms per collection, wall s,
and the speed-up of the mark and of the collection over the sequential
config ("seq") of the same bench.  With --prof, the breakdown of worker time
(runs with VGC_PAR_PROF=1): idle, steal, packet pool (of which lock wait),
the rest (scanning), as % of summed worker time, plus CAS failures per
million claims and steals or packets per collection.
"""
import json, statistics, sys
from collections import OrderedDict

args = sys.argv[1:]
prof = "--prof" in args
args = [a for a in args if a != "--prof"]
rows = []
for p in args:
    with open(p) as f:
        rows += [json.loads(l) for l in f if l.strip()]

groups = OrderedDict()
for r in rows:
    if r.get("rc", 0) != 0:
        continue
    groups.setdefault((r["bench"], r["config"]), []).append(r)


def med(rs, f):
    v = [f(r) for r in rs]
    v = [x for x in v if x is not None]
    return statistics.median(v) if v else None


def per_coll(r, k):
    m = r.get("majors") or 0
    return r[k] / m / 1e3 if m and k in r else None


def fmt(x, f="{:.1f}"):
    return "-" if x is None else f.format(x)


if not prof:
    print("| bench | config | n | majors | mark ms/coll | coll ms/coll | sweep ms/coll | wall s | mark speed-up | coll speed-up |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for (b, c), rs in groups.items():
        mark = med(rs, lambda r: per_coll(r, "mark_us"))
        coll = med(rs, lambda r: per_coll(r, "full_gc_us"))
        sw = med(rs, lambda r: per_coll(r, "coll_sweep_us"))
        base = groups.get((b, "seq"))
        bm = med(base, lambda r: per_coll(r, "mark_us")) if base else None
        bc = med(base, lambda r: per_coll(r, "full_gc_us")) if base else None
        su = bm / mark if bm and mark else None
        sc = bc / coll if bc and coll else None
        print(f"| {b} | {c} | {len(rs)} | {fmt(med(rs, lambda r: r.get('majors')), '{:.0f}')} | {fmt(mark, '{:.2f}')} | "
              f"{fmt(coll, '{:.2f}')} | {fmt(sw, '{:.2f}')} | {fmt(med(rs, lambda r: r['wall_s']), '{:.2f}')} | "
              f"{fmt(su, '{:.2f}')} | {fmt(sc, '{:.2f}')} |")
else:
    print("| bench | config | mark ms/coll | idle % | steal % | pool % (lock wait %) | scan % | CAS fail /M claims (lost, neighbour) | steals ok/coll (tries) | packets pub/coll (shares) | lock contended % | thread start+join ms/coll |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for (b, c), rs in groups.items():
        r = rs[0]
        m = r.get("majors") or 1
        tot = r.get("worker_us")
        if not tot:
            continue
        idle, steal, pool, lw = (r.get(k, 0) for k in ("idle_us", "steal_us", "pool_us", "lock_wait_us"))
        # par_mark.c (O) reports lock_wait/hold, counter and idle instead
        if "steal_us" not in r:
            pool = r.get("lock_wait_us", 0) + r.get("lock_hold_us", 0) + r.get("cnt_us", 0)
            lw = r.get("lock_wait_us", 0)
        scan = tot - idle - steal - pool
        cl = r.get("claimed") or r.get("scanned") or 0
        cf = r.get("cas_fail")
        cfs = "-" if cf is None or not cl else f"{cf / cl * 1e6:.0f} ({r.get('cas_lost', 0) / cl * 1e6:.0f}, {r.get('cas_neigh', 0) / cl * 1e6:.0f})"
        st = "-" if "steal_ok" not in r or not r.get("steal_try") else f"{r['steal_ok'] / m:.0f} ({r['steal_try'] / m:.0f})"
        pk = "-" if not r.get("pkt_pub") else f"{r['pkt_pub'] / m:.0f} ({r.get('pkt_share', 0) / m:.0f})"
        if "steal_ok" not in r and r.get("sent"):
            pk = f"{r['sent'] / m:.0f} msgs"
        ln = r.get("lock_n")
        lc = "-" if not ln else f"{r.get('lock_contended', 0) / ln * 100:.0f}"
        thr = sum(r.get(k, 0) for k in ("start_lat_us", "join_lat_us")) / m / 1e3
        print(f"| {b} | {c} | {r['mark_us'] / m / 1e3:.2f} | {idle / tot * 100:.0f} | {steal / tot * 100:.0f} | "
              f"{pool / tot * 100:.0f} ({lw / tot * 100:.0f}) | {scan / tot * 100:.0f} | {cfs} | {st} | {pk} | {lc} | {thr:.2f} |")
