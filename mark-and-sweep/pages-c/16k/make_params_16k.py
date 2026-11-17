#!/usr/bin/env python3
"""Rewrite the two parameter modules for 16 KB pages (2048 words), in place:
GC.Spec.Pages.Params picks page_wsize_16k, and GC.Impl.Pages.Params's
literal page size and slot-count table follow (n_slots c = 2048 / cls c).
Every other module sees the parameters as abstract, so nothing else changes.

    make_params_16k.py <root>     (run in a scratch copy of the tree; see
                                   README.md in this directory)
"""
import re, sys
root = sys.argv[1]
CLS = [2,3,4,5,6,7,8,10,12,14,16,17,19,22,25,28,32,33,37,42,47,53,59,65,73,81,89,99,108,118,128]
OLD = {c: 4096 // w for c, w in enumerate(CLS)}
NEW = {c: 2048 // w for c, w in enumerate(CLS)}

def edit(path, f):
    t = open(path).read(); u = f(t)
    assert u != t, path
    open(path, "w").write(u)

def spec(t):
    old = "let page_wsize = page_wsize_32k"
    assert t.count(old) == 1
    return t.replace(old, "let page_wsize = page_wsize_16k")

def impl(t):
    old = "let page_wsize_u64 = assert_norm (page_wsize == 4096); 4096UL"
    assert t.count(old) == 1
    t = t.replace(old, "let page_wsize_u64 = assert_norm (page_wsize == 2048); 2048UL")
    # ns_values: every `n_slots c == v`, statement and assert_norm alike
    def ns(m):
        c, v = int(m.group(1)), int(m.group(2))
        assert v == OLD[c], m.group(0)
        return f"n_slots {c} == {NEW[c]}"
    t, n = re.subn(r"n_slots (\d+) == (\d+)", ns, t)
    assert n == 2 * len(CLS), n
    # n_slots_u64: the match from `let n_slots_u64` to the next blank line
    i = t.index("let n_slots_u64"); j = t.index("\n\n", i)
    body = t[i:j]
    def arm(m):
        c = len(CLS) - 1 if m.group(1) == "_" else int(m.group(1)[:-2])
        assert int(m.group(2)) == OLD[c], m.group(0)
        return f"| {m.group(1)} -> {NEW[c]}UL"
    body, n = re.subn(r"\| (\d+UL|_) -> (\d+)UL", arm, body)
    assert n == len(CLS), n
    return t[:i] + body + t[j:]

edit(f"{root}/mark-and-sweep/spec/GC.Spec.Pages.Params.fst", spec)
edit(f"{root}/mark-and-sweep/impl/GC.Impl.Pages.Params.fst", impl)
print("parameters set to 16 KB pages")
