# Sandmark failures on the verified runtime: diagnosis

These are the failures listed under "Excluded" (and hamming's slowdown) in
`generational/ocaml-integration/tests/sandmark/README.md`, diagnosed on the
verified bytecode runtime of `sheera/parallel-mark-proto2`. No code in the
repository was changed.

**Method.** First, each failure was reproduced with the unmodified
`ocamlrun`. Then the same failures were rerun on a *diagnostic* `ocamlrun`,
built in a scratch directory only: a copy of `verified_gc/alloc_gen.c`
relinked against the same `libcamlrun.a`, and for hamming also a copy of the
extracted `GC_Gen_Impl.c`. The scratch build reports the following on stderr:

- for each collection, the block roots per source: `caml_global_data`, stack
  slots, local C roots, global C roots, the finaliser table, memprof, and the
  remembered set. Each count is split into minor, major and other targets, and
  the build keeps counting past `MAX_ROOTS` before it fails;
- after each full GC, a walk of the major heap (live and free words, objects by
  tag) and of the free list (length, block sizes, where the largest block is);
- after each collection, the state of every weak or ephemeron slot;
- the time spent in minor and full collections, with `minor_collect_full`
  split into its steps, and a count of free-list steps.

No tool attached to a running process; everything came from program output.

| Benchmark | What happens | Cause | Missing feature or bug? |
|---|---|---|---|
| stacks (floats-small, floats-large) | root overflow | deep recursion: 268K–304K block-valued stack slots | **bug**: a fixed-size root buffer |
| lazylist.100000_100 | root overflow | deep recursion: 279K block-valued stack slots | **bug**: a fixed-size root buffer (lazy values work) |
| finalise.50 … finalise.100 | root overflow | 263K–299K closures in the finaliser table, which never empties | **missing feature**: finalisers |
| zdd | `Out_of_memory` at any heap size | `Weak.get_copy` reads a key left dangling by the minor GC and asks for a block of 137 billion words | **missing feature** (weak references and ephemerons), and its absence is a **memory-safety bug** |
| hamming | 98.1 s against 0.42 s | first-fit promotion walks 26K–129K one- and two-word holes before reaching the one large free block | **bug** (performance) in the allocator |

## 1. Root overflow: stacks, lazylist, finalise

`alloc_gen.c` copies every root into `root_values[MAX_ROOTS]` (2^18 = 262,144)
before each collection, and aborts with "root overflow" when one more root
arrives. Stock OCaml scans its roots in place and has no such limit. In this
build `NO_NAKED_POINTERS` is defined (`runtime/caml/m.h`), so
`caml_do_local_roots_byt` drops return addresses before they reach the
collector. The measurement confirms it: 0 code pointers were seen among the
roots.

Each failing collection is shown below with its heap at 4M words. The heap size
makes no difference to root counts.

| Run | Collection | Block roots | Stack words | Stack slots | Finaliser table | Remembered set | Other | Distinct targets* |
|---|---|---|---|---|---|---|---|---|
| stacks 100000 floats-small | #20 | 268,324 | 536,637 | 268,319 (minor 1) | 0 | 0 | 5 | 4 |
| stacks 20000 floats-large | #3 | 304,015 | 354,684 | 304,010 (minor 1) | 0 | 0 | 5 | 19 |
| lazylist 100000 100 | #9 | 278,930 | 557,853 | 278,925 (minor 43,691) | 0 | 0 | 5 | 87,383 |
| finalise 50 | #16 | 262,732 | 17 | 4 | 262,723 (minor 16,628) | 0 | 5 | 262,143 |
| finalise 60 | #14 | 282,170 | 17 | 4 | 282,161 | 0 | 5 | 262,143 |
| finalise 70 | #11 | 265,172 | 17 | 5 | 265,162 | 0 | 5 | 262,141 |
| finalise 80 | #10 | 283,068 | 17 | 5 | 283,058 | 0 | 5 | 262,141 |
| finalise 90 | #9 | 294,464 | 17 | 4 | 294,455 | 0 | 5 | 262,143 |
| finalise 100 | #8 | 298,922 | 17 | 5 | 298,912 (minor 37,449) | 0 | 5 | 262,141 |

"Other" is `caml_global_data` (1) plus the global C roots (4). Local C roots,
memprof and the scan hook contributed none. The remembered set (`ref_table`)
never held more than 23 entries. Weak tables are not roots in 4.14: weak
arrays are heap blocks with `Abstract_tag`.

\* Distinct objects among the first 2^18 stored roots.

- **stacks.** `floats_small a0 n = a0 +. (floats_small a0 (n-1)) *. a0` is not
  tail-recursive. Each bytecode frame is 6 words: the return address, `env`,
  `extra_args`, the arguments `a0` and `n`, and `a0` pushed for the
  multiplication. Three of those words are blocks: the closure and two copies
  of the boxed `100.0`. At the overflow, about 89,000 of the 100,000 frames
  are live, giving 268K root slots that point to only 4 objects.
  `floats_large` passes 16 boxed floats, about 17 blocks per frame, and
  overflows at about 18,000 frames deep. The ints variants never collect
  (they allocate nothing), which is why they pass.
- **lazylist.** `add_lazy` is not tail-recursive, and its depth is the list
  length (100,000). Each frame holds `l`, the new lazy cell and the closure.
  Lazy values themselves behave correctly: `lazy_primes` passes, and hamming
  gives stock's output.
- **finalise.** `Gc.finalise` adds an entry to `finalisable_first`.
  `caml_final_do_roots` passes each entry's function as a root. The bytecode
  compiler allocates a fresh closure for `fun n -> …` at every call, so the
  targets are all distinct. The verified runtime never runs finalisers, so it
  never calls `caml_final_update_*` and the table only grows: about
  10,001 × 1,001 × p / 100 entries by the end, 5.0M at p = 50. The overflow
  comes after about 525 of the 10,001 iterations at p = 50, and after 300 at
  p = 100. Even with a larger buffer, the table's closures would stay live
  forever and be rescanned at every minor collection. The table's value
  fields are never updated after promotion either. That is harmless only
  because no finaliser ever runs.

**Missing feature or bug.** stacks and lazylist fail on a bug: the fixed root
buffer is smaller than the stacks stock allows (the default limit is 1M words
of stack). Neither program uses anything unimplemented. finalise fails because
finalisers are missing; root overflow is how it shows.

## 2. zdd: not memory growth, a dangling weak key

zdd hash-conses its nodes in a `Weak.Make` set and memoises in
`Ephemeron.K1.Make` and `Ephemeron.K2.Make` tables. It does not use `Lazy` or
`Gc.finalise`.

- **Stock:** 13.9 s, 821 minor and 17 major collections, `top_heap_words`
  20,834,304. Output `69`.
- **Verified** (88,080,384 words; the failure is the same at every size):
  `Out_of_memory` after 0.16 s. There are 2 minor collections and then 2 full
  collections:

| Collection | Live words | Live objects | Free words | Largest free block |
|---|---|---|---|---|
| full GC #1 | 247,400 | 59,573 | 87,832,984 | 87,681,915 |
| full GC #2 | 239,167 | 57,515 | 87,841,217 | 87,681,915 |

The live set is about 1% of stock's peak, so the heap is not filling up. Both
full collections are triggered by the failing request itself: the 50%
threshold check, then the retry after `allocate` fails. The request is for
**wosize 137,177,947,009**. A second run asked for 137,287,965,569, so the
size is garbage, and no heap size can satisfy it.

With `zdd.ml` rebuilt with `-g` (in scratch), the backtrace is
`Stdlib__Weak.get_copy` ← `Weak.Make.find_or` ← `Zdd.of_word`.
`caml_ephemeron_get_key_copy` allocates a block of `Wosize_val(key)` words to
copy the key into, so the key's "header" is garbage. It points into the minor
heap, which the collection has emptied:

```
[ephediag] after minor GC: 2020 ephemerons, 5162 block slots: 5162 point into
           the (now empty) minor heap ...; ephe_ref_table 5162 entries
```

**The cause.** `WeakSet.merge` stores a freshly allocated (young) node in a
major-heap weak array. `caml_ephe_set_key` records the slot in
`Caml_state->ephe_ref_table`. The verified minor collection reads only
`ref_table`. It never rewrites `ephe_ref_table`'s slots, and it does not scan
`Abstract_tag` blocks. So after every minor collection, every young weak key
and ephemeron key or data value is a dangling pointer into the reset minor
heap. Two secondary defects show up as well:

- weak keys in the major heap are never cleared, so an object that is
  otherwise unreachable is swept while the weak array still points at it;
- `caml_ephe_list_head` still links ephemerons that a full GC has freed.

Nothing walks that list on this runtime yet.

**Missing feature or bug.** Weak references and ephemerons are missing. But
their absence is not merely "`Weak.get` does not track liveness", as
`docs/known-issues.md` puts it. A program that stores a young value in a weak
array or ephemeron reads freed memory after the next minor collection.

## 3. hamming: the allocator, not sleep

The runs were taken one after the other under `caffeinate -i`, with `n` =
10_000, the README's heap (16M words), and output compared. The machine was on
battery. Low Power Mode was on at the start and off by the end (`pmset`), so
these timings are, if anything, slightly favourable to the verified runtime.

| Runtime | Wall | User | Collections | Output |
|---|---|---|---|---|
| stock | **0.42 s** | 0.28 s | 49 minor, 6 major | — |
| verified | **98.10 s** | 95.23 s | 46 minor, 1 major | same as stock |

That is 233× slower, and it is CPU time, not sleep. Lower than the earlier
500× (148.6 s), but real.

**Where the time goes** (diagnostic build, `n` = 10):

| Heap words | Minor GCs | Minor GC time | Full GC time | `scan_loop` | Promotions | Free-list steps past a too-small block |
|---|---|---|---|---|---|---|
| 4,194,304 | 40 | 10.7 s | 0.08 s | 10.6 s | 1,614,988 | 1,195,243,260 |
| 16,777,216 | 40 | 81.2 s | 0.03 s | 84.2 s | 1,614,988 | 3,599,268,121 |

Almost all of the run is promotion. Each promotion's `allocate_part1` skips 740
(4M words) to 2,230 (16M words) blocks on average. After each full collection,
the free list looks like this:

| Heap words | Full GC | Free-list blocks | wosize 1 | wosize 2 | wosize ≥ 3 | Largest block, position in list |
|---|---|---|---|---|---|---|
| 4M | #1 | 25,871 | 12,908 | 12,920 | 43 | 3,316,842 words, **last** |
| 4M | #4 | 38,620 | 19,300 | 19,270 | 50 | 591,255 words, **last** |
| 16M | #1 | 128,854 | 64,316 | 64,351 | 187 | 13,241,495 words, **last** |

Two policies combine to cause this:

1. Allocation is right-justified, so the heap fills from the top down, and the
   large remaining free block lies at the low end.
2. The sweep pushes each flushed block onto the head as it walks up the heap,
   so the list runs from high addresses to low, and that block comes last.

Every promotion of three words or more (hamming's lazy thunks and closures)
then walks past every one- and two-word hole first. A larger heap means a later
first major collection, more holes, and longer walks: 7.6× the time for 4× the
heap. Stock 4.14 uses best-fit with size classes by default, so it never walks
small holes for a large request.

A contributing factor is that the verified collector does not short-circuit
`Forward_tag` blocks, as stock does. Forced lazy cells stay live as
indirections: 70K–301K `Forward` objects across the 4M-word run's full
collections, and 275K at 16M words. Many of the small holes come from the same
lazy machinery.

**Missing feature or bug.** This is a performance bug in the allocator's
free-list policy. Lazy values are supported and correct. Not short-circuiting
`Forward` is a missing optimisation, not a missing feature.
