# End-to-end correctness: safety and liveness

Module: `mark-and-sweep/impl/GC.Impl.Correct.fst`. Stage 1 contains the
definitions and the statements; every proof is admitted.

The module restructures what the collector guarantees into two named parts:

```
gc_correct : gc_precondition_with_roots h_init st roots fp cap
           /\ collect_post h_init s2 roots fp final_fp
           ==> gc_safe h_init s2 roots /\ gc_live h_init s2 roots fp final_fp
```

- `h_init` is the heap before the collection.
- `s2` and `final_fp` are the heap and free-list head that
  `GC.Impl.collect_with_roots` returns.
- `collect_post` is the pure part of that function's `ensures`, copied word for
  word.

`collect_correct` is a Pulse function that calls `collect_with_roots` and
returns its result, with `gc_safe /\ gc_live` as its postcondition. It is what
ties the statement to the real collector: if `collect_post` drifted from the
real `ensures`, its body would fail to check.

## The heap the clauses talk about

Every clause is stated of `s2`, the heap the shipped fused sweep+coalesce pass
leaves. That heap is not literally `coalesce (sweep h_mark fp)`: the sweep
writes a header and a link into each dead object, the fused pass does not, and
nothing zeroes free blocks (PR #33). The postcondition (`gc_coalesce_source`)
gives only

```
heaps_agree_mod_free s2 (fst (coalesce (sweep h_mark fp)))  /\  final_fp == snd (...)
```

for some `h_mark` satisfying `mark_post`. Agreement means that, block by block
along the walk, the headers are equal, the fields of live blocks are equal, and
the links of free blocks are equal. The rest of a free block is not compared.
Everything below that is proved of the spec heap is carried to `s2` across this
relation.

The postcondition does **not** say `s2 == fst (fused_sweep_coalesce h_mark)`.
`GC.Impl.fst` knows that equation internally, but it never leaves the function.
As a consequence, `fused_partition` and `fused_exact`, which are stated about
`fst (fused_sweep_coalesce h_mark)`, cannot be applied to `s2` directly. The
routes listed below go through the spec heap and `HeapAgree` instead.

## 1. Safety: nothing reachable is lost

`gc_safe h_init s2 roots`:

| Conjunct | In plain words |
|---|---|
| `well_formed_heap s2` | The heap the collector returns is a valid heap: every header, size and pointer field is in range. |
| `full_gc_correctness h_init s2 roots` | The mark was exact: an object was marked if and only if it was reachable. Every marked object survives, ends white, and keeps its successors and every field. Every object of `s2` is white or blue. |
| `major_gc_live_subgraph_isomorphism h_init s2 roots` | Every reachable object survives and is white. Between reachable objects the edges are the same before and after, and so are their fields and successor lists. |

**Status: already proved.** All three come straight from `collect_post`; the
first is reached through `gc_postcondition_elim`. `gc_safe_of_post` states
this.

## 2. Liveness: everything unreachable is reclaimed and reusable

`gc_live h_init s2 roots fp final_fp` is the conjunction of four clauses.

### (a) `unreachable_reclaimed`

> Pick any object `x` in the heap before the collection that is not reachable
> from the roots. Every word it occupied, header and fields, lies inside some
> free (blue) block of `s2`.

The clause is phrased through coverage rather than through `x` itself, because
`x` usually does not survive as an object: coalescing merges it into a larger
free block, and its old header becomes dead space inside that block.

**Status: new.** It is not `major_gc_unreachable_final_blue`, which speaks of
objects of `s2` that are unreachable *in `s2`*, not of objects of `h_init`.
Proof route:

1. `mark_post` pillar 2 says an unreachable `x` is not black in `h_mark`.
   Pillar 2 is guarded by graph well-formedness, which is why `gc_correct`
   needs the precondition.
2. There are no grey objects, so `x` is white or blue. `sweep_white_becomes_blue`
   and `sweep_blue_stays_blue` make it blue in `hs = sweep h_mark fp`, at the
   same size. So every word of `x` is `blue_covered` in `hs`.
3. `coalesce_correct`, clause 3a, carries that coverage to `fst (coalesce hs)`.
4. `HeapAgree.agree_block` carries it to `s2`, since the objects, colours and
   sizes are equal.

Step 2 needs sweep to preserve the size of every object. That lemma exists as
`GC.Spec.SweepCoalesce.sweep_preserves_wosize_all`, but it is `private`. Stage
2 needs it exported, or restated in the new module from the public
`sweep_object_preserves_self_wosize` and `sweep_aux_preserves_wosize_nonmember`.
Making it public is not changing a `val`; it adds one.

### (b) `free_blocks_listed`

> Every free block of `s2` with at least one field is on the free list that
> starts at `final_fp`. The exceptions are blocks with no field at all
> (fragments): they have no room for a link word.

This is `FL.fl_complete s2 final_fp`.

**Status: follows from existing lemmas.** `coalesce_exact` gives
`fl_exact (fst (coalesce hs)) final_fp`; it needs `post_sweep hs`, which comes
from `sweep_post_sweep_strong_gen`. `HeapAgree.agree_fl_exact` carries it to
`s2`. `fused_exact` states the same thing for the fused heap, but it does not
apply to `s2` (see above).

### (c1) `coalescing_lossless`

> `s2` is, up to the contents of free blocks, what coalescing makes of the
> swept heap of a correct mark. Coalescing:
>
> - gained or lost no free word (total free space is the same);
> - left the region covered by free blocks exactly as it was;
> - left no two free blocks side by side;
> - kept every white object where it was, at the same size.

The existential fixes one marked heap `h_mark`. That ties the coalescing facts
to the same witness as `gc_coalesce_source`, rather than to an arbitrary heap
that happens to coalesce into `s2`.

**Status: `coalesce_correct` is proved; the transfer to `s2` is new.**
`coalesce_correct hs` needs `post_sweep_strong hs` (from
`sweep_post_sweep_strong_gen`), and density and a non-empty walk (from
`coalesce_precondition_bridge_gen`). Its four conclusions are about
`fst (coalesce hs)`. Each is a function of the object list, the colours and the
sizes, so `HeapAgree.agree_block` moves them to `s2`.

`fused_agrees_sweep_coalesce` is not used here directly. It is what
`GC.Impl.fst` uses to establish `gc_coalesce_source`, and this statement starts
from that.

### (c2) `heap_partitioned`

> The heap words the walk covers split exactly into three classes:
>
> - live (white) objects;
> - free blocks on the free list;
> - fragments.
>
> There is no fourth class: no free block is lost track of.

This is the statement of `fused_partition` and `heap_partition_strong`, at
`s2` and `final_fp`.

**Status: follows from existing lemmas.** `Part.heap_partition_strong s2
final_fp` needs:

- every object is white or blue, from `gc_postcondition_elim`;
- `fl_complete`, which is clause (b).

The right-hand side is `walk_end s2 zero_addr`, not `heap_size`. The walk can
stop up to one word short of the end of the heap, as in `fused_partition`.

## 3. `gc_correct`

**Status: new**, an assembly of the above. Its hypothesis includes the
collector's precondition, not only its postcondition, because clause (a) needs
graph well-formedness of `h_init`.

## Vacuity checks

These are in the module and are checked on every build:

| Check | What it rules out |
|---|---|
| `gc_correct_hyps_not_false`, under `expect_failure` | Z3 cannot derive `False` from `gc_correct`'s hypotheses. This is the repository's usual check (`mark-and-sweep/NOTES.md`, "Vacuity checking"). If the hypotheses were contradictory, the admitted theorem would be empty. |
| `gc_live_not_from_safe`, under `expect_failure` | Liveness is not a consequence of safety, so `gc_live` adds something. |
| `unreachable_reclaimed_header`, proved | Clause (a)'s guard is not empty: an object's own header word is always in its extent. Clause (a) therefore constrains every unreachable object. |

The first two only show that Z3 cannot prove something. They do not
*construct* a heap that satisfies the hypotheses. A concrete witness would be
stronger: a small heap, its roots, and a proof of `gc_precondition_with_roots`.
I'd propose it for stage 2 if you want one.

The two remaining guards are not empty either:

- Clause (b) quantifies over the free blocks of `s2` with at least one field.
- Clause (c1) is an existential. It is pinned to the same `h_mark` as the
  postcondition's witness, and so cannot be met by an unrelated heap.

## Points for review

1. **Base.** This branch is built on PR #33 (`8c797b3`). PR #33 itself branches
   from `837976c`, which predates the current `origin/main` merges of #27 and
   #32.
2. **`fl_sound` is not in the statement.** Clause (b) is the completeness half
   of `fl_exact`. The soundness half says every block on the free list is a
   free block of `s2`, so the allocator can never hand out a live object. That
   is a safety property. It follows the same way as (b), through
   `agree_fl_exact`, and could be added to `gc_safe`.
3. **No fused equation in the postcondition.** The clauses are stated on `s2`
   through `heaps_agree_mod_free`, as asked. A conjunct
   `s2 == fst (fused_sweep_coalesce h_mark)` could not be derived from
   `collect`'s postcondition without changing a `val`, so it was left out.
