# Size-exact major allocation

The major-heap allocator hands out blocks whose header records exactly the
requested size. Before this change it did not, and the error was visible to
OCaml programs. This note covers the bug, the fix, the proofs it took, and
what is still open.

Issue: [#19](https://github.com/FStarLang/pulse-verified-gc/issues/19).
Regression test: `generational/ocaml-integration/tests/alloc_exact_promotion.ml`
(`make -C generational/ocaml-integration/tests correctness`).

## 1. The bug

A free block that is exactly one word longer than the request cannot be
split: a linked free block needs a header and a body word for the link, so a
one-word remainder cannot stay on the free list. The old allocator handed over
the whole block and wrote the header with the **block's** size, not the
requested one. It was a proved property, not a slip:
`alloc_from_block_wosize_lemma` promised only `wz <= wosize <= wz + 1`.

Promotion zeroed the extra word, and the verified collector ignores it
(`is_pointer 0` is false). OCaml does not:

- `Array.length` and the bounds check both read the header, so the object
  appears one field longer and the check allows reading the extra field.
- `Hashtbl` masks indices with `Array.length h.data - 1`, which is only valid
  for power-of-two lengths. A `2^n` bucket array declared as `2^n + 1` can be
  indexed at `2^n`, which reads the 0. `Is_block 0` is true, so it is followed
  to NULL.

That is the native SIGSEGV in OCaml's `tests/ast-invariants` (`ocamlcommon` is
full of hash tables). The direct major path hid the bug because the runtime
rewrites the header after `verified_allocate` returns. Promotion does not; it
copies the header the allocator wrote.

## 2. The fix: right-justify, as stock OCaml does

Stock's `nf_allocate_block` (`runtime/freelist.c`) carves the object from the
**high end** of the free block. The verified allocator now does the same. With
`leftover = block_wz - wz`:

| leftover | result |
|---|---|
| 0 | exact fit: the object's header is the block's header; the block leaves the list |
| 1 | the spare word becomes a header-only fragment (wosize 0, blue, never linked) at the block's address; the object starts one word later; the block leaves the list |
| >= 2 | the block shrinks in place to `leftover - 1` words, keeping its address and its link; the object's header is at `hd + leftover * 8` |

In every case the object declares exactly `wz`. The fragment is reclaimed by
coalescing at the next collection, like any other blue block.

Allocation now requires `wz >= 1` (`GC.Spec.Allocator`, `GC.Impl.Allocator`).
Every caller already guaranteed it except the C bridge's major path, which now
maps a request of 0 to 1 (`verified_gc/alloc_gen.c`). OCaml represents
zero-length blocks as static atoms, so this path is not reached in practice.

## 3. What the proofs establish

The fix needed the free-list invariants stated precisely enough to talk about
a wosize-0 fragment, which the previous ones could not.

| claim | where |
|---|---|
| Sweep never makes an unlinkable (wosize-0) block the list head | `sweep_object`, `GC.Spec.Sweep.fsti` |
| The free list is exactly the blue blocks that can carry a link: `fl_sound` (every list node is such a block) and `fl_complete` (every such block is on the list), together `fl_exact` | `GC.Spec.FreeList.fst` |
| Every heap word is counted exactly once: on a swept heap, allocated + free cells + fragments (in whsize, header included) cover the whole walk; with `fl_complete`, the free cells are exactly the ones on the list, so nothing is free but unreachable | `heap_partition_swept`, `heap_partition_strong`, `GC.Spec.Partition.fst` |
| Allocation is exact, and conserves words: the object gets exactly `wz`, and the remainder plus fragment account for the rest | `alloc_from_block_exact` (`GC.Spec.Allocator.fsti`), `alloc_from_block_accounting` (`GC.Spec.Partition.fst`) |
| The only object an allocation creates is the allocated one | `alloc_from_block_only_new_is_alloc`, `GC.Spec.Allocator.Lemmas.Part2.fst` |
| Coalescing produces a free list that is complete, and the partition holds after it | `coalesce_complete`, `fused_partition`, `GC.Spec.Coalesce.Complete.fst` |
| After a full collection the free list is exact | `coalesce_exact`, `fused_exact`, `GC.Spec.Coalesce.Complete.fst` |

`linkable_heap`, the previous assumption that every blue object is linkable,
is gone. A wosize-0 fragment falsifies it, and it was assumed, never
established.

## 4. What it cost

- **`alloc_spec_new_objects_blue_part1` is weaker.** The new object used to be
  the blue remainder; now it is the white allocated block, so the theorem
  excludes `obj_out`. This follows from the geometry. Its three consumers
  already case-split on `obj_out`.
- **The header frame needs the object off the free list.** The remainder's
  header is rewritten too, so `alloc_spec_read_header_other_part1` requires
  `chain_avoids`. Consumers that derived non-blueness use
  `alloc_spec_preserves_blue_part1`.
- **One shape is guarded.** `alloc_search` rewrites the predecessor's link
  before the block writes. If the predecessor's object address were this
  block's header word (a wosize-0 predecessor), the two would disagree.
  `fl_valid` excludes that; `alloc_search` is total, so its arm also checks
  `prev_fp <> hd`.

Some modules got faster: `GC.Spec.Allocator` went from about 340s to 10s.
`GC.Gen.AllocProps` got slower (about 20s to 54s), almost all of it the new
`alloc_search_preserves_blue` induction.

## 5. Proof-engineering notes

These cost time to learn on this change and apply to the rest of the
codebase:

- **Do not nest opaque applications.** One `alloc_from_block` inside another's
  argument made `GC.Spec.Allocator` take 913s. A transparent mirror of the
  inner value, `alloc_replacement_fp`, bridged by an equation lemma, took it
  to 50s.
- **Keep transparent definitions out of recursive ones,** and do not duplicate
  an arm's body: either multiplies the cost of every unfolding (4s to 304s, and
  22s to 610s, in the two cases hit here). Fold a guard into the arm's
  condition instead.
- **Do not trust `--retry` to separate flakiness from regressions.** A
  deterministic failure looked flaky until it was compared against the branch
  point: a stale term (`make_header block_wz` where the spec now writes
  `make_header wz`) meant the header write never matched. More rlimit cannot
  fix that.
- **Trivial arithmetic fails in large contexts.** Discharge it in a one-line
  private lemma with an empty context (`aligned_distinct`, `add_zero_offset`,
  `block_prev_separated`), not with more rlimit.

## 6. Still open

- **Promotion padding.** `zero_promote_padding` and the lemmas around it now
  zero a word that no longer exists. Removing them changes the extracted C.
- **`heap_objects_dense`** is defined twice (`GC.Gen.Promote.fsti`,
  `GC.Spec.SweepInv.fst`) and should live in `common/spec`.

## 7. When allocation may fail

`verified_allocate` raises `Out_of_memory` only after a failed allocation, a
full collection, and a second failed allocation. `GC.Spec.Allocator.Oom`
proves what that second failure means:

| lemma | says |
|---|---|
| `alloc_spec_oom_no_fit` | if `alloc_spec` returns no object on a well-formed heap whose free list is valid, terminates and is complete, then every blue block is smaller than the request |
| `fused_oom_no_fit` | the coalescer's output meets those hypotheses, and so does the fused pass's heap, which agrees with it modulo free-block bodies; so on the heap the collector produces (`fused_sweep_coalesce`, under the hypotheses `GC.Impl.fst` discharges), a failed allocation means **no free block anywhere is big enough** |

It does not say the heap is full. Fragmentation can still make an allocation
fail with enough free words in total, spread over blocks that are each too
small. The argument has to rule out the search giving up early: running out of
fuel (`fl_chain_terminates`), stopping at a node the free list would continue
past (objects lie at least a word above `zero_addr`), and bailing on bounds
(a right-justified object lies inside its block, which lies inside the heap).

## 8. Allocation keeps the free list exact

A full collection leaves the free list exact (`fused_exact`).
`GC.Gen.AllocExact` shows allocation keeps it that way:

| lemma | says |
|---|---|
| `alloc_spec_preserves_fl_sound` | after an allocation, everything on the list is still a blue block with room for a link |
| `alloc_spec_preserves_fl_complete` | and every such block is still on the list |
| `alloc_spec_preserves_fl_exact` | the two together |
| `alloc_spec_fits_succeeds` | with an exact free list, an allocation succeeds whenever some free block is big enough |

Soundness follows from what the allocator proofs already show (nothing new
joins the chain, and the allocated object is not on it). Completeness is the
new part: nothing that was on the list falls off it, except the block an
exact fit or a one-word leftover unlinks. The proof follows the search to the
block it allocates from, at depth `k` with `prev` before it, and splits on
where a node `y` sits:

- before the block: the walk to `y` reads no link the allocation changed;
- the block itself: at a split it stays on the list unchanged; otherwise it is
  the allocated object or the fragment, and leaves;
- after the block: the new walk is the old one with the block cut out --
  `prev` now links to `next` -- and termination guarantees the old walk never
  passes `prev` or the block again.

## 9. An allocation succeeds whenever a block fits

The headline is `alloc_succeeds_when_a_block_fits`: from any heap with an
exact free list (`alloc_entry`), after any run of allocations and field
writes to live objects (`run`, `run_ok`), an allocation succeeds whenever
some free block is big enough. The runtime's retry after a collection
(`verified_allocate`) is then needed only when no single free block fits.

An exact free list comes from:

| starting point | lemma |
|---|---|
| a coalesced swept heap | `coalesce_entry` |
| the pass the collector runs | `fused_entry` |
| any heap satisfying the collector's invariant, i.e. anything `gen_gc` or `minor_collect_full` returns | `major_heap_shape_gives_entry` |

The last needs the invariant to carry it: `major_heap_shape`
(`GC.Gen.HeapInvariant`) now includes `fl_exact`, and both collections
re-establish it:

| who changes the major heap | why the free list stays exact |
|---|---|
| full collection (`gen_gc`) | `coalesce_exact` (`GC.Gen.PostCollectionShape`) |
| minor collection: promotion | each `promote_object` is an allocation (§8) followed by writes inside the promoted object (`promote_object_preserves_fl_complete`), carried through the Cheney traversal by `GC.Gen.CheneyFlComplete` |
| minor collection: pointer rewrite | it changes no header and no field of a blue block (`update_major_pointers_preserves_fl_complete`) |
| direct allocation | §8 (`alloc_spec_preserves_entry`) |
| the program's field writes | a write inside a live object's body is no header and no free cell's link (`field_write_preserves_entry`) |

After a minor collection, soundness comes for free from conjuncts the
invariant already had: `fl_valid` (every cell is an object with room for a
link) and `chain_objects_blue` (every cell is blue), via
`fl_valid_cob_gives_sound`.

Two things are assumed rather than proved, as they already are for the rest
of the invariant:

- the program writes only fields of live objects, never a free block;
- the runtime fills a newly allocated object's fields before the next
  collection. Allocation alone does not keep all of `major_heap_shape` --
  until then the new object's fields hold whatever the free block held -- but
  it does keep the free-list part, which is all an allocation needs.
