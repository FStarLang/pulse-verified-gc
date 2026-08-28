# SPOT Status: Small Proof-Oriented Test for Generational GC

Read about SPOTs here:
https://risemsr.github.io/blog/2026-04-16-spotting-specs/

## Goal

Build a **truly admit/assume-free SPOT** that validates:

1. **GC preconditions are not too strong**: All 11 preconditions for `minor_collect_full` can be satisfied by constructing a small, concrete heap (major + minor) using allocator APIs
2. **GC postconditions are useful**: The isomorphism postcondition is strong enough to prove meaningful properties about the result (e.g., unreachable objects are collected, reachable objects are promoted, pointers are forwarded correctly)

The SPOT should demonstrate a complete end-to-end workflow:
- Start with empty heaps
- Allocate objects in major and minor heaps
- Wire up pointer relationships
- Prove all 11 GC preconditions hold
- Call `minor_collect_full`
- Extract the result and prove postcondition properties from the isomorphism

I want objects

* A in the minor heap
* B in the minor heap (unreachable)
* C in the major heap with a pointer to A

And I want to prove that this heap is well-formed for calling gen_gc.

And then prove that after calling gen_gc, A is promoted to an object A' in the major heap, C points to A', and B is collected.

The constructive witness below validates that the collector contracts are usable
on a concrete heap, not just on abstract heaps satisfying assumed predicates.

## Current State

The top-level `spot/` campaign has been replaced. The old overlapping modules
with admits/assumes and markdown fragments in `.fst` files were removed from the
active build; historical attempts remain only under `spot/archive/`.

The active SPOT layer is admit/assume-free and verifies locally with:

```bash
cd spot
make verify
```

The local `Makefile` uses `fstar.exe --dep full` to generate `.depend`, so
`make -j` can schedule the `.fsti`/`.fst` files incrementally and in dependency
order. Each active SPOT interface and implementation is checked with
`--z3rlimit 10 --retry 3`, using the same include paths as the
generational development and treating upstream `GC.*` modules as already cached.

## Where to Start

The top-level SPOT is **`GC.SPOT.ConcreteCallFull.call_concrete_gen_gc_spot`**.
It takes nothing but the generational heap holding the A/B/C fixture, allocates
the roots array, forwarding array, Cheney queue, remembered-slot table and a
two-slot gray stack itself, calls the real `gen_gc`, frees everything, and
returns the concrete conclusions: `C` survives, `A` has a promoted image `A'`
that survives, `C.field1` still points to `A'`, and `B` was never promoted.

`GC.SPOT.ConcreteCallMinor.call_concrete_minor_collect_full_spot` is the same
thing one phase earlier, stopping after `minor_collect_full`.

Reading order, each layer using only the ones above it:

| Layer | Modules |
| --- | --- |
| fixture | `Layout`, `ConcreteMinor` (A, B), `ConcreteMajor` (C, free block) |
| contract packaging | `Preconditions`, `Postconditions` |
| scenario | `ThreeObjects` (roots `[C; A]`, slot table `[C.field1]`) |
| pure obligations | `ConcreteForwarding`, `ConcreteScenarios`, `ConcreteFull` |
| resource setup | `ConcreteSetup` |
| generic wrappers | `CallMinor`, `CallFull` |
| concrete wrappers | `ConcreteCallMinor`, **`ConcreteCallFull`** |

Both concrete wrappers also come in a `_borrowed` variant that takes the
arrays, queue, slot table and gray stack as parameters instead of allocating
them, for readers who want to see the resource obligations rather than the
allocation.

## Active Module Structure

- `GC.SPOT.Layout`: names the intended three-object layout. `A` and `B` are
  minor offsets (`a_minor = 8`, `b_minor = 24`) and the module proves their
  basic pointer/distinctness facts.
- `GC.SPOT.ConcreteMinor`: constructs the two-object minor heap by calling the
  real minor allocation spec twice, proves the resulting A/B layout and zero
  fields, and packages the concrete `minor_heap_shape`.
- `GC.SPOT.ConcreteMajor`: constructs the major heap containing C and one blue
  free-list block, proves the C.field1 -> A remembered edge, the object list,
  free-list facts, and the concrete `major_heap_shape`.
- `GC.SPOT.Preconditions`: packages the real `minor_collect_full` and `gen_gc`
  preconditions into named predicates with elimination lemmas. This is only a
  proof boundary; it does not weaken the collector contracts.
- `GC.SPOT.Postconditions`: packages post-minor and post-full consequences.
  It exposes reusable lemmas for promotion from nonzero forwarding, no-promotion
  from zero forwarding, remembered-field rewriting, and final major survival
  from the `gen_gc` isomorphism postcondition.
- `GC.SPOT.ConcreteForwarding`: proves the concrete Cheney forwarding facts.
  The concrete no-OOM obligation is discharged internally by proving root
  coverage and scanned-forwarding closure for C -> A, A's promotion succeeds,
  and the unreachable minor object B's forwarding-map entry remains zero.
- `GC.SPOT.ConcreteScenarios`: connects the concrete A/B/C heaps, roots, slot
  table, and forwarding array to the real `minor_collect_full` and `gen_gc`
  precondition bundles. It proves A is promoted, C.field1 is rewritten to A',
  and B has no promoted image.
- `GC.SPOT.ConcreteFull`: connects the post-minor result to the final `gen_gc`
  postcondition. It proves C survives, A' survives, and C.field1 still points
  to A' in the final major heap.
- `GC.SPOT.ConcreteSetup`: the sequence lemmas that identify freshly allocated
  arrays with the concrete root, forwarding and slot sequences, so the
  concrete wrappers can allocate their own resources.
- `GC.SPOT.CallMinor`: a Pulse wrapper that calls the real
  `minor_collect_full`, taking the packaged precondition and returning the
  packaged postcondition.
- `GC.SPOT.ConcreteCallMinor`: the concrete Pulse minor-collection SPOT. From
  the concrete A/B/C heap resources, root array, forwarding array, Cheney queue,
  and remembered slot table, it derives the real `minor_collect_full`
  precondition, calls it through `GC.SPOT.CallMinor`, and immediately proves
  the useful concrete consequences: A has a promoted image, C.field1 contains
  that image in the post-minor heap, and B has no promoted image.
- `GC.SPOT.CallFull`: a Pulse wrapper that calls the real `gen_gc`.
- `GC.SPOT.ConcreteCallFull`: the concrete Pulse full-GC SPOT. It derives the
  real `gen_gc` precondition from the concrete heap/resources plus the supplied
  post-minor gray stack shape, calls `gen_gc`, and consumes the exported
  `gen_gc` postconditions to prove that a successful final heap contains C and
  A', with C.field1 still pointing to A'.
- `GC.SPOT.ThreeObjects`: the C/A/B scenario layer. Roots are `[C; A]` before
  the minor phase, and the remembered table contains C's field slot. The module
  proves that C and A are combined-graph roots, A is promoted when the real
  precondition bundle holds, C's field is rewritten to A', B is not promoted
  when its forwarding entry is zero, and final `gen_gc` reachability implies
  survival in the final major heap.

## What This Proves

The cleaned campaign now validates the collector proof surface directly:

1. The SPOT calls the real Pulse entry points (`minor_collect_full` and
   `gen_gc`) rather than a model or duplicate implementation. The generic
   wrappers expose the raw contracts, while the concrete wrappers establish
   those contracts for the three-object heap and consume the postconditions.
2. The root set includes `C` pre-minor, so the post-minor major GC has a root
   path that keeps both C and the promoted A' live.
3. The remembered slot layout is explicit: the single remembered slot is C's
   field 1, which contains a minor pointer to A. Field 0 happens to be empty in
   this fixture, but nothing requires that: field 0 is covered by the slot
   table like any other field, and the bridge hypothesis
   `major_field_zero_covered` is discharged from the slot-table preconditions
   rather than assumed. The postcondition proof uses the exported forwarding
   theorem to show that field 1 is rewritten to A's promoted image.
4. B's collection fact is isolated to the exact Cheney execution fact that
   `(cheney_promote ...).fwd_map b_minor == 0UL`, which is now proved for the
   concrete heap and then lifted to "B was not promoted."
5. The concrete Cheney no-OOM precondition is no longer exposed by the concrete
   call connectors. `ConcreteForwarding` proves it once from the three-object
   heap and roots, and the minor/full concrete wrappers call that lemma before
   invoking the generic collector wrappers.
6. The final full-GC connector uses `gen_gc_roots_post`,
   `gen_gc_heap_shape_post`, and
   `gen_gc_reachable_subgraph_isomorphism_post`: C and A' are placed in the
   major mark stack from the rewritten roots, shown reachable in the post-minor
   major heap, and then shown to survive in the final major heap.
7. C.field1 preservation is proved through the exported major-GC live-subgraph
   isomorphism: the post-minor proof establishes that C.field1 contains A', and
   the final proof uses the field-preservation conjunct for reachable object C
   at field index 2 to show the same slot still contains A' after `gen_gc`.
8. The final Pulse layer is imperative: `ConcreteCallMinor` calls
   `minor_collect_full` on concrete resources and `ConcreteCallFull` calls
   `gen_gc` on concrete resources. The full connector now takes an empty gray
   stack with capacity at least two and proves internally that darkening the
   concrete post-minor roots produces the real `gen_gc` major-collection
   precondition.

## Completed Connector

The active SPOT now covers the concrete three-object scenario end to end:

- roots before the minor phase are exactly `[C; A]`;
- the remembered table has exactly one slot, C.field1;
- the concrete heap satisfies the `minor_collect_full` preconditions;
- the concrete Cheney no-OOM proof is derived from the layout and is not a
  caller precondition of the concrete Pulse connectors;
- the post-minor result promotes A to A', rewrites C.field1 to A', and leaves
  B without a promoted image;
- the post-minor state satisfies the `gen_gc` preconditions from an initially
  empty gray stack with capacity at least two; and
- the final major heap contains both C and A', with C.field1 still pointing to
  A'.

There are no local admits or assumes in the active `GC.SPOT.*` campaign.
The remaining visible preconditions of the concrete call connectors are linear
Pulse resources (heap, roots, forwarding array, Cheney queue, remembered slots,
and an initially empty gray stack). The former stack-shape proof obligation is
now constructed inside the concrete full-GC wrapper.
## Second scenario: an interior (infix) pointer in the major heap

`GC.SPOT.InfixMajor`, `GC.SPOT.InfixPre`, `GC.SPOT.InfixPost` and
`GC.SPOT.InfixCall` audit the *other* end of the specification: the relaxation
of the major-heap invariant that admits OCaml interior pointers.

The heap is ten words at `zero_addr`:

```
z + 0   Q's header          wosize 1, tag 0,           White
z + 8   Q                   field 0 = z + 48  <-- the interior pointer
z + 16  P's header          wosize 5, tag closure_tag, White
z + 24  P                   field 0 = 0       (code pointer)
z + 32  P's field 1 = 0     (closinfo)
z + 40  H's header          wosize 3, tag infix_tag,   White   (= P field 2)
z + 48  H                   field 0 = 0                        (= P field 3)
z + 56  P's field 4 = 0
z + 64  F's header          wosize FW, tag 0,          Blue
z + 72  F                   link word = 0     (free list terminates here)
```

`H` is never enumerated by `objects` — its header sits inside `P`'s body, so
the object walk steps straight over it — yet the live object `Q` points
directly at it. That is exactly the shape a mutually recursive OCaml closure
block produces, and exactly what the retired `no_infix_field_targets` conjunct
of `major_heap_shape` forbade.

The audit has two halves, and the point is that both hold of *the same heap*:

- `spot_infix_violates_no_infix_field_targets` — the heap refutes
  `no_infix_field_targets`, so it was inadmissible under the old invariant;
- `spot_infix_major_heap_shape` — the heap nevertheless satisfies all fifteen
  conjuncts of the current `GC.Gen.HeapInvariant.major_heap_shape`, including
  `well_formed_heap` (via the *resolved*-target formulation of part 2/3, with
  `resolve_object H == P` proved from `infix_addr_conds`), `no_pointer_to_blue`
  (the interior pointer resolves to the White `P`) and `blue_fields_non_infix`.

`GC.SPOT.InfixPre` discharges the rest of `gen_gc`'s precondition. The nursery
is `GC.Gen.MinorHeap.minor_reset`, so the minor side is vacuous and the
remembered table is empty — `spot_infix_ref_table_covers` proves that no field
of this heap holds a minor pointer, the interior pointer included. It also
proves `~(cheney_oom ...)`: there is nothing to promote.

`GC.SPOT.InfixCall` then calls the real `gen_gc`. Its postcondition records
that

- the collection succeeds (`snd res == true`), from `gen_gc`'s
  `not ok ==> cheney_oom` and the no-OOM proof above;
- `GC.Gen.HeapInvariant.collection_heap_shape` — literally the predicate the
  precondition demands — holds again of the returned state;
- the nursery handed back is the reset one; and
- `Q` is still an enumerated object of the post-collection major heap.

Together these say that the relaxation is real: a heap with a genuine OCaml
interior pointer is accepted by `gen_gc`, collected, and handed back satisfying
the same invariant, with the root still live.

## `GC.SPOT.MinorInfix` — interior pointers in the nursery

The nursery counterpart of `GC.SPOT.InfixMajor`, added with the Phase E
relaxation that let interior (infix) pointers into the minor heap.

It fixes a scenario `minor_infix_scenario minor major fp roots slots n c i`:
the standard minor-collection context, plus the fact that field `i` of major
object `c` holds an address *interior to* a nursery closure.

- `spot_minor_infix_admissible` — the scenario satisfies the collector's entry
  invariant: the enclosing nursery object is a real `minor_objects` member with
  `Closure_tag`, and the interior address lies strictly inside it.
- `spot_minor_infix_promoted` — after the collection the closure is promoted,
  the interior address is forwarded to an interior pointer of the post heap at
  the same offset (OCaml's `*p += offset`), the major field is rewritten to
  that interior image, and the post-collection graph still carries the edge
  `c -> promoted closure`, because the graph resolves interior pointers.
- `spot_minor_infix_was_forbidden` — reproduces the clause deleted from
  `collection_heap_shape` and derives `False` from it plus the scenario, so the
  scenario is exactly what the old restriction ruled out.

This module quantifies over an abstract nursery; the concrete witness is
below.

## `GC.SPOT.MinorInfixHeap` / `MinorInfixPre` / `MinorInfixCall` — a concrete major-to-nursery interior pointer

`GC.SPOT.MinorInfix` proves the theorems, but over an abstract nursery, and for
a while it could not do better: `minor_alloc_spec` writes only a header and
leaves the body zero, so no sequence of allocations can produce a nursery
containing an infix header, and `GC.Gen.MinorHeap` exposed no other way to build
a minor state.

That was a limitation of the *spec-level* constructors, not of the collector.
Nursery infix headers are supported: `minor_infix_wf` constrains them and
`resolve_minor` interprets them. `minor_alloc_spec`'s `tag <> 249` only rules
out allocating a block whose own header is `Infix_tag`, which mirrors OCaml
exactly — `CLOSUREREC` (`runtime/interp.c:575`) makes one
`Alloc_small(blksize, Closure_tag)` for a whole mutually recursive group and
then stores the infix headers into the block's *body*, so `Alloc_small` is never
called with `Infix_tag`. These three modules close the gap by building the
nursery the way the mutator does, word by word.

`GC.SPOT.MinorInfixHeap` is the nursery. It is laid out exactly as `CLOSUREREC`
(`runtime/interp.c:575-610`) lays out a two-function mutually recursive group:

```
byte  0 : header   wosize 3, tag 247 (Closure_tag)        word 3319
byte  8 : field 0                          <- the closure, `Layout.a_minor`
byte 16 : field 1 = infix header, wosize 2, tag 249       word 2297
byte 24 : field 2                          <- the infix,   `Layout.b_minor`
byte 32 : bump
```

The chain walk steps from byte 0 straight to the bump, so `minor_objects` is the
singleton `[8]` and the infix header at byte 16 is a *body* word. The infix
wosize is not a size: it is the byte offset back to the closure divided by
eight, so `2` means "my parent is 16 bytes below me". Note that 2297 is not
eight-aligned, so neither `GC.Spec.HeapGraph.is_pointer_field` nor
`GC.Gen.Promote.is_minor_pointer` accepts it — that is what makes an infix
header safe to store inside a scanned block. Checking this nursery against
`minor_wf` needs the chain walk's defining equations, which is why
`GC.Gen.MinorHeap` now exports `minor_objects_from`, `minor_objects_from_zero`,
`minor_chain_walk_stop` and `minor_chain_walk_step`.

`GC.SPOT.ConcreteMajorInfix` is the major heap: the same two-object heap as
`GC.SPOT.ConcreteMajor` (both are instantiations of the new
`GC.SPOT.ConcreteMajorGen`, which is generic in the stored nursery pointer),
except that field 1 of the live object `c` holds `24` — a pointer into the
*middle* of the nursery closure — rather than `8`. That the two share one
construction and one set of proofs is the point: a nursery pointer is opaque to
the major heap, so storing an interior one changes nothing about its shape.

`GC.SPOT.MinorInfixPre` discharges `gen_gc`'s precondition for that pair, with
roots `[c; 24]` and a one-entry remembered set holding the address of `c`'s
field 1. The interior address has to be a root: `remembered_targets_in_roots`
demands that every minor value reachable through the remembered set also appear
in the root set, so this SPOT exercises interior *roots* as well as interior
fields. `roots_valid_for_minor_collection` admits the interior root because
Phase H.2 routed it through `resolve_minor`, which names the closure at byte 8.

- `spot_mi_field_is_interior` — the value in `c`'s field 1 really is an infix
  address of the nursery, is *not* itself an enumerated object, and resolves to
  the closure.
- `spot_mi_collection_heap_shape` / `spot_mi_gen_gc_pre` — the entry invariant,
  and the full precondition, hold of this heap.
- `spot_mi_was_forbidden` — the clause Phase H deleted from
  `collection_heap_shape` is *false* of this heap. Together with the previous
  item this is the non-vacuity statement: not merely a heap the collector
  accepts, but exactly a heap the collector used to reject.

`GC.SPOT.MinorInfixCall` runs the real `gen_gc` on it. Its postcondition records
that `collection_heap_shape` is restored, the nursery comes back zeroed, and the
root array has been rewritten to the Cheney-collected roots. It deliberately
does not pin `snd res == true`: `gen_gc` reports failure only on a concrete
out-of-memory event, and ruling that out for a nursery with live content is a
separate and much larger obligation (`GC.SPOT.ConcreteForwarding` spends 600
lines on it for the two-object nursery) that is orthogonal to the question this
SPOT answers.

## `GC.SPOT.NoScanMajor` — a no-scan object whose bytes spell a heap address

The non-vacuity witness for the *other* invariant relaxation: dropping
`GC.Spec.Fields.no_scan_invariant` from `gen_gc`'s major-heap precondition.

`no_scan_tag` is 251, and blocks at or above it are strings, `Bytes.t`,
`Bigarray` payloads and custom blocks. Their contents are arbitrary bytes by
construction, so eight consecutive bytes of a string may perfectly well spell an
eight-aligned in-range heap address — `Bytes.set` will do it on request. The old
invariant said that never happens, which made every real OCaml heap containing a
string inadmissible. Nothing reported it, because no spec-level operation can
*build* a no-scan object: the allocator hands back White/tag-0 blocks, and
`sweep_object` never changes a tag, so the only way one enters the model is
through the initial heap.

The heap is four words at `zero_addr`:

```
z + 0   S's header    wosize 1, tag 251 (no_scan_tag), White
z + 8   S             body word = z + 32   <-- pointer-shaped, and pointing
                                               into the middle of the free block
z + 16  F's header    wosize FW, tag 0,               Blue
z + 24  F             link word = 0        (free list terminates here)
```

`z + 32` is eight-aligned and inside the heap, so
`GC.Spec.HeapGraph.is_pointer_field` accepts it, but it is neither an enumerated
object nor an infix address — it is a word in the interior of the free block.
Under the old part 2 it therefore had to be excluded, and `no_scan_invariant` is
what excluded it.

Both halves are proved of the same heap:

- `spot_ns_violates_no_scan_invariant` — the heap refutes
  `GC.Spec.Fields.no_scan_invariant`, so it was inadmissible before;
- `spot_ns_major_heap_shape` — the heap nevertheless satisfies every conjunct of
  `GC.Gen.HeapInvariant.major_heap_shape`, including `well_formed_heap` (parts 2
  and 3 are now guarded by `fields_constrained`, which skips `S` entirely),
  `no_pointer_to_blue` (likewise), and the clause that replaced
  `no_scan_invariant`, `GC.Gen.Promote.blue_fields_closed` — supplied here by
  proving `GC.Spec.Fields.blue_blocks_scannable` pointwise and calling
  `GC.Gen.PromoteUpdate.BlueAlloc.wfh_part2_implies_blue_fields_closed`.

The nursery analogue `GC.Gen.Promote.minor_no_scan_invariant` has since been
removed as well: the Cheney scan window is now
`GC.Gen.MinorHeap.minor_scan_wosize`, which is 0 for a tag >= 251 object, so
nothing is assumed about young no-scan bodies either.  See
`docs/no-scan-support-plan.md` §10.  That relaxation *did* change the extracted
C --- it was covering a real bug, reproduced by
`generational/ocaml-integration/tests/nursery_no_scan_interior.ml`.

## `GC.SPOT.NoScanMinor` — a young no-scan block whose body spells a nursery address

The nursery analogue of the previous SPOT, and the witness for deleting
`GC.Gen.Promote.minor_no_scan_invariant` from `gen_gc`'s precondition.

The nursery is three words:

```
byte  0   header       wosize 2, tag 251 (no_scan_tag)
byte  8   field 0      = 8   <-- passes the collector's nursery-pointer test
byte 16   field 1      = 8
byte 24   bump
```

`8` is chosen for two reasons. It satisfies `GC.Gen.Promote.is_minor_pointer`
(`8 <= v < minor_heap_size && v % 8 = 0`) — that predicate is the *whole* of the
runtime test the Cheney scan applies to a body word, so before the fix the
collector would have forwarded this word — and its upper 54 bits are zero, so it
has wosize 0 and cannot pose as an object header. That keeps the two surviving
mutator assumptions, `minor_guards_complete` and `minor_infix_wf`, true of the
same heap: nothing here masquerades as an object start, and no address carries
`Infix_tag`.

- `spot_ns_minor_was_forbidden` — the nursery refutes the deleted clause
  (restated verbatim in the interface as `deleted_minor_no_scan_invariant`), so
  it was inadmissible before;
- `spot_ns_minor_heap_shape` / `spot_ns_collection_heap_shape` — it nevertheless
  satisfies `GC.Gen.HeapInvariant.minor_heap_shape`, and the full entry
  invariant `collection_heap_shape` against `GC.SPOT.ConcreteMajor`'s major
  heap. The scan window is empty (`spot_ns_nursery_scan_window_empty`), which is
  what makes `minor_major_fields_no_blue` — narrowed to `minor_scan_wosize` in
  the same change — hold without saying anything about the forged words.

One incidental fact falls out and is exported as
`forged_word_not_major_pointer`: the two halves of the deleted invariant were
never simultaneously refutable. `GC.Spec.HeapGraph.is_pointer_field` demands
`v >= zero_addr + 8`, and `GC.Spec.Base.zero_addr_above_2048` gives
`zero_addr >= 2048 == minor_heap_size`, while `is_minor_pointer` demands
`v < minor_heap_size`. The ranges are disjoint, so refuting either half refutes
the conjunction.
