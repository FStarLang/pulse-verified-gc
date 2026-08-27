# Plan: supporting no-scan objects with arbitrary contents

*Status: diagnosed, not yet implemented.*

This is the no-scan analogue of `docs/infix-support-plan.md`. It has the same
shape as that one, and the same root cause: a whole-heap predicate is stronger
than the collector needs, the strengthening is invisible because the
specification's own constructors cannot build a counterexample, and the heaps it
excludes are ones stock OCaml produces constantly.

## 1. What the invariants say

`GC.Spec.Fields.no_scan_invariant`:

```fstar
forall (src: obj_addr) (idx: nat).
  Seq.mem src (objects zero_addr g) /\ is_no_scan src g /\ ~(is_blue src g) /\
  idx < wosize_of_object src g /\ ... ==>
  ~(is_pointer_field (read_word g (src + idx * 8)))
```

`GC.Gen.Promote.minor_no_scan_invariant` is the nursery analogue, and
additionally rules out `is_minor_pointer`.

Both say: *a no-scan object contains no word that looks like a heap pointer.*

## 2. Why this is false of OCaml

`no_scan_tag` is 251. Blocks at or above it are `String_tag`, `Double_array_tag`,
`Abstract_tag` and `Custom_tag` — strings, `Bytes.t`, `Bigarray` payloads,
`Int64`/`Int32`/`Nativeint` boxes, and custom blocks holding C pointers. Their
contents are *arbitrary bytes by construction*. Eight consecutive bytes of a
string may spell an 8-aligned in-range address with no difficulty whatsoever;
`Bytes.set` will do it on request.

So `no_scan_invariant` is not a fact about the mutator. It is a restriction the
collector imposes on its input, and one a real OCaml program violates routinely.

## 3. Why nothing has ever reported it

No spec-level operation can create a no-scan object:

- the allocator recolors the block it hands out to **White, tag 0**
  (`GC.Spec.Allocator.fsti:15`), so allocation never produces `tag >= 251`;
- `sweep_object` writes exactly two things — the colour, and field 1 as the
  free-list link (`GC.Spec.Sweep.fst:58-65`). It never touches the rest of the
  body, and never changes a tag;
- coalescing likewise merges headers.

A no-scan object can therefore only enter the model through the *initial* heap.
Every preservation obligation is discharged against a heap that already
satisfies the invariant, and no proof ever has to construct one. The invariant is
maintainable precisely because the specification cannot exhibit a counterexample
— which is exactly the vacuity `docs/infix-support-plan.md` diagnosed for
interior pointers, in a different clause.

The nursery is the same story: `minor_alloc_spec` writes a header and leaves the
body zero, so no sequence of spec-level allocations puts pointer-looking bytes
into a nursery string either.

## 4. Where the requirement actually comes from

It is *not* needed to justify tracing. On that question the collector and the
graph model already agree:

| | follows a no-scan object's fields? |
|---|---|
| extracted C (`is_scannable = tag < 251 && tag != 249`) | no |
| `GC.Spec.HeapGraph.get_pointer_fields` (`HeapGraph.fst:150`) | no |
| `well_formed_heap_part2` (`Fields.fst:535`) | **yes** |
| `GC.Spec.Mark.no_pointer_to_blue` (`Mark.fsti:227`) | **yes** |

Both offenders go through `exists_field_pointing_to_unchecked`
(`Fields.fst:79`) — the name is accurate: it walks every field of every object
without consulting the tag. `well_formed_heap_part2` uses it directly;
`no_pointer_to_blue` reaches it through `points_to` (`Fields.fst:483`).

So field closure and "no live object points into the free list" are demanded of
words the collector never reads, and `no_scan_invariant` is the assumption that
makes the demand satisfiable. `minor_no_scan_invariant` exists only to carry the
assumption across promotion: `promote_object` copies raw words, so
`promote_object_preserves_no_scan_invariant` (`GC.Gen.Promote.fsti:571`) can
only maintain the major invariant if the nursery already satisfied it. It has no
independent purpose, and cannot be removed on its own.

## 5. Free blocks are cleared, which is what makes the fix possible

An earlier revision of this document claimed that a freed no-scan block keeps
the string's bytes, that `alloc_spec` hands those bytes back as the fields of a
scannable object, and that part 2 must therefore cover blue blocks whatever
their tag. **That is wrong.** The coalescing pass clears free blocks.

`GC.Spec.Coalesce.flush_blue` writes a *fresh* header for the merged run,

```fstar
let hdr = makeHeader wz_u64 Blue 0UL in   (* tag 0, not the corpse's tag *)
let g1  = write_word g hd hdr in
let g2  = HeapGraph.set_field g1 fb 1UL fp in
let g3  = Alloc.zero_fields g2 (fb + mword) (wz - 1) in
```

and `coalesce_aux` flushes *every* blue run, singletons included. So after
coalescing, every blue block has

- **tag 0** --- never `no_scan_tag`; this is already proved, as
  `GC.Spec.Coalesce.coalesce_aux_blue_tag_zero` (`Coalesce.fst:1854`), whose
  existing client is `coalesce_blue_not_infix`;
- **fields 2..wosize all zero**, hence not pointer-shaped;
- **field 1** = the free-list link, an object address.

Part 2's coverage of blue blocks in a coalesced heap therefore costs nothing:
the only pointer-shaped word in a free block is its link. What that coverage
*buys* is exactly that link, because a split leaves it as field 1 of the block
the allocator hands back.

Blue **and** no-scan blocks exist only in the transient post-sweep,
pre-coalesce heap --- `GC.Spec.Sweep.sweep_object` rewrites only the link word
and the colour, so between sweep and coalesce a dead string is blue with its
bytes intact. Those are precisely the objects the relaxation wants to exclude.

## 6. The one real side condition

With §5 corrected, only a single derivation actually needs repair:

```
GC.Gen.PromoteUpdate.BlueAlloc.wfh_part2_implies_blue_fields_closed
```

derives `GC.Gen.Promote.blue_fields_closed` from part 2 with no side condition.
Excluding no-scan sources from part 2 breaks it for a blue no-scan block.

The repair is to give it the side condition *"no blue object is no-scan"*, which
is exactly what coalescing establishes and what `coalesce_aux_blue_tag_zero`
already proves. This is not a new kind of obligation: `blue_fields_non_infix`
has precisely the same story, is established at the same place by the same
mechanism, and is carried in `major_heap_shape` and to the top level by
`GC.Spec.Correctness.gc_blue_fields_non_infix_gen`
(see the commentary at `GC.Gen.HeapInvariant.fsti:50-62`).

There is a single caller,
`GC.Gen.CheneyPreservation.cheney_promote_preserves_blue_fields_closed`
(`CheneyPreservation.fst:1179`), and it already carries `blue_fields_non_infix
major` in its `requires` --- the new clause sits beside it.

Because the exclusion is then **colour-independent**,

```fstar
let fields_constrained (g: heap) (src: obj_addr) : GTot bool =
  not (is_no_scan src g)
```

`GC.Spec.Mark.color_change_preserves_wf` transports it for free, and the
sweep-blues-a-dead-string transition raises no obligation at all: the block is
excluded before and after. This is the point the earlier revision got backwards
by making the predicate mention `is_blue`.

## 7. What it takes

1. **(done)** Add a `blue_blocks_scannable` clause --- no blue object is
   no-scan --- and prove the coalescing pass establishes it.
   `GC.Spec.Fields.blue_blocks_scannable` is the predicate, with the usual
   `_elim`/`_intro` pair, and `GC.Spec.Coalesce.coalesce_blue_blocks_scannable`
   is the theorem: it mirrors `coalesce_blue_not_infix` line for line, reading
   tag 0 off `coalesce_aux_blue_tag_zero` and then discharging
   `~(is_no_scan obj g')` through `is_no_scan_spec` and `no_scan_tag_val`
   instead of `is_infix_spec` and `infix_tag_val`.

   What remains of this step is the plumbing: putting the clause into
   `GC.Gen.HeapInvariant.major_heap_shape` beside `blue_fields_non_infix` and
   carrying it to the top level alongside `gc_blue_fields_non_infix_gen`.
   Across a minor collection it comes back the same way `blue_fields_non_infix`
   does. Both are only worth doing together with steps 2-5, since the clause has
   no consumer until part 2 is relaxed.
2. Add it to the `requires` of `wfh_part2_implies_blue_fields_closed` and of
   `cheney_promote_preserves_blue_fields_closed`.
3. Restate `well_formed_heap_part2` and `well_formed_heap_part3` over
   `fields_constrained`, threading it through their accessors --- `wfh_part2_elim`,
   `well_formed_heap_part2_intro{,_raw}`, `well_formed_heap_part2_3_transport`,
   `well_formed_heap_part2_3_intro_raw`, `wf_field_target_in_objects{,_raw}`,
   `points_to_target_in_objects{,_raw}`, `points_to_target_infix_wf`,
   `field_pointer_target_in_objects`, `no_infix_field_targets*`,
   `blue_fields_non_infix*`, `no_field_points_to_addr*`.
4. Same for `no_pointer_to_blue` (`Mark.fsti:227`), a plain `let` that can take
   the conjunct directly, plus its `no_pointer_to_blue_intro_from_fields`
   callback shape.
5. Delete `no_scan_invariant`, `minor_no_scan_invariant`,
   `promote_object_preserves_no_scan_invariant` and the ~41 interface mentions
   that thread them, re-proving the four consumers below by *skipping* no-scan
   objects instead of deriving a contradiction from them:

   | Site | What it currently discharges |
   |---|---|
   | `GC.Spec.Correctness.sweep_field_no_scan_contradiction:394` | a black no-scan object has no pointer field |
   | `GC.Spec.MarkBoundedCorrectness:1172` | same, transported across `mark_color_inv` |
   | `GC.Impl.MarkBounded.fst:1023` | preservation across bounded root darkening |
   | `GC.Spec.Coalesce.Shape.fst:104` | `coalesce_no_scan_invariant` |

6. A SPOT exhibiting a heap with a no-scan object whose body spells a heap
   address, shown to satisfy the relaxed precondition --- the non-vacuity
   witness, as `GC.SPOT.MinorInfixPre` is for interior pointers.

## 8. Measured fallout of step 3

Step 3 was carried out experimentally to size it. `GC.Spec.Fields.fst` verifies
after 53 threading sites and four substantive repairs:

- `well_formed_heap_part2_3_transport` must hypothesise agreement of
  `fields_constrained` rather than being stated over `is_no_scan` piecemeal;
- the private write- and colour-locality lemmas
  (`write_word_field_pointing_self_implies`,
  `color_change_preserves_field_pointing_other`) must *not* take the conjunct ---
  they are statements about the unchecked predicate itself;
- the `ensures` of the transport's `fields` callback must not take it either, or
  every caller inherits the obligation;
- inside `field_write_preserves_wf`, transporting the conjunct across the write
  needs `tag_of_object_spec` and `is_no_scan_spec` at both heaps, on top of the
  `read_write_different` that already gives header stability.

The whole repository then reported only **nine** further errors:

| Module | Nature |
|---|---|
| `GC.Spec.Mark.fst:172` | `header_agree` must also transport the conjunct |
| `GC.Spec.MarkBounded.fst:169` | `push_children_bounded_preserves_bsp` needs `~(is_no_scan obj g)`; the caller already branches on `is_no_scan` |
| `GC.Gen.NoBlueUtil.fst:56,57` | one interface `requires` |
| `GC.Spec.Coalesce.fst:2778,2779` | `white_target_resolve_stable` and its two callers |
| `GC.Spec.Sweep.fst:151` | resolved by *not* adding a precondition to `field_write_preserves_wf` |
| `GC.Gen.PromoteUpdate.BlueAlloc.fst:121,122` | the one in §6 |

## 9. Recommendation

Worth doing. Step 1 is the only genuinely new proof work, and it has a complete
template in `blue_fields_non_infix` plus an already-proved ingredient in
`coalesce_aux_blue_tag_zero`. Steps 3 and 4 are measured above. Step 5 is the
bulk of the diff but is mechanical unthreading.

The extracted C should not change: the implementation already ignores these
words, and the free blocks it produces are already cleared.
