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

## 5. The freed-no-scan gap, and why it decides the design

There is a second instance, and it is the one that settles the shape of the fix.

`no_scan_invariant` excludes blue objects, because a blue object's field 1 is
the free-list link. But a freed string is blue **and** no-scan, and the sweep
does not zero its body. Its remaining words are still the string's bytes, and
`well_formed_heap_part2` still requires every one of them that looks like a
pointer to name an enumerated object.

The tempting reading is that this is a second thing to relax: constrain only
field 1 of a blue block and leave the rest opaque. That reading is wrong, and
the reason is `alloc_spec`. Allocation recolours a blue block to White with
**tag 0** and does *not* clear its body (`GC.Spec.Allocator.fsti:15`). The words
a free block holds today are the fields a scannable object holds tomorrow. A
free block's entire body must therefore stay constrained whatever its tag --- it
is the model's stand-in for "the mutator initialises every field before the
collector can observe the object".

This is also what makes `GC.Gen.Promote.blue_fields_closed` derivable from
part 2 (`GC.Gen.PromoteUpdate.BlueAlloc.wfh_part2_implies_blue_fields_closed`),
which the whole Cheney promotion development depends on.

So the relaxation can only ever exclude *live* (non-blue) no-scan objects:

```fstar
let fields_constrained (g: heap) (src: obj_addr) : GTot bool =
  not (is_no_scan src g) || is_blue src g
```

## 6. Why that is not enough --- the blocking obstruction

With blue blocks still fully constrained, `fields_constrained` *changes value*
when a live no-scan object is recoloured to Blue. Sweeping a dead string
therefore has to **establish** part 2 for its body, from nothing.

The only fact in the repository that discharges that is `no_scan_invariant`
itself: a live no-scan object has no pointer-looking field at all, so part 2 for
the freshly-blued block is vacuous. Removing the invariant removes the proof
that sweep preserves well-formedness.

Concretely the obligation lands on `GC.Spec.Mark.color_change_preserves_wf`,
which is generic in the target colour and is what `GC.Spec.Sweep` uses to blue a
block.

`no_scan_invariant` is also genuinely *consumed*, not merely propagated:

| Site | What it discharges |
|---|---|
| `GC.Spec.Correctness.sweep_field_no_scan_contradiction:394` | a black no-scan object has no pointer field, so field-data preservation has no case to prove |
| `GC.Spec.MarkBoundedCorrectness:1172` | same, transported across `mark_color_inv` |
| `GC.Impl.MarkBounded.fst:1023` | preservation across bounded root darkening |
| `GC.Spec.Coalesce.Shape.fst:104` | `coalesce_no_scan_invariant` |

The Correctness one is not an artifact. A *genuine* pointer stored in a live
no-scan object would dangle after a collection, because no-scan fields are not
traced --- that is true of stock OCaml too. Real OCaml is safe because nothing
ever dereferences those bytes; the model needs the invariant because
`well_formed_heap` and successor preservation are stated over the *unchecked*
field enumeration, which does not consult the tag.

**Conclusion.** The relaxation is not blocked on proof effort. It is blocked on
a modelling assumption --- that reused memory is never observed uninitialised
--- which is currently carried by "a free block's body is well-formed" plus
"a live no-scan object has no pointer-looking field". Removing the second
without replacing the first is unsound-by-construction: sweep would put
arbitrary bytes on the free list and the allocator would hand them out as the
fields of a scannable object.

## 7. What it would actually take

In dependency order:

1. Give the model a notion of *uninitialised* field content, or have `sweep`
   and `alloc_spec` agree on a cleared body for free blocks. This is an
   implementation-visible change (a header retag and/or body clear in
   `sweep_object`), so it changes the extracted C. Everything else is blocked on
   it.
2. Then `fields_constrained` can drop the `is_blue` disjunct and become simply
   `not (is_no_scan src g)`, which is colour-independent and therefore survives
   `color_change_preserves_wf` for free.
3. Restate `well_formed_heap_part2` and `well_formed_heap_part3` over
   `fields_constrained`, and thread it through their accessors --- `wfh_part2_elim`,
   `well_formed_heap_part2_intro`, `well_formed_heap_part2_intro_raw`,
   `well_formed_heap_part2_3_transport`, `well_formed_heap_part2_3_intro_raw`,
   `wf_field_target_in_objects{,_raw}`, `points_to_target_in_objects{,_raw}`,
   `points_to_target_infix_wf`, `field_pointer_target_in_objects`,
   `no_infix_field_targets*`, `blue_fields_non_infix*`, `no_field_points_to_addr*`.
4. Same treatment for `no_pointer_to_blue` (`Mark.fsti:227`), a plain `let` that
   can take the conjunct directly, plus its `no_pointer_to_blue_intro_from_fields`
   callback shape.
5. Delete `no_scan_invariant`, `minor_no_scan_invariant`,
   `promote_object_preserves_no_scan_invariant` and the ~41 interface mentions
   that thread them, re-proving the four consumers above by *skipping* no-scan
   objects rather than deriving a contradiction from them.
6. A SPOT exhibiting a heap with a no-scan object whose body spells a heap
   address, shown to satisfy the relaxed precondition --- the non-vacuity
   witness, as `GC.SPOT.MinorInfixPre` is for interior pointers.

## 8. Measured fallout of steps 3 and 4

Steps 3 and 4 were carried out experimentally to size them, then reverted once
§6 established that they cannot stand on their own.

`GC.Spec.Fields.fst` needed 53 threading sites and four substantive repairs:

- `well_formed_heap_part2_3_transport` must hypothesise agreement of
  `fields_constrained`, not of `is_no_scan` --- a recolour to Blue changes which
  objects the clauses cover;
- inside `field_write_preserves_wf`, `fields_constrained g src ==
  fields_constrained g' src` needs `tag_of_object_spec`, `is_no_scan_spec`,
  `color_of_object_spec` and `is_blue_iff` at both heaps, on top of the
  `read_write_different` that already gives header stability;
- the private write- and colour-locality lemmas (`write_word_field_pointing_self_implies`,
  `color_change_preserves_field_pointing_other`) must *not* take the conjunct;
  they are statements about the unchecked predicate itself;
- the `ensures` of the transport's `fields` callback must not take it either,
  or every caller inherits the obligation.

With that in place the whole repository reported just **nine** further errors:

| Module | Nature |
|---|---|
| `GC.Spec.Mark.fst:172` | `header_agree` must also transport the new conjunct |
| `GC.Spec.MarkBounded.fst:169` | `push_children_bounded_preserves_bsp` needs `~(is_no_scan obj g)`; available at the caller, which already branches on `is_no_scan` |
| `GC.Gen.NoBlueUtil.fst:56,57` | one interface `requires` |
| `GC.Spec.Coalesce.fst:2778,2779` | `white_target_resolve_stable` and its two callers |
| `GC.Spec.Sweep.fst:151` | resolved by *not* adding a precondition to `field_write_preserves_wf` |
| `GC.Gen.PromoteUpdate.BlueAlloc.fst:121,122` | **the structural one** --- `wfh_part2_implies_blue_fields_closed`, i.e. §5 |

So the mechanical cost is small and well understood. The cost is entirely in
step 1.

## 9. Recommendation

Do not attempt this as a spec-only relaxation; §6 shows it cannot close. Treat
it as a change to the free-block contract first, and only then as a relaxation
of parts 2 and 3.

Until then, the honest description of `no_scan_invariant` and
`minor_no_scan_invariant` is the one now in the source: they are not an OCaml
memory-model guarantee, they are what lets a dead no-scan object be put on the
free list while keeping the free list's bodies well-formed for the allocator to
hand back out.
