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

## 5. The freed-no-scan gap

There is a second, sharper instance, and it is *not* covered by the invariant.

`no_scan_invariant` excludes blue objects, because a blue object's field 1 is
the free-list link. But a freed string is blue **and** no-scan, and the sweep
does not zero its body. Its remaining words are still the string's bytes, and
`well_formed_heap_part2` still requires every one of them that looks like a
pointer to name an enumerated object. Nothing rescues them.

This is invisible today for the reason in §3 — the allocator cannot produce a
string to free. It means the fix cannot simply be "exclude no-scan sources from
part 2": the free-list link of a blue no-scan block genuinely must stay closed,
while the rest of its body genuinely must not be constrained.

## 6. What it takes

Align the heap-level closure predicates with the words the collector can
actually follow. Those are exactly:

1. fields `1..wosize` of live (non-blue) **scannable** objects — precisely the
   graph's edge set; and
2. **field 1 only** of blue objects — the free-list link.

Everything else in the heap is opaque bytes.

Concretely:

- **Phase 1.** Introduce the notion in `GC.Spec.Fields` (say
  `field_is_followed g src idx`) and restate `well_formed_heap_part2`'s
  antecedent over it. Part 2 is `opaque_to_smt` and deliberately sealed, so the
  body change is confined to this file; the cost lands on its accessors
  (`wfh_part2_elim`, `well_formed_heap_part2_intro`,
  `well_formed_heap_part2_3_transport`, `wf_field_target_in_objects`,
  `points_to_target_infix_wf`, and the `*_raw` variants).
- **Phase 2.** Repair the elimination sites — about 27 outside `Fields.fst`.
  Most are scanning the source object, so `~(is_no_scan src g)` is already in
  scope; the ones that quantify over all objects need restructuring.
- **Phase 3.** Same treatment for `no_pointer_to_blue` (`Mark.fsti:227`), which
  is a plain `let` and can take the conjunct directly, plus its
  `no_pointer_to_blue_intro_from_fields` callback shape.
- **Phase 4.** Delete `no_scan_invariant`, `minor_no_scan_invariant`,
  `promote_object_preserves_no_scan_invariant` and the ~41 interface mentions
  that thread them.
- **Phase 5.** A SPOT exhibiting a heap with a no-scan object whose body spells
  a heap address, shown to satisfy the relaxed precondition — the non-vacuity
  witness, as `GC.SPOT.MinorInfixPre` is for interior pointers. Ideally a second
  one for a *freed* no-scan block, covering §5.

## 7. Cost and risk

`well_formed_heap_part2` is the clause that decides which heaps the collector
accepts, and it lives in `common/spec/`, so every phase invalidates the whole
`_cache`. Phase 2 is the bulk of the work and the only part whose difficulty is
hard to predict from the outside: a preservation proof that currently quantifies
over all objects may need a genuinely different argument once the obligation is
restricted.

The extracted C should not change. As with interior pointers in the nursery, the
implementation already does the right thing — it simply never reads these words.

## 8. Recommendation

Worth doing, and worth doing after the interior-pointer work has settled rather
than alongside it, since both touch the same accessors in `GC.Spec.Fields`.

The freed-no-scan gap in §5 is the part that should not be left undocumented:
unlike the live case it is not merely a restriction, it is a clause that no
invariant in the repository currently discharges, kept satisfiable only by the
allocator's inability to produce a no-scan block.
