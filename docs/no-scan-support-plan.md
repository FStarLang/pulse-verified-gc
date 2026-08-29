# Plan: supporting no-scan objects with arbitrary contents

*Status: implemented, for both heaps.  §§1--9 cover the major heap, which
needed no implementation change.  §10 covers the nursery, done in a follow-up;
that one was a real bug and did change the extracted C.*

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

## 7. What was done

1. **`blue_blocks_scannable`** --- no blue object is no-scan.
   `GC.Spec.Fields.blue_blocks_scannable` is the predicate, with the usual
   `_elim`/`_intro` pair, and `GC.Spec.Coalesce.coalesce_blue_blocks_scannable`
   is the theorem: it mirrors `coalesce_blue_not_infix` line for line, reading
   tag 0 off `coalesce_aux_blue_tag_zero` and then discharging
   `~(is_no_scan obj g')` through `is_no_scan_spec` and `no_scan_tag_val`
   instead of `is_infix_spec` and `infix_tag_val`.

2. **`wfh_part2_implies_blue_fields_closed` gained the side condition.**  That
   is the one derivation §6 identified.

3. **`well_formed_heap_part2` and `_part3` were restated over
   `fields_constrained`**, threaded through every accessor, intro, elim and
   callback type --- 57 sites in `GC.Spec.Fields.fst`.

4. **`GC.Spec.Mark.no_pointer_to_blue` likewise**, including its
   `no_pointer_to_blue_intro_from_fields` callback.

5. **`no_scan_invariant` was removed from every precondition.**  It survives as
   a *definition* only, because the SPOT in step 6 uses it to state what the old
   invariant rejected, and because the nursery variant is still live.  Purged
   from: `GC.Gen.HeapInvariant.major_heap_shape`,
   `GC.Impl.MarkBoundedPrecondition.darken_precondition`,
   `GC.Impl.gc_precondition_with_roots`, `GC.Spec.Correctness.mark_post` and
   `sweep_post_sweep_strong`, `GC.Spec.Coalesce.post_sweep_strong`,
   `GC.Spec.MarkBoundedCorrectness`.  The four consumers tabulated in the old
   step 5 now *skip* no-scan objects instead of deriving a contradiction from
   them; `GC.Spec.Coalesce.Shape.coalesce_no_scan_invariant` and the
   `mark_*_preserves_no_scan_invariant` family were deleted outright.

6. **`GC.SPOT.NoScanMajor`** is the non-vacuity witness: a two-object major heap
   whose live `no_scan_tag` block holds one word of body spelling
   `zero_addr + 32` --- a word-aligned in-heap address that is *not* an
   enumerated object (it points into the middle of the free block).  The module
   proves both halves:

   - `spot_ns_violates_no_scan_invariant` --- the heap does **not** satisfy the
     old `GC.Spec.Fields.no_scan_invariant`, so it was previously inadmissible;
   - `spot_ns_major_heap_shape` --- it *does* satisfy
     `GC.Gen.HeapInvariant.major_heap_shape`, `gen_gc`'s major-heap
     precondition.

## 8. The pivot: `blue_fields_closed` rather than `blue_blocks_scannable` in
   `major_heap_shape`

Step 1 originally planned to carry `blue_blocks_scannable` in
`major_heap_shape`, so that `wfh_part2_implies_blue_fields_closed` could be
invoked wherever `blue_fields_closed` was wanted.  That is one indirection too
many: the *only* thing the promotion development wants is
`blue_fields_closed`, and it already had a full `*_preserves_blue_fields_closed`
chain through Cheney promotion.  So `major_heap_shape` carries

```fstar
blue_fields_closed major
```

directly, in the slot `no_scan_invariant major` used to occupy.  This is not a
strengthening --- before the relaxation it was derivable from part 2 with no
side condition at all --- and it removes the need to thread
`blue_blocks_scannable` through both collections.  `blue_blocks_scannable` is
still what *establishes* the clause at the one place it must be established,
after coalescing.

Consequences worth knowing:

- `GC.Gen.PostCollectionShape` re-establishes it after a major collection with
  `coalesce_blue_fields_closed`, a 30-line clone of
  `coalesce_blue_fields_non_infix`.
- Clients that build a heap by hand (the SPOTs) prove `blue_blocks_scannable`
  pointwise and call `wfh_part2_implies_blue_fields_closed` once.

## 9. Threading notes

Three patterns account for nearly all of the mechanical diff, and are worth
knowing before touching this again:

- **Transporting the conjunct across a colour change** is
  `color_preserves_is_no_scan obj g c` when the recoloured object *is* the
  source, and `color_change_preserves_other_is_no_scan recoloured src g c`
  otherwise.  `GC.Spec.Mark.fst` needed this at 40 call sites, because every
  `push_children_*` lemma now requires `fields_constrained g obj`.
- **Transporting it across a header-framing lemma needs four spec calls**, not
  one: `hd_address_spec src; tag_of_object_spec src h1; tag_of_object_spec src
  h2; is_no_scan_spec src h1; is_no_scan_spec src h2`.
- **A local `Lemma` closure passed to a `Fields` combinator does not inherit the
  combinator's new hypothesis** --- F* accepts a callback that requires *less*,
  so each lambda's `requires` has to be extended by hand.

Structure-preservation proofs discharge the no-scan case by showing the tag
survives on both sides: `HeapGraph.get_pointer_fields` returns `Seq.empty` for a
no-scan object, so both sides of the equation are empty.

## 10. The nursery (done in a follow-up)

`minor_no_scan_invariant` was initially left in
`GC.Gen.HeapInvariant.minor_heap_shape`, on the grounds that relaxing it was a
strictly larger job than the major heap and not mechanical.  That turned out to
be right about the size and wrong about the difficulty, and it has since been
done --- it had to be, because unlike the major-heap clauses this one was
covering a *real* bug: the extracted `scan_loop` walked no-scan nursery bodies,
and a forged interior pointer inside a young `Bytes.t` crashed the collector.
See `docs/known-issues.md`, "Fixed: no-scan blocks in the nursery were
scanned", and `tests/nursery_no_scan_interior.ml`.

The shape of the fix is different from the major heap's, because the asymmetry
runs the other way.  The major heap needed no implementation change: parts 2
and 3 of `well_formed_heap` are guarded by `GC.Spec.Fields.fields_constrained`,
so relaxing the spec was enough.  The nursery needed the opposite --- the spec
was silent in the wrong direction (it quantified over all objects and excluded
the awkward ones by hypothesis) and the implementation genuinely read the
bodies.

What made it tractable was choosing where to put the guard.  Rather than adding
a tag test inside `cheney_forward_fields`, the *scan window* became a derived
quantity:

```fstar
let minor_scan_wosize (ms: minor_state) (obj: U64.t) : nat =
  if minor_tag ms obj >= 251 then 0 else minor_wosize ms obj
```

and every site that *reads* a nursery body switched to it, while every site
that *promotes* one kept `minor_wosize` (promotion copies the body verbatim,
tag notwithstanding).  Because `cheney_forward_fields ... 0 0` is already the
base case, every preservation lemma --- all proved for arbitrary `i, wz` ---
carried over unchanged.  `cheney_scan` being a `val` in the `.fsti` with
`cheney_scan_base` / `cheney_scan_step` equation lemmas confined the body
change to one module.

The `minor_tag minor src < 251` obligation in
`GC.Gen.MinorCollectForwarding.{Reflection,Edges}` was discharged not by
threading a new invariant through six lemmas, but by *strengthening the
existing one to an equation*:
`GC.Gen.CheneyPreservation.Fields.cheney_promote_fwd_target_no_scan_iff_minor_tag`
went from `is_no_scan target = false` to
`is_no_scan target = (minor_tag minor x >= 251)`.  That is sound because
`promote_object` ends in `set_promoted_tag ... (minor_tag minor obj)`, and it
is cheap because the threading lemmas around it are frame/preservation lemmas
that never look at the tag: only the establishing branch changed, by keeping
the comparison symbolic instead of assuming `tag < 251`.  Roughly 60 lines,
confined to one module, instead of the ~250 across six that were feared.

`minor_no_scan_invariant` is now deleted, and `minor_heap_shape` is
`minor_wf /\ minor_guards_complete /\ minor_infix_wf`.

`GC.Gen.HeapInvariant.minor_major_fields_no_blue` was narrowed in the same way,
for the same reason: it quantified over every young field, so an ordinary young
`Bytes.t` holding a word that happens to satisfy `is_pointer_field` still
falsified `gen_gc`'s precondition even after `minor_no_scan_invariant` was gone.
It now quantifies over `minor_scan_wosize` too, as does
`GC.Gen.ReachabilityBridge.minor_no_pointer_to_blue`.

`spot/GC.SPOT.NoScanMinor` is the machine-checked non-vacuity witness, the
nursery counterpart of `GC.SPOT.NoScanMajor`: a three-word nursery holding one
tag-251 block whose two body words are `8` --- a value `is_minor_pointer`
accepts, so the pre-fix `scan_loop` would have forwarded it.  The module proves
both halves of the claim: `spot_ns_minor_was_forbidden` refutes the deleted
clause (restated verbatim in the interface), and `spot_ns_collection_heap_shape`
establishes `gen_gc`'s full entry invariant for the same nursery against
`GC.SPOT.ConcreteMajor`'s major heap.

## 11. Outcome

For the major heap (§§1--9) the extracted C is **byte-identical**: the
implementation already ignored these words, and the free blocks it produces are
already cleared.

For the nursery (§10) it is not, and that is the point.  `scan_loop` gained

```c
uint64_t tag = hdr & 0xFFULL;
uint64_t wosize;
if (tag >= 251ULL) wosize = 0ULL; else wosize = hdr >> 10U;
```

which is exactly the guard `update_all_objects` and `mark_and_push` already
had.  With the old C, `tests/nursery_no_scan_interior.ml` dies with "major heap
full"; with the new C it passes, and `tests/no_scan.ml` section 9 was
strengthened back to the word-aligned interior forgery (`v+8`) it had been
downgraded from.
