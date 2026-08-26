# Plan: supporting infix pointers in the minor heap

Status: **proposal, written for review.**

Companion to `docs/infix-support-plan.md`, which covered the *major* heap and is
complete (Phases 0–5 done, audited by `spot/GC.SPOT.InfixMajor` and friends).
This document covers the remaining restriction: minor-heap interior pointers.

## 1. What stock OCaml does

The question is whether a *real* OCaml program can produce an interior (infix)
pointer that targets the minor heap. It can, on every path. Citations are to
`generational/ocaml-integration/ocaml-4.14-unchanged/`.

### 1.1 Mutually recursive closures are allocated in the minor heap

`runtime/interp.c:575` (`CLOSUREREC`):

```c
mlsize_t envofs = nfuncs * 3 - 1;
mlsize_t blksize = envofs + nvars;
if (blksize <= Max_young_wosize) {
  Alloc_small(accu, blksize, Closure_tag);      /* minor heap */
} else {
  accu = caml_alloc_shr(blksize, Closure_tag);  /* PR#6385: major heap */
}
```

`Max_young_wosize` is 256 (`runtime/caml/config.h:204`). Two mutually recursive
functions with no free variables give `blksize = 5`, so the block is allocated
in the **minor heap**. The native path takes the same branch:
`asmcomp/cmm_helpers.ml:797` emits an inline `Calloc` (a `young_ptr` bump) when
`wordsize <= Config.max_young_wosize`.

So the premise behind the current restriction — "maybe mutually recursive
objects always go straight to the major heap" — is false. They go to the minor
heap in the common case, and only spill to the major heap when the closure
block exceeds 256 words.

### 1.2 A root can be a minor infix pointer

`CLOSUREREC` pushes each infix entry point onto the OCaml stack
(`interp.c:601`, `*--sp = (value) p;`) so that `OFFSETCLOSURE` can find it.
`runtime/roots_byt.c:39` scans the whole stack with `caml_oldify_one`. In
native code, `Uoffset` "produces a valid Caml value, pointing just after an
infix header" (`asmcomp/cmmgen.ml:409`) and lands in a frame-descriptor slot
that `roots_nat.c` passes to `Oldify`.

### 1.3 A field of a young block can hold a minor infix pointer

Nothing prevents it: a closure's environment slot, or any ordinary record
field, can be assigned `g` where `g` is a member of a mutual recursion group.
`caml_oldify_mopup` (`runtime/minor_gc.c:295`) scans promoted blocks' fields
and calls `caml_oldify_one` on every young block field, infix included.

### 1.4 A field of a *major* block can hold a minor infix pointer

`caml_modify` (`runtime/memory.c:617`) needs no infix special case:

```c
if (Is_block(val) && Is_young(val)) {
  add_to_ref_table (Caml_state->ref_table, fp);
}
```

`Is_block` is true of an infix pointer (low bit clear) and `Is_young` is true
when the parent closure is in the nursery, so the field is recorded in the
remembered set. `caml_empty_minor_heap` then replays the table through
`caml_oldify_one`.

### 1.5 How `caml_oldify_one` handles it

`runtime/minor_gc.c:231`:

```c
} else if (tag == Infix_tag) {
  mlsize_t offset = Infix_offset_hd (hd);
  caml_oldify_one (v - offset, p);   /* Cannot recurse deeper than 1. */
  *p += offset;
}
```

Promote the parent, then re-add the byte offset. Because the parent's body is
copied verbatim, the infix header sits at the same offset in the copy, so
`new_parent + offset` is a valid infix pointer in the major heap. OCaml 5.x
restructures this as a `do/while` with an explicit `infix_offset` local, but
the algorithm is identical.

Two layout invariants are documented at `runtime/caml/mlvalues.h:224`:

* *"Infix_tag must be odd so that the infix header is scanned as an integer"* —
  which is why an infix header word can sit in a scanned block without the mark
  phase mistaking it for a pointer;
* *"infix headers can only occur in blocks with tag Closure_tag"*.

The second is the invariant our spec is currently missing (§3.1).

### 1.6 Layout, concretely

`let rec f x = g x and g y = f y` (`nfuncs = 2`, `nvars = 0`, `blksize = 5`):

```
-8   header   Closure_tag(247) | wosize=5
+0   Field 0  code_f
+8   Field 1  closinfo_f
+16  Field 2  Make_header(3, Infix_tag, white)     <- infix header, wosize = 3
+24  Field 3  code_g                               <- val_g = val_f + 24
+32  Field 4  closinfo_g
```

`Infix_offset_val(val_g) = 3 * 8 = 24`, and `val_g - 24 == val_f`. Note
`wosize = 3 >= 2` and the parent carries `Closure_tag`: exactly the two
conditions §3.1 adds.

## 2. What we already have

The gap is narrower than the code comments suggest.

### 2.1 The implementation is already infix-capable, and so is the shipped C

`generational/impl/GC.Gen.Impl.Cheney.fst`:

* `forward_if_minor` (`:294`) reads the tag and dispatches to
  `forward_if_minor_infix` (`:133`) when `tag == 249`;
* `forward_if_minor` is called from **both** the root loop (`:585`) and the
  field-scan loop (`:837`), so fields are already handled;
* `GC.Gen.Impl.MinorHeap.synthesize_infix_forwarding` (`:549`) walks the
  nursery synthesising `fwd[infix] = fwd[parent] + delta` entries, and
  `maybe_add_infix_parent` (`:634`) adds infix parents as roots.

All of this survives extraction: `generational/snapshot/GC_Gen_Impl.c` contains
`synthesize_infix_forwarding` (`:498`) and `forward_if_minor_infix` (`:649`).

**Consequence: this change should not alter the extracted C at all.** It is a
pure specification/proof change that lets the existing code be *applied* to
heaps it already handles.

### 2.2 The spec-level forwarding function is already infix-aware

`generational/spec/GC.Gen.Cheney.fst:100`:

```fstar
let cheney_forward_one minor cs addr =
  if cs.cs_fwd addr <> 0UL then cs
  else if is_infix_in_minor minor addr then
    let parent = infix_parent minor addr in
    let cs' = cheney_forward_normal minor cs parent in
    ... extend_forwarding cs'.cs_fwd addr (cs'.cs_fwd parent + delta) ...
  else cheney_forward_normal minor cs addr
```

This is `caml_oldify_one`'s infix case verbatim. `cheney_forward_fields`
(`:167`) and `cheney_forward_roots` (`:189`) both go through it.

### 2.3 The obsolete rationale

`generational/spec/GC.Gen.HeapInvariant.fsti:83`:

> *Forwarding an infix sub-object produces an interior major pointer, which is
> valid for roots but not for major object fields under the current
> `well_formed_heap_part2` model.*

and `:71`:

> *Cheney's forwarding map is keyed by whole minor objects, so lifting that is a
> separate change.*

Both halves are now wrong:

1. `well_formed_heap_part2`/`part3` were relaxed to the **resolved**-target
   formulation by `docs/infix-support-plan.md` Phase 1, so an interior major
   pointer in a major field is legal today. `spot/GC.SPOT.InfixMajor` audits
   exactly that.
2. The forwarding map is *not* keyed only by whole minor objects —
   `cheney_forward_one` extends it at the infix address itself.

## 3. The actual blocker

Two opaque predicates, `minor_fields_no_infix_targets` (`HeapInvariant.fsti:89`)
and `major_minor_fields_no_infix_targets` (`:95`), forbid the §1.3 and §1.4
scenarios. They are consumed at eleven `_elim` sites, and every one of them
exists to feed a single obligation, `field_fwd_targets_in_objects`
(`GC.Gen.CheneyPreservation.fst:1280`):

```fstar
Seq.mem ((prom.fwd_map old_val) <: obj_addr) (objects zero_addr prom.major_final)
```

That is the **raw**-enumeration requirement. An infix target cannot satisfy it
by construction — it is an interior address, deliberately not enumerated. This
is precisely the obligation that Phase 1 of the major-heap work replaced with
the resolved form. The same replacement is what is needed here.

Note what is *already* proved:
`Forwarding.cheney_promote_fwd_valid_or_infix` (`Forwarding.fsti:321`) gives

```fstar
fwd x <> 0UL ==> bounds /\ aligned /\
  (Seq.mem ((fwd x) <: obj_addr) (objects zero_addr g) \/ is_infix (fwd x) g)
```

so the infix disjunct is established. What is missing is upgrading `is_infix`
to `infix_addr_wf` — i.e. proving the promoted infix header still names an
enumerated closure parent.

### 3.1 Why `minor_infix_wf` must be strengthened first

`GC.Gen.MinorHeap.fsti:273` requires of an infix address `addr` with
`wz = minor_wosize ms addr` and `parent = addr - wz*8`:

```
wz > 0, wz*8 <= addr - 8, parent >= 8, parent % 8 == 0,
Seq.mem parent (minor_objects ms),
addr - parent < minor_wosize ms parent * 8
```

`GC.Spec.Object.infix_addr_conds` (`:445`) requires, of the major heap:

```
w >= 2, p >= 8, p < heap_size, p % 8 == 0,
Seq.mem p objs, is_closure p g,
h < p + wosize(p)*8
```

Two conjuncts are missing on the minor side: **`wz >= 2`** and
**`is_closure parent`**. Both are OCaml invariants (§1.5, §1.6): the smallest
infix offset is 3 words, and infix headers only occur in `Closure_tag` blocks.
Without them the promoted infix target cannot be shown well-formed in the major
heap, so they must be added to `minor_infix_wf`.

This strengthens a *precondition* the client must establish. That is the
correct direction — it is a demand on the mutator that stock OCaml already
meets — and it is what makes the field restriction removable.

### 3.2 Why promotion preserves the layout

`promote_object` (`GC.Gen.Promote.fsti:103`) is
`alloc_spec`, then `copy_fields minor new_major obj new_addr 0 wosize`, then
`zero_promote_padding`, then `set_promoted_tag`.

* `copy_fields` copies the body **verbatim**, so the infix header word at
  parent-relative byte offset `delta - 8` is reproduced exactly. Hence
  `wosize_of_object (fwd addr) major_final == minor_wosize minor addr`.
* `zero_promote_padding` only touches field indices `>= wosize`; the infix
  header is at index `(delta - 8)/8 < wosize - 1`, so it is untouched.
* `set_promoted_tag` writes `minor_tag minor obj`, preserving `Closure_tag`.

Therefore, writing `P = fwd(parent)` and `delta = addr - parent = wz*8`:

```
parent_closure_addr_nat (fwd addr) major_final
  = (P + delta) - wosize_of_object (fwd addr) major_final * 8
  = P + wz*8 - wz*8
  = P
```

which is enumerated (it is a normal, non-infix promotion target, so
`fwd_noninfix_targets_valid` applies), carries `closure_tag`, and satisfies the
containment bound because `alloc_spec` never shrinks a block. All of
`infix_addr_conds` follows.

## 4. Phased plan

### Phase A — strengthen `minor_infix_wf`

`generational/spec/GC.Gen.MinorHeap.fsti/.fst`: add `wz >= 2` and
`minor_tag ms parent == 247` to `minor_infix_wf`, and extend
`infix_parent_in_minor_objects` to expose them.

Establishment sites are few (`spot/GC.SPOT.ConcreteMinor.fst:306`, and any
future minor SPOT); everywhere else `minor_infix_wf` is only *threaded* as a
hypothesis, so strengthening it is free. Risk: low. No proof should break.

### Phase B — prove the promoted infix target well-formed

`GC.Gen.CheneyPreservation.Forwarding`: add

```fstar
let fwd_infix_targets_wf (minor: minor_state) (fwd: forwarding_map) (g: heap) : prop =
  forall (x: U64.t). fwd x <> 0UL /\ is_infix_in_minor minor x ==>
    U64.v (fwd x) >= U64.v mword /\ U64.v (fwd x) < heap_size /\
    U64.v (fwd x) % U64.v mword == 0 /\
    Seq.mem (resolve_object ((fwd x) <: obj_addr) g) (objects zero_addr g) /\
    infix_addr_wf g (objects zero_addr g) ((fwd x) <: obj_addr)
```

and `cheney_promote_fwd_infix_targets_wf` establishing it, by the §3.2
argument, reusing `cheney_promote_fwd_noninfix_targets_valid` for the parent.

This is the substantive proof work. Risk: medium — it needs a "promoted body
word equals minor body word" frame lemma; `Fields.cheney_promote_fwd_target_fields_match`
already provides one.

### Phase C — weaken the field obligation

`GC.Gen.CheneyPreservation.fst`: restate `field_fwd_targets_in_objects` as

```fstar
Seq.mem (resolve_object ((fwd old_val) <: obj_addr) major) (objects zero_addr major) /\
infix_addr_wf major (objects zero_addr major) ((fwd old_val) <: obj_addr)
```

Re-prove `cheney_promote_field_fwd_targets_in_objects_from_shape` by case
splitting on `is_infix_in_minor minor old_val` — the non-infix branch is the
existing proof minus the two `_elim` calls, the infix branch is Phase B.
Then adapt `update_major_pointers_preserves_wfh_part2_from_field_targets`
(`:1545`), whose conclusion is *already* the resolved form; its `field_closure`
helper currently discharges the infix case with `resolve_non_infix`, and gains
a real branch instead.

Risk: medium-high. This is the most SMT-expensive module family in the repo;
`CheneyPreservation.Forwarding` is on `EAGER_QI_CHECKED`, `.Fields` deliberately
is not.

### Phase D — the remaining `_elim` sites

`GC.Gen.MinorCollectForwarding.Reflection` (`:193, 258, 301, 401, 465`),
`.NonPointerFields` (`:113, 169`), `.fst` (`:493, 685`). Each needs the same
raw→resolved swap. Expect these to be mechanical once Phase C settles the
pattern.

### Phase D2 — interior *roots* in the combined-graph isomorphism  ⚠️ **partial**

Phase D covers interior pointers stored in *fields*.  Interior pointers held
directly in a **root** are a separate, larger piece of work and are currently
outside the reachable subgraph the isomorphism theorem talks about.

`GC.Gen.CombinedGraph.classify_root` is raw, so an interior root `r` yields
`MinorV r`, which is not a vertex of the combined graph.  The post side omits it
symmetrically: `Promote.rewrite_root` maps such a root to `fwd parent + delta`,
which is likewise not a vertex of the post-collection graph, and
`MinorCollectForwarding.Helpers.post_minor_reachable` demands `r == rr` with `rr`
a graph vertex.  The theorem is therefore *sound* -- both sides consistently
exclude a closure kept alive only by an interior root -- but *incomplete*: it
says nothing about such a closure, in either direction.

The collector itself is unaffected.  `Cheney.cheney_forward_one` forwards an
interior root through its parent and installs `fwd r = fwd parent + delta`, and
`CheneyBFS.fwd_covers_roots` / `Reachability.minor_reachable` both resolve their
roots, so an interior root does keep its closure alive at run time.

Closing the gap needs, in order:

1. `classify_root` (and `classify_roots`, ~60 call sites) to take a
   `minor_state` and resolve, with `classify_roots_inv_minor` restated
   existentially (`exists r. Seq.mem r roots /\ resolve_minor ms r == v`).
2. `post_minor_reachable` to admit a resolved root:
   `r == rr \/ r == HeapGraph.resolve_field res.mc_major rr`.
3. A new lemma that a promoted infix forwarding target resolves to its promoted
   parent -- `resolve_object (fwd x) res.mc_major == fwd (infix_parent minor x)`
   -- carried through `update_major_pointers`.
4. `normal_classified_root_image_in_rewrite_roots` weakened to the resolved
   form, and its consumers in `GC.Gen.MinorCollectForwarding` adapted.
5. `roots_valid_for_minor_collection` relaxed to admit an interior nursery
   root, and the relaxation propagated to everything that consumes it.

**Step 1 is done; step 3 is supplied by `MCFH.fwd_image_resolves` (Phase F).
Steps 2, 4 and 5 are open, and step 5 is the one that makes the others worth
doing.**

`classify_root` now resolves, matching `Reachability.minor_reachable_roots`,
which Phase D had already made resolution-aware; the two root notions agreed
only by accident before.  `classify_roots_inv_minor` is correspondingly
existential, and `classify_roots_minor_mem_raw` recovers the old pre-resolution
conclusion for a non-interior root.

Step 2 was attempted and **deliberately backed out**.  The reason is that step 5
is the load-bearing one: `roots_valid_for_minor_collection` still places every
nursery root in `minor_objects minor`, and nursery objects are never infix, so
under the hypotheses the isomorphism theorem actually carries, an interior root
*cannot occur*.  Weakening `post_minor_reachable` therefore buys nothing today
while weakening the theorem's forward direction (`image_valid`) for every
client, and it costs a disjunct that must be destructured at every use --- two
proofs (`normal_src_edge_preserves_post_minor_reachable`,
`MajorReachabilityTransfer.result_post_reachable_swap`) diverged on it.

What landed instead is the non-vacuous half: the resolution `classify_root`
performs is discharged locally, in
`normal_classified_root_image_in_rewrite_roots`, from a new hypothesis

```fstar
[@@"opaque_to_smt"]
let roots_not_infix_in_minor (minor: minor_state) (roots: seq U64.t) : prop =
  forall (r: U64.t).
    Seq.mem r roots /\ is_minor_pointer r ==> ~(is_infix_in_minor minor r)
```

threaded through the four lemmas of the reachability-transfer chain and derived
once, at `normal_post_reachable_subgraph_isomorphism`, by
`roots_valid_not_infix`.  Naming the assumption on its own is what makes step 5
a local edit later: the chain no longer depends on
`roots_valid_for_minor_collection` at all, only on this one consequence of it.

`opaque_to_smt` is not decoration.  The chain's contexts already carry many
`Seq.mem _ roots` facts, and letting Z3 instantiate this quantifier there pushed
`ready_src_reach_image_post_reachable` past the 300 s cap; behind
`roots_not_infix_in_minor_elim` it costs nothing.  Threading the full
`roots_valid_for_minor_collection` (which mentions the recursive `minor_objects`
and `objects zero_addr`) diverged outright.

#### What is left, precisely

The restriction is *only* in the specification.  The extracted collector already
handles an interior root, on both sides of the collection:

* **Nursery.**  `GC.Gen.Impl.Cheney`'s root loop (`:596`) calls the same
  `forward_if_minor` as the field scan (`:850`), which dispatches to
  `forward_if_minor_infix` on tag 249; `CheneyBFS.fwd_covers_infix_roots` and
  `scan_preserves_fwd_covers_infix_roots` were added in Phase A/B for exactly
  this case.
* **Major heap.**  `GC.Impl.MarkBounded.check_and_darken_bounded_spec` applies
  `SpecObject.resolve_object` to every root *before* darkening, so an interior
  root greys its enclosing closure.  The extracted C does the same.

So no collector code is missing.  What is missing is that four specifications
still describe a root as its own object rather than as something that resolves
to one.

##### The minor-side chain (as previously scoped)

`MCFH.roots_valid_for_minor_collection`'s minor branch becomes

```fstar
is_minor_pointer r ==>
  Seq.mem (resolve_minor minor r) (minor_objects minor) /\
  minor_wosize minor (resolve_minor minor r) > 0
```

and that *forces* step 2: once an interior root is admissible,
`roots_valid_not_infix` is no longer provable, the reachability chain loses its
supplier of `roots_not_infix_in_minor`, and the resolution must be carried in
`post_minor_reachable` after all.  Three proofs then need repair, all located
and two of them repaired during the attempt:

1. `normal_src_edge_preserves_post_minor_reachable` --- its four nested
   `FStar.Classical.exists_elim` motives spell the old `r == rr` shape out
   literally.  **Fix known and verified:** replace `r == rr` by the disjunction
   in all six places (three `requires`, three `#(fun ... -> ...)` motives) and in
   the innermost `finish_d` assertion.

2. `post_reach_witness_is_normal_image` / `post_rewritten_root_is_normal_image`
   --- the backward direction destructures `post_minor_reachable` with
   `indefinite_description_ghost` and requires `r == rr`.  **Fix known and
   verified:** merge the two into one `post_root_image_is_normal_image` taking
   the vertex `r` and the disjunction, branching on `is_minor_pointer r0` for
   the underlying root.  The wrong disjunct is discharged in each branch by
   `well_formed_heap_part4 res.mc_major` (from
   `CheneyPres.cheney_collect_preserves_wfh_from_shape`): a *vertex* is never
   interior, while `fwd r0` for an interior `r0` is, by
   `MCFH.fwd_image_resolves`.

3. `MajorReachabilityTransfer.result_post_reachable_swap` (`:133`) --- moves a
   `result_post_reachable` fact between two heaps that
   `graphs_agree_on ... live` relates.  Its hypothesis
   `forall (r: vertex_id). Seq.mem r rts ==> live r` quantifies over *vertices*,
   and an interior `rr` is not one, so nothing lets `resolve_field ha rr` move to
   `resolve_field hb rr`.  **New work:** add
   `forall (rr: U64.t). Seq.mem rr rts ==> HG.resolve_field ha rr == HG.resolve_field hb rr`
   to the `requires` and discharge it in `major_result_post_transfer` from the
   field-data-preservation pillar of `GC.Spec.Correctness` (an interior root's
   header sits in the body of a live object, which a major collection preserves).

##### The major-side chain --- the part the earlier scoping missed

Relaxing `roots_valid_for_minor_collection` immediately breaks
`GC.Gen.MajorPrecondition.post_minor_minor_root_valid`, whose conclusion is

```fstar
MBP.root_valid_for_darkening result.mc_major (Promote.rewrite_root r prom.fwd_map)
```

and `rewrite_root` deliberately does **not** resolve, so for an interior nursery
root the rewritten root is an interior pointer into the promoted closure.
`GC.Impl.MarkBoundedPrecondition.root_valid_for_darkening` demands
`Seq.mem (r <: obj_addr) (objects zero_addr g)`, which such an address does not
satisfy.  That predicate, and `GC.Impl.MarkBounded.root_points_to_object` behind
it, must be restated over `SpecObject.resolve_object r g`.

This was measured, not guessed.  Relaxing `root_points_to_object` alone to

```fstar
Seq.mem (SpecObject.resolve_object (SpecHeap.f_address h) g)
        (SpecFields.objects zero_addr g)
```

and running `make -C mark-and-sweep -k -j128` fails exactly three modules:

| Module | Failure | Fix |
|---|---|---|
| `GC.Impl.MarkBoundedPrecondition.fst:23` | `root_valid_for_darkening_points_to_object` | add `SpecObject.resolve_non_infix` --- one line |
| `GC.Impl.MarkBounded.fst:418` | `root_points_to_object_transfer` | hypothesis must become `resolve_object` agreement rather than `is_infix` agreement; both callers are colour changes, so `GC.Spec.Object.color_preserves_resolve_object` supplies it |
| `GC.Impl.MarkBoundedRootLemmas.fst:250` | `check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root` | its conclusion `Seq.mem (v <: obj_addr) st'` must become `Seq.mem (resolve_object (v <: obj_addr) g) st'`, and its colour hypotheses must likewise be about the resolved object |

The third of those is not local.  It propagates to
`GC.Impl.MarkBoundedRootLemmas.check_and_darken_bounded_spec_preserves_stack_roots`
(`forall x ∈ st'. Seq.mem x roots` becomes
`forall x ∈ st'. exists q ∈ roots. resolve_object q g == x`), hence to
`GC.Impl.MarkBoundedPrecondition.darken_roots_match_stack`, hence to

```fstar
let roots_match_stack (roots: Seq.seq U64.t) (st: Seq.seq obj_addr) : prop
```

in `GC.Gen.Impl.fsti:69`, which must gain a `heap` parameter and read

```fstar
let roots_match_stack (g: heap) (roots: Seq.seq U64.t) (st: Seq.seq obj_addr) : prop =
  (forall (r: U64.t). Seq.mem r roots ==> is_val_addr r) /\
  (forall (r: obj_addr). Seq.mem (r <: U64.t) roots ==>
     Seq.mem (SpecObject.resolve_object r g) st) /\
  (forall (r: obj_addr). Seq.mem r st ==>
     (exists (q: obj_addr). Seq.mem (q <: U64.t) roots /\
                            SpecObject.resolve_object q g == r))
```

`roots_match_stack` is part of `gen_gc`'s **user-visible postcondition**
(`gen_gc_roots_post`), so this is an interface change, and it reaches
`GC.SPOT.InfixPost`, `GC.SPOT.ConcreteFull` and their helpers.

##### What does *not* need to change

`GC.Spec.Mark.root_props` and the five pillars of `GC.Spec.Correctness` are
untouched.  The major collector never sees the raw root array: `GC.Gen.Impl`
hands it the *darkened mark stack* (`gc_precondition_with_roots g' st' st'`),
and `st'` already holds resolved, enumerated objects.  The interior-root notion
stops at the darkening boundary.

##### Status and recommendation

This is Phase H, and it is a project of its own --- roughly ten modules across
`mark-and-sweep/impl`, `generational/spec`, `generational/impl` and `spot`, one
of them (`GC.Gen.Impl`) a large Pulse module, plus a change to `gen_gc`'s
published postcondition.  It is **not** a tail of Phase D2.

### Phase H.1 — interior roots in the major collector  ✅ **done**

The major-heap half of Phase H is complete: **the mark-and-sweep darkening pass
now specifies a root as something that *names* an object rather than as an
object.**  Every predicate along the darkening chain was moved onto
`SpecObject.resolve_object`, which is the identity on ordinary pointers, so
nothing about a non-interior root set changed.

| Predicate | Before | After |
|---|---|---|
| `GC.Impl.MarkBounded.root_points_to_object g v` | `Seq.mem (v <: obj_addr) (objects zero_addr g)` and `~is_infix v g` | `Seq.mem (resolve_object (v <: obj_addr) g) (objects zero_addr g)` |
| `GC.Impl.MarkBoundedPrecondition.root_valid_for_darkening g r` | membership and non-blueness of `r` | membership and non-blueness of `resolve_object r g` |
| `check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root` | pushes `v` | pushes `resolve_object (v <: obj_addr) g` |
| `check_and_darken_bounded_spec_preserves_stack_roots` | "the stack stays a subset of `roots`" | "the step adds at most `resolve_object (v <: obj_addr) g`" (the `roots` parameter is gone) |
| `GC.Gen.Impl.roots_match_stack roots st` | `roots` and `st` are equal as sets | `roots_match_stack g roots st`: `st` holds exactly `MBP.root_named g roots`, i.e. the *resolutions* of the roots |

Two supporting families were added to `GC.Impl.MarkBounded`:

* `check_and_darken_bounded_spec_preserves_resolve` /
  `darken_roots_bounded_prefix_preserves_resolve` /
  `darken_roots_bounded_spec_preserves_resolve` --- darkening only recolours
  headers, and `resolve_object` reads only tag and size, so the object a value
  names is stable across the whole darkening pass.  These replace the
  `preserves_is_infix` calls that used to feed
  `root_points_to_object_transfer`, whose hypothesis is now `resolve_object`
  agreement rather than `is_infix` agreement.
* `MBP.root_named g roots x` --- "`x` is the object some root names in `g`".
  This is the weakening of "every stack entry is a root value" that interior
  roots force: an interior root pushes the closure it points into, and that
  closure is not itself a root value.

`check_and_darken_bounded_spec_preserves_read_word` also had to move: the slot
it excludes is now the header of the *resolved* target,
`resolve_object (v <: obj_addr) g - mword`, not `v - mword`.

Because the generational entry point still restricts nursery roots (below), the
rewritten roots after a minor collection are all ordinary pointers, and
`GC.Gen.MajorPrecondition.post_minor_roots_valid_for_darkening` now proves that
outright (`resolve_object r result.mc_major == r` in both the minor and the
major branch).  `gen_gc_roots_post` therefore still publishes the literal
membership `Seq.mem (r <: obj_addr) prepared_st` alongside the resolved
`roots_match_stack`, which is what `spot/GC.SPOT.ConcreteFull` and
`spot/GC.SPOT.InfixPost` consume.

Extracted C is byte-identical, and the OCaml integration suite (2514 checks,
groups 11 and 12 exercising interior-pointer roots) passes under both runtimes.

### Phase H.2 — interior roots in the nursery  ❌ **not done**

The remaining restriction is the *minor* branch of
`MinorFwd.roots_valid_for_minor_collection`, which still demands
`Seq.mem (resolve_minor minor r) (minor_objects minor)` **and** that `r` itself
be an enumerated nursery object.  Relaxing it was attempted and is recorded in
`/dev/null`-free form here because the blocker is precise and worth writing down.

Relaxing the minor branch makes a rewritten root an interior pointer *into the
major heap*, which forces an interior disjunct into the post-collection
reachability predicate:

```fstar
let post_reach_from_root (post_major: heap) (post_roots: seq U64.t) (w rr: U64.t) : prop =
  let post_g = HeapModel.create_graph post_major in
  exists (r: vertex_id{mem_graph_vertex post_g r})
         (x: vertex_id{mem_graph_vertex post_g x}).
    Seq.mem rr post_roots /\
    (r == rr \/ r == HeapGraph.resolve_field post_major rr) /\
    x == w /\ reachable post_g r x
```

That much *was* made to verify (the restructuring is described below, and is
worth keeping: it is the general recipe for a duplicated existential).  The hard
blocker is downstream, in `GC.Gen.MajorReachabilityTransfer`:

`result_post_reachable_swap` moves a reachability fact from the pre-sweep heap
`h1` to the post-sweep heap `h2`.  With the interior disjunct present it must
additionally show

```
HG.resolve_field h1 rr == HG.resolve_field h2 rr      -- for every root rr
```

otherwise the entry vertex on the `h2` side cannot be reconstructed.  That
equality reduces, via `SpecObject.resolve_object_locality`, to

```
read_word h1 (hd_address rr) == read_word h2 (hd_address rr)
```

and the only tool for it is the field-data-preservation pillar of
`MS.major_gc_live_subgraph_isomorphism`, which covers fields `1 .. wosize p` of
a live object `p`.  The infix header at `hd_address rr` *is* field
`off / mword` of `p = resolve_object rr h1`, where `off = wosize(header of rr) * 8`
--- but only if `off / mword <= wosize p h1`, i.e. only if the interior root
actually points *inside* its claimed parent.

Nothing in the repository supplies that bound for a **root**.  For an interior
pointer stored in a *field* it comes from `SpecFields.wf_field_target_infix_wf`,
which yields `SpecObject.infix_addr_wf g (objects zero_addr g) dst`, whose
`infix_addr_conds` conjunct is exactly `U64.v h < p + wosize p * 8`.  Roots are
not field targets, so the condition has to be *assumed* of them.

So Phase H.2 needs, in order:

1. `SpecObject.infix_addr_wf` added as a conjunct of
   `MBP.root_valid_for_darkening` and of the minor branch of
   `roots_valid_for_minor_collection` (the honest well-formedness condition on
   an interior root: if it is interior, it points inside a genuine closure).
2. A new Cheney preservation lemma carrying that condition from a nursery
   interior root to its forwarded image --- the analogue for roots of
   `GC.Gen.CheneyPreservation.Frame`'s field-target transport (`:182-189`).
   `MCFH.fwd_image_resolves` already gives `is_infix (fwd x) updated` and the
   resolution; what is missing is `infix_addr_conds`, i.e. that the promoted
   parent is enumerated, is a closure, and still spans the offset.
3. `well_formed_heap h1 /\ well_formed_heap h2` added to
   `MRT.major_transfer_hyp` (needed for the *non*-interior case: a live root is
   enumerated in `h2`, and `well_formed_heap_part4` forbids an enumerated object
   from carrying an infix header, so it resolves to itself there).
4. A new `root_resolution_agrees h1 h2 droots rr` in
   `GC.Gen.MajorReachabilityTransfer`, and the rewrite of
   `result_post_reachable_swap` / `major_result_post_transfer` for the nested
   `exists rr. post_reach_from_root ...` shape.
5. The `GC.Gen.Impl` call site and the two SPOTs.

Step 2 is the risk: it is Cheney-layer reasoning about the geometry of a copied
closure, and there is no existing lemma to build on.

##### The restructuring that *did* work, for whoever picks this up

`post_minor_reachable` and `result_post_reachable` are the same predicate at
different arguments.  Adding the interior disjunct broke both introduction and
transport for one reason:

> While the body said only `r == rr`, the root witness `rr` was *determined* by
> the source-vertex witness `r`, so the solver recovered all three witnesses
> from one.  The disjunct severs that link, and Z3 then finds **none** of them
> --- even in an empty context, even with the entire witness body asserted at
> the intended witnesses, at any fuel/ifuel/rlimit.

Three changes together fix it:

* **Delegation.**  Define
  `post_minor_reachable minor major fp roots w = result_post_reachable res.mc_major (rewrite_roots roots prom.fwd_map) w`
  rather than restating the body, so the two are interchangeable by unfolding
  alone.
* **Factoring.**  Put the inner two binders behind `post_reach_from_root`, with
  the root as a *parameter*; `result_post_reachable` is then a one-binder
  `exists`.  Introduction becomes
  `FStar.Classical.exists_intro (post_reach_from_root ...) rr` at an explicitly
  named root, leaving the solver only the two vertices, which `r == rr` still
  determines.
* **Abstract-heap introduction lemmas.**  State the refl lemmas over an abstract
  heap (`result_post_reachable_refl_direct` / `_resolved`); performing the same
  introduction in place, where the heap is
  `(cheney_collect_spec minor major fp roots).mc_major`, does not go through.

The general rule: **keep a duplicated existential behind a folded (non-`unfold`)
function symbol whose arguments are the varying terms**, so that transport
across a propositional equality is ordinary SMT congruence.  Inlining it (via
`unfold`, or by restating the body) destroys that.

These approaches were tried and do **not** work: an equivalence lemma taking the
heap equality in `requires` (any fuel/ifuel, rlimit up to 100); restating it
over the collector's own applied terms; marking `result_post_reachable`
`unfold`; asserting the witness body at the intended witnesses before asserting
the goal; and an abstract-heap refl lemma with a *disjunctive* `requires`.

### Phase E — delete the restrictions  ✅ **done**

*Implemented.*  Both predicates are gone from `GC.Gen.HeapInvariant` (`.fsti` and
`.fst`), together with their intro/elim lemmas, their `minor_reset_*`
preservation lemmas, and their conjuncts in `minor_heap_shape_intro/_elim` and
`collection_heap_shape_intro/_elim`.

The uniform bridge that made every interior branch collapse to the old
non-interior shape is `GC.Gen.MinorCollectForwarding.Helpers.fwd_image_resolves`:
for any forwarded source `x`,

```
resolve_object (fwd x) (cheney_collect_spec …).mc_major == fwd (resolve_minor minor x)
```

so a field holding an interior nursery pointer is rewritten to an interior
pointer of the promoted copy, whose *resolution* is the image of the resolved
target.  The combined-graph edge is therefore unchanged, which is why the
`_edge_forwarded` theorems in `.Edges` kept their statements verbatim while the
`_field_forwarded` ones had to be restated over the raw stored word `ov`.

The remaining consumers were repaired module by module: `.NonPointerFields`
(`fwd_source_resolves_in_minor_objects`), `.Reflection`, `.Edges` and
`GC.Gen.MinorCollectForwarding` itself.  The two "unforwarded target is not
interior" helpers (`Reflection.minor_field_target_non_infix`,
`MinorCollectForwarding.major_field_target_non_infix`) are now proved by
contradiction against `minor_field_infix_target_forwarded` /
`major_field_infix_target_forwarded` rather than against a heap-shape clause.

`spot/GC.SPOT.ThreeObjects` keeps its crisp `read_word … == fwd a_minor`
conclusion because `spot_minor_scenario_pre` was strengthened with the
scenario-specific fact that `c`'s field holds `a_minor` itself; that is a
property of the concrete scenario, not a restriction on the collector.

The original plan for this phase follows.


Remove `minor_fields_no_infix_targets` and
`major_minor_fields_no_infix_targets` from `GC.Gen.HeapInvariant` (definitions,
intro/elim lemmas, and the `minor_heap_shape` / `collection_heap_shape`
conjuncts), drop the establishment obligations from
`spot/GC.SPOT.ConcreteScenarios.fst` and `spot/GC.SPOT.ConcreteMinor.fst`, and
update the cross-reference comment at `common/spec/GC.Spec.Fields.fst:941`.

**Prerequisite discovered while doing Phase D.** Phase D leaves ~8 `_elim` call
sites (in `GC.Gen.MinorCollectForwarding`, `.Edges`, `.Reflection`,
`.NonPointerFields`) discharging their non-interiority obligation from these two
predicates.  Replacing each with a real interior branch needs one fact that no
existing invariant supplies:

> for every live nursery object `x` and field index `i`, if the stored word is
> interior then `fwd` has an entry for the *interior* address, not just for its
> parent.

`fwd_closed` cannot supply it, because `minor_successors` now resolves: the
successor of a field holding an interior pointer *is* the parent.  Yet the field
of the promoted copy is rewritten to `fwd raw`, so `fwd raw <> 0` is exactly what
`update_object_pointers` needs.

The implementation already establishes it -- `cheney_forward_fields` applies
`cheney_forward_one` to the raw field word, and its infix branch installs
`fwd raw = fwd parent + delta` whenever the bounded guard passes, reporting OOM
otherwise.  Surfacing it means:

1. a third conjunct of `CheneyBFS.addr_covered`,
   `is_infix_in_minor minor addr ==> cs.cs_fwd addr <> 0UL`, established by
   `addr_covered_infix_step` (guard passes) and `addr_covered_intro_forwarded`
   (entry already present);
2. a `fwd_covers_infix_fields` conjunct of `fwd_well_formed`, with the
   `fwd_well_formed_covers_reachable` analogue that lifts it to every reachable
   object; and
3. only then the eight `_elim` sites, each gaining an interior branch that pairs
   the new coverage fact with Phase B's `fwd_infix_targets_wf` (the target is a
   well-formed interior pointer of the final major heap) and Phase C's already
   resolved `field_fwd_targets_in_objects`.

Step 1 rests on one further obligation, which is where the chain bottoms out.
`cheney_forward_one`'s interior branch (`GC.Gen.Cheney.fst:100`) installs the
entry only when a bounded guard passes:

```fstar
if cs'.cs_fwd parent <> 0UL &&
   U64.v addr >= U64.v parent &&
   U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
```

and when it fails the state is returned with no entry and *no* OOM report --
`GC.Gen.Impl.Cheney.forward_if_minor_infix` mirrors this in its
`U64.lt sum heap_size_u64` test.  So coverage is not merely unproved in that
path, it is false.

The guard is nevertheless never taken, and the argument is short: `delta` is the
interior object's offset inside its enclosing closure, so `minor_infix_wf` bounds
it by `minor_wosize parent * 8`; the promoted copy occupies
`[fwd parent, fwd parent + minor_wosize parent * 8)` in a `well_formed_heap`
major heap, so part 1 of well-formedness puts that whole span below `heap_size`.

**This is not a live defect, and it is worth being precise about why.**  No
theorem is violated, because `gen_gc`'s precondition makes the arm unreachable
three ways over -- every route by which an interior nursery address could reach
`forward_if_minor` is already closed:

* *as a root* -- `roots_valid_for_minor_collection`
  (`GC.Gen.MinorCollectForwarding.Helpers.fsti:84`) demands
  `is_minor_pointer r ==> Seq.mem r (minor_objects minor)`, and
  `minor_objects_not_infix` says an interior address is never in
  `minor_objects`;
* *as a nursery field* -- `minor_fields_no_infix_targets`, a conjunct of
  `minor_heap_shape`;
* *as a major-to-nursery field* -- `major_minor_fields_no_infix_targets`, a
  conjunct of `collection_heap_shape` itself.

So the reachable-subgraph isomorphism is not weak here; the precondition is
strong.  The arm is latent, and it is latent on exactly the path this work item
is opening: Phase E deletes the two field restrictions and Phase D2 the root
one, and the moment either lands the arm becomes reachable and the coverage
conjunct of `addr_covered` becomes unprovable.  That is how it surfaced -- not
by inspection, but because step 1 above is precisely the statement the arm
falsifies.

One caveat does survive at the C boundary.  The extracted collector is called
by a runtime shim that F* preconditions do not bind, and stock OCaml produces
interior roots and fields routinely (§1.1).  In the failure arm the entry is
simply not written, and both rewrite sites *skip* zero entries -- roots are left
unchanged (`GC_Gen_Impl.c:1315`) and fields are not written at all
(`GC_Gen_Impl.c:1451`) -- so the survivor would point into the nursery, which
minor collection then zeroes.  A dangling pointer, not a null.  That is reason
enough to close the arm ahead of the phases that need it.

**The promotion arm of this is done.**  `GC.Gen.AllocProps.
alloc_spec_obj_body_within_heap` derives the body bound from
`alloc_spec_obj_in_objects_part1` and `alloc_spec_preserves_wfh_part1`;
`GC.Gen.Impl.Cheney.promote_new_addr_body_bound` packages it for
`promote_object`; and the guard-failure arm that follows a successful promotion
is now `assert (pure False)`.  The extracted C is unchanged -- the runtime test
is still emitted, its else arm is merely known to be dead.

**The already-forwarded arm remains.**  There the entry `fwd parent` comes from
an earlier forwarding step rather than a fresh allocation, so the bound has to
be carried rather than re-derived.  The recipe:

* add `fwd_has_room minor cs` -- `forall x. Seq.mem x (minor_objects minor) /\
  cs.cs_fwd x <> 0UL ==> U64.v (cs.cs_fwd x) + minor_wosize minor x * 8 <=
  heap_size` -- as a conjunct of `GC.Gen.Cheney.SimOne.cheney_bfs_inv`, in the
  same shape as `fwd_infix_closed`;
* establishing it at a promotion step needs `alloc_spec_obj_body_within_heap`,
  whose three hypotheses (`well_formed_heap_part1 cs.cs_major`, `fl_valid`,
  `fl_chain_terminates`) are *not* currently part of `cheney_bfs_inv`.  Folding
  them in is the natural move and costs less than it looks: every implementation
  function that touches the state already carries all three in both its
  precondition *and* its postcondition (see `forward_if_minor_infix`), so the
  impl side needs nothing new.  The work is re-establishing them at the
  spec-level steps, where `GC.Gen.CheneyPreservation.Forwarding` already has the
  allocator preservation lemmas in hand.

Only once both arms are closed does the third conjunct of `addr_covered` hold
unconditionally, which is what steps 2 and 3 above build on.

### Phase F — audit ✅ done

`spot/GC.SPOT.MinorInfix` is the nursery analogue of `spot/GC.SPOT.InfixMajor`.
It fixes a scenario predicate `minor_infix_scenario minor major fp roots slots n
c i` — the standard minor-collection context (`collection_heap_shape`, the
remembered-set coverage facts, `cheney_no_oom`, combined-reachability of both
endpoints) together with the one thing that makes it interesting: field `i` of
major object `c` holds an address that is *interior to* a nursery closure,
`is_infix_in_minor minor (stored_target major c i)`.

Three theorems:

* `spot_minor_infix_admissible` — the scenario is admissible: the enclosing
  nursery object is a genuine `minor_objects` member carrying `Closure_tag`
  (247), the interior address has `wosize >= 2`, and it lies strictly inside
  its parent. That is, the interior pointer is well formed *as OCaml lays it
  out*, and the entry invariant accepts it.
* `spot_minor_infix_promoted` — the audit proper. After the collection the
  enclosing closure is promoted (`fwd par <> 0`), the *interior* address is
  forwarded too, its image is again an interior pointer of the post-collection
  major heap resolving to the promoted closure (offset preserved — exactly
  `caml_oldify_one`'s `*p += offset`), the major field is rewritten to that
  interior image rather than to the closure, and the post-collection heap graph
  nevertheless carries the edge `c -> fwd par`, because the graph resolves
  interior pointers. The proof chains `CG.classify_major_field_is_minor` →
  `MCFE.combined_major_minor_field_forwarded` → `MCFH.fwd_image_resolves` →
  `MCFE.combined_major_minor_edge_forwarded`.
* `spot_minor_infix_was_forbidden` — non-vacuity in the sense that matters
  here. The clause deleted from `collection_heap_shape` in Phase E is
  reproduced verbatim as a local definition, and the lemma derives `False` from
  it together with the scenario. So the scenario is *precisely, and only*, what
  the old restriction ruled out: the two theorems above were unstatable before
  Phase E.

**Satisfiability gap (open).** `spot_minor_infix_was_forbidden` shows the
scenario is exactly the deleted restriction's complement, but it does not
exhibit a concrete witness the way `GC.SPOT.InfixMajor` does for the major
heap. A witness needs a nursery *containing* a closure with an infix header,
and there is currently no way to build one: `GC.Gen.MinorHeap` only ever
produces `minor_state`s through `minor_init` and `minor_alloc_spec`, and every
allocated object body is zero. Adding a body-write primitive means proving that
writing a body word preserves the abstract `minor_chain_valid` /
`minor_chain_no_infix`, and the existing `_read_eq` lemmas require agreement
*below bump*, which a body write violates — so it needs a new induction
tracking which positions the chain visits (hence chain-object
non-overlap), in `GC.Gen.MinorHeap.fsti`. That interface change invalidates the
entire `.checked` cache on every iteration, which is why it is deferred.

### Phase G — an OCaml-level test ✅ done

`generational/ocaml-integration/tests/infix_closures.ml` gains three nursery
groups (8, 9, 10), taking it from 678 to 2128 assertions. All pass under the
verified runtime and, as a differential check, under stock OCaml.

* **8 — major → minor.** A slot is first forced into the major heap (proved by
  showing a minor collection does not move it), then an interior pointer to a
  brand-new closure group is stored into it, so the edge arrives through the
  remembered set. Nothing else references the group. After one minor collection
  the target address has *changed* — so the group really was in the nursery —
  the field is still `Infix_tag`, `Obj.size` (the offset back to the parent) is
  unchanged, `Obj.reachable_words` is unchanged, and all three closures in the
  group still compute the right answers. Then mark & sweep is run and must not
  move it.
* **9 — minor → minor.** Referrer and closure group are both young, so the edge
  is found by Cheney scanning rather than the remembered set, and both are
  promoted in the same pass. Because the parent is observable here, the offset
  relation is checked as an *address difference*: `interior − parent ==
  wosize*8` before and after, with the difference itself invariant. Sharing is
  also checked — the field and a second referrer still hold the same address.
* **10 — sweep pressure.** 200 nursery groups anchored from a promoted array by
  interior pointers only, with 200 more dropped; every survivor is shown to have
  moved out of the nursery with its offset, reachable-word count and computed
  values intact, and to survive three subsequent major collections.

The `**Scope**` note in `generational/ocaml-integration/README.md`, which used
to say these heaps fell outside the generational invariant, is updated: they are
now inside it in both generations.

Two further groups (11, 12) were added when Phase H was scoped, taking the
count to 2514.  They move the interior pointer out of the heap entirely and
into a **root**: the closure block is referenced by nothing but a local
variable, which the bytecode runtime scans off the stack verbatim.  Group 11
takes one such root through promotion and then through mark & sweep, checking
the infix offset, the reachable-word count and every computed value at each
step; group 12 keeps 24 of them live simultaneously, one per frame of a
recursion, with the collections forced at the innermost frame.  Both pass under
the verified runtime and under stock OCaml.

These two groups are the evidence for the claim made in Phase H: the collector
handles interior roots today, and it was only the specifications that described
a root as its own object.  Phase H.1 has since lifted the major-heap half of
that; the nursery half is Phase H.2.

## 5. Risks

* **Verification cost.** `CheneyPreservation.*` dominates the build. Phases C
  and D may need the `EAGER_QI_CHECKED` membership revisited per module, and
  the Z3 4.15.3 mitigations (top-level helper lemmas over abstract parameters,
  per-branch `assert` of the exact goal) will be needed.
* **Precondition strengthening.** Phase A adds two conjuncts to a client
  obligation. Justified by §1.5/§1.6, but it must be documented as a mutator
  trust assumption alongside `minor_guards_complete`.
* **No C change expected**, but extraction must be re-run and the snapshot
  diffed to confirm it.

## 6. Sequencing

A → B → C → D → E, each verified and committed separately; F and G afterwards.
Phase A is independently useful and low-risk, so it can land first regardless
of how B lands.  Phase D2 sits between D and E; **Phase H --- interior pointers
held directly in a root --- is separate and open** (see "What is left,
precisely" under Phase D2).

**Status.** Phases A, B, C and D are done: each landed as its own fully verified
commit, with the extracted C byte-identical throughout.  What that buys, today:

* the spec-level model of interior pointers is complete and non-vacuous --
  `minor_infix_wf` mirrors `GC.Spec.Object.infix_addr_conds` conjunct for
  conjunct, and a promoted interior target is proved to be a well-formed
  interior pointer of the final major heap;
* the *combined graph* and the *Cheney live set* both resolve interior field
  values, so an object referenced only through an interior pointer is a
  first-class member of the reachable set rather than an absent vertex;
* the forwarding map's root coverage is stated in resolved form, matching what
  the implementation actually establishes.

**Status (final).**  Phases A through G are done and committed, each fully
verified with the extracted C byte-identical throughout.  `gen_gc` accepts, and
correctly collects, a heap whose nursery *and* major fields hold interior
pointers; `spot/GC.SPOT.MinorInfix` audits that on a concrete heap and
`generational/ocaml-integration/tests/infix_closures.ml` exercises it against
real OCaml closures.

What remains restricted is exactly one thing: a **root** may not itself be an
interior pointer.  `MCFH.roots_valid_for_minor_collection` still places every
nursery root in `minor_objects minor`, and
`GC.Impl.MarkBoundedPrecondition.root_valid_for_darkening` still requires a
major root to be an enumerated object.  Both implementations already resolve
such a root; only the specifications are conservative.  Lifting the restriction
is Phase H, scoped and measured above.

## 7. Recommendation

Proceed. The restriction rules out a heap shape that stock OCaml produces
routinely (§1.1), while the implementation and the extracted C already handle
it correctly (§2.1) and the spec-level forwarding function already models it
(§2.2). The remaining work is confined to the preservation proofs, and follows
a pattern already executed once for the major heap.

*Done for fields.*  For roots (Phase H) the same recommendation holds and for
the same reason --- both collectors already resolve roots at run time --- but
the work is larger than the rest of this plan assumed, because it changes
`gen_gc`'s published `roots_match_stack` postcondition.  It should be planned
and landed on its own, not bolted onto Phase D2.
