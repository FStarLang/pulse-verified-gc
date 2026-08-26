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

### Phase E — delete the restrictions

Remove `minor_fields_no_infix_targets` and
`major_minor_fields_no_infix_targets` from `GC.Gen.HeapInvariant` (definitions,
intro/elim lemmas, and the `minor_heap_shape` / `collection_heap_shape`
conjuncts), drop the establishment obligations from
`spot/GC.SPOT.ConcreteScenarios.fst` and `spot/GC.SPOT.ConcreteMinor.fst`, and
update the cross-reference comment at `common/spec/GC.Spec.Fields.fst:941`.

### Phase F — audit

A minor-heap analogue of `spot/GC.SPOT.InfixMajor`: a concrete nursery holding
a five-word closure with an infix sub-object, referenced from a second minor
object's field *and* from a major object's field via the remembered set. Show
it satisfies `collection_heap_shape`, call `gen_gc`, and characterise the post
heap. This is what would give the same confidence the major-heap SPOT gives.

### Phase G — an OCaml-level test

Extend `generational/ocaml-integration/` with a mutually recursive closure that
stays in the nursery across a minor collection, mirroring the existing
major-heap infix test.

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
of how B lands.

## 7. Recommendation

Proceed. The restriction rules out a heap shape that stock OCaml produces
routinely (§1.1), while the implementation and the extracted C already handle
it correctly (§2.1) and the spec-level forwarding function already models it
(§2.2). The remaining work is confined to the preservation proofs, and follows
a pattern already executed once for the major heap.
