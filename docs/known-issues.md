# Known issues

Gaps that are open in the verified generational collector, each with a
reproducer under `generational/ocaml-integration/tests/`. Run them with

```bash
make -C generational/ocaml-integration/tests known-gaps
```

There are currently none: the last one graduated to a regression test.

Fixed issues are kept below for the record, because their reproducers are now
regression tests and it is useful to know what they were guarding. Run those
with `make -C generational/ocaml-integration/tests correctness`.

---

---

## Open: finalisers and weak pointers are not run

**Observed by:** `tests/no_scan.ml` section 4 (which skips its liveness
assertion when the control finaliser does not fire)

`Gc.finalise` registers callbacks but the verified runtime never runs them,
and `Weak.get` does not track liveness. `no_scan.ml` therefore compares
against a *control* — a second doomed block with no forged reference — and
only asserts collection when the control's finaliser fires, so the test
carries no information on a runtime without finalisers rather than failing
spuriously.

---

## Fixed: `caml_minor_collection()` was a no-op

**Regression test:** `tests/make_vect_barrier.ml`
**Fixed in:** `patches/runtime_gen.patch`, `runtime/minor_gc.c`
**Severity:** heap corruption — reachable from safe OCaml

`ocaml-4.14-verified-gen/runtime/minor_gc.c` used to stub the function out:

```c
CAMLexport void caml_minor_collection (void)
{
  /* Disabled: we use our own verified GC.
     Keep the function body empty so callers don't crash. */
}
```

But four callers (`array.c`, `custom.c`, and two in `weak.c`) use it to
establish "the value I am holding is no longer young", and then rely on that
to store the value **without a write barrier**. `caml_make_vect` is the
sharpest:

```c
if (Is_block(init) && Is_young(init)) caml_minor_collection ();
CAMLassert(!(Is_block(init) && Is_young(init)));
res = caml_alloc_shr(size, 0);
/* "We now know that [init] is not in the minor heap, so there is
    no need to call [caml_initialize]." */
for (i = 0; i < size; i++) Field(res, i) = init;
```

With an empty body `init` stayed young, the `CAMLassert` was compiled out of
the release build, and those `size` raw stores created major→minor pointers
recorded in **neither** the `ref_table` **nor** any root set. The next minor
collection promoted the target without updating them and left every slot
dangling:

```ocaml
let y = Array.make 4 7 in
let a = Array.make 300 y in   (* 300 > Max_young_wosize = 256 *)
(* ... one minor collection ... *)
a.(0)                          (* garbage: bad length, bad tag *)
```

The boundary was exactly `Max_young_wosize`: `Array.init 256` was clean and
`Array.init 257` corrupted every element, because 257 is where the container
is born in the major heap and takes the `caml_make_vect` path above.

`verified_do_minor_gc()` already existed in `verified_gc/alloc_gen.c`, with a
comment naming this exact scenario — it was simply never called. The fix wires
it up. Note this was an **integration** bug in the OCaml runtime glue, not a
defect in the verified F\*/Pulse collector: the extracted C is unchanged.

---

## Fixed: no-scan blocks in the nursery were scanned

**Regression test:** `tests/nursery_no_scan_interior.ml` (now part of
`make -C generational/ocaml-integration/tests correctness`), plus
`tests/no_scan.ml` section 9, whose interior-pointer case was restored when
this was fixed.
**Severity:** soundness — was reachable from safe OCaml, no `Obj` needed
**Scope:** minor collection only; the major heap was always correct

A block whose tag is `>= no_scan_tag` (251) — `string`/`Bytes`, `Int64`/
`Int32`/`nativeint` boxes, `Bigarray`, flat float arrays, and custom blocks —
holds raw bytes, not fields. Its contents are ordinary program data and may
hold *any* bit pattern, including values that look exactly like heap
addresses. A collector must never interpret them as pointers.

The major heap always got this right. Both major-heap passes in
`generational/snapshot/GC_Gen_Impl.c` are guarded:

| Function | Guard |
|---|---|
| `update_all_objects` | `if (tag >= no_scan_tag) { /* skip body */ }` |
| `mark_and_push` | `if (!(tag >= no_scan_tag)) push_children_bounded_impl(...)` |

The nursery did not. `scan_loop` (the Cheney scan) read the header, took
`wosize`, and walked every field with no tag test at all, so every word of a
young `Bytes.t` was a candidate pointer during a minor collection. The same
loop contains the infix-aware path: a word that is 8-aligned and lands inside
the nursery is looked up in the forwarding array, and if the block it appears
to point at carries tag 249 the collector reads a synthetic infix header and
walks *backwards* to a supposed parent closure. Applied to arbitrary bytes,
that promoted nonsense and the program died with "major heap full".

### Why the proof did not catch it

The missing guard did not slip past a postcondition. It was admitted by a
*precondition* that `gen_gc` assumed and that nothing on the C side
established. The chain was:

```
GC.Gen.Impl.fsti          gen_gc  requires  collection_heap_shape minor 's 'fp
GC.Gen.HeapInvariant.fst    collection_heap_shape = major_heap_shape
                                                  /\ minor_heap_shape
                                                  /\ minor_major_fields_no_blue
GC.Gen.HeapInvariant.fst    minor_heap_shape      = minor_wf
                                                  /\ minor_guards_complete
                                                  /\ minor_infix_wf
                                                  /\ minor_no_scan_invariant
```

and `GC.Gen.Promote.minor_no_scan_invariant` read:

```fstar
let minor_no_scan_invariant (minor: minor_state) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects minor) /\
    minor_tag minor obj >= 251 /\
    j < minor_wosize minor obj ==>
     ~(is_pointer_field (minor_read_field minor obj j)) /\
     ~(is_minor_pointer (to_minor_offset (minor_read_field minor obj j)))
```

That is exactly the property the reproducer violated. Under this hypothesis a
young no-scan block provably contains nothing pointer-shaped, so walking its
fields is a no-op and the guard in `scan_loop` was *redundant*. The
implementation was correct with respect to the specification; the
specification assumed the case away. That is also why deleting the invariant
and adding the guard turned out to be one and the same piece of work.

Note the asymmetry with the major heap, which is what made that half cheap:
`well_formed_heap` parts 2 and 3 are guarded by
`GC.Spec.Fields.fields_constrained` (`= not is_no_scan`), so the major
specification is *unconditionally* silent about no-scan bodies and needed no
implementation change. The nursery instead stated its field property over
*all* objects and then excluded the inconvenient ones by hypothesis.

It leaked at the extraction boundary: these are `pure` conjuncts of a Pulse
precondition, so they are erased. `verified_gc/alloc_gen.c` calls
`minor_collect_full(...)` with data only — no check, and no comment recording
the debt. And the assumption was not merely unchecked but *false* for
ordinary programs: `is_minor_pointer v` is just
`8 <= v < minor_heap_size && v % 8 = 0`, i.e. "an 8-aligned integer below
256 KB", which any young `Bytes` holding a small little-endian integer
satisfies.

### The fix

A single new definition in `GC.Gen.MinorHeap`:

```fstar
let minor_scan_wosize (ms: minor_state) (obj: U64.t) : nat =
  if minor_tag ms obj >= 251 then 0 else minor_wosize ms obj
```

used at every point where the collector *reads* a nursery body — the Cheney
scan (`GC.Gen.Cheney.cheney_scan`), the combined graph
(`GC.Gen.CombinedGraph.minor_object_edges`), `GC.Gen.Reachability.
minor_successors`, and the BFS/preservation development — while *promotion*
keeps using the true `minor_wosize`, since it copies the whole body verbatim
regardless of tag. This mirrors `major_object_edges`, which already had the
`if is_no_scan obj major then Seq.empty` clause.

The obligation `minor_tag minor src < 251` that this creates in
`GC.Gen.MinorCollectForwarding.{Reflection,Edges}` is discharged by
strengthening
`GC.Gen.CheneyPreservation.Fields.cheney_promote_fwd_target_no_scan_iff_minor_tag`
from `is_no_scan target = false` to
`is_no_scan target = (minor_tag minor x >= 251)` — an equation, which is sound
because `promote_object` copies the source tag verbatim. An edge out of the
image then implies the image is scannable, hence the source was.

`minor_no_scan_invariant` is deleted. `minor_heap_shape` is now just
`minor_wf /\ minor_guards_complete /\ minor_infix_wf`.

`GC.Gen.HeapInvariant.minor_major_fields_no_blue` — the third conjunct of
`collection_heap_shape` — was narrowed to `minor_scan_wosize` at the same time,
and for the same reason: it quantified over *every* young field, so deleting
`minor_no_scan_invariant` alone would still have left `gen_gc`'s precondition
falsified by an ordinary young `Bytes.t`. `GC.Gen.ReachabilityBridge.
minor_no_pointer_to_blue` was narrowed with it.

`spot/GC.SPOT.NoScanMinor` is the machine-checked witness that the relaxation is
real: a three-word nursery holding one tag-251 block whose body words are `8`,
a value `is_minor_pointer` accepts. `spot_ns_minor_was_forbidden` refutes the
deleted clause; `spot_ns_collection_heap_shape` proves `gen_gc`'s full entry
invariant of the same nursery.

In the extracted C, `scan_loop` gained:

```c
uint64_t tag = hdr & 0xFFULL;
uint64_t wosize;
if (tag >= 251ULL) wosize = 0ULL; else wosize = hdr >> 10U;
```

### Still outstanding: the other two mutator trust assumptions

`minor_no_scan_invariant` was not the only unchecked hypothesis about nursery
contents. Two neighbours remain, and the reproducer's three patterns
discriminate between them:

| Predicate | Says | Labelled in source |
|---|---|---|
| `minor_guards_complete` (`MinorHeap.fsti`) | any word that *looks* like a valid header **is** a real object | "In practice OCaml tagged values ... do not produce such confusion" |
| `minor_infix_wf` (`MinorHeap.fsti`) | any infix-looking address has a real `Closure_tag` parent | "trust assumption on the mutator" |

Before the fix, `interior` (`v + 8`) violated all three and was the pattern
that aborted; `plain` violated only the no-scan invariant and survived by
luck. Both remaining assumptions are now only reachable through *scanned*
fields, where a well-typed OCaml mutator does not violate them — but they are
still assumptions about mutator data, and ideally would be replaced by
runtime tests in the same way.
