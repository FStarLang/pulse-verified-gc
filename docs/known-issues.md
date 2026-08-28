# Known issues

Gaps that are open in the verified generational collector, each with a
reproducer under `generational/ocaml-integration/tests/`. Run them with

```bash
make -C generational/ocaml-integration/tests known-gaps
```

Fixed issues are kept at the bottom for the record, because their reproducers
are now regression tests and it is useful to know what they were guarding.

---

## Open: no-scan blocks in the nursery are scanned

**Reproducer:** `tests/nursery_no_scan_interior.ml`
**Severity:** soundness — reachable from safe OCaml, no `Obj` needed to trigger
**Scope:** minor collection only; the major heap is correct

A block whose tag is `>= no_scan_tag` (251) — `string`/`Bytes`, `Int64`/
`Int32`/`nativeint` boxes, `Bigarray`, flat float arrays, and custom blocks —
holds raw bytes, not fields. Its contents are ordinary program data and may
hold *any* bit pattern, including values that look exactly like heap
addresses. A collector must never interpret them as pointers.

The major heap gets this right. Both major-heap passes in
`generational/snapshot/GC_Gen_Impl.c` are guarded:

| Function | Guard |
|---|---|
| `update_all_objects` | `if (tag >= no_scan_tag) { /* skip body */ }` |
| `mark_and_push` | `if (!(tag >= no_scan_tag)) push_children_bounded_impl(...)` |

The nursery does not. `scan_loop` (the Cheney scan) reads the header, takes
`wosize`, and walks every field with no tag test at all:

```c
uint64_t hdr    = minor_read(minor, obj - 8ULL);
uint64_t wosize = hdr >> 10U;
...
while (field_idx < wosize) { /* every word treated as a candidate pointer */ }
```

So every word of a young `Bytes.t` is a candidate pointer during a minor
collection. The same loop contains the infix-aware path: a word that is
8-aligned and lands inside the nursery is looked up in the forwarding array,
and if the block it appears to point at carries tag 249 the collector reads a
synthetic infix header and walks *backwards* to a supposed parent closure.
Applied to arbitrary bytes, that promotes nonsense.

Observable effect, from pure OCaml:

```ocaml
let anchors = Array.init 400 (fun i -> Array.make 4 i) in
for i = 0 to 399 do
  let b = Bytes.make 48 '\000' in
  (* a word-aligned address pointing INTO another young block *)
  let a = Int64.add (address_of anchors.(i)) 8L in
  Bytes.set_int64_ne b 0 a;
  keep.(i) <- b
done
(* next minor collection: *)
(*   verified gen GC: promotion failed — major heap full *)
```

Writing the *exact* address of a live young block (rather than an interior
one) is tolerated today, because following it merely promotes something that
was live anyway. It is the interior/garbage patterns that break — and those
are exactly what a length-prefixed binary format or a serialized pointer-like
value produces by accident. `nursery_no_scan_interior.ml` runs all three
patterns (`odd`, `plain`, `interior`) so the discriminating one is obvious.

### Specification side

The matching gap is that `GC.Gen.CombinedGraph.major_object_edges` skips
no-scan sources but `minor_object_edges` does not, so `gen_gc` still carries a
nursery counterpart of the `no_scan_invariant` that real OCaml heaps violate.
The major-heap half of that invariant was removed (see
`docs/no-scan-support-plan.md`); the nursery half was deliberately deferred
because adding the guard creates an obligation `minor_tag minor src < 251` at
three points in `GC.Gen.MinorCollectForwarding.Reflection`, which needs the
converse of
`GC.Gen.CheneyPreservation.Fields.cheney_promote_fwd_target_not_no_scan_of_minor_tag_lt`
threaded through `forward_one` / `forward_fields` / `forward_roots` / `scan` /
`promote`.

**Fixing it means changing the implementation as well as the proof:** a
`tag >= no_scan_tag` guard in `GC.Gen.Impl.Cheney`'s scan loop, mirroring the
two major-heap guards, and then re-establishing the Cheney correctness and
preservation lemmas against the guarded spec. Unlike the major-heap
relaxation, this one *will* change the extracted C.

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
