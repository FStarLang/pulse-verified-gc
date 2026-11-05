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


## Fixed: the proactive full collection counted only promotion

**Observed by:** writing `tests/explicit_major.ml` (a first draft that
allocated its churn directly in the major heap died with "promotion failed")

`do_minor_gc` starts a full collection when the words that went through minor
collections since the last one exceed half the major heap. Words allocated
directly in the major heap (`caml_alloc_shr`: blocks over `Max_young_wosize`)
are not counted. A program that allocates mostly large blocks fills the major
heap with garbage that only a failed major allocation collects; if the next
minor collection comes first, its promotion finds no room, and promotion
failure is fatal. Fixed by counting direct major allocation towards the
trigger (4.14's `caml_allocated_words`): stop-the-world in
`bytes_promoted_since_major` (issue #34, `tests/large_alloc_garbage.ml`);
with `VERGC_MAJOR=incremental` the trigger and the pacing count the words
promoted and allocated directly, and a minor collection mid-cycle that may
not fit finishes the cycle first.

---

## Open: runtime paths outside the collector's model of the program

**Observed by:** the runtime audit for the incremental sweep

The verified collector's contracts (`GC.Gen.Impl`'s trusted bridge
obligations) model the program as allocation, field writes through
`caml_modify` / `caml_initialize` (since M3 the verified barrier,
`GC.Gen.Impl.Barrier`, whose precondition `GC.Gen.Barrier.modify_ok` is the
trusted part), and nursery allocation. These runtime paths
change a live major block in other ways; each is safe in both major modes for
the reason given, but none is covered by a proof:

- **`Obj.truncate` is unsupported**: `caml_obj_truncate` raises
  `Invalid_argument "Obj.truncate: not supported by the verified GC"` for
  every block and changes nothing (OCaml 5 removed it). Shrinking a block in
  place leaves a leftover block the collector's invariants have no account
  of, so it is ruled out rather than argued safe
  (`generational/ocaml-integration/tests/obj_truncate.ml`). Neither the stdlib
  nor OCaml's own testsuite calls it.
- **Tag changes**: `Obj.set_tag`, `Lazy` forcing (`Forward_tag`),
  `caml_update_dummy`. They write the tag byte, never the colour.
- **Closure bodies written through `caml_modify`**: `caml_update_dummy` of a
  closure value (`let rec` of values whose right-hand sides are closures)
  copies the closure's words -- code pointers, the closure info word, infix
  headers -- into the dummy with `caml_modify`, after setting its tag to
  `Closure_tag`. `modify_ok` asks for a block that is not a closure (its body
  holds the infix headers interior pointers resolve through). At run time
  the verified barrier does what stock's does (the old values are the
  dummy's immediates, so nothing is darkened, and a young value copied from
  the closure's environment is remembered), and a dummy of at most `Max_young_wosize` words is young, so
  its writes never reach the barrier.
- **Slots outside the verified heap**: `caml_modify` / `caml_initialize` of a
  slot that is neither in the nursery nor in the verified major heap (native
  code's static data) take the stock logic in the bridge (`vergc_modify`,
  without darkening), not the verified barrier. While marking that needs no
  darkening: such a slot is a root (a module block's field), and what a root
  held when the cycle started was darkened by `start_cycle`. If such a slot gets a young
  value it goes into the ref table, which `ref_table_sound_with` does not
  allow; the minor collection's slot rewrite (`rewrite_one_slot`, which only
  checks `slot < heap_size`) rewrites it as stock would.
- **Intern** (`Marshal.from_*`): a block of at most `Max_wosize` words is one
  `caml_alloc_shr` block carved into objects that all get that block's colour.
  That is the colour the allocator would give each of them, because the sweep
  does not run during intern, so they are all on the same side of the cursor
  (and while marking all are black, as each would be).
  A larger one (over 2^54 words, so not in practice) goes to a stock heap
  chunk outside the verified heap.
- **Infix headers** (`CLOSUREREC`, `caml_alloc_dummy_infix`) are written inside
  a closure block; their colour is irrelevant.
- **Weak arrays and ephemerons** are `Abstract_tag` blocks that nothing cleans
  (see "finalisers and weak pointers are not run"). `Weak.get` can return a
  block that marking did not reach: stop-the-world a freed one, mid-sweep a
  one *pending free* (white, in front of the cursor), whose resurrection breaks the
  sweep phase's invariant. Same class of bug in both modes; the weak and
  ephemeron tests are expected failures (`regression/pr5233` among them since
  `Gc.full_major` runs the verified collector).
- **Stock's major collector, compaction, and heap finalisation** never run:
  `Gc.major`, `Gc.full_major` and `Gc.compact` call the verified collector
  directly, `caml_major_collection_slice` and `caml_finish_major_cycle` forward
  to it, `caml_compact_heap` and `caml_finalise_heap` do nothing, and the
  remaining stock entry points are fatal (`VERGC_STOCK_GC_UNREACHABLE`) (so `Gc.compact` does not compact, and `Gc.set`'s policy change
  is not honoured). Stock's `caml_gc_phase` therefore stays `Phase_idle`, and
  every path still guarded by it (`weak.c`, `finalise.c`) is dead;
  `caml_modify` and `caml_array_fill` darken at the verified collector's
  phase instead, through the verified barrier.

---

## Open: every promotion failure is reported as "major heap full"

**Observed by:** instrumenting the pre-fix build while diagnosing the nursery
no-scan bug below

`cheney_promote_phase` reports failure through a single `bool oom`, and
`verified_gc/alloc_gen.c` renders any `false` as

```
verified gen GC: promotion failed — major heap full (30 MB)
  Set MIN_EXPANSION_WORDSIZE=8000000 (or larger) to increase heap.
```

That flag is set by seven distinct sites in `GC_Gen_Impl.c`, only some of which
are genuine allocation failures. The rest are defensive refusals — most notably
"cannot promote a zero-word object", which is what actually fired in the no-scan
diagnosis below with the major heap 99.5% empty. The advice to raise
`MIN_EXPANSION_WORDSIZE` is then actively misleading: no heap size could have
helped.

This is a diagnostics defect, not a soundness one — the collector correctly
declines and aborts rather than proceeding. Fixing it means widening the failure
channel (an enum, or at minimum distinguishing "allocator returned null" from
"refused a malformed object") and having `alloc_gen.c` print accordingly.

---

## Open: incremental marking restarts a partly scanned object on a write

**Observed by:** the design of the mark slice (M4); see DESIGN_AND_IMPL.md,
"The mark slice"

With `VERGC_MAJOR=incremental` a mark slice scans a large object a budget's
worth of fields at a time, and a write into a field it has already scanned
restarts the object's scan (the object is grey and its scanned fields must
stay dark; 4.14 blackens first and needs no restart).  A program that keeps
writing into a large array the marker is half way through can therefore
keep that cycle's marking from ending in slices; it then ends when memory
runs short (a minor collection without room finishes the cycle: one long
pause) or at the next full collection.  Not observed in the tests or
benchmarks (`tests/incremental_mark.ml` writes into a 60000-element array
mid-scan and its cycles end in slices), but nothing bounds it.  The fix
would be 4.14's: resume after the written field rather than from the start,
which needs a different cache invariant.

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

## Fixed: the minor collection assumed distinct remembered slots

**Checked by:** `spot/GC.SPOT.DuplicateSlot` (proof, no runtime test)
**Fixed in:** `GC.Gen.TwoPassEquiv` (the precondition was dropped)

The minor collection's contract used to require `slots_pairwise_distinct`:
no field listed twice in the remembered set. Stock `caml_modify` does not
guarantee that. A field written young -> immediate -> young is recorded twice,
because the second write sees an immediate old value, and the bridge passes
`caml_ref_table` through without deduplicating. The obligation was unmet, not
just unchecked.

No bug came of it, because rewriting a slot twice does nothing the second time.
The first rewrite forwards the slot to a major copy, and a forwarding target is
never a forwarded nursery pointer (`fwd_targets_stable`). The proof now shows
this (`rewrite_slots_iter_slot_effect` holds for any slot sequence), and the
precondition is gone from `minor_collect`, `minor_collect_with` and `full_gc`.

---

## Fixed: `Gc.full_major` ran stock's major collector over the verified heap

**Regression test:** `tests/explicit_major.ml` (`make correctness`)
**Fixed in:** `patches/runtime_gen.patch` (`runtime/major_gc.c`,
`runtime/compact.c`)
**Severity:** heap corruption -- reachable from safe OCaml

`caml_gc_full_major`, `caml_gc_major`, `caml_gc_compaction` and `Gc.set`'s
policy change call stock's `caml_finish_major_cycle`, and `caml_gc_dispatch`
calls `caml_major_collection_slice`; the patch left both alone. So
`Gc.full_major ()` ran stock's mark and sweep. The verified major heap is
registered `In_heap` in the page table, so stock's mark darkened every object
reachable in it, while stock's sweep walks only stock's own (empty) chunks
and never whitened them. The idle heap was left full of black objects. A
fresh white block stored into one of them was then invisible to the next
verified mark (which does not rescan a black object), and the verified sweep
freed it while it was reachable:

```ocaml
let a = Array.make 2000 [||] in          (* major *)
Gc.full_major ();                         (* stock cycle: a is now black *)
for i = 0 to 1999 do a.(i) <- Array.make 300 i done;
(* ... allocate until a verified collection runs: a.(i) freed, SIGSEGV *)
```

The `Gc` calls now run the verified collector (`verified_do_full_gc`: the
nursery emptied and a whole verified cycle, called from `runtime/gc_ctrl.c` and
from `caml_finish_major_cycle`; `verified_major_collection_slice`: with
`VERGC_MAJOR=incremental` a slice, or the start of a cycle when idle), compaction and
`caml_finalise_heap` do nothing, and stock's `caml_gc_phase` never leaves
`Phase_idle`.

---

## Fixed: the major allocator wrote the block size, not the requested size

**Issue:** [#19](https://github.com/FStarLang/pulse-verified-gc/issues/19)
**Regression test:** `tests/alloc_exact_promotion.ml` (`make correctness`)
**Fixed by:** right-justified allocation (`GC.Spec.Allocator`, `GC.Impl.Allocator`)
**Severity:** an object field that is not a value, visible from safe OCaml
(`Array.length` is one too large)

When a free block was exactly one word longer than the request, the allocator
handed the whole block over and wrote the header with the *block's* wosize.
On the direct major path the runtime overwrites that header straight away, so
nothing sees it. Promotion does not: the minor-to-major copy rebuilds the
header from the one the allocator wrote, so the promoted object declares one
field more than was copied into it, and that field is not a value.

The reproducer fragments the major heap into blocks of wosize 101 pinned
between survivors, then promotes objects of wosize 100, so every request
leaves a one-word remainder. It checks `Array.length` of each promoted object
and passes under stock OCaml. Before the fix, 6793 of 22671 promoted objects
declared 101 fields under the verified GC.

`tests/ast-invariants` in OCaml's testsuite tripped over the same bug natively,
but only on some platforms, because it depends on something following the
extra field and faulting.

The fix is the one stock OCaml uses: allocation is right-justified. The object
is carved from the *end* of the free block, so its header always records
exactly the requested size, and whatever is left (even a single word) stays
behind as a free remainder. See `docs/allocator-exactness.md`.

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
that promoted nonsense.

The observed symptom is the abort `"promotion failed — major heap full"`, which
is a misnomer worth spelling out. Instrumenting the pre-fix build shows the
major heap is essentially empty at the abort (18,716 words promoted into a
30 MB heap) and that **no** allocation ever failed. The real path: the forged
word makes the scan read field 0 of the anchor as a header; that word is the
OCaml immediate `2i+1`, whose tag byte is 249 (`Infix_tag`) for `i ∈ {124, 252,
380}`; its `wosize` is `(2i+1) >> 10 == 0`, so the infix walk computes
`parent = child - 0 == child` and the promoter hits its defensive "cannot
promote a zero-word object" branch. That branch sets the `oom` flag, and
`cheney_promote_phase`'s single boolean result is rendered by `alloc_gen.c` as
"major heap full". Measured: 9 refusals = 3 anchors × 3 minor collections. The
misleading diagnostic is itself an open issue, recorded above.

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
`minor_no_scan_invariant` alone would still have left `full_gc`'s precondition
falsified by an ordinary young `Bytes.t`. `GC.Gen.ReachabilityBridge.
minor_no_pointer_to_blue` was narrowed with it.

`spot/GC.SPOT.NoScanMinor` is the machine-checked witness that the relaxation is
real: a three-word nursery holding one tag-251 block whose body words are `8`,
a value `is_minor_pointer` accepts. `spot_ns_minor_was_forbidden` refutes the
deleted clause; `spot_ns_collection_heap_shape` proves `full_gc`'s full entry
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
