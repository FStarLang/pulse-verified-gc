Status: design, pre-Stage-3 capture

# Forwarding pointer & tag handling

## TL;DR

OCaml marks a forwarded minor-heap object with `Forward_tag = 250` in the
tag byte and the promoted address in `field[0]`. We instead overwrite the
header *color* to `Blue` (already in our 2-bit palette) and keep `field[0]`
for the promoted address. This preserves `GC.Lib.Header`'s 8/2/54 bit
layout, keeps the full 0–255 tag range free for the OCaml tag taxonomy,
and avoids overload with `Forward_tag`'s lazy-value semantics. The
`wosize == 0` case (no `field[0]` slot) writes a `0xFFFFFFFFFFFFFFFF`
sentinel — unreachable as a major address since the major heap fits in
`pow2 57`. Clients must check the header color before reading `field[0]`
as a forwarding pointer.

## Background: OCaml's `Forward_tag` encoding

Per the [Real World OCaml GC chapter][rwo-gc], OCaml's minor collector
copies a live young block into the major heap, then rewrites the original
header so that subsequent root scans can chase the forwarding pointer:

- The original header's tag byte becomes `Forward_tag = 250`.
- `field[0]` is overwritten with the new major-heap address.
- The wosize is left intact (so the original slot is still walkable).

The same tag value also marks user-visible *lazy* values that have been
forced — the runtime relies on the context (location, surrounding code)
to disambiguate. In a verified setting this overload is awkward: we would
have to spec away the lazy-value case and prove no minor-heap object
*starts life* with `Forward_tag` before the promotion pass runs.

## Our choice: Blue-color sentinel

`common/lib/GC.Lib.Header.fst:58-62` defines

```fstar
type header_sem = {
  wosize : w:uint_t 64{w < pow2 54};
  color  : color_sem;       // White | Gray | Blue | Black
  tag    : t:uint_t 64{t < 256};
}
```

In the major heap, `Blue` already means "free-list block". Minor-heap
objects in our model never carry `Blue` during normal operation — every
freshly bump-allocated young block is `White`. We therefore overload `Blue`
in the minor heap to mean "forwarded":

| Heap  | `Blue` color means         |
| ----- | -------------------------- |
| Major | free-list block            |
| Minor | forwarded to major (field[0] holds new address) |

Why this is verification-friendly:

1. **No tag-space carve-out.** `tag` retains its full 0–255 range, matching
   OCaml's structured / no-scan taxonomy (see below) one-to-one.
2. **No collision with `Forward_tag` lazy semantics.** `tag == 250` simply
   becomes a `well_formed_minor` precondition (out of scope).
3. **No header layout change.** `pack_header` / `unpack_header` in
   `GC.Lib.Header` stay bit-for-bit identical, so `end_to_end_correctness`
   (`mark-and-sweep/spec/GC.Spec.Correctness.fsti:123-164`) holds unchanged.
4. **Disjoint color discipline.** The minor heap is a separate `seq U8.t`
   from the major heap, so the major's `Blue ⇔ free-list` invariant is
   unaffected.

The detection helpers (in pseudo-F* form, to be added to
`GC.Spec.MinorCollect` in Stage 3):

```fstar
let is_forwarded (m: minor_state) (obj: obj_addr) : bool =
  let h = m_read_header m (obj - mword) in
  h.color = Blue && h.wosize >= 1

let read_forwarding (m: minor_state) (obj: obj_addr{is_forwarded m obj})
  : obj_addr
  = m_read_word m.m_data obj                  // field[0]
```

## OCaml tag taxonomy and our treatment

`oldify_one_spec` (Stage 3, in `mark-and-sweep/spec/GC.Spec.MinorCollect.fst`)
branches on the header tag. The cases below mirror OCaml's `caml/mlvalues.h`
constants but only the ones relevant to a single-generation, no-finalizer,
no-ephemeron core are in scope:

| Tag range  | Name                    | Scan fields? | Promotion handling                                    |
| ---------- | ----------------------- | ------------ | ----------------------------------------------------- |
| 0–246      | Structured blocks       | Yes          | Copy fields, enqueue for mop-up scan                  |
| 247        | `Closure_tag`           | Yes          | Copy fields, enqueue for mop-up scan                  |
| 248        | `Object_tag`            | Yes          | Treated like structured (in scope)                    |
| 249        | `Infix_tag`             | n/a          | **Out of scope** — spec precondition `tag <> 249`     |
| 250        | `Forward_tag`           | Yes (in OCaml) | **Out of scope** — would collide with our Blue encoding; spec precondition `tag <> 250` |
| 251        | `Abstract_tag`          | No           | Copy bytes, skip field scan                           |
| 252        | `String_tag`            | No           | Copy bytes, skip field scan                           |
| 253        | `Double_tag`            | No           | Copy bytes, skip field scan                           |
| 254        | `Double_array_tag`      | No           | Copy bytes, skip field scan; also skipped by barrier  |
| 255        | `Custom_tag`            | No           | Copy bytes, skip field scan; opaque to GC             |

The threshold `no_scan_tag = 251` is the same constant OCaml uses; in our
spec it appears as a literal branch in `oldify_one_spec`:

```fstar
if h.tag >= 251 then copy_bytes_only m g fp obj h.wosize
else if h.tag = 249 || h.tag = 250 then False_elim ()   // precondition
else copy_and_enqueue m g fp obj h.wosize h.tag
```

`Infix_tag` and `Forward_tag` are excluded by a `well_formed_minor`
precondition: no minor-heap object has `tag ∈ {249, 250}`. This is sound
in our setting because we do not yet support lazy values or closure-infix
pointers; both will be revisited if the verified core is ever extended to
those features.

## The `wosize == 0` corner case

A wosize-0 block has a header word but no fields, so there is no `field[0]`
to overwrite with a forwarding address. The chosen protocol for promoting
such an object:

1. Call `alloc_spec g fp 0` (`mark-and-sweep/spec/GC.Spec.Allocator.fst:182`)
   to obtain a fresh major slot. The allocator already bumps requested
   wosize 0 up to 1 internally (line 183: `let wz = if requested_wz = 0
   then 1 else requested_wz`), so the major slot is well-formed.
2. Overwrite the original minor header's color to `Blue`.
3. Write `0xFFFFFFFFFFFFFFFF` into the word at the original object address
   (i.e. the byte position where `field[0]` would otherwise live; this
   byte is part of the minor heap's reserved per-object footprint regardless
   of wosize).
4. Stage 3's `is_forwarded` short-circuit (`wosize >= 1`) means this
   sentinel is *not* misread as a real forwarding address. The mop-up
   pass instead uses a separate `is_forwarded_zero` check.

The sentinel is sound because `heap_size <= pow2 57` (`GC.Spec.Base`), so
`2^64 - 1` cannot match any valid `obj_addr`. A code path that misreads
the sentinel as an address fails the `obj_addr` precondition — a
verification error, not a silent miscompile.

## Tag-safety invariant

The single client-visible invariant Stage 3 must establish and Stage 4
must preserve:

> **Invariant (forwarding read).** For any minor-heap object address `obj`,
> a client may dereference `field[0]` as a forwarding pointer only after
> reading the header at `obj - mword` and confirming `color = Blue` and
> `wosize >= 1`. If `wosize == 0`, the client must instead consult the
> wosize-0 forwarding side-table built during mop-up (Stage 3 detail).

This invariant guards every mop-up scan, every remembered-set rewrite,
and every root-rewriting pass. It is local — no global rank or fuel
argument is required — so it composes cleanly with the existing
five-pillar correctness theorem.

## Where this lands in code

- `common/lib/GC.Lib.Header.fst:58-62` — `header_sem` / `color_sem`; the
  Blue-color overload is interpretation-only, no edits here.
- `mark-and-sweep/spec/GC.Spec.Allocator.fst:182` — `alloc_spec`, used as
  a black box from `oldify_one_spec` (including the `wosize == 0` case).
- `mark-and-sweep/spec/GC.Spec.MinorCollect.fst` (new, Stage 3) —
  `is_forwarded`, `read_forwarding`, tag-branching `oldify_one_spec`.
- `mark-and-sweep/impl/GC.Impl.MinorCollect.fst` (new, Stage 3) — Pulse
  realisation.

## Open questions

- **Wosize-0 side table vs. sentinel reuse.** The plan above writes
  `0xFFFFFFFFFFFFFFFF` and detects it positionally. An alternative is a
  small Pulse-verified hashtable mapping minor-side wosize-0 addresses to
  their major-side replacements. The sentinel approach is simpler; the
  side-table approach is more uniform with the `wosize >= 1` case. To be
  settled when Stage 3 starts.
- **`Object_tag = 248` treatment.** Treated as structured here. If OCaml
  runtime integration ever lands and exercises object-with-mutable-method
  semantics, this may need revisiting (e.g. method-table caching has
  historically been a source of subtle GC-interaction bugs in OCaml).
- **`Forward_tag` reintroduction.** If a future milestone wants to support
  OCaml lazy values, the cleanest re-introduction is a third minor-heap
  color (currently the 2-bit palette has White/Gray/Blue/Black; Gray is
  unused in the minor heap and could be repurposed). Out of scope here.

[rwo-gc]: https://dev.realworldocaml.org/garbage-collector.html
