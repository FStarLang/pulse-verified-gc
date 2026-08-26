# Verified Generational GC — OCaml 4.14 Integration

Drop-in replacement for OCaml 4.14's garbage collector using a **verified
generational GC** (Cheney minor + mark-and-sweep major) extracted from F*/Pulse
to C via KaRaMeL.

## Architecture

```
OCaml 4.14 runtime (patched: memory.h, interp.c, minor_gc.c, ...)
    ↓ inline minor bump allocation; verified_allocate_minor() slow path
alloc_gen.c (bridge: root scanning, minor/major collection, heap init)
    ↓ minor_alloc(), allocate(), minor_collect_full(), gen_gc()
GC_Gen_Impl.c (KaRaMeL-extracted verified code)
```

### Three layers

1. **GC_Gen_Impl.c** — KaRaMeL-extracted verified code.  Contains both the
   generational (minor bump + Cheney BFS promotion) and mark-and-sweep (major)
   collectors.  Zero hand-written logic — all code extracted from verified
   F*/Pulse source.

2. **alloc_gen.c** — C bridge layer.  Provides the shared minor
   bump pointer used by the inline `Alloc_small` fast path,
   `verified_allocate_minor()` for the small-allocation slow path, and
   `verified_allocate()` for shared/major allocation.  Handles:
   - NULL-base trick for major heap (offsets = absolute addresses)
   - Root scanning via `caml_do_roots`
   - Minor→major address translation for roots
   - Inter-generational pointer handling via OCaml's `caml_ref_table`
   - Gray stack management for major GC

3. **runtime_gen.patch** — OCaml runtime modifications (~250 lines).  Patches
   `memory.h` (inline minor allocation plus slow-path `verified_allocate_minor`),
   `memory.c` (caml_alloc_shr), `interp.c` (Setup_for_gc), `minor_gc.c`
   (disable native GC).

## Quick start

```bash
# 1. Set up (clone OCaml, apply patches, build runtimes)
make setup

# 2. Run smoke tests
make test

# 3. Run benchmarks (requires hyperfine)
make benchmark
```

## Trust boundary

| Component | Lines | Why trusted |
|-----------|-------|-------------|
| `alloc_gen.c` | ~250 | Bridge: root scanning, address translation, heap init |
| NULL-base patches | ~20 | 6 patches to GC_Gen_Impl.c for absolute addressing |
| `runtime_gen.patch` | ~250 | OCaml runtime modifications |
| `krmlinit.c` | ~25 | Derived constant initialization |
| `compat.c` | ~5 | Missing `FStar_UInt64_ne` shim |
| `caml_ref_table` completeness | — | Same trust as stock OCaml |

Everything else is KaRaMeL-extracted from verified F*/Pulse code with zero admits.

## Configuration

Set `MIN_EXPANSION_WORDSIZE` environment variable to control major heap size
(in words).  Default: 32M words (256MB).

Minor heap size is set at runtime with `MINOR_HEAP_WORDS`.  The default is
256K words (2MB), matching OCaml's default, with a floor large enough for
`Max_young_wosize`.

## Tests

`make test` runs two groups, in this order:

1. **Correctness tests** (`make -C tests correctness`) — assertion-driven
   programs that check specific properties of the collector and exit non-zero
   on failure.
2. **Smoke tests** — the eight Computer Language Benchmarks Game programs, run
   once each to confirm the collector survives realistic workloads.

### `tests/infix_closures.ml` — interior (infix) pointers

Mutually recursive OCaml functions compile to a *single* heap block. The first
function is that block (`Closure_tag = 247`); every later one is addressed by a
pointer into the **middle** of the block, just past an extra header tagged
`Infix_tag = 249` whose size field records the distance in words back to the
start. So an ordinary OCaml program stores, in an ordinary heap field, a
pointer that is not the address of any allocated block. The collector has to
recognise it and mark the *enclosing* block.

The test makes 2128 assertions in ten groups. Groups 1-7 are about the major
heap; groups 8-10 are about the nursery, where interior pointers are hardest,
because Cheney copying has to forward the *enclosing* block and then re-apply
the offset (`caml_oldify_one`'s `offset = Infix_offset_hd(hd); ...; *p +=
offset`).

| # | What it checks |
|---|---|
| 1 | Three mutually recursive functions really do share one block, with `Infix_tag` on the 2nd and 3rd |
| 2 | Every clause of `GC.Spec.Object.infix_addr_conds` holds numerically on the live heap: `wosize >= 2`, `parent == h - wosize*8`, both addresses word-aligned, parent is `Closure_tag`, and the infix header lies strictly inside the parent's body |
| 3 | A heap field genuinely stores an interior pointer |
| 4 | The interior pointer survives promotion into the major heap; the parent offset is invariant across the move |
| 5 | A block reachable from the roots **only** through an interior pointer survives mark & sweep, along with the array captured in its environment |
| 6 | 400 groups, half dropped, all survivors held only by interior pointers — real sweep pressure |
| 7 | The post-collection heap has the same shape: identical tags, sizes, addresses, `Obj.reachable_words` counts and physical identities |
| 8 | A **major -> minor** interior pointer, reaching a group that lives in the nursery and is anchored *only* by that pointer. The edge arrives through the remembered set (`caml_modify` records the raw interior word, which is why the forwarding map is keyed on it). After one minor collection the target has moved — so it really was young — the field is still `Infix_tag`, the offset is unchanged, and all three closures still compute |
| 9 | A **minor -> minor** interior pointer: referrer and group both young, so the edge is found by Cheney scanning and both are promoted in one pass. Here the parent is observable, so `interior - parent == wosize*8` is checked as an address difference before *and* after, and sharing between two referrers is preserved |
| 10 | 200 nursery groups anchored from a major-heap array by interior pointers only, with 200 more dropped: every one is shown to have been promoted, with its offset, reachable-word count and computed values intact |

Collections are forced the way a real program forces them, by allocating;
`Gc.quick_stat` confirms they happened. (`Gc.full_major` is *not* wired to the
verified collector and will crash — the verified collector runs from the
allocation path.) `MIN_EXPANSION_WORDSIZE` is set small so that major
collections occur quickly.

The same binary is also run under stock OCaml as a differential check; both
runtimes must reach the same verdict. Compaction is disabled at startup
(`max_overhead = 1000000`) so that the address-stability assertions are
meaningful under stock OCaml too — the verified major collector is non-moving.

**Scope.** The heaps this test builds are now inside the *generational*
collector's invariant, in both generations. Interior pointers in major fields
are admitted by `GC.Gen.HeapInvariant.major_heap_shape` (`well_formed_heap` is
stated on `resolve_object dst g`, not on the raw word), and interior pointers
into the nursery are admitted by `minor_heap_shape` / `collection_heap_shape`,
whose two restrictions forbidding them were removed once Cheney forwarding was
proved to preserve interiority. The corresponding audits are
`spot/GC.SPOT.InfixMajor` (a concrete major heap with an interior pointer that
satisfies the whole precondition, is collected by the real `gen_gc`, and comes
back satisfying it again) and `spot/GC.SPOT.MinorInfix` (the nursery analogue).
See `docs/minor-infix-support-plan.md`.

**The test is sensitive.** Rebuilding the runtime with the pre-fix
`check_and_darken_bounded` — the version that darkened the raw field value
instead of resolving `infix_tag` targets to `v - wosize*8` — makes group 5 fail
immediately (the infix header is overwritten with a colour, `Obj.tag` reads 0
instead of 249) and then segfaults.
