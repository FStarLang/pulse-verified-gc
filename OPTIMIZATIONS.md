# Optimization Notes

Current performance focus: reduce the overhead of the OCaml integration while
keeping the extracted F*/Pulse collector as the authority for collection,
promotion, marking, sweeping, and root rewriting.

## Implemented: minor allocation fast path

`Alloc_small_aux` in the patched OCaml runtime now reserves small objects by
updating the verified minor heap's shared bump counter directly when space is
available.  If the fast path misses, `Alloc_small_aux` calls
`verified_allocate_minor()`, which initializes the heap if needed, runs minor
collection, and retries minor allocation instead of falling back to the major
heap.  Shared/large allocations continue to use `verified_allocate()` and the
verified major free list.

This removes the per-object call into extracted `gen_alloc` on the common
allocation path and writes each fast-path object header once.  Slow minor
allocations reuse the extracted header when `WITH_PROFINFO` is disabled; the
runtime still finalizes headers for profiling builds and shared/major
allocation paths.  The extracted minor allocator now writes its header with
`GC.Impl.ArrayWord.write_u64_le`, so the generated C emits one 64-bit store
instead of eight byte stores.

Full benchmark run on `nbodies.byte 100000`: the verified runtime went from the
previous ~3.76x slowdown to **2.34x** slowdown versus stock OCaml on this
machine.

## Candidate follow-up optimizations

1. Major-GC trigger accounting: replace the current conservative
   `bytes_promoted_since_major += minor_bump_before_collection` heuristic with
   actual promoted bytes or a free-capacity pressure signal.  The current
   heuristic can trigger major collections when most minor objects die young.

2. Sweep/coalesce writes: weaken the free-block representation so sweep only
   needs to initialize free-list headers and links, not zero every payload word
   in a reclaimed block.

3. Sparse forwarding-array clearing: avoid `memset` over the full forwarding
   array on every minor collection.  Track touched forwarding entries, or use an
   epoch/tag scheme so only entries reached during the current collection are
   considered live.

4. Queue clearing: avoid full gray/Cheney queue initialization when only the
   initialized prefix is semantically meaningful.

5. Root and remembered-set buffering: reduce bridge-side copying by reusing
   root buffers and gray-stack storage across full collections instead of
   allocating/freeing them each time.

6. Major free-list search: profile large-object allocation after the minor fast
   path lands; if it becomes visible, split free lists by size class or keep a
   rover pointer to avoid repeated first-fit scans.
