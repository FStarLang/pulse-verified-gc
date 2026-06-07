# Heap expansion status

## End goal

Support a general, grow-only, expandable major heap for the verified OCaml generational GC while preserving the same end-to-end correctness story as the original fixed-size major heap.

Concretely, the major heap should become a non-moving collection of active chunks in one virtual address namespace. Existing object addresses must remain stable. Expansion should acquire a fresh disjoint chunk, initialize it as blue free-list memory, link it into the global major free list, and then proceed through the verified allocation/collection path. The collector should retain the existing guarantees: live objects survive, roots are rewritten correctly, major and minor invariants are preserved, pointer/graph edges are preserved through forwarding and update, and no new untracked admits or runtime assumptions are introduced.

The intended runtime policy is preflight expansion, not mid-promotion expansion: before a Cheney minor collection, compute a conservative promotion demand, ensure the major free-list head has enough contiguous capacity, run/expand if needed, and only then start promotion. If ordinary major allocation fails, the runtime should run major GC, retry, acquire/register a fresh chunk if still short, call the verified expansion/linking path, and retry allocation.

## Current progress

The proof development has moved from planning into a substantial verified chunked-major model and chunked generational collection shell.

- **Pure chunked heap model:** `GC.Spec.MajorHeap` models active chunks, disjoint chunk ranges, chunk-local/global object enumeration, chunked reads/writes, old-read framing, add-chunk framing, and single-chunk compatibility with the original dense heap.
- **Range-owned implementation model:** `GC.Impl.MajorHeap` owns active chunk ranges with `pts_to_range`, has verified chunk-local read/write helpers, indexed chunk ownership, and single-chunk adapters to/from the legacy dense heap predicate.
- **Chunked allocator/expansion:** `GC.Spec.MajorAllocator` has fresh-chunk initialization, free-list linking, chunked first-fit allocation, expand-on-OOM specs, capacity/head-capacity preflight specs, preservation of free-list validity/termination/fit/above-zero, and verified Pulse wrappers for owned expansion/allocation.
- **Generational heap invariants:** chunked analogues now exist for allocator shape, no-blue minor-to-major fields, no-infix major-to-minor fields, no-black/no-scan/no-pointer-to-blue, chain-blue side invariants, and collection-shape preservation through expansion/preflight.
- **Chunked Cheney promotion and update:** `GC.Gen.ChunkedPromote`, `GC.Gen.ChunkedCheney`, and `GC.Gen.ChunkedUpdate` now provide chunked promotion, forwarding loops, full collection shell, major-pointer update, single-chunk compatibility, no-OOM/preflight bridges, forwarding-target shape, allocator-shape preservation, old object/header/field preservation, and exact old-field update effects.
- **Client-facing chunked correctness bundle:** `GC.Gen.CheneyCorrectness.chunked_cheney_gc_correct_after_preflight` packages optional head expansion, chunked promotion/update/root rewrite/minor reset, reachable-minor forwarding, allocator-shape preservation, forwarding-target validity, old-major survival, and old-header/field preservation.
- **Graph preservation surface:** `GC.Gen.CombinedGraph` has chunked vertex characterization, chunked classification, edge constructors/eliminators, old-major field edge introduction, expansion-safe old-view graph/reachability preservation, chunked minor-field edge introduction, and old-major post-collection edge corollaries for unchanged and forwarded fields.
- **Latest proof step:** added a bundled forward graph-morphism surface and continued discharging readiness. `GC.Gen.CheneyCorrectness` maps ready source vertices and edges into the post-collection chunked major graph via `chunked_graph_maps_to_major_graph_prop`, and exposes the above-minor-target plus non-blue-source readiness reductions. The newest edge-derived target-witness layer lives in the split `GC.Gen.CheneyGraphReadiness` module: major-target branches can derive the target witness from `CG.mem_ce` plus a heap-wide `chunked_major_objects_above_minor` predicate. `GC.SPOT.HeapExpansion` audits the one-vertex, all-vertices, one-edge, all-edges, bundled graph-morphism, above-minor-target readiness, non-blue-source readiness, and edge-derived-target readiness surfaces.

Recent validation before this status update included targeted F* checks for `GC.Gen.CombinedGraph`, `GC.Gen.CheneyCorrectness`, `GC.Gen.CheneyGraphReadiness`, and `GC.SPOT.HeapExpansion`; refreshed query-stat profiling showed the split `GC.Gen.CheneyGraphReadiness` module verifying in about 1.5 seconds overall, the earlier graph-morphism wrappers verifying in the targeted `GC.Gen.CheneyCorrectness` profile in about 1.5 seconds overall, and the chunked vertex lemmas verifying in `GC.Gen.CombinedGraph` in about 1.1 seconds overall. Full SPOT plus broad `make generational` verification passed.

## Remaining steps

1. **Package graph-morphism readiness for clients.** Continue deriving `chunked_graph_vertex_maps_to_major_ready` and `chunked_graph_edge_maps_to_major_ready` from higher-level heap/root invariants. The major-target nonrewrite side condition now has an above-minor-address bridge, major-source header witnesses now have a non-blue active-object bridge, and major-target address witnesses can be recovered from actual graph edges once `chunked_major_objects_above_minor` is available. Callers still need reachable/scannable minor-source facts and selected-live-subgraph predicates bundled, and the active-major-above-minor predicate should be connected to the authoritative heap/chunk initialization and expansion path.
2. **Strengthen toward the final end-to-end theorem.** The current graph theorem is a forward image preservation surface. The fixed-heap-style end-to-end goal still needs the remaining isomorphism/reflection pieces, especially injectivity/surjectivity over the chosen live subgraph and a client-ready statement over `MH.major_heap` and `build_chunked_combined_graph`.
3. **Port or bridge major GC/mark-sweep surfaces.** The runtime expansion policy assumes major GC can run before expansion. The chunked allocator/expansion path is far along, but full chunk-aware major mark/sweep/coalesce remains a larger remaining stage unless kept behind a single-chunk compatibility boundary.
4. **Wire implementation/runtime acquisition.** Update the extracted/Pulse-facing allocation and collection entry points so they consume the chunked major heap representation, then update `alloc_gen.c` to allocate/register chunks, check alignment/disjointness/page-table facts, and call verified expansion/preflight functions.
5. **Extraction, docs, and integration tests.** Keep extraction stable, update design/runtime docs once the proof/API shape is final, and add integration scenarios where allocation or minor collection expands the major heap instead of failing.

## Strategy for acquiring new heap chunks

The verified code should not call `malloc` directly. The C runtime bridge acquires raw memory, page-rounds it, registers it with OCaml's page table, and checks the facts required by the verified model: base alignment, size, no overflow, virtual address bounds, disjointness from active major chunks, and disjointness from the minor range.

Once those facts hold, the verified expansion path treats the memory as a fresh `heap_chunk`: initialize it as one or more blue free-list blocks, prepend/link the fresh block chain to the global major free list, prove old reads/objects/graph facts are framed, and retry allocation or start Cheney promotion with enough head capacity. If promotion would otherwise fail because of OOM, the intended architecture is that preflight has already prevented that state by expanding before promotion begins.

## Audit checklist

Audit these parts to confirm the development is still on track:

- **Chunk model soundness:** `common/spec/GC.Spec.MajorHeap.*` for chunk disjointness, lookup uniqueness, word containment, object enumeration, add-chunk framing, and single-chunk compatibility.
- **Owned heap boundary:** `common/impl/GC.Impl.MajorHeap.fst` for `pts_to_range` ownership, indexed chunk resources, read/write accessors, and adapters to/from legacy `Heap.is_heap`.
- **Expansion and allocator contracts:** `mark-and-sweep/spec/GC.Spec.MajorAllocator*` for fresh chunk initialization, free-list validity/termination/fit, expand-on-OOM, head-capacity preflight, and split-allocation preservation.
- **Generational invariant lift:** `generational/spec/GC.Gen.HeapInvariant.*` for `chunked_collection_heap_shape`, preflight preservation, no-blue/no-infix/no-scan/no-pointer-to-blue, and `chunked_chain_objects_blue`.
- **Chunked Cheney/update correctness:** `generational/spec/GC.Gen.ChunkedPromote.*`, `GC.Gen.ChunkedCheney.*`, `GC.Gen.ChunkedUpdate.*`, and `GC.Gen.CheneyPreservation.*` for no-OOM/preflight, forwarding-target shape, allocator-shape preservation, old object/header/field preservation, and exact update effects.
- **Client theorem surface:** `generational/spec/GC.Gen.CheneyCorrectness.*` for the current chunked correctness bundle and edge/reachability corollaries. This is the best place to check whether the proof states the user-facing guarantees we ultimately need.
- **Graph bridge:** `generational/spec/GC.Gen.CombinedGraph.*` for chunked classification, edge introduction, old-view graph/reachability preservation, and the shape of future graph-morphism proofs.
- **SPOT audit:** `spot/GC.SPOT.HeapExpansion.fst` should wrap each important public contract without admits, so weak interfaces or missing premises show up in a smaller client module.
- **Runtime bridge assumptions:** later, audit `generational/ocaml-integration/verified_gc/alloc_gen.c` and extraction headers for the exact trusted facts passed from C to verified expansion.

## Validation bar

Before committing each proof milestone, keep checking:

- No new `admit()` or untracked `assume` in touched active files.
- Targeted F* verification of changed modules and interfaces.
- `cd spot && make verify` after public contract changes.
- Broad `make generational` after generational spec/impl changes.
- Warning 349 stays absent or is made explicit with stable split queries.
- Extraction and runtime tests once the implementation boundary changes.
