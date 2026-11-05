/* Minimal test harness for the verified generational GC.
 *
 * Tests: init → minor allocs → minor_collect → full_gc → reuse →
 *        an incremental collection (minor_collect + start_cycle, mark
 *        slices, sweep slices, a major allocation and a minor collection
 *        mid-sweep), and one with a 1-entry mark stack (roots overflow it,
 *        the mark slices rescan).
 *
 * Small objects go to the nursery (`minor_alloc`), major ones to the free
 * list at the collector's phase (`allocate`), as the OCaml bridge does.
 *
 * The verified code does not allocate the nursery, so we construct
 * minor_heap_t manually with heap-allocated storage.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "compat.h"
#include "GC_Gen_Impl.h"
#include "krmlinit.h"
#include "internal/GC_Gen_Impl.h"
#include "internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h"

/* Read a word from minor heap (host byte order, little-endian assumed) */
static uint64_t peek_minor(minor_heap_t mh, uint64_t offset)
    __attribute__((unused));
static uint64_t peek_minor(minor_heap_t mh, uint64_t offset) {
    return minor_read(mh, offset);
}

int main(void)
{
    zero_addr = 0;
    heap_size_u64 = 1024 * 1024;

    /* Initialize derived constants (fwd_array_size, queue_size_sz, ...) */
    krmlinit_globals();

    printf("=== Verified Generational GC Test ===\n");
    printf("minor_heap_size = %lld bytes\n", (long long)minor_heap_size_sz);
    printf("minor_heap_size_u64 = %llu\n", (unsigned long long)minor_heap_size_u64);
    printf("heap_size_u64 (major) = %llu\n", (unsigned long long)heap_size_u64);

    /* ---- Allocate major heap ---- */
    size_t major_bytes = (size_t)heap_size_u64;
    uint8_t *major_data = calloc(major_bytes, 1);
    if (!major_data) { perror("calloc major"); return 1; }
    heap_t major_heap = { .data = major_data, .size = major_bytes };

    printf("\nInitializing %zu-byte major heap ...\n", major_bytes);
    uint64_t fp = init_heap(major_heap);
    printf("init_heap returned fp = %llu\n", (unsigned long long)fp);

    /* ---- Allocate minor heap (manually) ---- */
    size_t minor_bytes = (size_t)minor_heap_size_sz;
    uint8_t *minor_data = calloc(minor_bytes, 1);
    if (!minor_data) { perror("calloc minor"); free(major_data); return 1; }
    uint64_t *bump_ref = calloc(1, sizeof(uint64_t));
    if (!bump_ref) { perror("calloc bump"); free(minor_data); free(major_data); return 1; }
    *bump_ref = 0;
    minor_heap_t minor = { .data = minor_data, .size = minor_bytes, .bump_ref = bump_ref };

    /* ---- Free-list head reference ---- */
    phase_state *phase_ref = NULL;
    uint64_t *fp_ref = calloc(1, sizeof(uint64_t));
    if (!fp_ref) { perror("calloc fp_ref"); goto cleanup; }
    *fp_ref = fp;

    /* ---- The collector's phase: Idle (stop-the-world) ---- */
    phase_ref = calloc(1, sizeof(phase_state));
    if (!phase_ref) { perror("calloc phase_ref"); goto cleanup; }
    phase_ref->ps_kind = 0;  /* Idle */

    /* ---- The persistent mark state: empty stack, flag down, positions 0 ---- */
    size_t mark_cap = major_bytes / 64;
    if (mark_cap < 256) mark_cap = 256;
    uint64_t *mark_storage = calloc(mark_cap, sizeof(uint64_t));
    size_t *mark_top = malloc(sizeof(size_t));
    bool *mark_overflow = calloc(1, sizeof(bool));
    uint64_t *mark_pos = calloc(3, sizeof(uint64_t));
    if (!mark_storage || !mark_top || !mark_overflow || !mark_pos) { perror("calloc mark"); goto cleanup; }
    *mark_top = mark_cap;
    mark_pos[1] = 1;
    gray_stack_rec mark_stack = { .storage = mark_storage, .top = mark_top, .cap = mark_cap };

    /* ---- Construct gen_heap ---- */
    gen_heap_t gh = { .minor = minor, .major = major_heap, .fp_ref = fp_ref,
                      .phase_ref = phase_ref, .mark_stack = mark_stack,
                      .mark_overflow = mark_overflow, .mark_cur = &mark_pos[0],
                      .mark_field = &mark_pos[1], .mark_rescan = &mark_pos[2] };

    /* ---- Forwarding array ---- */
    size_t fwd_entries = (size_t)minor_heap_size_sz / 8;  /* one entry per word */
    uint64_t *fwd_arr = calloc(fwd_entries, sizeof(uint64_t));
    if (!fwd_arr) { perror("calloc fwd"); goto cleanup; }
    uint64_t *queue = calloc((size_t)queue_size_sz, sizeof(uint64_t));
    if (!queue) { perror("calloc queue"); goto cleanup_fwd; }
    uint64_t empty_slots[1] = { 0 };

    /* ---- Phase 1: Minor allocations ---- */
    printf("\n--- Phase 1: Minor allocations ---\n");

    uint64_t obj1 = minor_alloc(minor, 2, 0);  /* 2-word object, tag=0 */
    printf("minor_alloc(2, tag=0) = %llu (bump=%llu)\n",
           (unsigned long long)obj1, (unsigned long long)*bump_ref);

    uint64_t obj2 = minor_alloc(minor, 3, 0);  /* 3-word object */
    printf("minor_alloc(3, tag=0) = %llu (bump=%llu)\n",
           (unsigned long long)obj2, (unsigned long long)*bump_ref);

    uint64_t obj3 = minor_alloc(minor, 1, 0);  /* 1-word object */
    printf("minor_alloc(1, tag=0) = %llu (bump=%llu)\n",
           (unsigned long long)obj3, (unsigned long long)*bump_ref);

    if (obj1 == 0 || obj2 == 0 || obj3 == 0) {
        printf("FAIL: minor allocation returned 0\n");
        goto cleanup_queue;
    }

    /* Store a pointer from obj1 to obj3 (field 1 of obj1 = obj3's address) */
    minor_write(minor, obj1, obj3);
    printf("Stored pointer obj1[0] -> obj3 = %llu\n", (unsigned long long)obj3);

    /* ---- Phase 2: Minor collection ---- */
    printf("\n--- Phase 2: Minor collect ---\n");

    /* Root array: obj1 and obj2 are roots; obj3 reachable via obj1 */
    uint64_t roots[2] = { obj1, obj2 };
    size_t nroots = 2;

    /* Zero forwarding array */
    memset(fwd_arr, 0, fwd_entries * sizeof(uint64_t));

    printf("Calling minor_collect (nroots=%zu) ...\n", nroots);
    minor_collect(gh, roots, nroots, fwd_arr, queue, empty_slots, 0);

    printf("After minor_collect:\n");
    printf("  bump = %llu (should be 0 after reset)\n", (unsigned long long)*bump_ref);
    printf("  roots[0] = %llu (was obj1=%llu, now major)\n",
           (unsigned long long)roots[0], (unsigned long long)obj1);
    printf("  roots[1] = %llu (was obj2=%llu, now major)\n",
           (unsigned long long)roots[1], (unsigned long long)obj2);

    if (*bump_ref != 0) {
        printf("FAIL: bump should be 0 after minor_collect\n");
        goto cleanup_queue;
    }

    /* ---- Phase 3: More minor allocations + full GC ---- */
    printf("\n--- Phase 3: Full GC (minor + major) ---\n");

    uint64_t obj4 = minor_alloc(minor, 2, 0);
    printf("minor_alloc(2, tag=0) = %llu\n", (unsigned long long)obj4);

    /* No roots → everything becomes garbage after full GC */
    uint64_t empty_roots[1] = { 0 };
    memset(fwd_arr, 0, fwd_entries * sizeof(uint64_t));
    if (!full_gc(gh, empty_roots, 0, fwd_arr, queue, empty_slots, 0)) {
        printf("FAIL: full_gc promotion phase failed\n");
        goto cleanup_queue;
    }
    if (phase_ref->ps_kind != 0) {
        printf("FAIL: full_gc left the collector mid-cycle\n");
        goto cleanup_queue;
    }
    printf("full_gc left fp = %llu\n", (unsigned long long)*fp_ref);

    /* ---- Phase 4: Allocate after GC ---- */
    printf("\n--- Phase 4: Post-GC allocation ---\n");

    uint64_t obj5 = minor_alloc(minor, 1, 0);
    printf("minor_alloc(1, tag=0) after GC = %llu\n", (unsigned long long)obj5);

    if (obj5 == 0) {
        printf("FAIL: allocation after GC failed\n");
        goto cleanup_queue;
    }

    /* ---- Phase 5: An incremental major collection ---- */
    printf("\n--- Phase 5: Incremental collection (start, slices) ---\n");

    /* Some garbage and a live object in the major heap, the live one rooted. */
    uint64_t live = 0;
    for (int i = 0; i < 64; i++) {
        uint64_t o = allocate(major_heap, fp_ref, phase_ref, 4, 0);
        if (o == 0) { printf("FAIL: allocate\n"); goto cleanup_queue; }
        for (int j = 0; j < 4; j++) *(uint64_t *)(major_data + o + 8 * j) = 1;  /* integers */
        if (i == 17) live = o;
    }
    uint64_t live_root[1] = { live };
    memset(fwd_arr, 0, fwd_entries * sizeof(uint64_t));
    /* A cycle starts right after a minor collection, with the nursery empty. */
    if (!minor_collect(gh, live_root, 1, fwd_arr, queue, empty_slots, 0)) {
        printf("FAIL: minor_collect promotion failed\n");
        goto cleanup_queue;
    }
    start_cycle(gh, live_root, 1);
    if (phase_ref->ps_kind != 2) {
        printf("FAIL: start_cycle did not leave the collector marking\n");
        goto cleanup_queue;
    }
    int mslices = 0;
    while (phase_ref->ps_kind == 2 && mslices < 1000) { major_slice(gh, 2); mslices++; }
    if (phase_ref->ps_kind != 1) {
        printf("FAIL: marking did not finish\n");
        goto cleanup_queue;
    }
    printf("marked in %d slices of 2 words; sweeping from cursor %llu\n", mslices,
           (unsigned long long)phase_ref->ps_cursor);

    /* A few slices, then a major allocation and a minor collection mid-sweep. */
    int slices = 0;
    bool fin = false;
    while (!fin && slices < 4) { fin = major_slice(gh, 16); slices++; }
    if (!fin) {
        uint64_t o = allocate(major_heap, fp_ref, phase_ref, 2, 0);
        if (o != 0) { *(uint64_t *)(major_data + o) = 1; *(uint64_t *)(major_data + o + 8) = 1; }
        printf("mid-sweep allocate = %llu (cursor %llu)\n",
               (unsigned long long)o, (unsigned long long)phase_ref->ps_cursor);
        uint64_t y = minor_alloc(minor, 2, 0);
        uint64_t yroots[1] = { y };
        memset(fwd_arr, 0, fwd_entries * sizeof(uint64_t));
        minor_collect(gh, yroots, 1, fwd_arr, queue, empty_slots, 0);
        if (*bump_ref != 0 || phase_ref->ps_kind != 1) {
            printf("FAIL: minor collection mid-sweep\n");
                goto cleanup_queue;
        }
    }
    while (!fin) { fin = major_slice(gh, 16); slices++; }
    printf("sweep finished after %d slices of 16 words\n", slices);
    major_slice(gh, UINT64_MAX);  /* idle already: nothing to do */
    if (phase_ref->ps_kind != 0) {
        printf("FAIL: the sweep did not finish\n");
        goto cleanup_queue;
    }
    if (allocate(major_heap, fp_ref, phase_ref, 1, 0) == 0) {
        printf("FAIL: allocation after the incremental collection failed\n");
        goto cleanup_queue;
    }

    /* ---- Phase 6: A 1-entry mark stack: the roots overflow it ---- */
    printf("\n--- Phase 6: Root darkening overflows a 1-entry mark stack ---\n");
    gh.mark_stack.cap = 1;
    *mark_top = 1;
    uint64_t a = 0, b = 0;
    for (int i = 0; i < 8; i++) {
        uint64_t o = allocate(major_heap, fp_ref, phase_ref, 2, 0);
        if (o == 0) { printf("FAIL: allocate\n"); goto cleanup_queue; }
        *(uint64_t *)(major_data + o) = 1; *(uint64_t *)(major_data + o + 8) = 1;
        if (i == 2) a = o;
        if (i == 5) b = o;
    }
    *(uint64_t *)(major_data + a) = b;   /* a -> b: b is reached only through a */
    uint64_t two_roots[2] = { a, live };
    memset(fwd_arr, 0, fwd_entries * sizeof(uint64_t));
    if (!minor_collect(gh, two_roots, 2, fwd_arr, queue, empty_slots, 0)) {
        printf("FAIL: minor_collect promotion failed\n");
        goto cleanup_queue;
    }
    start_cycle(gh, two_roots, 2);
    if (!*mark_overflow) {
        printf("FAIL: two roots in a 1-entry stack should raise the overflow flag\n");
        goto cleanup_queue;
    }
    while (!major_slice(gh, 3)) { }
    /* a, b and live survive: their headers are white (live), not blue (free) */
    uint64_t ha = *(uint64_t *)(major_data + a - 8), hb = *(uint64_t *)(major_data + b - 8);
    if (((ha >> 8) & 3) != 0 || ((hb >> 8) & 3) != 0) {
        printf("FAIL: an object reachable from the roots was freed\n");
        goto cleanup_queue;
    }
    printf("overflowed marking kept both roots' objects and their child\n");

    printf("\nAll tests passed.\n");
    free(queue);
    free(fwd_arr);
    free(phase_ref);
    free(fp_ref);
    free(bump_ref);
    free(minor_data);
    free(major_data);
    return 0;

cleanup_queue:
    free(queue);
cleanup_fwd:
    free(fwd_arr);
cleanup:
    if (phase_ref) free(phase_ref);
    if (fp_ref) free(fp_ref);
    if (bump_ref) free(bump_ref);
    free(minor_data);
    free(major_data);
    return 1;
}
