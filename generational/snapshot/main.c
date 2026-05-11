/* Minimal test harness for the verified generational GC.
 *
 * Tests: init → minor allocs → minor_collect → major GC → reuse.
 *
 * NOTE: alloc_minor_heap() as extracted uses VLA (returns stack pointers),
 * so we construct minor_heap_t manually with heap-allocated storage.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
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
    /* Initialize derived constants (fwd_array_size, queue_size_sz, ...) */
    krmlinit_globals();

    printf("=== Verified Generational GC Test ===\n");
    printf("minor_heap_size = %lld bytes\n", (long long)minor_heap_size);
    printf("minor_heap_size_u64 = %llu\n", (unsigned long long)minor_heap_size_u64);
    printf("max_young_wosize_u64 = %llu\n", (unsigned long long)max_young_wosize_u64);
    printf("heap_size_u64 (major) = %llu\n", (unsigned long long)GC_Spec_Base_heap_size_u64);

    /* ---- Allocate major heap ---- */
    size_t major_bytes = (size_t)GC_Spec_Base_heap_size_u64;
    uint8_t *major_data = calloc(major_bytes, 1);
    if (!major_data) { perror("calloc major"); return 1; }
    heap_t major_heap = { .data = major_data, .size = major_bytes };

    printf("\nInitializing %zu-byte major heap ...\n", major_bytes);
    uint64_t fp = init_heap(major_heap);
    printf("init_heap returned fp = %llu\n", (unsigned long long)fp);

    /* ---- Allocate minor heap (manually, not via alloc_minor_heap) ---- */
    size_t minor_bytes = (size_t)minor_heap_size;
    uint8_t *minor_data = calloc(minor_bytes, 1);
    if (!minor_data) { perror("calloc minor"); free(major_data); return 1; }
    uint64_t *bump_ref = calloc(1, sizeof(uint64_t));
    if (!bump_ref) { perror("calloc bump"); free(minor_data); free(major_data); return 1; }
    *bump_ref = 0;
    minor_heap_t minor = { .data = minor_data, .size = minor_bytes, .bump_ref = bump_ref };

    /* ---- Free-list head reference ---- */
    uint64_t *fp_ref = calloc(1, sizeof(uint64_t));
    if (!fp_ref) { perror("calloc fp_ref"); goto cleanup; }
    *fp_ref = fp;

    /* ---- Construct gen_heap ---- */
    gen_heap_t gh = { .minor = minor, .major = major_heap, .fp_ref = fp_ref };

    /* ---- Forwarding array ---- */
    size_t fwd_entries = (size_t)fwd_array_size;
    uint64_t *fwd_arr = calloc(fwd_entries, sizeof(uint64_t));
    if (!fwd_arr) { perror("calloc fwd"); goto cleanup; }

    /* ---- Phase 1: Minor allocations ---- */
    printf("\n--- Phase 1: Minor allocations ---\n");

    uint64_t obj1 = gen_alloc(gh, 2, 0);  /* 2-word object, tag=0 */
    printf("gen_alloc(2, tag=0) = %llu (bump=%llu)\n",
           (unsigned long long)obj1, (unsigned long long)*bump_ref);

    uint64_t obj2 = gen_alloc(gh, 3, 0);  /* 3-word object */
    printf("gen_alloc(3, tag=0) = %llu (bump=%llu)\n",
           (unsigned long long)obj2, (unsigned long long)*bump_ref);

    uint64_t obj3 = gen_alloc(gh, 1, 0);  /* 1-word object */
    printf("gen_alloc(1, tag=0) = %llu (bump=%llu)\n",
           (unsigned long long)obj3, (unsigned long long)*bump_ref);

    if (obj1 == 0 || obj2 == 0 || obj3 == 0) {
        printf("FAIL: minor allocation returned 0\n");
        goto cleanup_fwd;
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
    minor_collect(gh, roots, nroots, fwd_arr);

    printf("After minor_collect:\n");
    printf("  bump = %llu (should be 0 after reset)\n", (unsigned long long)*bump_ref);
    printf("  roots[0] = %llu (was obj1=%llu, now major)\n",
           (unsigned long long)roots[0], (unsigned long long)obj1);
    printf("  roots[1] = %llu (was obj2=%llu, now major)\n",
           (unsigned long long)roots[1], (unsigned long long)obj2);

    if (*bump_ref != 0) {
        printf("FAIL: bump should be 0 after minor_collect\n");
        goto cleanup_fwd;
    }

    /* ---- Phase 3: More minor allocations + full GC ---- */
    printf("\n--- Phase 3: Full GC (minor + major) ---\n");

    uint64_t obj4 = gen_alloc(gh, 2, 0);
    printf("gen_alloc(2, tag=0) = %llu\n", (unsigned long long)obj4);

    /* Gray stack for major collection */
    size_t gray_cap = major_bytes / 64;
    if (gray_cap < 256) gray_cap = 256;
    uint64_t *gray_storage = calloc(gray_cap, sizeof(uint64_t));
    if (!gray_storage) { perror("calloc gray"); goto cleanup_fwd; }
    size_t gray_top = gray_cap;  /* stack grows downward; start at cap = empty */
    gray_stack_rec st = { .storage = gray_storage, .top = &gray_top, .cap = gray_cap };

    /* No roots → everything becomes garbage after full GC */
    uint64_t empty_roots[1] = { 0 };
    memset(fwd_arr, 0, fwd_entries * sizeof(uint64_t));
    uint64_t result_fp = gen_gc(gh, empty_roots, 0, fwd_arr, st);
    printf("gen_gc returned fp = %llu\n", (unsigned long long)result_fp);

    /* ---- Phase 4: Allocate after GC ---- */
    printf("\n--- Phase 4: Post-GC allocation ---\n");
    *fp_ref = result_fp;

    uint64_t obj5 = gen_alloc(gh, 1, 0);
    printf("gen_alloc(1, tag=0) after GC = %llu\n", (unsigned long long)obj5);

    if (obj5 == 0) {
        printf("FAIL: allocation after GC failed\n");
        free(gray_storage);
        goto cleanup_fwd;
    }

    printf("\nAll tests passed.\n");
    free(gray_storage);
    free(fwd_arr);
    free(fp_ref);
    free(bump_ref);
    free(minor_data);
    free(major_data);
    return 0;

cleanup_fwd:
    free(fwd_arr);
cleanup:
    if (fp_ref) free(fp_ref);
    if (bump_ref) free(bump_ref);
    free(minor_data);
    free(major_data);
    return 1;
}
