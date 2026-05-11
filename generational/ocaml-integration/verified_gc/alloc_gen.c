/* alloc_gen.c — Bridge between OCaml 4.14 runtime and the verified
 *               generational GC (Cheney minor + mark-and-sweep major).
 *
 * Provides:
 *   verified_allocate(wosize, tag)    — called from OCaml's Alloc_small / caml_alloc_shr
 *   caml_trigger_verified_gc(unit)    — OCaml-callable full GC trigger
 *
 * Uses:
 *   gen_alloc()       from GC_Gen_Impl.c — bump alloc (minor) or free-list (major)
 *   minor_collect()   from GC_Gen_Impl.c — Cheney BFS promotion
 *   collect()         from GC_Gen_Impl.c — mark-and-sweep on major heap
 *
 * NULL-base trick (major heap only):
 *   major.data = NULL so that byte offsets become absolute virtual addresses.
 *   Patches to GC_Gen_Impl.c:
 *     1. zero_addr       — non-static, set to heap_base absolute address
 *     2. is_pointer      — lower-bound check (v >= zero_addr + 8)
 *     3. update_all_objects — start at zero_addr instead of 0
 *     4. rescan_heap_impl  — start at zero_addr instead of 0
 *     5. is_valid_fp      — use zero_addr for lower bound
 *     6. darken_if_white_bounded — non-static for root darkening
 *
 * Minor heap:
 *   Uses a real data pointer (minor.data = calloc'd buffer).
 *   Minor offsets are 0-based.  The bridge translates between absolute
 *   OCaml pointers and minor offsets at allocation and collection boundaries.
 *
 * Inter-generational pointers:
 *   Uses OCaml's caml_ref_table (populated by caml_modify).  Before minor
 *   collection, the bridge translates ref_table entries from absolute minor
 *   pointers to minor offsets in-place.  After minor_collect, update_all_objects
 *   rewrites them to major addresses (absolute with NULL-base).
 */

#include "GC_Gen_Impl.h"
#include "internal/GC_Gen_Impl.h"
#include "internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#ifndef CAML_INTERNALS
#define CAML_INTERNALS
#endif
#include "../caml/misc.h"
#include "../caml/mlvalues.h"
#include "../caml/roots.h"
#include "../caml/minor_gc.h"  /* for caml_ref_table */

/* --- Patched externs from GC_Gen_Impl.c --- */
extern uint64_t zero_addr;
extern void darken_if_white_bounded(heap_t heap, gray_stack_rec st, uint64_t h_addr);

/* --- Globals --- */
static gen_heap_t   gc_gen_heap;
static uint64_t    *gc_fwd_arr;
static uint8_t     *minor_base;      /* absolute address of minor heap buffer */
static int          heap_initialized = 0;

/* Root scanning: parallel arrays for roots and writeback locations */
#define MAX_ROOTS  (1 << 18)  /* 256K root slots */
static uint64_t   root_values[MAX_ROOTS];
static value      *root_locs[MAX_ROOTS];
static size_t      root_count;

/* --- Heap initialization --- */

static void ensure_heap(void) {
    if (heap_initialized) return;
    heap_initialized = 1;

    /* --- Major heap --- */
    size_t major_words = 32 * 1024 * 1024;  /* 256 MB / 8 = 32M words */
    const char *env = getenv("MIN_EXPANSION_WORDSIZE");
    if (env) {
        size_t w = (size_t)atoll(env);
        if (w > 0) major_words = w;
    }
    size_t major_bytes = major_words * 8;

    uint8_t *major_base = (uint8_t *)calloc(1, major_bytes);
    if (!major_base)
        caml_fatal_error("verified gen GC: cannot allocate major heap");

    /* NULL-base trick: GC offsets become absolute addresses */
    zero_addr = (uint64_t)(uintptr_t)major_base;
    GC_Spec_Base_heap_size_u64 = (uint64_t)(uintptr_t)(major_base + major_bytes);

    gc_gen_heap.major.data = NULL;
    gc_gen_heap.major.size = major_bytes;

    /* Initialize major free list: one big blue block */
    uint64_t total_words_u64 = (uint64_t)major_words;
    uint64_t wosize = total_words_u64 - 1;
    uint64_t blue_hdr = (wosize << 10) | (2ULL << 8) | 0ULL;  /* blue, tag 0 */
    *(uint64_t *)major_base = blue_hdr;
    *(uint64_t *)(major_base + 8) = 0;  /* free list terminator */

    uint64_t initial_fp = zero_addr + 8;

    /* fp_ref */
    uint64_t *fp_ref = (uint64_t *)malloc(sizeof(uint64_t));
    if (!fp_ref) caml_fatal_error("verified gen GC: malloc fp_ref");
    *fp_ref = initial_fp;
    gc_gen_heap.fp_ref = fp_ref;

    /* --- Minor heap --- */
    size_t minor_sz = (size_t)minor_heap_size;
    uint8_t *minor_data = (uint8_t *)calloc(1, minor_sz);
    if (!minor_data)
        caml_fatal_error("verified gen GC: cannot allocate minor heap");
    minor_base = minor_data;

    gc_gen_heap.minor.data = minor_data;
    gc_gen_heap.minor.size = minor_sz;

    uint64_t *bump_ref = (uint64_t *)calloc(1, sizeof(uint64_t));
    if (!bump_ref) caml_fatal_error("verified gen GC: malloc bump_ref");
    gc_gen_heap.minor.bump_ref = bump_ref;

    /* --- Forwarding array --- */
    gc_fwd_arr = (uint64_t *)calloc((size_t)fwd_array_size, sizeof(uint64_t));
    if (!gc_fwd_arr)
        caml_fatal_error("verified gen GC: cannot allocate fwd array");

    caml_gc_message(0x20, "Verified gen GC: major=%luMB minor=%luKB\n",
                    (unsigned long)(major_bytes / (1024*1024)),
                    (unsigned long)(minor_sz / 1024));
}

/* --- Address translation helpers --- */

static inline int is_minor_absolute(value v) {
    return (uint64_t)(uintptr_t)v >= (uint64_t)(uintptr_t)minor_base &&
           (uint64_t)(uintptr_t)v < (uint64_t)(uintptr_t)minor_base + minor_heap_size_u64;
}

static inline uint64_t abs_to_minor_offset(value v) {
    return (uint64_t)((uintptr_t)v - (uintptr_t)minor_base);
}

static inline value minor_offset_to_abs(uint64_t off) {
    return (value)((uintptr_t)minor_base + (uintptr_t)off);
}

/* --- Root scanning callback for minor collection --- */

static void scan_minor_root(value root, value *root_ptr) {
    if (root_count >= MAX_ROOTS) return;

    /* Only collect block roots (not integers) */
    if (!Is_block(root) || Wosize_val(root) == 0) return;

    uint64_t translated;
    if (is_minor_absolute(root)) {
        /* Minor pointer: translate absolute → offset */
        translated = abs_to_minor_offset(root);
    } else {
        /* Major pointer or non-heap: pass through */
        translated = (uint64_t)(uintptr_t)root;
    }

    root_values[root_count] = translated;
    root_locs[root_count] = root_ptr;
    root_count++;
}

/* --- Minor collection --- */

static void do_minor_gc(void) {
    ensure_heap();
    caml_gc_message(0x20, "Verified gen GC: minor collection\n");
    Caml_state->_stat_minor_collections++;

    /* 1. Collect roots */
    root_count = 0;
    caml_do_roots(scan_minor_root, 1);

    /* 2. Translate inter-generational pointers (caml_ref_table entries).
     *    caml_ref_table contains (value **) entries — each points to a
     *    field in a major object that was modified by caml_modify.
     *    If the field value is a young (minor) pointer, translate from
     *    absolute to minor offset so update_all_objects can find it. */
    {
        value **r;
        for (r = caml_ref_table.base; r < caml_ref_table.ptr; r++) {
            value v = **r;
            if (Is_block(v) && is_minor_absolute(v)) {
                **r = (value)(uintptr_t)abs_to_minor_offset(v);
            }
        }
    }

    /* 3. Also add ref_table entries as roots (they are additional roots
     *    for the minor collector — major→minor pointers that must be
     *    followed during promotion). */
    {
        value **r;
        for (r = caml_ref_table.base; r < caml_ref_table.ptr; r++) {
            if (root_count >= MAX_ROOTS) break;
            value v = (value)(uintptr_t)(**r);  /* already translated above */
            uint64_t v64 = (uint64_t)(uintptr_t)v;
            /* Only add if it's a minor offset (was a young pointer) */
            if (v64 >= 8 && v64 < minor_heap_size_u64 && v64 % 8 == 0) {
                root_values[root_count] = v64;
                root_locs[root_count] = NULL;  /* no OCaml writeback for ref_table roots */
                root_count++;
            }
        }
    }

    /* 4. Zero forwarding array */
    memset(gc_fwd_arr, 0, (size_t)fwd_array_size * sizeof(uint64_t));

    /* 5. Call verified minor_collect */
    minor_collect(gc_gen_heap, root_values, (size_t)root_count, gc_fwd_arr);

    /* 6. Write back rewritten roots to OCaml locations.
     *    After minor_collect, root_values contain major addresses (absolute
     *    with NULL-base) for promoted objects, or unchanged for major roots. */
    {
        size_t i;
        for (i = 0; i < root_count; i++) {
            if (root_locs[i] != NULL) {
                uint64_t rewritten = root_values[i];
                /* After promotion, all roots are major addresses (absolute)
                 * or 0 (failed promotion).  Write back to OCaml. */
                if (rewritten != 0)
                    *root_locs[i] = (value)(uintptr_t)rewritten;
            }
        }
    }

    /* 7. Clear caml_ref_table */
    caml_ref_table.ptr = caml_ref_table.base;
}

/* --- Full GC (minor + major) --- */

static void do_full_gc(void) {
    ensure_heap();
    caml_gc_message(0x20, "Verified gen GC: full collection\n");
    Caml_state->_stat_major_collections++;

    /* Phase 1: Minor collection to promote live young objects */
    do_minor_gc();

    /* Phase 2: Major mark-and-sweep */

    /* Allocate gray stack */
    size_t gray_cap = gc_gen_heap.major.size / 64;
    if (gray_cap < 4096) gray_cap = 4096;
    uint64_t *gray_storage = (uint64_t *)calloc(gray_cap, sizeof(uint64_t));
    if (!gray_storage)
        caml_fatal_error("verified gen GC: cannot allocate gray stack");

    size_t gray_top = gray_cap;  /* stack grows downward; cap = empty */
    gray_stack_rec gc_stack;
    gc_stack.storage = gray_storage;
    gc_stack.top = &gray_top;
    gc_stack.cap = gray_cap;

    /* Scan roots again — darken live major objects into gray stack */
    root_count = 0;
    caml_do_roots(scan_minor_root, 1);
    {
        size_t i;
        for (i = 0; i < root_count; i++) {
            uint64_t root = root_values[i];
            /* After minor GC, all roots should be major addresses (absolute) */
            if (root >= zero_addr + 8 && root < GC_Spec_Base_heap_size_u64 &&
                root % 8 == 0)
            {
                uint64_t h_addr = root - 8;
                darken_if_white_bounded(gc_gen_heap.major, gc_stack, h_addr);
            }
        }
    }

    /* Run verified mark-and-sweep on major heap */
    uint64_t fp = *gc_gen_heap.fp_ref;
    uint64_t new_fp = collect(gc_gen_heap.major, gc_stack, fp);
    *gc_gen_heap.fp_ref = new_fp;

    free(gray_storage);
}

/* --- Allocation entry point --- */

void *verified_allocate(mlsize_t wosize, uint8_t tag) {
    ensure_heap();

    uint64_t result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);

    if (result == 0) {
        /* Minor heap full — collect and retry */
        do_minor_gc();
        result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);
    }

    if (result == 0) {
        /* Major heap also full — full GC and retry */
        do_full_gc();
        result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);
    }

    if (result == 0) {
        caml_fatal_error("verified gen GC: out of memory after collection");
        return NULL;  /* unreachable */
    }

    /* gen_alloc returns value address (header + 8).  Convert to header pointer.
     * For minor: result is a minor offset → translate to absolute.
     * For major: result is already absolute (NULL-base trick). */
    uint64_t hdr_addr = result - 8;
    if (result < minor_heap_size_u64) {
        /* Minor heap allocation */
        return (void *)((uintptr_t)minor_base + (uintptr_t)hdr_addr);
    } else {
        /* Major heap allocation (absolute address with NULL-base) */
        return (void *)(uintptr_t)hdr_addr;
    }
}

/* --- OCaml primitive --- */

CAMLprim value caml_trigger_verified_gc(value v) {
    (void)v;
    do_full_gc();
    return Val_unit;
}
