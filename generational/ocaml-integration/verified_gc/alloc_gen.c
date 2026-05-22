/* alloc_gen.c — Bridge between OCaml 4.14 runtime and the verified
 *               generational GC (Cheney minor + mark-and-sweep major).
 *
 * Provides:
 *   verified_allocate(wosize, tag)    — called from OCaml's Alloc_small / caml_alloc_shr
 *   caml_trigger_verified_gc(unit)    — OCaml-callable full GC trigger
 *
 * Uses:
 *   gen_alloc()            from GC_Gen_Impl.c — bump alloc (minor) or free-list (major)
 *   minor_collect_full()   from GC_Gen_Impl.c — Cheney BFS + ref_table rewrite (full correctness)
 *   collect()              from GC_Gen_Impl.c — mark-and-sweep on major heap
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
 *   pointers to minor offsets in-place.  minor_collect_full rewrites those
 *   slots to major addresses (absolute with NULL-base).
 */

#include "GC_Gen_Impl.h"
#include "internal/GC_Gen_Impl.h"
#include "internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h"
#include "krmlinit.h"
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
#include "../caml/minor_gc.h"  /* for struct caml_ref_table */
#include "../caml/domain_state.h"  /* for Caml_state */
#include "../caml/address_class.h" /* for In_heap, caml_page_table_add */

/* --- Patched externs from GC_Gen_Impl.c --- */
#include "GC_Spec_ZeroAddr.h"  /* zero_addr, heap_size_u64 */
#include "profiling_counters.h"
extern size_t queue_size_sz;
extern void darken_if_white_bounded(heap_t heap, gray_stack_rec st, uint64_t h_addr);

/* --- Globals --- */
static gen_heap_t   gc_gen_heap;
static uint64_t    *gc_fwd_arr;
static uint64_t    *gc_queue;         /* BFS queue for Cheney promotion (heap-allocated) */
static uint8_t     *minor_base;      /* absolute address of minor heap buffer */
static int          heap_initialized = 0;

/* Inline fast-path globals for Alloc_small_aux (memory.h) */
uint64_t *vergc_minor_bump_ref;
uint8_t  *vergc_minor_base;
uint64_t  vergc_minor_size;

/* Root scanning: parallel arrays for roots and writeback locations */
#define MAX_ROOTS  (1 << 18)  /* 256K root slots */
static uint64_t   root_values[MAX_ROOTS];
static value      *root_locs[MAX_ROOTS];
static size_t      root_count;

/* Track total bytes promoted since last major GC.  When this approaches
 * the major heap size, we trigger a major GC to avoid promotion failures. */
static uint64_t   bytes_promoted_since_major = 0;
static int        in_full_gc = 0;  /* re-entrancy guard */

/* Fast-path tracking: when only non-pointer objects (tag >= no_scan_tag) are
 * allocated in the minor heap, the verified BFS trivially handles them
 * (objects with tag >= no_scan_tag have no pointer fields to scan). */

/* minor_base_addr is defined in the extracted GC_Gen_Base module.
 * We set it at runtime to the actual minor heap buffer address so that
 * the verified to_minor_offset_u64 can translate absolute→offset inline. */
extern uint64_t minor_base_addr;

/* --- Heap initialization --- */

static void ensure_heap(void) {
    if (heap_initialized) return;
    heap_initialized = 1;
    atexit(gc_print_profile);

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
    heap_size_u64 = (uint64_t)(uintptr_t)(major_base + major_bytes);

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
    /* Override the verified constant (2048B) with a production-sized minor heap.
     * OCaml default is 256K words = 2MB.  We match that default, overridable
     * via environment variable. */
    size_t minor_words = 256 * 1024;  /* 2 MB / 8 = 256K words (matches OCaml default) */
    const char *minor_env = getenv("MINOR_HEAP_WORDS");
    if (minor_env) {
        size_t w = (size_t)atoll(minor_env);
        if (w >= 256) minor_words = w;
    }
    size_t minor_sz = minor_words * 8;
    minor_heap_size_u64 = (uint64_t)minor_sz;
    max_young_wosize_u64 = 256ULL;  /* match OCaml's Max_young_wosize */

    /* Re-derive constants that depend on minor_heap_size */
    krmlinit_globals();
    uint8_t *minor_data = (uint8_t *)calloc(1, minor_sz);
    if (!minor_data)
        caml_fatal_error("verified gen GC: cannot allocate minor heap");
    minor_base = minor_data;

    gc_gen_heap.minor.data = minor_data;
    gc_gen_heap.minor.size = minor_sz;

    uint64_t *bump_ref = (uint64_t *)calloc(1, sizeof(uint64_t));
    if (!bump_ref) caml_fatal_error("verified gen GC: malloc bump_ref");
    gc_gen_heap.minor.bump_ref = bump_ref;

    /* Initialize inline fast-path globals for Alloc_small_aux */
    vergc_minor_bump_ref = bump_ref;
    vergc_minor_base     = minor_data;
    vergc_minor_size     = (uint64_t)minor_sz;

    /* Set minor_base_addr so the verified to_minor_offset_u64 can
     * translate absolute minor addresses to offsets inline. */
    minor_base_addr = (uint64_t)(uintptr_t)minor_data;

    /* --- Forwarding array --- */
    gc_fwd_arr = (uint64_t *)calloc((size_t)queue_size_sz, sizeof(uint64_t));
    if (!gc_fwd_arr)
        caml_fatal_error("verified gen GC: cannot allocate fwd array");

    /* --- BFS queue (heap-allocated to avoid stack overflow for large minor heaps) --- */
    gc_queue = (uint64_t *)calloc((size_t)queue_size_sz, sizeof(uint64_t));
    if (!gc_queue)
        caml_fatal_error("verified gen GC: cannot allocate BFS queue");

    /* Register our minor heap with OCaml's domain state so that
     * Is_young() recognizes minor pointers.  Without this, the write
     * barrier in caml_modify / caml_initialize never records
     * major→minor pointers in the ref_table, leaving stale minor
     * addresses in major objects after minor GC. */
    Caml_state->_young_start = (value *)minor_data;
    Caml_state->_young_end   = (value *)(minor_data + minor_sz);
    Caml_state->_young_ptr   = Caml_state->_young_end;
    Caml_state->_young_alloc_start = Caml_state->_young_start;
    Caml_state->_young_alloc_end   = Caml_state->_young_end;

    /* Register our major heap in OCaml's page table so that Is_in_heap()
     * returns true for addresses inside it.  Without this, the write
     * barrier in caml_modify / caml_initialize skips the ref_table update
     * for stores into major-heap objects, leaving inter-generational
     * pointers untracked and causing stale minor addresses after GC. */
    if (caml_page_table_add(In_heap, major_base, major_base + major_bytes) != 0)
        caml_fatal_error("verified gen GC: page table registration failed");

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
    if (!Is_block(root)) return;

    /* Validate the pointer is a real heap address, not a minor offset
     * that leaked from a previous GC cycle. Valid pointers are large
     * absolute addresses; minor offsets are small (< minor_heap_size). */
    uintptr_t r = (uintptr_t)root;
    if (r < (uintptr_t)minor_heap_size_u64) return;

    if (Wosize_val(root) == 0) return;

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

static void do_major_gc_only(void);  /* forward decl */
static void do_full_gc(void);       /* forward decl */

/* Core minor GC implementation.  If major heap space is insufficient,
 * promotion will partially fail.  The caller must handle this. */
static void do_minor_gc_core(void) {

    PROF_INC(minor_gc_count);
    PROF_START(minor_gc_total);

    /* 1. Collect roots */
    PROF_START(root_scan);
    root_count = 0;
    caml_do_roots(scan_minor_root, 1);

    /* 2. Inter-generational pointers (ref_table entries) are absolute
     * addresses.  The verified to_minor_offset_u64 handles translation
     * inline during cheney_promote_phase and update_one_object, so no
     * pre-translation is needed. */

    /* 3. Also add ref_table entries as roots */
    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        value **r;
        for (r = tbl->base; r < tbl->ptr; r++) {
            value v = (value)(uintptr_t)(**r);
            uint64_t v64 = (uint64_t)(uintptr_t)v;
            /* ref_table values are absolute addresses; translate to offset */
            if (is_minor_absolute((value)v64)) {
                uint64_t off = v64 - (uint64_t)(uintptr_t)minor_base;
                if (root_count >= MAX_ROOTS)
                    caml_fatal_error("verified gen GC: root overflow (ref_table)");
                root_values[root_count] = off;
                root_locs[root_count] = NULL;
                root_count++;
            }
        }
    }
    PROF_END(root_scan);

    /* 4. Zero forwarding array */
    PROF_START(fwd_arr_zero);
    memset(gc_fwd_arr, 0, (size_t)queue_size_sz * sizeof(uint64_t));
    PROF_END(fwd_arr_zero);

    /* 5. Minor collection via verified minor_collect_full.
     *
     * The verified minor_collect_full bundles:
     *   cheney_promote_phase (with infix-aware BFS) +
     *   update_promoted_objects +
     *   rewrite_heap_slots (ref_table entries) +
     *   rewrite_roots_impl + minor_heap_reset
     * and returns ok: bool (false = OOM).
     *
     * Full correctness: the post-collection major heap equals
     * cheney_collect_spec — both promoted objects' fields AND the
     * ref_table slots are rewritten in one verified call.
     *
     * The BFS handles infix sub-objects (tag=249) natively: when it
     * encounters an infix address, it promotes the parent closure and
     * derives the infix forwarding inline. */
    bool promote_ok;
    PROF_START(cheney);
    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        size_t n_slots = (size_t)(tbl->ptr - tbl->base);
        _Static_assert(sizeof(value *) == sizeof(uint64_t),
            "ref_table optimization requires LP64 (sizeof(value*)==8)");
        promote_ok = minor_collect_full(gc_gen_heap, root_values,
                                        (size_t)root_count, gc_fwd_arr,
                                        gc_queue,
                                        (uint64_t *)tbl->base, n_slots);
    }
    PROF_END(cheney);

    /* OOM check (verified flag from cheney_promote_phase) */
    if (!promote_ok) {
        uint64_t major_size = heap_size_u64 - zero_addr;
        fprintf(stderr,
            "verified gen GC: promotion failed — major heap full (%lu MB)\n"
            "  Some objects could not be promoted (live set exceeds heap capacity).\n"
            "  Set MIN_EXPANSION_WORDSIZE=%lu (or larger) to increase heap.\n",
            (unsigned long)(major_size / 1048576),
            (unsigned long)(major_size / 4));
        caml_fatal_error("verified gen GC: out of memory (major heap too small)");
    }

    /* 6. Write back rewritten roots to OCaml stack/globals.
     *
     * At this point all roots have been successfully rewritten to major
     * addresses by rewrite_roots_impl (we fatal-errored above if any
     * weren't).  Write the new major addresses back to the actual OCaml
     * root slots so the mutator sees promoted objects. */
    PROF_START(writeback);
    {
        uint64_t minor_limit = minor_heap_size_u64;
        size_t i;
        for (i = 0; i < root_count; i++) {
            if (root_locs[i] != NULL) {
                uint64_t rewritten = root_values[i];
                if (rewritten == 0) continue;
                /* Should never happen — we aborted above if any roots
                 * remained as minor offsets.  Defensive check. */
                if (rewritten < minor_limit) {
                    caml_fatal_error(
                        "verified gen GC: internal error — unpromoted root after check");
                }
                *root_locs[i] = (value)(uintptr_t)rewritten;
            }
        }
    }
    PROF_END(writeback);

    /* 7. Clear ref_table */
    Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;

    PROF_END(minor_gc_total);
    /* If we reach here, all promotions succeeded (we abort in 5d.1 otherwise) */
}

static void do_minor_gc(void) {
    ensure_heap();
    if (*gc_gen_heap.minor.bump_ref == 0) return;  /* nothing to collect */
    Caml_state->_stat_minor_collections++;

    /* Proactive major GC: run a full GC periodically to prevent the major
     * heap from filling up.  Without this, the heap fills with dead objects
     * and the next minor GC will abort with an OOM error.
     *
     * Trigger when cumulative promoted data exceeds 50% of major heap.
     * Using bump_before as a conservative upper bound on promoted bytes. */
    if (!in_full_gc) {
        uint64_t bump = *gc_gen_heap.minor.bump_ref;
        uint64_t major_size = heap_size_u64 - zero_addr;
        /* Use 50% threshold — balances sweep cost vs fragmentation */
        uint64_t threshold = major_size / 2;
        if (bytes_promoted_since_major + bump > threshold) {
            do_full_gc();
            if (*gc_gen_heap.minor.bump_ref == 0) return;
        }
    }

    uint64_t fp_before = *gc_gen_heap.fp_ref;
    uint64_t bump_before = *gc_gen_heap.minor.bump_ref;

    do_minor_gc_core();

    /* Track promoted bytes (approximate by the minor bump value) */
    bytes_promoted_since_major += bump_before;
}

/* --- Full GC (minor + major) --- */

static int full_gc_count = 0;

/* Run major mark-and-sweep only (no minor collection).
 * Assumes minor heap is empty (already collected). */
static void do_major_gc_only(void) {
    PROF_INC(major_gc_count);
    PROF_START(major_gc);
    Caml_state->_stat_major_collections++;
    full_gc_count++;

    /* Allocate gray stack */
    size_t gray_cap = gc_gen_heap.major.size / 64;
    if (gray_cap < 4096) gray_cap = 4096;
    uint64_t *gray_storage = (uint64_t *)calloc(gray_cap, sizeof(uint64_t));
    if (!gray_storage)
        caml_fatal_error("verified gen GC: cannot allocate gray stack");

    size_t gray_top = gray_cap;
    gray_stack_rec gc_stack;
    gc_stack.storage = gray_storage;
    gc_stack.top = &gray_top;
    gc_stack.cap = gray_cap;

    /* Scan roots — darken live major objects */
    root_count = 0;
    caml_do_roots(scan_minor_root, 1);
    {
        size_t i;
        for (i = 0; i < root_count; i++) {
            uint64_t root = root_values[i];
            if (root >= zero_addr + 8 && root < heap_size_u64 &&
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

    /* Reset promotion counter after major collection */
    bytes_promoted_since_major = 0;

    free(gray_storage);
    PROF_END(major_gc);
}

static void do_full_gc(void) {
    ensure_heap();
    in_full_gc = 1;

    /* Phase 1: Minor collection to promote live young objects */
    do_minor_gc();

    /* Phase 2: Major mark-and-sweep */
    do_major_gc_only();

    in_full_gc = 0;
}

/* --- Allocation entry point --- */

void *verified_allocate(mlsize_t wosize, uint8_t tag) {
    ensure_heap();

    /* Trigger minor GC when minor heap cannot fit this allocation. */
    {
        uint64_t bump = *gc_gen_heap.minor.bump_ref;
        uint64_t needed = ((uint64_t)wosize + 1) * 8;
        if ((uint64_t)wosize <= max_young_wosize_u64 && bump + needed > minor_heap_size_u64) {
            do_minor_gc();
        }
    }

    PROF_START(minor_alloc);
    uint64_t result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);
    PROF_END(minor_alloc);

    if (result == 0) {
        do_minor_gc();
        PROF_START(minor_alloc);
        result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);
        PROF_END(minor_alloc);
    }

    if (result == 0) {
        do_full_gc();
        PROF_START(minor_alloc);
        result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);
        PROF_END(minor_alloc);
    }

    if (result == 0) {
        caml_fatal_error("verified gen GC: out of memory after collection");
        return NULL;
    }

    /* Track if any pointer-bearing objects are in the minor heap */
    if (result < minor_heap_size_u64) {
        PROF_INC(minor_alloc_count);
    } else {
        PROF_INC(major_alloc_count);
    }

    /* gen_alloc returns the object address (first field = header + 8).
     * OCaml's Alloc_small_aux expects an HP (header pointer).
     * It writes the header at hp[0] and derives val = hp + 8.
     * For minor: result is a minor offset → translate to absolute HP.
     * For major: result is already absolute (NULL-base trick). */
    uint64_t hdr_addr = result - 8;  /* header offset/address */
    if (result < minor_heap_size_u64) {
        /* Minor heap allocation — translate offset to absolute HP */
        return (void *)((uintptr_t)minor_base + (uintptr_t)hdr_addr);
    } else {
        /* Major heap allocation (absolute address with NULL-base) */
        void *ret = (void *)(uintptr_t)hdr_addr;
        /* The verified allocate() sets tag=0; patch in the correct tag. */
        uint8_t *hdr_ptr = (uint8_t *)ret;
        hdr_ptr[0] = tag;  /* tag is in lowest byte of header */
        return ret;
    }
}

/* --- OCaml primitive --- */

CAMLprim value caml_trigger_verified_gc(value v) {
    (void)v;
    do_full_gc();
    return Val_unit;
}

/* Called by caml_minor_collection() in minor_gc.c.
 * Some C primitives (e.g., caml_make_vect for large arrays) force a minor
 * collection to promote a young value before using it without write barriers.
 * We must actually run our verified minor GC so that (a) the value gets
 * promoted to major and (b) the ref_table isn't silently cleared. */
void verified_do_minor_gc(void) {
    ensure_heap();
    if (*gc_gen_heap.minor.bump_ref > 0) {
        do_minor_gc();
    }
}
