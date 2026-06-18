/* alloc_gen.c — Bridge between OCaml 4.14 runtime and the verified
 *               generational GC (Cheney minor + mark-and-sweep major).
 *
 * Provides:
 *   verified_allocate_minor(wosize, tag) — slow path for Alloc_small
 *   verified_allocate(wosize, tag)       — major/shared allocation path
 *   caml_trigger_verified_gc(unit)    — OCaml-callable full GC trigger
 *
 * Uses:
 *   minor_alloc()          from GC_Gen_Impl.c — bump alloc in the minor heap
 *   allocate()             from GC_Gen_Impl.c — free-list allocation in the major heap
 *   minor_collect_full()   from GC_Gen_Impl.c — Cheney BFS + ref_table rewrite (full correctness)
 *   gen_gc()               from GC_Gen_Impl.c — verified minor+major full collection
 *
 * NULL-base trick (major heap only):
 *   major.data = NULL so that byte offsets become absolute virtual addresses.
 *   Patches to GC_Gen_Impl.c:
 *     1. zero_addr       — non-static, set to heap_base absolute address
 *     2. is_pointer      — lower-bound check (v >= zero_addr + 8)
 *     3. update_all_objects — start at zero_addr instead of 0
 *     4. rescan_heap_impl  — start at zero_addr instead of 0
 *     5. is_valid_fp      — use zero_addr for lower bound
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
#include <sys/mman.h>

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
#include <errno.h>
extern size_t queue_size_sz;

/* --- Globals --- */
static gen_heap_t   gc_gen_heap;
static uint64_t    *gc_fwd_arr;
static uint64_t    *gc_queue;         /* BFS queue for Cheney promotion (heap-allocated) */
static uint8_t     *minor_base;      /* absolute address of minor heap buffer */
static int          heap_initialized = 0;

/* Major chunks registered with the OCaml page table.  The runtime grows by
 * appending chunks inside one contiguous arena so the dense verified
 * allocator/collector can keep scanning zero_addr..heap_size_u64. */
#define MAX_MAJOR_CHUNKS 1024
#define DEFAULT_MAJOR_WORDS ((size_t)32 * 1024 * 1024)
#define DEFAULT_MINOR_WORDS ((size_t)256 * 1024)
#define DEFAULT_MAJOR_RESERVE_CHUNKS ((size_t)4)
typedef struct {
    uint8_t *base;
    size_t bytes;
} major_chunk_rec;

typedef struct {
    uint64_t demand_words;
    uint64_t head_wosize;
    uint64_t required_head_wosize;
    uint64_t required_chunk_words;
    uint64_t planned_expansion_words;
    uint64_t suggested_major_words;
} major_preflight_snapshot;

static major_chunk_rec major_chunks[MAX_MAJOR_CHUNKS];
static size_t major_chunk_count = 0;
static uint64_t major_bytes_total = 0;
static uint8_t *major_arena_base = NULL;
static uint64_t major_arena_reserved_bytes = 0;
static uint64_t major_arena_active_bytes = 0;

static void fatal_promotion_failed(void);

static size_t configured_words_or_default(const char *name, size_t default_words) {
    const char *env = getenv(name);
    char *end = NULL;
    unsigned long long parsed;

    if (env == NULL || *env == '\0')
        return default_words;
    if (*env < '0' || *env > '9')
        caml_fatal_error("verified gen GC: invalid %s", name);

    errno = 0;
    parsed = strtoull(env, &end, 10);
    if (errno != 0 || end == env || *end != '\0' || parsed == 0 ||
        parsed > (unsigned long long)SIZE_MAX)
        caml_fatal_error("verified gen GC: invalid %s", name);

    return (size_t)parsed;
}

static size_t configured_major_chunk_words(const char *name, size_t default_words) {
    size_t words = configured_words_or_default(name, default_words);
    if (!major_chunk_words_in_header_range((uint64_t)words)) {
        if (words < 2)
            caml_fatal_error("verified gen GC: %s must be at least 2 words", name);
        caml_fatal_error("verified gen GC: %s must be at most 2^54 words", name);
    }
    return words;
}

static size_t configured_initial_major_words(void) {
    return configured_major_chunk_words("MIN_EXPANSION_WORDSIZE", DEFAULT_MAJOR_WORDS);
}

static size_t configured_expansion_chunk_words(void) {
    return configured_major_chunk_words(
        "VERGC_MAJOR_EXPANSION_WORDSIZE",
        configured_initial_major_words());
}

static size_t add_words_or_fatal(size_t a, size_t b, const char *what) {
    if (a > SIZE_MAX - b)
        caml_fatal_error("%s", what);
    return a + b;
}

static size_t configured_major_reserve_words(size_t initial_words,
                                             size_t expansion_words) {
    const char *env = getenv("VERGC_MAJOR_MAX_WORDSIZE");
    size_t reserve_words;
    size_t i;

    if (env != NULL && *env != '\0') {
        reserve_words = configured_major_chunk_words(
            "VERGC_MAJOR_MAX_WORDSIZE", initial_words);
    } else {
        reserve_words = initial_words;
        for (i = 1; i < DEFAULT_MAJOR_RESERVE_CHUNKS; i++) {
            reserve_words = add_words_or_fatal(
                reserve_words, expansion_words,
                "verified gen GC: default major arena size overflow");
        }
    }

    if (reserve_words < initial_words)
        caml_fatal_error(
            "verified gen GC: VERGC_MAJOR_MAX_WORDSIZE smaller than initial heap");
    return reserve_words;
}

static size_t words_to_bytes_or_fatal(size_t words, const char *what) {
    if (!major_chunk_words_fit_bytes((uint64_t)words))
        caml_fatal_error("%s", what);
    return (size_t)major_chunk_words_to_bytes((uint64_t)words);
}

static uint8_t *allocate_major_arena_memory(size_t bytes) {
    int flags = MAP_PRIVATE | MAP_ANONYMOUS;
    void *base;

#ifdef MAP_NORESERVE
    flags |= MAP_NORESERVE;
#endif

    base = mmap(NULL, bytes, PROT_READ | PROT_WRITE, flags, -1, 0);
    if (base == MAP_FAILED)
        caml_fatal_error("verified gen GC: cannot reserve major heap arena");
    return base;
}

static int ranges_overlap(uintptr_t start, uintptr_t end,
                          uintptr_t other_start, uintptr_t other_end) {
    return major_ranges_overlap((uint64_t)start, (uint64_t)end,
                                (uint64_t)other_start, (uint64_t)other_end);
}

static uintptr_t range_end_or_fatal(uintptr_t start, size_t bytes, const char *what) {
    if (!major_bytes_can_add((uint64_t)start, (uint64_t)bytes))
        caml_fatal_error("%s", what);
    return start + bytes;
}

static void check_major_chunk_facts(uint8_t *base, size_t bytes) {
    uintptr_t start = (uintptr_t)base;
    uintptr_t end;
    size_t i;

    if (base == NULL)
        caml_fatal_error("verified gen GC: null major chunk");
    if (bytes == 0 || !major_word_aligned((uint64_t)bytes))
        caml_fatal_error("verified gen GC: invalid major chunk size");
    if (!major_word_aligned((uint64_t)start))
        caml_fatal_error("verified gen GC: unaligned major chunk base");
    end = range_end_or_fatal(
        start, bytes, "verified gen GC: major chunk address overflow");

    if (minor_base != NULL && minor_heap_size_u64 != 0) {
        uintptr_t minor_start = (uintptr_t)minor_base;
        size_t minor_size = (size_t)minor_heap_size_u64;
        uintptr_t minor_end;
        if ((uint64_t)minor_size != minor_heap_size_u64)
            caml_fatal_error("verified gen GC: minor heap address overflow");
        minor_end = range_end_or_fatal(
            minor_start, minor_size, "verified gen GC: minor heap address overflow");
        if (ranges_overlap(start, end, minor_start, minor_end))
            caml_fatal_error("verified gen GC: major chunk overlaps minor heap");
    }

    for (i = 0; i < major_chunk_count; i++) {
        uintptr_t old_start = (uintptr_t)major_chunks[i].base;
        uintptr_t old_end = range_end_or_fatal(
            old_start, major_chunks[i].bytes,
            "verified gen GC: registered major chunk address overflow");
        if (ranges_overlap(start, end, old_start, old_end))
            caml_fatal_error("verified gen GC: overlapping major chunks");
    }
}

static void register_major_chunk(uint8_t *base, size_t bytes) {
    uint8_t *end;
    check_major_chunk_facts(base, bytes);
    if (major_chunk_count >= MAX_MAJOR_CHUNKS)
        caml_fatal_error("verified gen GC: too many major chunks");
    if (!major_bytes_can_add(major_bytes_total, (uint64_t)bytes))
        caml_fatal_error("verified gen GC: major heap size overflow");
    end = (uint8_t *)(uintptr_t)range_end_or_fatal(
        (uintptr_t)base, bytes, "verified gen GC: major chunk address overflow");
    if (caml_page_table_add(In_heap, base, end) != 0)
        caml_fatal_error("verified gen GC: page table registration failed");
    major_chunks[major_chunk_count].base = base;
    major_chunks[major_chunk_count].bytes = bytes;
    major_chunk_count++;
    major_bytes_total += (uint64_t)bytes;
}

static uint64_t current_major_bytes(void) {
    return major_bytes_total;
}

static uint64_t current_major_words(void) {
    return major_bytes_to_words(current_major_bytes());
}

static uintptr_t minor_addr_at_offset_or_fatal(uint64_t off, const char *what) {
    size_t off_sz = (size_t)off;
    if ((uint64_t)off_sz != off)
        caml_fatal_error("%s", what);
    return range_end_or_fatal((uintptr_t)minor_base, off_sz, what);
}

static uint64_t object_header_addr_or_fatal(uint64_t object_addr, const char *what) {
    uint64_t word_bytes = (uint64_t)sizeof(value);
    if (object_addr < word_bytes)
        caml_fatal_error("%s", what);
    return major_address_offset(word_bytes, object_addr);
}

static void refresh_verified_major_bounds(uint64_t active_end) {
    heap_size_u64 = active_end;
    gc_gen_heap.major.size = (size_t)major_arena_active_bytes;
    krmlinit_globals();
}

static inline uint64_t header_wosize(uint64_t header) {
    return major_header_wosize(header);
}

/* Runtime mirror of the verified minor_promotion_demand shape: sum the
 * header-inclusive size of every currently allocated minor object. */
static uint64_t minor_promotion_demand_words(void) {
    uint64_t off = 0;
    uint64_t bump = *gc_gen_heap.minor.bump_ref;
    uint64_t demand = 0;

    if (bump > minor_heap_size_u64 || !major_word_aligned(bump))
        caml_fatal_error("verified gen GC: invalid minor allocation frontier");

    while (off < bump) {
        uint64_t header =
            *(uint64_t *)minor_addr_at_offset_or_fatal(
                off, "verified gen GC: minor object address overflow");
        uint64_t wosize = header_wosize(header);
        uint64_t object_words;
        uint64_t object_bytes;

        if (!major_words_can_add(wosize, 1ULL))
            caml_fatal_error("verified gen GC: minor object size overflow");
        object_words = object_words_for_wosize(wosize);
        if (!major_chunk_words_fit_bytes(object_words))
            caml_fatal_error("verified gen GC: minor object byte overflow");
        object_bytes = major_chunk_words_to_bytes(object_words);
        if (object_bytes == 0 ||
            !major_arena_has_available_bytes(off, bump, object_bytes))
            caml_fatal_error("verified gen GC: malformed minor object layout");
        if (!major_words_can_add(demand, object_words))
            caml_fatal_error("verified gen GC: promotion demand overflow");

        demand += object_words;
        off += object_bytes;
    }

    if (off != bump)
        caml_fatal_error("verified gen GC: malformed minor allocation frontier");
    return demand;
}

static uint64_t major_free_head_wosize(void) {
    uint64_t fp = *gc_gen_heap.fp_ref;
    uintptr_t header_addr;

    if (fp == 0)
        return 0;
    if (!major_address_has_word_room(zero_addr))
        caml_fatal_error("verified gen GC: invalid major base address");
    if (!major_free_head_in_range(zero_addr, heap_size_u64, fp))
        caml_fatal_error("verified gen GC: invalid major free-list head");
    if (!major_word_aligned(fp))
        caml_fatal_error("verified gen GC: unaligned major free-list head");

    header_addr = (uintptr_t)major_free_head_header_addr(fp);
    return header_wosize(*(uint64_t *)header_addr);
}

static uint64_t required_head_wosize_for_promotion(uint64_t demand_words) {
    if (!major_words_can_add(demand_words, 1ULL))
        caml_fatal_error("verified gen GC: promotion demand too large");
    return major_preflight_required_head_wosize(demand_words);
}

static uint64_t required_chunk_words_for_head(uint64_t head_wosize) {
    if (!major_words_can_add(head_wosize, 1ULL))
        caml_fatal_error("verified gen GC: promotion head demand too large");
    return major_preflight_required_chunk_words(head_wosize);
}

static uint64_t suggested_major_words_for_retry(uint64_t required_chunk_words) {
    uint64_t current_words = current_major_words();
    return major_preflight_suggested_major_words(
        current_words, required_chunk_words);
}

static uint64_t planned_expansion_chunk_words(uint64_t required_chunk_words) {
    uint64_t configured_words = (uint64_t)configured_expansion_chunk_words();
    return major_preflight_planned_chunk_words(configured_words, required_chunk_words);
}

static major_preflight_snapshot current_major_preflight_snapshot(void) {
    major_preflight_snapshot snapshot;
    snapshot.demand_words = minor_promotion_demand_words();
    snapshot.head_wosize = major_free_head_wosize();
    snapshot.required_head_wosize =
        required_head_wosize_for_promotion(snapshot.demand_words);
    snapshot.required_chunk_words =
        required_chunk_words_for_head(snapshot.required_head_wosize);
    snapshot.planned_expansion_words =
        planned_expansion_chunk_words(snapshot.required_chunk_words);
    snapshot.suggested_major_words =
        suggested_major_words_for_retry(snapshot.required_chunk_words);
    return snapshot;
}

static int snapshot_head_ready(const major_preflight_snapshot *snapshot) {
    return major_preflight_head_ready(
        snapshot->head_wosize, snapshot->required_head_wosize);
}

static uint64_t format_major_chunk(uint8_t *base, size_t words, uint64_t next_fp) {
    uint64_t base_addr = (uint64_t)(uintptr_t)base;
    uint64_t total_words_u64 = (uint64_t)words;
    uint64_t wosize = major_chunk_words_to_wosize(total_words_u64);
    uint64_t fp_out;

    if (!major_address_has_word_room(base_addr))
        caml_fatal_error("verified gen GC: invalid major chunk base address");
    fp_out = major_chunk_initial_fp(base_addr);
    return init_major_chunk_raw(gc_gen_heap.major, base_addr, fp_out, wosize, next_fp);
}

static void expand_major_heap_words(uint64_t requested_words, const char *reason) {
    size_t words;
    size_t bytes;
    uint8_t *base;
    uintptr_t start;
    uintptr_t end;
    uint64_t old_fp;
    uint64_t new_fp;

    if (requested_words > (uint64_t)SIZE_MAX)
        caml_fatal_error("verified gen GC: expansion chunk too large");
    words = (size_t)requested_words;
    if (!major_chunk_words_in_header_range((uint64_t)words))
        caml_fatal_error("verified gen GC: expansion chunk outside verified range");
    bytes = words_to_bytes_or_fatal(
        words, "verified gen GC: expansion chunk byte size overflow");

    if (major_arena_base == NULL ||
        !major_arena_has_available_bytes(major_arena_active_bytes,
                                         major_arena_reserved_bytes,
                                         (uint64_t)bytes)) {
        fprintf(stderr,
            "verified gen GC: cannot expand major heap for %s; "
            "active=%llu words reserve=%llu words requested=%llu words\n",
            reason,
            (unsigned long long)major_bytes_to_words(major_arena_active_bytes),
            (unsigned long long)major_bytes_to_words(major_arena_reserved_bytes),
            (unsigned long long)requested_words);
        caml_fatal_error(
            "verified gen GC: major heap arena exhausted; increase VERGC_MAJOR_MAX_WORDSIZE");
    }

    base = major_arena_base + major_arena_active_bytes;
    start = (uintptr_t)base;
    end = range_end_or_fatal(
        start, bytes, "verified gen GC: major heap expansion address overflow");
    if (!major_heap_end_below_verified_limit((uint64_t)end))
        caml_fatal_error("verified gen GC: major heap expansion address overflow");

    old_fp = *gc_gen_heap.fp_ref;
    major_arena_active_bytes += (uint64_t)bytes;
    refresh_verified_major_bounds((uint64_t)end);
    new_fp = format_major_chunk(base, words, old_fp);
    register_major_chunk(base, bytes);
    *gc_gen_heap.fp_ref = new_fp;

    caml_gc_message(0x20,
        "Verified gen GC: expanded major heap by %luMB for %s (%lu chunk(s), %llu words total)\n",
        (unsigned long)(bytes / (1024 * 1024)),
        reason,
        (unsigned long)major_chunk_count,
        (unsigned long long)current_major_words());
}

static void ensure_major_head_for_minor_promotion(void) {
    major_preflight_snapshot snapshot = current_major_preflight_snapshot();
    if (snapshot_head_ready(&snapshot))
        return;

    expand_major_heap_words(
        snapshot.planned_expansion_words, "minor promotion preflight");

    snapshot = current_major_preflight_snapshot();
    if (!snapshot_head_ready(&snapshot))
        fatal_promotion_failed();
}

static void expand_major_heap_for_allocation(uint64_t requested_wosize) {
    uint64_t normalized_wosize =
        major_allocation_demand_wosize(requested_wosize);
    uint64_t required_words;
    uint64_t planned_words;

    if (!major_words_can_add(normalized_wosize, 1ULL))
        caml_fatal_error("verified gen GC: major allocation request too large");
    required_words = major_preflight_required_chunk_words(normalized_wosize);
    planned_words = planned_expansion_chunk_words(required_words);
    expand_major_heap_words(planned_words, "major allocation retry");
}

/* Inline minor-allocation fast-path state for Alloc_small_aux (memory.h).
 * The fast path reserves bytes by updating the same verified bump counter;
 * collections and heap initialization still go through verified_allocate_minor(). */
uint64_t *vergc_minor_bump_ref;
uint8_t  *vergc_minor_base;
uint64_t  vergc_minor_size;

uintnat vergc_minor_words_current(void) {
    if (!heap_initialized || gc_gen_heap.minor.bump_ref == NULL) return 0;
    return (uintnat)major_bytes_to_words(*gc_gen_heap.minor.bump_ref);
}

uintnat vergc_major_words_current(void) {
    if (!heap_initialized) return 0;
    return (uintnat)current_major_words();
}

uintnat vergc_major_top_words_current(void) {
    return vergc_major_words_current();
}

uintnat vergc_major_chunks_current(void) {
    if (!heap_initialized) return 0;
    return (uintnat)major_chunk_count;
}

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
    size_t major_words = configured_initial_major_words();
    size_t expansion_words = configured_expansion_chunk_words();
    size_t reserve_words =
        configured_major_reserve_words(major_words, expansion_words);
    size_t major_bytes = words_to_bytes_or_fatal(
        major_words, "verified gen GC: major heap word size overflow");
    size_t reserve_bytes = words_to_bytes_or_fatal(
        reserve_words, "verified gen GC: major heap reserve size overflow");

    uint8_t *major_base = allocate_major_arena_memory(reserve_bytes);
    uintptr_t major_start = (uintptr_t)major_base;
    uintptr_t initial_end = range_end_or_fatal(
        major_start, major_bytes, "verified gen GC: major heap arena address overflow");
    uintptr_t reserve_end = range_end_or_fatal(
        major_start, reserve_bytes, "verified gen GC: major heap arena address overflow");
    if (!major_heap_end_below_verified_limit((uint64_t)reserve_end))
        caml_fatal_error("verified gen GC: major heap arena address overflow");

    major_arena_base = major_base;
    major_arena_reserved_bytes = (uint64_t)reserve_bytes;
    major_arena_active_bytes = (uint64_t)major_bytes;

    /* NULL-base trick: GC offsets become absolute addresses */
    zero_addr = (uint64_t)major_start;
    heap_size_u64 = (uint64_t)initial_end;

    gc_gen_heap.major.data = NULL;
    gc_gen_heap.major.size = major_bytes;

    /* Initialize major free list through the verified raw chunk formatter. */
    uint64_t initial_fp = format_major_chunk(major_base, major_words, 0);

    /* fp_ref */
    uint64_t *fp_ref = (uint64_t *)malloc(sizeof(uint64_t));
    if (!fp_ref) caml_fatal_error("verified gen GC: malloc fp_ref");
    *fp_ref = initial_fp;
    gc_gen_heap.fp_ref = fp_ref;

    /* --- Minor heap --- */
    /* Override the verified constant (2048B) with a production-sized minor heap.
     * OCaml default is 256K words = 2MB.  We match that default, overridable
     * via environment variable. */
    max_young_wosize_u64 = 256ULL;  /* match OCaml's Max_young_wosize */
    size_t minor_words =
        configured_words_or_default("MINOR_HEAP_WORDS", DEFAULT_MINOR_WORDS);
    uint64_t min_minor_words = object_words_for_wosize(max_young_wosize_u64);
    if (minor_words < (size_t)min_minor_words)
        minor_words = (size_t)min_minor_words;
    size_t minor_sz = words_to_bytes_or_fatal(
        minor_words, "verified gen GC: minor heap word size overflow");
    minor_heap_size_u64 = (uint64_t)minor_sz;

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

    /* Register our major heap chunk in OCaml's page table so that Is_in_heap()
     * returns true for addresses inside it.  Without this, the write
     * barrier in caml_modify / caml_initialize skips the ref_table update
     * for stores into major-heap objects, leaving inter-generational
     * pointers untracked and causing stale minor addresses after GC. */
    register_major_chunk(major_base, major_bytes);

    caml_gc_message(0x20,
                    "Verified gen GC: major=%luMB reserve=%luMB in %lu chunk(s) minor=%luKB\n",
                    (unsigned long)(major_bytes / (1024*1024)),
                    (unsigned long)(reserve_bytes / (1024*1024)),
                    (unsigned long)major_chunk_count,
                    (unsigned long)(minor_sz / 1024));
}

/* --- Address translation helpers --- */

static inline int is_minor_absolute(value v) {
    return major_address_in_range(
        (uint64_t)(uintptr_t)minor_base,
        minor_heap_size_u64,
        (uint64_t)(uintptr_t)v);
}

static inline uint64_t abs_to_minor_offset(value v) {
    return major_address_offset(
        (uint64_t)(uintptr_t)minor_base,
        (uint64_t)(uintptr_t)v);
}

static inline value minor_offset_to_abs(uint64_t off) {
    return (value)minor_addr_at_offset_or_fatal(
        off, "verified gen GC: minor offset address overflow");
}

/* --- Root scanning callback for minor collection --- */

static void scan_minor_root(value root, value *root_ptr) {
    if (root_count >= MAX_ROOTS)
        caml_fatal_error("verified gen GC: root overflow");

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

static void collect_minor_roots_and_refs(void) {
    root_count = 0;
    caml_do_roots(scan_minor_root, 1);

    /* Inter-generational pointers (ref_table entries) are absolute
     * addresses.  The verified to_minor_offset_u64 handles translation
     * inline during cheney_promote_phase and update_one_object, so no
     * pre-translation is needed.
     *
     * Also add ref_table entries as minor-collection roots. */
    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        value **r;
        for (r = tbl->base; r < tbl->ptr; r++) {
            value v = (value)(uintptr_t)(**r);
            uint64_t v64 = (uint64_t)(uintptr_t)v;
            if (is_minor_absolute((value)v64)) {
                uint64_t off = major_address_offset(
                    (uint64_t)(uintptr_t)minor_base,
                    v64);
                if (root_count >= MAX_ROOTS)
                    caml_fatal_error("verified gen GC: root overflow (ref_table)");
                root_values[root_count] = off;
                root_locs[root_count] = NULL;
                root_count++;
            }
        }
    }
}

static void fatal_promotion_failed(void) {
    uint64_t major_size = current_major_bytes();
    major_preflight_snapshot snapshot = current_major_preflight_snapshot();
    fprintf(stderr,
        "verified gen GC: promotion failed — major heap full (%lu MB, %lu chunk(s))\n"
        "  Minor promotion demand: %llu words; major free-list head: %llu words.\n"
        "  Verified preflight requires head >= %llu words; fresh chunk >= %llu words.\n"
        "  Expansion chunk policy requested >= %llu words.\n"
        "  Current head satisfies preflight: %s.\n"
        "  Some objects could not be promoted (live set exceeds heap capacity).\n"
        "  Increase VERGC_MAJOR_MAX_WORDSIZE beyond %llu words to allow more growth.\n",
        (unsigned long)(major_size / 1048576),
        (unsigned long)major_chunk_count,
        (unsigned long long)snapshot.demand_words,
        (unsigned long long)snapshot.head_wosize,
        (unsigned long long)snapshot.required_head_wosize,
        (unsigned long long)snapshot.required_chunk_words,
        (unsigned long long)snapshot.planned_expansion_words,
        snapshot_head_ready(&snapshot) ? "yes" : "no",
        (unsigned long long)snapshot.suggested_major_words);
    caml_fatal_error("verified gen GC: out of memory (major heap too small)");
}

static void write_back_rewritten_roots(const uint64_t *rewritten_roots) {
    uint64_t minor_limit = minor_heap_size_u64;
    size_t i;
    for (i = 0; i < root_count; i++) {
        if (root_locs[i] != NULL) {
            uint64_t rewritten = rewritten_roots[i];
            if (rewritten == 0) continue;
            if (rewritten < minor_limit) {
                caml_fatal_error(
                    "verified gen GC: internal error — unpromoted root after check");
            }
            *root_locs[i] = (value)(uintptr_t)rewritten;
        }
    }
}

static uint64_t rewrite_root_from_forwarding(uint64_t root) {
    if (root >= 8 && root < minor_heap_size_u64 && root % 8 == 0) {
        size_t idx = (size_t)(root / 8);
        uint64_t rewritten = gc_fwd_arr[idx];
        if (rewritten == 0 || rewritten < minor_heap_size_u64) {
            caml_fatal_error(
                "verified gen GC: internal error — unpromoted root after gen_gc");
        }
        return rewritten;
    }
    return root;
}

static void write_back_forwarded_roots(void) {
    size_t i;
    for (i = 0; i < root_count; i++) {
        if (root_locs[i] != NULL) {
            uint64_t rewritten = rewrite_root_from_forwarding(root_values[i]);
            if (rewritten != 0)
                *root_locs[i] = (value)(uintptr_t)rewritten;
        }
    }
}

/* --- Minor collection --- */

static void do_full_gc(void);       /* forward decl */

/* Core minor GC implementation.  If major heap space is insufficient,
 * promotion will partially fail.  The caller must handle this. */
static void do_minor_gc_core(void) {

    PROF_INC(minor_gc_count);
    PROF_START(minor_gc_total);

    /* 1. Collect roots */
    PROF_START(root_scan);
    collect_minor_roots_and_refs();
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
        fatal_promotion_failed();
    }

    /* 6. Write back rewritten roots to OCaml stack/globals.
     *
     * At this point all roots have been successfully rewritten to major
     * addresses by rewrite_roots_impl (we fatal-errored above if any
     * weren't).  Write the new major addresses back to the actual OCaml
     * root slots so the mutator sees promoted objects. */
    PROF_START(writeback);
    write_back_rewritten_roots(root_values);
    PROF_END(writeback);

    /* 7. Clear ref_table */
    Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;

    PROF_END(minor_gc_total);
    /* If we reach here, all promotions succeeded (we abort in 5d.1 otherwise) */
}

static void do_minor_gc(void) {
    ensure_heap();
    if (*gc_gen_heap.minor.bump_ref == 0) return;  /* nothing to collect */
    ensure_major_head_for_minor_promotion();

    /* Proactive major GC: run a full GC periodically to prevent the major
     * heap from filling up.  Without this, the heap fills with dead objects
     * and the next minor GC will abort with an OOM error.
     *
     * Trigger when cumulative promoted data exceeds 50% of major heap.
     * Using bump_before as a conservative upper bound on promoted bytes. */
    if (!in_full_gc) {
        uint64_t bump = *gc_gen_heap.minor.bump_ref;
        uint64_t major_size = current_major_bytes();
        /* Use 50% threshold — balances sweep cost vs fragmentation */
        uint64_t threshold = major_size / 2;
        if (bytes_promoted_since_major + bump > threshold) {
            do_full_gc();
            if (*gc_gen_heap.minor.bump_ref == 0) return;
        }
    }

    uint64_t fp_before = *gc_gen_heap.fp_ref;
    uint64_t bump_before = *gc_gen_heap.minor.bump_ref;
    Caml_state->_stat_minor_collections++;
    Caml_state->_stat_minor_words += (double)major_bytes_to_words(bump_before);

    do_minor_gc_core();

    /* Track promoted bytes (approximate by the minor bump value) */
    bytes_promoted_since_major += bump_before;
}

/* --- Full GC (minor + major) --- */

static int full_gc_count = 0;

static void do_full_gc(void) {
    ensure_heap();
    in_full_gc = 1;
    if (*gc_gen_heap.minor.bump_ref != 0)
        ensure_major_head_for_minor_promotion();

    PROF_INC(major_gc_count);
    PROF_START(major_gc);
    Caml_state->_stat_major_collections++;
    full_gc_count++;

    if (*gc_gen_heap.minor.bump_ref != 0) {
        PROF_INC(minor_gc_count);
        Caml_state->_stat_minor_collections++;
        Caml_state->_stat_minor_words +=
            (double)major_bytes_to_words(*gc_gen_heap.minor.bump_ref);
    }

    /* Build the minor-collection root set: OCaml roots plus remembered slots. */
    PROF_START(root_scan);
    collect_minor_roots_and_refs();
    PROF_END(root_scan);

    PROF_START(fwd_arr_zero);
    memset(gc_fwd_arr, 0, (size_t)queue_size_sz * sizeof(uint64_t));
    PROF_END(fwd_arr_zero);

    /* gen_gc now prepares the major mark stack itself: minor_collect_full
     * rewrites this roots array in place, then gen_gc darkens those post-minor
     * roots and pushes them onto an initially empty gray stack before running
     * mark-and-sweep.  Keep roots separate from the stack storage so the C
     * bridge matches the verified separation-logic model. */
    size_t gray_cap = gc_gen_heap.major.size / 64;
    if (gray_cap < 4096) gray_cap = 4096;
    if (gray_cap < root_count) gray_cap = root_count;
    if (gray_cap == 0) gray_cap = 1;

    uint64_t *gray_storage = (uint64_t *)calloc(gray_cap, sizeof(uint64_t));
    if (!gray_storage)
        caml_fatal_error("verified gen GC: cannot allocate gray stack");

    uint64_t *roots_for_gc =
        (uint64_t *)calloc(root_count == 0 ? 1 : root_count, sizeof(uint64_t));
    if (!roots_for_gc) {
        free(gray_storage);
        caml_fatal_error("verified gen GC: cannot allocate root buffer");
    }
    if (root_count > 0)
        memcpy(roots_for_gc, root_values, root_count * sizeof(uint64_t));

    size_t gray_top = gray_cap;

    gray_stack_rec gc_stack;
    gc_stack.storage = gray_storage;
    gc_stack.top = &gray_top;
    gc_stack.cap = gray_cap;

    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        size_t n_slots = (size_t)(tbl->ptr - tbl->base);
        _Static_assert(sizeof(value *) == sizeof(uint64_t),
            "ref_table optimization requires LP64 (sizeof(value*)==8)");
        K___uint64_t_bool result =
            gen_gc(gc_gen_heap, roots_for_gc, (size_t)root_count, gc_fwd_arr,
                   gc_queue, (uint64_t *)tbl->base, n_slots, gc_stack);
        if (!result.snd) {
            free(roots_for_gc);
            free(gray_storage);
            in_full_gc = 0;
            fatal_promotion_failed();
        }
    }

    PROF_START(writeback);
    write_back_forwarded_roots();
    PROF_END(writeback);

    Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
    bytes_promoted_since_major = 0;

    free(roots_for_gc);
    free(gray_storage);
    PROF_END(major_gc);

    in_full_gc = 0;
}

/* --- Allocation entry points --- */

void *verified_allocate_minor(mlsize_t wosize, uint8_t tag) {
    ensure_heap();

    if ((uint64_t)wosize == 0 || (uint64_t)wosize > max_young_wosize_u64)
        caml_fatal_error("verified gen GC: non-minor allocation on minor path");

    uint64_t object_words = object_words_for_wosize((uint64_t)wosize);
    if (!major_chunk_words_fit_bytes(object_words))
        caml_fatal_error("verified gen GC: minor object byte overflow");
    uint64_t needed = major_chunk_words_to_bytes(object_words);
    if (needed > minor_heap_size_u64)
        caml_fatal_error("verified gen GC: minor heap smaller than Max_young_wosize");

    if (!major_arena_has_available_bytes(
            *gc_gen_heap.minor.bump_ref, minor_heap_size_u64, needed)) {
        do_minor_gc();
    }

    if (!major_arena_has_available_bytes(
            *gc_gen_heap.minor.bump_ref, minor_heap_size_u64, needed)) {
        caml_fatal_error("verified gen GC: minor allocation failed after collection");
        return NULL;
    }

    PROF_START(minor_alloc);
    uint64_t result = minor_alloc(gc_gen_heap.minor, (uint64_t)wosize, (uint64_t)tag);
    PROF_END(minor_alloc);

    if (result == 0) {
        caml_fatal_error("verified gen GC: minor allocation unexpectedly returned OOM");
        return NULL;
    }

    PROF_INC(minor_alloc_count);

    /* minor_alloc returns the object offset (first field = header + 8).
     * OCaml's allocation paths expect an HP (header pointer).  Slow minor
     * allocations can reuse the verified header when profiling bits are absent;
     * fast/raw allocations get a final runtime header. */
    uint64_t hdr_addr = object_header_addr_or_fatal(
        result, "verified gen GC: minor allocation header address underflow");
    return (void *)minor_addr_at_offset_or_fatal(
        hdr_addr, "verified gen GC: minor allocation address overflow");
}

void *verified_allocate(mlsize_t wosize, uint8_t tag) {
    (void)tag;
    ensure_heap();

    PROF_START(major_alloc);
    uint64_t fp = *gc_gen_heap.fp_ref;
    K___uint64_t_uint64_t res = allocate(gc_gen_heap.major, fp, (uint64_t)wosize);
    *gc_gen_heap.fp_ref = res.fst;
    uint64_t result = res.snd;
    PROF_END(major_alloc);

    if (result == 0) {
        do_full_gc();
        PROF_START(major_alloc);
        fp = *gc_gen_heap.fp_ref;
        res = allocate(gc_gen_heap.major, fp, (uint64_t)wosize);
        *gc_gen_heap.fp_ref = res.fst;
        result = res.snd;
        PROF_END(major_alloc);
    }

    if (result == 0) {
        expand_major_heap_for_allocation((uint64_t)wosize);
        PROF_START(major_alloc);
        fp = *gc_gen_heap.fp_ref;
        res = allocate(gc_gen_heap.major, fp, (uint64_t)wosize);
        *gc_gen_heap.fp_ref = res.fst;
        result = res.snd;
        PROF_END(major_alloc);
    }

    if (result == 0) {
        caml_fatal_error("verified gen GC: major allocation failed after collection");
        return NULL;
    }

    PROF_INC(major_alloc_count);

    /* allocate returns an absolute object address (first field = header + 8)
     * via the major heap's NULL-base trick.  The OCaml runtime finalizes the
     * header after this returns, installing the requested tag/profinfo bits. */
    return (void *)(uintptr_t)object_header_addr_or_fatal(
        result, "verified gen GC: major allocation header address underflow");
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
