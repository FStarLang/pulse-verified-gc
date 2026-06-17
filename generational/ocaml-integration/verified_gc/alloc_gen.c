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

/* Major chunks registered with the OCaml page table.  The verified entrypoints
 * are still dense/single-chunk today; this table makes the trusted runtime
 * boundary explicit before wiring discontiguous extracted APIs. */
#define MAX_MAJOR_CHUNKS 1024
#define DEFAULT_MAJOR_WORDS ((size_t)32 * 1024 * 1024)
#define DEFAULT_MINOR_WORDS ((size_t)256 * 1024)
#define MAX_MAJOR_CHUNK_WORDS (1ULL << 54)
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
    if (words < 2)
        caml_fatal_error("verified gen GC: %s must be at least 2 words", name);
    if ((unsigned long long)words > MAX_MAJOR_CHUNK_WORDS)
        caml_fatal_error("verified gen GC: %s must be at most 2^54 words", name);
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

static size_t words_to_bytes_or_fatal(size_t words, const char *what) {
    if (words > SIZE_MAX / sizeof(value))
        caml_fatal_error("%s", what);
    return words * sizeof(value);
}

static uint8_t *allocate_major_chunk_memory(size_t bytes) {
    uint8_t *base = (uint8_t *)calloc(1, bytes);
    if (!base)
        caml_fatal_error("verified gen GC: cannot allocate major heap");
    return base;
}

static int ranges_overlap(uintptr_t start, uintptr_t end,
                          uintptr_t other_start, uintptr_t other_end) {
    return start < other_end && other_start < end;
}

static void check_major_chunk_facts(uint8_t *base, size_t bytes) {
    uintptr_t start = (uintptr_t)base;
    uintptr_t end = start + bytes;
    size_t i;

    if (base == NULL)
        caml_fatal_error("verified gen GC: null major chunk");
    if (bytes == 0 || bytes % sizeof(value) != 0)
        caml_fatal_error("verified gen GC: invalid major chunk size");
    if (start % sizeof(value) != 0)
        caml_fatal_error("verified gen GC: unaligned major chunk base");
    if (end < start)
        caml_fatal_error("verified gen GC: major chunk address overflow");

    if (minor_base != NULL && minor_heap_size_u64 != 0) {
        uintptr_t minor_start = (uintptr_t)minor_base;
        uintptr_t minor_size = (uintptr_t)minor_heap_size_u64;
        uintptr_t minor_end = minor_start + minor_size;
        if ((uint64_t)minor_size != minor_heap_size_u64 || minor_end < minor_start)
            caml_fatal_error("verified gen GC: minor heap address overflow");
        if (ranges_overlap(start, end, minor_start, minor_end))
            caml_fatal_error("verified gen GC: major chunk overlaps minor heap");
    }

    for (i = 0; i < major_chunk_count; i++) {
        uintptr_t old_start = (uintptr_t)major_chunks[i].base;
        uintptr_t old_end = old_start + major_chunks[i].bytes;
        if (ranges_overlap(start, end, old_start, old_end))
            caml_fatal_error("verified gen GC: overlapping major chunks");
    }
}

static void register_major_chunk(uint8_t *base, size_t bytes) {
    check_major_chunk_facts(base, bytes);
    if (major_chunk_count >= MAX_MAJOR_CHUNKS)
        caml_fatal_error("verified gen GC: too many major chunks");
    if (bytes > UINT64_MAX - major_bytes_total)
        caml_fatal_error("verified gen GC: major heap size overflow");
    if (caml_page_table_add(In_heap, base, base + bytes) != 0)
        caml_fatal_error("verified gen GC: page table registration failed");
    major_chunks[major_chunk_count].base = base;
    major_chunks[major_chunk_count].bytes = bytes;
    major_chunk_count++;
    major_bytes_total += (uint64_t)bytes;
}

static uint64_t current_major_bytes(void) {
    return major_bytes_total;
}

static inline uint64_t header_wosize(uint64_t header) {
    return header >> 10;
}

/* Runtime mirror of the verified minor_promotion_demand shape: sum the
 * header-inclusive size of every currently allocated minor object. */
static uint64_t minor_promotion_demand_words(void) {
    uint64_t off = 0;
    uint64_t bump = *gc_gen_heap.minor.bump_ref;
    uint64_t demand = 0;

    if (bump > minor_heap_size_u64 || bump % sizeof(value) != 0)
        caml_fatal_error("verified gen GC: invalid minor allocation frontier");

    while (off < bump) {
        uint64_t header = *(uint64_t *)(minor_base + off);
        uint64_t wosize = header_wosize(header);
        uint64_t object_words;
        uint64_t object_bytes;

        if (wosize > UINT64_MAX - 1)
            caml_fatal_error("verified gen GC: minor object size overflow");
        object_words = wosize + 1;
        if (object_words > UINT64_MAX / sizeof(value))
            caml_fatal_error("verified gen GC: minor object byte overflow");
        object_bytes = object_words * sizeof(value);
        if (object_bytes == 0 || object_bytes > bump - off)
            caml_fatal_error("verified gen GC: malformed minor object layout");
        if (demand > UINT64_MAX - object_words)
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
    if (zero_addr > UINT64_MAX - sizeof(value))
        caml_fatal_error("verified gen GC: invalid major base address");
    if (fp < zero_addr + sizeof(value) || fp >= heap_size_u64)
        caml_fatal_error("verified gen GC: invalid major free-list head");
    if (fp % sizeof(value) != 0)
        caml_fatal_error("verified gen GC: unaligned major free-list head");

    header_addr = (uintptr_t)(fp - sizeof(value));
    return header_wosize(*(uint64_t *)header_addr);
}

static uint64_t required_head_wosize_for_promotion(uint64_t demand_words) {
    if (demand_words > UINT64_MAX - 1)
        caml_fatal_error("verified gen GC: promotion demand too large");
    return demand_words + 1;
}

static uint64_t required_chunk_words_for_head(uint64_t head_wosize) {
    if (head_wosize > UINT64_MAX - 1)
        caml_fatal_error("verified gen GC: promotion head demand too large");
    return head_wosize + 1;
}

static uint64_t suggested_major_words_for_retry(uint64_t required_chunk_words) {
    uint64_t current_words = current_major_bytes() / sizeof(value);
    uint64_t doubled_words =
        current_words > UINT64_MAX / 2 ? UINT64_MAX : current_words * 2;
    return doubled_words >= required_chunk_words
        ? doubled_words
        : required_chunk_words;
}

static uint64_t planned_expansion_chunk_words(uint64_t required_chunk_words) {
    uint64_t configured_words = (uint64_t)configured_expansion_chunk_words();
    return configured_words >= required_chunk_words
        ? configured_words
        : required_chunk_words;
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

static int major_preflight_head_ready(const major_preflight_snapshot *snapshot) {
    return snapshot->head_wosize >= snapshot->required_head_wosize;
}

/* Inline minor-allocation fast-path state for Alloc_small_aux (memory.h).
 * The fast path reserves bytes by updating the same verified bump counter;
 * collections and heap initialization still go through verified_allocate_minor(). */
uint64_t *vergc_minor_bump_ref;
uint8_t  *vergc_minor_base;
uint64_t  vergc_minor_size;

uintnat vergc_minor_words_current(void) {
    if (!heap_initialized || gc_gen_heap.minor.bump_ref == NULL) return 0;
    return (uintnat)(*gc_gen_heap.minor.bump_ref / sizeof(value));
}

uintnat vergc_major_words_current(void) {
    if (!heap_initialized) return 0;
    return (uintnat)(current_major_bytes() / sizeof(value));
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
    size_t major_bytes = words_to_bytes_or_fatal(
        major_words, "verified gen GC: major heap word size overflow");

    uint8_t *major_base = allocate_major_chunk_memory(major_bytes);

    /* NULL-base trick: GC offsets become absolute addresses */
    zero_addr = (uint64_t)(uintptr_t)major_base;
    heap_size_u64 = (uint64_t)(uintptr_t)(major_base + major_bytes);

    gc_gen_heap.major.data = NULL;
    gc_gen_heap.major.size = major_bytes;

    /* Initialize major free list through the verified raw chunk formatter. */
    uint64_t total_words_u64 = (uint64_t)major_words;
    uint64_t wosize = total_words_u64 - 1;
    uint64_t initial_fp =
        init_major_chunk_raw(gc_gen_heap.major, zero_addr, zero_addr + 8, wosize, 0);

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
    if (minor_words < (size_t)max_young_wosize_u64 + 1)
        minor_words = (size_t)max_young_wosize_u64 + 1;
    size_t minor_sz = minor_words * 8;
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

    caml_gc_message(0x20, "Verified gen GC: major=%luMB in %lu chunk(s) minor=%luKB\n",
                    (unsigned long)(major_bytes / (1024*1024)),
                    (unsigned long)major_chunk_count,
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
                uint64_t off = v64 - (uint64_t)(uintptr_t)minor_base;
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
        "  Future expansion chunk policy would request >= %llu words.\n"
        "  Current head satisfies preflight: %s.\n"
        "  Some objects could not be promoted (live set exceeds heap capacity).\n"
        "  Set MIN_EXPANSION_WORDSIZE=%llu (or larger) to increase heap.\n",
        (unsigned long)(major_size / 1048576),
        (unsigned long)major_chunk_count,
        (unsigned long long)snapshot.demand_words,
        (unsigned long long)snapshot.head_wosize,
        (unsigned long long)snapshot.required_head_wosize,
        (unsigned long long)snapshot.required_chunk_words,
        (unsigned long long)snapshot.planned_expansion_words,
        major_preflight_head_ready(&snapshot) ? "yes" : "no",
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
    Caml_state->_stat_minor_words += (double)(bump_before / sizeof(value));

    do_minor_gc_core();

    /* Track promoted bytes (approximate by the minor bump value) */
    bytes_promoted_since_major += bump_before;
}

/* --- Full GC (minor + major) --- */

static int full_gc_count = 0;

static void do_full_gc(void) {
    ensure_heap();
    in_full_gc = 1;

    PROF_INC(major_gc_count);
    PROF_START(major_gc);
    Caml_state->_stat_major_collections++;
    full_gc_count++;

    if (*gc_gen_heap.minor.bump_ref != 0) {
        PROF_INC(minor_gc_count);
        Caml_state->_stat_minor_collections++;
        Caml_state->_stat_minor_words +=
            (double)(*gc_gen_heap.minor.bump_ref / sizeof(value));
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

    uint64_t needed = ((uint64_t)wosize + 1) * 8;
    if (needed > minor_heap_size_u64)
        caml_fatal_error("verified gen GC: minor heap smaller than Max_young_wosize");

    if (*gc_gen_heap.minor.bump_ref > minor_heap_size_u64 - needed) {
        do_minor_gc();
    }

    if (*gc_gen_heap.minor.bump_ref > minor_heap_size_u64 - needed) {
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
    uint64_t hdr_addr = result - 8;  /* header offset/address */
    return (void *)((uintptr_t)minor_base + (uintptr_t)hdr_addr);
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
        caml_fatal_error("verified gen GC: major allocation failed after collection");
        return NULL;
    }

    PROF_INC(major_alloc_count);

    /* allocate returns an absolute object address (first field = header + 8)
     * via the major heap's NULL-base trick.  The OCaml runtime finalizes the
     * header after this returns, installing the requested tag/profinfo bits. */
    return (void *)(uintptr_t)(result - 8);
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
