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

/* The size classes (GC.Spec.SizeClass): list w holds free blocks of wosize w
 * for 1 <= w <= VGC_N_SMALL, list 0 every larger one.  Must equal
 * n_small_u64, which the extracted code has inlined; the snapshot's
 * size_lists_test.c checks the extracted allocator's cut-off. */
#define VGC_N_SMALL 16
#define VGC_N_LISTS (VGC_N_SMALL + 1)
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
#include "../caml/signals.h" /* for caml_update_young_limit */
#include "../caml/address_class.h" /* for In_heap, caml_page_table_add */
#include "../caml/memprof.h" /* for caml_memprof_renew_minor_sample */
#include "../caml/major_gc.h" /* for caml_allocated_words */

/* --- Patched externs from GC_Gen_Impl.c --- */
#include "GC_Spec_ZeroAddr.h"  /* zero_addr, heap_size_u64 */
#include "profiling_counters.h"
extern size_t queue_size_sz;

/* --- Globals --- */
static gen_heap_t   gc_gen_heap;
static uint64_t    *gc_fwd_arr;
static uint64_t    *gc_queue;         /* BFS queue for Cheney promotion (heap-allocated) */
static uint64_t     gc_tbl_len;       /* object-start table: entries (64 KB windows) */
static uint8_t     *minor_base;      /* absolute address of minor heap buffer */
static int          heap_initialized = 0;
static uint64_t    *minor_snapshot;   /* do_full_gc: minor heap before gen_gc */

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

/* Root scanning: parallel arrays for roots and writeback locations */
#define MAX_ROOTS  (1 << 18)  /* 256K root slots */
static uint64_t   root_values[MAX_ROOTS];
static value      *root_locs[MAX_ROOTS];
static size_t      root_count;

/* Track total bytes promoted or allocated directly in the major heap
 * (verified_allocate) since the last major GC.  When this approaches the
 * major heap size, we trigger a major GC to avoid promotion failures. */
static uint64_t   bytes_promoted_since_major = 0;
static int        in_full_gc = 0;  /* re-entrancy guard */

/* Fast-path tracking: when only non-pointer objects (tag >= no_scan_tag) are
 * allocated in the minor heap, the verified BFS trivially handles them
 * (objects with tag >= no_scan_tag have no pointer fields to scan). */

/* minor_base_addr is defined in the extracted GC_Gen_Base module.
 * We set it at runtime to the actual minor heap buffer address so that
 * the verified to_minor_offset_u64 can translate absolute→offset inline. */
extern uint64_t minor_base_addr;

#ifdef VERGC_PROTO
/* The allocator-comparison prototypes (verified_gc/proto/, docs/
 * allocator-comparison-results.md).  Built only with PROTO=A or PROTO=B. */
void vergc_proto_init(uint64_t *heads, uint64_t *tbl, uint64_t tbl_len);
void vergc_proto_minor_begin(uint64_t promoted_words, uint64_t heap_words);
void vergc_proto_minor_end(void);
void vergc_proto_full_begin(void);
void vergc_proto_full_end(void);
void vergc_proto_direct_begin(void);
void vergc_proto_direct_end(void);
int  impl_sweeping(void);
void vergc_proto_check(const char *where);
uint64_t vergc_proto_scale(uint64_t requested_bytes);
#define VERGC_CONSUMED(b) vergc_proto_scale(b)
#else
#define VERGC_CONSUMED(b) (b)
#endif

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

    /* Free-list heads, one per size class (GC.Spec.SizeClass): class w for
     * 1 <= w <= n_small, class 0 for every larger block.  The one free block
     * goes on the list of its class. */
    uint64_t *heads = (uint64_t *)calloc(VGC_N_LISTS, sizeof(uint64_t));
    if (!heads) caml_fatal_error("verified gen GC: calloc heads");
    heads[(1 <= wosize && wosize <= VGC_N_SMALL) ? wosize : 0] = initial_fp;
    gc_gen_heap.heads = heads;

    /* Object-start table (GC.Spec.ObjectTable): one entry per 64 KB window of
     * the major heap, naming a header of the heap walk at or below the
     * window's first byte (exactly the block containing it, right after a
     * sweep or a rebuild).  The verified rebuild walks the heap once. */
    gc_tbl_len = ((uint64_t)major_bytes + 0xFFFFULL) >> 16;
    uint64_t *tbl = (uint64_t *)calloc((size_t)gc_tbl_len, sizeof(uint64_t));
    if (!tbl) caml_fatal_error("verified gen GC: calloc object-start table");
    gc_gen_heap.tbl = tbl;
    /* Filled by the verified rebuild once krmlinit_globals() has run below:
     * the extracted code reads its own copy of zero_addr, set there. */

    /* --- Minor heap --- */
    /* Override the verified constant (2048B) with a production-sized minor heap.
     * OCaml default is 256K words = 2MB.  We match that default, overridable
     * via environment variable. */
    max_young_wosize_u64 = 256ULL;  /* match OCaml's Max_young_wosize */
    size_t minor_words = 256 * 1024;  /* 2 MB / 8 = 256K words (matches OCaml default) */
    const char *minor_env = getenv("MINOR_HEAP_WORDS");
    if (minor_env) {
        size_t w = (size_t)atoll(minor_env);
        if (w > 0) minor_words = w;
    }
    if (minor_words < (size_t)max_young_wosize_u64 + 1)
        minor_words = (size_t)max_young_wosize_u64 + 1;
    size_t minor_sz = minor_words * 8;
    minor_heap_size_u64 = (uint64_t)minor_sz;

    /* Re-derive constants that depend on minor_heap_size */
    krmlinit_globals();
    table_rebuild(gc_gen_heap.major, gc_gen_heap.tbl);
#ifdef VERGC_PROTO
    vergc_proto_init(heads, tbl, gc_tbl_len);
#endif
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

    /* Finish the swap the way stock caml_set_minor_heap_size does (see the
     * tail of that function in runtime/minor_gc.c).  Overwriting young_start /
     * young_end / young_ptr alone is not enough: young_limit and
     * caml_memprof_young_trigger still point into the buffer we are about to
     * free, and both are at a *higher* address than this heap, so
     *
     *   - every allocation sees young_ptr < young_limit and traps into
     *     caml_alloc_small_dispatch, and
     *   - young_ptr < caml_memprof_young_trigger breaks memprof's invariant
     *     "lambda == 0 implies caml_memprof_young_trigger == young_alloc_start",
     *     so a sample is recorded with lambda == 0 and a garbage n_samples.
     *     The callback then reads Alloc_minor(tracker) with tracker == 0.
     *
     * caml_memprof_renew_minor_sample() resets the trigger and calls
     * caml_update_young_limit() for us. */
    Caml_state->_young_alloc_mid = Caml_state->_young_alloc_start
                                   + Wsize_bsize (minor_sz) / 2;
    Caml_state->_young_trigger   = Caml_state->_young_alloc_start;
    Caml_state->_minor_heap_wsz  = Wsize_bsize (minor_sz);
    caml_memprof_renew_minor_sample();

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
    uint64_t major_size = heap_size_u64 - zero_addr;
    fprintf(stderr,
        "verified gen GC: promotion failed — major heap full (%lu MB)\n"
        "  Some objects could not be promoted (live set exceeds heap capacity).\n"
        "  Set MIN_EXPANSION_WORDSIZE=%lu (or larger) to increase heap.\n",
        (unsigned long)(major_size / 1048576),
        (unsigned long)(major_size / 4));
    caml_fatal_error("verified gen GC: out of memory (major heap too small)");
}

/* Words promoted by the collection that just ran.  gc_fwd_arr maps the minor
 * offset of each promoted object to its major copy, so index i is the object
 * whose header is minor word i - 1.  An entry whose header is Infix_tag is an
 * interior pointer into a closure counted under its parent: skip it.
 *
 * The minor heap is zeroized by the collection, so headers come either from
 * the major copies (snapshot == NULL: valid only when nothing has swept
 * the major heap since promotion) or from a pre-collection copy of the minor
 * heap. */
static uint64_t promoted_words(const uint64_t *snapshot) {
    uint64_t words = 0;
    size_t i;
    for (i = 1; i < queue_size_sz; i++) {
        uint64_t fwd = gc_fwd_arr[i];
        header_t hd;
        if (fwd == 0) continue;
        hd = snapshot != NULL ? (header_t)snapshot[i - 1]
                              : Hd_val((value)(uintptr_t)fwd);
        if (Tag_hd(hd) == Infix_tag) continue;
        words += Whsize_hd(hd);
    }
    return words;
}

/* Stock promotes through caml_alloc_shr_for_minor_gc, which counts promoted
 * words in caml_allocated_words (and so in major_words) as well as in
 * promoted_words.  Do the same so minor + major - promoted stays the total. */
static void count_promoted_words(uint64_t words) {
    Caml_state->_stat_promoted_words += (double)words;
    caml_allocated_words += (uintnat)words;
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


/* --- Free-list and object-start table checker (test builds only) ---
 *
 * With -DVGC_CHECK_ALLOC, every collection, and every 1024th direct major
 * allocation, re-checks the free-list invariant the proofs maintain
 * (GC.Spec.FreeLists: fls_valid, fls_terminates, fls_exact) and the table
 * invariant (GC.Spec.ObjectTable.table_sound) by walking the major heap:
 *   - the walk from zero_addr tiles the heap exactly;
 *   - every table entry is a header of the walk, at or below its window's
 *     boundary zero_addr + j * 64 KB, and the entries do not decrease;
 *   - right after a full collection (exact != 0), when the sweep has just
 *     rebuilt the table, every entry is moreover the header of the walk block
 *     that contains its boundary (GC.Spec.ObjectTable.table_ok).  Between
 *     sweeps that need not hold: unmarshalling (runtime/intern.c) re-tiles a
 *     major block into the objects it reads, adding walk positions the
 *     table does not hear of;
 *   - every cell of list i is the start of a blue object of wosize >= 1 whose
 *     class is i (class w = w for 1 <= w <= n_small, else 0);
 *   - each list ends, and no cell is on a list twice or on two lists;
 *   - every blue object of wosize >= 1 is on a list.
 * Any failure aborts with a message naming the check. */
#ifdef VGC_CHECK_ALLOC
static uint8_t *chk_starts;           /* one bit per heap word: an object start */
static uint8_t *chk_hdrs;             /* one bit per heap word: a walk header */
static uint64_t chk_alloc_count;

static void chk_fail(const char *where, const char *what, size_t list, uint64_t cell) {
    fprintf(stderr, "VGC_CHECK_ALLOC: %s: %s (list %zu, cell 0x%llx)\n",
            where, what, list, (unsigned long long)cell);
    abort();
}

static void check_free_lists(const char *where, int exact) {
    uint64_t z = zero_addr, hs = heap_size_u64;
    uint64_t words = (hs - z) / 8;
    uint64_t n_small = VGC_N_SMALL;
    size_t n_lists = VGC_N_LISTS;
    if (!chk_starts) {
        chk_starts = (uint8_t *)calloc((size_t)(words / 8 + 1), 1);
        chk_hdrs = (uint8_t *)calloc((size_t)(words / 8 + 1), 1);
        if (!chk_starts || !chk_hdrs) caml_fatal_error("VGC_CHECK_ALLOC: calloc");
    }
    memset(chk_starts, 0, (size_t)(words / 8 + 1));
    memset(chk_hdrs, 0, (size_t)(words / 8 + 1));
    /* 1. the walk, marking the walk headers and the object starts that can be
     *    cells, and (exact) checking the entries of the boundaries inside each
     *    block */
    uint64_t cells = 0;
    uint64_t pos = z;
    uint64_t k = 0, last = z;
    while (pos + 8 < hs) {
        uint64_t hdr = *(uint64_t *)(uintptr_t)pos;
        uint64_t wz = hdr >> 10;
        uint64_t col = (hdr >> 8) & 3;
        uint64_t next = pos + (wz + 1) * 8;
        if (next > hs || next <= pos) chk_fail(where, "walk overruns the heap", 0, pos + 8);
        {
            uint64_t h = (pos - z) / 8;
            chk_hdrs[h / 8] |= (uint8_t)(1u << (h % 8));
        }
        while (exact && k < gc_tbl_len && z + (k << 16) < next) {
            if (gc_gen_heap.tbl[k] != pos) {
                uint64_t got = gc_gen_heap.tbl[k];
                fprintf(stderr, "VGC_CHECK_ALLOC: window %llu (boundary +0x%llx): entry +0x%llx, "
                        "containing block +0x%llx (wosize %llu, colour %llu)\n",
                        (unsigned long long)k, (unsigned long long)(k << 16),
                        (unsigned long long)(got - z), (unsigned long long)(pos - z),
                        (unsigned long long)wz, (unsigned long long)col);
                chk_fail(where, "table entry does not name the block containing its boundary",
                         (size_t)k, got);
            }
            k++;
        }
        last = pos;
        if (col == 2 && wz >= 1) {
            uint64_t w = (pos + 8 - z) / 8;
            chk_starts[w / 8] |= (uint8_t)(1u << (w % 8));
            cells++;
        }
        pos = next;
    }
    if (exact)
        for (; k < gc_tbl_len; k++)
            if (gc_gen_heap.tbl[k] != last)
                chk_fail(where, "table entry past the walk does not name the last block",
                         (size_t)k, gc_gen_heap.tbl[k]);
    /* 1b. the table is sound: every entry a walk header at or below its
     *     boundary, entries non-decreasing */
    for (k = 0; k < gc_tbl_len; k++) {
        uint64_t e = gc_gen_heap.tbl[k];
        if (e < z || e >= hs || (e - z) % 8 != 0)
            chk_fail(where, "table entry outside the heap or misaligned", (size_t)k, e);
        uint64_t h = (e - z) / 8;
        if (!(chk_hdrs[h / 8] & (1u << (h % 8))))
            chk_fail(where, "table entry is not a header of the walk", (size_t)k, e);
        if (e > z + (k << 16))
            chk_fail(where, "table entry above its boundary", (size_t)k, e);
        if (k > 0 && gc_gen_heap.tbl[k - 1] > e)
            chk_fail(where, "table entries decrease", (size_t)k, e);
    }
    /* 2. the lists: each cell is a marked start of its class, met once */
    uint64_t listed = 0;
    for (size_t i = 0; i < n_lists; i++) {
        uint64_t cur = gc_gen_heap.heads[i];
        uint64_t steps = 0;
        while (cur != 0) {
            if (cur % 8 != 0 || cur < z + 8 || cur >= hs)
                chk_fail(where, "cell out of the heap or misaligned", i, cur);
            uint64_t w = (cur - z) / 8;
            if (!(chk_starts[w / 8] & (1u << (w % 8))))
                chk_fail(where, "cell is not a free block with a link, or is listed twice", i, cur);
            chk_starts[w / 8] &= (uint8_t)~(1u << (w % 8));
            uint64_t wz = *(uint64_t *)(uintptr_t)(cur - 8) >> 10;
            size_t cls = (1 <= wz && wz <= n_small) ? (size_t)wz : 0;
            if (cls != i) chk_fail(where, "cell on the wrong list for its size", i, cur);
            listed++;
            if (++steps > words) chk_fail(where, "list does not end", i, cur);
            cur = *(uint64_t *)(uintptr_t)cur;
        }
    }
    /* 3. every free block with a link is listed */
    if (listed != cells) chk_fail(where, "a free block is on no list", 0, 0);
}

/* The allocator's table writes, after each direct major allocation of `wz`
 * words at `obj`: every boundary inside the new object names its header
 * (GC.Spec.ObjectTable.alloc_table), unless the entry past them names a
 * block below it (alloc_stale), in which case none is written. */
static void check_alloc_table(uint64_t obj, uint64_t wz) {
    uint64_t z = zero_addr, hs = heap_size_u64;
    uint64_t hp = obj - 8, p_end = obj + wz * 8;
    uint64_t lim = (p_end + 8 >= hs) ? hs : p_end;
    uint64_t j0 = (hp - z + 0xFFFF) >> 16, k1 = (lim - z + 0xFFFF) >> 16;
    if (j0 >= k1) return;
    if (k1 < gc_tbl_len && gc_gen_heap.tbl[k1] < hp) return;
    for (uint64_t j = j0; j < k1; j++)
        if (gc_gen_heap.tbl[j] != hp)
            chk_fail("after a major allocation",
                     "allocator did not set the entry of a boundary inside the object",
                     (size_t)j, gc_gen_heap.tbl[j]);
}
#if defined(VERGC_PROTO)
#define CHECK_FREE_LISTS(where) \
    do { if (!impl_sweeping()) check_free_lists(where, 0); } while (0)
#define CHECK_FREE_LISTS_EXACT(where) \
    do { if (!impl_sweeping()) check_free_lists(where, 1); } while (0)
#else
#define CHECK_FREE_LISTS(where) check_free_lists(where, 0)
#define CHECK_FREE_LISTS_EXACT(where) check_free_lists(where, 1)
#endif
#elif defined(VERGC_PROTO_B) && defined(VERGC_PROTO_CHECK)
#define CHECK_FREE_LISTS(where) vergc_proto_check(where)
#define CHECK_FREE_LISTS_EXACT(where) vergc_proto_check(where)
#else
#define CHECK_FREE_LISTS(where) ((void)0)
#define CHECK_FREE_LISTS_EXACT(where) ((void)0)
#endif

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
    CHECK_FREE_LISTS("after a minor collection");

    /* No sweep has run since promotion, so the major copies' headers are
     * intact. */
    count_promoted_words(promoted_words(NULL));

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
        uint64_t major_size = heap_size_u64 - zero_addr;
        /* Use 50% threshold — balances sweep cost vs fragmentation */
        uint64_t threshold = major_size / 2;
        if (VERGC_CONSUMED(bytes_promoted_since_major + bump) > threshold) {
            do_full_gc();
            if (*gc_gen_heap.minor.bump_ref == 0) return;
        }
    }

    uint64_t bump_before = *gc_gen_heap.minor.bump_ref;
    Caml_state->_stat_minor_collections++;
    Caml_state->_stat_minor_words += (double)(bump_before / sizeof(value));

#ifdef VERGC_PROTO
    vergc_proto_minor_begin(bytes_promoted_since_major / 8,
                            (heap_size_u64 - zero_addr) / 8);
#endif
    do_minor_gc_core();
#ifdef VERGC_PROTO
    vergc_proto_minor_end();
#endif

    /* Track promoted bytes (approximate by the minor bump value) */
    bytes_promoted_since_major += bump_before;
}

#ifdef NATIVE_CODE

/* Called from runtime/startup_nat.c, right
 * after caml_init_gc(), to point minor heap to the one managed by verified GC 
 * overriding whatever stock init has set up. */
void vergc_native_minor_startup_init(void) {
    /* Save stock's real minor buffer (allocated moments ago by
     * caml_init_gc -> caml_set_minor_heap_size, in runtime/startup_nat.c
     * right before this function is called) so it can be freed below --
     * ensure_heap() immediately overwrites these fields to point at our
     * own buffer, and once overwritten, the old pointer is unrecoverable.
     */
    void  *old_base  = Caml_state->_young_base;
    value *old_start = Caml_state->_young_start;
    value *old_end   = Caml_state->_young_end;

    ensure_heap();

    if (caml_page_table_add(In_young, minor_base,
                             minor_base + minor_heap_size_u64) != 0)
        caml_fatal_error("verified gen GC: minor page table registration failed");

    if (old_start != NULL) {
        caml_page_table_remove(In_young, old_start, old_end);
        caml_stat_free(old_base);
    }
}

/* Native backend decrements young_ptr in the fast allocation path to minor heap. 
 * Native's compiled code allocates top-down (young_ptr descends from
 * young_alloc_end); bump_ref counts bytes used, bottom-up.  The two
 * conventions differ in DIRECTION, but "how many bytes are in use" is the
 * same number in both.

 * Setting bump_ref to number of bytes used would mean that minor heap is occupied
 * from [0, bump_ref) - but that is not the case as native code fills the minor heap 
 * from high end. But, our verified gc only uses bump_ref to know how many bytes are used
 * and never walks from [0, bump_ref] - so this is safe to do until we make our verified gc
 * match the native code's allocation direction.
 */
static void vergc_sync_bump_ref_from_young_ptr(void) {
     uint64_t used_bytes = (uint64_t)((uint8_t *)Caml_state->_young_alloc_end
                                      - (uint8_t *)Caml_state->_young_ptr);
    /* This check is required because native code decrements young_ptr regardless of it going below the start */
    if (used_bytes > minor_heap_size_u64) used_bytes = minor_heap_size_u64;
    *gc_gen_heap.minor.bump_ref = used_bytes;
}

/* After a collection has emptied the minor heap (bump_ref == 0), move
 * young_ptr back to match. */
static void vergc_native_reset_young_ptr(void) {
    Caml_state->_young_ptr = Caml_state->_young_alloc_end; /* reset minor heap to empty */
    Caml_state->_young_trigger = Caml_state->_young_alloc_start; /* ensures young_trigger remains start of the heap */
    caml_update_young_limit(); /* set the young_limit, which is actually used by native code to check if heap is full 
                                * can be different from young_trigger if there is memory profiling */
}

void vergc_native_run_minor_collection(void) {
    vergc_sync_bump_ref_from_young_ptr(); /* do_minor_gc uses bump_ref to check if collection is needed */
    do_minor_gc();
    vergc_native_reset_young_ptr();
}

#endif

/* --- Full GC (minor + major) --- */

static int full_gc_count = 0;

static void do_full_gc(void) {
    ensure_heap();
    in_full_gc = 1;
#ifdef VERGC_PROTO
    vergc_proto_full_begin();
#endif

    #ifdef NATIVE_CODE
        /* A full GC can be entered without passing through
        * vergc_native_run_minor_collection() */
        vergc_sync_bump_ref_from_young_ptr();
    #endif

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

    /* gen_gc sweeps after promoting, and a promoted copy reachable only
     * through a dead remembered slot can be swept and coalesced, so its major
     * header cannot be read afterwards.  It also zeroizes the minor heap, so
     * keep a copy of the minor headers for promoted_words. */
    if (minor_snapshot == NULL) {
        minor_snapshot = (uint64_t *)malloc((size_t)minor_heap_size_u64);
        if (!minor_snapshot)
            caml_fatal_error("verified gen GC: cannot allocate minor snapshot");
    }
    memcpy(minor_snapshot, minor_base, (size_t)minor_heap_size_u64);

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
        bool ok =
            gen_gc(gc_gen_heap, roots_for_gc, (size_t)root_count, gc_fwd_arr,
                   gc_queue, (uint64_t *)tbl->base, n_slots, gc_stack);
        if (!ok) {
            free(roots_for_gc);
            free(gray_storage);
            in_full_gc = 0;
            fatal_promotion_failed();
        }
    }

    CHECK_FREE_LISTS_EXACT("after a full collection");

    PROF_START(writeback);
    write_back_forwarded_roots();
    PROF_END(writeback);

    Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
    bytes_promoted_since_major = 0;

    free(roots_for_gc);
    free(gray_storage);
    PROF_END(major_gc);
#ifdef VERGC_PROTO
    vergc_proto_full_end();
#endif

    #ifdef NATIVE_CODE
        /* gen_gc emptied the minor heap.  Without this young_ptr keeps its
         * old value: the next collection would count those words in
         * minor_words a second time, and the space would not be reused. */
        vergc_native_reset_young_ptr();
    #endif

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

    /* The verified `allocate` now carries `wosize >= 1` as a precondition, so
     * that the implementation can drop a compare-and-select from every major
     * allocation. Nothing in the OCaml runtime should reach here with zero --
     * a zero-length block is the static Atom, not a heap allocation -- but a
     * C stub calling caml_alloc_shr(0, tag) would, and the patched
     * caml_alloc_shr_aux only rejects sizes ABOVE Max_wosize.
     *
     * Normalize rather than reject, because that is what `alloc_spec` does
     * (`let wz = if requested_wz = 0 then 1 else requested_wz`). Rejecting
     * would make the bridge disagree with the spec the Pulse code is verified
     * against; normalizing keeps them in step. */
    if (wosize == 0) wosize = 1;

    /* Proactive full GC, on the same 50% threshold as do_minor_gc().  Direct
     * major allocations count toward bytes_promoted_since_major (below), so a
     * heap filled by large blocks that are then dropped still triggers a full
     * collection before the next minor collection has to promote into it
     * (issue #34). */
    uint64_t alloc_bytes = ((uint64_t)wosize + 1) * 8;
    if (!in_full_gc) {
        uint64_t major_size = heap_size_u64 - zero_addr;
        if (VERGC_CONSUMED(bytes_promoted_since_major + alloc_bytes) > major_size / 2)
            do_full_gc();
    }

#ifdef VERGC_PROTO
    vergc_proto_direct_begin();
#endif
    PROF_START(major_alloc);
    uint64_t result = allocate(gc_gen_heap.major, gc_gen_heap.heads, gc_gen_heap.tbl, (uint64_t)wosize);
    PROF_END(major_alloc);
#ifdef VGC_CHECK_ALLOC
    if ((++chk_alloc_count & 1023) == 0) CHECK_FREE_LISTS("after a major allocation");
#elif defined(VERGC_PROTO_B) && defined(VERGC_PROTO_CHECK)
    {
        static uint64_t n_direct;
        if ((++n_direct & 1023) == 0) CHECK_FREE_LISTS("after a major allocation");
    }
#endif

    if (result == 0) {
        do_full_gc();
        PROF_START(major_alloc);
        result = allocate(gc_gen_heap.major, gc_gen_heap.heads, gc_gen_heap.tbl, (uint64_t)wosize);
        PROF_END(major_alloc);
    }
#ifdef VERGC_PROTO
    vergc_proto_direct_end();
#endif

    if (result == 0) {
        /* The heap here is the one a full collection just produced, so by
         * GC.Spec.Allocator.Oom.fused_oom_no_fit every free block is smaller
         * than the request: the heap may still have enough free words in total,
         * but no single block fits.
         *
         * Return failure rather than aborting: caml_alloc_shr_aux's check_oom()
         * turns a NULL/0 into a catchable Out_of_memory (and into a fatal error
         * by itself if we are inside a minor collection, where raising is not
         * possible -- that is stock's own distinction). Calling
         * caml_fatal_error() here instead made Out_of_memory unraisable in this
         * runtime: a program with `try ... with Out_of_memory` had its process
         * killed instead of its handler run.
         *
         * Keep the sizing hint, once, because our major heap does not grow and
         * the user genuinely needs to know which knob to turn. */
        static int hinted = 0;
        if (!hinted) {
            uint64_t major_size = heap_size_u64 - zero_addr;
            hinted = 1;
            fprintf(stderr,
                "verified gen GC: major heap exhausted (%lu MB) — raising "
                "Out_of_memory.\n  The major heap does not grow; set "
                "MIN_EXPANSION_WORDSIZE=%lu (or larger) to enlarge it.\n",
                (unsigned long)(major_size / 1048576),
                (unsigned long)(major_size / 4));
        }
        return NULL;
    }

#if defined(VGC_CHECK_ALLOC) && !defined(VERGC_PROTO_B)
    check_alloc_table(result, (uint64_t)wosize);
#endif
    PROF_INC(major_alloc_count);
    bytes_promoted_since_major += alloc_bytes;

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

/* Called by Gc.major, Gc.full_major and Gc.compact (runtime/gc_ctrl.c) in
 * place of the stock major cycle and compaction.  do_full_gc collects both
 * generations and counts the minor collection, the major collection and the
 * promoted words. */
void verified_do_full_gc(void) {
    do_full_gc();
}

/* Called by caml_minor_collection() in minor_gc.c.
 * Some C primitives (e.g., caml_make_vect for large arrays) force a minor
 * collection to promote a young value before using it without write barriers.
 * We must actually run our verified minor GC so that (a) the value gets
 * promoted to major and (b) the ref_table isn't silently cleared. */
void verified_do_minor_gc(void) {
    ensure_heap();
#ifdef NATIVE_CODE
    /* Native keeps the authoritative state in young_ptr; the helper does the
     * young_ptr <-> bump_ref translation and resets young_ptr afterwards. */
    if (Caml_state->_young_ptr != Caml_state->_young_alloc_end) vergc_native_run_minor_collection();
#else
    /* Bytecode allocates through bump_ref directly (young_ptr is parked at
     * young_alloc_end by ensure_heap and never moves), so no translation is
     * needed; do_minor_gc() already no-ops when bump_ref == 0. */
    do_minor_gc();
#endif
}