/* alloc_gen.c — Bridge between OCaml 4.14 runtime and the verified
 *               generational GC (Cheney minor + mark-and-sweep major).
 *
 * Provides:
 *   verified_allocate_minor(wosize, tag) — slow path for Alloc_small
 *   verified_allocate(wosize, tag)       — major/shared allocation path
 *   caml_trigger_verified_gc(unit)    — OCaml-callable full GC trigger
 *
 * Uses, from GC_Gen_Impl.c (GC.Gen.Impl, shaped like OCaml 4.14's
 * runtime/major_gc.c):
 *   minor_alloc()   — bump allocation in the minor heap
 *   allocate()      — free-list allocation in the major heap, at the phase
 *   minor_collect() — the minor collection (Cheney BFS + ref_table rewrite),
 *                     at either phase
 *   start_cycle()   — start a major cycle, idle and with the nursery empty:
 *                     darken the roots onto the persistent mark stack; the
 *                     phase becomes Marking (4.14's start_cycle)
 *   major_slice()   — one slice of the cycle (a budget in words): a mark
 *                     slice while marking (Sweeping once nothing is grey),
 *                     a sweep slice while sweeping; returns whether the
 *                     collector is idle again
 *                     (4.14's caml_major_collection_slice)
 *   full_gc()       — a whole collection: minor_collect, start_cycle, then
 *                     major_slice with an unbounded budget until idle (one
 *                     slice marks, one sweeps)
 *
 * Sweep mode (VERGC_SWEEP, read once at start-up):
 *   stw (default) — every full collection is full_gc: the cycle runs to its
 *     end at once.
 *   incremental   — a full collection finishes any cycle still running, then
 *     is minor_collect + start_cycle, and marks at once (major_slice with an
 *     unbounded budget while marking: mark slices between program steps are
 *     the incremental-mark plan's M5); the sweep then runs in slices, one after
 *     each minor collection (see incremental_slice for the budget).  Finishing
 *     a cycle (4.14's caml_finish_major_cycle) is major_slice with an unbounded
 *     budget until idle (finish_cycle_now).  A failed major allocation
 *     mid-sweep finishes the cycle and retries, then runs a full collection
 *     (and finishes it) and retries, then fails.
 *
 * The trusted obligations GC.Gen.Impl lists, and how this bridge
 * meets them (see also OCAML_INTEGRATION.md):
 *   - fresh objects are initialised before the next collector call: OCaml's
 *     caml_alloc_shr callers initialise every field (caml_initialize, or raw
 *     stores of old values) before they allocate again, as stock requires;
 *     a sweep slice never reads a field anyway;
 *   - field writes go through caml_modify / caml_initialize, whose barrier
 *     fills caml_ref_table, the remembered set handed to every minor
 *     collection;
 *   - the minor collection's arguments: the forwarding array is zeroed before
 *     every call, the remembered set is caml_ref_table (reset after every
 *     minor collection, so it never names a slot in an object that was
 *     unreachable when marking ended), its targets are added to the roots;
 *   - gc_gen_heap.phase_ref is written only by the extracted collector; this
 *     file only reads it (vergc_sweeping, vergc_allocation_color).
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
 *   pointers to minor offsets in-place.  minor_collect rewrites those
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
#include "../caml/signals.h" /* for caml_update_young_limit */
#include "../caml/address_class.h" /* for In_heap, caml_page_table_add */
#include "../caml/memprof.h" /* for caml_memprof_renew_minor_sample */
#include "../caml/gc.h"      /* for Caml_white, Caml_black */
#include "../caml/major_gc.h" /* for caml_allocated_words */

/* --- Patched externs from GC_Gen_Impl.c --- */
#include "GC_Spec_ZeroAddr.h"  /* zero_addr, heap_size_u64 */
#include "profiling_counters.h"
extern size_t queue_size_sz;

/* --- Globals --- */
/* The collector's record.  Not static: the patched caml_modify and
 * caml_initialize (runtime/memory.c) pass its address to the extracted
 * barrier directly. */
gen_heap_t          gc_gen_heap;
static uint64_t    *gc_fwd_arr;
static uint64_t    *gc_queue;         /* BFS queue for Cheney promotion (heap-allocated) */
static uint8_t     *minor_base;      /* absolute address of minor heap buffer */
static int          heap_initialized = 0;
static uint64_t    *minor_snapshot;   /* do_full_gc, stw: minor heap before full_gc */

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

/* --- Sweep mode (VERGC_SWEEP) and the incremental sweep's pacing --- */

static int        sweep_incremental = 0;    /* VERGC_SWEEP=incremental */
/* Slice budget, in words (decision D3 of the incremental-sweep plan):
 *   budget = max(VERGC_SWEEP_MIN_WORDS, VERGC_SWEEP_K * promoted + direct)
 * where `promoted` is the words the minor collection just collected (an upper
 * bound on the words it promoted) and `direct` the words allocated directly
 * in the major heap since the last slice. */
static uint64_t   sweep_min_words = 4096;  /* VERGC_SWEEP_MIN_WORDS */
static uint64_t   sweep_k = 4;             /* VERGC_SWEEP_K */
static uint64_t   sweep_direct_words = 0;  /* major-allocated words since the last slice */

/* Statistics, printed at exit with VERGC_SWEEP_STATS=1. */
static uint64_t   stat_cycles = 0;          /* full collections (full_gc, or minor_collect + start_cycle) */
static uint64_t   stat_sweeps_done = 0;     /* sweeps that reached the end of the heap */
static uint64_t   stat_slices = 0;          /* major_slice calls mid-sweep, with a budget */
static uint64_t   stat_words_swept = 0;     /* words the cursor moved over, in slices and finishes */
static uint64_t   stat_finish_full = 0;     /* cycle finished before a full collection (D4) */
static uint64_t   stat_finish_alloc = 0;    /* cycle finished on a failed major allocation */
static uint64_t   stat_finish_promote = 0;  /* cycle finished before a minor collection, for room */
static uint64_t   stat_finish_explicit = 0; /* cycle finished for Gc.full_major & co. */
static uint64_t   stat_alloc_mid_sweep = 0; /* major allocations while sweeping */

/* minor_base_addr is defined in the extracted GC_Gen_Base module.
 * We set it at runtime to the actual minor heap buffer address so that
 * the verified to_minor_offset_u64 can translate absolute→offset inline. */
extern uint64_t minor_base_addr;

/* --- Heap initialization --- */

static uint64_t env_u64(const char *name, uint64_t dflt, uint64_t min) {
    const char *v = getenv(name);
    if (v == NULL || *v == '\0') return dflt;
    char *end;
    unsigned long long x = strtoull(v, &end, 10);
    if (*end != '\0' || x < min) {
        fprintf(stderr, "verified gen GC: ignoring %s=%s (want an integer >= %llu)\n",
                name, v, (unsigned long long)min);
        return dflt;
    }
    return (uint64_t)x;
}

static void print_sweep_stats(void) {
    fprintf(stderr,
        "vergc-sweep: mode=%s cycles=%lu sweeps_done=%lu slices=%lu words_swept=%lu "
        "finish_full=%lu finish_alloc=%lu finish_promote=%lu finish_explicit=%lu "
        "alloc_mid_sweep=%lu\n",
        sweep_incremental ? "incremental" : "stw",
        (unsigned long)stat_cycles, (unsigned long)stat_sweeps_done,
        (unsigned long)stat_slices, (unsigned long)stat_words_swept,
        (unsigned long)stat_finish_full, (unsigned long)stat_finish_alloc,
        (unsigned long)stat_finish_promote, (unsigned long)stat_finish_explicit,
        (unsigned long)stat_alloc_mid_sweep);
}

/* VERGC_SWEEP=stw|incremental, read once. Anything else is stw, with one
 * warning. */
static void read_sweep_mode(void) {
    const char *mode = getenv("VERGC_SWEEP");
    if (mode != NULL && *mode != '\0') {
        if (strcmp(mode, "incremental") == 0)
            sweep_incremental = 1;
        else if (strcmp(mode, "stw") != 0)
            fprintf(stderr, "verified gen GC: unknown VERGC_SWEEP=%s, using stw "
                            "(want stw or incremental)\n", mode);
    }
    if (sweep_incremental) {
        sweep_min_words = env_u64("VERGC_SWEEP_MIN_WORDS", sweep_min_words, 1);
        sweep_k = env_u64("VERGC_SWEEP_K", sweep_k, 0);
    }
    const char *st = getenv("VERGC_SWEEP_STATS");
    if (st != NULL && *st != '\0' && strcmp(st, "0") != 0)
        atexit(print_sweep_stats);
}

static void ensure_heap(void) {
    if (heap_initialized) return;
    heap_initialized = 1;
    atexit(gc_print_profile);
    read_sweep_mode();

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

    /* phase_ref: the major collector's phase, which the verified allocator
     * reads to colour a new object (GC.Spec.Phase.allocation_color).  It
     * starts Idle (ps_kind 0).  start_cycle sets it to Sweeping and the
     * major_slice that ends the sweep sets it back to Idle; stop-the-world
     * that all happens inside full_gc, so between collections it is Idle and
     * every major allocation is white.  Only the extracted collector writes
     * it. */
    phase_state *phase_ref = (phase_state *)calloc(1, sizeof(phase_state));
    if (!phase_ref) caml_fatal_error("verified gen GC: malloc phase_ref");
    phase_ref->ps_kind = 0;  /* Idle */
    gc_gen_heap.phase_ref = phase_ref;

    /* The persistent mark state (GC.Gen.Impl.mark_state): the mark stack,
     * its overflow flag, the partly scanned object and its next field, and
     * the rescan cursor, owned by the collector from here on.  Empty (top ==
     * cap: the stack grows downward), the flag down and the positions 0, as
     * mark_state says at every phase but Marking.  start_cycle darkens the
     * roots onto it (raising the flag if they do not fit: the mark slices
     * then rescan the heap), the write barrier pushes onto it while marking,
     * and the mark slices drain it.  calloc'd, so its pages cost nothing
     * until used. */
    size_t mark_cap = major_bytes / 64;
    if (mark_cap < 4096) mark_cap = 4096;
    const char *cap_env = getenv("VERGC_MARK_STACK");   /* testing: a small stack */
    if (cap_env) {
        size_t c = (size_t)atoll(cap_env);
        if (c > 0) mark_cap = c;
    }
    uint64_t *mark_storage = (uint64_t *)calloc(mark_cap, sizeof(uint64_t));
    size_t *mark_top = (size_t *)malloc(sizeof(size_t));
    bool *mark_overflow = (bool *)calloc(1, sizeof(bool));
    uint64_t *mark_pos = (uint64_t *)calloc(3, sizeof(uint64_t));
    if (!mark_storage || !mark_top || !mark_overflow || !mark_pos)
        caml_fatal_error("verified gen GC: cannot allocate the mark stack");
    *mark_top = mark_cap;
    gc_gen_heap.mark_stack.storage = mark_storage;
    gc_gen_heap.mark_stack.top = mark_top;
    gc_gen_heap.mark_stack.cap = mark_cap;
    gc_gen_heap.mark_overflow = mark_overflow;
    gc_gen_heap.mark_cur = &mark_pos[0];
    gc_gen_heap.mark_field = &mark_pos[1];
    gc_gen_heap.mark_rescan = &mark_pos[2];
    mark_pos[1] = 1;

    /* --- Minor heap --- */
    /* Override the verified constant (2048B) with a production-sized minor heap.
     * OCaml default is 256K words = 2MB.  We match that default, overridable
     * via environment variable. */
    size_t minor_words = 256 * 1024;  /* 2 MB / 8 = 256K words (matches OCaml default) */
    const char *minor_env = getenv("MINOR_HEAP_WORDS");
    if (minor_env) {
        size_t w = (size_t)atoll(minor_env);
        if (w > 0) minor_words = w;
    }
    if (minor_words < (size_t)Max_young_wosize + 1)
        minor_words = (size_t)Max_young_wosize + 1;
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

/* --- The sweep phase (VERGC_SWEEP=incremental) --- */

/* Is the major collector mid-sweep?  phase_ref is the collector's; we only
 * read it.  ps_kind: 0 Idle, 1 Sweeping, 2 Marking (GC.Impl.Allocator.phase_of).
 * Marking is entered by start_cycle and, for now, always finished within
 * the same do_full_gc (mark_now), so between collector calls it is never
 * Marking. */
static inline int vergc_sweeping(void) {
    return gc_gen_heap.phase_ref->ps_kind == 1;
}

/* The colour the verified allocator gives a block whose header is at `hp`
 * (GC.Spec.Phase.allocation_color, as `allocate` computes it): black while
 * marking, black mid-sweep at or above the cursor, white otherwise.  caml_allocation_color
 * and the patched caml_alloc_shr_aux / caml_obj_truncate use it. */
color_t vergc_allocation_color(void *hp) {
    if (!heap_initialized) return Caml_white;
    uint64_t a = (uint64_t)(uintptr_t)hp;
    if (a < zero_addr || a >= heap_size_u64) return Caml_white;
    const phase_state *ph = gc_gen_heap.phase_ref;
    return (ph->ps_kind == 2 || (ph->ps_kind == 1 && a >= ph->ps_cursor))
           ? Caml_black : Caml_white;
}

/* The end of a sweep.  Stock counts a major collection when its cycle ends,
 * and tests wait on Gc.quick_stat's major_collections for a collection to
 * have happened, so the incremental mode counts it here rather than when the
 * cycle starts (stw counts it in do_full_gc, where the cycle also ends). */
static void sweep_ended(void) {
    stat_sweeps_done++;
    Caml_state->_stat_major_collections++;
}

/* One major slice of `budget` words.  Returns whether the collector is idle
 * again. */
static int run_major_slice(uint64_t budget) {
    if (!vergc_sweeping()) return 1;
    uint64_t c0 = gc_gen_heap.phase_ref->ps_cursor;
    PROF_START(major_gc);
    bool fin = major_slice(gc_gen_heap, budget);
    PROF_END(major_gc);
    stat_slices++;
    stat_words_swept += (gc_gen_heap.phase_ref->ps_cursor - c0) / 8;
    if (fin) sweep_ended();
    return fin;
}

/* Finish the cycle (4.14's caml_finish_major_cycle): major slices with an
 * unbounded budget until the collector is idle -- one slice, in fact.
 * `counter` records why. */
static void finish_cycle_now(uint64_t *counter) {
    if (!vergc_sweeping()) return;
    uint64_t c0 = gc_gen_heap.phase_ref->ps_cursor;
    PROF_START(major_gc);
    while (!major_slice(gc_gen_heap, UINT64_MAX)) { }
    PROF_END(major_gc);
    (*counter)++;
    stat_words_swept += (gc_gen_heap.phase_ref->ps_cursor - c0) / 8;
    sweep_ended();
}

/* The slice after a minor collection that collected `minor_words` words
 * (decision D3):
 *
 *   budget = max(VERGC_SWEEP_MIN_WORDS,
 *                VERGC_SWEEP_K * minor_words + words allocated directly in
 *                the major heap since the last slice)
 *
 * Defaults 4096 and 4.  A sweep of a heap of W words therefore finishes
 * after at most W / K promoted words, long before the next cycle starts
 * (do_minor_gc's trigger: promoted words > W / 2), so in steady state a
 * cycle's sweep is over before the next one is requested.
 *
 * Future work: port 4.14's pacing (caml_major_collection_slice, runtime/
 * major_gc.c L938-1109), which computes the work from the words allocated
 * and promoted, caml_percent_free, and smooths it over caml_major_window
 * slices with a work credit. */
static void incremental_slice(uint64_t minor_words) {
    uint64_t direct = sweep_direct_words;
    sweep_direct_words = 0;
    if (!vergc_sweeping()) return;
    uint64_t budget = minor_words;
    if (sweep_k != 0 && budget > UINT64_MAX / sweep_k) budget = UINT64_MAX;
    else budget *= sweep_k;
    budget = (budget > UINT64_MAX - direct) ? UINT64_MAX : budget + direct;
    if (budget < sweep_min_words) budget = sweep_min_words;
    run_major_slice(budget);
}

/* Mid-sweep, garbage in front of the cursor is not on the free list yet, so
 * a minor collection might find too little room to promote into -- and a
 * promotion failure is fatal.  Before a minor collection that may promote
 * `bytes`, walk the free list (stopping as soon as there is enough) and finish
 * the cycle first if it holds less than twice that.  Stop-the-world there is
 * no such check: there the free list is the whole of the free memory. */
static void ensure_room_for_promotion(uint64_t bytes) {
    if (!vergc_sweeping()) return;
    uint64_t need = 2 * (bytes / 8);
    uint64_t have = 0;
    uint64_t p = *gc_gen_heap.fp_ref;
    uint64_t fuel = (heap_size_u64 - zero_addr) / 8;
    while (p >= zero_addr + 8 && p < heap_size_u64 && p % 8 == 0 && fuel-- > 0) {
        have += Wosize_hd(*(uint64_t *)(uintptr_t)(p - 8)) + 1;
        if (have >= need) return;
        p = *(uint64_t *)(uintptr_t)p;
    }
    finish_cycle_now(&stat_finish_promote);
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
                "verified gen GC: internal error — unpromoted root after full collection");
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
void verified_do_minor_gc(void);     /* forward decl */

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

    /* 5. Minor collection via verified minor_collect, at the collector's
     * phase (mid-sweep: the cursor and the pending set are kept).
     *
     * The verified minor_collect bundles:
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
        promote_ok = minor_collect(gc_gen_heap, root_values,
                                   (size_t)root_count, gc_fwd_arr,
                                   gc_queue,
                                   (uint64_t *)tbl->base, n_slots);
    }
    PROF_END(cheney);

    /* OOM check (verified flag from cheney_promote_phase) */
    if (!promote_ok) {
        fatal_promotion_failed();
    }

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
     * Using bump_before as a conservative upper bound on promoted bytes.
     * The same rule in both modes; incremental, do_full_gc finishes any sweep
     * still running and starts a new cycle. */
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

    uint64_t bump_before = *gc_gen_heap.minor.bump_ref;
    Caml_state->_stat_minor_collections++;
    Caml_state->_stat_minor_words += (double)(bump_before / sizeof(value));

    if (sweep_incremental) ensure_room_for_promotion(bump_before);

    do_minor_gc_core();

    /* Track promoted bytes (approximate by the minor bump value) */
    bytes_promoted_since_major += bump_before;

    /* Incremental: a slice of the sweep after each minor collection. */
    if (sweep_incremental) incremental_slice(bump_before / 8);
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

/* --- The write barrier (caml_modify, caml_initialize) --- */

/* A slot of the verified major heap.  Before ensure_heap both bounds are 0,
 * so nothing is. */
static inline int vergc_in_major(const value *fp) {
    uint64_t a = (uint64_t)(uintptr_t)fp;
    return a - zero_addr < heap_size_u64 - zero_addr;
}

/* caml_modify of a slot that is not in the nursery (the caller wrote a
 * nursery slot itself: no barrier is needed there, 4.14's fast path).
 * Returns whether the caller must add fp to the ref table.
 *
 * In the verified major heap this is the extracted `modify_field`
 * (GC.Gen.Impl.Barrier): old value read, darkened while marking, new value
 * written, and "the new value is young and the old one was not".  The
 * trusted obligations: fp is a field of a live, scannable, non-closure block
 * and val is a value the program holds (GC.Gen.Barrier.modify_ok), and the
 * caller appends fp to the ref table exactly when this returns true
 * (GC.Gen.Barrier.modify_ref_table then keeps the table covering and sound).
 *
 * Elsewhere (a slot outside both heaps, e.g. native code's static data): the
 * stock logic without darkening (nothing is ever marking there: the verified
 * collector's roots cover such slots). */
int vergc_modify(value *fp, value val) {
    if (vergc_in_major(fp))
        return modify_field(&gc_gen_heap, (uint64_t)(uintptr_t)fp, (uint64_t)val);
    value old = *fp;
    *fp = val;
    return Is_block(val) && Is_young(val) && !(Is_block(old) && Is_young(old));
}

/* caml_initialize of a slot that is not in the nursery: the first value of a
 * field of a block just allocated.  Returns whether the caller must add fp
 * to the ref table: the value is young.  No darkening (the old value is
 * garbage).  In the verified major heap this is the extracted
 * `initialize_field`. */
int vergc_initialize(value *fp, value val) {
    if (vergc_in_major(fp))
        return initialize_field(&gc_gen_heap, (uint64_t)(uintptr_t)fp, (uint64_t)val);
    *fp = val;
    return Is_block(val) && Is_young(val);
}

/* --- Full GC (minor + major) --- */

static int full_gc_count = 0;

static void do_full_gc(void) {
    ensure_heap();
    in_full_gc = 1;

    /* Incremental: a full collection requested mid-sweep finishes the cycle
     * first (decision D4, as 4.14 does): start_cycle needs an idle
     * collector. */
    if (sweep_incremental) finish_cycle_now(&stat_finish_full);

    #ifdef NATIVE_CODE
        /* A full GC can be entered without passing through
        * vergc_native_run_minor_collection() */
        vergc_sync_bump_ref_from_young_ptr();
    #endif

    PROF_INC(major_gc_count);
    PROF_START(major_gc);
    if (!sweep_incremental) Caml_state->_stat_major_collections++;
    full_gc_count++;
    stat_cycles++;

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

    /* minor_collect rewrites this roots array in place, then start_cycle
     * darkens those post-minor roots onto the collector's persistent mark
     * stack (raising its overflow flag if they do not fit). */
    uint64_t *roots_for_gc =
        (uint64_t *)calloc(root_count == 0 ? 1 : root_count, sizeof(uint64_t));
    if (!roots_for_gc)
        caml_fatal_error("verified gen GC: cannot allocate root buffer");
    if (root_count > 0)
        memcpy(roots_for_gc, root_values, root_count * sizeof(uint64_t));

    /* Stop-the-world, full_gc sweeps right after promoting, and a promoted
     * copy reachable only through a dead remembered slot can be swept and
     * coalesced, so its major header cannot be read afterwards.  It also
     * zeroizes the minor heap, so keep a copy of the minor headers for
     * promoted_words.  Incremental, nothing sweeps between minor_collect and
     * the count (start_cycle only recolours headers), so the major copies'
     * headers are read, as after any minor collection. */
    if (!sweep_incremental) {
        if (minor_snapshot == NULL) {
            minor_snapshot = (uint64_t *)malloc((size_t)minor_heap_size_u64);
            if (!minor_snapshot)
                caml_fatal_error("verified gen GC: cannot allocate minor snapshot");
        }
        memcpy(minor_snapshot, minor_base, (size_t)minor_heap_size_u64);
    }

    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        size_t n_slots = (size_t)(tbl->ptr - tbl->base);
        _Static_assert(sizeof(value *) == sizeof(uint64_t),
            "ref_table optimization requires LP64 (sizeof(value*)==8)");
        bool ok;
        if (sweep_incremental) {
            /* The minor collection, then -- unless promotion ran out of
             * memory, as full_gc -- root darkening and marking; the phase
             * becomes Sweeping and the sweep runs in slices from here on. */
            ok = minor_collect(gc_gen_heap, roots_for_gc, (size_t)root_count,
                               gc_fwd_arr, gc_queue, (uint64_t *)tbl->base,
                               n_slots);
            if (ok) {
                count_promoted_words(promoted_words(NULL));
                start_cycle(gc_gen_heap, roots_for_gc, (size_t)root_count);
                /* Marking, at once for now (M5 runs mark slices between
                 * program steps): one unbounded slice finishes it. */
                while (gc_gen_heap.phase_ref->ps_kind == 2)
                    major_slice(gc_gen_heap, UINT64_MAX);
            }
        } else {
            ok = full_gc(gc_gen_heap, roots_for_gc, (size_t)root_count,
                         gc_fwd_arr, gc_queue, (uint64_t *)tbl->base, n_slots);
            if (ok) count_promoted_words(promoted_words(minor_snapshot));
        }
        if (!ok) {
            free(roots_for_gc);
            in_full_gc = 0;
            fatal_promotion_failed();
        }
    }

    PROF_START(writeback);
    write_back_forwarded_roots();
    PROF_END(writeback);

    Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
    /* The trigger counts what was promoted or allocated directly in the major
     * heap since the last cycle started.  This collection's own promotions
     * happened before its marking, so they are in the marked heap -- live
     * data of the cycle, not growth since it -- and the count restarts at
     * zero (stop-the-world the cycle has also ended: the heap is the live
     * data). */
    bytes_promoted_since_major = 0;
    sweep_direct_words = 0;

    free(roots_for_gc);
    PROF_END(major_gc);

    #ifdef NATIVE_CODE
        /* The minor collection emptied the minor heap.  Without this young_ptr keeps its
         * old value: the next collection would count those words in
         * minor_words a second time, and the space would not be reused. */
        vergc_native_reset_young_ptr();
    #endif

    in_full_gc = 0;
}

/* --- Allocation entry points --- */

void *verified_allocate_minor(mlsize_t wosize, uint8_t tag) {
    ensure_heap();

    if ((uint64_t)wosize == 0 || (uint64_t)wosize > (uint64_t)Max_young_wosize)
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

static void major_heap_exhausted_hint(void) {
    /* Keep the sizing hint, once, because our major heap does not grow and
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
}

/* The verified allocator, at the collector's phase: the free-list head and
 * the phase record (its cached swept_tail) are updated in place. */
static uint64_t allocate_timed(mlsize_t wosize, uint8_t tag) {
    PROF_START(major_alloc);
    uint64_t r = allocate(gc_gen_heap.major, gc_gen_heap.fp_ref, gc_gen_heap.phase_ref,
                          (uint64_t)wosize, (uint64_t)tag);
    PROF_END(major_alloc);
    return r;
}

/* verified_allocate, VERGC_SWEEP=incremental.  allocate allocates at the
 * collector's phase: mid-sweep a block in front of the cursor is black (the
 * sweep keeps it), one behind it white.  On failure:
 *   1. mid-sweep, finish the cycle (the garbage in front of the cursor is not
 *      on the free list yet) and retry;
 *   2. then a full collection, finished, and retry -- what stop-the-world's
 *      full_gc gives;
 *   3. then fail: Out_of_memory, as stop-the-world. */
static void *verified_allocate_incremental(mlsize_t wosize, uint8_t tag) {
    if (vergc_sweeping()) stat_alloc_mid_sweep++;
    uint64_t result = allocate_timed(wosize, tag);
    if (result == 0 && vergc_sweeping()) {
        finish_cycle_now(&stat_finish_alloc);
        result = allocate_timed(wosize, tag);
    }
    if (result == 0) {
        do_full_gc();
        finish_cycle_now(&stat_finish_alloc);
        result = allocate_timed(wosize, tag);
    }
    if (result == 0) {
        /* As stop-the-world: the heap is the one a full collection and its
         * whole sweep produced, so no free block fits. */
        major_heap_exhausted_hint();
        return NULL;
    }
    PROF_INC(major_alloc_count);
    sweep_direct_words += (uint64_t)wosize + 1;
    return (void *)(uintptr_t)(result - 8);
}

void *verified_allocate(mlsize_t wosize, uint8_t tag) {
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

    /* The verified allocator writes the object's final header: `wosize`,
     * `tag`, and the colour the collector's phase gives it -- white when
     * Idle (always, stop-the-world); mid-sweep, black in front of the cursor.
     * The patched caml_alloc_shr_aux keeps that colour and rewrites only the
     * profiling bits (WITH_PROFINFO).
     *
     * GC.Spec.Allocator's alloc_spec_preserves_wfh_part4 requires
     * `tag <> infix_tag`: an Infix header inside a free block would break the
     * heap's well-formedness. caml_alloc_shr (and every other caller of
     * caml_alloc_shr_aux) is never called with Infix_tag -- infix headers are
     * only ever written inside a Closure_tag block -- so assert it. */
    CAMLassert(tag != Infix_tag);

    /* Proactive full GC, on the same 50% threshold as do_minor_gc(), in both
     * modes.  Direct major allocations count toward bytes_promoted_since_major
     * (below), so a heap filled by large blocks that are then dropped still
     * triggers a full collection before the next minor collection has to
     * promote into it (issue #34).  Incremental, do_full_gc finishes any
     * sweep still running and starts a new cycle, as from do_minor_gc. */
    uint64_t alloc_bytes = ((uint64_t)wosize + 1) * 8;
    if (!in_full_gc) {
        uint64_t major_size = heap_size_u64 - zero_addr;
        if (bytes_promoted_since_major + alloc_bytes > major_size / 2)
            do_full_gc();
    }

    if (sweep_incremental) {
        /* sweep_direct_words (the sweep's budget) counts it as well. */
        void *hp = verified_allocate_incremental(wosize, tag);
        if (hp != NULL) bytes_promoted_since_major += alloc_bytes;
        return hp;
    }
    uint64_t result = allocate_timed(wosize, tag);

    if (result == 0) {
        do_full_gc();
        result = allocate_timed(wosize, tag);
    }

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
         * killed instead of its handler run. */
        major_heap_exhausted_hint();
        return NULL;
    }

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

/* --- Stock's major-GC entry points (runtime/major_gc.c, gc_ctrl.c) --- */

/* caml_major_collection_slice: Gc.major_slice.  Incremental and mid-sweep, a
 * major_slice of `howmuch` words when positive (stock: "enough work to free n
 * words"), else the default budget; nothing otherwise -- a cycle starts only
 * from do_full_gc. */
void verified_major_collection_slice(intnat howmuch) {
    ensure_heap();
    if (!sweep_incremental || !vergc_sweeping()) return;
    uint64_t budget = howmuch > 0 ? (uint64_t)howmuch : sweep_direct_words;
    sweep_direct_words = 0;
    if (budget < sweep_min_words) budget = sweep_min_words;
    run_major_slice(budget);
}

/* Gc.major, Gc.full_major and Gc.compact (runtime/gc_ctrl.c), in place of the
 * stock major cycle and compaction, and caml_finish_major_cycle (Gc.set's
 * policy change).  A whole collection: the nursery emptied, then a full
 * collection of both generations, and (incremental) its whole sweep, so that
 * the program observes a finished cycle as it does on stock -- one major
 * collection counted. */
void verified_do_full_gc(void) {
    ensure_heap();
    verified_do_minor_gc();
    do_full_gc();
    if (sweep_incremental) finish_cycle_now(&stat_finish_explicit);
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