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
 *                     at any phase
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
 * Major mode (VERGC_MAJOR, read once at start-up; VERGC_SWEEP is an alias,
 * VERGC_MAJOR wins when both are set):
 *   stw (default) — every major collection is full_gc: the cycle runs to its
 *     end at once, triggered when the words promoted or allocated directly in
 *     the major heap since the last one exceed half the heap.
 *   incremental   — 4.14's rhythm: the cycle runs in slices, marking and then
 *     sweeping, with the program running in between.  After every minor
 *     collection: at Idle, start_cycle when the trigger fires (the nursery is
 *     empty there, as start_cycle needs); otherwise one major_slice, whose
 *     budget the pacing computes (see "Pacing" below).  The trigger matters
 *     only at Idle: mid-cycle, memory pressure makes the slices bigger, it
 *     never finishes the cycle.  Finishing a cycle (4.14's
 *     caml_finish_major_cycle: major_slice with an unbounded budget until
 *     idle, finish_cycle_now) happens only where the program needs a
 *     finished cycle or memory now: a full collection (Gc.full_major & co.,
 *     the second step of the allocation failure ladder), a failed major
 *     allocation mid-cycle (finish, retry; then a full collection, retry;
 *     then Out_of_memory), and a minor collection mid-cycle that might not
 *     find room to promote into.
 *
 * The trusted obligations GC.Gen.Impl lists, and how this bridge
 * meets them (see also OCAML_INTEGRATION.md):
 *   - fresh objects are initialised before the next collector call: OCaml's
 *     caml_alloc_shr callers initialise every field (caml_initialize, or raw
 *     stores of values the program holds) before they allocate again, as
 *     stock requires.  While marking the block is black (the allocation
 *     colour), and its fields are only bound once initialised
 *     (GC.Gen.MarkPhase.Alloc);
 *   - field writes go through caml_modify / caml_initialize, whose barrier
 *     fills caml_ref_table, the remembered set handed to every minor
 *     collection, and darkens the old value while marking;
 *   - the minor collection's arguments: the forwarding array is zeroed before
 *     every call, the remembered set is caml_ref_table (reset after every
 *     minor collection, so it never names a slot in an object that was
 *     unreachable when marking ended), its targets are added to the roots;
 *   - while marking, every white object the program holds is one the marker
 *     will reach: the roots are darkened at once by start_cycle, and the
 *     program only obtains values by allocating (black) or loading fields of
 *     what it holds (OCaml's type safety, as 4.14 relies on);
 *   - gc_gen_heap.phase_ref is written only by the extracted collector; this
 *     file only reads it (vergc_phase, vergc_allocation_color).
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
#include <time.h>

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
#include "../caml/major_gc.h" /* for caml_allocated_words, caml_major_window */

/* 4.14's pacing parameters, which Gc.set and OCAMLRUNPARAM set as usual:
 * caml_percent_free (space_overhead, `o`) and caml_major_window (`w`). */
extern uintnat caml_percent_free;

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

/* stw: bytes promoted or allocated directly in the major heap
 * (verified_allocate) since the last major collection.  When this approaches
 * half the major heap, a full collection runs, so that promotion never finds
 * the heap full. */
static uint64_t   bytes_promoted_since_major = 0;
static int        in_full_gc = 0;  /* re-entrancy guard */

/* The mark counter: the words the mark slices blackened since start_cycle
 * (GC.Gen.Impl.gen_heap_t.mark_words; start_cycle zeroes it).  Read when
 * marking ends, for the statistics and the live-words estimate. */
static uint64_t *mark_words_ref;
#define VERGC_SET_MARK_WORDS(p) (mark_words_ref = (p), gc_gen_heap.mark_words = (p))

/* --- Major mode (VERGC_MAJOR), pacing and statistics --- */

static int        major_incremental = 0;    /* VERGC_MAJOR=incremental */

/* Pacing knobs (incremental mode; see "Pacing" below):
 *   VERGC_SLICE_WORDS      — a fixed budget for every automatic slice, in
 *                            place of the computed one (testing: tiny slices).
 *                            0 (default): computed.
 *   VERGC_SLICE_MIN_WORDS  — the least budget of an automatic slice (default
 *                            4096); VERGC_SWEEP_MIN_WORDS is an alias.
 *   VERGC_TRIGGER_MIN_WORDS — the least allocation between two cycles
 *                            (default: an eighth of the heap). */
static uint64_t   slice_words_fixed = 0;
static uint64_t   slice_min_words = 4096;
static uint64_t   trigger_min_words = 0;    /* set in ensure_heap */

/* Statistics, printed at exit with VERGC_MAJOR_STATS=1 (alias
 * VERGC_SWEEP_STATS). */
static int        stats_enabled = 0;
static uint64_t   stat_cycles = 0;          /* major cycles started (start_cycle or full_gc) */
static uint64_t   stat_cycles_done = 0;     /* cycles whose sweep reached the end of the heap */
static uint64_t   stat_mark_slices = 0;     /* budgeted major_slice calls that started marking */
static uint64_t   stat_sweep_slices = 0;    /* budgeted major_slice calls that started sweeping */
static uint64_t   stat_marks_spanned = 0;   /* cycles whose marking took more than one slice */
static uint64_t   stat_words_marked = 0;    /* words blackened by the mark slices (the mark counter) */
static uint64_t   stat_words_swept = 0;     /* words the sweep cursor moved over, in slices and finishes */
/* Finishing a cycle early (incremental): a cycle in progress run to its end
 * at once, by reason. */
static uint64_t   stat_finish_full = 0;     /* before a full collection */
static uint64_t   stat_finish_alloc = 0;    /* on a failed major allocation */
static uint64_t   stat_finish_promote = 0;  /* before a minor collection, for room to promote */
static uint64_t   stat_finish_mid_mark = 0; /* of those, finishes that started while marking */
/* Whole collections (stw: every major collection), by reason. */
static uint64_t   stat_full_explicit = 0;   /* Gc.full_major, Gc.major, Gc.compact, policy change */
static uint64_t   stat_full_alloc = 0;      /* a failed major allocation (after finishing) */
static uint64_t   stat_full_other = 0;      /* the stw trigger, caml_trigger_verified_gc */
static uint64_t   stat_trigger_overhead = 0;/* cycles started by the space_overhead trigger */
static uint64_t   stat_trigger_heap = 0;    /* cycles started by the heap-fraction safety net */
static uint64_t   stat_trigger_clock = 0;   /* cycles started by the minor-allocation clock */
static uint64_t   stat_trigger_explicit = 0;/* cycles started by Gc.major_slice at Idle */
static uint64_t   stat_minor_mid_mark = 0;  /* minor collections while marking */
static uint64_t   stat_alloc_mid_mark = 0;  /* major allocations while marking */
static uint64_t   stat_alloc_mid_sweep = 0; /* major allocations while sweeping */
static uint64_t   stat_modify_mid_mark = 0; /* barrier calls on major slots while marking */
static uint64_t   stat_barrier_darken = 0;  /* of those, the ones that pushed or raised the overflow flag */
static uint64_t   stat_overflows = 0;       /* times the overflow flag was found newly raised */
static uint64_t   stat_rescans = 0;         /* rescans of the heap started by the mark slices */

/* Pause times (CLOCK_MONOTONIC, measured only with statistics on). */
typedef struct { uint64_t n, total_ns, max_ns; } pause_stat;
static pause_stat pause_minor, pause_start, pause_mark, pause_sweep, pause_finish, pause_full;

static inline uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

static inline void pause_add(pause_stat *p, uint64_t ns) {
    p->n++;
    p->total_ns += ns;
    if (ns > p->max_ns) p->max_ns = ns;
}

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

static void print_pause(const char *name, const pause_stat *p) {
    fprintf(stderr, " %s=%lu/%.1f/%.1f", name, (unsigned long)p->n,
            p->n ? (double)p->total_ns / (double)p->n / 1000.0 : 0.0,
            (double)p->max_ns / 1000.0);
}

static void print_major_stats(void) {
    fprintf(stderr,
        "vergc-major: mode=%s cycles=%lu cycles_done=%lu mark_slices=%lu "
        "sweep_slices=%lu marks_spanned=%lu words_marked=%lu words_swept=%lu "
        "finish_full=%lu finish_alloc=%lu finish_promote=%lu finish_mid_mark=%lu "
        "full_explicit=%lu full_alloc=%lu full_other=%lu trigger_overhead=%lu trigger_heap=%lu "
        "trigger_clock=%lu trigger_explicit=%lu minor_mid_mark=%lu alloc_mid_mark=%lu "
        "alloc_mid_sweep=%lu modify_mid_mark=%lu barrier_darken=%lu "
        "overflows=%lu rescans=%lu\n",
        major_incremental ? "incremental" : "stw",
        (unsigned long)stat_cycles, (unsigned long)stat_cycles_done,
        (unsigned long)stat_mark_slices, (unsigned long)stat_sweep_slices,
        (unsigned long)stat_marks_spanned,
        (unsigned long)stat_words_marked, (unsigned long)stat_words_swept,
        (unsigned long)stat_finish_full, (unsigned long)stat_finish_alloc,
        (unsigned long)stat_finish_promote, (unsigned long)stat_finish_mid_mark,
        (unsigned long)stat_full_explicit, (unsigned long)stat_full_alloc,
        (unsigned long)stat_full_other,
        (unsigned long)stat_trigger_overhead, (unsigned long)stat_trigger_heap,
        (unsigned long)stat_trigger_clock, (unsigned long)stat_trigger_explicit,
        (unsigned long)stat_minor_mid_mark, (unsigned long)stat_alloc_mid_mark,
        (unsigned long)stat_alloc_mid_sweep, (unsigned long)stat_modify_mid_mark,
        (unsigned long)stat_barrier_darken,
        (unsigned long)stat_overflows, (unsigned long)stat_rescans);
    /* Pauses: count/mean/max, in microseconds. */
    fprintf(stderr, "vergc-pauses:");
    print_pause("minor", &pause_minor);
    print_pause("start", &pause_start);
    print_pause("mark", &pause_mark);
    print_pause("sweep", &pause_sweep);
    print_pause("finish", &pause_finish);
    print_pause("full", &pause_full);
    fprintf(stderr, "\n");
}

/* Is the environment variable set to something other than "" or "0"? */
static int env_flag(const char *name) {
    const char *v = getenv(name);
    return v != NULL && *v != '\0' && strcmp(v, "0") != 0;
}

/* VERGC_MAJOR=stw|incremental, read once; VERGC_SWEEP is an alias (the
 * incremental sweep of M2 grew into the incremental major collector), and
 * VERGC_MAJOR wins when both are set.  Anything else is stw, with one
 * warning. */
static void read_major_mode(void) {
    const char *var = "VERGC_MAJOR";
    const char *mode = getenv(var);
    if (mode == NULL || *mode == '\0') { var = "VERGC_SWEEP"; mode = getenv(var); }
    if (mode != NULL && *mode != '\0') {
        if (strcmp(mode, "incremental") == 0)
            major_incremental = 1;
        else if (strcmp(mode, "stw") != 0)
            fprintf(stderr, "verified gen GC: unknown %s=%s, using stw "
                            "(want stw or incremental)\n", var, mode);
    }
    if (major_incremental) {
        slice_words_fixed = env_u64("VERGC_SLICE_WORDS", 0, 0);
        slice_min_words = env_u64("VERGC_SWEEP_MIN_WORDS", slice_min_words, 1);
        slice_min_words = env_u64("VERGC_SLICE_MIN_WORDS", slice_min_words, 1);
    }
    stats_enabled = env_flag("VERGC_MAJOR_STATS") || env_flag("VERGC_SWEEP_STATS");
    if (stats_enabled) atexit(print_major_stats);
}

static void ensure_heap(void) {
    if (heap_initialized) return;
    heap_initialized = 1;
    atexit(gc_print_profile);
    read_major_mode();

    /* --- Major heap --- */
    size_t major_words = 32 * 1024 * 1024;  /* 256 MB / 8 = 32M words */
    const char *env = getenv("MIN_EXPANSION_WORDSIZE");
    if (env) {
        size_t w = (size_t)atoll(env);
        if (w > 0) major_words = w;
    }
    size_t major_bytes = major_words * 8;
    trigger_min_words = env_u64("VERGC_TRIGGER_MIN_WORDS", (uint64_t)major_words / 8, 0);

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
     * starts Idle (ps_kind 0).  start_cycle sets it to Marking, the mark
     * slice that finds nothing grey to Sweeping, and the sweep slice that
     * ends the sweep back to Idle; stop-the-world all of that happens inside
     * full_gc, so between collections it is Idle.  Only the extracted
     * collector writes it. */
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
    uint64_t *mark_pos = (uint64_t *)calloc(4, sizeof(uint64_t));
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
    VERGC_SET_MARK_WORDS(&mark_pos[3]);

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

/* --- The collector's phase --- */

/* phase_ref is the collector's; we only read it.  ps_kind: 0 Idle,
 * 1 Sweeping, 2 Marking (GC.Impl.Allocator.phase_of). */
static inline int vergc_idle(void)     { return gc_gen_heap.phase_ref->ps_kind == 0; }
static inline int vergc_sweeping(void) { return gc_gen_heap.phase_ref->ps_kind == 1; }
static inline int vergc_marking(void)  { return gc_gen_heap.phase_ref->ps_kind == 2; }

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


static inline uint64_t mark_stack_len(void) {
    return (uint64_t)(gc_gen_heap.mark_stack.cap - *gc_gen_heap.mark_stack.top);
}

/* --- Accounting: allocation, occupancy, the trigger (incremental) --- */
/*
 * All in words (headers included).  `allocated` is what goes into the major
 * heap -- promoted copies and direct major allocations (caml_alloc_shr) --
 * the analogue of 4.14's caml_allocated_words.
 *
 *   pace_words   allocated since the last slice (the slice's work, below);
 *   since_end    allocated since the last cycle ended (or start-up);
 *   in_cycle     allocated since the current cycle started;
 *   occ_end      the words in use when the last cycle ended, estimated as
 *                the words the cycle marked plus the words allocated during
 *                it (black, or white behind the sweep cursor: both survive
 *                its sweep).  An upper bound on what was not free then:
 *                every block that survives a sweep was marked or allocated
 *                during the cycle.
 *
 * So `occ_end + since_end` bounds the words in use now from above, and the
 * heap minus that bounds the free words from below.
 */
static uint64_t   pace_words = 0;
static uint64_t   since_end = 0;
static uint64_t   in_cycle = 0;
static uint64_t   minor_since_end = 0;  /* words allocated in the nursery since the last cycle ended */
static uint64_t   occ_end = 0;
static uint64_t   cycle_marked = 0;     /* words marked by this cycle (0 until marking ends) */
static int        cycle_mark_slices = 0;/* mark slices of this cycle */

static inline uint64_t heap_words(void) { return (heap_size_u64 - zero_addr) / 8; }

/* The words in use now, estimated from above (since_end keeps counting
 * through a cycle: what the cycle frees is not known until it ends). */
static inline uint64_t occupancy_now(void) { return occ_end + since_end; }

static inline void account_alloc(uint64_t words) {
    pace_words += words;
    since_end += words;
    in_cycle += words;
}

/* The trigger, at Idle only (incremental mode never starts a cycle mid-cycle):
 * 4.14's space_overhead -- start a cycle once the words allocated since the
 * last one ended exceed `caml_percent_free` percent of the words in use then
 * (at least VERGC_TRIGGER_MIN_WORDS) -- and, as a safety net for a heap of
 * fixed size, once the words in use (estimated, from above) exceed half the
 * heap: a cycle needs free memory to run in, about 2/3 of what is free when
 * it starts (see the pacing).  `extra` is a direct allocation about to be
 * made.  A third, slow clock stands in for 4.14's back-to-back cycles: a
 * cycle also starts once the nursery has allocated as many words as the
 * major heap has since the last one ended, so that a program whose garbage
 * all dies young still sees major cycles (and Gc.quick_stat's count move),
 * if rarely.  Returns 0 (no), 1 (space_overhead), 2 (safety net) or 3
 * (clock). */
static int cycle_trigger(uint64_t extra) {
    uint64_t pf = caml_percent_free == 0 ? 1 : caml_percent_free;
    uint64_t a = since_end + extra;
    uint64_t target = occ_end / 100 * pf + (occ_end % 100) * pf / 100;
    if (target < trigger_min_words) target = trigger_min_words;
    if (a >= target) return 1;
    if (occ_end + a >= heap_words() / 2) return 2;
    if (minor_since_end >= heap_words()) return 3;
    return 0;
}

/* --- Pacing (incremental): 4.14's caml_major_collection_slice --- */
/*
 * runtime/major_gc.c (4.14) computes, at each slice, the fraction P of the
 * cycle's work to do from the words allocated since the last slice:
 *
 *   FM = free memory at the start of the cycle
 *   G  = 2 * FM / 3                 (what the cycle may allocate)
 *   P  = allocated / G              (capped at 0.3 per slice; the rest is a
 *                                    backlog carried to the next slice)
 *   mark slice:  P * MW / 0.4 words (40% of the cycle marks MW words)
 *   sweep slice: P * SW / 0.6 words (60% of it sweeps SW words)
 *
 * smoothed over caml_major_window slices (a ring of buckets advanced by the
 * minor collections' clock), with a work credit for forced slices
 * (Gc.major_slice).  4.14 takes FM = heap * pf / (100 + pf) (pf =
 * caml_percent_free), MW = heap * 100 / (100 + pf) and SW = heap, its heap
 * growing to keep that so.  Ours is a fixed heap, so FM is also bounded by
 * what is free (from above: heap - words in use, estimated from above, at
 * least heap / 64), and MW is the words in use when the cycle started (all
 * marking can scan, in mark-budget words).  The cycle then ends after about
 * G words are allocated, whatever the heap's size.
 */
#define VERGC_MAX_WINDOW 50
static double     ring[VERGC_MAX_WINDOW];
static int        ring_window = 1;
static int        ring_index = 0;
static double     gc_clock = 0.0;
static double     work_credit = 0.0;
static double     p_backlog = 0.0;
static double     cycle_fm = 1.0;       /* FM, for the current cycle */
static double     cycle_mw = 1.0;       /* MW, for the current cycle */

/* caml_major_window as Gc.set left it, the ring spread over it when it
 * changed (4.14's caml_set_major_window). */
static void sync_window(void) {
    int w = caml_major_window;
    if (w < 1) w = 1;
    if (w > VERGC_MAX_WINDOW) w = VERGC_MAX_WINDOW;
    if (w == ring_window) return;
    double total = 0.0;
    for (int i = 0; i < ring_window; i++) total += ring[i];
    for (int i = 0; i < w; i++) ring[i] = total / w;
    ring_window = w;
    ring_index = 0;
}

/* The fraction of the cycle's work that `words` allocated words call for. */
static inline double work_fraction(double words) {
    return words * 3.0 / 2.0 / cycle_fm;
}

/* Fix the cycle's estimates when it starts: FM and MW (above). */
static void cycle_estimates(void) {
    double h = (double)heap_words();
    double pf = caml_percent_free == 0 ? 1.0 : (double)caml_percent_free;
    double in_use = (double)occupancy_now();
    double fm = h * pf / (100.0 + pf);
    double free_lb = h - in_use;
    if (free_lb < h / 64.0) free_lb = h / 64.0;
    if (fm > free_lb) fm = free_lb;
    cycle_fm = fm < 1.0 ? 1.0 : fm;
    cycle_mw = in_use < 1.0 ? 1.0 : in_use;
}

/* The words of work for a slice whose share of the cycle is `p`. */
static uint64_t slice_budget(double p) {
    double w = vergc_marking() ? p * cycle_mw / 0.4 : p * (double)heap_words() / 0.6;
    if (slice_words_fixed != 0) return slice_words_fixed;
    if (w < (double)slice_min_words) return slice_min_words;
    if (w >= 1.8e19) return UINT64_MAX - 1;
    return (uint64_t)w;
}

static void cycle_ended(void);

/* One major slice (budget UINT64_MAX: unbounded, a finish).  Returns whether
 * the collector is idle afterwards. */
static int ov_seen = 0;   /* the overflow flag as last seen */

static int run_major_slice(uint64_t budget) {
    if (vergc_idle()) return 1;
    int was_marking = vergc_marking();
    int budgeted = budget != UINT64_MAX;
    uint64_t c0 = gc_gen_heap.phase_ref->ps_cursor;
    int ov0 = *gc_gen_heap.mark_overflow;
    if (ov0 && !ov_seen) stat_overflows++;
    uint64_t r0 = *gc_gen_heap.mark_rescan;
    uint64_t t0 = stats_enabled ? now_ns() : 0;
    PROF_START(major_gc);
    bool fin = major_slice(gc_gen_heap, budget);
    PROF_END(major_gc);
    if (stats_enabled) pause_add(was_marking ? &pause_mark : &pause_sweep, now_ns() - t0);
    ov_seen = *gc_gen_heap.mark_overflow;
    if (was_marking) {
        if (budgeted) stat_mark_slices++;
        cycle_mark_slices++;
        if (ov0 && !*gc_gen_heap.mark_overflow) stat_rescans++;
        else if (r0 == 0 && *gc_gen_heap.mark_rescan != 0) stat_rescans++;
        if (!vergc_marking()) {
            /* Marking ended in this slice: the sweep starts at the first block. */
            cycle_marked = *mark_words_ref;
            stat_words_marked += cycle_marked;
            if (cycle_mark_slices > 1) stat_marks_spanned++;
            c0 = zero_addr;
        }
    } else if (budgeted) {
        stat_sweep_slices++;
    }
    if (vergc_sweeping() || fin)
        stat_words_swept += ((fin ? heap_size_u64 : gc_gen_heap.phase_ref->ps_cursor) - c0) / 8;
    if (fin) cycle_ended();
    return fin;
}

/* An automatic slice (4.14's caml_major_collection_slice with howmuch = -1)
 * or a forced one (howmuch = 0: the size of the next bucket; howmuch > 0:
 * the work to free about howmuch words), not idle. */
static void paced_slice(intnat howmuch) {
    sync_window();
    double p = work_fraction((double)pace_words);
    if (p < caml_extra_heap_resources) p = caml_extra_heap_resources;
    p += p_backlog;
    p_backlog = 0.0;
    if (p > 0.3) { p_backlog = p - 0.3; p = 0.3; }
    for (int i = 0; i < ring_window; i++) ring[i] += p / ring_window;

    double filt_p;
    if (gc_clock >= 1.0) {
        gc_clock -= 1.0;
        if (++ring_index >= ring_window) ring_index = 0;
    }
    if (howmuch == -1) {
        double spend = work_credit < ring[ring_index] ? work_credit : ring[ring_index];
        work_credit -= spend;
        filt_p = ring[ring_index] - spend;
        ring[ring_index] = 0.0;
    } else {
        if (howmuch == 0) {
            int i = ring_index + 1;
            if (i >= ring_window) i = 0;
            filt_p = ring[i];
        } else {
            filt_p = work_fraction((double)howmuch);
        }
        work_credit += filt_p;
        if (work_credit > 1.0) work_credit = 1.0;
    }
    pace_words = 0;
    caml_extra_heap_resources = 0.0;
    run_major_slice(slice_budget(filt_p));
}

/* The end of a cycle (the sweep reached the end of the heap).  Stock counts a
 * major collection when its cycle ends, and tests wait on Gc.quick_stat's
 * major_collections for a collection to have happened, so the incremental
 * mode counts it here rather than when the cycle starts (stw counts it in
 * do_full_gc, where the cycle also ends). */
static void cycle_ended(void) {
    stat_cycles_done++;
    Caml_state->_stat_major_collections++;
    occ_end = cycle_marked + in_cycle;
    since_end = 0;
    minor_since_end = 0;
    in_cycle = 0;
    cycle_marked = 0;
}

/* Finish the cycle (4.14's caml_finish_major_cycle): major slices with an
 * unbounded budget until the collector is idle -- one to finish marking, one
 * to sweep.  `counter`, if any, records why a cycle in progress is cut short
 * (none: the cycle a full collection has just started). */
static void finish_cycle_now(uint64_t *counter) {
    if (vergc_idle()) return;
    if (counter != NULL) {
        (*counter)++;
        if (vergc_marking()) stat_finish_mid_mark++;
    }
    uint64_t t0 = stats_enabled ? now_ns() : 0;
    int saved = stats_enabled;
    stats_enabled = 0;   /* time the finish as a whole */
    while (!run_major_slice(UINT64_MAX)) { }
    stats_enabled = saved;
    if (stats_enabled && counter != NULL) pause_add(&pause_finish, now_ns() - t0);
}

/* Mid-cycle, garbage is not on the free list until the sweep reaches it, so
 * a minor collection might find too little room to promote into -- and a
 * promotion failure is fatal.  Before a minor collection that may promote
 * `bytes`, mid-cycle: if the heap minus the words in use (estimated from
 * above) leaves room for twice that, go on; otherwise walk the free list
 * (stopping as soon as there is enough) and finish the cycle -- marking and
 * the sweep: finishing only the marking frees nothing -- if it holds less.
 * At Idle the free list is the whole of the free memory, and the trigger has
 * kept the heap at most about half full. */
static void ensure_room_for_promotion(uint64_t bytes) {
    if (vergc_idle()) return;
    uint64_t need = 2 * (bytes / 8);
    uint64_t in_use = occupancy_now();
    if (in_use < heap_words() && heap_words() - in_use >= need) return;
    uint64_t have = 0;
    uint64_t p = *gc_gen_heap.fp_ref;
    uint64_t fuel = heap_words();
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

static void do_full_gc(uint64_t *reason);   /* forward decl */
#ifdef NATIVE_CODE
static void vergc_sync_bump_ref_from_young_ptr(void);
static void vergc_native_reset_young_ptr(void);
#endif
void verified_do_minor_gc(void);     /* forward decl */

/* Core minor GC implementation, at the collector's phase.  Leaves the
 * rewritten roots in root_values (so start_cycle can darken them right
 * after) and returns the words promoted.  A promotion failure is fatal. */
static uint64_t do_minor_gc_core(void) {

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
     * phase (mid-sweep: the cursor and the pending set are kept; while
     * marking: promoted copies are black, the grey objects kept).
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
    uint64_t promoted = promoted_words(NULL);
    count_promoted_words(promoted);

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
    return promoted;
}

/* Start a major cycle (incremental), right after do_minor_gc_core: Idle, the
 * nursery empty, and root_values the roots it rewrote (the program's roots
 * and the remembered slots' targets, which are promoted copies: darkening
 * them as well only keeps them a cycle longer).  start_cycle darkens them
 * onto the persistent mark stack and the phase becomes Marking (4.14's
 * start_cycle, called from the slice after a minor collection). */
static void start_major_cycle(void) {
    uint64_t t0 = stats_enabled ? now_ns() : 0;
    PROF_START(major_gc);
    start_cycle(gc_gen_heap, root_values, (size_t)root_count);
    PROF_END(major_gc);
    if (stats_enabled) pause_add(&pause_start, now_ns() - t0);
    stat_cycles++;
    cycle_mark_slices = 0;
    cycle_marked = 0;
    in_cycle = 0;
    cycle_estimates();
    /* What was allocated while idle is not this cycle's work: 4.14 zeroes
     * caml_allocated_words at every slice, the one that starts the cycle
     * included. */
    pace_words = 0;
    caml_extra_heap_resources = 0.0;
    if (*gc_gen_heap.mark_overflow && !ov_seen) { stat_overflows++; ov_seen = 1; }
}

/* A minor collection, then the start of a cycle (incremental, Idle): what a
 * trigger outside a minor collection does (a direct major allocation,
 * Gc.major_slice at Idle, a full collection).  The minor collection runs even
 * when the nursery is empty: it gathers the roots start_cycle darkens. */
static void begin_cycle_now(void) {
    ensure_heap();
    in_full_gc = 1;
#ifdef NATIVE_CODE
    vergc_sync_bump_ref_from_young_ptr();
#endif
    uint64_t bump = *gc_gen_heap.minor.bump_ref;
    if (bump != 0) {
        Caml_state->_stat_minor_collections++;
        Caml_state->_stat_minor_words += (double)(bump / sizeof(value));
    }
    uint64_t t0 = stats_enabled ? now_ns() : 0;
    uint64_t promoted = do_minor_gc_core();
    if (stats_enabled) pause_add(&pause_minor, now_ns() - t0);
    account_alloc(promoted);
    minor_since_end += bump / 8;
    gc_clock += (double)bump / (double)minor_heap_size_u64;
    start_major_cycle();
#ifdef NATIVE_CODE
    vergc_native_reset_young_ptr();
#endif
    in_full_gc = 0;
}

static void do_minor_gc(void) {
    ensure_heap();
    if (*gc_gen_heap.minor.bump_ref == 0) return;  /* nothing to collect */

    /* stw: a full GC before the minor collection when the words promoted or
     * allocated directly since the last one exceed half the heap (bump_before
     * a conservative upper bound on what this one promotes), so that the
     * heap never fills with garbage a promotion then fails on. */
    if (!major_incremental && !in_full_gc) {
        uint64_t bump = *gc_gen_heap.minor.bump_ref;
        uint64_t major_size = heap_size_u64 - zero_addr;
        uint64_t threshold = major_size / 2;
        if (bytes_promoted_since_major + bump > threshold) {
            do_full_gc(&stat_full_other);
            if (*gc_gen_heap.minor.bump_ref == 0) return;
        }
    }

    uint64_t bump_before = *gc_gen_heap.minor.bump_ref;
    Caml_state->_stat_minor_collections++;
    Caml_state->_stat_minor_words += (double)(bump_before / sizeof(value));

    if (!major_incremental) {
        uint64_t t0 = stats_enabled ? now_ns() : 0;
        do_minor_gc_core();
        if (stats_enabled) pause_add(&pause_minor, now_ns() - t0);
        /* Track promoted bytes (approximate by the minor bump value) */
        bytes_promoted_since_major += bump_before;
        return;
    }

    /* Incremental: 4.14's rhythm.  The minor collection runs at the phase
     * (mid-cycle, possibly after finishing the cycle for room); then, at
     * Idle, the trigger may start a cycle -- the nursery is empty now, as
     * start_cycle needs -- and otherwise a slice runs, marking or sweeping. */
    if (vergc_marking()) stat_minor_mid_mark++;
    ensure_room_for_promotion(bump_before);
    uint64_t t0 = stats_enabled ? now_ns() : 0;
    uint64_t promoted = do_minor_gc_core();
    if (stats_enabled) pause_add(&pause_minor, now_ns() - t0);
    account_alloc(promoted);
    minor_since_end += bump_before / 8;
    gc_clock += (double)bump_before / (double)minor_heap_size_u64;
    if (in_full_gc) return;
    if (vergc_idle()) {
        int why = cycle_trigger(0);
        if (why != 0) {
            if (why == 1) stat_trigger_overhead++;
            else if (why == 2) stat_trigger_heap++;
            else stat_trigger_clock++;
            start_major_cycle();
        }
    } else {
        paced_slice(-1);
    }
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
 * stock logic without darkening.  Such a slot is a root (module blocks'
 * fields are among the roots start_cycle darkens), and overwriting a root
 * needs no darkening: what it held was darkened when the cycle started.
 *
 * With statistics on, a barrier call while marking is counted, and so is a
 * darkening (the mark stack grew, or the overflow flag went up). */
static int vergc_modify_counted(value *fp, value val) {
    if (!vergc_marking())
        return modify_field(&gc_gen_heap, (uint64_t)(uintptr_t)fp, (uint64_t)val);
    stat_modify_mid_mark++;
    uint64_t n0 = mark_stack_len();
    int ov0 = *gc_gen_heap.mark_overflow;
    int r = modify_field(&gc_gen_heap, (uint64_t)(uintptr_t)fp, (uint64_t)val);
    if (mark_stack_len() > n0 || (!ov0 && *gc_gen_heap.mark_overflow)) stat_barrier_darken++;
    return r;
}

int vergc_modify(value *fp, value val) {
    if (vergc_in_major(fp)) {
        if (__builtin_expect(stats_enabled, 0)) return vergc_modify_counted(fp, val);
        return modify_field(&gc_gen_heap, (uint64_t)(uintptr_t)fp, (uint64_t)val);
    }
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

/* stw: full_gc, a whole collection of both generations. */
static void do_full_gc_stw(void) {
    in_full_gc = 1;
    uint64_t t0 = stats_enabled ? now_ns() : 0;

    #ifdef NATIVE_CODE
        /* A full GC can be entered without passing through
        * vergc_native_run_minor_collection() */
        vergc_sync_bump_ref_from_young_ptr();
    #endif

    PROF_INC(major_gc_count);
    PROF_START(major_gc);
    Caml_state->_stat_major_collections++;
    full_gc_count++;
    stat_cycles++;
    stat_cycles_done++;

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

    /* full_gc's minor collection rewrites this roots array in place, then
     * start_cycle darkens those post-minor roots onto the collector's
     * persistent mark stack (raising its overflow flag if they do not fit). */
    uint64_t *roots_for_gc =
        (uint64_t *)calloc(root_count == 0 ? 1 : root_count, sizeof(uint64_t));
    if (!roots_for_gc)
        caml_fatal_error("verified gen GC: cannot allocate root buffer");
    if (root_count > 0)
        memcpy(roots_for_gc, root_values, root_count * sizeof(uint64_t));

    /* full_gc sweeps right after promoting, and a promoted copy reachable only
     * through a dead remembered slot can be swept and coalesced, so its major
     * header cannot be read afterwards.  It also zeroizes the minor heap, so
     * keep a copy of the minor headers for promoted_words. */
    if (minor_snapshot == NULL) {
        minor_snapshot = (uint64_t *)malloc((size_t)minor_heap_size_u64);
        if (!minor_snapshot)
            caml_fatal_error("verified gen GC: cannot allocate minor snapshot");
    }
    memcpy(minor_snapshot, minor_base, (size_t)minor_heap_size_u64);

    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        size_t n_slots = (size_t)(tbl->ptr - tbl->base);
        _Static_assert(sizeof(value *) == sizeof(uint64_t),
            "ref_table optimization requires LP64 (sizeof(value*)==8)");
        bool ok = full_gc(gc_gen_heap, roots_for_gc, (size_t)root_count,
                          gc_fwd_arr, gc_queue, (uint64_t *)tbl->base, n_slots);
        if (!ok) {
            free(roots_for_gc);
            in_full_gc = 0;
            fatal_promotion_failed();
        }
        count_promoted_words(promoted_words(minor_snapshot));
    }

    PROF_START(writeback);
    write_back_forwarded_roots();
    PROF_END(writeback);

    Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
    /* The cycle has ended: the heap is the live data. */
    bytes_promoted_since_major = 0;

    free(roots_for_gc);
    PROF_END(major_gc);

    #ifdef NATIVE_CODE
        /* The minor collection emptied the minor heap.  Without this young_ptr keeps its
         * old value: the next collection would count those words in
         * minor_words a second time, and the space would not be reused. */
        vergc_native_reset_young_ptr();
    #endif

    if (stats_enabled) pause_add(&pause_full, now_ns() - t0);
    in_full_gc = 0;
}

/* A whole collection of both generations, finished (counted under
 * `reason`): stw, full_gc; incremental, finish any cycle still running
 * (start_cycle needs Idle), then a minor collection and start_cycle, and
 * finish that cycle too.  The program then observes a finished cycle, as with
 * stock's caml_finish_major_cycle after a full major. */
static void do_full_gc(uint64_t *reason) {
    ensure_heap();
    (*reason)++;
    if (!major_incremental) { do_full_gc_stw(); return; }
    uint64_t t0 = stats_enabled ? now_ns() : 0;
    finish_cycle_now(&stat_finish_full);
    begin_cycle_now();
    finish_cycle_now(NULL);
    if (stats_enabled) pause_add(&pause_full, now_ns() - t0);
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

/* verified_allocate, VERGC_MAJOR=incremental.  allocate allocates at the
 * collector's phase: black while marking; mid-sweep black in front of the
 * cursor (the sweep keeps it), white behind it.  Before it:
 *   - at Idle, the trigger (phase-aware: never mid-cycle) may start a cycle
 *     (a minor collection and start_cycle);
 *   - mid-cycle, once a minor heap's worth of words has been allocated since
 *     the last slice, a paced slice (4.14 requests one there, from
 *     caml_alloc_shr: a program allocating only major blocks still drives
 *     the cycle).
 * On failure:
 *   1. mid-cycle, finish the cycle (garbage is not on the free list until
 *      the sweep reaches it) and retry;
 *   2. then a full collection, finished, and retry -- what stop-the-world's
 *      full_gc gives;
 *   3. then fail: Out_of_memory, as stop-the-world. */
static void *verified_allocate_incremental(mlsize_t wosize, uint8_t tag) {
    uint64_t words = (uint64_t)wosize + 1;
    if (!in_full_gc) {
        if (vergc_idle()) {
            int why = cycle_trigger(words);
            if (why != 0) {
                if (why == 1) stat_trigger_overhead++;
            else if (why == 2) stat_trigger_heap++;
            else stat_trigger_clock++;
                begin_cycle_now();
            }
        } else if (pace_words >= minor_heap_size_u64 / 8) {
            paced_slice(-1);
        }
    }
    if (vergc_marking()) stat_alloc_mid_mark++;
    else if (vergc_sweeping()) stat_alloc_mid_sweep++;
    uint64_t result = allocate_timed(wosize, tag);
    if (result == 0 && !vergc_idle() && !in_full_gc) {
        finish_cycle_now(&stat_finish_alloc);
        result = allocate_timed(wosize, tag);
    }
    if (result == 0 && !in_full_gc) {
        do_full_gc(&stat_full_alloc);
        result = allocate_timed(wosize, tag);
    }
    if (result == 0) {
        /* As stop-the-world: the heap is the one a full collection and its
         * whole sweep produced, so no free block fits. */
        major_heap_exhausted_hint();
        return NULL;
    }
    PROF_INC(major_alloc_count);
    account_alloc(words);
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
     * Idle (always, stop-the-world); black while marking; mid-sweep, black in
     * front of the cursor.  The patched caml_alloc_shr_aux keeps that colour
     * and rewrites only the profiling bits (WITH_PROFINFO).
     *
     * GC.Spec.Allocator's alloc_spec_preserves_wfh_part4 requires
     * `tag <> infix_tag`: an Infix header inside a free block would break the
     * heap's well-formedness. caml_alloc_shr (and every other caller of
     * caml_alloc_shr_aux) is never called with Infix_tag -- infix headers are
     * only ever written inside a Closure_tag block -- so assert it. */
    CAMLassert(tag != Infix_tag);

    if (major_incremental) return verified_allocate_incremental(wosize, tag);

    /* stw: a proactive full GC on the same 50% threshold as do_minor_gc().
     * Direct major allocations count toward bytes_promoted_since_major
     * (below), so a heap filled by large blocks that are then dropped still
     * triggers a full collection before the next minor collection has to
     * promote into it (issue #34). */
    uint64_t alloc_bytes = ((uint64_t)wosize + 1) * 8;
    if (!in_full_gc) {
        uint64_t major_size = heap_size_u64 - zero_addr;
        if (bytes_promoted_since_major + alloc_bytes > major_size / 2)
            do_full_gc(&stat_full_other);
    }

    uint64_t result = allocate_timed(wosize, tag);

    if (result == 0) {
        do_full_gc(&stat_full_alloc);
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
    do_full_gc(&stat_full_other);
    return Val_unit;
}

/* --- Stock's major-GC entry points (runtime/major_gc.c, gc_ctrl.c) --- */

/* caml_major_collection_slice: Gc.major_slice (runtime/gc_ctrl.c calls it
 * whatever stock's phase says).  Incremental: at Idle, start a cycle (4.14
 * starts one there: a minor collection, then start_cycle); otherwise a paced
 * slice, `howmuch` as 4.14 reads it (0: the next bucket's work; n > 0: the
 * work to free about n words; -1: an automatic slice).  stw: nothing (there
 * are no slices). */
void verified_major_collection_slice(intnat howmuch) {
    ensure_heap();
    if (!major_incremental || in_full_gc) return;
    if (vergc_idle()) {
        stat_trigger_explicit++;
        begin_cycle_now();
        return;
    }
    paced_slice(howmuch < -1 ? -1 : howmuch);
}

/* Gc.major, Gc.full_major and Gc.compact (runtime/gc_ctrl.c), in place of the
 * stock major cycle and compaction, and caml_finish_major_cycle (Gc.set's
 * policy change).  A whole collection: the nursery emptied, then a full
 * collection of both generations, finished, so that the program observes a
 * finished cycle as it does on stock -- one major collection counted. */
void verified_do_full_gc(void) {
    ensure_heap();
    verified_do_minor_gc();
    do_full_gc(&stat_full_explicit);
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
