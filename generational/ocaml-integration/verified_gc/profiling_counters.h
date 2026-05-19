/* profiling_counters.h — Fine-grained overhead instrumentation.
 * Include this and call gc_print_profile() at exit. */
#ifndef PROFILING_COUNTERS_H
#define PROFILING_COUNTERS_H

#include <time.h>
#include <stdio.h>
#include <stdint.h>

#ifdef GC_PROFILE

static inline uint64_t rdtsc(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

/* Counters */
static uint64_t prof_minor_alloc_count = 0;
static uint64_t prof_major_alloc_count = 0;
static uint64_t prof_minor_gc_count = 0;
static uint64_t prof_major_gc_count = 0;
static uint64_t prof_objects_promoted = 0;
static uint64_t prof_fields_translated = 0;
static uint64_t prof_fields_updated = 0;

/* Timing accumulators (nanoseconds) */
static uint64_t prof_t_minor_alloc = 0;    /* gen_alloc for minor */
static uint64_t prof_t_major_alloc = 0;    /* gen_alloc for major (free-list) */
static uint64_t prof_t_root_scan = 0;      /* caml_do_roots + root processing */
static uint64_t prof_t_fwd_arr_zero = 0;   /* memset gc_fwd_arr */
static uint64_t prof_t_translate = 0;      /* translate_minor_fields (legacy, unused) */
static uint64_t prof_t_infix_find = 0;     /* find_infix_parents (legacy, unused) */
static uint64_t prof_t_queue_zero = 0;     /* Pulse_Lib_Array_fill (inside cheney_promote_phase) */
static uint64_t prof_t_cheney = 0;         /* minor_collect total */
static uint64_t prof_t_infix_synth = 0;    /* synthesize_infix_forwarding (legacy, unused) */
static uint64_t prof_t_update_fields = 0;  /* update_one_object loop (inside minor_collect) */
static uint64_t prof_t_rewrite_roots = 0;  /* rewrite_roots_impl (inside minor_collect) */
static uint64_t prof_t_writeback = 0;      /* root writeback (step 6) */
static uint64_t prof_t_ref_table = 0;      /* ref_table rewriting (5.5) */
static uint64_t prof_t_minor_reset = 0;    /* minor_heap_reset */
static uint64_t prof_t_major_gc = 0;       /* collect() (mark + sweep) */
static uint64_t prof_t_minor_gc_total = 0; /* total do_minor_gc_core time */

#define PROF_START(var)  uint64_t _prof_##var = rdtsc()
#define PROF_END(var)    prof_t_##var += (rdtsc() - _prof_##var)
#define PROF_INC(ctr)    prof_##ctr++
#define PROF_ADD(ctr, n) prof_##ctr += (n)

static void gc_print_profile(void) {
    uint64_t total = prof_t_minor_gc_total + prof_t_major_gc + prof_t_minor_alloc + prof_t_major_alloc;
    fprintf(stderr, "\n=== GC Profile ===\n");
    fprintf(stderr, "Counts:\n");
    fprintf(stderr, "  minor allocs:     %12lu\n", (unsigned long)prof_minor_alloc_count);
    fprintf(stderr, "  major allocs:     %12lu\n", (unsigned long)prof_major_alloc_count);
    fprintf(stderr, "  minor GCs:        %12lu\n", (unsigned long)prof_minor_gc_count);
    fprintf(stderr, "  major GCs:        %12lu\n", (unsigned long)prof_major_gc_count);
    fprintf(stderr, "  objects promoted:  %12lu\n", (unsigned long)prof_objects_promoted);
    fprintf(stderr, "  fields translated: %12lu\n", (unsigned long)prof_fields_translated);
    fprintf(stderr, "  fields updated:    %12lu\n", (unsigned long)prof_fields_updated);
    fprintf(stderr, "\nTiming (ms):\n");
    fprintf(stderr, "  minor alloc (gen_alloc):   %8.1f ms (%5.1f%%)\n",
        prof_t_minor_alloc/1e6, 100.0*prof_t_minor_alloc/total);
    fprintf(stderr, "  major alloc (free-list):    %8.1f ms (%5.1f%%)\n",
        prof_t_major_alloc/1e6, 100.0*prof_t_major_alloc/total);
    fprintf(stderr, "  --- Minor GC breakdown: ---\n");
    fprintf(stderr, "  root scan:                 %8.1f ms (%5.1f%%)\n",
        prof_t_root_scan/1e6, 100.0*prof_t_root_scan/total);
    fprintf(stderr, "  fwd_arr zero (memset):     %8.1f ms (%5.1f%%)\n",
        prof_t_fwd_arr_zero/1e6, 100.0*prof_t_fwd_arr_zero/total);
    fprintf(stderr, "  translate_minor_fields:    %8.1f ms (%5.1f%%)\n",
        prof_t_translate/1e6, 100.0*prof_t_translate/total);
    fprintf(stderr, "  find_infix_parents:        %8.1f ms (%5.1f%%)\n",
        prof_t_infix_find/1e6, 100.0*prof_t_infix_find/total);
    fprintf(stderr, "  minor_collect:             %8.1f ms (%5.1f%%)\n",
        prof_t_cheney/1e6, 100.0*prof_t_cheney/total);
    fprintf(stderr, "    (includes queue zero):   %8.1f ms\n",
        prof_t_queue_zero/1e6);
    fprintf(stderr, "  [legacy] find_infix:       %8.1f ms (%5.1f%%)\n",
        prof_t_infix_find/1e6, 100.0*prof_t_infix_find/total);
    fprintf(stderr, "  [legacy] synth_infix:      %8.1f ms (%5.1f%%)\n",
        prof_t_infix_synth/1e6, 100.0*prof_t_infix_synth/total);
    fprintf(stderr, "  update_one_object loop:    %8.1f ms (%5.1f%%)\n",
        prof_t_update_fields/1e6, 100.0*prof_t_update_fields/total);
    fprintf(stderr, "  rewrite_roots:             %8.1f ms (%5.1f%%)\n",
        prof_t_rewrite_roots/1e6, 100.0*prof_t_rewrite_roots/total);
    fprintf(stderr, "  ref_table rewrite:         %8.1f ms (%5.1f%%)\n",
        prof_t_ref_table/1e6, 100.0*prof_t_ref_table/total);
    fprintf(stderr, "  root writeback:            %8.1f ms (%5.1f%%)\n",
        prof_t_writeback/1e6, 100.0*prof_t_writeback/total);
    fprintf(stderr, "  minor_heap_reset:          %8.1f ms (%5.1f%%)\n",
        prof_t_minor_reset/1e6, 100.0*prof_t_minor_reset/total);
    fprintf(stderr, "  minor GC total:            %8.1f ms\n",
        prof_t_minor_gc_total/1e6);
    fprintf(stderr, "  --- Major GC: ---\n");
    fprintf(stderr, "  major GC (mark+sweep):     %8.1f ms (%5.1f%%)\n",
        prof_t_major_gc/1e6, 100.0*prof_t_major_gc/total);
    fprintf(stderr, "  === TOTAL GC overhead:     %8.1f ms ===\n",
        total/1e6);
    fprintf(stderr, "  per minor alloc: %.1f ns\n",
        prof_minor_alloc_count ? (double)prof_t_minor_alloc/prof_minor_alloc_count : 0);
    fprintf(stderr, "  per minor GC: %.3f ms\n",
        prof_minor_gc_count ? prof_t_minor_gc_total/1e6/prof_minor_gc_count : 0);
}

#else /* !GC_PROFILE */

#define PROF_START(var)
#define PROF_END(var)
#define PROF_INC(ctr)
#define PROF_ADD(ctr, n)
static void gc_print_profile(void) {}

#endif /* GC_PROFILE */

#endif /* PROFILING_COUNTERS_H */
