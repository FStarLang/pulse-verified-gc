/* par_sweep_bridge.c — the parallel sweep, behind a setting that is off by
 * default (docs/parallel-sweep-phase1.md, §9, Stage 3).
 *
 *   VERGC_PAR_SWEEP_THREADS=n   start n worker threads and sweep in parallel;
 *                               unset or 0: the sequential sweep, unchanged
 *   VERGC_PAR_SWEEP_K=k         at most k pieces per sweep (default 4n; the
 *                               pool caps it at 64)
 *
 * When on, collect_with_roots (GC_Gen_Impl.c) calls `parallel` in place of
 * fused_sweep_coalesce.  par_sweep has fused_sweep_coalesce's result, by
 * GC.Spec.SweepPar.sweep_par_correct and the proof of sweep_par_seq.
 *
 * A test build (-DVERGC_PAR_SWEEP_CHECK, `make -C verified_gc PAR_SWEEP_CHECK=1`)
 * also runs the sequential sweep on the same heap at every collection, and
 * aborts unless the heap and the free-list head are exactly equal.  With
 * VERGC_PAR_SWEEP_CHECK_CONTROL=1 it flips one heap byte after the parallel
 * sweep, so the comparison must fail: a control that the check is live.
 * With VERGC_PAR_SWEEP_RACE_CONTROL=1 it runs par_sweep on a helper thread
 * while this thread reads the whole heap, with no synchronisation: a data
 * race that ThreadSanitizer must report.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "GC_SweepPar.h"

/* GC_Gen_Impl.h's heap_t.  GC_SweepPar.h's GC_Impl_Heap_heap_t has the same
 * fields; the two extractions name the type differently. */
typedef struct heap_t_s { uint8_t *data; size_t size; } heap_t;

extern uint64_t (*vergc_sweep_hook)(heap_t heap, uint64_t (*seq)(heap_t heap));
void sweep_par_krmlinit_globals(void);      /* parallel-sweep/snapshot/krmlinit.c, renamed */
int par_sweep_init(int nthreads);           /* parallel-sweep/c/par_sweep.c */
uint64_t par_sweep(GC_Impl_Heap_heap_t h, size_t k);

static size_t pieces;

#ifdef VERGC_PAR_SWEEP_CHECK
#include <pthread.h>

static long checked;

struct race { GC_Impl_Heap_heap_t h; uint64_t fp; };
static void *race_sweep(void *p) { struct race *r = p; r->fp = par_sweep(r->h, pieces); return NULL; }
static int workers;

static void check_summary(void)
{
  fprintf(stderr, "par-sweep check: %ld collections, heap and head equal to the sequential "
          "sweep, %d workers, k %zu\n", checked, workers, pieces);
}

static uint64_t parallel(heap_t h, uint64_t (*seq)(heap_t))
{
  GC_Impl_Heap_heap_t ph = { .data = h.data, .size = h.size };
  /* The heap is [zero_addr, heap_size_u64) at data + address (data is NULL
   * for the major heap: addresses are absolute).  Nothing below zero_addr is
   * written by either sweep. */
  uint8_t *base = (uint8_t *)((uintptr_t)h.data + (uintptr_t)zero_addr);
  size_t n = (size_t)(heap_size_u64 - zero_addr);
  uint8_t *in = malloc(n), *want = malloc(n);
  if (in == NULL || want == NULL) { fprintf(stderr, "par-sweep check: out of memory\n"); abort(); }
  memcpy(in, base, n);
  uint64_t fp_seq = seq(h);
  memcpy(want, base, n);
  memcpy(base, in, n);
  uint64_t fp;
  if (getenv("VERGC_PAR_SWEEP_RACE_CONTROL") != NULL) {
    struct race r = { ph, 0 };
    pthread_t t;
    volatile uint64_t sum = 0;
    if (pthread_create(&t, NULL, race_sweep, &r) != 0) abort();
    for (size_t i = 0; i + 8 <= n; i += 8) sum += *(uint64_t *)(base + i);
    pthread_join(t, NULL);
    fp = r.fp;
  } else
    fp = par_sweep(ph, pieces);
  if (getenv("VERGC_PAR_SWEEP_CHECK_CONTROL") != NULL) base[n / 2] ^= 1;
  checked++;
  if (fp != fp_seq || memcmp(base, want, n) != 0) {
    size_t i = 0;
    while (i < n && base[i] == want[i]) i++;
    fprintf(stderr, "par-sweep check: collection %ld DIFFERS: head %llu vs sequential %llu, "
            "first differing byte at offset %zu of %zu\n", checked,
            (unsigned long long)fp, (unsigned long long)fp_seq, i, n);
    abort();
  }
  free(in);
  free(want);
  return fp;
}
#else
static uint64_t parallel(heap_t h, uint64_t (*seq)(heap_t))
{
  (void)seq;
  GC_Impl_Heap_heap_t ph = { .data = h.data, .size = h.size };
  return par_sweep(ph, pieces);
}
#endif

/* Called once by ensure_heap (alloc_gen.c), after zero_addr and heap_size_u64
 * are set and before the first collection. */
void vergc_par_sweep_setup(void)
{
  const char *t = getenv("VERGC_PAR_SWEEP_THREADS");
  int n = t ? atoi(t) : 0;
  if (n <= 0) return;
  const char *kv = getenv("VERGC_PAR_SWEEP_K");
  long k = kv ? atol(kv) : 4L * n;
  pieces = k < 1 ? 1 : (size_t)k;
  sweep_par_krmlinit_globals();
#ifdef VERGC_PAR_SWEEP_CHECK
  workers = par_sweep_init(n);
  atexit(check_summary);
#else
  par_sweep_init(n);
#endif
  vergc_sweep_hook = parallel;
}
