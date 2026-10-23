/* Runs the parallel sweep's pieces on threads started at each sweep and
   joined before merge (docs/parallel-sweep-phase1.md, §9, Stages 2 and 3).
   No thread outlives a sweep, so fork and Thread.exit need no handling. */
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include "GC_SweepPar.h"

#define MAX_PIECES 64

static int nworkers;
static GC_Impl_Heap_heap_t heap;
static uint64_t bounds[MAX_PIECES + 1];
static seg_result results[MAX_PIECES];
static size_t npieces;
static atomic_size_t next;

static void *worker(void *unused)
{
  (void)unused;
  for (size_t i; (i = atomic_fetch_add(&next, 1)) < npieces; )
    results[i] = sweep_segment(heap, bounds[i], bounds[i + 1]);
  return NULL;
}

int par_sweep_init(int nthreads)
{
  nworkers = nthreads < 0 ? 0 : nthreads > MAX_PIECES ? MAX_PIECES : nthreads;
  return nworkers;
}

uint64_t par_sweep(GC_Impl_Heap_heap_t h, size_t k)
{
  k = k < 1 ? 1 : k > MAX_PIECES ? MAX_PIECES : k;
  if (nworkers == 0) return sweep_par_seq(h, k, bounds, results);
  size_t n = prepass0(h, k, bounds);
  heap = h;
  npieces = n - 1;
  atomic_store(&next, 0);
  pthread_t t[MAX_PIECES];
  int started = 0;
  sigset_t all, old;
  sigfillset(&all);
  pthread_sigmask(SIG_BLOCK, &all, &old);
  while (started < nworkers - 1 && pthread_create(&t[started], NULL, worker, NULL) == 0) started++;
  pthread_sigmask(SIG_SETMASK, &old, NULL);
  worker(NULL);                 /* the main thread is the nth worker */
  for (int i = 0; i < started; i++) pthread_join(t[i], NULL);
  return merge0(h, results, n - 1);
}
