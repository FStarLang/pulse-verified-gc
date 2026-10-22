/* Runs the parallel sweep's pieces on a pool of threads
   (docs/parallel-sweep-phase1.md, §9, Stage 2).  Design only: not wired in. */
#include <pthread.h>
#include <signal.h>
#include "GC_SweepPar.h"

#define MAX_PIECES 64

static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t work = PTHREAD_COND_INITIALIZER;
static pthread_cond_t done = PTHREAD_COND_INITIALIZER;
static int nworkers;
static heap_t heap;
static uint64_t bounds[MAX_PIECES + 1];
static seg_result results[MAX_PIECES];
static size_t npieces, next, unfinished;

static void *worker(void *unused)
{
  (void)unused;
  pthread_mutex_lock(&mu);
  for (;;) {
    while (next == npieces) pthread_cond_wait(&work, &mu);
    size_t i = next++;
    heap_t h = heap;
    uint64_t lo = bounds[i], hi = bounds[i + 1];
    pthread_mutex_unlock(&mu);
    seg_result r = sweep_segment(h, lo, hi);
    pthread_mutex_lock(&mu);
    results[i] = r;
    if (--unfinished == 0) pthread_cond_signal(&done);
  }
}

static void forget_workers(void) { nworkers = 0; }

void par_sweep_init(int nthreads)
{
  pthread_atfork(NULL, NULL, forget_workers);
  sigset_t all, old;
  sigfillset(&all);
  pthread_sigmask(SIG_BLOCK, &all, &old);
  for (; nworkers < nthreads; nworkers++) {
    pthread_t t;
    if (pthread_create(&t, NULL, worker, NULL) != 0) break;
    pthread_detach(t);
  }
  pthread_sigmask(SIG_SETMASK, &old, NULL);
}

uint64_t par_sweep(heap_t h, size_t k)
{
  k = k < 1 ? 1 : k > MAX_PIECES ? MAX_PIECES : k;
  if (nworkers == 0) return sweep_par_seq(h, k, bounds, results);
  size_t n = prepass0(h, k, bounds);
  pthread_mutex_lock(&mu);
  heap = h;
  npieces = n - 1; next = 0; unfinished = n - 1;
  pthread_cond_broadcast(&work);
  while (unfinished > 0) pthread_cond_wait(&done, &mu);
  pthread_mutex_unlock(&mu);
  return merge0(h, results, n - 1);
}
