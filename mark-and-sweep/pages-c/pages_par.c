/* pages_par.c - the trusted part of the parallel page sweep: the threads.
 *
 * Everything the parallel sweep computes is verified Pulse code, extracted
 * to GC_Pages.c: par_prepare, sweep_chunk and par_finish
 * (mark-and-sweep/impl/GC.Impl.Pages.{CDrive,CPar}.fst).  This file only
 * runs sweep_chunk on threads.
 *
 * Specification (trusted).  par_sweep(heap, t, bm, parts, bounds, nc, k)
 * has the effect of the verified GC.Impl.Pages.CDrive.sweep_par_seq(heap,
 * t, bm, parts, bounds, nc): it calls par_prepare, then sweep_chunk(c) for
 * every chunk c < nc, then par_finish, as sweep_par_seq does; but the calls
 * to sweep_chunk run on k threads, chunks t, t + k, t + 2k, ... on thread t
 * (thread 0 is the caller).  Each sweep_chunk(c) reads and writes only chunk
 * c's heap bytes, page records, bitmap words and record parts[c * PW ..],
 * which are disjoint from every other chunk's, and reads only the bounds and
 * the word array t.tw, which no chunk writes: its Pulse precondition owns
 * nothing else.  So the calls give the same result in any order or at the
 * same time.  Every thread has returned from its chunks before par_finish
 * runs (the pool's done count, under its mutex).
 *
 * The threads are a persistent pool, as the prototype's (proto_common.c):
 * workers 1 .. k-1 are started on first use and wait on a condition
 * variable; a fork leaves the child with no workers, and it starts new ones.
 */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "GC_Pages.h"
#include "pages_par.h"

#define MAX_WORKERS 8

static pthread_mutex_t pool_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  pool_go = PTHREAD_COND_INITIALIZER;
static pthread_cond_t  pool_done = PTHREAD_COND_INITIALIZER;
static int      pool_started;                 /* workers running */
static uint64_t pool_gen;                     /* one more per run */
static int      pool_pending;                 /* workers still on this run */
static int      pool_atfork_set;
static uint64_t pool_start_gen[MAX_WORKERS];

/* The run's arguments, written under the mutex before pool_gen moves. */
static heap_t     job_heap;
static pstate_t   job_t;
static uint32_t  *job_bm;
static uint64_t  *job_parts;
static uint64_t  *job_bounds;
static size_t     job_nc;
static int        job_k;

static void run_chunks(int i) {
    for (size_t c = (size_t)i; c < job_nc; c += (size_t)job_k)
        sweep_chunk(job_heap, job_t, job_bm, job_parts, job_bounds, c);
}

static void *pool_worker(void *p) {
    int i = (int)(intptr_t)p;
    pthread_mutex_lock(&pool_mu);
    uint64_t seen = pool_start_gen[i];
    for (;;) {
        while (pool_gen == seen) pthread_cond_wait(&pool_go, &pool_mu);
        seen = pool_gen;
        int k = job_k;
        pthread_mutex_unlock(&pool_mu);
        if (i < k) run_chunks(i);
        pthread_mutex_lock(&pool_mu);
        if (--pool_pending == 0) pthread_cond_signal(&pool_done);
    }
    return NULL;
}

static void pool_child(void) {
    pool_started = 0;
    pthread_mutex_init(&pool_mu, NULL);
    pthread_cond_init(&pool_go, NULL);
    pthread_cond_init(&pool_done, NULL);
}

void par_sweep(heap_t heap, pstate_t t, uint32_t *bm, uint64_t *parts, uint64_t *bounds,
               uint64_t nc, int k) {
    if (k < 1) k = 1;
    if (k > MAX_WORKERS) k = MAX_WORKERS;
    par_prepare(t, bounds, nc);
    if (k == 1) {
        for (size_t c = 0; c < nc; c++) sweep_chunk(heap, t, bm, parts, bounds, c);
    } else {
        if (!pool_atfork_set) { pthread_atfork(NULL, NULL, pool_child); pool_atfork_set = 1; }
        pthread_mutex_lock(&pool_mu);
        while (pool_started < k - 1) {
            pthread_t th;
            int i = pool_started + 1;
            pool_start_gen[i] = pool_gen;
            if (pthread_create(&th, NULL, pool_worker, (void *)(intptr_t)i) != 0) {
                fprintf(stderr, "pages_par: pthread_create failed\n");
                abort();
            }
            pthread_detach(th);
            pool_started++;
        }
        job_heap = heap; job_t = t; job_bm = bm; job_parts = parts; job_bounds = bounds;
        job_nc = (size_t)nc; job_k = k;
        pool_pending = pool_started;
        pool_gen++;
        pthread_cond_broadcast(&pool_go);
        pthread_mutex_unlock(&pool_mu);
        run_chunks(0);
        pthread_mutex_lock(&pool_mu);
        while (pool_pending > 0) pthread_cond_wait(&pool_done, &pool_mu);
        pthread_mutex_unlock(&pool_mu);
    }
    par_finish(heap, t, parts, nc);
}
