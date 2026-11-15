/* What alloc_pages.c of the parallel prototype (sheera/pages-parallel-proto)
 * needs from proto_common.c for the parallel bitmap sweep: the stubs of
 * proto_stubs.c, the bitmap, and the prototype's worker pool, whose code
 * below is copied verbatim from proto_common.c (the "worker pool" section). */
#include "proto.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

int       proto_mode = SW_PAR;
int       proto_threads = 1;
int       proto_check_control = 0;
int       proto_stats = 0;
int       proto_mem = 0;
int       proto_mark = 1;               /* the bitmap */
uint32_t *proto_bm;
int       proto_chunks_static = 1;      /* static chunks; VERGC_PSTATIC=0: dynamic */
int       proto_pool_record = 0;
uint64_t  zero_addr, heap_size_u64;

uint64_t proto_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}
void proto_sweep_work_begin(int kind) { (void)kind; }
void proto_sweep_work_end(int kind) { (void)kind; }
void proto_record_eager_sweep(uint64_t ns) { (void)ns; }
void proto_count(const char *name, uint64_t n) { (void)name; (void)n; }
void proto_mem_after_mark(void) {}

/* ---- worker pool ---------------------------------------------------------
 * Workers 1..n-1 are threads started on first use and kept; job 0 runs on
 * the caller.  A fork leaves the child with only the calling thread, so the
 * child forgets the workers and starts new ones if it sweeps in parallel. */
#define MAX_WORKERS 8
static pthread_mutex_t pool_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  pool_go = PTHREAD_COND_INITIALIZER;
static pthread_cond_t  pool_done = PTHREAD_COND_INITIALIZER;
static int             pool_started;            /* threads running */
static uint64_t        pool_gen;
static int             pool_pending;
static proto_job       pool_f;
static void           *pool_arg;
static int             pool_n;
static int             pool_atfork_set;
static uint64_t        pool_start_gen[MAX_WORKERS];  /* pool_gen when created */

/* Per-job durations of the last parallel run, for the balance statistic. */
static uint64_t job_ns[MAX_WORKERS];
static double   imbalance_sum;      /* sum over runs of max job / mean job */
static uint64_t imbalance_n;

static void timed_job(proto_job f, int i, int n, void *arg) {
    uint64_t t0 = proto_now();
    f(i, n, arg);
    job_ns[i] = proto_now() - t0;
}

static void *pool_worker(void *p) {
    int i = (int)(intptr_t)p;
    pthread_mutex_lock(&pool_mu);
    uint64_t seen = pool_start_gen[i];       /* so the first job is not missed */
    for (;;) {
        while (pool_gen == seen) pthread_cond_wait(&pool_go, &pool_mu);
        seen = pool_gen;
        proto_job f = pool_f;
        void *arg = pool_arg;
        int n = pool_n;
        pthread_mutex_unlock(&pool_mu);
        if (i < n) timed_job(f, i, n, arg);
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

void proto_pool_run(int n, proto_job f, void *arg) {
    if (n <= 1) { f(0, 1, arg); return; }
    if (!pool_atfork_set) { pthread_atfork(NULL, NULL, pool_child); pool_atfork_set = 1; }
    pthread_mutex_lock(&pool_mu);
    while (pool_started < n - 1 && pool_started < MAX_WORKERS - 1) {
        pthread_t th;
        int i = pool_started + 1;
        pool_start_gen[i] = pool_gen;
        if (pthread_create(&th, NULL, pool_worker, (void *)(intptr_t)i) != 0) {
            fprintf(stderr, "proto: pthread_create failed\n"); abort();
        }
        pthread_detach(th);
        pool_started++;
    }
    pool_f = f;
    pool_arg = arg;
    pool_n = n;
    pool_pending = pool_started;
    pool_gen++;
    pthread_cond_broadcast(&pool_go);
    pthread_mutex_unlock(&pool_mu);
    timed_job(f, 0, n, arg);
    pthread_mutex_lock(&pool_mu);
    while (pool_pending > 0) pthread_cond_wait(&pool_done, &pool_mu);
    pthread_mutex_unlock(&pool_mu);
    uint64_t mx = 0, sum = 0;
    for (int i = 0; i < n; i++) { sum += job_ns[i]; if (job_ns[i] > mx) mx = job_ns[i]; }
    if (sum > 0 && proto_pool_record) { imbalance_sum += (double)mx * n / (double)sum; imbalance_n++; }
}

static void (*chunk_f)(int);
static int chunk_k;
static volatile int chunk_next;

static void chunk_job(int i, int n, void *arg) {
    (void)arg;
    int c;
    if (proto_chunks_static) {        /* chunks i, i + n, i + 2n, ... */
        for (c = i; c < chunk_k; c += n) chunk_f(c);
        return;
    }
    while ((c = __atomic_fetch_add(&chunk_next, 1, __ATOMIC_RELAXED)) < chunk_k) chunk_f(c);
}

void proto_pool_chunks(int n, int k, void (*chunk)(int c)) {
    chunk_f = chunk;
    chunk_k = k;
    chunk_next = 0;
    proto_pool_run(n, chunk_job, NULL);
}

