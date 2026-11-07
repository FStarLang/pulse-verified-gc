/* proto_common.c — modes, timers, pauses, pacing and the worker pool shared
 * by the two prototypes (see proto.h).  Unverified; measurement only. */
#include "proto.h"
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

int       proto_mode = SW_SEQ;
int       proto_threads = 4;
int       proto_check_control = 0;
int       proto_stats = 0;
int       proto_mem = 0;
uint64_t *proto_heads;
uint64_t *proto_tbl;
uint64_t  proto_tbl_len;

uint64_t proto_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

/* ---- growable arrays of durations -------------------------------------- */
typedef struct { uint64_t *v; size_t n, cap; } vec_t;
static void vec_push(vec_t *a, uint64_t x) {
    if (a->n == a->cap) {
        a->cap = a->cap ? 2 * a->cap : 1024;
        a->v = (uint64_t *)realloc(a->v, a->cap * sizeof(uint64_t));
        if (!a->v) { fprintf(stderr, "proto: out of memory (stats)\n"); abort(); }
    }
    a->v[a->n++] = x;
}
static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y;
}
static uint64_t vec_q(vec_t *a, double q) {         /* quantile, sorts a */
    if (a->n == 0) return 0;
    qsort(a->v, a->n, sizeof(uint64_t), cmp_u64);
    size_t i = (size_t)(q * (double)(a->n - 1) + 0.5);
    return a->v[i];
}
static uint64_t vec_sum(const vec_t *a) {
    uint64_t s = 0;
    for (size_t i = 0; i < a->n; i++) s += a->v[i];
    return s;
}

/* ---- collection timers -------------------------------------------------- */
static uint64_t t_mark, t_mark0, t_sweep, t_full, t_full0, t_minor, t_minor0;
static uint64_t n_full, n_minor;
static vec_t    eager_sweeps;               /* one per collection */
static vec_t    mark_times;

void vergc_proto_mark_begin(void) { t_mark0 = proto_now(); }
void vergc_proto_mark_end(void) {
    uint64_t d = proto_now() - t_mark0;
    t_mark += d;
    vec_push(&mark_times, d);
}
void proto_record_eager_sweep(uint64_t ns) { t_sweep += ns; vec_push(&eager_sweeps, ns); }

/* ---- VERGC_PROTO_MEM: pointer locality after the mark --------------------
 * For every black block that is scanned, every field that points into the
 * major heap is one edge, except a field equal to the one before it (an
 * array filled with one value is one edge); it is counted by the distance
 * from the source block's header to the target's: under 64 bytes, 4 KB,
 * 256 KB, 2 MB, or more.  The mark follows these edges, so the shares say how
 * far its reads jump.  Also counted: the 4 KB OS pages that hold live words;
 * live words per such page is the density of what the mark reads. */
static uint64_t n_rescans;
void vergc_proto_rescan(void) { n_rescans++; }

static uint64_t loc_edges, loc_b[5], loc_blocks, loc_live_words, loc_os_pages;

/* The order the mark reads memory in, replayed: a depth-first walk of the
 * black blocks (a stack, children pushed in field order, as the mark's gray
 * stack does), started from each not yet visited black block in address
 * order, since the roots are not at hand here.  Counted per block visited:
 * a jump of 4 KB or more from the block visited before it, and a miss in a
 * 256-entry direct-mapped model of the data TLB (4 KB pages). */
static uint64_t dfs_visits, dfs_j4k, dfs_tlb_miss;
static uint8_t *dfs_seen;
static uint64_t *dfs_stack, dfs_cap;

static inline int dfs_test_set(uint64_t a) {
    uint64_t i = (a - zero_addr) >> 3;
    uint8_t m = (uint8_t)(1u << (i & 7));
    if (dfs_seen[i >> 3] & m) return 1;
    dfs_seen[i >> 3] |= m;
    return 0;
}

static void dfs_walk(void) {
    uint64_t z = zero_addr, hs = heap_size_u64, words = (hs - z) / 8;
    dfs_seen = calloc(words / 8 + 1, 1);
    if (dfs_cap == 0) { dfs_cap = 1 << 20; dfs_stack = malloc(dfs_cap * 8); }
    if (!dfs_seen || !dfs_stack) return;
    uint64_t tlb[256], last = 0;
    memset(tlb, 0xff, sizeof tlb);
    for (uint64_t root = z; root + 8 < hs; root += (HD_WZ(PW(root)) + 1) * 8) {
        if (!IS_BLACK(PW(root)) || dfs_test_set(root)) continue;
        uint64_t sp = 0;
        dfs_stack[sp++] = root;
        while (sp) {
            uint64_t cur = dfs_stack[--sp], h = PW(cur), wz = HD_WZ(h);
            uint64_t d = cur > last ? cur - last : last - cur, pg = cur >> 12;
            dfs_visits++;
            if (d >= 4096) dfs_j4k++;
            if (tlb[pg & 255] != pg) { tlb[pg & 255] = pg; dfs_tlb_miss++; }
            last = cur;
            if ((h & 0xff) >= 251) continue;
            uint64_t prev = 1;
            for (uint64_t i = 1; i <= wz; i++) {
                uint64_t v = PW(cur + 8 * i);
                if ((v & 7) || v <= z || v >= hs || v == prev) continue;
                prev = v;
                uint64_t t = v - 8;
                if (!IS_BLACK(PW(t)) || t + (HD_WZ(PW(t)) + 1) * 8 > hs || dfs_test_set(t)) continue;
                if (sp == dfs_cap) {
                    uint64_t *n = realloc(dfs_stack, dfs_cap * 2 * 8);
                    if (!n) { free(dfs_seen); return; }
                    dfs_stack = n; dfs_cap *= 2;
                }
                dfs_stack[sp++] = t;
            }
        }
    }
    free(dfs_seen);
}

void proto_mem_after_mark(void) {
    uint64_t z = zero_addr, hs = heap_size_u64, last_os_page = UINT64_MAX;
    for (uint64_t cur = z; cur + 8 < hs;) {
        uint64_t h = PW(cur), wz = HD_WZ(h);
        if (IS_BLACK(h)) {
            uint64_t first = (cur - z) >> 12, last = (cur + wz * 8 - z) >> 12;
            loc_blocks++;
            loc_live_words += wz + 1;
            /* OS pages holding live words, each counted once per collection */
            loc_os_pages += last - first + (first != last_os_page);
            last_os_page = last;
            if ((h & 0xff) < 251) {
                uint64_t prev = 1;
                for (uint64_t i = 1; i <= wz; i++) {
                    uint64_t v = PW(cur + 8 * i);
                    if ((v & 7) || v <= z || v >= hs || v == prev) continue;
                    prev = v;
                    uint64_t t = v - 8, d = t > cur ? t - cur : cur - t;
                    loc_edges++;
                    loc_b[d < 64 ? 0 : d < 4096 ? 1 : d < (256u << 10) ? 2 : d < (2u << 20) ? 3 : 4]++;
                }
            }
        }
        cur += (wz + 1) * 8;
    }
    dfs_walk();
}

/* ---- incremental sweep work and the pauses it causes --------------------
 * A "stop" is one mutator-visible interruption: a minor collection, a direct
 * major allocation, or a full collection.  The sweep work done inside a stop
 * (paced slices, sweeping inside an allocation, finishing the sweep) is that
 * stop's sweep pause.  Each piece of work is also kept by kind. */
static int      stop_depth;
static uint64_t stop_sweep;
static vec_t    pauses;                       /* sweep pause per stop with work */
static uint64_t kind_n[PK_N], kind_max[PK_N], kind_total[PK_N], kind_t0[PK_N];
static int      kind_open[PK_N];
static uint64_t slice_n, slice_max;           /* single slices, within bursts */

static void stop_begin(void) { if (stop_depth++ == 0) stop_sweep = 0; }
static void stop_end(void) {
    if (--stop_depth == 0 && stop_sweep > 0) vec_push(&pauses, stop_sweep);
}

void proto_sweep_work_begin(int kind) {
    if (kind_open[kind]++ == 0) kind_t0[kind] = proto_now();
}
void proto_sweep_work_end(int kind) {
    if (--kind_open[kind] != 0) return;
    uint64_t d = proto_now() - kind_t0[kind];
    kind_n[kind]++;
    kind_total[kind] += d;
    if (d > kind_max[kind]) kind_max[kind] = d;
    if (stop_depth > 0) stop_sweep += d;
    else vec_push(&pauses, d);
}

/* Pacing (both allocators): before each minor collection, sweep slices until
 * the swept fraction reaches 4 x (words promoted or allocated in the major
 * heap since the last major collection) / (heap words), at least one slice.
 * The next major collection is due at one half, so the sweep is normally
 * closed at one quarter, before it. */
static void paced_slices(uint64_t promoted_words, uint64_t heap_words) {
    double target = 4.0 * (double)promoted_words / (double)heap_words;
    if (target > 1.0) target = 1.0;
    proto_sweep_work_begin(PK_SLICE);
    do {
        uint64_t t0 = proto_now();
        impl_slice();
        uint64_t d = proto_now() - t0;
        slice_n++;
        if (d > slice_max) slice_max = d;
    } while (impl_sweeping() && impl_swept_fraction() < target);
    proto_sweep_work_end(PK_SLICE);
}

/* ---- the bridge's entry points (verified_gc/alloc_gen.c) ---------------- */
static uint64_t counters_v[16];
static const char *counters_k[16];
void proto_count(const char *name, uint64_t n) {
    for (int i = 0; i < 16; i++) {
        if (counters_k[i] == NULL) counters_k[i] = name;
        if (counters_k[i] == name) { counters_v[i] += n; return; }
    }
}

static double pool_imbalance(void);

static void print_stats(void) {
    if (!proto_stats) return;
    static const char *modes[] = {"seq", "par", "incremental"};
    FILE *f = stderr;
    fprintf(f, "VERGC_PROTO_STATS impl=%s mode=%s threads=%d majors=%llu minors=%llu",
            impl_name(), modes[proto_mode], proto_mode == SW_PAR ? proto_threads : 1,
            (unsigned long long)n_full, (unsigned long long)n_minor);
    fprintf(f, " mark_ms=%.3f sweep_ms=%.3f full_ms=%.3f minor_ms=%.3f",
            t_mark / 1e6, t_sweep / 1e6, t_full / 1e6, t_minor / 1e6);
    uint64_t nsw = eager_sweeps.n;
    fprintf(f, " sweeps=%llu sweep_med_ms=%.4f sweep_max_ms=%.4f mark_med_ms=%.4f",
            (unsigned long long)nsw, vec_q(&eager_sweeps, 0.5) / 1e6,
            vec_q(&eager_sweeps, 1.0) / 1e6, vec_q(&mark_times, 0.5) / 1e6);
    fprintf(f, " pause_n=%zu pause_total_ms=%.3f pause_p99_ms=%.4f pause_max_ms=%.4f",
            pauses.n, vec_sum(&pauses) / 1e6, vec_q(&pauses, 0.99) / 1e6,
            vec_q(&pauses, 1.0) / 1e6);
    fprintf(f, " slices=%llu slice_max_ms=%.4f", (unsigned long long)slice_n, slice_max / 1e6);
    static const char *kinds[] = {"burst", "alloc", "finish"};
    for (int k = 0; k < PK_N; k++)
        fprintf(f, " %s_n=%llu %s_max_ms=%.4f %s_total_ms=%.3f",
                kinds[k], (unsigned long long)kind_n[k], kinds[k], kind_max[k] / 1e6,
                kinds[k], kind_total[k] / 1e6);
    for (int i = 0; i < 16 && counters_k[i]; i++)
        fprintf(f, " %s=%llu", counters_k[i], (unsigned long long)counters_v[i]);
    fprintf(f, " par_imbalance=%.3f", pool_imbalance());
    fprintf(f, " rescans=%llu", (unsigned long long)n_rescans);
    if (proto_mem)
        fprintf(f, " loc_blocks=%llu loc_live_words=%llu loc_os_pages=%llu loc_edges=%llu"
                   " loc_64=%llu loc_4k=%llu loc_256k=%llu loc_2m=%llu loc_far=%llu",
                (unsigned long long)loc_blocks, (unsigned long long)loc_live_words,
                (unsigned long long)loc_os_pages, (unsigned long long)loc_edges,
                (unsigned long long)loc_b[0], (unsigned long long)loc_b[1],
                (unsigned long long)loc_b[2], (unsigned long long)loc_b[3],
                (unsigned long long)loc_b[4]);
    if (proto_mem)
        fprintf(f, " dfs_visits=%llu dfs_j4k=%llu dfs_tlb_miss=%llu",
                (unsigned long long)dfs_visits, (unsigned long long)dfs_j4k,
                (unsigned long long)dfs_tlb_miss);
    impl_stats(f);
    fprintf(f, "\n");
}

void vergc_proto_init(uint64_t *heads, uint64_t *tbl, uint64_t tbl_len) {
    proto_heads = heads;
    proto_tbl = tbl;
    proto_tbl_len = tbl_len;
    const char *m = getenv("VERGC_SWEEP");
    if (m == NULL || strcmp(m, "seq") == 0) proto_mode = SW_SEQ;
    else if (strcmp(m, "par") == 0) proto_mode = SW_PAR;
    else if (strcmp(m, "incremental") == 0) proto_mode = SW_INCR;
    else { fprintf(stderr, "VERGC_SWEEP=%s: expected seq, par or incremental\n", m); exit(2); }
    const char *t = getenv("VERGC_PAR_SWEEP_THREADS");
    if (t) {
        proto_threads = atoi(t);
        if (proto_threads < 1 || proto_threads > 8) {
            fprintf(stderr, "VERGC_PAR_SWEEP_THREADS=%s: expected 1..8\n", t); exit(2);
        }
    }
    const char *c = getenv("VERGC_PROTO_CHECK_CONTROL");
    proto_check_control = c != NULL && atoi(c) != 0;
    const char *s = getenv("VERGC_PROTO_STATS");
    proto_stats = s != NULL && atoi(s) != 0;
    const char *mm = getenv("VERGC_PROTO_MEM");
    proto_mem = mm != NULL && atoi(mm) != 0;
    impl_init();
    atexit(print_stats);
}

void vergc_proto_minor_begin(uint64_t promoted_words, uint64_t heap_words) {
    stop_begin();
    n_minor++;
    t_minor0 = proto_now();
    if (impl_sweeping()) paced_slices(promoted_words, heap_words);
}
void vergc_proto_minor_end(void) {
    t_minor += proto_now() - t_minor0;
    stop_end();
}

void vergc_proto_full_begin(void) {
    stop_begin();
    n_full++;
    if (impl_sweeping()) {
        proto_sweep_work_begin(PK_FINISH);
        impl_finish();
        proto_sweep_work_end(PK_FINISH);
    }
    t_full0 = proto_now();
}
void vergc_proto_full_end(void) {
    t_full += proto_now() - t_full0;
    stop_end();
}

void vergc_proto_direct_begin(void) { stop_begin(); }
void vergc_proto_direct_end(void) { stop_end(); }

void vergc_proto_check(const char *where) { impl_check(where); }

uint64_t vergc_proto_scale(uint64_t requested_bytes) {
    return (uint64_t)((double)requested_bytes * impl_consumption());
}

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
    if (sum > 0) { imbalance_sum += (double)mx * n / (double)sum; imbalance_n++; }
}

static void (*chunk_f)(int);
static int chunk_k;
static volatile int chunk_next;

static void chunk_job(int i, int n, void *arg) {
    (void)i; (void)n; (void)arg;
    int c;
    while ((c = __atomic_fetch_add(&chunk_next, 1, __ATOMIC_RELAXED)) < chunk_k) chunk_f(c);
}

void proto_pool_chunks(int n, int k, void (*chunk)(int c)) {
    chunk_f = chunk;
    chunk_k = k;
    chunk_next = 0;
    proto_pool_run(n, chunk_job, NULL);
}

/* Mean over parallel sweeps of (slowest job) / (mean job): 1.0 is even. */
static double pool_imbalance(void) {
    return imbalance_n ? imbalance_sum / (double)imbalance_n : 0.0;
}
