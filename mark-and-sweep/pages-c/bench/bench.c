/* Microbenchmark: the extracted page allocator and sweep (GC_Pages.c) against
 * the unverified prototype B2 (alloc_pages.c on sheera/alloc-pages-proto,
 * VERGC_B_VARIANT=2, eager sequential sweep), on the same operations.
 *
 * Built twice from this file: -DPROTO for the prototype, otherwise the
 * extracted code.  Each workload starts from a freshly initialised heap of
 * NPAGES pages of 32 KB; only the timed loop is measured.  The object sizes
 * and the survivors come from a fixed pseudo-random sequence, so both builds
 * do the same requests and mark the same objects.
 *
 *   small    allocate small objects (whsize 2..128) until about 40% of the
 *            heap is requested: ns per allocation
 *   mixed    as small, with 0.5% of requests large (wosize 128..8191)
 *   large    large objects only (wosize 200..20000)
 *   sweepS   after `mixed`, mark S% of the objects black and sweep the
 *            heap: ms per sweep and ns per page in use
 *   realloc  after sweep50, allocate small objects again for as many words
 *            as were freed: ns per allocation (pops from swept pages and
 *            pages given back)
 *   reallocS as realloc, from a heap filled with small objects only, so
 *            that both allocators start from pool pages alone
 *
 * Usage: bench_proto|bench_verified [reps]   prints one line per workload:
 *   <workload> <median> <unit>
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#ifdef PROTO
#include "proto.h"
uint64_t vergc_proto_allocate(heap_t heap, uint64_t *heads, uint64_t *tbl, uint64_t wz);
void vergc_proto_sweep(heap_t heap, uint64_t *heads, uint64_t *tbl);
#else
#include "GC_Pages.h"
#include "krmlinit.h"
#endif

#define NPAGES 4096ULL
#define PB     32768ULL
#define BYTES  (NPAGES * PB)

static uint8_t *mem;
static heap_t heap;

#ifdef PROTO
static void a_init(void) {
    zero_addr = (uint64_t)(uintptr_t)mem;
    heap_size_u64 = zero_addr + BYTES;
    heap.data = mem;
    heap.size = BYTES;
    impl_init();
}
static inline uint64_t a_alloc(uint64_t wz) { return vergc_proto_allocate(heap, NULL, NULL, wz); }
static inline uint64_t *a_hdr(uint64_t o) { return (uint64_t *)(uintptr_t)(o - 8); }
static void a_sweep(void) { vergc_proto_sweep(heap, NULL, NULL); }
static const char *a_name = "proto-B2";
#else
static pstate_t st;
static void a_init(void) {
    zero_addr = 0;
    heap_size_u64 = BYTES;
    krmlinit_globals();
    heap.data = mem;
    heap.size = BYTES;
    if (!st.tpm) {
        st.tpm = calloc(NPAGES, sizeof(prec));
        st.tmeta = calloc(2, sizeof(uint64_t));
        st.tcof = calloc(129, sizeof(uint64_t));
        st.tcls = calloc(31, sizeof(uint64_t));
        st.tns = calloc(31, sizeof(uint64_t));
        st.tavail = calloc(64, sizeof(uint64_t));
        st.tlarge = calloc(17, sizeof(uint64_t));
    }
    init(heap, st);
}
static inline uint64_t a_alloc(uint64_t wz) { return alloc_white(heap, st, wz); }
static inline uint64_t *a_hdr(uint64_t o) { return (uint64_t *)(mem + o - 8); }
static void a_sweep(void) { sweep(heap, st); }
static const char *a_name = "verified";
#endif

static uint64_t now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static uint64_t rng;
static inline uint64_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return rng;
}

/* Request sizes (wosize), fixed per workload. */
#define MAXN (40u << 20)
static uint32_t *req;
static uint64_t *objs;
static size_t nreq;

static uint64_t small_wz(void) {
    uint64_t r = rnd() % 100;
    if (r < 50) return 1 + rnd() % 3;
    if (r < 80) return 4 + rnd() % 5;
    if (r < 95) return 9 + rnd() % 24;
    return 33 + rnd() % 95;
}

static void make_reqs(int kind, uint64_t words) {
    rng = 0x9E3779B97F4A7C15ULL + (uint64_t)kind;
    uint64_t tot = 0;
    nreq = 0;
    while (tot < words && nreq < MAXN) {
        uint64_t wz;
        if (kind == 0) wz = small_wz();
        else if (kind == 1) wz = rnd() % 1000 < 5 ? 128 + rnd() % 8064 : small_wz();
        else wz = 200 + rnd() % 19801;
        req[nreq++] = (uint32_t)wz;
        tot += wz + 1;
    }
}

static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y;
}

static uint64_t run_allocs(size_t n) {
    uint64_t t0 = now();
    for (size_t i = 0; i < n; i++) {
        uint64_t o = a_alloc(req[i]);
        if (!o) { fprintf(stderr, "%s: out of memory at request %zu\n", a_name, i); exit(1); }
        objs[i] = o;
    }
    return now() - t0;
}

static void mark(size_t n, unsigned pct, uint64_t seed) {
    rng = seed;
    for (size_t i = 0; i < n; i++)
        if (rnd() % 100 < pct) *a_hdr(objs[i]) |= 0x300ULL;
}

static uint64_t pages_used;   /* rough: words requested / page words */

int main(int argc, char **argv) {
    int reps = argc > 1 ? atoi(argv[1]) : 7;
    mem = aligned_alloc(PB, BYTES + PB);
    req = malloc(sizeof(uint32_t) * MAXN);
    objs = malloc(sizeof(uint64_t) * MAXN);
    if (!mem || !req || !objs) { perror("alloc"); return 1; }
    memset(mem, 0, BYTES + PB);
    uint64_t target = BYTES / 8 * 40 / 100;
    const char *names[] = {"small", "mixed", "large"};
    uint64_t *t = malloc(sizeof(uint64_t) * reps);

    for (int k = 0; k < 3; k++) {
        make_reqs(k, target);
        for (int r = 0; r < reps; r++) { a_init(); t[r] = run_allocs(nreq); }
        qsort(t, reps, sizeof(uint64_t), cmp_u64);
        printf("%-8s %8.2f ns/alloc  (%s, %zu allocs)\n", names[k], (double)t[reps / 2] / nreq, a_name, nreq);
    }

    unsigned pcts[] = {10, 50, 90};
    for (int s = 0; s < 3; s++) {
        make_reqs(1, target);
        pages_used = target / 4096;
        for (int r = 0; r < reps; r++) {
            a_init();
            run_allocs(nreq);
            mark(nreq, pcts[s], 12345 + r);
            uint64_t t0 = now();
            a_sweep();
            t[r] = now() - t0;
        }
        qsort(t, reps, sizeof(uint64_t), cmp_u64);
        printf("sweep%-3u %8.3f ms/sweep  (%s, %.1f ns/page in use)\n", pcts[s],
               (double)t[reps / 2] / 1e6, a_name, (double)t[reps / 2] / pages_used);
    }

    /* realloc: after a 50% sweep, allocate small objects again */
    {
        make_reqs(1, target);
        size_t n1 = nreq;
        for (int r = 0; r < reps; r++) {
            make_reqs(1, target);
            a_init();
            run_allocs(n1);
            mark(n1, 50, 777);
            a_sweep();
            make_reqs(0, target / 2);
            t[r] = run_allocs(nreq);
        }
        qsort(t, reps, sizeof(uint64_t), cmp_u64);
        printf("realloc  %8.2f ns/alloc  (%s, %zu allocs)\n", (double)t[reps / 2] / nreq, a_name, nreq);
    }
    /* reallocS: the same from a heap of small objects only */
    {
        make_reqs(0, target);
        size_t n1 = nreq;
        for (int r = 0; r < reps; r++) {
            make_reqs(0, target);
            a_init();
            run_allocs(n1);
            mark(n1, 50, 777);
            a_sweep();
            make_reqs(0, target / 2);
            t[r] = run_allocs(nreq);
        }
        qsort(t, reps, sizeof(uint64_t), cmp_u64);
        printf("reallocS %8.2f ns/alloc  (%s, %zu allocs)\n", (double)t[reps / 2] / nreq, a_name, nreq);
    }
    return 0;
}
