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
 *   inc      incremental mode: after a mixed heap with 50% marked, the
 *            sweep starts; allocations alternate with one-unit slices (one
 *            per 8 allocations; incL one per 64; incS from a small-only
 *            heap), the sweep finished at the end: ns per allocation
 *
 * Usage: bench_proto|bench_verified [reps [workload]]   prints one line per
 * workload run: <workload> <median> <unit>.  With a workload name (small,
 * mixed, large, sweep, realloc, reallocS) only that one runs, so that each
 * starts in a fresh process; `bench.sh` does that for every workload,
 * alternating the two binaries.
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
/* Incremental mode: the prototype's own (SW_INCR): the cycle start, a unit
 * per slice, and allocation that sweeps when it finds no room. */
static void a_start_inc(void) { proto_mode = SW_INCR; vergc_proto_sweep(heap, NULL, NULL); }
static int a_sweeping(void) { return impl_sweeping(); }
static void a_slice(void) { impl_slice(); }
static inline uint64_t a_alloc_inc(uint64_t wz) { return vergc_proto_allocate(heap, NULL, NULL, wz); }
static const char *a_name = "proto-B2";
#else
static pstate_t st;
static void a_init(void) {
    zero_addr = 0;
    heap_size_u64 = BYTES + 16;   /* the pages, and the two-word tail the layout reserves */
    krmlinit_globals();
    heap.data = mem;
    heap.size = BYTES + 16;
    if (!st.tpm) {
        st.tpm = calloc(NPAGES, sizeof(prec));
        st.tw = calloc(1024, sizeof(uint64_t));
    }
    init(heap, st);
}
#ifdef TAGGED
/* The allocator with a tag (alloc_tag, plan section 27.1), white, as a
 * promotion copies objects of several tags. */
static inline uint64_t a_alloc(uint64_t wz) { return alloc_tag(heap, st, wz, White, wz & 7); }
#else
static inline uint64_t a_alloc(uint64_t wz) { return alloc_white(heap, st, wz); }
#endif
static inline uint64_t *a_hdr(uint64_t o) { return (uint64_t *)(mem + o - 8); }
static void a_sweep(void) { sweep(heap, st); }
/* Incremental mode (plan section 28): start_sweep, then slices of one unit
 * (sweep_slice) from a cursor, between allocations of the phase's
 * allocator (alloc_ph, white, with a tag); an allocation that finds no room
 * mid-sweep sweeps a unit and tries again, as the prototype's does, on a
 * slow path out of line (as the prototype's refill). */
static uint64_t cur;
static int swp;
static void a_start_inc(void) { start_sweep(st); cur = 0; swp = 1; }
static int a_sweeping(void) { return swp; }
static void a_slice(void) {
    if (swp) { cur = sweep_slice(heap, st, cur, 1); if (cur >= NPAGES) swp = 0; }
}
__attribute__((noinline)) static uint64_t a_alloc_retry(uint64_t wz) {
    uint64_t o = 0;
    while (!o && swp) { a_slice(); o = alloc_ph(heap, st, wz, wz & 7, false); }
    return o;
}
static inline uint64_t a_alloc_inc(uint64_t wz) {
    uint64_t o = alloc_ph(heap, st, wz, wz & 7, false);
    if (__builtin_expect(!o, 0)) o = a_alloc_retry(wz);
    return o;
}
#ifdef TAGGED
static const char *a_name = "verified-tag";
#else
static const char *a_name = "verified";
#endif
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

/* The timed part of the incremental workloads, in a function of its own as
 * run_allocs is: inlined into main, the allocator's fast path was compiled
 * with main's register pressure, which cost the verified build 2.7 ns per
 * allocation in this loop and not elsewhere (plan section 28.4). */
__attribute__((noinline)) static uint64_t run_inc(size_t n, unsigned k) {
    uint64_t t0 = now();
    a_start_inc();
    unsigned j = 0;
    for (size_t i = 0; i < n; i++) {
        uint64_t o = a_alloc_inc(req[i]);
        if (!o) { fprintf(stderr, "%s: out of memory at request %zu\n", a_name, i); exit(1); }
        objs[i] = o;
        if (++j == k) { j = 0; a_slice(); }
    }
    while (a_sweeping()) a_slice();
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
    const char *only = argc > 2 ? argv[2] : NULL;
#define RUN(name) (!only || strcmp(only, name) == 0)
    mem = aligned_alloc(PB, BYTES + PB);
    req = malloc(sizeof(uint32_t) * MAXN);
    objs = malloc(sizeof(uint64_t) * MAXN);
    if (!mem || !req || !objs) { perror("alloc"); return 1; }
    memset(mem, 0, BYTES + PB);
    uint64_t target = BYTES / 8 * 40 / 100;
    const char *names[] = {"small", "mixed", "large"};
    uint64_t *t = malloc(sizeof(uint64_t) * reps);

    for (int k = 0; k < 3; k++) {
        if (!RUN(names[k])) continue;
        make_reqs(k, target);
        for (int r = 0; r < reps; r++) { a_init(); t[r] = run_allocs(nreq); }
        qsort(t, reps, sizeof(uint64_t), cmp_u64);
        printf("%-8s %8.2f ns/alloc  (%s, %zu allocs)\n", names[k], (double)t[reps / 2] / nreq, a_name, nreq);
    }

    unsigned pcts[] = {10, 50, 90};
    for (int s = 0; s < 3 && RUN("sweep"); s++) {
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
    if (RUN("realloc")) {
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
    if (RUN("reallocS")) {
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
    /* incremental: after a mixed (inc, incL) or small-only (incS) heap with
     * 50% marked, the sweep starts and allocations of half the heap's
     * requests alternate with slices of one unit, one per K allocations;
     * the sweep is finished at the end.  ns per allocation, slices and the
     * sweep's start included. */
    struct { const char *name; int fill, again; unsigned k; } incs[] = {
        { "inc", 1, 1, 8 }, { "incL", 1, 1, 64 }, { "incS", 0, 0, 8 } };
    for (int w = 0; w < 3; w++) {
        if (!RUN(incs[w].name)) continue;
        make_reqs(incs[w].fill, target);
        size_t n1 = nreq;
        size_t n2 = 0;
        for (int r = 0; r < reps; r++) {
            make_reqs(incs[w].fill, target);
            a_init();
            run_allocs(n1);
            mark(n1, 50, 777);
            make_reqs(incs[w].again, target / 2);
            n2 = nreq;
            t[r] = run_inc(n2, incs[w].k);
        }
        qsort(t, reps, sizeof(uint64_t), cmp_u64);
        printf("%-8s %8.2f ns/alloc  (%s, %zu allocs, a slice per %u)\n", incs[w].name,
               (double)t[reps / 2] / n2, a_name, n2, incs[w].k);
    }
    return 0;
}
