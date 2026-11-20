/* Promotion benchmark (plan section 30): the minor collection with the page
 * allocator (GC_Pages.c, minor_collect_idle) against main's, with akhil's
 * first-fit free list (generational/snapshot/GC_Gen_Impl.c, minor_collect),
 * both Idle.
 *
 * Built twice from this file: -DMAIN for main's, otherwise ours.  Both run
 * the same collections: the nursery (2048 bytes, GC.Gen.Base) filled with
 * one shape of objects, the forwarding array zeroed (a precondition of
 * both), then one collection, timed alone.  A rep is COLLS collections from
 * a freshly initialised major heap of the same size above the nursery's
 * addresses (zero_addr = 2048): NPAGES pages of 32 KB for ours, one free
 * block for main's; the result is the median over
 * reps, in ns per promoted object.  Every collection is checked: the root
 * forwarded to a major address and the nursery reset.
 *
 *   list    127 objects of one field, each pointing at the next: all promoted
 *   tree    85 objects of two fields, a binary tree: all promoted
 *   mixed   a list of objects of 1 to 6 fields: all promoted
 *   half    the list, with only its first half reachable
 *   infix   closures of 4 fields with an infix header, a list through their
 *           infix pointers
 *
 * Two major heaps:
 *   fresh   (the default) the heap as initialised: one free block for
 *           main's, free pages for ours;
 *   steady  (a third argument "steady") after a major collection: the heap
 *           filled with objects of 2 to 7 words in turn, every other one
 *           marked black, then swept (main's `collect` with an empty mark
 *           stack, ours `start_sweep` and `sweep_all`): main's free list is
 *           the dead objects' holes in address order, ours the pools' dead
 *           slots.  A rep is then COLLS_S collections.
 *
 * Usage: bench_promo_main|bench_promo_pages [reps [workload [steady]]]
 * prints one line per workload: <workload> <ns per promoted object>, the
 * workload suffixed -s on the steady heap.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#ifdef MAIN
#include "GC_Gen_Impl.h"
#include "krmlinit.h"
#else
#include "GC_Pages.h"
#include "krmlinit.h"
#endif

#define MHS    2048ULL
#define ZA     2048ULL
#define NPAGES 1024ULL
#define PB     32768ULL
#define TAILB  16ULL
#define BYTES  (ZA + NPAGES * PB + TAILB)
#define COLLS  6000
#define COLLS_S 500

static int steady;

static uint8_t *mem;
static heap_t heap;
static uint8_t nursery[MHS];
static uint64_t nbump;
static uint64_t fwd[MHS / 8];
static uint64_t queue[MHS / 8];
static uint64_t roots[1];

#ifdef MAIN
static const char *a_name = "main";
static uint64_t fp_cell;
static phase_state phase;
static gen_heap_t gh;
static uint64_t no_slots[1];

/* The heap from zero_addr = 2048, as ours, so that no major address looks
 * like a nursery one: one blue block over the whole heap, the free list
 * that block.  (main's init_heap writes this header at zero_addr but
 * returns 8, as if zero_addr were 0; main's own test runs at 0.) */
static void a_init(void) {
    zero_addr = ZA;
    heap_size_u64 = BYTES;
    krmlinit_globals();
    heap.data = mem; heap.size = (size_t)BYTES;
    uint64_t wz = (BYTES - ZA) / 8 - 1, h = (wz << 10) | (2ULL << 8), z = 0;
    memcpy(mem + ZA, &h, 8);
    memcpy(mem + ZA + 8, &z, 8);
    fp_cell = ZA + 8;
    memset(&phase, 0, sizeof phase);
    minor_heap_t mh = { .data = nursery, .size = (size_t)MHS, .bump_ref = &nbump };
    memset(&gh, 0, sizeof gh);
    gh.minor = mh; gh.major = heap; gh.fp_ref = &fp_cell; gh.phase_ref = &phase;
}

static bool a_collect(void) {
    return minor_collect(gh, roots, 1, fwd, queue, no_slots, 0);
}

static uint64_t a_alloc(uint64_t wz) { return allocate(heap, &fp_cell, &phase, wz, 0); }

static void a_sweep(void) {
    static uint64_t storage[16];
    static size_t top;
    top = 16;
    gray_stack_rec gs = { .storage = storage, .top = &top, .cap = 16 };
    fp_cell = collect(heap, gs, fp_cell);
}
#else
static const char *a_name = "pages";
#define NCLS 31
#define NL 17
#define W_LEN ((2 * NCLS + NL) + 2 + 129 + 2 * NCLS)
static prec pm[NPAGES];
static uint64_t tw[W_LEN];
static pstate_t st;

static void a_init(void) {
    zero_addr = ZA;
    heap_size_u64 = BYTES;
    krmlinit_globals();
    heap.data = mem; heap.size = (size_t)BYTES;
    st.tpm = pm; st.tw = tw;
    init(heap, st);
}

static bool a_collect(void) {
    minor_heap_t mh = { .data = nursery, .size = (size_t)MHS, .bump_ref = &nbump };
    return minor_collect_idle(mh, heap, st, roots, 1, fwd, queue, NULL, 0);
}

static uint64_t a_alloc(uint64_t wz) { return alloc_ph(heap, st, wz, 0, false); }

static void a_sweep(void) { start_sweep(st); sweep_all(heap, st); }
#endif

static void nwr(uint64_t a, uint64_t v) { memcpy(nursery + a, &v, 8); }

/* The steady heap: filled with objects of 2 to 7 words in turn, every
 * other one black, then swept. */
static void steady_heap(void) {
    for (uint64_t i = 0;; i++) {
        uint64_t o = a_alloc(1 + i % 6);
        if (!o) break;
        if (i % 2 == 0) {
            uint64_t h; memcpy(&h, mem + o - 8, 8);
            h = (h & ~(3ULL << 8)) | (3ULL << 8);
            memcpy(mem + o - 8, &h, 8);
        }
    }
    a_sweep();
}

static uint64_t nalloc(uint64_t wz, uint64_t tag) {
    uint64_t h = nbump;
    nwr(h, (wz << 10) | tag);
    nbump = h + (wz + 1) * 8;
    return h + 8;
}

/* Fill the nursery with one shape; return the number of objects reachable
 * from the root, which the collection promotes. */
static unsigned fill(const char *w) {
    memset(nursery, 0, sizeof nursery);
    nbump = 0;
    if (!strcmp(w, "list") || !strcmp(w, "half")) {
        uint64_t o[127];
        for (int i = 0; i < 127; i++) o[i] = nalloc(1, 0);
        int last = !strcmp(w, "half") ? 63 : 126;
        for (int i = 0; i < 126; i++) nwr(o[i], i < last ? o[i + 1] : 1);
        nwr(o[126], 1);
        roots[0] = o[0];
        return (unsigned)last + 1;
    } else if (!strcmp(w, "tree")) {
        uint64_t o[85];
        for (int i = 0; i < 85; i++) o[i] = nalloc(2, 0);
        for (int i = 0; i < 85; i++) {
            nwr(o[i], 2 * i + 1 < 85 ? o[2 * i + 1] : 1);
            nwr(o[i] + 8, 2 * i + 2 < 85 ? o[2 * i + 2] : 3);
        }
        roots[0] = o[0];
        return 85;
    } else if (!strcmp(w, "mixed")) {
        uint64_t o[128]; unsigned n = 0, used = 0;
        for (;;) {
            uint64_t wz = 1 + n % 6;
            if (used + (wz + 1) * 8 > MHS) break;
            o[n++] = nalloc(wz, 0);
            used += (unsigned)((wz + 1) * 8);
        }
        for (unsigned i = 0; i < n; i++) {
            uint64_t wz = 1 + i % 6;
            nwr(o[i], i + 1 < n ? o[i + 1] : 1);
            for (uint64_t j = 1; j < wz; j++) nwr(o[i] + 8 * j, 2 * j + 1);
        }
        roots[0] = o[0];
        return n;
    } else if (!strcmp(w, "infix")) {
        /* closures of 4 fields: code, info, infix header (offset 3), code;
         * field 1 points at the next closure's infix address */
        uint64_t p[51]; unsigned n = 51;
        for (unsigned i = 0; i < n; i++) p[i] = nalloc(4, 247);
        for (unsigned i = 0; i < n; i++) {
            nwr(p[i], 1);
            nwr(p[i] + 8, i + 1 < n ? p[i + 1] + 24 : 5);
            nwr(p[i] + 16, (3ULL << 10) | 249);
            nwr(p[i] + 24, 9);
        }
        roots[0] = p[0] + 24;
        return n;
    }
    fprintf(stderr, "unknown workload %s\n", w);
    exit(2);
}

static uint64_t now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static int cmp(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return x < y ? -1 : x > y;
}

/* One rep: COLLS collections from a fresh heap; ns per promoted object. */
static __attribute__((noinline)) double rep(const char *w) {
    a_init();
    if (steady) steady_heap();
    uint64_t t = 0, objs = 0;
    int colls = steady ? COLLS_S : COLLS;
    for (int c = 0; c < colls; c++) {
        unsigned k = fill(w);
        memset(fwd, 0, sizeof fwd);
        uint64_t r0 = roots[0];
        uint64_t t0 = now();
        bool ok = a_collect();
        uint64_t t1 = now();
        if (!ok || roots[0] < ZA || roots[0] == r0 || nbump != 0) {
            fprintf(stderr, "%s: %s: collection %d failed (ok %d root %llu was %llu bump %llu)\n", a_name, w, c, (int)ok, (unsigned long long)roots[0], (unsigned long long)r0, (unsigned long long)nbump);
            exit(1);
        }
        t += t1 - t0;
        objs += k;
    }
    return (double)t / (double)objs;
}

int main(int argc, char **argv) {
    int reps = argc > 1 ? atoi(argv[1]) : 7;
    const char *only = argc > 2 ? argv[2] : NULL;
    steady = argc > 3 && !strcmp(argv[3], "steady");
    const char *ws[] = { "list", "tree", "mixed", "half", "infix" };
    mem = calloc((size_t)BYTES, 1);
    if (!mem) { perror("calloc"); return 1; }
    for (unsigned k = 0; k < sizeof ws / sizeof ws[0]; k++) {
        if (only && strcmp(only, ws[k])) continue;
        double t[64];
        if (reps > 64) reps = 64;
        for (int r = 0; r < reps; r++) t[r] = rep(ws[k]);
        qsort(t, (size_t)reps, sizeof t[0], cmp);
        printf("%s%s %8.2f\n", ws[k], steady ? "-s" : "", t[reps / 2]);
    }
    free(mem);
    return 0;
}
