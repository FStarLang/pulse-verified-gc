/* The parallel page sweep (GC.Impl.Pages.CPar/CDrive and pages_par.c):
 * a differential test against the verified sequential sweep.
 *
 * Two copies of the same heap and allocator state are built by the same
 * requests.  The same objects are marked in both: in copy A as black
 * headers, in copy B as bits of the bitmap.  Copy A is swept by the
 * sequential header sweep (GC.Impl.Pages.Sweep.sweep), copy B by the
 * parallel bitmap sweep at k threads.  Both are proved to compute
 * SweepAll.sweep_all of the same heap (the bitmap's marks are the black
 * headers), so the heaps, the page records and the lists must be equal byte
 * for byte; the free-page hints may differ (each is a valid lower bound),
 * and the bitmap must be all zero after.  Then both allocate again, with the
 * same requests, and must give the same addresses and the same heaps.
 *
 *   pages_par_test [trials]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "GC_Pages.h"
#include "krmlinit.h"
#include "pages_par.h"

#define NPAGES 384ULL
#define PB     32768ULL
#define BYTES  (NPAGES * PB)
#define NCLS 31
#define NL 17
#define O_MT (2 * NCLS + NL)
#define W_LEN (O_MT + 2 + 129 + 2 * NCLS)

typedef struct {
    uint8_t *mem;
    heap_t heap;
    pstate_t st;
} copy_t;

static copy_t A, B;
static uint32_t *bm;
static uint64_t parts[PAGES_PAR_MAX_CHUNKS * PAGES_PAR_PW];
static uint64_t bounds[PAGES_PAR_MAX_CHUNKS + 1];
static uint64_t *objs;
static size_t nobj;
static int failures, checks;

static uint64_t rng;
static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void make(copy_t *x) {
    x->mem = aligned_alloc(PB, BYTES);
    memset(x->mem, 0, BYTES);
    x->heap.data = x->mem;
    x->heap.size = BYTES;
    x->st.tpm = calloc(NPAGES, sizeof(prec));
    x->st.tw = calloc(W_LEN, sizeof(uint64_t));
}

static uint64_t req(void) {
    uint64_t r = rnd() % 1000;
    if (r < 6) return 128 + rnd() % 5000;        /* large */
    r = rnd() % 100;
    if (r < 50) return 1 + rnd() % 3;
    if (r < 80) return 4 + rnd() % 5;
    if (r < 95) return 9 + rnd() % 24;
    return 33 + rnd() % 95;
}

#define CHECK(c, ...) do { checks++; if (!(c)) { failures++; if (failures < 20) { \
    fprintf(stderr, "FAIL: "); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); } } } while (0)

/* Allocate the same requests in both copies, about `words` words. */
static void fill(uint64_t seed, uint64_t words) {
    rng = seed;
    uint64_t tot = 0;
    nobj = 0;
    while (tot < words) {
        uint64_t wz = req();
        uint64_t a = alloc_white(A.heap, A.st, wz);
        uint64_t b = alloc_white(B.heap, B.st, wz);
        CHECK(a == b, "alloc %zu: %llu vs %llu", nobj, (unsigned long long)a, (unsigned long long)b);
        if (!a) break;
        objs[nobj++] = a;
        tot += wz + 1;
    }
}

static void mark(uint64_t seed, unsigned pct) {
    rng = seed;
    for (size_t i = 0; i < nobj; i++) {
        if (rnd() % 100 >= pct) continue;
        uint64_t h = objs[i] - 8;
        uint64_t v;
        memcpy(&v, A.mem + h, 8);
        v |= 0x300ULL;
        memcpy(A.mem + h, &v, 8);
        uint64_t w = h >> 3;
        bm[w >> 5] |= 1u << (w & 31);
    }
}

static void compare(const char *what) {
    CHECK(memcmp(A.mem, B.mem, BYTES) == 0, "%s: heaps differ", what);
    CHECK(memcmp(A.st.tpm, B.st.tpm, NPAGES * sizeof(prec)) == 0, "%s: page records differ", what);
    CHECK(memcmp(A.st.tw, B.st.tw, O_MT * sizeof(uint64_t)) == 0, "%s: lists differ", what);
    CHECK(A.st.tw[O_MT + 1] == B.st.tw[O_MT + 1], "%s: epochs differ", what);
}

static void trial(uint64_t seed, unsigned pct, int k) {
    zero_addr = 0;
    heap_size_u64 = BYTES;
    krmlinit_globals();
    init(A.heap, A.st);
    init(B.heap, B.st);
    memset(bm, 0, (BYTES / 8 / 32) * sizeof(uint32_t));
    fill(seed, BYTES / 8 * 6 / 10);
    for (int round = 0; round < 3; round++) {
        mark(seed * 31 + round, pct);
        sweep(A.heap, A.st);
        par_sweep(B.heap, B.st, bm, parts, bounds, PAGES_PAR_CHUNKS(k), k);
        char what[64];
        snprintf(what, sizeof what, "seed %llu pct %u k %d round %d", (unsigned long long)seed, pct, k, round);
        compare(what);
        int zero = 1;
        for (size_t i = 0; i < BYTES / 8 / 32; i++) if (bm[i]) { zero = 0; break; }
        CHECK(zero, "%s: bitmap not zero", what);
        /* allocate again: the same addresses, the same heaps */
        fill(seed * 7 + round, BYTES / 8 * 2 / 10);
        compare(what);
    }
}

int main(int argc, char **argv) {
    int trials = argc > 1 ? atoi(argv[1]) : 6;
    make(&A);
    make(&B);
    bm = calloc(BYTES / 8 / 32, sizeof(uint32_t));
    objs = malloc(sizeof(uint64_t) * (BYTES / 16));
    unsigned pcts[] = {0, 10, 50, 90, 100};
    int ks[] = {1, 2, 3, 4};
    for (int t = 0; t < trials; t++)
        for (int p = 0; p < 5; p++)
            for (int i = 0; i < 4; i++)
                trial(1000 + (uint64_t)t, pcts[p], ks[i]);
    printf("pages_par_test: %d checks, %d failures\n", checks, failures);
    return failures != 0;
}
