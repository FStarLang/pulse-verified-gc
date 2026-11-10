/* The page allocator (GC.Impl.Pages.*): directed tests of the extracted C.
 *
 * Each test lays out a small heap of 32 KB pages by hand (zero_addr = 0, so
 * offsets are addresses), runs the extracted `alloc` or `sweep`, and checks
 * every header, link, page-map entry and list head it should have written
 * against the specification (GC.Spec.Pages.*):
 *   - a small block takes the first free slot of the first page on its
 *     class's list, or a fresh pool page whose slots are linked in order;
 *     a block smaller than its slot gets a blue filler after it;
 *   - a large block is carved from the right of the first listed block that
 *     fits, or gets a new run of free pages, the rest of the run one blue
 *     block listed in front of list 0 when it has at least lg_min words;
 *   - when nothing fits, nothing changes;
 *   - the sweep whitens survivors, links each pool page's dead slots from the
 *     last one down, gives back pool pages with no survivor and whole free
 *     pages of runs, merges dead stretches of runs, and lists every merged
 *     block of at least lg_min words, in address order, in front of list 0.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "GC_Pages.h"
#include "krmlinit.h"

#define PW 4096ULL            /* words per page (GC.Spec.Pages.Params) */
#define PB (PW * 8ULL)        /* bytes per page */
#define NCLS 31
#define NL 17
#define LG_MIN 129ULL         /* small_max + 1 */
#define MAXP 8

static uint8_t *mem;
static heap_t heap;
static prec pm[MAXP];          /* stored records: the epoch of the last sweep */
static uint64_t meta[2];       /* the free-page hint, the sweep epoch */
static uint64_t tcof[129], tcls[NCLS], tns[NCLS];   /* the class tables, filled by init */
static uint64_t avail[NCLS];
static uint64_t large[NL];
static pstate_t st;
static uint64_t np;
static int failures, checks;

enum { WHITE = 0, GRAY = 1, BLUE = 2, BLACK = 3 };
enum { FREE = 0, POOL = 1, HEAD = 2, CONT = 3 };

static void wr(uint64_t a, uint64_t v) { memcpy(mem + a, &v, 8); }
static uint64_t rd(uint64_t a) { uint64_t v; memcpy(&v, mem + a, 8); return v; }
static uint64_t hdr(uint64_t wz, uint64_t col) { return (wz << 10) | (col << 8); }
static uint64_t pg(uint64_t i) { return i * PB; }

#define CHECK(name, cond) do { \
    checks++; \
    if (!(cond)) { printf("FAIL: pages: %s: %s (line %d)\n", name, #cond, __LINE__); failures++; } \
} while (0)

/* A page's record as the specification sees it (State.pinfo, `view`). */
typedef struct { uint8_t code; uint64_t arg; bool swept; uint64_t free_head, nfree, next; } vrec;

static vrec rec(uint8_t code, uint64_t arg, bool swept, uint64_t fh, uint64_t nf, uint64_t nx) {
    vrec r = { .code = code, .arg = arg, .swept = swept, .free_head = fh, .nfree = nf, .next = nx };
    return r;
}

/* Page i's record as the extracted code reads it (State.to_pinfo): swept
 * when it is free or was swept in the current epoch. */
static vrec V(uint64_t i) {
    prec p = pm[i];
    bool fr = !(p.pcode == POOL && p.parg < NCLS) && !(p.pcode == HEAD && p.parg > 0) && p.pcode != CONT;
    return rec(p.pcode, p.parg, fr || p.sep == meta[1], p.pfree_head, p.pnfree, p.pnext);
}

/* Store a record as the extracted code does (State.of_pinfo). */
static void put(uint64_t i, vrec r) {
    prec p = { .pcode = r.code, .parg = r.arg, .sep = r.swept ? meta[1] : 0,
               .pfree_head = r.free_head, .pnfree = r.nfree, .pnext = r.next };
    pm[i] = p;
}

static int same_rec(vrec a, vrec b) {
    return a.code == b.code && a.arg == b.arg && a.swept == b.swept &&
           a.free_head == b.free_head && a.nfree == b.nfree && a.next == b.next;
}

/* A heap of `n` free pages, from the extracted `init`: one blue block per
 * page, every entry a free page's, every list empty.  Checked once here. */
static void fresh(uint64_t n) {
    np = n;
    heap_size_u64 = n * PB;
    zero_addr = 0;
    krmlinit_globals();
    memset(mem, 0xAB, (size_t)(MAXP * PB));
    heap.data = mem;
    heap.size = (size_t)heap_size_u64;
    for (int i = 0; i < MAXP; i++) pm[i] = (prec){ .pcode = HEAD, .parg = 7, .sep = 99, .pfree_head = 1, .pnfree = 2, .pnext = 3 };
    meta[0] = 5; meta[1] = 0;
    for (int c = 0; c < NCLS; c++) avail[c] = 5;
    for (int k = 0; k < NL; k++) large[k] = 9;
    st.tpm = pm; st.tavail = avail; st.tlarge = large; st.tmeta = meta; st.tcof = tcof; st.tcls = tcls; st.tns = tns;
    init(heap, st);
    for (uint64_t i = 0; i < n; i++) {
        CHECK("init", rd(pg(i)) == hdr(PW - 1, BLUE));
        CHECK("init", same_rec(V(i), rec(FREE, 0, true, 0, 0, 0)));
    }
    for (int c = 0; c < NCLS; c++) CHECK("init", avail[c] == 0);
    for (int k = 0; k < NL; k++) CHECK("init", large[k] == 0);
    memset(mem, 0, (size_t)(MAXP * PB));
    for (uint64_t i = 0; i < n; i++) wr(pg(i), hdr(PW - 1, BLUE));
}

/* A heap of whole pages and a tail of 3 words: `init` gives the tail one
 * blue block. */
static void test_init_tail(void) {
    heap_size_u64 = 2 * PB + 24;
    zero_addr = 0;
    krmlinit_globals();
    memset(mem, 0xAB, (size_t)(MAXP * PB));
    heap.data = mem;
    heap.size = (size_t)heap_size_u64;
    st.tpm = pm; st.tavail = avail; st.tlarge = large; st.tmeta = meta; st.tcof = tcof; st.tcls = tcls; st.tns = tns;
    init(heap, st);
    CHECK("init tail", rd(0) == hdr(PW - 1, BLUE) && rd(PB) == hdr(PW - 1, BLUE));
    CHECK("init tail", rd(2 * PB) == hdr(2, BLUE));
    CHECK("init tail", same_rec(V(1), rec(FREE, 0, true, 0, 0, 0)));
}

/* ------------------------------------------------------------------------ */
/* Allocation                                                                */
/* ------------------------------------------------------------------------ */

static void test_small(void) {
    fresh(4);

    /* wosize 1: class 0 (2-word slots); page 0 becomes a pool page, slot 0 */
    uint64_t r = alloc(heap, st, 1, White);
    CHECK("small first", r == 8);
    CHECK("small first", rd(0) == hdr(1, WHITE));
    /* 2048 slots, no tail; slot k links to slot k+1's object */
    CHECK("small first", rd(16) == hdr(1, BLUE) && rd(24) == 40);
    CHECK("small first", rd(pg(1) - 16) == hdr(1, BLUE) && rd(pg(1) - 8) == 0);
    CHECK("small first", same_rec(V(0), rec(POOL, 0, true, 24, 2047, 0)));
    CHECK("small first", avail[0] == 1);
    CHECK("small first", rd(pg(1)) == hdr(PW - 1, BLUE) && V(1).code == FREE);

    /* the next one pops slot 1; black, as while marking */
    r = alloc(heap, st, 1, Black);
    CHECK("small black", r == 24);
    CHECK("small black", rd(16) == hdr(1, BLACK));
    CHECK("small black", same_rec(V(0), rec(POOL, 0, true, 40, 2046, 0)));

    /* wosize 0 takes a 2-word slot: its header, then a 1-word blue filler */
    r = alloc(heap, st, 0, White);
    CHECK("wosize 0", r == 40);
    CHECK("wosize 0", rd(32) == hdr(0, WHITE) && rd(40) == hdr(0, BLUE));
    CHECK("wosize 0", same_rec(V(0), rec(POOL, 0, true, 56, 2045, 0)));

    /* wosize 8 (9 words): class 7 (10-word slots), on page 1; a 1-word filler;
     * 409 slots and a 6-word tail filler */
    r = alloc(heap, st, 8, White);
    CHECK("filler", r == pg(1) + 8);
    CHECK("filler", rd(pg(1)) == hdr(8, WHITE) && rd(pg(1) + 72) == hdr(0, BLUE));
    CHECK("filler", rd(pg(1) + 80) == hdr(9, BLUE) && rd(pg(1) + 88) == pg(1) + 168);
    CHECK("filler", rd(pg(1) + 408 * 80) == hdr(9, BLUE) && rd(pg(1) + 408 * 80 + 8) == 0);
    CHECK("filler", rd(pg(1) + 409 * 80) == hdr(5, BLUE));
    CHECK("filler", same_rec(V(1), rec(POOL, 7, true, pg(1) + 88, 408, 0)));
    CHECK("filler", avail[7] == 2 && avail[0] == 1);
}

static void test_large(void) {
    fresh(4);
    put(0, rec(POOL, 0, true, 0, 0, 0));   /* pages 0 and 1 in use */
    put(1, rec(POOL, 0, true, 0, 0, 0));

    /* wosize 200: no listed block, so a new run of one page (page 2); the
     * 3895 words left are one blue block, listed */
    uint64_t r = alloc(heap, st, 200, White);
    uint64_t rest = pg(2) + 201 * 8;
    CHECK("new run", r == pg(2) + 8);
    CHECK("new run", rd(pg(2)) == hdr(200, WHITE));
    CHECK("new run", rd(rest) == hdr(3894, BLUE) && rd(rest + 8) == 0);
    CHECK("new run", large[0] == rest + 8);
    CHECK("new run", same_rec(V(2), rec(HEAD, 1, true, 0, 0, 0)));

    /* wosize 300 is carved from the right of that block, which stays listed */
    r = alloc(heap, st, 300, White);
    uint64_t obj_hd = rest + 3594 * 8;
    CHECK("carve", r == obj_hd + 8);
    CHECK("carve", rd(rest) == hdr(3593, BLUE) && rd(rest + 8) == 0);
    CHECK("carve", rd(obj_hd) == hdr(300, WHITE));
    CHECK("carve", large[0] == rest + 8);

    /* wosize 3500: 3594 words left would leave 93 < lg_min: carved, and the
     * remainder unlinked (the head becomes its link, 0) */
    r = alloc(heap, st, 3500, White);
    CHECK("unlink", r == rest + 93 * 8 + 8);
    CHECK("unlink", rd(rest) == hdr(92, BLUE) && rd(rest + 93 * 8) == hdr(3500, WHITE));
    CHECK("unlink", large[0] == 0);

    /* wosize 5000 needs two free pages; only page 3 is free: nothing changes */
    uint8_t *before = malloc((size_t)heap_size_u64);
    memcpy(before, mem, (size_t)heap_size_u64);
    prec pm_before[MAXP]; memcpy(pm_before, pm, sizeof pm);
    r = alloc(heap, st, 5000, White);
    CHECK("no room", r == 0);
    CHECK("no room", memcmp(before, mem, (size_t)heap_size_u64) == 0);
    CHECK("no room", memcmp(pm_before, pm, sizeof pm) == 0 && large[0] == 0);
    free(before);

    /* wosize 4095 fills page 3 exactly: no rest */
    r = alloc(heap, st, 4095, White);
    CHECK("full page", r == pg(3) + 8 && rd(pg(3)) == hdr(4095, WHITE));
    CHECK("full page", same_rec(V(3), rec(HEAD, 1, true, 0, 0, 0)) && large[0] == 0);

    /* now no free page at all: a small block of a new class fails */
    r = alloc(heap, st, 2, White);
    CHECK("no page", r == 0 && avail[1] == 0);
}

static void test_two_pages(void) {
    fresh(4);
    put(0, rec(POOL, 0, true, 0, 0, 0));
    /* wosize 5000 (5001 words): two pages, 1, 2; 3191 words left, listed */
    uint64_t r = alloc(heap, st, 5000, White);
    CHECK("two pages", r == pg(1) + 8 && rd(pg(1)) == hdr(5000, WHITE));
    CHECK("two pages", rd(pg(1) + 5001 * 8) == hdr(3190, BLUE));
    CHECK("two pages", large[0] == pg(1) + 5001 * 8 + 8);
    CHECK("two pages", same_rec(V(1), rec(HEAD, 2, true, 0, 0, 0)));
    CHECK("two pages", same_rec(V(2), rec(CONT, 0, true, 0, 0, 0)));
}

/* ------------------------------------------------------------------------ */
/* The sweep                                                                 */
/* ------------------------------------------------------------------------ */

/* A pool page of class 0 (2-word slots) whose slots have the given colours
 * (wosize 1 each); the other slots are free. */
static void pool_page(uint64_t i, int n, const int *col) {
    for (uint64_t k = 0; k < PW / 2; k++) {
        uint64_t a = pg(i) + k * 16;
        if ((int)k < n) wr(a, hdr(1, (uint64_t)col[k]));
        else { wr(a, hdr(1, BLUE)); wr(a + 8, 0); }
    }
    put(i, rec(POOL, 0, true, 0, 0, 0));
}

/* A run of `n` pages at `h` holding blocks of the given whole sizes and
 * colours, end to end. */
static void run_pages(uint64_t h, uint64_t n, int m, const uint64_t *w, const int *col) {
    uint64_t a = pg(h);
    for (int k = 0; k < m; k++) { wr(a, hdr(w[k] - 1, (uint64_t)col[k])); a += w[k] * 8; }
    put(h, rec(HEAD, n, true, 0, 0, 0));
    for (uint64_t j = h + 1; j < h + n; j++) put(j, rec(CONT, 0, true, 0, 0, 0));
}

static void test_sweep(void) {
    fresh(8);
    /* page 0: slot 0 black, slot 1 white, the rest free */
    { int col[] = { BLACK, WHITE }; pool_page(0, 2, col); }
    /* page 1: a pool page with no survivor */
    { int col[] = { WHITE, WHITE, WHITE }; pool_page(1, 3, col); }
    /* pages 2-3: a run, a black block of 100 words then white ones */
    { uint64_t w[] = { 100, 50, 2 * PW - 150 }; int col[] = { BLACK, WHITE, WHITE };
      run_pages(2, 2, 3, w, col); }
    /* page 4: a run with nothing black */
    { uint64_t w[] = { PW }; int col[] = { WHITE }; run_pages(4, 1, 1, w, col); }
    /* page 5: a run with two dead stretches that are listed and one that is
     * too small, between black blocks */
    { uint64_t w[] = { 200, 100, 300, 50, 40, 100, PW - 790 };
      int col[] = { WHITE, BLACK, WHITE, BLUE, BLACK, WHITE, BLACK };
      run_pages(5, 1, 7, w, col); }
    /* page 6: free; page 7: a run whose dead tail is too small to list */
    { uint64_t w[] = { PW - 20, 20 }; int col[] = { BLACK, WHITE }; run_pages(7, 1, 2, w, col); }
    avail[0] = 1;            /* stale lists, which the sweep clears */
    large[0] = pg(6) + 8;

    sweep(heap, st);

    /* page 0: slot 0 white; slots 1..2047 free, each linked to the one
     * before it, slot 1 to nothing; the list head is the last slot */
    CHECK("pool", rd(pg(0)) == hdr(1, WHITE));
    CHECK("pool", rd(16) == hdr(1, BLUE) && rd(24) == 0);
    CHECK("pool", rd(32) == hdr(1, BLUE) && rd(40) == 24);
    CHECK("pool", rd(pg(1) - 16) == hdr(1, BLUE) && rd(pg(1) - 8) == pg(1) - 32 + 8);
    CHECK("pool", same_rec(V(0), rec(POOL, 0, true, pg(1) - 8, 2047, 0)));
    CHECK("pool", avail[0] == 1);
    for (int c = 1; c < NCLS; c++) CHECK("pool", avail[c] == 0);
    /* page 1: given back */
    CHECK("empty pool", rd(pg(1)) == hdr(PW - 1, BLUE) && same_rec(V(1), rec(FREE, 0, true, 0, 0, 0)));
    /* pages 2-3: the survivor; the dead stretch [100, 2 pages) is the piece
     * before page 3, 3996 words and listed, and page 3 given back */
    uint64_t pre = pg(2) + 800;
    CHECK("run", rd(pg(2)) == hdr(99, WHITE));
    CHECK("run", rd(pre) == hdr(3995, BLUE));
    CHECK("run", rd(pg(3)) == hdr(PW - 1, BLUE) && same_rec(V(3), rec(FREE, 0, true, 0, 0, 0)));
    CHECK("run", same_rec(V(2), rec(HEAD, 1, true, 0, 0, 0)));
    /* page 4: given back */
    CHECK("dead run", rd(pg(4)) == hdr(PW - 1, BLUE) && same_rec(V(4), rec(FREE, 0, true, 0, 0, 0)));
    /* page 5: [200 dead][100 black][300 + 50 dead, merged][40 black][100 dead]
     * [3306 black]: blocks of 200 and 350 words are listed, 100 is not */
    uint64_t p5 = pg(5);
    CHECK("merge", rd(p5) == hdr(199, BLUE));
    CHECK("merge", rd(p5 + 200 * 8) == hdr(99, WHITE));
    CHECK("merge", rd(p5 + 300 * 8) == hdr(349, BLUE));
    CHECK("merge", rd(p5 + 650 * 8) == hdr(39, WHITE));
    CHECK("merge", rd(p5 + 690 * 8) == hdr(99, BLUE));
    CHECK("merge", rd(p5 + 790 * 8) == hdr(PW - 791, WHITE));
    CHECK("merge", same_rec(V(5), rec(HEAD, 1, true, 0, 0, 0)));
    /* page 7: its 20-word tail is too small to list */
    CHECK("small piece", rd(pg(7)) == hdr(PW - 21, WHITE) && rd(pg(7) + (PW - 20) * 8) == hdr(19, BLUE));
    CHECK("small piece", same_rec(V(7), rec(HEAD, 1, true, 0, 0, 0)));
    /* page 6 stays free */
    CHECK("free page", same_rec(V(6), rec(FREE, 0, true, 0, 0, 0)));
    /* list 0, in the order the units are swept, each run's blocks in address
     * order in front of the list so far: page 5's two blocks, then page 2's */
    CHECK("list", large[0] == p5 + 8);
    CHECK("list", rd(p5 + 8) == p5 + 300 * 8 + 8);
    CHECK("list", rd(p5 + 300 * 8 + 8) == pre + 8);
    CHECK("list", rd(pre + 8) == 0);
    for (int k = 1; k < NL; k++) CHECK("list", large[k] == 0);
}

/* The sweep, then an allocation from what it freed. */
static void test_sweep_then_alloc(void) {
    fresh(2);
    { int col[] = { WHITE, BLACK }; pool_page(0, 2, col); }
    { uint64_t w[] = { PW }; int col[] = { WHITE }; run_pages(1, 1, 1, w, col); }
    sweep(heap, st);
    /* slot 0 is the only free slot before slot 1; the list head is the last */
    CHECK("cycle sweep", same_rec(V(0), rec(POOL, 0, true, pg(1) - 8, 2047, 0)));
    CHECK("cycle sweep", V(1).code == FREE && large[0] == 0);
    uint64_t r = alloc(heap, st, 1, White);
    CHECK("cycle alloc", r == pg(1) - 8 && rd(pg(1) - 16) == hdr(1, WHITE));
    CHECK("cycle alloc", V(0).free_head == pg(1) - 24 && V(0).nfree == 2046);
    r = alloc(heap, st, 1000, White);
    CHECK("cycle alloc", r == pg(1) + 8 && same_rec(V(1), rec(HEAD, 1, true, 0, 0, 0)));
}

int main(void) {
    mem = calloc((size_t)(MAXP * PB), 1);
    if (!mem) { perror("calloc"); return 1; }
    test_init_tail();
    test_small();
    test_large();
    test_two_pages();
    test_sweep();
    test_sweep_then_alloc();
    free(mem);
    if (failures) { printf("pages: %d of %d checks FAILED\n", failures, checks); return 1; }
    printf("pages: all %d checks passed\n", checks);
    return 0;
}
