/* alloc_pages.c — B: an OCaml 5-style allocator for our collector
 * (docs/allocator-comparison.md, sections 3 and 6.1).  Unverified; for
 * measurement only.
 *
 * Layout.  The major heap is the same calloc region.  It is divided into
 * pages of 4096 words (32 KB) counted from zero_addr; the words after the
 * last whole page are a tail that is never used.  A side table pm[] says
 * what each page is:
 *   K_FREE   a free page: one blue block of wosize 4095;
 *   K_POOL   a pool of class c: slots of cls_wh[c] words from the page start,
 *            then a filler for the 4096 mod cls_wh[c] words left;
 *   K_LARGE  the first page of a large run of pm[].run pages, K_LCONT the
 *            others: objects of whsize > 257, managed like A's list 0 (first
 *            fit, right-justified, coalescing that stops at the run's edges).
 * Pages [hwm, npages) and the tail have never been used and are covered by
 * one blue block (the wilderness), so untouched memory stays untouched.
 *
 * The heap stays tiled by headers at all times: a free slot is one blue
 * block of the slot's size; an object smaller than its slot is followed by a
 * blue filler; fillers are on no list.  So the extracted, verified mark and
 * Cheney collection run unchanged, and the verified sweep can be run on a
 * copy of this heap as the oracle (proto_check.c).
 *
 * Sweep.  For each pool page, slot by slot: a black slot start becomes white;
 * anything else becomes a blue slot on the page's list.  A page with no live
 * slot becomes free; one with free slots goes on avail[c].  Large runs are
 * swept by walking them and coalescing each maximal run of non-black blocks;
 * an empty run gives its pages back.  The eager sweep does this in address
 * order; the parallel one gives each thread a contiguous range of pages and
 * joins by concatenating lists; the incremental one sweeps one page per step
 * (a large run is one step), and an allocation sweeps at most one page of its
 * class before taking a free page (OCaml 5's pool_find). */
#include "proto.h"
#include <stdlib.h>
#include <string.h>

#define PG_WORDS     4096ULL
#define PG_BYTES     (PG_WORDS * 8ULL)
#define NCLS         40
#define MAX_SMALL_WH 257ULL
#define NIL          UINT32_MAX

/* gen_sizeclasses.ml with max_slot = 257 (the note, section 3.1), whsize. */
static const uint32_t cls_wh[NCLS] = {
    1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 17, 19, 22, 25, 28, 32, 36, 40,
    45, 51, 57, 63, 70, 78, 87, 96, 105, 114, 126, 141, 153, 167, 183, 204,
    216, 229, 245, 257};
static uint8_t  cls_of[MAX_SMALL_WH + 1];     /* whsize -> class */
static uint32_t cls_ns[NCLS], cls_tail[NCLS]; /* slots per page, tail words */

enum { K_FREE = 0, K_POOL = 1, K_LARGE = 2, K_LCONT = 3 };

typedef struct {
    uint64_t free_head;   /* first free slot (field address), 0 = none */
    uint32_t next;        /* next page on avail[cls] */
    uint32_t nfree;       /* free slots */
    uint32_t run;         /* K_LARGE: pages in the run */
    uint8_t  kind, cls, swept, pad;
} page_t;

/* Lists a sweep builds: per class, the pages with a free slot, in ascending
 * order; the large run's free blocks; the lowest page freed. */
typedef struct {
    uint32_t av_h[NCLS], av_t[NCLS];
    uint64_t lg_h, lg_t;  /* lg_t: the first block pushed (its link ends the list) */
    uint32_t min_free;
    uint32_t pages_used;
} lists_t;

static page_t  *pm;
static uint32_t npages, hwm, free_hint;  /* no free page below free_hint */
static uint64_t Z, HS, tail_words;
static lists_t  G;                       /* the allocator's lists */

/* stats */
static uint64_t st_small, st_req_words, st_slot_words, st_large, st_pool_inits;
static uint64_t st_large_grow, st_max_pages_used, st_unit_sweeps;

static inline uint64_t pa(uint32_t p) { return Z + (uint64_t)p * PG_BYTES; }

static void lists_clear(lists_t *L) {
    for (int c = 0; c < NCLS; c++) L->av_h[c] = L->av_t[c] = NIL;
    L->lg_h = L->lg_t = 0;
    L->min_free = NIL;
    L->pages_used = 0;
}

static inline void av_append(lists_t *L, uint32_t c, uint32_t p) {
    pm[p].next = NIL;
    if (L->av_t[c] == NIL) L->av_h[c] = p; else pm[L->av_t[c]].next = p;
    L->av_t[c] = p;
}

static inline void av_push_front(uint32_t c, uint32_t p) {
    pm[p].next = G.av_h[c];
    G.av_h[c] = p;
    if (G.av_t[c] == NIL) G.av_t[c] = p;
}

static inline void lg_push(lists_t *L, uint64_t f) {
    PW(f) = L->lg_h;
    L->lg_h = f;
    if (L->lg_t == 0) L->lg_t = f;
}

/* The blue block over the pages never used, and the tail. */
static void wild_fix(void) {
    if (hwm < npages)
        PW(pa(hwm)) = MK_BLUE((uint64_t)(npages - hwm) * PG_WORDS + tail_words - 1);
    else if (tail_words > 0)
        PW(pa(npages)) = MK_BLUE(tail_words - 1);
}

static uint32_t take_free_page(void) {
    uint32_t p = free_hint;
    while (p < hwm && pm[p].kind != K_FREE) p++;
    if (p < hwm) { free_hint = p + 1; return p; }
    free_hint = hwm;
    if (hwm < npages) {
        p = hwm++;
        wild_fix();
        free_hint = hwm;
        pm[p].kind = K_FREE;
        return p;
    }
    return NIL;
}

static void pool_init(uint32_t p, uint32_t c) {
    uint64_t base = pa(p), wh = cls_wh[c], ns = cls_ns[c], step = wh * 8;
    uint64_t hb = MK_BLUE(wh - 1), s = base;
    for (uint64_t j = 0; j + 1 < ns; j++, s += step) {
        PW(s) = hb;
        PW(s + 8) = s + step + 8;
    }
    PW(s) = hb;
    PW(s + 8) = 0;
    if (cls_tail[c]) PW(base + ns * step) = MK_BLUE(cls_tail[c] - 1);
    page_t *g = &pm[p];
    g->free_head = base + 8;
    g->next = NIL;
    g->nfree = (uint32_t)ns;
    g->run = 0;
    g->kind = K_POOL;
    g->cls = (uint8_t)c;
    g->swept = 1;
    st_pool_inits++;
}

/* ---- sweeping one unit --------------------------------------------------- */

/* Returns 1 if the page became free. */
static int sweep_pool(uint32_t p, lists_t *L) {
    page_t *g = &pm[p];
    uint32_t c = g->cls;
    uint64_t wh = cls_wh[c], ns = cls_ns[c], step = wh * 8;
    uint64_t base = pa(p), hb = MK_BLUE(wh - 1), head = 0;
    uint32_t nfree = 0;
    uint64_t j = ns;
    if (proto_check_control) j--;   /* control mutant: never looks at the last slot */
    while (j-- > 0) {
        uint64_t s = base + j * step, h = PW(s);
        if (IS_BLACK(h)) {
            PW(s) = WHITEN(h);
        } else {
            PW(s) = hb;
            PW(s + 8) = head;
            head = s + 8;
            nfree++;
        }
    }
    g->swept = 1;
    if (nfree == ns) {
        PW(base) = MK_BLUE(PG_WORDS - 1);
        g->kind = K_FREE;
        g->free_head = 0;
        g->nfree = 0;
        if (p < L->min_free) L->min_free = p;
        return 1;
    }
    g->free_head = head;
    g->nfree = nfree;
    L->pages_used++;
    if (nfree) av_append(L, c, p);
    return 0;
}

static inline void lg_flush(lists_t *L, uint64_t rs, uint64_t rw) {
    PW(rs) = MK_BLUE(rw - 1);
    if (rw >= 2) lg_push(L, rs + 8);
}

/* Returns 1 if the run became free pages. */
static int sweep_large(uint32_t p, lists_t *L) {
    uint32_t k = pm[p].run;
    uint64_t cur = pa(p), e = pa(p + k), rs = 0, rw = 0;
    int live = 0;
    while (cur < e) {
        uint64_t h = PW(cur), next = cur + (HD_WZ(h) + 1) * 8;
        if (IS_BLACK(h)) {
            if (rw) lg_flush(L, rs, rw);
            rw = 0;
            PW(cur) = WHITEN(h);
            live = 1;
        } else {
            if (rw == 0) rs = cur;
            rw += HD_WZ(h) + 1;
        }
        cur = next;
    }
    for (uint32_t q = p; q < p + k; q++) pm[q].swept = 1;
    if (!live) {
        for (uint32_t q = p; q < p + k; q++) {
            PW(pa(q)) = MK_BLUE(PG_WORDS - 1);
            pm[q].kind = K_FREE;
            pm[q].run = 0;
        }
        if (p < L->min_free) L->min_free = p;
        return 1;
    }
    if (rw) lg_flush(L, rs, rw);
    L->pages_used += k;
    return 0;
}

static void sweep_range(uint32_t lo, uint32_t hi, lists_t *L) {
    uint32_t p = lo;
    while (p < hi && pm[p].kind == K_LCONT) p++;   /* run owned by the range below */
    while (p < hi) {
        switch (pm[p].kind) {
        case K_POOL:
            sweep_pool(p, L);
            p++;
            break;
        case K_LARGE: {
            uint32_t k = pm[p].run;
            sweep_large(p, L);
            p += k;
            break;
        }
        default:
            if (pm[p].kind == K_FREE && p < L->min_free) L->min_free = p;
            p++;
        }
    }
}

/* Install the lists of n parts swept in address order.  Avail lists are
 * concatenated in ascending order and the large lists in descending order,
 * so a parallel sweep leaves exactly what the sequential one does. */
static void lists_install(lists_t *parts, int n) {
    for (int c = 0; c < NCLS; c++) {
        G.av_h[c] = G.av_t[c] = NIL;
        for (int i = 0; i < n; i++) {
            if (parts[i].av_h[c] == NIL) continue;
            if (G.av_t[c] == NIL) G.av_h[c] = parts[i].av_h[c];
            else pm[G.av_t[c]].next = parts[i].av_h[c];
            G.av_t[c] = parts[i].av_t[c];
        }
    }
    G.lg_h = G.lg_t = 0;
    uint64_t tail = 0;
    uint32_t mf = NIL, used = 0;
    for (int i = n - 1; i >= 0; i--) {
        if (parts[i].lg_h) {
            if (tail) PW(tail) = parts[i].lg_h; else G.lg_h = parts[i].lg_h;
            tail = parts[i].lg_t;
        }
    }
    for (int i = 0; i < n; i++) {
        if (parts[i].min_free < mf) mf = parts[i].min_free;
        used += parts[i].pages_used;
    }
    free_hint = mf == NIL ? hwm : mf;
    G.min_free = NIL;
    if (used > st_max_pages_used) st_max_pages_used = used;
}

/* ---- incremental sweep --------------------------------------------------- */
static int      sweeping;
static uint32_t cursor;
static uint64_t inc_total, inc_done;   /* pages to sweep this cycle, swept */
static uint32_t *ua_next;              /* unswept pages of a class with a free slot */
static uint32_t ua_head[NCLS];
static uint64_t freed_units;           /* units that gave pages back */

static void incr_close(void) {
    sweeping = 0;
    uint32_t used = 0;
    for (uint32_t p = 0; p < hwm; p++)
        if (pm[p].kind == K_POOL || pm[p].kind == K_LARGE || pm[p].kind == K_LCONT) used++;
    if (used > st_max_pages_used) st_max_pages_used = used;
#ifdef VERGC_PROTO_CHECK
    chk_sweep_closed("when B's incremental sweep closed");
    impl_check("when B's incremental sweep closed");
#endif
}

static void incr_start(void) {
    lists_clear(&G);
    for (int c = 0; c < NCLS; c++) ua_head[c] = NIL;
    inc_total = inc_done = 0;
    for (uint32_t p = hwm; p-- > 0;) {
        page_t *g = &pm[p];
        if (g->kind == K_POOL) {
            g->swept = 0;
            inc_total++;
            if (g->nfree > 0) { ua_next[p] = ua_head[g->cls]; ua_head[g->cls] = p; }
        } else if (g->kind == K_LARGE) {
            for (uint32_t q = p; q < p + g->run; q++) pm[q].swept = 0;
            inc_total += g->run;
        }
    }
    cursor = 0;
    sweeping = 1;
    if (inc_total == 0) incr_close();
}

/* Sweep the unit at p (an unswept pool page or large run start). */
static void incr_unit(uint32_t p) {
    uint32_t pages = pm[p].kind == K_LARGE ? pm[p].run : 1;
#ifdef VERGC_PROTO_CHECK
    chk_unit_pre(pa(p), pa(p + pages));
#endif
    int freed = pm[p].kind == K_LARGE ? sweep_large(p, &G) : sweep_pool(p, &G);
    st_unit_sweeps++;
    inc_done += pages;
    if (freed) freed_units++;
    if (G.min_free < free_hint) free_hint = G.min_free;
    G.min_free = NIL;
#ifdef VERGC_PROTO_CHECK
    chk_unit_post("after B's incremental sweep of a unit", 1);
#endif
}

/* One step: the next unswept unit at the cursor; closes the sweep at the end. */
static void incr_step(void) {
    while (cursor < hwm) {
        page_t *g = &pm[cursor];
        if ((g->kind == K_POOL || g->kind == K_LARGE) && !g->swept) {
            uint32_t p = cursor;
            cursor += g->kind == K_LARGE ? g->run : 1;
            incr_unit(p);
            return;
        }
        cursor++;
    }
    incr_close();
}

int    impl_sweeping(void) { return sweeping; }
void   impl_slice(void) { if (sweeping) incr_step(); }       /* one page = 4096 words */
double impl_swept_fraction(void) { return inc_total ? (double)inc_done / (double)inc_total : 1.0; }
void   impl_finish(void) { while (sweeping) incr_step(); }

/* ---- allocation ---------------------------------------------------------- */

static uint32_t refill(uint32_t c) {
    if (sweeping) {
        /* OCaml 5's pool_find: an unswept page of this class that had a free
         * slot when the cycle started still has one, so one sweep suffices. */
        while (ua_head[c] != NIL) {
            uint32_t p = ua_head[c];
            ua_head[c] = ua_next[p];
            if (pm[p].kind != K_POOL || pm[p].swept) continue;
            proto_sweep_work_begin(PK_ALLOC);
            incr_unit(p);
            proto_sweep_work_end(PK_ALLOC);
            if (G.av_h[c] != NIL) return G.av_h[c];
        }
    }
    uint32_t p = take_free_page();
    if (p == NIL && sweeping) {
        /* No free page: sweep on until this class has a slot or a page is
         * freed (the exception in the note, section 4.2). */
        uint64_t f0 = freed_units;
        proto_sweep_work_begin(PK_ALLOC);
        while (sweeping && G.av_h[c] == NIL && freed_units == f0) incr_step();
        proto_sweep_work_end(PK_ALLOC);
        if (G.av_h[c] != NIL) return G.av_h[c];
        p = take_free_page();
    }
    if (p == NIL) return NIL;
    pool_init(p, c);
    av_push_front(c, p);
    return p;
}

static uint64_t alloc_small(uint64_t wz) {
    uint64_t whs = wz + 1;
    uint32_t c = cls_of[whs];
    uint32_t p = G.av_h[c];
    if (p == NIL && (p = refill(c)) == NIL) return 0;
    page_t *g = &pm[p];
    uint64_t f = g->free_head;
    g->free_head = PW(f);
    if (--g->nfree == 0) {
        G.av_h[c] = g->next;
        if (G.av_h[c] == NIL) G.av_t[c] = NIL;
        g->next = NIL;
    }
    uint64_t h = f - 8, wh = cls_wh[c];
    PW(h) = wz << 10;
    if (wh > whs) PW(h + whs * 8) = MK_BLUE(wh - whs - 1);
    st_small++;
    st_req_words += whs;
    st_slot_words += wh;
    return f;
}

/* First fit on the large list, carving right-justified (A's list 0). */
static uint64_t lg_fit(uint64_t wz) {
    uint64_t prev = 0, cur = G.lg_h;
    while (cur) {
        uint64_t h = cur - 8, bw = HD_WZ(PW(h)), next = PW(cur);
        if (bw >= wz) {
            uint64_t left = bw - wz, ah = h + left * 8;
            if (left >= 2) {
                PW(h) = MK_BLUE(left - 1);
            } else {
                if (prev) PW(prev) = next; else G.lg_h = next;
                if (left == 1) PW(h) = MK_BLUE(0);
            }
            PW(ah) = wz << 10;
            return ah + 8;
        }
        prev = cur;
        cur = next;
    }
    return 0;
}

/* A new large run: the first k consecutive free pages (the wilderness
 * counts as free), pushed as one blue block. */
static int lg_grow(uint64_t wz) {
    uint64_t k = (wz + 1 + PG_WORDS - 1) / PG_WORDS;
    uint32_t s = 0, run = 0, p;
    for (p = free_hint; p < npages; p++) {
        if (p >= hwm || pm[p].kind == K_FREE) {
            if (run == 0) s = p;
            if (++run == k) break;
        } else {
            run = 0;
        }
    }
    if (run < k) return 0;
    for (uint32_t q = s; q < s + k; q++) {
        pm[q].kind = K_LCONT;
        pm[q].next = NIL;
        pm[q].swept = 1;
        pm[q].run = 0;
        pm[q].free_head = 0;
        pm[q].nfree = 0;
    }
    pm[s].kind = K_LARGE;
    pm[s].run = (uint32_t)k;
    if (s + k > hwm) { hwm = s + (uint32_t)k; wild_fix(); }
    if (free_hint == s) free_hint = s + (uint32_t)k;
    PW(pa(s)) = MK_BLUE(k * PG_WORDS - 1);
    PW(pa(s) + 8) = G.lg_h;
    G.lg_h = pa(s) + 8;
    st_large_grow++;
    return 1;
}

static uint64_t alloc_large(uint64_t wz) {
    uint64_t r = lg_fit(wz);
    if (r == 0 && lg_grow(wz)) r = lg_fit(wz);
    if (r == 0 && sweeping) {
        proto_sweep_work_begin(PK_ALLOC);
        while (r == 0 && sweeping) {
            uint64_t f0 = freed_units;
            uint64_t l0 = G.lg_h;
            incr_step();
            if (G.lg_h != l0) r = lg_fit(wz);
            if (r == 0 && freed_units != f0 && lg_grow(wz)) r = lg_fit(wz);
        }
        proto_sweep_work_end(PK_ALLOC);
    }
    if (r) st_large++;
    return r;
}

uint64_t vergc_proto_allocate(heap_t heap, uint64_t *heads, uint64_t *tbl, uint64_t wz) {
    (void)heap; (void)heads; (void)tbl;
    uint64_t r = wz + 1 <= MAX_SMALL_WH ? alloc_small(wz) : alloc_large(wz);
#ifdef VERGC_PROTO_CHECK
    if (r && sweeping) chk_note_alloc(r - 8);
#endif
    return r;
}

/* ---- the sweep hook ------------------------------------------------------ */
static lists_t parts[MAX_CHUNKS];
static int     n_chunks;

/* Chunk c of n_chunks: an equal share of the pages, in address order. */
static void par_chunk(int c) {
    uint32_t lo = (uint32_t)((uint64_t)hwm * c / n_chunks);
    uint32_t hi = (uint32_t)((uint64_t)hwm * (c + 1) / n_chunks);
    lists_clear(&parts[c]);
    sweep_range(lo, hi, &parts[c]);
}

void vergc_proto_sweep(heap_t heap, uint64_t *heads, uint64_t *tbl) {
    (void)heap; (void)heads; (void)tbl;
#ifdef VERGC_PROTO_CHECK
    chk_oracle();
#endif
    if (proto_mode == SW_INCR) { incr_start(); return; }
    uint64_t t0 = proto_now();
    int n = proto_mode == SW_PAR ? proto_threads : 1;
    if (n == 1) {
        n_chunks = 1;
        lists_clear(&parts[0]);
        sweep_range(0, hwm, &parts[0]);
    } else {
        n_chunks = n * CHUNKS_PER_THREAD;
        proto_pool_chunks(n, n_chunks, par_chunk);
    }
    lists_install(parts, n_chunks);
    proto_record_eager_sweep(proto_now() - t0);
#ifdef VERGC_PROTO_CHECK
    chk_compare_eager("after B's sweep", 0);
    impl_check("after B's sweep");
#endif
}

/* ---- setup and stats ----------------------------------------------------- */
const char *impl_name(void) { return "B"; }

/* Words B uses per word requested, so far: rounding up to a size class.
 * The bridge's collection trigger counts requested words; scaled by this it
 * counts what B consumes (docs/allocator-comparison-results.md, section 2). */
double impl_consumption(void) {
    return st_req_words ? (double)st_slot_words / (double)st_req_words : 1.0;
}

void impl_init(void) {
    Z = zero_addr;
    HS = heap_size_u64;
    uint64_t words = (HS - Z) / 8;
    npages = (uint32_t)(words / PG_WORDS);
    tail_words = words % PG_WORDS;
    if (npages < 2) { fprintf(stderr, "B: heap smaller than two pages\n"); exit(2); }
    pm = (page_t *)calloc((size_t)npages + 1, sizeof(page_t));
    ua_next = (uint32_t *)calloc((size_t)npages + 1, sizeof(uint32_t));
    if (!pm || !ua_next) { fprintf(stderr, "B: calloc page map\n"); exit(2); }
    for (int c = 0; c < NCLS; c++) {
        cls_ns[c] = (uint32_t)(PG_WORDS / cls_wh[c]);
        cls_tail[c] = (uint32_t)(PG_WORDS - (uint64_t)cls_ns[c] * cls_wh[c]);
    }
    for (uint64_t wh = 2, c = 1; wh <= MAX_SMALL_WH; wh++) {
        while (cls_wh[c] < wh) c++;
        cls_of[wh] = (uint8_t)c;
    }
    hwm = 0;
    free_hint = 0;
    wild_fix();
    lists_clear(&G);
}

void impl_stats(FILE *f) {
    fprintf(f, " small_allocs=%llu req_words=%llu slot_words=%llu large_allocs=%llu"
               " pool_inits=%llu large_grows=%llu unit_sweeps=%llu max_pages_used=%llu"
               " max_used_words=%llu pages=%u hwm=%u",
            (unsigned long long)st_small, (unsigned long long)st_req_words,
            (unsigned long long)st_slot_words, (unsigned long long)st_large,
            (unsigned long long)st_pool_inits, (unsigned long long)st_large_grow,
            (unsigned long long)st_unit_sweeps, (unsigned long long)st_max_pages_used,
            (unsigned long long)(st_max_pages_used * PG_WORDS), npages, hwm);
}

/* ---- invariant checker (pages_ok and the lists), check builds ----------- */
#ifdef VERGC_PROTO_CHECK
static uint8_t *ck_seen;      /* one bit per heap word */
static uint8_t *ck_onlist;    /* one byte per page */

static inline int bit_test_set(uint8_t *bm, uint64_t a) {
    uint64_t w = (a - Z) / 8;
    int was = (bm[w >> 3] >> (w & 7)) & 1;
    bm[w >> 3] |= (uint8_t)(1u << (w & 7));
    return was;
}

void impl_check(const char *where) {
    uint64_t words = (HS - Z) / 8;
    if (!ck_seen) {
        ck_seen = (uint8_t *)calloc((size_t)(words / 8 + 1), 1);
        ck_onlist = (uint8_t *)calloc((size_t)npages + 1, 1);
        if (!ck_seen || !ck_onlist) { fprintf(stderr, "B check: calloc\n"); abort(); }
    }
    memset(ck_seen, 0, (size_t)(words / 8 + 1));
    memset(ck_onlist, 0, (size_t)npages + 1);
    chk_walk(where, Z, HS);
    /* avail lists: pool pages of the class, swept, with a free slot, once */
    for (uint32_t c = 0; c < NCLS; c++) {
        uint32_t steps = 0, last = NIL;
        for (uint32_t p = G.av_h[c]; p != NIL; p = pm[p].next) {
            if (p >= hwm || pm[p].kind != K_POOL || pm[p].cls != c)
                chk_fail(where, "avail page is not a pool of its class", p, c);
            if (!pm[p].swept) chk_fail(where, "avail page is unswept", p, c);
            if (pm[p].nfree == 0) chk_fail(where, "avail page has no free slot", p, c);
            if (ck_onlist[p]++) chk_fail(where, "page on avail twice", p, c);
            if (++steps > npages) chk_fail(where, "avail list does not end", p, c);
            last = p;
        }
        if (last != G.av_t[c]) chk_fail(where, "avail tail is not the last page", last, c);
    }
    if (hwm < npages && PW(pa(hwm)) != MK_BLUE((uint64_t)(npages - hwm) * PG_WORDS + tail_words - 1))
        chk_fail(where, "wilderness header", hwm, PW(pa(hwm)));
    if (free_hint > hwm) chk_fail(where, "free hint above hwm", free_hint, hwm);
    for (uint32_t p = 0; p < hwm;) {
        page_t *g = &pm[p];
        uint64_t base = pa(p);
        if (p < free_hint && g->kind == K_FREE) chk_fail(where, "free page below the free hint", p, free_hint);
        if (g->kind == K_FREE) {
            if (PW(base) != MK_BLUE(PG_WORDS - 1)) chk_fail(where, "free page header", p, PW(base));
            p++;
            continue;
        }
        if (g->kind == K_LCONT) chk_fail(where, "large continuation page without its run start", p, 0);
        if (g->kind == K_LARGE) {
            uint32_t k = g->run;
            if (k == 0 || p + k > hwm) chk_fail(where, "large run length", p, k);
            for (uint32_t q = p + 1; q < p + k; q++)
                if (pm[q].kind != K_LCONT) chk_fail(where, "large run page kind", q, pm[q].kind);
            chk_walk(where, base, pa(p + k));
            if (g->swept)
                for (uint64_t cur = base; cur < pa(p + k); cur += (HD_WZ(PW(cur)) + 1) * 8)
                    if (IS_BLACK(PW(cur))) chk_fail(where, "black block in a swept large run", p, cur);
            p += k;
            continue;
        }
        /* K_POOL */
        uint32_t c = g->cls;
        uint64_t wh = cls_wh[c], ns = cls_ns[c], step = wh * 8, hb = MK_BLUE(wh - 1);
        if (c == 0 || c >= NCLS) chk_fail(where, "pool class", p, c);
        uint32_t blue_slots = 0;
        for (uint64_t j = 0; j < ns; j++) {
            uint64_t s = base + j * step, h = PW(s);
            chk_walk(where, s, s + step);   /* the walk from a slot start stays in the slot */
            if (IS_BLUE(h)) {
                if (h != hb) chk_fail(where, "blue slot of the wrong size", p, s);
                blue_slots++;
            } else if (g->swept && IS_BLACK(h)) {
                chk_fail(where, "black slot in a swept page", p, s);
            }
        }
        if (cls_tail[c]) {
            uint64_t t = base + ns * step;
            if (PW(t) != MK_BLUE(cls_tail[c] - 1)) chk_fail(where, "page tail filler", p, PW(t));
        }
        uint32_t n = 0;
        for (uint64_t f = g->free_head; f; f = PW(f)) {
            uint64_t s = f - 8;
            if (s < base || s >= base + ns * step || (s - base) % step != 0)
                chk_fail(where, "free slot is not a slot start of its page", p, f);
            if (PW(s) != hb) chk_fail(where, "listed slot is not blue", p, f);
            if (bit_test_set(ck_seen, s)) chk_fail(where, "slot listed twice", p, f);
            if (++n > ns) chk_fail(where, "slot list does not end", p, f);
        }
        if (n != g->nfree) chk_fail(where, "free count differs from the list", p, n);
        if (n != blue_slots) chk_fail(where, "a blue slot is on no list", p, blue_slots);
        if (g->swept && n > 0 && !ck_onlist[p]) chk_fail(where, "swept page with a free slot is not on avail", p, c);
        if (!g->swept && ck_onlist[p]) chk_fail(where, "unswept page on avail", p, c);
        p++;
    }
    /* the large list: blue blocks in swept large runs, once; when no sweep is
     * open, every blue block of wosize >= 1 in a large run is listed */
    uint64_t listed = 0, steps = 0;
    for (uint64_t f = G.lg_h; f; f = PW(f)) {
        uint64_t s = f - 8, h = PW(s);
        if (s < Z || s >= pa(hwm)) chk_fail(where, "large cell outside the used pages", s, 0);
        uint32_t p = (uint32_t)((s - Z) / PG_BYTES);
        while (pm[p].kind == K_LCONT) p--;
        if (pm[p].kind != K_LARGE || !pm[p].swept) chk_fail(where, "large cell outside a swept run", s, p);
        if (!IS_BLUE(h) || HD_WZ(h) == 0) chk_fail(where, "large cell is not a blue block", s, h);
        if (bit_test_set(ck_seen, s)) chk_fail(where, "large cell listed twice", s, 0);
        listed++;
        if (++steps > (HS - Z) / 16) chk_fail(where, "large list does not end", s, 0);
    }
    if (!sweeping) {
        uint64_t blue = 0;
        for (uint32_t p = 0; p < hwm; p++) {
            if (pm[p].kind != K_LARGE) continue;
            for (uint64_t cur = pa(p); cur < pa(p + pm[p].run); cur += (HD_WZ(PW(cur)) + 1) * 8)
                if (IS_BLUE(PW(cur)) && HD_WZ(PW(cur)) >= 1) blue++;
        }
        if (blue != listed) chk_fail(where, "a blue block in a large run is on no list", blue, listed);
    }
}
#else
void impl_check(const char *where) { (void)where; }
#endif
