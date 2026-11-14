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

/* Variants (docs/allocator-comparison-results.md, section 9), chosen at build
 * time:
 *   VERGC_B_VARIANT=1  B: the note's 40 classes up to 257 words; no pool
 *                      header; large runs as above.
 *   VERGC_B_VARIANT=2  B2, OCaml 5 as it is: its 32 classes (runtime/caml/
 *                      sizeclasses.h) for whsize <= 128; each pool starts with
 *                      OCaml 5's 4-word pool header and the class's wastage (a
 *                      blue filler here, the page map being on the side); larger
 *                      blocks in the large-object area (LARGE_AREA below).
 *   VERGC_B_VARIANT=3  B3: as B2, but exact classes for whsize 1..16 and then
 *                      classes about 12% apart up to 128, and each class
 *                      allocates from its lowest-address page with a free slot
 *                      (LOWEST_FIRST).
 *   PG_WORDS_CFG       page size in words (default 4096, 32 KB).
 *
 * LARGE_AREA.  Large blocks are carved at their exact size from free blocks
 * on one first-fit list (A's list 0), as in B; in addition a new run joins a
 * swept large run next to it, so free blocks merge across what were run
 * edges; and the sweep gives every whole free page inside a run back to the
 * free pages, splitting the run, as freeing a large block does in OCaml 5. */
#ifndef VERGC_B_VARIANT
#define VERGC_B_VARIANT 1
#endif
#ifndef PG_WORDS_CFG
#define PG_WORDS_CFG 4096
#endif
#define PG_WORDS     ((uint64_t)PG_WORDS_CFG)
#define PG_BYTES     (PG_WORDS * 8ULL)
#define NIL          UINT32_MAX

#if VERGC_B_VARIANT == 1
#define NCLS         40
#define MAX_SMALL_WH 257ULL
#define POOL_HDR     0
/* gen_sizeclasses.ml with max_slot = 257 (the note, section 3.1), whsize.
 * B_CLASS_129 (diagnostic build B-129): the class 141 becomes 129, so that
 * binarytrees' 129-word arrays fill their slots exactly. */
#ifdef B_CLASS_129
#define CLS_141 129
#else
#define CLS_141 141
#endif
static const uint32_t cls_wh[NCLS] = {
    1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 17, 19, 22, 25, 28, 32, 36, 40,
    45, 51, 57, 63, 70, 78, 87, 96, 105, 114, 126, CLS_141, 153, 167, 183, 204,
    216, 229, 245, 257};
#elif VERGC_B_VARIANT == 2
#define NCLS         32
#define MAX_SMALL_WH 128ULL
#define POOL_HDR     4
#define LARGE_AREA   1
/* OCaml 5's wsize_sizeclass (whsize, header included). */
static const uint32_t cls_wh[NCLS] = {
    1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 17, 19, 22, 25, 28, 32, 33, 37, 42,
    47, 53, 59, 65, 73, 81, 89, 99, 108, 118, 128};
#elif VERGC_B_VARIANT == 3
#define NCLS         35
#define MAX_SMALL_WH 128ULL
#define POOL_HDR     4
#define LARGE_AREA   1
#define LOWEST_FIRST 1
/* Exact to 16, then each about 12% above the last (rounded), capped at 128. */
static const uint32_t cls_wh[NCLS] = {
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    18, 20, 22, 25, 28, 31, 35, 39, 44, 49, 55, 62, 69, 77, 86, 96, 108, 121, 128};
#else
#error "VERGC_B_VARIANT must be 1, 2 or 3"
#endif

/* The smallest free block the large list keeps.  In the large-object area no
 * request is below MAX_SMALL_WH words, so smaller pieces stay unlisted blue
 * blocks until the sweep merges them with their neighbours; listing them
 * would only lengthen every first-fit search. */
#ifdef LARGE_AREA
#define LG_MIN_WZ MAX_SMALL_WH
#else
#define LG_MIN_WZ 1ULL
#endif

static uint8_t  cls_of[MAX_SMALL_WH + 1];     /* whsize -> class */
/* Per class: slots per page, the filler before the first slot (pool header
 * and wastage, B2/B3) and after the last (B), in words. */
static uint32_t cls_ns[NCLS], cls_off[NCLS], cls_tail[NCLS];

enum { K_FREE = 0, K_POOL = 1, K_LARGE = 2, K_LCONT = 3 };

typedef struct {
    uint64_t free_head;   /* first free slot (field address), 0 = none */
    uint32_t next;        /* next page on avail[cls] */
    uint32_t nfree;       /* free slots */
    uint32_t run;         /* K_LARGE: pages in the run; K_LCONT: its first page */
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

/* The pages of a class with a free slot.  B and B2: a list (av_h/av_t);
 * B3: one bit per page and class, so the lowest page is found by a scan from
 * a per-class hint (no set bit below avlo[c] words). */
#ifdef LOWEST_FIRST
static uint64_t *avbm;
static uint32_t  avnw, avlo[NCLS];

static inline void av_append(lists_t *L, uint32_t c, uint32_t p) {
    __atomic_fetch_or(&avbm[(uint64_t)c * avnw + (p >> 6)], 1ULL << (p & 63), __ATOMIC_RELAXED);
    if (L == &G && (p >> 6) < avlo[c]) avlo[c] = p >> 6;
}
static inline void av_push_front(uint32_t c, uint32_t p) { av_append(&G, c, p); }
static inline uint32_t av_first(uint32_t c) {
    uint64_t *b = avbm + (uint64_t)c * avnw;
    for (uint32_t w = avlo[c]; w < avnw; w++)
        if (b[w]) { avlo[c] = w; return (w << 6) + (uint32_t)__builtin_ctzll(b[w]); }
    avlo[c] = avnw;
    return NIL;
}
static inline void av_drop_first(uint32_t c, uint32_t p) {
    avbm[(uint64_t)c * avnw + (p >> 6)] &= ~(1ULL << (p & 63));
}
static void av_reset(void) {
    memset(avbm, 0, (size_t)NCLS * avnw * sizeof(uint64_t));
    for (int c = 0; c < NCLS; c++) avlo[c] = 0;
}
#else
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
static inline uint32_t av_first(uint32_t c) { return G.av_h[c]; }
static inline void av_drop_first(uint32_t c, uint32_t p) {
    G.av_h[c] = pm[p].next;
    if (G.av_h[c] == NIL) G.av_t[c] = NIL;
    pm[p].next = NIL;
}
static void av_reset(void) {}
#endif

#ifdef LARGE_AREA
/* Mark pages [h, h + k) as one large run. */
static void set_run(uint32_t h, uint32_t k) {
    pm[h].kind = K_LARGE;
    pm[h].run = k;
    for (uint32_t q = h + 1; q < h + k; q++) { pm[q].kind = K_LCONT; pm[q].run = h; }
}
#endif

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
    uint64_t hb = MK_BLUE(wh - 1), s = base + cls_off[c] * 8;
    if (cls_off[c]) PW(base) = MK_BLUE(cls_off[c] - 1);
    uint64_t first = s;
    for (uint64_t j = 0; j + 1 < ns; j++, s += step) {
        PW(s) = hb;
        PW(s + 8) = s + step + 8;
    }
    PW(s) = hb;
    PW(s + 8) = 0;
    if (cls_tail[c]) PW(first + ns * step) = MK_BLUE(cls_tail[c] - 1);
    page_t *g = &pm[p];
    g->free_head = first + 8;
    g->next = NIL;
    g->nfree = (uint32_t)ns;
    g->run = 0;
    g->kind = K_POOL;
    g->cls = (uint8_t)c;
    g->swept = 1;
    st_pool_inits++;
}

/* ---- sweeping one unit --------------------------------------------------- */

/* The mark: header colours (VERGC_MARK=hdr), or the bitmap
 * (par_mark_pages.c), in which case a live block's header is already white
 * and is not written, and the bits read are cleared: a pool page's slice of
 * PG_WORDS / 32 words at once after its sweep if it kept a survivor
 * (VERGC_BM_CLEAR=page, the default), or each bit as it is read (=bit); a
 * large block's bit always singly. */
static int bm_clear_bit;
static inline uint32_t *bm_slice(uint32_t p) { return proto_bm + (size_t)p * (PG_WORDS / 32); }

/* Returns 1 if the page became free. */
static inline __attribute__((always_inline)) int sweep_pool_g(uint32_t p, lists_t *L, const int bm) {
    page_t *g = &pm[p];
    uint32_t c = g->cls;
    uint64_t wh = cls_wh[c], ns = cls_ns[c], step = wh * 8;
    uint64_t base = pa(p), first = base + cls_off[c] * 8, hb = MK_BLUE(wh - 1), head = 0;
    uint32_t *bw = bm ? bm_slice(p) : NULL;
    uint32_t nfree = 0;
    uint64_t j = ns;
    if (proto_check_control == 1) j--;   /* control mutant: never looks at the last slot */
    while (j-- > 0) {
        uint64_t s = first + j * step;
        int live;
        if (bm) {
            uint64_t i = (s - base) >> 3;
            uint32_t m = 1u << (i & 31);
            live = (bw[i >> 5] & m) != 0;
            if (live && bm_clear_bit) bw[i >> 5] &= ~m;
        } else {
            uint64_t h = PW(s);
            live = IS_BLACK(h);
            if (live) PW(s) = WHITEN(h);
        }
        if (!live) {
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
    if (bm && !bm_clear_bit && proto_check_control != 3) memset(bw, 0, PG_WORDS / 8);  /* 3: a mutant */
    g->free_head = head;
    g->nfree = nfree;
    L->pages_used++;
    if (nfree) av_append(L, c, p);
    return 0;
}
static int sweep_pool_h(uint32_t p, lists_t *L) { return sweep_pool_g(p, L, 0); }
static int sweep_pool_b(uint32_t p, lists_t *L) { return sweep_pool_g(p, L, 1); }
static inline int sweep_pool(uint32_t p, lists_t *L) {
    return proto_mark ? sweep_pool_b(p, L) : sweep_pool_h(p, L);
}

/* A large block's mark: its header's colour, or its bit (cleared here). */
static inline int lg_live(uint64_t cur, uint64_t h) {
    if (!proto_mark) return IS_BLACK(h);
    uint64_t i = (cur - Z) >> 3;
    uint32_t m = 1u << (i & 31);
    if (!(proto_bm[i >> 5] & m)) return 0;
    proto_bm[i >> 5] &= ~m;
    return 1;
}

static inline void lg_flush(lists_t *L, uint64_t rs, uint64_t rw) {
    PW(rs) = MK_BLUE(rw - 1);
    if (rw - 1 >= LG_MIN_WZ) lg_push(L, rs + 8);
}

#ifdef LARGE_AREA
/* A free run [rs, rs + rw words) found in the large run being swept, whose
 * kept pages so far start at *seg.  Whole pages inside it become free pages:
 * the pages before them stay a run [*seg, a), the rest of the run starts
 * again at b.  The parts of the free run outside those pages stay blue
 * blocks.  Returns 1 if a page was freed. */
static int lg_free_run(lists_t *L, uint64_t rs, uint64_t rw, uint32_t *seg) {
    uint32_t a = (uint32_t)((rs - Z + PG_BYTES - 1) / PG_BYTES);
    uint32_t b = (uint32_t)((rs + rw * 8 - Z) / PG_BYTES);
    if (b <= a) { lg_flush(L, rs, rw); return 0; }
    if (pa(a) > rs) lg_flush(L, rs, (pa(a) - rs) / 8);
    if (a > *seg) { set_run(*seg, a - *seg); L->pages_used += a - *seg; }
    for (uint32_t q = a; q < b; q++) {
        PW(pa(q)) = MK_BLUE(PG_WORDS - 1);
        pm[q].kind = K_FREE;
        pm[q].run = 0;
        pm[q].swept = 1;
    }
    if (a < L->min_free) L->min_free = a;
    uint64_t re = rs + rw * 8;
    if (re > pa(b)) lg_flush(L, pa(b), (re - pa(b)) / 8);
    *seg = b;
    return 1;
}

/* Returns 1 if any page of the run became free. */
static int sweep_large(uint32_t p, lists_t *L) {
    uint32_t k = pm[p].run, end = p + k, seg = p;
    uint64_t cur = pa(p), e = pa(end), rs = 0, rw = 0;
    int freed = 0, seen_used = 0;
    for (uint32_t q = p; q < end; q++) pm[q].swept = 1;
    while (cur < e) {
        uint64_t h = PW(cur), next = cur + (HD_WZ(h) + 1) * 8;
        /* control mutant 2: the run's first block that is not blue is kept
         * even if dead.  (Its first block is usually the blue piece left
         * over by carving from the right, so the mutant must skip it.) */
        int keep = 0, live = lg_live(cur, h);
        if (proto_check_control == 2 && !seen_used && !IS_BLUE(h)) {
            seen_used = 1;
            if (!live) {
                static int fired = 0;
                keep = 1;
                if (!__atomic_exchange_n(&fired, 1, __ATOMIC_RELAXED))
                    fprintf(stderr, "control mutant 2 fired: dead block at 0x%llx kept\n",
                            (unsigned long long)cur);
            }
        }
        if (live || keep) {
            if (rw) freed |= lg_free_run(L, rs, rw, &seg);
            rw = 0;
            if (!proto_mark) PW(cur) = WHITEN(h);
        } else {
            if (rw == 0) rs = cur;
            rw += HD_WZ(h) + 1;
        }
        cur = next;
    }
    if (rw) freed |= lg_free_run(L, rs, rw, &seg);
    if (seg < end) { set_run(seg, end - seg); L->pages_used += end - seg; }
    return freed;
}
#else
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
#endif

/* Sweep the units whose first page is in [lo, hi); lo is not inside a run. */
static void sweep_range(uint32_t lo, uint32_t hi, lists_t *L) {
    uint32_t p = lo;
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
#ifdef LOWEST_FIRST
    (void)parts;
    for (int c = 0; c < NCLS; c++) avlo[c] = 0;   /* the sweep set the bits */
#else
    for (int c = 0; c < NCLS; c++) {
        G.av_h[c] = G.av_t[c] = NIL;
        for (int i = 0; i < n; i++) {
            if (parts[i].av_h[c] == NIL) continue;
            if (G.av_t[c] == NIL) G.av_h[c] = parts[i].av_h[c];
            else pm[G.av_t[c]].next = parts[i].av_h[c];
            G.av_t[c] = parts[i].av_t[c];
        }
    }
#endif
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
    av_reset();
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
            if ((p = av_first(c)) != NIL) return p;
        }
    }
    uint32_t p = take_free_page();
    if (p == NIL && sweeping) {
        /* No free page: sweep on until this class has a slot or a page is
         * freed (the exception in the note, section 4.2). */
        uint64_t f0 = freed_units;
        proto_sweep_work_begin(PK_ALLOC);
        while (sweeping && av_first(c) == NIL && freed_units == f0) incr_step();
        proto_sweep_work_end(PK_ALLOC);
        if ((p = av_first(c)) != NIL) return p;
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
    uint32_t p = av_first(c);
    if (p == NIL && (p = refill(c)) == NIL) return 0;
    page_t *g = &pm[p];
    uint64_t f = g->free_head;
    g->free_head = PW(f);
    if (--g->nfree == 0) av_drop_first(c, p);
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
            if (left >= 1) PW(h) = MK_BLUE(left - 1);
            if (left == 0 || left - 1 < LG_MIN_WZ) {
                if (prev) PW(prev) = next; else G.lg_h = next;
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
    if (s + k > hwm) { hwm = s + (uint32_t)k; wild_fix(); }
#ifdef LARGE_AREA
    {   /* join a swept large run on either side */
        uint32_t h = s, len = (uint32_t)k, e = s + (uint32_t)k;
        if (s > 0 && (pm[s - 1].kind == K_LARGE || pm[s - 1].kind == K_LCONT)) {
            uint32_t l = pm[s - 1].kind == K_LARGE ? s - 1 : pm[s - 1].run;
            if (pm[l].swept) { h = l; len = e - l; }
        }
        if (e < hwm && pm[e].kind == K_LARGE && pm[e].swept) len += pm[e].run;
        set_run(h, len);
    }
#else
    pm[s].kind = K_LARGE;
    pm[s].run = (uint32_t)k;
#endif
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
static lists_t  parts[MAX_CHUNKS];
static int      n_chunks;
static uint32_t chunk_lo[MAX_CHUNKS + 1];

/* Chunk c of n_chunks: about an equal share of the pages, in address order.
 * The bounds are fixed before the threads start, each moved past any run
 * that crosses it: a run belongs to the chunk holding its first page, and
 * the sweep of a run changes page kinds (B2 and B3 split runs), so a thread
 * must not look at another chunk's pages to find where its own begin. */
static void chunk_bounds(void) {
    for (int c = 0; c < n_chunks; c++) {
        uint32_t lo = (uint32_t)((uint64_t)hwm * c / n_chunks);
        if (c > 0 && lo < chunk_lo[c - 1]) lo = chunk_lo[c - 1];
        while (lo < hwm && pm[lo].kind == K_LCONT) lo++;
        chunk_lo[c] = lo;
    }
    chunk_lo[n_chunks] = hwm;
}

static void par_chunk(int c) {
    lists_clear(&parts[c]);
    sweep_range(chunk_lo[c], chunk_lo[c + 1], &parts[c]);
}

void vergc_proto_sweep(heap_t heap, uint64_t *heads, uint64_t *tbl) {
    (void)heap; (void)heads; (void)tbl;
    if (proto_mem) proto_mem_after_mark();
#ifdef VERGC_PROTO_CHECK
    chk_oracle();
    proto_mark_after_oracle();
#endif
    if (proto_mode == SW_INCR) {
        if (proto_mark) { fprintf(stderr, "B: the incremental sweep reads header colours only\n"); exit(2); }
        incr_start();
        return;
    }
    uint64_t t0 = proto_now();
    av_reset();
    int n = proto_mode == SW_PAR ? proto_threads : 1;
    if (n == 1) {
        n_chunks = 1;
        lists_clear(&parts[0]);
        sweep_range(0, hwm, &parts[0]);
    } else {
        n_chunks = n * CHUNKS_PER_THREAD;
        chunk_bounds();
        proto_pool_chunks(n, n_chunks, par_chunk);
    }
    lists_install(parts, n_chunks);
    proto_record_eager_sweep(proto_now() - t0);
    if (proto_mem) impl_mem();
#ifdef VERGC_PROTO_CHECK
    chk_compare_eager("after B's sweep", 0);
    impl_check("after B's sweep");
    proto_mark_after_sweep();
#endif
}

/* ---- setup and stats ----------------------------------------------------- */
const char *impl_name(void) {
    static char nm[16];
#ifdef B_CLASS_129
    return "B-129";
#endif
    if (VERGC_B_VARIANT == 1 && PG_WORDS == 4096) return "B";
    if (VERGC_B_VARIANT == 2 && PG_WORDS == 4096) return "B2";
    snprintf(nm, sizeof nm, "B%d-%lluK", VERGC_B_VARIANT, (unsigned long long)(PG_BYTES >> 10));
    return nm;
}

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
        uint64_t usable = PG_WORDS - POOL_HDR, waste;
        cls_ns[c] = (uint32_t)(usable / cls_wh[c]);
        waste = usable - (uint64_t)cls_ns[c] * cls_wh[c];
        /* OCaml 5 puts the pool header and the wastage before the slots */
        cls_off[c] = POOL_HDR ? (uint32_t)(POOL_HDR + waste) : 0;
        cls_tail[c] = POOL_HDR ? 0 : (uint32_t)waste;
    }
#ifdef LOWEST_FIRST
    avnw = npages / 64 + 1;
    avbm = (uint64_t *)calloc((size_t)NCLS * avnw, sizeof(uint64_t));
    if (!avbm) { fprintf(stderr, "B: calloc avail bitmap\n"); exit(2); }
#endif
    for (uint64_t wh = 2, c = 1; wh <= MAX_SMALL_WH; wh++) {
        while (cls_wh[c] < wh) c++;
        cls_of[wh] = (uint8_t)c;
    }
    const char *bc = getenv("VERGC_BM_CLEAR");
    if (bc != NULL) {
        if (strcmp(bc, "bit") == 0) bm_clear_bit = 1;
        else if (strcmp(bc, "page") != 0) { fprintf(stderr, "VERGC_BM_CLEAR: page or bit\n"); exit(2); }
    }
    hwm = 0;
    free_hint = 0;
    wild_fix();
    lists_clear(&G);
}

/* VERGC_PROTO_MEM: after each eager sweep, where the words of the pages in
 * use go.  Pool pages: live words (the objects' whsize), rounding (the rest
 * of each live slot), free slots, and the fillers before and after the slots;
 * large runs: live words and free words.  Kept for the collection with the
 * most pages in use. */
static uint64_t m_n, m_pages, m_pool_pages, m_lg_pages;
static uint64_t m_live, m_round, m_slot_free, m_fill, m_lg_live, m_lg_free;

void impl_mem(void) {
    uint64_t pool = 0, lgp = 0, live = 0, rnd = 0, sfree = 0, fill = 0, llive = 0, lfree = 0;
    for (uint32_t p = 0; p < hwm;) {
        page_t *g = &pm[p];
        if (g->kind == K_POOL) {
            uint32_t c = g->cls;
            uint64_t wh = cls_wh[c], first = pa(p) + cls_off[c] * 8;
            pool++;
            fill += cls_off[c] + cls_tail[c];
            for (uint64_t j = 0; j < cls_ns[c]; j++) {
                uint64_t h = PW(first + j * wh * 8);
                if (IS_BLUE(h)) sfree += wh;
                else { live += HD_WZ(h) + 1; rnd += wh - (HD_WZ(h) + 1); }
            }
            p++;
        } else if (g->kind == K_LARGE) {
            lgp += g->run;
            for (uint64_t cur = pa(p); cur < pa(p + g->run);) {
                uint64_t h = PW(cur), w = HD_WZ(h) + 1;
                if (IS_BLUE(h)) lfree += w; else llive += w;
                cur += w * 8;
            }
            p += g->run;
        } else {
            p++;
        }
    }
    m_n++;
    if (pool + lgp >= m_pages) {
        m_pages = pool + lgp; m_pool_pages = pool; m_lg_pages = lgp;
        m_live = live; m_round = rnd; m_slot_free = sfree; m_fill = fill;
        m_lg_live = llive; m_lg_free = lfree;
    }
}

void impl_stats(FILE *f) {
    fprintf(f, " bm_clear=%s", bm_clear_bit ? "bit" : "page");
    if (proto_mem)
        fprintf(f, " mem_n=%llu mem_pages=%llu mem_pool_pages=%llu mem_lg_pages=%llu"
                   " mem_live=%llu mem_round=%llu mem_slot_free=%llu mem_fill=%llu"
                   " mem_lg_live=%llu mem_lg_free=%llu pg_words=%llu",
                (unsigned long long)m_n, (unsigned long long)m_pages,
                (unsigned long long)m_pool_pages, (unsigned long long)m_lg_pages,
                (unsigned long long)m_live, (unsigned long long)m_round,
                (unsigned long long)m_slot_free, (unsigned long long)m_fill,
                (unsigned long long)m_lg_live, (unsigned long long)m_lg_free,
                (unsigned long long)PG_WORDS);
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
#ifdef LOWEST_FIRST
        for (uint32_t w = 0; w < avnw; w++) {
            uint64_t b = avbm[(uint64_t)c * avnw + w];
            if (b && w < avlo[c]) chk_fail(where, "avail bit below the class's hint", w, c);
            for (; b; b &= b - 1) {
                uint32_t p = (w << 6) + (uint32_t)__builtin_ctzll(b);
#else
        uint32_t steps = 0, last = NIL;
        for (uint32_t p = G.av_h[c]; p != NIL; p = pm[p].next) {
            {
#endif
                if (p >= hwm || pm[p].kind != K_POOL || pm[p].cls != c)
                    chk_fail(where, "avail page is not a pool of its class", p, c);
                if (!pm[p].swept) chk_fail(where, "avail page is unswept", p, c);
                if (pm[p].nfree == 0) chk_fail(where, "avail page has no free slot", p, c);
                if (ck_onlist[p]++) chk_fail(where, "page on avail twice", p, c);
#ifndef LOWEST_FIRST
                if (++steps > npages) chk_fail(where, "avail list does not end", p, c);
                last = p;
#endif
            }
        }
#ifndef LOWEST_FIRST
        if (last != G.av_t[c]) chk_fail(where, "avail tail is not the last page", last, c);
#endif
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
            for (uint32_t q = p + 1; q < p + k; q++) {
                if (pm[q].kind != K_LCONT) chk_fail(where, "large run page kind", q, pm[q].kind);
#ifdef LARGE_AREA
                if (pm[q].run != p) chk_fail(where, "large continuation page names another run", q, pm[q].run);
#endif
            }
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
        uint64_t first = base + cls_off[c] * 8;
        if (c == 0 || c >= NCLS) chk_fail(where, "pool class", p, c);
        if (cls_off[c] && PW(base) != MK_BLUE(cls_off[c] - 1)) chk_fail(where, "pool header filler", p, PW(base));
        uint32_t blue_slots = 0;
        for (uint64_t j = 0; j < ns; j++) {
            uint64_t s = first + j * step, h = PW(s);
            chk_walk(where, s, s + step);   /* the walk from a slot start stays in the slot */
            if (IS_BLUE(h)) {
                if (h != hb) chk_fail(where, "blue slot of the wrong size", p, s);
                blue_slots++;
            } else if (g->swept && IS_BLACK(h)) {
                chk_fail(where, "black slot in a swept page", p, s);
            }
        }
        if (cls_tail[c]) {
            uint64_t t = first + ns * step;
            if (PW(t) != MK_BLUE(cls_tail[c] - 1)) chk_fail(where, "page tail filler", p, PW(t));
        }
        uint32_t n = 0;
        for (uint64_t f = g->free_head; f; f = PW(f)) {
            uint64_t s = f - 8;
            if (s < first || s >= first + ns * step || (s - first) % step != 0)
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
     * open, every blue block of wosize >= LG_MIN_WZ in a large run is listed */
    uint64_t listed = 0, steps = 0;
    for (uint64_t f = G.lg_h; f; f = PW(f)) {
        uint64_t s = f - 8, h = PW(s);
        if (s < Z || s >= pa(hwm)) chk_fail(where, "large cell outside the used pages", s, 0);
        uint32_t p = (uint32_t)((s - Z) / PG_BYTES);
        while (pm[p].kind == K_LCONT) p--;
        if (pm[p].kind != K_LARGE || !pm[p].swept) chk_fail(where, "large cell outside a swept run", s, p);
        if (!IS_BLUE(h) || HD_WZ(h) < LG_MIN_WZ) chk_fail(where, "large cell is not a blue block", s, h);
        if (bit_test_set(ck_seen, s)) chk_fail(where, "large cell listed twice", s, 0);
        listed++;
        if (++steps > (HS - Z) / 16) chk_fail(where, "large list does not end", s, 0);
    }
    if (!sweeping) {
        uint64_t blue = 0;
        for (uint32_t p = 0; p < hwm; p++) {
            if (pm[p].kind != K_LARGE) continue;
            for (uint64_t cur = pa(p); cur < pa(p + pm[p].run); cur += (HD_WZ(PW(cur)) + 1) * 8)
                if (IS_BLUE(PW(cur)) && HD_WZ(PW(cur)) >= LG_MIN_WZ) blue++;
        }
        if (blue != listed) chk_fail(where, "a blue block in a large run is on no list", blue, listed);
    }
}
#else
void impl_check(const char *where) { (void)where; }
#endif
