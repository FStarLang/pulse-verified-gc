/* proto_check.c — the comparison with the verified sweep (check builds,
 * -DVERGC_PROTO_CHECK; docs/allocator-comparison.md, section 6.2).
 *
 * At every major collection, after the mark, the heap is copied and the
 * extracted, verified fused_sweep_coalesce is run on the copy: its result is
 * the oracle.  The sweeps share no code with it except, for A, the
 * sequential sweep itself.  Then:
 *   - an eager sweep (sequential or parallel) must leave exactly the oracle's
 *     survivors (non-blue blocks), at the same addresses, with the same
 *     headers and contents; for A also the same free blocks, lists and
 *     table, word for word;
 *   - an incremental sweep is checked unit by unit (a page or large run for
 *     B, a slice for A): a block that was black before the unit must be
 *     white after it, with its contents unchanged, and be an oracle survivor;
 *     one that was white must not be; for B it must lie in a blue block after
 *     the unit.
 *     When the sweep closes, the non-blue blocks must be the oracle's
 *     survivors plus the blocks allocated since the mark.
 * Any difference aborts. */
#include "proto.h"
#ifdef VERGC_PROTO_CHECK
#include <stdlib.h>
#include <string.h>

static uint64_t Z, HS, H;
static uint8_t *copy;           /* the oracle heap */
static uint8_t *surv, *allocd;  /* one bit per heap word */
static uint64_t chk_heads[N_LISTS];
static uint64_t *chk_tbl;
static uint64_t n_oracles, n_units;

void chk_fail(const char *where, const char *what, uint64_t a, uint64_t b) {
    fprintf(stderr, "VERGC_PROTO_CHECK: %s: %s (0x%llx, 0x%llx; heap at 0x%llx)\n", where, what,
            (unsigned long long)a, (unsigned long long)b, (unsigned long long)zero_addr);
    abort();
}

static inline void bset(uint8_t *bm, uint64_t a) {
    uint64_t w = (a - Z) / 8;
    bm[w >> 3] |= (uint8_t)(1u << (w & 7));
}
static inline int btest(const uint8_t *bm, uint64_t a) {
    uint64_t w = (a - Z) / 8;
    return (bm[w >> 3] >> (w & 7)) & 1;
}
static inline uint64_t cw(uint64_t live) { return (uint64_t)(uintptr_t)copy + (live - Z); }

void chk_walk(const char *where, uint64_t a, uint64_t b) {
    uint64_t cur = a;
    while (cur < b) {
        if (b == heap_size_u64 && cur + 8 >= b) return;   /* the walk's own end */
        uint64_t next = cur + (HD_WZ(PW(cur)) + 1) * 8;
        if (next > b || next <= cur) chk_fail(where, "walk overruns its region", cur, b);
        cur = next;
    }
}

void chk_oracle(void) {
    Z = zero_addr;
    HS = heap_size_u64;
    if (!copy) {
        H = HS - Z;
        copy = (uint8_t *)malloc((size_t)H);
        surv = (uint8_t *)malloc((size_t)(H / 64 + 1));
        allocd = (uint8_t *)malloc((size_t)(H / 64 + 1));
        chk_tbl = (uint64_t *)calloc((size_t)proto_tbl_len + 1, sizeof(uint64_t));
        if (!copy || !surv || !allocd || !chk_tbl) chk_fail("oracle", "out of memory", H, 0);
    }
    memcpy(copy, (void *)(uintptr_t)Z, (size_t)H);
    /* the verified sweep, on the copy: it reads its heap bounds from the
     * extracted code's own copies of zero_addr and heap_size */
    uint64_t z1 = zero_addr1, hs1 = heap_size_u640;
    zero_addr1 = (uint64_t)(uintptr_t)copy;
    heap_size_u640 = zero_addr1 + H;
    heap_t hc = { .data = NULL, .size = (size_t)H };
    vergc_verified_fused_sweep(hc, chk_heads, chk_tbl);
    zero_addr1 = z1;
    heap_size_u640 = hs1;
    memset(surv, 0, (size_t)(H / 64 + 1));
    memset(allocd, 0, (size_t)(H / 64 + 1));
    uint64_t c = (uint64_t)(uintptr_t)copy, ce = c + H;
    while (c + 8 < ce) {
        uint64_t h = PW(c);
        if (!IS_BLUE(h)) bset(surv, Z + (c - (uint64_t)(uintptr_t)copy));
        c += (HD_WZ(h) + 1) * 8;
    }
    n_oracles++;
}

static inline uint64_t tr(uint64_t live_or_0, uint64_t copy_or_0, int *ok) {
    /* a link or table entry: 0, or an address translating between the heaps */
    if (live_or_0 == 0 || copy_or_0 == 0) { *ok = live_or_0 == copy_or_0; return 0; }
    *ok = live_or_0 - Z == copy_or_0 - (uint64_t)(uintptr_t)copy;
    return 0;
}

void chk_compare_eager(const char *where, int exact) {
    uint64_t c0 = (uint64_t)(uintptr_t)copy;
    /* 1. every oracle survivor is in the heap, same header and contents */
    uint64_t n_or = 0;
    for (uint64_t c = c0; c + 8 < c0 + H;) {
        uint64_t h = PW(c), wz = HD_WZ(h), live = Z + (c - c0);
        if (!IS_BLUE(h)) {
            n_or++;
            if (PW(live) != h) chk_fail(where, "survivor header differs from the verified sweep's", live, PW(live));
            if (memcmp((void *)(uintptr_t)(live + 8), (void *)(uintptr_t)(c + 8), (size_t)(wz * 8)) != 0)
                chk_fail(where, "survivor contents differ from the verified sweep's", live, wz);
        }
        c += (wz + 1) * 8;
    }
    /* 2. and nothing else survives */
    uint64_t n_live = 0;
    for (uint64_t cur = Z; cur + 8 < HS;) {
        uint64_t h = PW(cur);
        if (!IS_BLUE(h)) {
            n_live++;
            if (!btest(surv, cur)) chk_fail(where, "a block the verified sweep frees survives", cur, h);
        }
        cur += (HD_WZ(h) + 1) * 8;
    }
    if (n_live != n_or) chk_fail(where, "survivor counts differ", n_live, n_or);
    if (!exact) return;
    /* 3. A: the same walk, free blocks, links, lists and table */
    int ok;
    for (uint64_t cur = Z; cur + 8 < HS;) {
        uint64_t h = PW(cur), wz = HD_WZ(h);
        if (PW(cw(cur)) != h) chk_fail(where, "header differs from the verified sweep's", cur, h);
        if (IS_BLUE(h) && wz >= 1) {
            tr(PW(cur + 8), PW(cw(cur) + 8), &ok);
            if (!ok) chk_fail(where, "free-list link differs from the verified sweep's", cur, PW(cur + 8));
        }
        cur += (wz + 1) * 8;
    }
    for (int i = 0; i < N_LISTS; i++) {
        tr(proto_heads[i], chk_heads[i], &ok);
        if (!ok) chk_fail(where, "list head differs from the verified sweep's", (uint64_t)i, proto_heads[i]);
    }
    for (uint64_t k = 0; k < proto_tbl_len; k++) {
        tr(proto_tbl[k], chk_tbl[k], &ok);
        if (!ok) chk_fail(where, "table entry differs from the verified sweep's", k, proto_tbl[k]);
    }
}

/* ---- incremental: unit checks ------------------------------------------- */
typedef struct { uint64_t at, hdr, n; size_t off; } rec_t;
static rec_t   *recs;
static size_t   n_recs, cap_recs;
static uint64_t *saved;
static size_t   n_saved, cap_saved;
static uint64_t unit_a, unit_b;

void chk_unit_pre(uint64_t a, uint64_t b) {
    unit_a = a;
    unit_b = b;
    n_recs = n_saved = 0;
    for (uint64_t cur = a; cur < b && cur + 8 < HS;) {
        uint64_t h = PW(cur), wz = HD_WZ(h);
        if (!IS_BLUE(h)) {
            if (n_recs == cap_recs) {
                cap_recs = cap_recs ? 2 * cap_recs : 4096;
                recs = (rec_t *)realloc(recs, cap_recs * sizeof(rec_t));
                if (!recs) chk_fail("unit check", "out of memory", cap_recs, 0);
            }
            uint64_t keep = IS_BLACK(h) ? wz : 0;
            while (n_saved + keep > cap_saved) {
                cap_saved = cap_saved ? 2 * cap_saved : 65536;
                saved = (uint64_t *)realloc(saved, cap_saved * sizeof(uint64_t));
                if (!saved) chk_fail("unit check", "out of memory", cap_saved, 0);
            }
            recs[n_recs++] = (rec_t){ .at = cur, .hdr = h, .n = keep, .off = n_saved };
            memcpy(saved + n_saved, (void *)(uintptr_t)(cur + 8), (size_t)(keep * 8));
            n_saved += keep;
        }
        cur += (wz + 1) * 8;
    }
}

void chk_unit_post(const char *where, int dead_blue) {
    uint64_t blacks = 0;
    uint64_t wcur = unit_a, wnext = unit_a;   /* the block, after the unit, holding r->at */
    for (size_t i = 0; i < n_recs; i++) {
        rec_t *r = &recs[i];
        if (IS_BLACK(r->hdr)) {
            blacks++;
            if (!btest(surv, r->at)) chk_fail(where, "a black block is not an oracle survivor", r->at, r->hdr);
            if (PW(r->at) != WHITEN(r->hdr)) chk_fail(where, "a survivor is not white after its sweep", r->at, PW(r->at));
            if (memcmp((void *)(uintptr_t)(r->at + 8), saved + r->off, (size_t)(r->n * 8)) != 0)
                chk_fail(where, "the sweep changed a survivor's contents", r->at, r->n);
        } else {
            if (btest(surv, r->at)) chk_fail(where, "an oracle survivor was not black", r->at, r->hdr);
            if (dead_blue) {
                /* covered by a blue block: its own header, or a coalesced
                 * run or freed page starting below it */
                while (wnext <= r->at) { wcur = wnext; wnext = wcur + (HD_WZ(PW(wcur)) + 1) * 8; }
                if (!IS_BLUE(PW(wcur))) chk_fail(where, "a dead block is not covered by a blue block after its sweep", r->at, PW(wcur));
            }
        }
    }
    /* the oracle's survivors in the unit are exactly the black blocks */
    uint64_t n = 0;
    for (uint64_t a = unit_a; a < unit_b; a += 8) if (btest(surv, a)) n++;
    if (n != blacks) chk_fail(where, "oracle survivors in the unit differ from its black blocks", n, blacks);
    n_units++;
}

void chk_note_alloc(uint64_t hp) { if (copy) bset(allocd, hp); }

void chk_sweep_closed(const char *where) {
    uint64_t c0 = (uint64_t)(uintptr_t)copy;
    for (uint64_t cur = Z; cur + 8 < HS;) {
        uint64_t h = PW(cur);
        if (!IS_BLUE(h) && !btest(surv, cur) && !btest(allocd, cur))
            chk_fail(where, "a block that is neither a survivor nor new was not freed", cur, h);
        cur += (HD_WZ(h) + 1) * 8;
    }
    for (uint64_t c = c0; c + 8 < c0 + H;) {
        uint64_t h = PW(c), live = Z + (c - c0);
        /* The program runs while the sweep is open, and Lazy.force turns a
         * Lazy_tag (246) block into a Forward_tag (250) one in place. */
        uint64_t lh = PW(live);
        if (!IS_BLUE(h) && lh != h && !((h & 0xff) == 246 && lh == ((h & ~0xffULL) | 250)))
            chk_fail(where, "a survivor's header changed", live, lh);
        c += (HD_WZ(h) + 1) * 8;
    }
}
#endif
