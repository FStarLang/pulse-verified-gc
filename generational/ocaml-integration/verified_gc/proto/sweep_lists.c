/* sweep_lists.c — A's baselines for the allocator comparison
 * (docs/allocator-comparison.md, section 6.3).  Unverified; for measurement
 * only.  The allocator is always the verified size-list allocator, and the
 * sequential sweep the verified fused_sweep_coalesce.
 *
 * Parallel sweep.  Cut points come from the object-start table: thread i of
 * n starts at tbl[i * len / n], a header of the walk (table_sound).  Each
 * thread runs the fused sweep on its segment with its own 17 lists, and
 * leaves open the run of non-black blocks at each end of its segment: the
 * one starting at its first block (the lead) and the one reaching its end
 * (the trail).  The join, in address order, merges a trail with the next
 * segments' leads, rewrites the table entries inside a merged lead to the
 * merged run's start, and pushes runs and splices the segments' lists in the
 * order the sequential sweep pushes them.  So the heap, the 17 heads and the
 * table come out exactly as fused_sweep_coalesce leaves them, which the check
 * build compares word for word.
 *
 * Incremental sweep.  At the end of a mark the heads are cleared (as the
 * fused sweep does) and a cursor starts at zero_addr.  A slice runs the fused
 * sweep's loop from the cursor over at least SLICE_WORDS words.  Allocation
 * uses the verified allocator, so it only ever finds blocks behind the
 * cursor; if it finds none while the sweep is open, it sweeps one more slice
 * and retries, until it succeeds or the sweep closes. */
#include "proto.h"
#include <stdlib.h>
#include <string.h>

#define WIN (1ULL << TBL_SHIFT)

static uint64_t Z, HS;

static inline size_t cls_of_rw(uint64_t rw) {
    return (rw >= 2 && rw - 1 <= 16) ? (size_t)(rw - 1) : 0;
}

/* Push the run [rs, rs + rw words) as one blue block on heads (flush_blue). */
static inline void flush_run(uint64_t *heads, uint64_t rs, uint64_t rw) {
    PW(rs) = MK_BLUE(rw - 1);
    if (rw >= 2) {
        size_t c = cls_of_rw(rw);
        PW(rs + 8) = heads[c];
        heads[c] = rs + 8;
    }
}

/* ---- parallel sweep ------------------------------------------------------ */
typedef struct {
    uint64_t s, e;
    uint64_t lh[N_LISTS], lt[N_LISTS];   /* local lists: last pushed, first pushed */
    int      has_lead, all_run;
    uint64_t lead_rw;
    uint64_t k_lo, k_lead_hi;            /* windows of the lead run: [k_lo, k_lead_hi) */
    uint64_t trail_rs, trail_rw;
} seg_t;

static seg_t    segs[MAX_CHUNKS];
static uint64_t n_segs;

static void seg_sweep(seg_t *S) {
    uint64_t *tbl = proto_tbl;
    uint64_t cur = S->s, e = S->e, rs = 0, rw = 0, prev = cur;
    uint64_t k = (cur - Z + WIN - 1) >> TBL_SHIFT, nb = Z + (k << TBL_SHIFT);
    int seen_black = 0;
    for (int c = 0; c < N_LISTS; c++) S->lh[c] = S->lt[c] = 0;
    S->has_lead = S->all_run = 0;
    S->lead_rw = S->trail_rw = 0;
    S->k_lo = S->k_lead_hi = k;
    while (cur < e && cur + 8 < HS) {
        uint64_t h = PW(cur), next = cur + (HD_WZ(h) + 1) * 8;
        if (IS_BLACK(h)) {
            if (rw) {
                if (!seen_black && rs == S->s) {
                    S->has_lead = 1;          /* the join closes it */
                    S->lead_rw = rw;
                } else {
                    PW(rs) = MK_BLUE(rw - 1);
                    if (rw >= 2) {
                        size_t c = cls_of_rw(rw);
                        if (S->lh[c] == 0) S->lt[c] = rs + 8;
                        PW(rs + 8) = S->lh[c];
                        S->lh[c] = rs + 8;
                    }
                }
            }
            PW(cur) = WHITEN(h);
            while (nb < cur) { tbl[k++] = prev; nb += WIN; }
            if (!seen_black) S->k_lead_hi = k;
            prev = cur;
            seen_black = 1;
            rw = 0;
        } else {
            if (rw == 0) {
                rs = cur;
                while (nb < cur) { tbl[k++] = prev; nb += WIN; }
                prev = cur;
            }
            rw += HD_WZ(h) + 1;
        }
        cur = next;
    }
    while (nb < e) { tbl[k++] = prev; nb += WIN; }
    if (rw) {
        if (!seen_black) {           /* the whole segment is one run */
            S->has_lead = S->all_run = 1;
            S->lead_rw = rw;
            S->k_lead_hi = k;
        }
        S->trail_rs = rs;
        S->trail_rw = rw;
    }
    /* Control mutant: a join that cannot see this segment's lead, so a run
     * that crosses the cut stays split in two. */
    if (proto_check_control && S->s != Z && S->has_lead && !S->all_run) {
        PW(S->s) = MK_BLUE(S->lead_rw - 1);
        S->has_lead = 0;
    }
}

static void seg_chunk(int c) { seg_sweep(&segs[c]); }

/* T threads; for T > 1, CHUNKS_PER_THREAD segments per thread, taken
 * dynamically, cut at equal shares of the table's windows. */
static void par_sweep(uint64_t *heads, int T) {
    uint64_t cuts[MAX_CHUNKS + 1];
    int K = T == 1 ? 1 : T * CHUNKS_PER_THREAD;
    int n = 1;
    cuts[0] = Z;
    for (int i = 1; i < K; i++) {
        uint64_t c = proto_tbl[(uint64_t)i * proto_tbl_len / (uint64_t)K];
        if (c > cuts[n - 1] && c + 8 < HS) cuts[n++] = c;
    }
    cuts[n] = HS;
    for (int i = 0; i < n; i++) { segs[i].s = cuts[i]; segs[i].e = cuts[i + 1]; }
    n_segs = (uint64_t)n;
    proto_pool_chunks(T, n, seg_chunk);

    /* the join, in address order */
    for (int c = 0; c < N_LISTS; c++) heads[c] = 0;
    uint64_t ors = 0, orw = 0;                     /* the run open across cuts */
    for (int i = 0; i < n; i++) {
        seg_t *S = &segs[i];
        if (S->has_lead) {
            if (orw) {
                orw += S->lead_rw;
                for (uint64_t k = S->k_lo; k < S->k_lead_hi; k++) proto_tbl[k] = ors;
            } else {
                ors = S->s;
                orw = S->lead_rw;
            }
            if (S->all_run) continue;
        }
        if (orw) { flush_run(heads, ors, orw); orw = 0; }
        for (int c = 0; c < N_LISTS; c++)
            if (S->lh[c]) { PW(S->lt[c]) = heads[c]; heads[c] = S->lh[c]; }
        if (S->trail_rw) { ors = S->trail_rs; orw = S->trail_rw; }
    }
    if (orw) flush_run(heads, ors, orw);
}

/* ---- incremental sweep --------------------------------------------------- */
static int      sweeping;
static uint64_t i_cur, i_rs, i_rw, i_prev, i_k, i_nb;
static int      i_first;                 /* no black block met yet this cycle (control) */
static uint64_t st_slices_alloc, st_alloc_retries;

static void incr_close(void) {
    uint64_t *heads = proto_heads, *tbl = proto_tbl;
    if (i_rw) flush_run(heads, i_rs, i_rw);
    i_rw = 0;
    while (i_nb < HS) { tbl[i_k++] = i_prev; i_nb += WIN; }
    sweeping = 0;
#ifdef VERGC_PROTO_CHECK
    chk_sweep_closed("when A's incremental sweep closed");
    impl_check("when A's incremental sweep closed");
#endif
}

static void incr_start(void) {
    for (int c = 0; c < N_LISTS; c++) proto_heads[c] = 0;   /* clear_heads */
    i_cur = i_prev = i_nb = Z;
    i_rs = i_rw = i_k = 0;
    i_first = 1;
    sweeping = 1;
}

/* The fused sweep's loop from the cursor, over at least `budget` words. */
static void incr_run(uint64_t budget) {
    uint64_t *heads = proto_heads, *tbl = proto_tbl;
    uint64_t cur = i_cur, rs = i_rs, rw = i_rw, prev = i_prev, k = i_k, nb = i_nb;
    int64_t left = (int64_t)budget;
#ifdef VERGC_PROTO_CHECK
    {   /* the region this slice will cover, for the unit check */
        uint64_t c = cur;
        int64_t l = left;
        while (l > 0 && c + 8 < HS) { uint64_t w = HD_WZ(PW(c)) + 1; c += w * 8; l -= (int64_t)w; }
        chk_unit_pre(cur, c);
    }
#endif
    while (left > 0 && cur + 8 < HS) {
        uint64_t h = PW(cur), w = HD_WZ(h) + 1, next = cur + w * 8;
        if (IS_BLACK(h)) {
            if (rw) flush_run(heads, rs, rw);
            /* Control mutant: the cycle's first black block stays black. */
            if (proto_check_control && i_first) i_first = 0;
            else PW(cur) = WHITEN(h);
            while (nb < cur) { tbl[k++] = prev; nb += WIN; }
            prev = cur;
            rw = 0;
        } else {
            if (rw == 0) {
                rs = cur;
                while (nb < cur) { tbl[k++] = prev; nb += WIN; }
                prev = cur;
            }
            rw += w;
        }
        cur = next;
        left -= (int64_t)w;
    }
    i_cur = cur; i_rs = rs; i_rw = rw; i_prev = prev; i_k = k; i_nb = nb;
#ifdef VERGC_PROTO_CHECK
    chk_unit_post("after a slice of A's incremental sweep", 0);
#endif
    if (cur + 8 >= HS) incr_close();
}

int    impl_sweeping(void) { return sweeping; }
void   impl_slice(void) { if (sweeping) incr_run(SLICE_WORDS); }
double impl_swept_fraction(void) { return (double)(i_cur - Z) / (double)(HS - Z); }
void   impl_finish(void) { if (sweeping) incr_run(UINT64_MAX >> 2); }

uint64_t vergc_proto_allocate(heap_t heap, uint64_t *heads, uint64_t *tbl, uint64_t wz) {
    uint64_t r = vergc_lists_allocate(heap, heads, tbl, wz);
    if (r == 0 && sweeping) {
        proto_sweep_work_begin(PK_ALLOC);
        while (r == 0 && sweeping) {
            incr_run(SLICE_WORDS);
            st_slices_alloc++;
            r = vergc_lists_allocate(heap, heads, tbl, wz);
            st_alloc_retries++;
        }
        proto_sweep_work_end(PK_ALLOC);
    }
#ifdef VERGC_PROTO_CHECK
    if (r && sweeping) chk_note_alloc(r - 8);
#endif
    return r;
}

/* ---- the sweep hook ------------------------------------------------------ */
void vergc_proto_sweep(heap_t heap, uint64_t *heads, uint64_t *tbl) {
    if (proto_mem) proto_mem_after_mark();
#ifdef VERGC_PROTO_CHECK
    chk_oracle();
#endif
    if (proto_mode == SW_INCR) { incr_start(); return; }
    uint64_t t0 = proto_now();
    if (proto_mode == SW_PAR) par_sweep(heads, proto_threads);
    else vergc_verified_fused_sweep(heap, heads, tbl);
    proto_record_eager_sweep(proto_now() - t0);
    if (proto_mem) impl_mem();
#ifdef VERGC_PROTO_CHECK
    chk_compare_eager("after A's sweep", 1);
#endif
}

/* ---- setup and stats ----------------------------------------------------- */
const char *impl_name(void) { return "A"; }
double impl_consumption(void) { return 1.0; }   /* exact fit */

void impl_init(void) {
    Z = zero_addr;
    HS = heap_size_u64;
}

/* VERGC_PROTO_MEM: after each eager sweep, the words in live blocks and in
 * free blocks, and the free words in blocks under 129 words (fragments only
 * the small lists can use); kept for the collection with the most live words. */
static uint64_t m_n, m_live, m_free, m_frag;

void impl_mem(void) {
    uint64_t live = 0, fr = 0, frag = 0;
    for (uint64_t cur = Z; cur + 8 < HS;) {
        uint64_t h = PW(cur), w = HD_WZ(h) + 1;
        if (IS_BLUE(h)) { fr += w; if (w < 129) frag += w; }
        else live += w;
        cur += w * 8;
    }
    m_n++;
    if (live >= m_live) { m_live = live; m_free = fr; m_frag = frag; }
}

void impl_stats(FILE *f) {
    fprintf(f, " alloc_slices=%llu alloc_retries=%llu segments=%llu",
            (unsigned long long)st_slices_alloc, (unsigned long long)st_alloc_retries,
            (unsigned long long)n_segs);
    if (proto_mem)
        fprintf(f, " mem_n=%llu mem_live=%llu mem_free=%llu mem_frag=%llu",
                (unsigned long long)m_n, (unsigned long long)m_live,
                (unsigned long long)m_free, (unsigned long long)m_frag);
}

/* A's own checker (alloc_gen.c, -DVGC_CHECK_ALLOC) runs at the bridge's
 * check points; nothing more here. */
void impl_check(const char *where) { (void)where; }
