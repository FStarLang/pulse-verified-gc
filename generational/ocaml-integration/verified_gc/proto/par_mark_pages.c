/* par_mark_pages.c — UNVERIFIED prototype, for measurement only (stage P0 of
 * docs/pages-parallel-gc-design.md on sheera/pages-parallel).  The mark of
 * the page collector, chosen at startup:
 *
 *   VERGC_MARK=hdr   the verified sequential mark, exactly as gen_gc runs
 *                    it (darken the roots, mark_loop_bounded_flagged with
 *                    ov = false): marks are black headers.  The default.
 *   VERGC_MARK=bm    a sequential bitmap mark: the verified mark's order (a
 *                    stack of objects, claimed when pushed), with the marks
 *                    in the bitmap and no header written.
 *   VERGC_MARK=bp    BP of docs/parallel-mark-prototype2.md (par_mark2.c on
 *                    sheera/parallel-mark-proto2): work packets, a pool
 *                    under one lock, field-range entries, a 32-bit CAS on the
 *                    bitmap, the work_in_flight counter; with the fixes of
 *                    the design's section 1.3 (VERGC_BP_FIX).
 *   VERGC_MARK_THREADS=k   BP's workers (default: VERGC_PAR_SWEEP_THREADS
 *                    under VERGC_SWEEP=par, else 1).
 *   VERGC_BP_FIX=n   0: par_mark2.c's rules (every busy worker shares half
 *                    its entries every 32 entries while a worker is idle and
 *                    the pool is empty; the idle loop takes packets with a
 *                    blocking lock).  1: one share per request (an idle
 *                    worker sets share_wanted; a busy worker shares only when
 *                    it wins it back by CAS and holds at least VERGC_BP_SMIN
 *                    entries).  2 (default): 1, and the idle loop never blocks
 *                    on the lock (trylock, then back to spinning on the
 *                    atomic packet count, with back-off).
 *   VERGC_POOL_LOCK=mutex|spin   the pool lock: a pthread mutex (default, as
 *                    par_mark2.c) or a test-and-test-and-set spin lock on one
 *                    32-bit CAS, which is what the verified code can build
 *                    over FStar#4812's cas.
 *   VERGC_CAS_COUNTER=1   work_in_flight updated by a CAS loop instead of
 *                    fetch-and-add (again what the verified code can build).
 *   VERGC_PKT, VERGC_CHUNK, VERGC_BP_SMIN   packet size (256), range split
 *                    size (256), the least entries worth sharing (16).
 *
 * The bitmap: one bit per heap word from zero_addr, 32-bit words, so a page
 * of PG_WORDS words is PG_WORDS / 32 whole words (the design's section 1.2).
 * Only object headers' bits are set.  It is all zero between collections:
 * the sweep (alloc_pages.c) clears what it reads.
 *
 * Threads come from proto_common.c's persistent pool (the design's fix 3).
 *
 * Checks (-DVERGC_PROTO_CHECK): after a bitmap mark, no header may be black
 * or gray (the mark wrote none); then the verified mark runs on the same
 * heap and every object must be black exactly when its bit is set, and the
 * set bits must be the claimed objects.  The sweep's oracle is then taken
 * from those black headers (proto_check.c), the headers are made white again,
 * and the bitmap sweep runs and is compared with the oracle; the bitmap must
 * then be all zero.  VERGC_MARK_CHECK_CONTROL=1 flips one bit before the
 * comparison (the check must fail); VERGC_RACE_CONTROL=1 makes BP's claim a
 * plain read-modify-write (a race ThreadSanitizer must report, and lost bits
 * the check may catch). */
#include "proto.h"
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

/* GC_Gen_Impl.c (the extracted, verified code). */
void darken_roots_bounded(heap_t heap, gray_stack_rec st, uint64_t *roots, size_t nroots);
void mark_loop_bounded_flagged(heap_t heap, gray_stack_rec st, bool ov);
void vergc_proto_mark_begin(void);
void vergc_proto_mark_end(void);
void vergc_proto_sweep(heap_t heap, uint64_t *heads, uint64_t *tbl);

#define INFIX_TAG   249ULL
#define NO_SCAN_TAG 251ULL
#define ADDR_BITS   48
#define ADDR_MASK   ((1ULL << ADDR_BITS) - 1)
#define MAXLEN      65535ULL
#define EMPTY_E     0ULL
#define CL          128
#define MAXK        8

enum { MK_HDR = 0, MK_BM = 1, MK_BP = 2 };
int       proto_mark = MK_HDR;
uint32_t *proto_bm;                  /* the bitmap (bm, bp) */
uint64_t  proto_bm_words;

static int K = 1, fix = 2, race_control, check_control, spin_lock, cas_counter;
static uint64_t CHUNK = 256, SMIN = 16;
static size_t PKT = 256;

static inline uint64_t wosize_of(uint64_t h) { return h >> 10; }
static inline uint64_t tag_of(uint64_t h) { return h & 0xffULL; }
static inline int is_heap_pointer(uint64_t v) {
    return v >= zero_addr + 8 && v < heap_size_u64 && (v & 7) == 0;
}
static inline void cpu_relax(void) { __builtin_ia32_pause(); }

static inline uint64_t bit_index(uint64_t hd) { return (hd - zero_addr) >> 3; }
static inline int bm_test(uint64_t hd) {
    uint64_t i = bit_index(hd);
    return (__atomic_load_n(&proto_bm[i >> 5], __ATOMIC_RELAXED) >> (i & 31)) & 1;
}

/* ---- statistics ---------------------------------------------------------- */
static uint64_t s_claimed, s_entries, s_fields, s_cas_fail, s_cas_neigh;
static uint64_t s_pub, s_take, s_share, s_lock_n, s_lock_cont, s_take_fail, s_rounds;
static uint64_t s_roots, s_bm_stack_max;

/* ======================================================================== */
/* The sequential bitmap mark                                              */
/* ======================================================================== */
static uint64_t *sq;            /* objects (field addresses) still to scan */
static uint64_t  sq_cap;

static inline void sq_push(uint64_t *sp, uint64_t v) {
    if (*sp == sq_cap) {
        sq_cap = sq_cap ? 2 * sq_cap : 1 << 16;
        sq = (uint64_t *)realloc(sq, sq_cap * sizeof(uint64_t));
        if (!sq) { fprintf(stderr, "bm mark: out of memory\n"); abort(); }
    }
    sq[(*sp)++] = v;
}

/* Claim (plain) and push the object a field value v points to. */
static inline void bm_visit(uint64_t *sp, uint64_t v) {
    if (!is_heap_pointer(v)) return;
    uint64_t i = bit_index(v - 8);
    if ((proto_bm[i >> 5] >> (i & 31)) & 1) return;
    uint64_t h = PW(v - 8);
    uint64_t off = wosize_of(h) * 8;
    if (tag_of(h) == INFIX_TAG && v >= off + 8) {
        v -= off;
        h = PW(v - 8);
        i = bit_index(v - 8);
        if ((proto_bm[i >> 5] >> (i & 31)) & 1) return;
    }
    if (IS_BLUE(h)) return;
    proto_bm[i >> 5] |= 1u << (i & 31);
    s_claimed++;
    if (tag_of(h) >= NO_SCAN_TAG || wosize_of(h) == 0) return;
    sq_push(sp, v);
}

static void bm_mark(uint64_t *roots, size_t n) {
    uint64_t sp = 0;
    for (size_t r = 0; r < n; r++) bm_visit(&sp, roots[r]);
    s_roots += s_claimed;
    if (sp > s_bm_stack_max) s_bm_stack_max = sp;
    while (sp > 0) {
        uint64_t v = sq[--sp], wz = wosize_of(PW(v - 8));
        s_entries++;
        s_fields += wz;
        for (uint64_t f = 0; f < wz; f++) bm_visit(&sp, PW(v + 8 * f));
        if (sp > s_bm_stack_max) s_bm_stack_max = sp;
    }
}

/* ======================================================================== */
/* BP                                                                       */
/* ======================================================================== */
typedef struct packet { struct packet *next; size_t n; uint64_t e[]; } packet_t;

static struct {
    _Alignas(CL) pthread_mutex_t mu;
    packet_t *full, *empty;
    _Alignas(CL) atomic_long nfull;          /* read without the lock */
} pool = { .mu = PTHREAD_MUTEX_INITIALIZER };

static _Alignas(CL) atomic_long work_in_flight;
static _Alignas(CL) atomic_int idle_workers;
static _Alignas(CL) atomic_int share_wanted;  /* fix >= 1 */
static char pad0[CL] __attribute__((unused));

typedef struct {
    _Alignas(CL) int id;
    packet_t *in, *out, *spare;
    uint64_t claimed, entries, fields, cas_fail, cas_neigh;
    uint64_t pub, take, share, lock_n, lock_cont, take_fail;
} worker_t;
static worker_t wk[MAXK];

static packet_t *pkt_alloc(void) {
    packet_t *p = (packet_t *)malloc(sizeof(packet_t) + PKT * sizeof(uint64_t));
    if (!p) { fprintf(stderr, "bp mark: out of memory\n"); abort(); }
    p->n = 0;
    p->next = NULL;
    return p;
}

static _Alignas(CL) uint32_t spin_word;

static inline int lk_try(void) {
    if (!spin_lock) return pthread_mutex_trylock(&pool.mu) == 0;
    uint32_t z = 0;
    return __atomic_load_n(&spin_word, __ATOMIC_RELAXED) == 0 &&
           __atomic_compare_exchange_n(&spin_word, &z, 1, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
}
static inline void lk_wait(void) {
    if (!spin_lock) { pthread_mutex_lock(&pool.mu); return; }
    while (!lk_try()) cpu_relax();
}
static inline void lk_unlock(void) {
    if (!spin_lock) { pthread_mutex_unlock(&pool.mu); return; }
    uint32_t one = 1;   /* a CAS, as the verified code would release */
    __atomic_compare_exchange_n(&spin_word, &one, 0, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
}

static inline void cnt_add(long d) {
    if (!cas_counter) { atomic_fetch_add_explicit(&work_in_flight, d, memory_order_seq_cst); return; }
    long old = atomic_load_explicit(&work_in_flight, memory_order_seq_cst);
    while (!atomic_compare_exchange_weak_explicit(&work_in_flight, &old, old + d,
                                                  memory_order_seq_cst, memory_order_seq_cst)) {}
}

static inline void pool_lock(worker_t *w) {
    w->lock_n++;
    if (!lk_try()) { w->lock_cont++; lk_wait(); }
}

static void pool_publish(worker_t *w, packet_t *p) {
    pool_lock(w);
    cnt_add(1);
    p->next = pool.full;
    pool.full = p;
    atomic_fetch_add_explicit(&pool.nfull, 1, memory_order_relaxed);
    lk_unlock();
    w->pub++;
}

/* Take a full packet (its count passes to the taker).  fix >= 2: never
 * block -- a busy lock means try again later. */
static packet_t *pool_take(worker_t *w) {
    w->lock_n++;
    if (!lk_try()) {
        w->lock_cont++;
        if (fix >= 2) { w->take_fail++; return NULL; }
        lk_wait();
    }
    packet_t *p = pool.full;
    if (p) {
        pool.full = p->next;
        atomic_fetch_sub_explicit(&pool.nfull, 1, memory_order_relaxed);
    }
    lk_unlock();
    if (p) w->take++; else w->take_fail++;
    return p;
}

static packet_t *get_empty(worker_t *w) {
    if (w->spare) { packet_t *p = w->spare; w->spare = NULL; return p; }
    pool_lock(w);
    packet_t *p = pool.empty;
    if (p) pool.empty = p->next;
    lk_unlock();
    if (!p) p = pkt_alloc();
    p->n = 0;
    return p;
}

static void put_empty(worker_t *w, packet_t *p) {
    if (!w->spare) { w->spare = p; return; }
    pool_lock(w);
    p->next = pool.empty;
    pool.empty = p;
    lk_unlock();
}

/* Publish the older half of my larger packet. */
static void pkt_share(worker_t *w) {
    packet_t *src = w->in->n >= w->out->n ? w->in : w->out;
    size_t h = src->n / 2;
    if (h == 0) return;
    packet_t *p = get_empty(w);
    memcpy(p->e, src->e, h * sizeof(uint64_t));
    p->n = h;
    memmove(src->e, src->e + h, (src->n - h) * sizeof(uint64_t));
    src->n -= h;
    w->share++;
    pool_publish(w, p);
}

static inline void push_e(worker_t *w, uint64_t e) {
    packet_t *o = w->out;
    if (o->n == PKT) {
        pool_publish(w, o);
        o = w->out = get_empty(w);
    }
    o->e[o->n++] = e;
}

static inline uint64_t pop_e(worker_t *w) {
    if (w->in->n == 0) {
        if (w->out->n == 0) return EMPTY_E;
        packet_t *t = w->in; w->in = w->out; w->out = t;
    }
    return w->in->e[--w->in->n];
}

static inline int claim(worker_t *w, uint64_t hd) {
    uint64_t i = bit_index(hd);
    uint32_t *p = &proto_bm[i >> 5], m = 1u << (i & 31);
    if (race_control) {                       /* negative control: plain RMW */
        if (*(volatile uint32_t *)p & m) return 0;
        *(volatile uint32_t *)p |= m;
        return 1;
    }
    uint32_t old = __atomic_load_n(p, __ATOMIC_RELAXED);
    for (;;) {
        if (old & m) return 0;
        if (__atomic_compare_exchange_n(p, &old, old | m, false, __ATOMIC_RELAXED, __ATOMIC_RELAXED))
            return 1;
        w->cas_fail++;
        if (old & m) return 0;
        w->cas_neigh++;
    }
}

static inline void push_obj(worker_t *w, uint64_t v, uint64_t wz) {
    while (wz > 0) {
        uint64_t l = wz < MAXLEN ? wz : MAXLEN;
        push_e(w, v | (l << ADDR_BITS));
        v += l * 8;
        wz -= l;
    }
}

static inline void visit(worker_t *w, uint64_t v) {
    if (!is_heap_pointer(v)) return;
    if (bm_test(v - 8)) return;              /* bitmap first */
    uint64_t h = PW(v - 8);
    uint64_t off = wosize_of(h) * 8;
    if (tag_of(h) == INFIX_TAG && v >= off + 8) {
        v -= off;
        h = PW(v - 8);
    }
    if (IS_BLUE(h)) return;
    if (!claim(w, v - 8)) return;
    w->claimed++;
    uint64_t wz = wosize_of(h);
    if (tag_of(h) >= NO_SCAN_TAG || wz == 0) return;
    push_obj(w, v, wz);
}

static inline void scan_entry(worker_t *w, uint64_t e) {
    uint64_t start = e & ADDR_MASK, len = e >> ADDR_BITS;
    w->entries++;
    if (len > CHUNK) {
        push_e(w, (start + CHUNK * 8) | ((len - CHUNK) << ADDR_BITS));
        len = CHUNK;
    }
    w->fields += len;
    for (uint64_t i = 0; i < len; i++) visit(w, PW(start + i * 8));
}

static inline size_t held(worker_t *w) { return w->in->n + w->out->n; }

/* Every 32 entries: share if asked to. */
static inline void maybe_share(worker_t *w) {
    if (atomic_load_explicit(&pool.nfull, memory_order_relaxed) != 0) return;
    if (fix == 0) {
        if (atomic_load_explicit(&idle_workers, memory_order_relaxed) > 0) pkt_share(w);
        return;
    }
    if (atomic_load_explicit(&share_wanted, memory_order_relaxed) == 0) return;
    packet_t *src = w->in->n >= w->out->n ? w->in : w->out;
    if (src->n < SMIN) return;
    int one = 1;
    if (atomic_compare_exchange_strong_explicit(&share_wanted, &one, 0, memory_order_relaxed,
                                                memory_order_relaxed))
        pkt_share(w);
}

/* Find work or see 0.  On return with an entry the worker holds a count. */
static uint64_t idle_loop(worker_t *w) {
    uint64_t got = EMPTY_E;
    unsigned spins = 0, backoff = 1;
    atomic_fetch_add_explicit(&idle_workers, 1, memory_order_relaxed);
    for (;;) {
        if (atomic_load_explicit(&pool.nfull, memory_order_relaxed) > 0) {
            packet_t *p = pool_take(w);
            if (p) {
                put_empty(w, w->in);
                w->in = p;
                got = w->in->e[--w->in->n];
                break;
            }
        } else if (fix >= 1 && (spins & 63) == 0 &&
                   atomic_load_explicit(&share_wanted, memory_order_relaxed) == 0) {
            atomic_store_explicit(&share_wanted, 1, memory_order_relaxed);
        }
        if (atomic_load_explicit(&work_in_flight, memory_order_seq_cst) == 0) break;
        spins++;
        if (fix >= 2) {
            for (unsigned b = 0; b < backoff; b++) cpu_relax();
            if (backoff < 64) backoff <<= 1;
            if (spins > 65536) sched_yield();
        } else {
            if (spins > 4096) sched_yield(); else cpu_relax();
        }
    }
    atomic_fetch_sub_explicit(&idle_workers, 1, memory_order_relaxed);
    return got;
}

static void worker_main(worker_t *w) {
    int active = 0;
    unsigned tick = 0;
    for (;;) {
        uint64_t e;
        while ((e = pop_e(w)) != EMPTY_E) {
            scan_entry(w, e);
            if ((++tick & 31) == 0) maybe_share(w);
        }
        if (active) {
            cnt_add(-1);
            active = 0;
        }
        e = idle_loop(w);
        if (e == EMPTY_E) break;
        active = 1;
        scan_entry(w, e);
    }
}

static void bp_job(int i, int n, void *arg) { (void)n; (void)arg; worker_main(&wk[i]); }

/* Claim the roots on this thread and pack them into packets in the pool. */
static size_t setup_roots(uint64_t *roots, size_t n) {
    worker_t *m = &wk[0];
    size_t pushed = 0;
    packet_t *p = NULL;
    for (size_t r = 0; r < n; r++) {
        uint64_t v = roots[r];
        if (!is_heap_pointer(v)) continue;
        uint64_t h = PW(v - 8), off = wosize_of(h) * 8;
        if (tag_of(h) == INFIX_TAG && v >= off + 8) { v -= off; h = PW(v - 8); }
        if (IS_BLUE(h) || !claim(m, v - 8)) continue;
        m->claimed++;
        s_roots++;
        uint64_t wz = wosize_of(h);
        if (tag_of(h) >= NO_SCAN_TAG || wz == 0) continue;
        for (uint64_t a = v; wz > 0;) {
            uint64_t l = wz < MAXLEN ? wz : MAXLEN;
            if (!p) {
                p = pool.empty ? pool.empty : pkt_alloc();
                if (p == pool.empty) pool.empty = p->next;
                p->n = 0;
            }
            p->e[p->n++] = a | (l << ADDR_BITS);
            if (p->n == PKT) { p->next = pool.full; pool.full = p; pool.nfull++; p = NULL; }
            pushed++;
            a += l * 8;
            wz -= l;
        }
    }
    if (p) { p->next = pool.full; pool.full = p; pool.nfull++; }
    return pushed;
}

static void bp_mark(uint64_t *roots, size_t n) {
    for (int i = 0; i < K; i++) {
        worker_t *w = &wk[i];
        w->claimed = w->entries = w->fields = w->cas_fail = w->cas_neigh = 0;
        w->pub = w->take = w->share = w->lock_n = w->lock_cont = w->take_fail = 0;
        if (!w->in) { w->in = pkt_alloc(); w->out = pkt_alloc(); }
        w->id = i;
    }
    size_t pushed = setup_roots(roots, n);
    atomic_store(&share_wanted, 0);
    atomic_store(&idle_workers, 0);
    atomic_store(&work_in_flight, atomic_load(&pool.nfull));
    if (pushed > 0) {
        extern int proto_pool_record;
        proto_pool_record = 0;
        proto_pool_run(K, bp_job, NULL);
        proto_pool_record = 1;
        s_rounds++;
    }
    if (atomic_load(&work_in_flight) != 0 || pool.full != NULL) {
        fprintf(stderr, "bp mark: round ended with work left\n");
        abort();
    }
    for (int i = 0; i < K; i++) {
        worker_t *w = &wk[i];
        if (w->in->n || w->out->n) { fprintf(stderr, "bp mark: worker %d not empty\n", i); abort(); }
        s_claimed += w->claimed; s_entries += w->entries; s_fields += w->fields;
        s_cas_fail += w->cas_fail; s_cas_neigh += w->cas_neigh;
        s_pub += w->pub; s_take += w->take; s_share += w->share;
        s_lock_n += w->lock_n; s_lock_cont += w->lock_cont; s_take_fail += w->take_fail;
    }
}

/* ======================================================================== */
/* Setup, the collector's entry point, and the checks                       */
/* ======================================================================== */
static int inited;

static void mark_init(void) {
    inited = 1;
    const char *m = getenv("VERGC_MARK");
    if (m == NULL || strcmp(m, "hdr") == 0) proto_mark = MK_HDR;
    else if (strcmp(m, "bm") == 0) proto_mark = MK_BM;
    else if (strcmp(m, "bp") == 0) proto_mark = MK_BP;
    else { fprintf(stderr, "VERGC_MARK=%s: expected hdr, bm or bp\n", m); exit(2); }
    K = proto_mode == SW_PAR ? proto_threads : 1;
    const char *t = getenv("VERGC_MARK_THREADS");
    if (t) K = atoi(t);
    if (K < 1 || K > MAXK) { fprintf(stderr, "VERGC_MARK_THREADS: expected 1..%d\n", MAXK); exit(2); }
    const char *s;
    if ((s = getenv("VERGC_BP_FIX"))) fix = atoi(s);
    if ((s = getenv("VERGC_PKT"))) PKT = (size_t)atol(s);
    if ((s = getenv("VERGC_CHUNK"))) CHUNK = (uint64_t)atol(s);
    if ((s = getenv("VERGC_BP_SMIN"))) SMIN = (uint64_t)atol(s);
    if ((s = getenv("VERGC_RACE_CONTROL"))) race_control = atoi(s);
    if ((s = getenv("VERGC_POOL_LOCK"))) {
        if (strcmp(s, "spin") == 0) spin_lock = 1;
        else if (strcmp(s, "mutex") != 0) { fprintf(stderr, "VERGC_POOL_LOCK: mutex or spin\n"); exit(2); }
    }
    if ((s = getenv("VERGC_CAS_COUNTER"))) cas_counter = atoi(s);
    if ((s = getenv("VERGC_MARK_CHECK_CONTROL"))) check_control = atoi(s);
    if (PKT < 2 || CHUNK < 1) { fprintf(stderr, "VERGC_PKT >= 2, VERGC_CHUNK >= 1\n"); exit(2); }
    if (heap_size_u64 >= (1ULL << ADDR_BITS)) { fprintf(stderr, "bp mark: heap above 2^48\n"); exit(2); }
    if (proto_mark != MK_HDR) {
        proto_bm_words = ((heap_size_u64 - zero_addr) / 8 + 31) / 32;
        proto_bm = (uint32_t *)calloc((size_t)proto_bm_words, sizeof(uint32_t));
        if (!proto_bm) { fprintf(stderr, "mark: calloc bitmap\n"); exit(2); }
    }
}

#ifdef VERGC_PROTO_CHECK
static uint64_t n_mark_checks;

static uint64_t count_bits(void) {
    uint64_t n = 0;
    for (uint64_t i = 0; i < proto_bm_words; i++) n += (uint64_t)__builtin_popcount(proto_bm[i]);
    return n;
}

/* After a bitmap mark: no header black or gray; then the verified mark on
 * the same heap, black exactly where a bit is set. */
static void check_bitmap_mark(heap_t heap, gray_stack_rec st, uint64_t *roots, size_t nroots,
                              uint64_t claimed) {
    uint64_t z = zero_addr, hs = heap_size_u64, nobj = 0;
    for (uint64_t c = z; c + 8 < hs; c += (HD_WZ(PW(c)) + 1) * 8)
        if (HD_COL(PW(c)) == 1 || HD_COL(PW(c)) == COL_BLACK)
            chk_fail("bitmap mark", "a header was coloured", c, PW(c));
    uint64_t bits = count_bits();
    if (bits != claimed) chk_fail("bitmap mark", "set bits differ from claims", bits, claimed);
    if (check_control == 1) {            /* negative control: flip one bit */
        for (uint64_t c = z; c + 8 < hs; c += (HD_WZ(PW(c)) + 1) * 8)
            if (!IS_BLUE(PW(c))) {
                uint64_t i = bit_index(c);
                proto_bm[i >> 5] ^= 1u << (i & 31);
                break;
            }
    }
    darken_roots_bounded(heap, st, roots, nroots);
    mark_loop_bounded_flagged(heap, st, false);
    uint64_t diff = 0, first = 0;
    for (uint64_t c = z; c + 8 < hs; c += (HD_WZ(PW(c)) + 1) * 8) {
        nobj++;
        uint64_t i = bit_index(c);
        int bit = (proto_bm[i >> 5] >> (i & 31)) & 1;
        if (bit != IS_BLACK(PW(c))) { if (!diff) first = c; diff++; }
    }
    if (diff) {
        fprintf(stderr, "VERGC_MARK_CHECK: %llu of %llu headers differ from the bitmap\n",
                (unsigned long long)diff, (unsigned long long)nobj);
        chk_fail("bitmap mark", "differs from the verified mark", first, PW(first));
    }
    n_mark_checks++;
}

/* Called by the sweep once the oracle is taken: make the headers white
 * again, so the bitmap sweep sees the heap a bitmap mark leaves. */
void proto_mark_after_oracle(void) {
    if (proto_mark == MK_HDR) return;
    for (uint64_t c = zero_addr; c + 8 < heap_size_u64; c += (HD_WZ(PW(c)) + 1) * 8)
        if (IS_BLACK(PW(c))) PW(c) = WHITEN(PW(c));
}

/* After the sweep: the bitmap is all zero. */
void proto_mark_after_sweep(void) {
    if (proto_mark == MK_HDR) return;
    for (uint64_t i = 0; i < proto_bm_words; i++)
        if (proto_bm[i]) chk_fail("bitmap sweep", "a bit is left set", i, proto_bm[i]);
}
#endif

void vergc_proto_collect(heap_t heap, gray_stack_rec st, uint64_t *heads, uint64_t *tbl,
                         uint64_t *roots, size_t nroots) {
    if (!inited) mark_init();
    vergc_proto_mark_begin();
    uint64_t c0 = s_claimed;
    switch (proto_mark) {
    case MK_HDR:
        darken_roots_bounded(heap, st, roots, nroots);
        mark_loop_bounded_flagged(heap, st, false);
        break;
    case MK_BM:
        bm_mark(roots, nroots);
        break;
    default:
        bp_mark(roots, nroots);
    }
    vergc_proto_mark_end();
#ifdef VERGC_PROTO_CHECK
    if (proto_mark != MK_HDR) check_bitmap_mark(heap, st, roots, nroots, s_claimed - c0);
#else
    (void)c0;
#endif
    vergc_proto_sweep(heap, heads, tbl);
}

void proto_mark_stats(FILE *f) {
    static const char *names[] = {"hdr", "bm", "bp"};
    if (!inited) return;
    fprintf(f, " mark=%s mark_threads=%d", names[proto_mark], proto_mark == MK_BP ? K : 1);
    if (proto_mark == MK_HDR) return;
    fprintf(f, " claimed=%llu roots=%llu entries=%llu fields=%llu",
            (unsigned long long)s_claimed, (unsigned long long)s_roots,
            (unsigned long long)s_entries, (unsigned long long)s_fields);
    if (proto_mark == MK_BM)
        fprintf(f, " bm_stack_max=%llu", (unsigned long long)s_bm_stack_max);
    if (proto_mark == MK_BP)
        fprintf(f, " pool_lock=%s cas_counter=%d", spin_lock ? "spin" : "mutex", cas_counter),
        fprintf(f, " bp_fix=%d pkt=%zu chunk=%llu cas_fail=%llu cas_neigh=%llu pub=%llu take=%llu"
                   " take_fail=%llu share=%llu lock_n=%llu lock_cont=%llu rounds=%llu",
                fix, PKT, (unsigned long long)CHUNK, (unsigned long long)s_cas_fail,
                (unsigned long long)s_cas_neigh, (unsigned long long)s_pub,
                (unsigned long long)s_take, (unsigned long long)s_take_fail,
                (unsigned long long)s_share, (unsigned long long)s_lock_n,
                (unsigned long long)s_lock_cont, (unsigned long long)s_rounds);
#ifdef VERGC_PROTO_CHECK
    fprintf(f, " mark_checks=%llu", (unsigned long long)n_mark_checks);
#endif
}
