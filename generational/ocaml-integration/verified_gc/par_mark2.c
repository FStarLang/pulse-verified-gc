/* par_mark2.c — UNVERIFIED prototype, for measurement only; never to be
 * merged.  A parallel mark after established designs, beside par_mark.c's
 * ownership design (docs/parallel-mark-prototype2.md):
 *
 *   Marking as in OCaml 5 (Sivaramakrishnan et al., ICFP 2020; runtime/
 *   major_gc.c): no grey colour -- an object is grey by being on a mark
 *   stack -- and mark stack entries are field ranges.  An entry is one word:
 *   the address of its first field (low 48 bits) and its length in fields
 *   (high 16 bits), so that a Chase-Lev slot is one atomic word.  An object
 *   is pushed as one range (more if it has over 65535 fields); a range of
 *   more than CHUNK fields is split when popped, the rest pushed back first,
 *   so a large object's fields can be taken by other workers.
 *
 *   Claiming (VGC_PAR_VARIANT's first letter):
 *     A  CAS on the header word, white -> black (C11 64-bit atomics);
 *     B  a side mark bitmap, one bit per heap word, set with a 32-bit CAS;
 *        headers are not written by the mark, and the sweep
 *        (vergc_par2_sweep) reads and clears the bitmap.
 *
 *   Load balancing (second letter):
 *     P  a shared pool of work packets under one lock (Ossia et al., PLDI
 *        2002): each worker pops from an input packet and pushes to an
 *        output packet, publishes the output when full, and takes a packet
 *        from the pool when both are empty.  When some worker is idle and
 *        the pool is empty, a worker also publishes the older half of its
 *        entries (otherwise a deep structure stays on one worker forever).
 *     S  work stealing on Chase-Lev deques (Flood et al., 2001), in the C11
 *        form of Le et al. (PPoPP 2013) with seq_cst operations in place of
 *        the fences; a thief takes one entry from the top of a random
 *        victim's deque.  Deques grow; old arrays are freed after the join.
 *
 *   Termination: work_in_flight from docs/parallel-mark-design.md, counting
 *   here the workers holding work plus (P) the packets in the pool.  A worker
 *   holds one count while it has entries or is scanning; it gives it up when
 *   its own stack or packets are empty.  P: publishing adds 1 under the pool
 *   lock; taking a packet takes over that count.  S: a thief adds 1 before
 *   it tries to steal and takes it back if the steal fails.  So a 0 means no
 *   entry exists anywhere and no worker is scanning: a 0 is final, and a
 *   worker that reads 0 returns.
 *
 *   Threads: k workers started for each collection and joined.
 *
 * Environment (with VGC_PAR_MARK=k): VGC_PAR_VARIANT=AP|AS|BP|BS selects
 * this file; VGC_PAR_CHUNK=n (default 256), VGC_PAR_PKT=n (default 256).
 * VGC_PAR_RACE_CONTROL=1 makes the claim a plain read-modify-write: a data
 * race ThreadSanitizer must report (and, for B, lost bits the check may
 * catch).  Statistics and VGC_PAR_PROF as par_mark.c.
 */

#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/sysctl.h>
#include <x86intrin.h>

#include "GC_Gen_Impl.h"
#include "GC_Spec_ZeroAddr.h"

#define WHITE 0ULL
#define BLUE  2ULL
#define BLACK 3ULL
#define INFIX_TAG 249ULL
#define NO_SCAN_TAG 251ULL

#define MAXK 64
#define CL 128
#define ADDR_BITS 48
#define ADDR_MASK ((1ULL << ADDR_BITS) - 1)
#define MAXLEN 65535ULL
#define EMPTY_E 0ULL           /* no entry has length 0 */

static inline uint64_t colour_of(uint64_t h) { return (h >> 8) & 3ULL; }
static inline uint64_t wosize_of(uint64_t h) { return h >> 10; }
static inline uint64_t tag_of(uint64_t h) { return h & 0xffULL; }
static inline uint64_t with_colour(uint64_t h, uint64_t c) { return (h & ~(3ULL << 8)) | (c << 8); }
static inline int is_heap_pointer(uint64_t v)
{
  return v >= zero_addr + 8 && v < heap_size_u64 && (v & 7) == 0;
}
#define WORD(a) (*(uint64_t *)(uintptr_t)(a))
#define AWORD(a) ((_Atomic uint64_t *)(uintptr_t)(a))

static inline void cpu_relax(void) { __builtin_ia32_pause(); }
static inline uint64_t tsc(void) { return __rdtsc(); }
static double now_us(void)
{
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e6 + ts.tv_nsec / 1e3;
}

/* ------------------------------------------------------------------ */
/* Configuration                                                       */

static int K, claimB, steal_lb, stats, prof, race_control;
static uint64_t CHUNK = 256;
static size_t PKT = 256;

static _Atomic uint32_t *bitmap;   /* B: bit i is heap word zero_addr + 8 i */

static _Alignas(CL) atomic_long work_in_flight;
static _Alignas(CL) atomic_int idle_workers;   /* P: workers in their idle loop */
static char pad0[CL] __attribute__((unused));

/* ------------------------------------------------------------------ */
/* Chase-Lev deque (S)                                                 */

typedef struct ring {
  int64_t mask;
  struct ring *prev;               /* older arrays, freed after the join */
  _Atomic uint64_t slot[];
} ring_t;

typedef struct {
  _Alignas(CL) atomic_llong top;
  _Alignas(CL) atomic_llong bottom;
  _Atomic(ring_t *) arr;
} deque_t;

static ring_t *ring_new(int64_t size, ring_t *prev)
{
  ring_t *r = malloc(sizeof(ring_t) + (size_t)size * sizeof(uint64_t));
  if (!r) { fprintf(stderr, "par_mark2: out of memory\n"); abort(); }
  r->mask = size - 1;
  r->prev = prev;
  return r;
}

/* ------------------------------------------------------------------ */
/* Packets (P)                                                         */

typedef struct packet {
  struct packet *next;
  size_t n;
  uint64_t e[];
} packet_t;

static struct {
  _Alignas(CL) pthread_mutex_t mu;
  packet_t *full, *empty;
  _Alignas(CL) atomic_long nfull;  /* read without the lock by idle workers */
} pool;

/* ------------------------------------------------------------------ */
/* Workers                                                             */

typedef struct {
  _Alignas(CL) int id;
  int counted;                     /* S: given a count by the main thread */
  uint64_t rng;
  /* S */
  deque_t dq;
  /* P */
  packet_t *in, *out, *spare;
  /* statistics, private */
  uint64_t entries, fields, claimed, cas_fail, cas_lost, cas_neigh;
  uint64_t steal_try, steal_ok, steal_abort, probe_empty;
  uint64_t pkt_pub, pkt_take, pkt_share, pkt_get, lock_n, lock_cont;
  uint64_t cnt_n, idle_spins;
  /* VGC_PAR_PROF, cycles; disjoint buckets */
  uint64_t c_tot, c_idle, c_steal, c_pool, c_lockwait;
  double t_start, t_end;
} worker_t;

static worker_t wk[MAXK];

static struct {
  long rounds;
  double round_us, setup_us, create_us, start_lat_us, join_lat_us;
  uint64_t entries, fields, claimed, cas_fail, cas_lost, cas_neigh;
  uint64_t steal_try, steal_ok, steal_abort, probe_empty;
  uint64_t pkt_pub, pkt_take, pkt_share, pkt_get, lock_n, lock_cont, cnt_n, idle_spins;
  uint64_t c_tot, c_idle, c_steal, c_pool, c_lockwait, c_max_tot;
  uint64_t per_worker_claimed[MAXK];
  uint64_t roots_claimed;
} st2;

/* ---- claiming ---- */

static inline uint64_t hdr_load(uint64_t a)
{
  /* A: headers are CASed concurrently, so read them atomically.  B: the
   * mark never writes a header. */
  if (claimB) return WORD(a);
  return atomic_load_explicit(AWORD(a), memory_order_relaxed);
}

/* Claim the object whose header is at hd, with header value h (white). */
static inline int claim(worker_t *w, uint64_t hd, uint64_t h)
{
  if (claimB) {
    uint64_t i = (hd - zero_addr) >> 3;
    _Atomic uint32_t *p = &bitmap[i >> 5];
    uint32_t m = 1u << (i & 31);
    if (race_control) {                      /* negative control: plain RMW */
      uint32_t *q = (uint32_t *)p;
      if (*q & m) return 0;
      *q |= m;
      return 1;
    }
    uint32_t old = atomic_load_explicit(p, memory_order_relaxed);
    for (;;) {
      if (old & m) return 0;
      if (atomic_compare_exchange_strong_explicit(p, &old, old | m, memory_order_relaxed,
                                                  memory_order_relaxed))
        return 1;
      w->cas_fail++;
      if (old & m) { w->cas_lost++; return 0; }
      w->cas_neigh++;
    }
  } else {
    if (race_control) {                      /* negative control: plain store */
      if (colour_of(WORD(hd)) != WHITE) return 0;
      WORD(hd) = with_colour(h, BLACK);
      return 1;
    }
    uint64_t exp = h;
    if (atomic_compare_exchange_strong_explicit(AWORD(hd), &exp, with_colour(h, BLACK),
                                                memory_order_relaxed, memory_order_relaxed))
      return 1;
    w->cas_fail++;
    w->cas_lost++;                           /* only the colour changes during the mark */
    return 0;
  }
}

static inline int is_marked_B(uint64_t hd)
{
  uint64_t i = (hd - zero_addr) >> 3;
  return (atomic_load_explicit(&bitmap[i >> 5], memory_order_relaxed) >> (i & 31)) & 1;
}

/* ---- the two kinds of local stack ---- */

static void deque_grow(deque_t *d, int64_t b, int64_t t)
{
  ring_t *a = atomic_load_explicit(&d->arr, memory_order_relaxed);
  ring_t *n = ring_new((a->mask + 1) * 2, a);
  for (int64_t i = t; i < b; i++)
    atomic_store_explicit(&n->slot[i & n->mask],
                          atomic_load_explicit(&a->slot[i & a->mask], memory_order_relaxed),
                          memory_order_relaxed);
  atomic_store_explicit(&d->arr, n, memory_order_release);
}

static inline void dq_push(deque_t *d, uint64_t x)
{
  int64_t b = atomic_load_explicit(&d->bottom, memory_order_relaxed);
  int64_t t = atomic_load_explicit(&d->top, memory_order_acquire);
  ring_t *a = atomic_load_explicit(&d->arr, memory_order_relaxed);
  if (b - t > a->mask) { deque_grow(d, b, t); a = atomic_load_explicit(&d->arr, memory_order_relaxed); }
  atomic_store_explicit(&a->slot[b & a->mask], x, memory_order_relaxed);
  atomic_store_explicit(&d->bottom, b + 1, memory_order_release);
}

static inline uint64_t dq_pop(deque_t *d)
{
  int64_t b = atomic_load_explicit(&d->bottom, memory_order_relaxed) - 1;
  ring_t *a = atomic_load_explicit(&d->arr, memory_order_relaxed);
  atomic_store_explicit(&d->bottom, b, memory_order_seq_cst);
  int64_t t = atomic_load_explicit(&d->top, memory_order_seq_cst);
  if (t > b) {                                       /* empty */
    atomic_store_explicit(&d->bottom, b + 1, memory_order_relaxed);
    return EMPTY_E;
  }
  uint64_t x = atomic_load_explicit(&a->slot[b & a->mask], memory_order_relaxed);
  if (t == b) {                                      /* last entry: race the thieves */
    if (!atomic_compare_exchange_strong_explicit(&d->top, &t, t + 1, memory_order_seq_cst,
                                                 memory_order_relaxed))
      x = EMPTY_E;
    atomic_store_explicit(&d->bottom, b + 1, memory_order_relaxed);
  }
  return x;
}

/* 1: got *out; 0: empty; -1: lost a race */
static inline int dq_steal(deque_t *d, uint64_t *out)
{
  int64_t t = atomic_load_explicit(&d->top, memory_order_seq_cst);
  int64_t b = atomic_load_explicit(&d->bottom, memory_order_seq_cst);
  if (t >= b) return 0;
  ring_t *a = atomic_load_explicit(&d->arr, memory_order_acquire);
  uint64_t x = atomic_load_explicit(&a->slot[t & a->mask], memory_order_relaxed);
  if (!atomic_compare_exchange_strong_explicit(&d->top, &t, t + 1, memory_order_seq_cst,
                                               memory_order_relaxed))
    return -1;
  *out = x;
  return 1;
}

static inline int dq_nonempty(deque_t *d)
{
  return atomic_load_explicit(&d->top, memory_order_relaxed) <
         atomic_load_explicit(&d->bottom, memory_order_relaxed);
}

static packet_t *pkt_alloc(void)
{
  packet_t *p = malloc(sizeof(packet_t) + PKT * sizeof(uint64_t));
  if (!p) { fprintf(stderr, "par_mark2: out of memory\n"); abort(); }
  p->n = 0;
  p->next = NULL;
  return p;
}

static inline void pool_lock(worker_t *w)
{
  w->lock_n++;
  if (prof) {
    uint64_t t = tsc();
    if (pthread_mutex_trylock(&pool.mu) != 0) { w->lock_cont++; pthread_mutex_lock(&pool.mu); }
    w->c_lockwait += tsc() - t;
  } else if (pthread_mutex_trylock(&pool.mu) != 0) {
    w->lock_cont++;
    pthread_mutex_lock(&pool.mu);
  }
}

/* Publish a non-empty packet: one count for it, added under the lock while
 * the publisher still holds its own count. */
static void pool_publish(worker_t *w, packet_t *p)
{
  uint64_t t = prof ? tsc() : 0;
  pool_lock(w);
  atomic_fetch_add_explicit(&work_in_flight, 1, memory_order_seq_cst);
  w->cnt_n++;
  p->next = pool.full;
  pool.full = p;
  atomic_fetch_add_explicit(&pool.nfull, 1, memory_order_relaxed);
  pthread_mutex_unlock(&pool.mu);
  w->pkt_pub++;
  if (prof) w->c_pool += tsc() - t;
}

/* Take a packet; its count passes to the taker. */
static packet_t *pool_take(worker_t *w)
{
  uint64_t t = prof ? tsc() : 0;
  pool_lock(w);
  packet_t *p = pool.full;
  if (p) {
    pool.full = p->next;
    atomic_fetch_sub_explicit(&pool.nfull, 1, memory_order_relaxed);
  }
  pthread_mutex_unlock(&pool.mu);
  if (p) w->pkt_take++;
  if (prof) w->c_pool += tsc() - t;
  return p;
}

static packet_t *get_empty(worker_t *w)
{
  if (w->spare) { packet_t *p = w->spare; w->spare = NULL; return p; }
  uint64_t t = prof ? tsc() : 0;
  pool_lock(w);
  packet_t *p = pool.empty;
  if (p) pool.empty = p->next;
  pthread_mutex_unlock(&pool.mu);
  w->pkt_get++;
  if (!p) p = pkt_alloc();
  p->n = 0;
  if (prof) w->c_pool += tsc() - t;
  return p;
}

static void put_empty(worker_t *w, packet_t *p)
{
  if (!w->spare) { w->spare = p; return; }
  pool_lock(w);
  p->next = pool.empty;
  pool.empty = p;
  pthread_mutex_unlock(&pool.mu);
}

/* P: give the older half of my entries to idle workers. */
static void pkt_share(worker_t *w)
{
  packet_t *src = w->in->n >= w->out->n ? w->in : w->out;
  size_t h = src->n / 2;
  if (h == 0) return;
  packet_t *p = get_empty(w);
  memcpy(p->e, src->e, h * sizeof(uint64_t));
  p->n = h;
  memmove(src->e, src->e + h, (src->n - h) * sizeof(uint64_t));
  src->n -= h;
  w->pkt_share++;
  pool_publish(w, p);
}

static inline void push_e(worker_t *w, uint64_t e)
{
  if (steal_lb) { dq_push(&w->dq, e); return; }
  packet_t *o = w->out;
  if (o->n == PKT) {
    pool_publish(w, o);
    o = w->out = get_empty(w);
  }
  o->e[o->n++] = e;
}

static inline uint64_t pop_e(worker_t *w)
{
  if (steal_lb) return dq_pop(&w->dq);
  if (w->in->n == 0) {
    if (w->out->n == 0) return EMPTY_E;
    packet_t *t = w->in; w->in = w->out; w->out = t;
  }
  return w->in->e[--w->in->n];
}

/* Push the fields of the object at v (wz fields). */
static inline void push_obj(worker_t *w, uint64_t v, uint64_t wz)
{
  while (wz > 0) {
    uint64_t l = wz < MAXLEN ? wz : MAXLEN;
    push_e(w, v | (l << ADDR_BITS));
    v += l * 8;
    wz -= l;
  }
}

/* Mark through one field value. */
static inline void visit(worker_t *w, uint64_t v)
{
  if (!is_heap_pointer(v)) return;
  /* B: test the mark without touching the object.  Only object headers'
   * bits are ever set, so a set bit at v - 8 means v is a marked object (an
   * infix pointer's v - 8 is never set: it is resolved below). */
  if (claimB && is_marked_B(v - 8)) return;
  uint64_t h = hdr_load(v - 8);
  uint64_t off = wosize_of(h) * 8;
  if (tag_of(h) == INFIX_TAG && v >= off + 8) {
    v -= off;
    h = hdr_load(v - 8);
  }
  if (colour_of(h) != WHITE) return;
  if (!claim(w, v - 8, h)) return;      /* B: the claim's first load tests the bit */
  w->claimed++;
  uint64_t wz = wosize_of(h);
  if (tag_of(h) >= NO_SCAN_TAG || wz == 0) return;
  push_obj(w, v, wz);
}

static inline void scan_entry(worker_t *w, uint64_t e)
{
  uint64_t start = e & ADDR_MASK, len = e >> ADDR_BITS;
  w->entries++;
  if (len > CHUNK) {
    push_e(w, (start + CHUNK * 8) | ((len - CHUNK) << ADDR_BITS));
    len = CHUNK;
  }
  w->fields += len;
  for (uint64_t i = 0; i < len; i++) visit(w, WORD(start + i * 8));
}

static inline uint64_t xorshift(uint64_t *s)
{
  uint64_t x = *s;
  x ^= x << 13; x ^= x >> 7; x ^= x << 17;
  return *s = x;
}

/* Idle: find work or see 0.  Returns an entry, or EMPTY_E when the round is
 * over.  On return with an entry the worker holds a count. */
static uint64_t idle_loop(worker_t *w)
{
  uint64_t t0 = prof ? tsc() : 0, inner0 = w->c_steal + w->c_pool;
  uint64_t got = EMPTY_E;
  unsigned spins = 0;
  if (!steal_lb) atomic_fetch_add_explicit(&idle_workers, 1, memory_order_relaxed);
  for (;;) {
    if (steal_lb) {
      for (int a = 0; a < 2 * K && K > 1; a++) {
        unsigned v = (unsigned)(xorshift(&w->rng) % (uint64_t)(K - 1));
        if (v >= (unsigned)w->id) v++;
        deque_t *d = &wk[v].dq;
        if (!dq_nonempty(d)) { w->probe_empty++; continue; }
        uint64_t s0 = prof ? tsc() : 0;
        atomic_fetch_add_explicit(&work_in_flight, 1, memory_order_seq_cst);
        w->cnt_n++;
        w->steal_try++;
        uint64_t x;
        int r = dq_steal(d, &x);
        if (r == 1) {
          w->steal_ok++;
          if (prof) w->c_steal += tsc() - s0;
          got = x;
          goto out;
        }
        if (r < 0) w->steal_abort++;
        atomic_fetch_sub_explicit(&work_in_flight, 1, memory_order_seq_cst);
        w->cnt_n++;
        if (prof) w->c_steal += tsc() - s0;
      }
    } else if (atomic_load_explicit(&pool.nfull, memory_order_relaxed) > 0) {
      packet_t *p = pool_take(w);
      if (p) {
        put_empty(w, w->in);
        w->in = p;
        got = w->in->e[--w->in->n];
        goto out;
      }
    }
    long c = atomic_load_explicit(&work_in_flight, memory_order_seq_cst);
    if (c == 0) break;
    w->idle_spins++;
    if (++spins > 4096) sched_yield(); else cpu_relax();
  }
out:
  if (!steal_lb) atomic_fetch_sub_explicit(&idle_workers, 1, memory_order_relaxed);
  if (prof) w->c_idle += (tsc() - t0) - ((w->c_steal + w->c_pool) - inner0);
  return got;
}

static void *worker_main(void *arg)
{
  worker_t *w = arg;
  if (stats) w->t_start = now_us();
  uint64_t c0 = prof ? tsc() : 0;
  /* Not dq_nonempty: a thief may empty the deque before this thread starts. */
  int active = w->counted;
  unsigned tick = 0;
  for (;;) {
    uint64_t e;
    while ((e = pop_e(w)) != EMPTY_E) {
      scan_entry(w, e);
      if (!steal_lb && (++tick & 31) == 0 &&
          atomic_load_explicit(&idle_workers, memory_order_relaxed) > 0 &&
          atomic_load_explicit(&pool.nfull, memory_order_relaxed) == 0)
        pkt_share(w);
    }
    if (active) {
      atomic_fetch_sub_explicit(&work_in_flight, 1, memory_order_seq_cst);
      w->cnt_n++;
      active = 0;
    }
    e = idle_loop(w);
    if (e == EMPTY_E) break;
    active = 1;
    scan_entry(w, e);
  }
  if (prof) w->c_tot += tsc() - c0;
  if (stats) w->t_end = now_us();
  return NULL;
}

/* ------------------------------------------------------------------ */
/* Main thread                                                         */

static size_t setup_roots(uint64_t *roots, size_t n)
{
  worker_t *m = &wk[0];     /* claim statistics go to worker 0 */
  size_t pushed = 0, rr = 0;
  packet_t *p = NULL;
  for (size_t i = 0; i < n; i++) {
    uint64_t v = roots[i];
    if (!is_heap_pointer(v)) continue;
    uint64_t h = WORD(v - 8);
    uint64_t off = wosize_of(h) * 8;
    if (tag_of(h) == INFIX_TAG && v >= off + 8) { v -= off; h = WORD(v - 8); }
    if (colour_of(h) != WHITE) continue;
    if (!claim(m, v - 8, h)) continue;
    st2.roots_claimed++;
    uint64_t wz = wosize_of(h);
    if (tag_of(h) >= NO_SCAN_TAG || wz == 0) continue;
    for (uint64_t a = v; wz > 0;) {
      uint64_t l = wz < MAXLEN ? wz : MAXLEN, e = a | (l << ADDR_BITS);
      if (steal_lb) dq_push(&wk[rr++ % (size_t)K].dq, e);
      else {
        if (!p) p = pool.empty ? pool.empty : pkt_alloc();
        if (p == pool.empty) pool.empty = p->next;
        p->e[p->n++] = e;
        if (p->n == PKT) { p->next = pool.full; pool.full = p; pool.nfull++; p = NULL; }
      }
      pushed++;
      a += l * 8;
      wz -= l;
    }
  }
  if (p) { p->next = pool.full; pool.full = p; pool.nfull++; }
  return pushed;
}

void vergc_par2_mark(uint64_t *roots, size_t n)
{
  double t0 = stats ? now_us() : 0;
  for (int i = 0; i < K; i++) {
    worker_t *w = &wk[i];
    w->entries = w->fields = w->claimed = w->cas_fail = w->cas_lost = w->cas_neigh = 0;
    w->steal_try = w->steal_ok = w->steal_abort = w->probe_empty = 0;
    w->pkt_pub = w->pkt_take = w->pkt_share = w->pkt_get = w->lock_n = w->lock_cont = 0;
    w->cnt_n = w->idle_spins = 0;
    w->c_tot = w->c_idle = w->c_steal = w->c_pool = w->c_lockwait = 0;
  }
  size_t pushed = setup_roots(roots, n);
  long cnt = 0;
  for (int i = 0; i < K; i++) { wk[i].counted = steal_lb && dq_nonempty(&wk[i].dq); cnt += wk[i].counted; }
  if (!steal_lb) cnt = atomic_load(&pool.nfull);
  atomic_store(&work_in_flight, cnt);
  if (stats) st2.setup_us += now_us() - t0;
  if (pushed > 0) {
    pthread_t th[MAXK];
    double t1 = stats ? now_us() : 0;
    for (int i = 0; i < K; i++)
      if (pthread_create(&th[i], NULL, worker_main, &wk[i]) != 0) {
        fprintf(stderr, "par_mark2: pthread_create failed\n");
        abort();
      }
    double t2 = stats ? now_us() : 0;
    for (int i = 0; i < K; i++) pthread_join(th[i], NULL);
    if (stats) {
      double t3 = now_us(), maxs = 0, maxe = 0;
      for (int i = 0; i < K; i++) {
        if (wk[i].t_start > maxs) maxs = wk[i].t_start;
        if (wk[i].t_end > maxe) maxe = wk[i].t_end;
      }
      st2.create_us += t2 - t1;
      st2.start_lat_us += maxs - t1;
      st2.join_lat_us += t3 - maxe;
      st2.round_us += t3 - t1;
    }
    st2.rounds++;
  }
  /* Sanity: nothing left anywhere. */
  if (atomic_load(&work_in_flight) != 0 || pool.full != NULL) {
    fprintf(stderr, "par_mark2: round ended with work_in_flight %ld\n", (long)atomic_load(&work_in_flight));
    abort();
  }
  for (int i = 0; i < K; i++) {
    worker_t *w = &wk[i];
    if (steal_lb) {
      if (dq_nonempty(&w->dq)) { fprintf(stderr, "par_mark2: deque %d not empty\n", i); abort(); }
      ring_t *a = atomic_load(&w->dq.arr), *old = a->prev;
      a->prev = NULL;
      while (old) { ring_t *q = old->prev; free(old); old = q; }
    } else if (w->in->n || w->out->n) {
      fprintf(stderr, "par_mark2: packets of worker %d not empty\n", i);
      abort();
    }
  }
  uint64_t mx = 0;
  for (int i = 0; i < K; i++) {
    worker_t *w = &wk[i];
    st2.entries += w->entries; st2.fields += w->fields; st2.claimed += w->claimed;
    st2.cas_fail += w->cas_fail; st2.cas_lost += w->cas_lost; st2.cas_neigh += w->cas_neigh;
    st2.steal_try += w->steal_try; st2.steal_ok += w->steal_ok; st2.steal_abort += w->steal_abort;
    st2.probe_empty += w->probe_empty;
    st2.pkt_pub += w->pkt_pub; st2.pkt_take += w->pkt_take; st2.pkt_share += w->pkt_share;
    st2.pkt_get += w->pkt_get; st2.lock_n += w->lock_n; st2.lock_cont += w->lock_cont;
    st2.cnt_n += w->cnt_n; st2.idle_spins += w->idle_spins;
    st2.c_tot += w->c_tot; st2.c_idle += w->c_idle; st2.c_steal += w->c_steal;
    st2.c_pool += w->c_pool; st2.c_lockwait += w->c_lockwait;
    if (w->c_tot > mx) mx = w->c_tot;
    st2.per_worker_claimed[i] += w->claimed;
  }
  st2.c_max_tot += mx;
}

/* ------------------------------------------------------------------ */
/* B: the sweep, as fused_sweep_coalesce (GC_Gen_Impl.c) with the mark   */
/* read from the bitmap, and each bit cleared as it is read.            */

static inline uint64_t blue_header(uint64_t wz) { return (wz << 10) | (BLUE << 8); }

static inline uint64_t flush_blue(uint64_t fb, uint64_t rw, uint64_t fp)
{
  if (rw == 0) return fp;
  WORD(fb - 8) = blue_header(rw - 1);
  if (rw - 1 > 0) { WORD(fb) = fp; return fb; }
  return fp;
}

uint64_t vergc_par2_sweep(void)
{
  uint64_t cur = zero_addr, fb = 0, rw = 0, fp = 0;
  while (cur + 8 < heap_size_u64) {
    uint64_t hdr = WORD(cur), wz = wosize_of(hdr), next = cur + (wz + 1) * 8;
    uint64_t i = (cur - zero_addr) >> 3;
    _Atomic uint32_t *bw = &bitmap[i >> 5];
    uint32_t m = 1u << (i & 31), word = atomic_load_explicit(bw, memory_order_relaxed);
    if (word & m) {
      atomic_store_explicit(bw, word & ~m, memory_order_relaxed);
      fp = flush_blue(fb, rw, fp);
      /* the header is still white: nothing to write */
      fb = 0;
      rw = 0;
    } else {
      if (rw == 0) fb = cur + 8;
      rw += wz + 1;
    }
    cur = next;
  }
  return flush_blue(fb, rw, fp);
}

/* ------------------------------------------------------------------ */
/* Check support                                                       */

int vergc_par2_bitmap(void) { return claimB; }
int vergc_par2_marked(uint64_t hd) { return is_marked_B(hd); }
void vergc_par2_flip(uint64_t hd)
{
  uint64_t i = (hd - zero_addr) >> 3;
  atomic_fetch_xor(&bitmap[i >> 5], 1u << (i & 31));
}
/* Number of set bits (after a mark: the marked objects; after a sweep: 0). */
uint64_t vergc_par2_bits_set(void)
{
  uint64_t n = 0, words = ((heap_size_u64 - zero_addr) / 8 + 31) / 32;
  for (uint64_t i = 0; i < words; i++) n += (uint64_t)__builtin_popcount(atomic_load(&bitmap[i]));
  return n;
}

/* ------------------------------------------------------------------ */
/* Setup and statistics                                                */

static const char *vname;

/* Returns 1 if VGC_PAR_VARIANT selects this file. */
int vergc_par2_setup(int k, int stats_, int prof_, int race_)
{
  const char *v = getenv("VGC_PAR_VARIANT");
  if (!v || !*v || k <= 0) return 0;
  if (strlen(v) != 2 || (v[0] != 'A' && v[0] != 'B') || (v[1] != 'P' && v[1] != 'S')) {
    fprintf(stderr, "par_mark2: VGC_PAR_VARIANT must be AP, AS, BP or BS\n");
    abort();
  }
  if (heap_size_u64 > ADDR_MASK) { fprintf(stderr, "par_mark2: heap above 2^48\n"); abort(); }
  vname = v;
  K = k > MAXK ? MAXK : k;
  claimB = v[0] == 'B';
  steal_lb = v[1] == 'S';
  stats = stats_; prof = prof_; race_control = race_;
  const char *c = getenv("VGC_PAR_CHUNK");
  if (c && atoll(c) > 0) CHUNK = (uint64_t)atoll(c);
  if (CHUNK > MAXLEN) CHUNK = MAXLEN;
  const char *p = getenv("VGC_PAR_PKT");
  if (p && atoll(p) > 0) PKT = (size_t)atoll(p);
  if (claimB) {
    uint64_t words = ((heap_size_u64 - zero_addr) / 8 + 31) / 32;
    bitmap = calloc(words, sizeof(uint32_t));
    if (!bitmap) { fprintf(stderr, "par_mark2: cannot allocate the bitmap\n"); abort(); }
  }
  pthread_mutex_init(&pool.mu, NULL);
  for (int i = 0; i < K; i++) {
    worker_t *w = &wk[i];
    w->id = i;
    w->rng = 0x9E3779B97F4A7C15ULL * (uint64_t)(i + 1);
    atomic_init(&w->dq.top, 0);
    atomic_init(&w->dq.bottom, 0);
    atomic_init(&w->dq.arr, ring_new(1 << 13, NULL));
    w->in = pkt_alloc();
    w->out = pkt_alloc();
    w->spare = NULL;
  }
  return 1;
}

void vergc_par2_print_stats(void)
{
  fprintf(stderr, "vgc-mark2: variant %s chunk %llu pkt %zu\n", vname, (unsigned long long)CHUNK, PKT);
  fprintf(stderr,
          "vgc-mark2: rounds %ld setup_us %.0f round_us %.0f create_us %.0f start_lat_us %.0f "
          "join_lat_us %.0f\n",
          st2.rounds, st2.setup_us, st2.round_us, st2.create_us, st2.start_lat_us, st2.join_lat_us);
  fprintf(stderr,
          "vgc-mark2: roots_claimed %llu entries %llu fields %llu claimed %llu cas_fail %llu cas_lost %llu "
          "cas_neigh %llu\n",
          (unsigned long long)st2.roots_claimed, (unsigned long long)st2.entries,
          (unsigned long long)st2.fields, (unsigned long long)st2.claimed,
          (unsigned long long)st2.cas_fail, (unsigned long long)st2.cas_lost,
          (unsigned long long)st2.cas_neigh);
  fprintf(stderr,
          "vgc-mark2: steal_try %llu steal_ok %llu steal_abort %llu probe_empty %llu pkt_pub %llu "
          "pkt_take %llu pkt_share %llu pkt_get %llu lock_n %llu lock_contended %llu cnt_n %llu "
          "idle_spins %llu\n",
          (unsigned long long)st2.steal_try, (unsigned long long)st2.steal_ok,
          (unsigned long long)st2.steal_abort, (unsigned long long)st2.probe_empty,
          (unsigned long long)st2.pkt_pub, (unsigned long long)st2.pkt_take,
          (unsigned long long)st2.pkt_share, (unsigned long long)st2.pkt_get,
          (unsigned long long)st2.lock_n, (unsigned long long)st2.lock_cont,
          (unsigned long long)st2.cnt_n, (unsigned long long)st2.idle_spins);
  if (prof) {
    uint64_t hz = 0;
    size_t len = sizeof hz;
    sysctlbyname("machdep.tsc.frequency", &hz, &len, NULL, 0);
    double us = hz ? 1e6 / (double)hz : 0;
    fprintf(stderr,
            "vgc-mark2-prof: tsc_hz %llu worker_us %.0f max_worker_us %.0f idle_us %.0f steal_us %.0f "
            "pool_us %.0f lock_wait_us %.0f\n",
            (unsigned long long)hz, st2.c_tot * us, st2.c_max_tot * us, st2.c_idle * us,
            st2.c_steal * us, st2.c_pool * us, st2.c_lockwait * us);
  }
  fprintf(stderr, "vgc-mark2: per_worker_claimed");
  for (int i = 0; i < K; i++) fprintf(stderr, " %llu", (unsigned long long)st2.per_worker_claimed[i]);
  fprintf(stderr, "\n");
}
