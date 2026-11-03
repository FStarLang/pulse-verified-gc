/* par_mark.c — UNVERIFIED prototype of the parallel mark of
 * docs/parallel-mark-design.md (branch sheera/parallel-mark), for
 * measurement only.  Never to be merged.
 *
 * Environment:
 *   VGC_PAR_MARK=k          mark on k worker threads (started per round);
 *                           unset or 0: the verified sequential path
 *                           (gen_gc), unchanged, unless VGC_MARK_STATS is
 *                           set, in which case gen_gc's steps are called one
 *                           by one so the mark can be timed.
 *   VGC_PAR_S=n             capacity of each worker's mark stack
 *                           (default: the sequential gray-stack capacity,
 *                           heap bytes / 64)
 *   VGC_PAR_Q=n             capacity of each worker's inbox (default 4096)
 *   VGC_PAR_LOCAL=1         variant: a worker's own stack is counted in
 *                           work_in_flight as one token while non-empty,
 *                           not one unit per entry (messages still count 1)
 *   VGC_PAR_SPIN=1          variant: inbox locks are spin locks
 *                           (test-and-test-and-set on an atomic_flag-like
 *                           int) instead of pthread mutexes
 *   VGC_PAR_DEDUP=n         variant: each worker remembers the last n
 *                           (rounded up to a power of 2) pointers it sent
 *                           successfully this round, in a direct-mapped
 *                           cache, and does not send them again
 *   VGC_PAR_BATCH=b         variant: buffer up to b pointers per destination
 *                           and move them into its inbox under one lock
 *                           acquisition and one counter add; flushed when
 *                           full and whenever the worker's stack is empty
 *   VGC_PAR_CUT=live        variant: cut each collection's ranges at equal
 *                           shares of the previous collection's black words
 *                           (first collection: equal slices)
 *   VGC_PAR_VARIANT=v       with VGC_PAR_MARK=k: mark with par_mark2.c's
 *                           variant v (AP, AS, BP or BS) instead
 *   VGC_PAR_MARK_CHECK=1    at every major GC, also run the verified
 *                           sequential mark on the same pre-mark heap and
 *                           abort unless every header is equal
 *   VGC_PAR_MARK_CHECK_CONTROL=1  flip one colour bit of the parallel
 *                           result before comparing: the check must fail
 *   VGC_PAR_RACE_CONTROL=1  deliberately read the counter non-atomically
 *                           (a data race TSan must report)
 *   VGC_MARK_STATS=1        print mark-time statistics to stderr at exit
 *   VGC_PAR_PROF=1          with VGC_MARK_STATS: also time, with rdtsc, each
 *                           worker's lock waits and holds, counter atomics
 *                           and idle polling (adds overhead; for the
 *                           breakdown only, not for timings)
 *
 * Colour encoding and heap walk as GC_Gen_Impl.c: header = wosize << 10 |
 * colour << 8 | tag, colour 0 white, 1 gray, 2 blue, 3 black; objects are
 * contiguous from zero_addr while hd + 8 < heap_size_u64, next header at
 * hd + (wosize + 1) * 8; the heap is addressed absolutely (NULL base).
 */

#include <pthread.h>
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

/* Non-static functions of GC_Gen_Impl.c used to run the sequential mark in
 * pieces, and the sweep wrapper of gc_gen_impl_proto.c. */
void darken_roots_bounded(heap_t heap, gray_stack_rec st, uint64_t *roots, size_t nroots);
bool mark_inner_loop_impl(heap_t heap, gray_stack_rec st, bool ov_in);
void rescan_heap_impl(heap_t heap, gray_stack_rec st);
void mark_loop_bounded_flagged(heap_t heap, gray_stack_rec st, bool ov);
uint64_t vergc_fused_sweep_coalesce(heap_t heap);

/* par_mark2.c: the variants after established designs (VGC_PAR_VARIANT). */
int vergc_par2_setup(int k, int stats, int prof, int race);
void vergc_par2_mark(uint64_t *roots, size_t n);
uint64_t vergc_par2_sweep(void);
int vergc_par2_bitmap(void);
int vergc_par2_marked(uint64_t hd);
void vergc_par2_flip(uint64_t hd);
uint64_t vergc_par2_bits_set(void);
void vergc_par2_print_stats(void);

#define WHITE 0ULL
#define GRAY  1ULL
#define BLUE  2ULL
#define BLACK 3ULL
#define INFIX_TAG 249ULL
#define NO_SCAN_TAG 251ULL

#define HDR(a) (*(uint64_t *)(uintptr_t)(a))
static inline uint64_t colour_of(uint64_t h) { return (h >> 8) & 3ULL; }
static inline uint64_t wosize_of(uint64_t h) { return h >> 10; }
static inline uint64_t tag_of(uint64_t h) { return h & 0xffULL; }
static inline uint64_t with_colour(uint64_t h, uint64_t c) { return (h & ~(3ULL << 8)) | (c << 8); }
static inline int is_heap_pointer(uint64_t v)
{
  return v >= zero_addr + 8 && v < heap_size_u64 && (v & 7) == 0;
}

static inline void cpu_relax(void)
{
#if defined(__x86_64__) || defined(__i386__)
  __builtin_ia32_pause();
#elif defined(__aarch64__)
  __asm__ volatile("yield");
#endif
}

static double now_us(void)
{
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e6 + ts.tv_nsec / 1e3;
}

/* ------------------------------------------------------------------ */
/* Configuration and shared state                                      */

#define MAXK 64
#define CL 128

static int K;                 /* workers; 0 = sequential */
static size_t S, Q;
static size_t dedup;          /* VGC_PAR_DEDUP: per-worker sent-cache entries, power of 2; 0 = off */
static size_t batch;          /* VGC_PAR_BATCH: per-destination send buffer; 0 = off */
static int cut_live;          /* VGC_PAR_CUT=live */
static int local_count, spin_locks, check_mode, check_control, race_control, stats;
static int prof;              /* VGC_PAR_PROF */
static inline uint64_t tsc(void) { return __rdtsc(); }
static uint64_t slice;        /* bytes per range; owner(a) = (a - zero_addr) / slice */

typedef struct {
  _Alignas(CL) pthread_mutex_t mu;
  atomic_int spin;
  uint64_t *buf;
  size_t head, count;
} inbox_t;

typedef struct {
  _Alignas(CL) int id;
  uint64_t *stack;
  size_t top;
  int overflow;               /* written only by this worker during a round */
  int token;                  /* VGC_PAR_LOCAL: holds one count for its stack */
  uint64_t *sent_cache;       /* VGC_PAR_DEDUP: pointers sent successfully this round */
  uint64_t *outbuf[MAXK];     /* VGC_PAR_BATCH: pointers for worker j, not yet counted */
  size_t outn[MAXK];
  uint64_t flushes;
  /* statistics, private */
  uint64_t scanned, accepted, sent, dropped, stack_ovf, idle_spins, taken, deduped;
  double t_start, t_end;
  /* VGC_PAR_PROF, private; cycles.  Disjoint: a failed poll (empty take,
   * counter read, pause) counts only as idle. */
  uint64_t lk_n, lk_cont, lk_wait, lk_hold, cnt_n, cnt_cyc, idle_cyc, idle_n, tot_cyc;
  uint64_t lk_t0, lk_cnt0;
} worker_t;

static inbox_t inbox[MAXK];
static worker_t wk[MAXK];
static int overflow_main;
static _Alignas(CL) atomic_long work_in_flight;
static _Alignas(CL) char pad_after_counter[CL];

/* Statistics over the run */
static struct {
  long majors, rounds, fixups, roots_pushed, fixup_pushed;
  double mark_us, setup_us, round_us, fixup_us, create_us, start_lat_us, join_lat_us;
  double seq_inner_us, seq_rescan_us; long seq_rescans;
  double cut_us; uint64_t flushes;
  uint64_t scanned, accepted, sent, dropped, stack_ovf, idle_spins, taken, deduped;
  uint64_t per_worker_scanned[MAXK];
  uint64_t lk_n, lk_cont, lk_wait, lk_hold, cnt_n, cnt_cyc, idle_cyc, idle_n, tot_cyc, max_tot_cyc;
  long checked;
  double check_seq_us;
  /* whole collections: vergc_gen_gc_split's steps, and do_full_gc */
  double minor_us, sweep_us, split_us, full_gc_us;
  long full_gcs;
} st;

static int par2;              /* VGC_PAR_VARIANT set: par_mark2.c marks */

static uint64_t slice_inv;    /* UINT64_MAX / slice: owner() without a divide */
static uint64_t cuts[MAXK + 1];   /* VGC_PAR_CUT=live: range i is [cuts[i], cuts[i+1]) */

static inline unsigned owner(uint64_t hd)
{
  if (cut_live) {
    unsigned o = 0;
    while (o + 1 < (unsigned)K && hd >= cuts[o + 1]) o++;
    return o;
  }
  uint64_t off = hd - zero_addr;
  uint64_t o = (uint64_t)(((unsigned __int128)off * slice_inv) >> 64);   /* o or o - 1 */
  if (off >= (o + 1) * slice) o++;
  return o >= (uint64_t)K ? (unsigned)K - 1 : (unsigned)o;
}

/* ------------------------------------------------------------------ */
/* Inboxes                                                             */

static inline void ib_lock_raw(inbox_t *b)
{
  if (spin_locks) {
    for (;;) {
      if (!atomic_exchange_explicit(&b->spin, 1, memory_order_acquire)) return;
      while (atomic_load_explicit(&b->spin, memory_order_relaxed)) cpu_relax();
    }
  } else
    pthread_mutex_lock(&b->mu);
}

static inline void ib_unlock_raw(inbox_t *b)
{
  if (spin_locks) atomic_store_explicit(&b->spin, 0, memory_order_release);
  else pthread_mutex_unlock(&b->mu);
}

/* With VGC_PAR_PROF: count acquisitions and contended ones (a failed
 * trylock), and time the wait, and the hold less the counter atomics done
 * while holding. */
static inline void ib_lock(worker_t *w, inbox_t *b)
{
  if (!prof) { ib_lock_raw(b); return; }
  uint64_t t = tsc();
  w->lk_n++;
  if (spin_locks || pthread_mutex_trylock(&b->mu) != 0) {
    w->lk_cont++;
    ib_lock_raw(b);
  }
  w->lk_t0 = tsc();
  w->lk_wait += w->lk_t0 - t;
  w->lk_cnt0 = w->cnt_cyc;
}

static inline void ib_unlock(worker_t *w, inbox_t *b)
{
  if (prof) w->lk_hold += (tsc() - w->lk_t0) - (w->cnt_cyc - w->lk_cnt0);
  ib_unlock_raw(b);
}

/* A counter atomic, timed with VGC_PAR_PROF. */
#define CNT(w, op) do { if (prof) { uint64_t t_ = tsc(); op; (w)->cnt_cyc += tsc() - t_; (w)->cnt_n++; } \
                        else { op; } } while (0)

/* send(j, v): full test, counter increment and append under inbox[j]'s lock. */
static inline int send_msg(worker_t *w, unsigned j, uint64_t v)
{
  inbox_t *b = &inbox[j];
  int ok = 0;
  ib_lock(w, b);
  if (b->count == Q) {
    w->overflow = 1;
    w->dropped++;
  } else {
    ok = 1;
    CNT(w, atomic_fetch_add(&work_in_flight, 1));
    size_t tail = b->head + b->count;
    if (tail >= Q) tail -= Q;
    b->buf[tail] = v;
    b->count++;
    w->sent++;
  }
  ib_unlock(w, b);
  return ok;
}

/* VGC_PAR_BATCH: move worker w's buffered pointers for j into inbox[j] under
 * one lock acquisition, adding their number to the counter before they
 * appear; those that do not fit are dropped and set the overflow flag.  The
 * buffered pointers are not counted while buffered, so the worker flushes
 * before every decrement that could leave it holding no counted work. */
static void flush_one(worker_t *w, unsigned j)
{
  size_t n = w->outn[j];
  if (n == 0) return;
  inbox_t *b = &inbox[j];
  ib_lock(w, b);
  size_t room = Q - b->count, m = n < room ? n : room;
  if (m) {
    CNT(w, atomic_fetch_add(&work_in_flight, (long)m));
    for (size_t i = 0; i < m; i++) {
      size_t tail = b->head + b->count;
      if (tail >= Q) tail -= Q;
      b->buf[tail] = w->outbuf[j][i];
      b->count++;
    }
  }
  ib_unlock(w, b);
  w->sent += m;
  if (m < n) { w->overflow = 1; w->dropped += n - m; }
  w->outn[j] = 0;
  w->flushes++;
}

static inline void flush_all(worker_t *w)
{
  for (int j = 0; j < K; j++) if (w->outn[j]) flush_one(w, (unsigned)j);
}

static inline void send_or_buffer(worker_t *w, unsigned j, uint64_t v)
{
  if (batch) {
    w->outbuf[j][w->outn[j]++] = v;
    if (w->outn[j] == batch) flush_one(w, j);
  } else
    send_msg(w, j, v);
}

/* try_take: empty test and removal under the lock. */
static inline int try_take(worker_t *w, uint64_t *out)
{
  inbox_t *b = &inbox[w->id];
  int got = 0;
  ib_lock(w, b);
  if (b->count != 0) {
    *out = b->buf[b->head];
    b->head = b->head + 1 == Q ? 0 : b->head + 1;
    b->count--;
    got = 1;
  }
  ib_unlock(w, b);
  return got;
}

/* ------------------------------------------------------------------ */
/* Worker                                                              */

static inline void push_own(worker_t *w, uint64_t v)
{
  if (local_count) {
    if (!w->token) { CNT(w, atomic_fetch_add(&work_in_flight, 1)); w->token = 1; }
  } else
    CNT(w, atomic_fetch_add(&work_in_flight, 1));
  w->stack[w->top++] = v;
}

/* accept(v): v - 8 is in my range. */
static inline void accept(worker_t *w, uint64_t v)
{
  w->accepted++;
  uint64_t h = HDR(v - 8);
  uint64_t off = wosize_of(h) * 8;
  if (tag_of(h) == INFIX_TAG && v >= off + 8) {
    uint64_t c = v - off;
    unsigned oc = owner(c - 8);
    if (oc != (unsigned)w->id) { send_or_buffer(w, oc, c); return; }
    v = c;
    h = HDR(v - 8);
  }
  if (colour_of(h) == WHITE) {
    HDR(v - 8) = with_colour(h, GRAY);
    if (w->top == S) { w->overflow = 1; w->stack_ovf++; }
    else push_own(w, v);
  }
}

static inline void route(worker_t *w, uint64_t v)
{
  unsigned j = owner(v - 8);
  if (j == (unsigned)w->id) accept(w, v);
  else if (dedup) {
    /* Variant: skip a pointer this worker already sent successfully this
     * round; its owner handles that message within the round. */
    size_t slot = (size_t)((v >> 3) * 0x9E3779B97F4A7C15ULL >> 40) & (dedup - 1);
    if (w->sent_cache[slot] == v) { w->deduped++; return; }
    if (batch) { send_or_buffer(w, j, v); w->sent_cache[slot] = v; }   /* a later drop sets overflow */
    else if (send_msg(w, j, v)) w->sent_cache[slot] = v;
  } else
    send_or_buffer(w, j, v);
}

static inline void scan(worker_t *w, uint64_t x)
{
  uint64_t hd = x - 8;
  uint64_t h = HDR(hd);
  HDR(hd) = with_colour(h, BLACK);
  w->scanned++;
  if (tag_of(h) >= NO_SCAN_TAG) return;
  uint64_t wz = wosize_of(h);
  for (uint64_t i = 1; i <= wz; i++) {
    uint64_t v = HDR(hd + i * 8);
    if (is_heap_pointer(v)) route(w, v);
  }
}

static void *worker_main(void *arg)
{
  worker_t *w = arg;
  if (stats) w->t_start = now_us();
  uint64_t c0 = prof ? tsc() : 0;
  for (;;) {
    if (w->top != 0) {
      uint64_t x = w->stack[--w->top];
      scan(w, x);
      if (batch && w->top == 0) flush_all(w);
      if (local_count) {
        if (w->top == 0 && w->token) { CNT(w, atomic_fetch_sub(&work_in_flight, 1)); w->token = 0; }
      } else
        CNT(w, atomic_fetch_sub(&work_in_flight, 1));
    } else {
      uint64_t v;
      /* A failed poll counts only as idle: undo its lock and counter
       * profile below. */
      uint64_t p0 = 0, s_n = w->lk_n, s_c = w->lk_cont, s_w = w->lk_wait, s_h = w->lk_hold,
               s_cn = w->cnt_n, s_cc = w->cnt_cyc;
      if (prof) p0 = tsc();
      if (try_take(w, &v)) {
        w->taken++;
        accept(w, v);
        if (batch && w->top == 0) flush_all(w);
        CNT(w, atomic_fetch_sub(&work_in_flight, 1));
      } else {
        long c;
        if (race_control)
          c = *(volatile long *)(void *)&work_in_flight;   /* deliberate race */
        else
          c = atomic_load(&work_in_flight);
        if (prof) {
          w->lk_n = s_n; w->lk_cont = s_c; w->lk_wait = s_w; w->lk_hold = s_h;
          w->cnt_n = s_cn; w->cnt_cyc = s_cc;
        }
        if (c == 0) { if (prof) { w->idle_cyc += tsc() - p0; w->idle_n++; } break; }
        w->idle_spins++;
        cpu_relax();
        if (prof) { w->idle_cyc += tsc() - p0; w->idle_n++; }
      }
    }
  }
  if (prof) w->tot_cyc += tsc() - c0;
  if (stats) w->t_end = now_us();
  return NULL;
}

/* ------------------------------------------------------------------ */
/* Main thread: setup, rounds, fix-up                                  */

/* Main-thread push (setup and fix-up): onto the owner's stack. */
static inline int main_push(uint64_t obj)
{
  worker_t *w = &wk[owner(obj - 8)];
  if (w->top == S) { overflow_main = 1; return 0; }
  w->stack[w->top++] = obj;
  return 1;
}

/* Resolve an infix pointer to its closure, as check_and_darken_bounded. */
static inline uint64_t resolve(uint64_t v)
{
  uint64_t h = HDR(v - 8);
  uint64_t off = wosize_of(h) * 8;
  if (tag_of(h) == INFIX_TAG && v >= off + 8) return v - off;
  return v;
}

static long setup_roots(uint64_t *roots, size_t n)
{
  long pushed = 0;
  for (size_t i = 0; i < n; i++) {
    uint64_t r = roots[i];
    if (!is_heap_pointer(r)) continue;
    uint64_t c = resolve(r);
    uint64_t h = HDR(c - 8);
    if (colour_of(h) == WHITE) {
      HDR(c - 8) = with_colour(h, GRAY);
      pushed += main_push(c);
    }
  }
  return pushed;
}

static long fixup_walk(void)
{
  long pushed = 0;
  uint64_t end = heap_size_u64;
  for (uint64_t cur = zero_addr; cur + 8 < end;) {
    uint64_t h = HDR(cur);
    uint64_t wz = wosize_of(h);
    uint64_t c = colour_of(h);
    if (c == GRAY) {
      pushed += main_push(cur + 8);
    } else if (c == BLACK && tag_of(h) < NO_SCAN_TAG) {
      for (uint64_t i = 1; i <= wz; i++) {
        uint64_t v = HDR(cur + i * 8);
        if (!is_heap_pointer(v)) continue;
        uint64_t t = resolve(v);
        uint64_t th = HDR(t - 8);
        if (colour_of(th) == WHITE) {
          HDR(t - 8) = with_colour(th, GRAY);
          if (t - 8 < cur) pushed += main_push(t);   /* below the walk */
          /* else: the walk pushes it when it gets there */
        }
      }
    }
    cur += (wz + 1) * 8;
  }
  return pushed;
}

static void run_round(long pushed)
{
  pthread_t th[MAXK];
  if (local_count) {
    long n = 0;
    for (int i = 0; i < K; i++) { wk[i].token = wk[i].top != 0; n += wk[i].token; }
    atomic_store(&work_in_flight, n);
  } else
    atomic_store(&work_in_flight, pushed);
  if (dedup)
    for (int i = 0; i < K; i++) memset(wk[i].sent_cache, 0, dedup * sizeof(uint64_t));
  double t0 = stats ? now_us() : 0;
  for (int i = 0; i < K; i++)
    if (pthread_create(&th[i], NULL, worker_main, &wk[i]) != 0) {
      fprintf(stderr, "par_mark: pthread_create failed\n");
      abort();
    }
  double t1 = stats ? now_us() : 0;
  for (int i = 0; i < K; i++) pthread_join(th[i], NULL);
  if (stats) {
    double t2 = now_us(), maxs = 0, maxe = 0;
    for (int i = 0; i < K; i++) {
      if (wk[i].t_start > maxs) maxs = wk[i].t_start;
      if (wk[i].t_end > maxe) maxe = wk[i].t_end;
    }
    st.create_us += t1 - t0;
    st.start_lat_us += maxs - t0;
    st.join_lat_us += t2 - maxe;
    st.round_us += t2 - t0;
  }
  st.rounds++;
  /* Sanity: a finished round leaves every stack and inbox empty. */
  for (int i = 0; i < K; i++)
    if (wk[i].top != 0 || inbox[i].count != 0 || (local_count && wk[i].token)) {
      fprintf(stderr, "par_mark: round ended with work left (worker %d)\n", i);
      abort();
    }
}

static int any_overflow(void)
{
  int o = overflow_main;
  for (int i = 0; i < K; i++) o |= wk[i].overflow;
  return o;
}

static void par_mark(uint64_t *roots, size_t n)
{
  double t0 = stats ? now_us() : 0;
  overflow_main = 0;
  for (int i = 0; i < K; i++) { wk[i].overflow = 0; wk[i].top = 0; }
  long pushed = setup_roots(roots, n);
  st.roots_pushed += pushed;
  if (stats) st.setup_us += now_us() - t0;
  for (;;) {
    if (pushed > 0) run_round(pushed);
    if (!any_overflow()) break;
    overflow_main = 0;
    for (int i = 0; i < K; i++) wk[i].overflow = 0;
    double f0 = stats ? now_us() : 0;
    pushed = fixup_walk();
    st.fixups++;
    st.fixup_pushed += pushed;
    if (stats) st.fixup_us += now_us() - f0;
    if (pushed == 0) {
      if (overflow_main) { fprintf(stderr, "par_mark: S too small\n"); abort(); }
      break;
    }
  }
}

/* ------------------------------------------------------------------ */
/* Correctness check: compare with the verified sequential mark        */

static size_t count_objects(void)
{
  size_t n = 0;
  for (uint64_t cur = zero_addr; cur + 8 < heap_size_u64; cur += (wosize_of(HDR(cur)) + 1) * 8) n++;
  return n;
}

static void save_headers(uint64_t *out)
{
  size_t i = 0;
  for (uint64_t cur = zero_addr; cur + 8 < heap_size_u64; cur += (wosize_of(HDR(cur)) + 1) * 8)
    out[i++] = HDR(cur);
}

static void restore_headers(const uint64_t *in)
{
  size_t i = 0;
  for (uint64_t cur = zero_addr; cur + 8 < heap_size_u64; cur += (wosize_of(HDR(cur)) + 1) * 8)
    HDR(cur) = in[i++];
}

/* ------------------------------------------------------------------ */
/* Entry points                                                        */

static void print_stats(void)
{
  fprintf(stderr, "vgc-mark-stats: mode %s k %d S %zu Q %zu local %d spin %d dedup %zu batch %zu cut %s\n",
          K ? "par" : "seq", K, S, Q, local_count, spin_locks, dedup, batch, cut_live ? "live" : "equal");
  fprintf(stderr, "vgc-mark-stats: majors %ld mark_us %.0f\n", st.majors, st.mark_us);
  fprintf(stderr, "vgc-coll-stats: coll_minor_us %.0f coll_sweep_us %.0f coll_split_us %.0f "
          "full_gcs %ld full_gc_us %.0f\n", st.minor_us, st.sweep_us, st.split_us, st.full_gcs,
          st.full_gc_us);
  if (par2) {
    vergc_par2_print_stats();
  } else if (K == 0) {
    fprintf(stderr, "vgc-mark-stats: seq inner_us %.0f rescan_us %.0f rescans %ld\n",
            st.seq_inner_us, st.seq_rescan_us, st.seq_rescans);
  } else {
    fprintf(stderr,
            "vgc-mark-stats: rounds %ld fixups %ld setup_us %.0f round_us %.0f fixup_us %.0f "
            "create_us %.0f start_lat_us %.0f join_lat_us %.0f\n",
            st.rounds, st.fixups, st.setup_us, st.round_us, st.fixup_us, st.create_us,
            st.start_lat_us, st.join_lat_us);
    fprintf(stderr,
            "vgc-mark-stats: roots_pushed %ld fixup_pushed %ld scanned %llu accepted %llu "
            "sent %llu dropped %llu stack_ovf %llu taken %llu idle_spins %llu deduped %llu\n",
            st.roots_pushed, st.fixup_pushed, (unsigned long long)st.scanned,
            (unsigned long long)st.accepted, (unsigned long long)st.sent,
            (unsigned long long)st.dropped, (unsigned long long)st.stack_ovf,
            (unsigned long long)st.taken, (unsigned long long)st.idle_spins,
            (unsigned long long)st.deduped);
    fprintf(stderr, "vgc-mark-stats: flushes %llu cut_us %.0f\n", (unsigned long long)st.flushes, st.cut_us);
    if (prof) {
      uint64_t hz = 0; size_t len = sizeof hz;
      sysctlbyname("machdep.tsc.frequency", &hz, &len, NULL, 0);
      double us = hz ? 1e6 / (double)hz : 0;
      fprintf(stderr,
              "vgc-mark-prof: tsc_hz %llu worker_us %.0f max_worker_us %.0f lock_n %llu lock_contended %llu "
              "lock_wait_us %.0f lock_hold_us %.0f cnt_n %llu cnt_us %.0f idle_n %llu idle_us %.0f\n",
              (unsigned long long)hz, st.tot_cyc * us, st.max_tot_cyc * us,
              (unsigned long long)st.lk_n, (unsigned long long)st.lk_cont, st.lk_wait * us,
              st.lk_hold * us, (unsigned long long)st.cnt_n, st.cnt_cyc * us,
              (unsigned long long)st.idle_n, st.idle_cyc * us);
    }
    fprintf(stderr, "vgc-mark-stats: per_worker_scanned");
    for (int i = 0; i < K; i++) fprintf(stderr, " %llu", (unsigned long long)st.per_worker_scanned[i]);
    fprintf(stderr, "\n");
  }
  if (check_mode)
    fprintf(stderr, "vgc-par-mark-check: %ld collections, every header equal to the sequential mark's%s\n",
            st.checked, par2 && vergc_par2_bitmap() ? "; bitmap sweep equal to the verified sweep" : "");
}

static size_t env_size(const char *name, size_t dflt)
{
  const char *e = getenv(name);
  if (!e || !*e) return dflt;
  long long v = atoll(e);
  return v > 0 ? (size_t)v : dflt;
}

/* alloc_gen.c: the time of one whole do_full_gc. */
void vergc_par_note_full_gc(double us)
{
  st.full_gcs++;
  st.full_gc_us += us;
}

/* Returns 1 if gen_gc must be split (par mark or stats), else 0. */
int vergc_par_mark_setup(void)
{
  static int done = -1;
  if (done >= 0) return done;
  const char *k = getenv("VGC_PAR_MARK");
  K = k ? atoi(k) : 0;
  if (K < 0) K = 0;
  if (K > MAXK) K = MAXK;
  stats = getenv("VGC_MARK_STATS") != NULL;
  check_mode = getenv("VGC_PAR_MARK_CHECK") != NULL;
  check_control = getenv("VGC_PAR_MARK_CHECK_CONTROL") != NULL;
  race_control = getenv("VGC_PAR_RACE_CONTROL") != NULL;
  local_count = getenv("VGC_PAR_LOCAL") != NULL;
  spin_locks = getenv("VGC_PAR_SPIN") != NULL;
  prof = stats && getenv("VGC_PAR_PROF") != NULL;
  if (K == 0 && !stats) return done = 0;
  par2 = vergc_par2_setup(K, stats, prof, race_control);
  if (K > 0 && !par2) {
    size_t heap_bytes = (size_t)(heap_size_u64 - zero_addr);
    size_t gray_cap = heap_bytes / 64;
    if (gray_cap < 4096) gray_cap = 4096;
    S = env_size("VGC_PAR_S", gray_cap);
    { const char *q = getenv("VGC_PAR_Q"); Q = q && *q ? (size_t)atoll(q) : 4096; }   /* 0 allowed */
    dedup = env_size("VGC_PAR_DEDUP", 0);
    if (dedup) { size_t p = 1; while (p < dedup) p <<= 1; dedup = p; }
    batch = env_size("VGC_PAR_BATCH", 0);
    { const char *c = getenv("VGC_PAR_CUT"); cut_live = c && strcmp(c, "live") == 0; }
    uint64_t sl = (heap_bytes + (uint64_t)K - 1) / (uint64_t)K;
    slice = (sl + 7) & ~7ULL;
    slice_inv = UINT64_MAX / slice;
    for (int i = 0; i <= K; i++) cuts[i] = zero_addr + (i == K ? heap_bytes : (uint64_t)i * slice);
    for (int i = 0; i < K; i++) {
      wk[i].id = i;
      wk[i].stack = malloc(S * sizeof(uint64_t));
      inbox[i].buf = malloc((Q ? Q : 1) * sizeof(uint64_t));
      if (!wk[i].stack || !inbox[i].buf) { fprintf(stderr, "par_mark: out of memory\n"); abort(); }
      if (dedup && !(wk[i].sent_cache = calloc(dedup, sizeof(uint64_t)))) abort();
      if (batch)
        for (int j = 0; j < K; j++)
          if (!(wk[i].outbuf[j] = malloc(batch * sizeof(uint64_t)))) abort();
      pthread_mutex_init(&inbox[i].mu, NULL);
      atomic_init(&inbox[i].spin, 0);
    }
  }
  if (stats || check_mode) atexit(print_stats);
  return done = 1;
}

/* gen_gc (GC_Gen_Impl.c) with the mark replaced by the parallel one when
 * VGC_PAR_MARK is set, and timed. */
FStar_Pervasives_Native_tuple2__uint64_t_bool
vergc_gen_gc_split(gen_heap_t gh, uint64_t *roots, size_t nroots, uint64_t *fwd_arr,
                   uint64_t *queue, uint64_t *slots, size_t nslots, gray_stack_rec gst)
{
  double s0 = now_us();
  bool ok = minor_collect_full(gh, roots, nroots, fwd_arr, queue, slots, nslots);
  uint64_t fp_val = gh.fp_ref[0U];
  st.minor_us += now_us() - s0;
  if (!ok) return (FStar_Pervasives_Native_tuple2__uint64_t_bool){ ._1 = fp_val, ._2 = ok };
  st.majors++;
  int bm = par2 && vergc_par2_bitmap();   /* B: marks in the bitmap, read by the sweep */
  int swept = 0;                          /* the check already swept */
  uint64_t final_fp = 0;

  if (K == 0) {
    /* The sequential mark, exactly as gen_gc's (collect, that is
     * mark_loop_bounded_flagged with ov = false: no rescan unless the gray
     * stack overflowed), in timed pieces. */
    double t0 = now_us();
    darken_roots_bounded(gh.major, gst, roots, nroots);
    bool ov = mark_inner_loop_impl(gh.major, gst, false);
    double t1 = now_us();
    st.seq_inner_us += t1 - t0;
    while (ov) {
      double r0 = now_us();
      rescan_heap_impl(gh.major, gst);
      st.seq_rescans++;
      st.seq_rescan_us += now_us() - r0;
      if (*gst.top == gst.cap) break;
      double i0 = now_us();
      mark_inner_loop_impl(gh.major, gst, true);
      st.seq_inner_us += now_us() - i0;
    }
    st.mark_us += now_us() - t0;
  } else {
    uint64_t *pre = NULL;
    size_t nobj = 0;
    if (check_mode) {
      nobj = count_objects();
      pre = malloc(nobj * sizeof(uint64_t));
      if (!pre) { fprintf(stderr, "par_mark check: out of memory\n"); abort(); }
      save_headers(pre);
    }
    for (int i = 0; i < K; i++)
      wk[i].scanned = wk[i].accepted = wk[i].sent = wk[i].dropped = wk[i].stack_ovf =
        wk[i].idle_spins = wk[i].taken = wk[i].deduped = wk[i].flushes = 0;
    for (int i = 0; i < K; i++)
      wk[i].lk_n = wk[i].lk_cont = wk[i].lk_wait = wk[i].lk_hold = wk[i].cnt_n = wk[i].cnt_cyc =
        wk[i].idle_cyc = wk[i].idle_n = wk[i].tot_cyc = 0;
    double t0 = now_us();
    if (par2) vergc_par2_mark(roots, nroots);
    else par_mark(roots, nroots);
    st.mark_us += now_us() - t0;
    for (int i = 0; i < K && !par2; i++) {
      st.scanned += wk[i].scanned; st.accepted += wk[i].accepted; st.sent += wk[i].sent;
      st.dropped += wk[i].dropped; st.stack_ovf += wk[i].stack_ovf;
      st.idle_spins += wk[i].idle_spins; st.taken += wk[i].taken; st.deduped += wk[i].deduped;
      st.flushes += wk[i].flushes;
      st.per_worker_scanned[i] += wk[i].scanned;
    }
    if (prof && !par2) {
      uint64_t mx = 0;
      for (int i = 0; i < K; i++) {
        worker_t *w = &wk[i];
        st.lk_n += w->lk_n; st.lk_cont += w->lk_cont; st.lk_wait += w->lk_wait; st.lk_hold += w->lk_hold;
        st.cnt_n += w->cnt_n; st.cnt_cyc += w->cnt_cyc; st.idle_cyc += w->idle_cyc; st.idle_n += w->idle_n;
        st.tot_cyc += w->tot_cyc;
        if (w->tot_cyc > mx) mx = w->tot_cyc;
      }
      st.max_tot_cyc += mx;
    }
    if (check_mode) {
      uint64_t *par = malloc(nobj * sizeof(uint64_t));
      if (!par) { fprintf(stderr, "par_mark check: out of memory\n"); abort(); }
      save_headers(par);
      if (bm) {
        /* B leaves headers alone: read its marks from the bitmap. */
        size_t i = 0, marked = 0;
        if (check_control && nobj > 0) {
          uint64_t cur = zero_addr;
          for (size_t j = 0; j < nobj / 2; j++) cur += (wosize_of(HDR(cur)) + 1) * 8;
          vergc_par2_flip(cur);
        }
        for (uint64_t cur = zero_addr; cur + 8 < heap_size_u64; cur += (wosize_of(HDR(cur)) + 1) * 8, i++) {
          if (par[i] != pre[i]) {
            fprintf(stderr, "par_mark check: B wrote header of object %zu\n", i);
            abort();
          }
          if (vergc_par2_marked(cur)) { par[i] = with_colour(par[i], BLACK); marked++; }
        }
        if (vergc_par2_bits_set() != marked) {
          fprintf(stderr, "par_mark check: %llu bitmap bits set, %zu on object headers\n",
                  (unsigned long long)vergc_par2_bits_set(), marked);
          abort();
        }
      } else if (check_control && nobj > 0)
        par[nobj / 2] ^= (1ULL << 8);
      restore_headers(pre);
      double c0 = now_us();
      darken_roots_bounded(gh.major, gst, roots, nroots);
      mark_loop_bounded_flagged(gh.major, gst, false);
      st.check_seq_us += now_us() - c0;
      uint64_t *seq = pre;     /* reuse */
      save_headers(seq);
      size_t bad = 0, first = (size_t)-1, grays = 0;
      for (size_t i = 0; i < nobj; i++) {
        if (par[i] != seq[i]) { if (first == (size_t)-1) first = i; bad++; }
        if (colour_of(par[i]) == GRAY) grays++;
      }
      st.checked++;
      if (bad || grays) {
        fprintf(stderr,
                "par_mark check: collection %ld DIFFERS: %zu of %zu headers differ "
                "(first: object %zu, par %#llx seq %#llx), %zu gray left\n",
                st.checked, bad, nobj, first, first == (size_t)-1 ? 0ULL : (unsigned long long)par[first],
                first == (size_t)-1 ? 0ULL : (unsigned long long)seq[first], grays);
        abort();
      }
      /* The heap now holds the sequential result, which equals the parallel one. */
      if (bm) {
        /* Check the bitmap sweep too: from the pre-mark headers and the
         * bitmap, it must leave the heap and free pointer that the verified
         * sweep leaves from the sequential mark's headers. */
        size_t hb = (size_t)(heap_size_u64 - zero_addr);
        uint8_t *hseq = malloc(hb), *hbit = malloc(hb);
        if (!hseq || !hbit) { fprintf(stderr, "par_mark check: out of memory\n"); abort(); }
        memcpy(hseq, (void *)(uintptr_t)zero_addr, hb);
        restore_headers(par);                 /* par: pre-mark headers, B's marks as black */
        for (uint64_t cur = zero_addr; cur + 8 < heap_size_u64; cur += (wosize_of(HDR(cur)) + 1) * 8)
          if (colour_of(HDR(cur)) == BLACK) HDR(cur) = with_colour(HDR(cur), WHITE);
        uint64_t fp_b = vergc_par2_sweep();
        if (vergc_par2_bits_set() != 0) { fprintf(stderr, "par_mark check: bitmap not clear after sweep\n"); abort(); }
        memcpy(hbit, (void *)(uintptr_t)zero_addr, hb);
        memcpy((void *)(uintptr_t)zero_addr, hseq, hb);
        uint64_t fp_s = vergc_fused_sweep_coalesce(gh.major);
        if (fp_b != fp_s || memcmp(hbit, (void *)(uintptr_t)zero_addr, hb) != 0) {
          fprintf(stderr, "par_mark check: collection %ld: bitmap sweep DIFFERS from the verified sweep "
                  "(fp %#llx vs %#llx)\n", st.checked, (unsigned long long)fp_b, (unsigned long long)fp_s);
          abort();
        }
        free(hseq);
        free(hbit);
        final_fp = fp_s;
        swept = 1;
      }
      free(par);
      free(pre);
    }
  }

  if (K > 0 && cut_live && !par2) {
    /* VGC_PAR_CUT=live: cut the next collection's ranges at equal shares of
     * this collection's black words.  A separate walk here, timed apart from
     * the mark (cut_us); a real implementation would fuse it with the sweep. */
    double c0 = now_us();
    enum { NB = 4096 };
    static uint64_t hist[NB];
    memset(hist, 0, sizeof hist);
    uint64_t span = heap_size_u64 - zero_addr, bw = (span + NB - 1) / NB, total = 0;
    for (uint64_t cur = zero_addr; cur + 8 < heap_size_u64;) {
      uint64_t h = HDR(cur), wz = wosize_of(h);
      if (colour_of(h) == BLACK) { hist[(cur - zero_addr) / bw] += wz + 1; total += wz + 1; }
      cur += (wz + 1) * 8;
    }
    if (total > 0) {
      uint64_t acc = 0; int next = 1;
      for (int b = 0; b < NB && next < K; b++) {
        acc += hist[b];
        while (next < K && acc * (uint64_t)K >= total * (uint64_t)next)
          cuts[next++] = zero_addr + (uint64_t)(b + 1) * bw;
      }
      while (next < K) { cuts[next] = heap_size_u64; next++; }
    }
    st.cut_us += now_us() - c0;
  }

  if (!swept) {
    double w0 = now_us();
    final_fp = bm ? vergc_par2_sweep() : vergc_fused_sweep_coalesce(gh.major);
    st.sweep_us += now_us() - w0;
  }
  gh.fp_ref[0U] = final_fp;
  st.split_us += now_us() - s0;
  return (FStar_Pervasives_Native_tuple2__uint64_t_bool){ ._1 = final_fp, ._2 = ok };
}
