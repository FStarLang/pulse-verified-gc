/* Times par_sweep (par_sweep.c: threads started at each sweep and joined
 * before merge) against fused_sweep_coalesce, and checks every
 * result is byte-identical to it (docs/parallel-sweep-phase1.md, §9).
 * Reuses sweep_par_ctest.c's heap generator.
 *
 *   make -C parallel-sweep bench
 */
#define main ctest_main
#include "sweep_par_ctest.c"
#undef main
#include <time.h>

int par_sweep_init(int nthreads);
uint64_t par_sweep(GC_Impl_Heap_heap_t h, size_t k);

static double now_us(void)
{
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e6 + ts.tv_nsec / 1e3;
}

static int cmp(const void *a, const void *b)
{
  double x = *(const double *)a, y = *(const double *)b;
  return x < y ? -1 : x > y;
}

#define REPS 41

int main(int argc, char **argv)
{
  int nthreads = argc > 1 ? atoi(argv[1]) : 4;
  const char *name = argc > 2 ? argv[2] : "?";
  static const uint64_t sizes[] = { 64, 4096, 65536, 1u << 20, 4u << 20 };
  uint64_t za = 2048;
  int started = 0;
  for (size_t si = 0; si < sizeof sizes / sizeof *sizes; si++) {
    uint64_t words = sizes[si], hs = za + 8 * words;
    zero_addr = za; heap_size_u64 = hs;
    krmlinit_globals();
    if (!started) { par_sweep_init(nthreads); started = 1; }   /* after the globals */
    rng_s = 42 + si;
    uint8_t *g = calloc(1, hs), *a = malloc(hs), *b = malloc(hs);
    gen_heap(g, za, hs, MIXED);
    GC_Impl_Heap_heap_t ha = { .data = a, .size = hs }, hb = { .data = b, .size = hs };
    double ts[REPS], tp[REPS];
    for (int r = 0; r < REPS; r++) {
      memcpy(a, g, hs); memcpy(b, g, hs);
      double t0 = now_us();
      uint64_t fa = fused_sweep_coalesce(ha);
      double t1 = now_us();
      uint64_t fb = par_sweep(hb, 4 * (size_t)nthreads);
      double t2 = now_us();
      if (fa != fb || memcmp(a, b, hs) != 0) { printf("DIFFERS at %llu words\n", (unsigned long long)words); return 1; }
      ts[r] = t1 - t0; tp[r] = t2 - t1;
    }
    qsort(ts, REPS, sizeof *ts, cmp); qsort(tp, REPS, sizeof *tp, cmp);
    printf("%s %d threads, %8llu words: sequential %9.1f us, parallel %9.1f us (median of %d, equal)\n",
           name, nthreads, (unsigned long long)words, ts[REPS / 2], tp[REPS / 2], REPS);
    free(g); free(a); free(b);
  }
  return 0;
}
