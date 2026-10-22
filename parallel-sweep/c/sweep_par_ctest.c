/* The extracted parallel sweep, run one piece at a time, against the
 * extracted sequential fused_sweep_coalesce (docs/parallel-sweep-phase1.md, §9).
 *
 * For each generated heap and each k in {1, 2, 4, 8}, on two copies of the
 * same heap:
 *   A: fused_sweep_coalesce
 *   B: prepass; sweep_segment on each piece, in order; merge
 *   B': the same pieces swept in reverse order, as threads may finish
 *   C: sweep_par_seq (the extracted single-thread driver)
 * Every byte of the heap and the free-list head must be equal.
 *
 * A control leaves the last piece unswept (its record zeroed) and counts the
 * runs where that is caught; main fails if it is never caught.
 *
 * Heaps follow test/sweep_par_test.ml's generator, so they meet the
 * executable part of fused_pre: objects tile [zero_addr, heap_size), no gray,
 * no infix tag, scannable fields are odd, 0, or an enumerated object.
 *
 *   make -C parallel-sweep ctest
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "compat.h"
#include "GC_SweepPar.h"
#include "krmlinit.h"

#define WHITE 0ULL
#define BLUE  2ULL
#define BLACK 3ULL

/* --- A small deterministic generator (splitmix64) --- */
static uint64_t rng_s;
static uint64_t rnd(void) {
  uint64_t z = (rng_s += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}
static uint64_t below(uint64_t n) { return rnd() % n; }
static double unit(void) { return (double)(rnd() >> 11) / (double)(1ULL << 53); }

static void poke(uint8_t *d, uint64_t a, uint64_t v) { memcpy(d + a, &v, 8); }
static uint64_t peek(const uint8_t *d, uint64_t a) { uint64_t v; memcpy(&v, d + a, 8); return v; }

/* --- Heap shapes --- */
enum shape { MIXED, FRONT_PACKED, ALL_FREE, ALL_LIVE, NSHAPES };
static const char *shape_name[] = { "mixed", "front-packed", "all-free", "all-live" };

static uint64_t gen_wz(uint64_t rem) {
  uint64_t r = below(100), wz;
  if (r < 25) wz = 0; else if (r < 50) wz = 1; else if (r < 65) wz = 2;
  else if (r < 85) wz = 3 + below(3); else wz = 6 + below(8);
  return wz < rem - 1 ? wz : rem - 1;
}

/* Fill [zero_addr, heap_size) with objects; bytes below zero_addr random. */
static void gen_heap(uint8_t *d, uint64_t za, uint64_t hs, enum shape sh) {
  for (uint64_t i = 0; i < za; i++) d[i] = (uint8_t)rnd();
  double p_black = (double[]){0, .1, .3, .5, .7, .9, 1}[below(7)];
  double p_blue = unit() * 0.5;
  uint64_t words = (hs - za) / 8, rem = words;
  uint64_t live_words = sh == FRONT_PACKED ? words / (8 + below(64)) : 0;
  uint64_t a = za, nobj = 0;
  uint64_t *hds = malloc(sizeof *hds * (words + 1));
  while (rem > 0) {
    uint64_t wz, col;
    if (sh == FRONT_PACKED && a - za >= live_words * 8) { wz = rem - 1; col = below(2) ? WHITE : BLUE; }
    else {
      wz = gen_wz(rem);
      if (sh == ALL_FREE) col = below(2) ? WHITE : BLUE;
      else if (sh == ALL_LIVE || sh == FRONT_PACKED) col = BLACK;
      else col = unit() < p_black ? BLACK : unit() < p_blue ? BLUE : WHITE;
    }
    uint64_t tag = (uint64_t[]){0, 0, 0, 1, 2, 252}[below(6)];
    poke(d, a, (wz << 10) | (col << 8) | tag);
    hds[nobj++] = a;
    a += 8 * (wz + 1); rem -= wz + 1;
  }
  /* A wosize-0 header on the last word is a walk position but not an object. */
  uint64_t n_enum = nobj - (hds[nobj - 1] == hs - 8 ? 1 : 0);
  for (uint64_t i = 0; i < nobj; i++) {
    uint64_t h = peek(d, hds[i]), wz = h >> 10, tag = h & 0xff;
    for (uint64_t f = 0; f < wz; f++) {
      uint64_t v;
      if (tag >= 251) v = rnd();
      else switch (below(3)) {
        case 0: v = 2 * below(1000) + 1; break;
        case 1: v = n_enum > 0 ? hds[below(n_enum)] + 8 : 0; break;
        default: v = 0;
      }
      poke(d, hds[i] + 8 * (f + 1), v);
    }
  }
  free(hds);
}

/* --- One heap, every k --- */
static long n_heaps, n_runs, n_pieces, max_pieces, n_fewer, n_ctl, n_ctl_caught;

static int check(const char *what, const uint8_t *exp, const uint8_t *got, uint64_t hs,
                 uint64_t fpe, uint64_t fpg, uint64_t seed, size_t k) {
  if (fpe == fpg && memcmp(exp, got, hs) == 0) return 1;
  printf("FAIL %s: seed %llu, heap_size %llu, k %zu: head %llu vs %llu\n", what,
         (unsigned long long)seed, (unsigned long long)hs, k,
         (unsigned long long)fpe, (unsigned long long)fpg);
  for (uint64_t i = 0; i < hs; i++)
    if (exp[i] != got[i]) {
      uint64_t w = i & ~7ULL;
      printf("  first differing word at %llu: %016llx vs %016llx\n", (unsigned long long)w,
             (unsigned long long)peek(exp, w), (unsigned long long)peek(got, w));
      break;
    }
  return 0;
}

static int run_heap(uint64_t seed, uint64_t za, uint64_t words, enum shape sh) {
  uint64_t hs = za + 8 * words;
  zero_addr = za; heap_size_u64 = hs;
  krmlinit_globals();
  rng_s = seed;
  uint8_t *g = calloc(1, hs), *a = malloc(hs), *b = malloc(hs);
  if (!g || !a || !b) { fprintf(stderr, "out of memory\n"); exit(2); }
  gen_heap(g, za, hs, sh);

  memcpy(a, g, hs);
  uint64_t fpa = fused_sweep_coalesce((heap_t){ .data = a, .size = hs });

  static const size_t ks[] = { 1, 2, 4, 8 };
  for (size_t ki = 0; ki < 4; ki++) {
    size_t k = ks[ki];
    uint64_t bounds[9];
    seg_result results[8];
    heap_t hb = { .data = b, .size = hs };

    memcpy(b, g, hs);
    size_t n = prepass0(hb, k, bounds);
    if (n < 2 || n > k + 1 || bounds[0] != za || bounds[n - 1] != hs) {
      printf("FAIL prepass: seed %llu, k %zu, n %zu\n", (unsigned long long)seed, k, n);
      return 0;
    }
    for (size_t i = 0; i + 1 < n; i++) results[i] = sweep_segment(hb, bounds[i], bounds[i + 1]);
    uint64_t fpb = merge0(hb, results, n - 1);
    if (!check("pieces", a, b, hs, fpa, fpb, seed, k)) return 0;

    memcpy(b, g, hs);
    n = prepass0(hb, k, bounds);
    for (size_t i = n - 1; i-- > 0;) results[i] = sweep_segment(hb, bounds[i], bounds[i + 1]);
    fpb = merge0(hb, results, n - 1);
    if (!check("pieces, reverse order", a, b, hs, fpa, fpb, seed, k)) return 0;

    /* Control: the last piece is never swept. */
    memcpy(b, g, hs);
    n = prepass0(hb, k, bounds);
    for (size_t i = 0; i + 2 < n; i++) results[i] = sweep_segment(hb, bounds[i], bounds[i + 1]);
    results[n - 2] = (seg_result){ 0 };
    fpb = merge0(hb, results, n - 1);
    n_ctl++;
    if (fpb != fpa || memcmp(a, b, hs) != 0) n_ctl_caught++;

    memcpy(b, g, hs);
    uint64_t fpc = sweep_par_seq(hb, k, bounds, results);
    if (!check("sweep_par_seq", a, b, hs, fpa, fpc, seed, k)) return 0;

    n_runs++; n_pieces += n - 1;
    if ((long)(n - 1) > max_pieces) max_pieces = n - 1;
    if (n - 1 < k) n_fewer++;
  }
  n_heaps++;
  free(g); free(a); free(b);
  return 1;
}

int main(void) {
  static const uint64_t zas[] = { 2048, 4096 + 8 };
  long per_shape[NSHAPES] = { 0 };
  /* Small heaps, as in the OCaml test: 2 to 96 words, many seeds. */
  for (uint64_t s = 0; s < 4000; s++) {
    enum shape sh = (enum shape)(s % NSHAPES);
    if (!run_heap(s, zas[s % 2], 2 + s % 95, sh)) return 1;
    per_shape[sh]++;
  }
  /* Medium heaps: 100 to 20,000 words. */
  for (uint64_t s = 0; s < 400; s++) {
    enum shape sh = (enum shape)(s % NSHAPES);
    rng_s = 1000003 + s;
    if (!run_heap(1000003 + s, zas[s % 2], 100 + below(20000), sh)) return 1;
    per_shape[sh]++;
  }
  /* Large heaps: 1M words (8 MB). */
  for (uint64_t s = 0; s < 8; s++) {
    enum shape sh = (enum shape)(s % NSHAPES);
    if (!run_heap(7000001 + s, zas[s % 2], 1u << 20, sh)) return 1;
    per_shape[sh]++;
  }
  printf("heaps: %ld (", n_heaps);
  for (int i = 0; i < NSHAPES; i++) printf("%s%s %ld", i ? ", " : "", shape_name[i], per_shape[i]);
  printf(")\n(heap, k) runs: %ld, pieces: %ld, at most %ld per run, %ld runs with fewer than k\n",
         n_runs, n_pieces, max_pieces, n_fewer);
  printf("control (last piece unswept): caught in %ld of %ld runs\n", n_ctl_caught, n_ctl);
  if (n_ctl_caught == 0) { printf("FAIL: the control was never caught\n"); return 1; }
  printf("ok: pieces (in order and reversed) and sweep_par_seq equal fused_sweep_coalesce, heap and head, k = 1, 2, 4, 8\n");
  return 0;
}
