/* Minimal test harness for the verified mark-and-sweep GC.
 *
 * Provides the heap_size_u64 extern required by GC_Impl.c,
 * allocates a heap, initializes it, allocates objects, then collects.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "GC_Impl.h"

/* Configurable heap size (bytes).  GC_Impl.c references this as extern. */
uint64_t heap_size_u64 = 1024;

int main(void)
{
  size_t heap_bytes = (size_t)heap_size_u64;

  /* Allocate the heap (zero-initialized). */
  uint8_t *heap_data = calloc(heap_bytes, 1);
  if (!heap_data) { perror("calloc heap"); return 1; }

  heap_t heap = { .data = heap_data, .size = heap_bytes };

  /* Initialize heap as one big free block via verified init_heap */
  printf("Initializing %zu-byte heap ...\n", heap_bytes);
  uint64_t fp = init_heap(heap);
  printf("init_heap returned fp = %llu\n", (unsigned long long)fp);

  /* Allocate a few objects */
  printf("Allocating objects ...\n");
  K___uint64_t_uint64_t r1 = allocate(heap, fp, 2);
  printf("  alloc(2): fp=%llu, obj=%llu\n",
         (unsigned long long)r1.fst, (unsigned long long)r1.snd);
  fp = r1.fst;

  K___uint64_t_uint64_t r2 = allocate(heap, fp, 3);
  printf("  alloc(3): fp=%llu, obj=%llu\n",
         (unsigned long long)r2.fst, (unsigned long long)r2.snd);
  fp = r2.fst;

  K___uint64_t_uint64_t r3 = allocate(heap, fp, 1);
  printf("  alloc(1): fp=%llu, obj=%llu\n",
         (unsigned long long)r3.fst, (unsigned long long)r3.snd);
  fp = r3.fst;

  /* Gray stack: capacity in words. */
  size_t gray_cap = heap_bytes / sizeof(uint64_t);
  uint64_t *gray_storage = calloc(gray_cap, sizeof(uint64_t));
  size_t gray_top = gray_cap;  /* stack grows downward; start at capacity */
  if (!gray_storage) { perror("calloc gray"); free(heap_data); return 1; }

  gray_stack_rec st = {
    .storage = gray_storage,
    .top     = &gray_top,
    .cap     = gray_cap
  };

  /* Collect: no roots, so all objects become free */
  printf("Running collect ...\n");
  uint64_t result_fp = collect(heap, st, fp);
  printf("collect returned fp = %llu\n", (unsigned long long)result_fp);

  /* Verify coalescing: fp should point to the first object position (8),
   * meaning all three freed blocks were merged into one contiguous block. */
  if (result_fp != 8) {
    printf("FAIL: expected coalesced fp=8, got %llu\n", (unsigned long long)result_fp);
    free(gray_storage); free(heap_data);
    return 1;
  }

  /* Allocate a large object that wouldn't fit without coalescing.
   * Without coalescing, the largest free block would be the original remainder
   * (heap_size/8 - 2 - 3 - 4 - 2 - 1 = 116 words for 1024-byte heap).
   * With coalescing, we get heap_size/8 - 2 = 126 words. */
  uint64_t big_wosize = heap_size_u64 / 8 - 2; /* max possible allocation */
  K___uint64_t_uint64_t r4 = allocate(heap, result_fp, big_wosize);
  printf("  alloc(%llu) after GC: fp=%llu, obj=%llu\n",
         (unsigned long long)big_wosize,
         (unsigned long long)r4.fst, (unsigned long long)r4.snd);
  if (r4.snd == 0) {
    printf("FAIL: large allocation after coalesce returned null\n");
    free(gray_storage); free(heap_data);
    return 1;
  }

  printf("All tests passed.\n");
  free(gray_storage);
  free(heap_data);
  return 0;
}
