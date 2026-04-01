/* Minimal test harness for the verified mark-and-sweep GC.
 *
 * Provides the heap_size_u64 extern required by GC_Impl.c,
 * allocates a toy heap + gray stack, and calls collect().
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

  /* Gray stack: capacity in words. */
  size_t gray_cap = heap_bytes / sizeof(uint64_t);
  uint64_t *gray_storage = calloc(gray_cap, sizeof(uint64_t));
  size_t gray_top = 0;
  if (!gray_storage) { perror("calloc gray"); free(heap_data); return 1; }

  gray_stack_rec st = {
    .storage = gray_storage,
    .top     = &gray_top,
    .cap     = gray_cap
  };

  /* First pointer: nothing live, so collect is a no-op sweep. */
  uint64_t fp = 0;

  printf("Running collect on a %zu-byte heap ...\n", heap_bytes);
  uint64_t result = collect(heap, st, fp);
  printf("collect returned: %llu\n", (unsigned long long)result);

  /* Note: collect mutates the heap in-place.  On an all-zero heap the
   * sweep may corrupt metadata, so we skip freeing heap_data here to
   * keep the smoke-test simple.  A real embedder would supply a valid
   * heap with properly formatted OCaml object headers. */
  free(gray_storage);
  return 0;
}
