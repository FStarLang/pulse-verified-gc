/* allocator.h — Simple C free-list allocator for the verified GC.
 *
 * Manages a contiguous heap.  After collect() runs, the free list is
 * threaded through dead objects' first fields (OCaml value addresses).
 * The allocator walks this list for allocation.
 */

#ifndef ALLOCATOR_H
#define ALLOCATOR_H

#include <stdint.h>
#include <stddef.h>

/* Initialize the allocator with the given heap size in bytes.
 * Returns 0 on success, -1 on failure. */
int allocator_init(size_t heap_bytes);

/* Allocate space for an object of wosize words.
 * Returns a pointer to the HEADER (not the first field).
 * Returns NULL on failure (caller should trigger GC and retry). */
void *allocator_alloc(size_t wosize);

/* Set the free-list head (value address, i.e., header + 8).
 * Called after collect() returns the new free pointer. */
void allocator_set_freelist(uint64_t fp);

/* Get the current free-list head (value address). */
uint64_t allocator_get_freelist(void);

/* Get the heap base pointer. */
uint8_t *allocator_get_heap_base(void);

/* Get the heap size in bytes. */
size_t allocator_get_heap_size(void);

/* Get the heap end address (first byte past the heap). */
uint64_t allocator_get_heap_end(void);

#endif /* ALLOCATOR_H */
