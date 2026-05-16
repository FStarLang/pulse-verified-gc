/* compat.c — Missing krmllib primitives for standalone compilation.
 *
 * These are trivial implementations of FStar library functions that
 * KaRaMeL declares as extern but doesn't provide implementations for
 * in the minimal krmllib distribution.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

bool FStar_UInt64_ne(uint64_t a, uint64_t b) { return a != b; }

/* Word-level heap read/write (GC.Impl.ArrayWord assumed vals).
 * On little-endian platforms (x86-64, AArch64-LE), these are simple
 * aligned word loads/stores. */
uint64_t read_u64_le(uint8_t *arr, size_t offset) {
  return *(uint64_t *)(arr + offset);
}

void write_u64_le(uint8_t *arr, size_t offset, uint64_t v) {
  *(uint64_t *)(arr + offset) = v;
}
