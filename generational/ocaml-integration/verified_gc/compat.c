/* compat.c — Stub file for standalone compilation.
 *
 * All FStar library functions that KaRaMeL needs have been eliminated
 * from the extraction (U64.ne → not (U64.eq), etc.), so this file
 * is now empty. Kept as a placeholder in case future extractions
 * reintroduce extern dependencies.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* Word-level heap read/write (GC.Impl.ArrayWord assumed vals).
 * On little-endian platforms (x86-64, AArch64-LE), these are simple
 * aligned word loads/stores. */
uint64_t read_u64_le(uint8_t *arr, size_t offset) {
  return *(uint64_t *)(arr + offset);
}

void write_u64_le(uint8_t *arr, size_t offset, uint64_t v) {
  *(uint64_t *)(arr + offset) = v;
}
