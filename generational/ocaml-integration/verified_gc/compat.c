/* compat.c — Implementations of extern primitives declared by KaRaMeL extraction.
 *
 * GC_Gen_Impl.c (the extracted verified code) declares these as:
 *   extern uint64_t read_u64_le(uint8_t *arr, size_t offset);
 *   extern void write_u64_le(uint8_t *arr, size_t offset, uint64_t v);
 *
 * They originate from GC.Impl.ArrayWord's `assume val` declarations in F*,
 * which model word-level heap read/write as opaque primitives.  On
 * little-endian platforms (x86-64, AArch64-LE), these are simple aligned
 * word loads/stores.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

uint64_t read_u64_le(uint8_t *arr, size_t offset) {
  return *(uint64_t *)(arr + offset);
}

void write_u64_le(uint8_t *arr, size_t offset, uint64_t v) {
  *(uint64_t *)(arr + offset) = v;
}
