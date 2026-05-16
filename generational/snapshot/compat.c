/* compat.c — Extern primitives for the extracted verified GC.
 *
 * Provides:
 *   1. Heap configuration constants (GC.Spec.ZeroAddr externs)
 *   2. FStar library functions that KaRaMeL doesn't bundle
 *   3. Word-level heap read/write (GC.Impl.ArrayWord assumed vals)
 *
 * The heap configuration values (zero_addr, heap_size_u64) must be set
 * by the bridge BEFORE calling krmlinit() — see verified_gc_bridge.c.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* --- Heap configuration (GC.Spec.ZeroAddr externs) --- */

/* Base address of the managed heap (byte offset into the heap array).
 * Set by the bridge before krmlinit(). */
uint64_t zero_addr = 0;

/* Heap size in bytes (must be word-aligned, >= 16).
 * Set by the bridge before krmlinit(). */
uint64_t heap_size_u64 = 0;

/* --- FStar library functions --- */

bool FStar_UInt64_ne(uint64_t a, uint64_t b) { return a != b; }

/* --- Pulse library functions --- */

/* Pulse.Lib.Array.fill — fill an array with a constant value.
 * After ghost erasure: fill(n, arr, val, <erased>). */
void Pulse_Lib_Array_fill(size_t n, uint64_t *arr, uint64_t val, void *ghost) {
  (void)ghost;
  for (size_t i = 0; i < n; i++) arr[i] = val;
}

/* --- Word-level heap read/write (GC.Impl.ArrayWord assumed vals) ---
 * On little-endian platforms (x86-64, AArch64-LE), these are simple
 * aligned word loads/stores. */
uint64_t read_u64_le(uint8_t *arr, size_t offset) {
  return *(uint64_t *)(arr + offset);
}

void write_u64_le(uint8_t *arr, size_t offset, uint64_t v) {
  *(uint64_t *)(arr + offset) = v;
}
