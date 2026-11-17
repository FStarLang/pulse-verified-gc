/* compat.c — Extern primitives for the extracted verified GC.
 *
 * Provides:
 *   1. Heap configuration constants (GC.Spec.ZeroAddr externs)
 *   2. FStar library functions that KaRaMeL doesn't bundle
 *   (the word-level heap read/write, GC.Impl.ArrayWord's assumed vals,
 *   are static inline in compat.h)
 *
 * The heap configuration values (zero_addr, heap_size_u64) must be set
 * by the bridge BEFORE calling krmlinit() — see verified_gc_bridge.c.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

/* --- Heap configuration (GC.Spec.ZeroAddr externs) --- */

/* Base address of the managed heap (byte offset into the heap array).
 * Set by the bridge before krmlinit(). */
uint64_t zero_addr = 0;

/* Heap size in bytes (must be word-aligned, >= 16).
 * Set by the bridge before krmlinit(). */
uint64_t heap_size_u64 = 0;

/* --- FStar library functions --- */

bool FStar_UInt64_ne(uint64_t a, uint64_t b) { return a != b; }

/* The Pulse.Lib.Array functions the GC calls (`fill`, `zeroize`) are now
 * extracted by F* together with the GC (see ../Makefile), so they are no
 * longer provided here. */

/* --- Word-level heap read/write (GC.Impl.ArrayWord assumed vals) ---
 * read_u64_le and write_u64_le are static inline in compat.h. */
