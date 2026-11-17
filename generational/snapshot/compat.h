/* compat.h — Declarations for extern primitives provided by compat.c */

#ifndef COMPAT_H
#define COMPAT_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/* Heap configuration (GC.Spec.ZeroAddr externs) */
extern uint64_t zero_addr;
extern uint64_t heap_size_u64;

/* FStar library functions */
bool FStar_UInt64_ne(uint64_t a, uint64_t b);

/* Word-level heap read/write (GC.Impl.ArrayWord assumed vals).
 * On little-endian platforms (x86-64, AArch64-LE), these are simple
 * aligned word loads/stores.  Static inline, so that every extracted file
 * (compiled with -include compat.h) inlines them without link-time
 * optimisation; the extracted files' own `extern` declarations of them
 * then refer to these (C11 6.2.2p4: the prior internal linkage wins). */
static inline uint64_t read_u64_le(uint8_t *arr, size_t offset) {
  return *(uint64_t *)(arr + offset);
}

static inline void write_u64_le(uint8_t *arr, size_t offset, uint64_t v) {
  *(uint64_t *)(arr + offset) = v;
}

#endif /* COMPAT_H */
