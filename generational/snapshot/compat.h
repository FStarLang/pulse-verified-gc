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

/* Pulse library functions */
void Pulse_Lib_Array_fill(size_t n, uint64_t *arr, uint64_t val, void *ghost);
void Pulse_Lib_Array_zeroize(size_t n, uint8_t *arr, void *ghost);

/* Word-level heap read/write (GC.Impl.ArrayWord assumed vals) */
uint64_t read_u64_le(uint8_t *arr, size_t offset);
void write_u64_le(uint8_t *arr, size_t offset, uint64_t v);

#endif /* COMPAT_H */
