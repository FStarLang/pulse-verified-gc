/* compat.h — Declarations for extern primitives provided by compat.c */

#ifndef COMPAT_H
#define COMPAT_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

bool FStar_UInt64_ne(uint64_t a, uint64_t b);
uint64_t read_u64_le(uint8_t *arr, size_t offset);
void write_u64_le(uint8_t *arr, size_t offset, uint64_t v);

#endif /* COMPAT_H */
