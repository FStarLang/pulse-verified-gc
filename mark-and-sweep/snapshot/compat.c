/* compat.c — Extern primitives for the extracted verified GC. */

#include "compat.h"

bool FStar_UInt64_ne(uint64_t a, uint64_t b) {
  return a != b;
}

uint64_t read_u64_le(uint8_t *arr, size_t offset) {
  return *(uint64_t *)(arr + offset);
}

void write_u64_le(uint8_t *arr, size_t offset, uint64_t v) {
  *(uint64_t *)(arr + offset) = v;
}
