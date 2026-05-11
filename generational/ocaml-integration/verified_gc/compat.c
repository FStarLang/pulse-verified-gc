/* compat.c — Missing krmllib primitives for standalone compilation.
 *
 * These are trivial implementations of FStar library functions that
 * KaRaMeL declares as extern but doesn't provide implementations for
 * in the minimal krmllib distribution.
 */

#include <stdint.h>
#include <stdbool.h>

bool FStar_UInt64_ne(uint64_t a, uint64_t b) { return a != b; }
