/* Hand-maintained declarations for extern symbols that KaRaMeL drops.
 *
 * These functions are implemented in pulsegc_runtime.c.
 * This header is included in Pulse_Lib_GC.c after the internal headers.
 */

#ifndef PULSEGC_COMPAT_H
#define PULSEGC_COMPAT_H

#include "krmllib.h"

/* FStar.UInt64.uint_to_t — converts spec-level int to uint64_t.
 * Used for heap_size comparisons in isPointer and sweep loop. */
extern uint64_t FStar_UInt64_uint_to_t(krml_checked_int_t x);

#endif /* PULSEGC_COMPAT_H */
