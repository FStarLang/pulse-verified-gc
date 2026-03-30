/* Compatibility header for extern symbols from spec modules.
 * Include after internal headers in Pulse_Lib_GC.c. */

#ifndef PULSEGC_COMPAT_H
#define PULSEGC_COMPAT_H

#include "krmllib.h"

extern uint8_t Pulse_Spec_GC_Heap_uint64_to_uint8(uint64_t x);
extern uint64_t Pulse_Spec_GC_Heap_combine_bytes(
    uint8_t b0, uint8_t b1, uint8_t b2, uint8_t b3,
    uint8_t b4, uint8_t b5, uint8_t b6, uint8_t b7);
extern uint64_t Pulse_Spec_GC_Heap_f_address(uint64_t h_addr);
extern uint64_t Pulse_Spec_GC_Object_colorHeader(
    uint64_t header, Pulse_Lib_Header_color_sem new_color);
extern uint64_t FStar_UInt64_uint_to_t(krml_checked_int_t x);

#endif /* PULSEGC_COMPAT_H */
