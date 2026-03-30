/*
 * Pulse GC Runtime — C implementations for spec-level extern symbols.
 *
 * These functions are defined in F* spec modules that KaRaMeL marks
 * as -library (abstract). We provide concrete C implementations here.
 *
 * TODO: Make these inline_for_extraction in the F* spec modules so
 * they get inlined during extraction, eliminating this file.
 */

#include <stdint.h>
#include <stdbool.h>
#include "krmllib.h"
#include "internal/Pulse_Spec_GC_Pulse_Lib_Header_Pulse_Lib_Address.h"
#include "internal/Pulse_Lib_GC.h"

/* -------------------------------------------------------------------------
 * Pulse.Spec.GC.Base constants
 * ------------------------------------------------------------------------- */

uint64_t Pulse_Spec_GC_Base_mword = 8;
krml_checked_int_t Pulse_Spec_GC_Base_heap_size = 1024;
uint64_t Pulse_Spec_GC_Base_zero_addr = 0;

/* -------------------------------------------------------------------------
 * Pulse.Spec.GC.Heap helper functions
 * ------------------------------------------------------------------------- */

/* uint64_to_uint8: truncate uint64 to low byte */
uint8_t Pulse_Spec_GC_Heap_uint64_to_uint8(uint64_t x) {
    return (uint8_t)(x & 0xFF);
}

/* combine_bytes: pack 8 bytes into uint64_t (little-endian) */
uint64_t Pulse_Spec_GC_Heap_combine_bytes(
    uint8_t b0, uint8_t b1, uint8_t b2, uint8_t b3,
    uint8_t b4, uint8_t b5, uint8_t b6, uint8_t b7)
{
    return (uint64_t)b0
        | ((uint64_t)b1 << 8)
        | ((uint64_t)b2 << 16)
        | ((uint64_t)b3 << 24)
        | ((uint64_t)b4 << 32)
        | ((uint64_t)b5 << 40)
        | ((uint64_t)b6 << 48)
        | ((uint64_t)b7 << 56);
}

/* f_address: header address → first field address (skip 8-byte header) */
uint64_t Pulse_Spec_GC_Heap_f_address(uint64_t h_addr) {
    return h_addr + 8;
}

/* -------------------------------------------------------------------------
 * Pulse.Spec.GC.Object helper functions
 * ------------------------------------------------------------------------- */

/* colorHeader: replace color bits [8:9] in header with new_color
 * Header layout: | wosize (54 bits) | color (2 bits) | tag (8 bits) | */
uint64_t Pulse_Spec_GC_Object_colorHeader(
    uint64_t header,
    Pulse_Lib_Header_color_sem new_color)
{
    uint64_t mask = ~((uint64_t)0x3 << 8);
    return (header & mask) | ((uint64_t)new_color << 8);
}

/* -------------------------------------------------------------------------
 * FStar.UInt64 runtime support
 * ------------------------------------------------------------------------- */

uint64_t FStar_UInt64_uint_to_t(krml_checked_int_t x) {
    return (uint64_t)x;
}
