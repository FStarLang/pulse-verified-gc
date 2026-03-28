/*
 * Pulse GC Runtime — Provides extern symbols from spec modules.
 *
 * These are F* spec-level definitions that KaRaMeL marked as -library.
 * We provide concrete C implementations matching the F* values.
 *
 * Constants from Pulse.Spec.GC.Base:
 *   mword      = 8   (bytes per machine word)
 *   heap_size  = 1024 (total heap bytes)
 *   zero_addr  = 0
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

/* Aliases used in Pulse_Lib_GC (from Pulse.Lib.GC.Heap re-exports) */
uint64_t mword = 8;
krml_checked_int_t heap_size = 1024;
uint64_t zero_addr = 0;

/* -------------------------------------------------------------------------
 * Pulse.Spec.GC.Heap helper functions
 * ------------------------------------------------------------------------- */

/* uint64_to_uint8: truncate to low byte */
uint8_t Pulse_Spec_GC_Heap_uint64_to_uint8(uint64_t x) {
    return (uint8_t)(x & 0xFF);
}

/* combine_bytes: pack 8 bytes into a uint64_t (little-endian) */
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

/* f_address: compute field address from header address
 * f_address(h_addr) = h_addr + mword (skip header to get first field) */
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
    /* Clear bits 8-9, set new color */
    uint64_t mask = ~((uint64_t)0x3 << 8);
    return (header & mask) | ((uint64_t)new_color << 8);
}

/* -------------------------------------------------------------------------
 * Pulse.Lib.Header helper functions
 * ------------------------------------------------------------------------- */

/* pack_color: color_sem → uint_t 64 (represented as krml_checked_int_t) */
krml_checked_int_t Pulse_Lib_Header_pack_color(Pulse_Lib_Header_color_sem c) {
    return (krml_checked_int_t)c;
}

/* unpack_color: uint_t 64 → option color_sem */
FStar_Pervasives_Native_option__Pulse_Lib_Header_color_sem
Pulse_Lib_Header_unpack_color(krml_checked_int_t w) {
    FStar_Pervasives_Native_option__Pulse_Lib_Header_color_sem r;
    if (w >= 0 && w <= 3) {
        r.tag = FStar_Pervasives_Native_Some;
        r.v = (Pulse_Lib_Header_color_sem)w;
    } else {
        r.tag = FStar_Pervasives_Native_None;
        r.v = 0;
    }
    return r;
}

/* -------------------------------------------------------------------------
 * FStar.UInt64 runtime support
 * ------------------------------------------------------------------------- */

krml_checked_int_t FStar_UInt64_n = 64;

uint64_t FStar_UInt64_uint_to_t(krml_checked_int_t x) {
    return (uint64_t)x;
}

krml_checked_int_t FStar_UInt64_v(uint64_t x) {
    return (krml_checked_int_t)x;
}

krml_checked_int_t FStar_UInt64___proj__Mk__item__v(uint64_t projectee) {
    return (krml_checked_int_t)projectee;
}
