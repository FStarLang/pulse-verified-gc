/* PulseGC_compat.h — Type definitions for spec types used in extracted code.
 *
 * KaRaMeL extracts Pulse.Spec.GC.Base types (hp_addr, obj_addr, etc.) as
 * opaque names because the spec modules are not included in the extraction
 * bundle. These types are all refinements of uint64_t in the F* source,
 * so we typedef them accordingly here.
 *
 * Similarly, Pulse.Lib.Header.color_sem is an algebraic type in F* that
 * maps to a simple enum in C.
 *
 * This file is automatically included before PulseGC.h.
 */

#ifndef PULSEGC_COMPAT_H
#define PULSEGC_COMPAT_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* -------------------------------------------------------------------------- */
/* Spec types → C types                                                       */
/* -------------------------------------------------------------------------- */

/* hp_addr: word-aligned heap address (refinement of uint64_t in F*) */
typedef uint64_t Pulse_Spec_GC_Base_hp_addr;

/* obj_addr: object address, >= 8 (refinement of uint64_t in F*) */
typedef uint64_t Pulse_Spec_GC_Base_obj_addr;

/* heap: spec-level heap (Seq.seq uint8_t in F*); not used at runtime */
typedef void *Pulse_Spec_GC_Base_heap;

/* color_sem: GC color (algebraic type in F*) */
typedef enum {
  Pulse_Lib_Header_White = 0,
  Pulse_Lib_Header_Gray  = 1,
  Pulse_Lib_Header_Blue  = 2,
  Pulse_Lib_Header_Black = 3
} Pulse_Lib_Header_color_sem;

/* Color constants matching F* definitions */
static const Pulse_Lib_Header_color_sem white = Pulse_Lib_Header_White;
static const Pulse_Lib_Header_color_sem gray  = Pulse_Lib_Header_Gray;
static const Pulse_Lib_Header_color_sem blue  = Pulse_Lib_Header_Blue;
static const Pulse_Lib_Header_color_sem black = Pulse_Lib_Header_Black;

/* krml_checked_int_t: already defined by krmllib/krml/internal/compat.h as int32_t */

/* -------------------------------------------------------------------------- */
/* Spec-level functions used in extracted code                                */
/* -------------------------------------------------------------------------- */

/* Byte/word conversion (spec helpers called from Pulse.Lib.GC.Heap) */
static inline uint64_t Pulse_Spec_GC_Heap_uint8_to_uint64(uint8_t x) {
  return (uint64_t)x;
}

static inline uint8_t Pulse_Spec_GC_Heap_uint64_to_uint8(uint64_t x) {
  return (uint8_t)(x & 0xFF);
}

static inline uint64_t
Pulse_Spec_GC_Heap_combine_bytes(uint8_t b0, uint8_t b1, uint8_t b2,
                                  uint8_t b3, uint8_t b4, uint8_t b5,
                                  uint8_t b6, uint8_t b7) {
  return (uint64_t)b0
       | ((uint64_t)b1 << 8)
       | ((uint64_t)b2 << 16)
       | ((uint64_t)b3 << 24)
       | ((uint64_t)b4 << 32)
       | ((uint64_t)b5 << 40)
       | ((uint64_t)b6 << 48)
       | ((uint64_t)b7 << 56);
}

/* f_address: compute object (first field) address from header address */
static inline Pulse_Spec_GC_Base_obj_addr
Pulse_Spec_GC_Heap_f_address(Pulse_Spec_GC_Base_hp_addr h) {
  return h + 8; /* mword = 8 */
}

/* field1_of: address of first field (same as f_address) */
static inline Pulse_Spec_GC_Base_hp_addr
field1_of(Pulse_Spec_GC_Base_hp_addr h) {
  return h + 8;
}

/* -------------------------------------------------------------------------- */
/* Functions that KaRaMeL could not extract (declared here, defined in stubs) */
/* -------------------------------------------------------------------------- */

/* Forward declaration for struct type used in function signatures */
struct heap_t_s;
typedef struct heap_t_s heap_t;

/* getColor: extract color bits (8-9) from header and return enum */
Pulse_Lib_Header_color_sem getColor(uint64_t hdr);

/* pack_color: convert enum to header bit pattern */
static inline uint64_t Pulse_Lib_Header_pack_color(Pulse_Lib_Header_color_sem c) {
  return (uint64_t)c;
}

/* field_address_pure: compute field address (h_addr + i * 8) */
static inline uint64_t
field_address_pure(Pulse_Spec_GC_Base_hp_addr h_addr, uint64_t i) {
  return h_addr + i * 8;
}

/* read_field: read a field value from the heap */
uint64_t read_field(heap_t heap, Pulse_Spec_GC_Base_hp_addr h_addr,
                    uint64_t i, void *dummy);

/* parent_closure_of_infix: find parent closure of an infix object */
Pulse_Spec_GC_Base_hp_addr
parent_closure_of_infix(heap_t heap, Pulse_Spec_GC_Base_hp_addr obj);

/* Pulse_Lib_Reference_replace: update a stack-allocated variable */
static inline void
Pulse_Lib_Reference_replace(uint64_t *r, uint64_t new_val, void *dummy) {
  (void)dummy;
  *r = new_val;
}

/* FStar_Seq_Base_index: spec-only (should not be called at runtime) */
static inline uint8_t
FStar_Seq_Base_index(void *s, int32_t idx) {
  (void)s; (void)idx;
  return 0; /* spec_read_word is a spec function, not called at runtime */
}

/* FStar_UInt64_uint_to_t / FStar_UInt64_v: defined in stubs (extern in krmllib) */

#endif /* PULSEGC_COMPAT_H */
