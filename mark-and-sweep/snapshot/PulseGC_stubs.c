/* PulseGC_stubs.c — Runtime stubs for extern declarations in extracted code.
 *
 * Provides definitions for:
 * - Color equality comparison
 * - getColor (extract color bits from header)
 * - read_field (read object field from heap)
 * - parent_closure_of_infix (resolve infix object to parent closure)
 * - Spec-level constants (mword, heap_size, tags)
 *
 * These are "extern" in the KaRaMeL-generated PulseGC.h because the
 * corresponding F* definitions were in modules that KaRaMeL could not
 * fully translate to Low*.
 */

#include "PulseGC.h"

/* -------------------------------------------------------------------------- */
/* Color equality                                                             */
/* -------------------------------------------------------------------------- */

bool __eq__Pulse_Lib_Header_color_sem(Pulse_Lib_Header_color_sem x,
                                       Pulse_Lib_Header_color_sem y) {
  return x == y;
}

/* -------------------------------------------------------------------------- */
/* getColor: extract color bits (8-9) from 64-bit OCaml header                */
/* -------------------------------------------------------------------------- */

Pulse_Lib_Header_color_sem getColor(uint64_t hdr) {
  uint64_t raw = (hdr >> 8) & 0x3;
  switch (raw) {
    case 0:  return Pulse_Lib_Header_White;
    case 1:  return Pulse_Lib_Header_Gray;
    case 2:  return Pulse_Lib_Header_Blue;
    case 3:  return Pulse_Lib_Header_Black;
    default: return Pulse_Lib_Header_White; /* unreachable */
  }
}

/* -------------------------------------------------------------------------- */
/* read_field: read field i of object at h_addr                               */
/* -------------------------------------------------------------------------- */

uint64_t read_field(heap_t heap, Pulse_Spec_GC_Base_hp_addr h_addr,
                    uint64_t i, void *dummy) {
  (void)dummy;
  uint64_t addr = h_addr + i * 8;
  return read_word(heap, addr);
}

/* -------------------------------------------------------------------------- */
/* parent_closure_of_infix: resolve infix object → parent closure             */
/* -------------------------------------------------------------------------- */

Pulse_Spec_GC_Base_hp_addr
parent_closure_of_infix(heap_t heap, Pulse_Spec_GC_Base_hp_addr obj) {
  /* Read the infix offset from the first field (wosize encodes offset) */
  uint64_t hdr = read_word(heap, obj);
  uint64_t offset_words = getWosize(hdr);
  /* Parent closure header is offset_words * 8 bytes before this header */
  uint64_t offset_bytes = offset_words * 8;
  return obj - offset_bytes;
}

/* -------------------------------------------------------------------------- */
/* Spec-level constants                                                       */
/* -------------------------------------------------------------------------- */

/* Machine word size (8 bytes on 64-bit) */
uint64_t mword = 8;

/* Heap size: 1 MB (configurable) */
krml_checked_int_t heap_size = 1048576;
size_t heap_size_sz = 1048576;

/* First valid object address (after null sentinel) */
Pulse_Spec_GC_Base_hp_addr zero_addr = 0;

/* -------------------------------------------------------------------------- */
/* FStar.UInt64 conversion functions (extern in krmllib headers)              */
/* -------------------------------------------------------------------------- */

uint64_t FStar_UInt64_uint_to_t(krml_checked_int_t x) {
  return (uint64_t)(uint32_t)x;
}

krml_checked_int_t FStar_UInt64_v(uint64_t x) {
  return (krml_checked_int_t)x;
}
