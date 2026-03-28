/* Hand-maintained declarations for extern symbols that KaRaMeL drops
 * due to FStar.UInt.uint_t type issues.
 *
 * These functions are implemented in pulsegc_runtime.c.
 * This header is included early in Pulse_Lib_GC.c (via sed during snapshot),
 * after internal/Pulse_Lib_GC.h which already pulls in all needed types.
 */

#ifndef PULSEGC_COMPAT_H
#define PULSEGC_COMPAT_H

#include "krmllib.h"
/* Types already defined via internal/Pulse_Lib_GC.h → Pulse_Lib_GC.h chain */

/* Pulse.Lib.Header.pack_color — color_sem → int (uint_t 64 in F*) */
extern krml_checked_int_t
Pulse_Lib_Header_pack_color(uint8_t c);

/* Pulse.Lib.Header.unpack_color — int → option color_sem
 * Returns struct with .tag (None=0/Some=1) and .v (color) */
struct FStar_Pervasives_Native_option__Pulse_Lib_Header_color_sem_s;
extern struct FStar_Pervasives_Native_option__Pulse_Lib_Header_color_sem_s
Pulse_Lib_Header_unpack_color(krml_checked_int_t w);

#endif /* PULSEGC_COMPAT_H */
