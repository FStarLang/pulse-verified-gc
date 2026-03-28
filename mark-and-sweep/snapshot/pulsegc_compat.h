/* Hand-maintained declarations for extern symbols that KaRaMeL drops
 * due to FStar.UInt.uint_t type issues.
 *
 * These functions are implemented in pulsegc_runtime.c.
 * This header is included in Pulse_Lib_GC.c after the internal headers
 * that define the needed types.
 */

#ifndef PULSEGC_COMPAT_H
#define PULSEGC_COMPAT_H

#include "krmllib.h"
#include "internal/Pulse_Spec_GC_Pulse_Lib_Header_Pulse_Lib_Address.h"

/* Pulse.Lib.Header.pack_color — color_sem → uint_t 64 */
extern krml_checked_int_t
Pulse_Lib_Header_pack_color(Pulse_Lib_Header_color_sem c);

/* Pulse.Lib.Header.unpack_color — uint_t 64 → option color_sem */
extern FStar_Pervasives_Native_option__Pulse_Lib_Header_color_sem
Pulse_Lib_Header_unpack_color(krml_checked_int_t w);

#endif /* PULSEGC_COMPAT_H */
