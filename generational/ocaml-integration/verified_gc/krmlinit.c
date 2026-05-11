/* krmlinit.c — Initialize derived constants from verified code.
 *
 * Replaces KaRaMeL-generated krmlinit with direct C computation.
 * All values are trivially derived from minor_heap_size (a constant).
 */

#include "krmlinit.h"
#include "internal/GC_Gen_Impl.h"
#include "internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h"

void krmlinit_globals(void)
{
    fwd_array_size = minor_heap_size / 8;
    queue_size_sz  = (size_t)fwd_array_size;
    minor_heap_size_sz = (size_t)minor_heap_size;
}

