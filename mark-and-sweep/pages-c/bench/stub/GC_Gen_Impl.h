/* Stand-in for the generational snapshot's header: proto.h needs heap_t only. */
#ifndef GC_Gen_Impl_H
#define GC_Gen_Impl_H
#include <stdint.h>
#include <stddef.h>
typedef struct heap_t_s { uint8_t *data; size_t size; } heap_t;
#endif
