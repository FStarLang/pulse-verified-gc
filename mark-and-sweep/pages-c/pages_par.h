/* pages_par.h - the parallel page sweep: the threads (pages_par.c). */
#ifndef PAGES_PAR_H
#define PAGES_PAR_H
#include <stdint.h>
#include "GC_Pages.h"

/* Words per chunk record (CState.pw = 2 * n_cls + 10) and the chunk count
 * for k threads, as the prototype's (one chunk for one thread, else 8 per
 * thread). */
#define PAGES_PAR_PW 72
#define PAGES_PAR_CHUNKS(k) ((k) <= 1 ? 1 : 8 * (k))
#define PAGES_PAR_MAX_CHUNKS 64

/* par_prepare; sweep_chunk for every chunk, on k threads; par_finish.
 * parts: nc * PAGES_PAR_PW words; bounds: nc + 1 words. */
void par_sweep(heap_t heap, pstate_t t, uint32_t *bm, uint64_t *parts, uint64_t *bounds,
               uint64_t nc, int k);
#endif
