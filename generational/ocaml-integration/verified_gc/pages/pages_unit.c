/* pages_unit.c — the verified page allocator and page sweep
 * (GC.Impl.Pages.*, extracted to mark-and-sweep/pages-c), as one
 * translation unit for the runtime (VERGC_ALLOC=pages, alloc_gen.c).
 *
 * Compiled once per page size, with -DPAGES_KB=32 or 16 and -I naming the
 * directory of that size's extraction (verified_gc/Makefile).  The extracted
 * files are #included unchanged.  Their exported names (init, alloc,
 * sweep, ...) and their copies of the heap bounds (zero_addr1, ...) are
 * renamed here to vergc_p32_x_* / vergc_p16_x_*, so that both sizes and the
 * generational collector (which has globals of the same names) link into one
 * runtime.
 *
 * The three functions at the end are the whole interface, and are unverified
 * glue: they hold the heap record and the allocator's state (the page map and
 * the word array of GC.Impl.Pages.State), allocate them, and call the
 * extracted init, alloc_white and sweep. */

#include <stdio.h>
#include <stdlib.h>
#include "krmllib.h"

/* VP: this file's interface; VX: the extracted code's own names. */
#if PAGES_KB == 32
#define VP(x) vergc_p32_##x
#define VX(x) vergc_p32_x_##x
#elif PAGES_KB == 16
#define VP(x) vergc_p16_##x
#define VX(x) vergc_p16_x_##x
#else
#error "PAGES_KB must be 32 or 16"
#endif

#define page_hdr_u640    VX(page_hdr_u640)
#define tail_hdr_u640    VX(tail_hdr_u640)
#define init             VX(init)
#define alloc_white      VX(alloc_white)
#define alloc            VX(alloc)
#define start_sweep      VX(start_sweep)
#define sweep_all        VX(sweep_all)
#define sweep            VX(sweep)
#define heap_size_u640   VX(heap_size_u640)
#define zero_addr0       VX(zero_addr0)
#define zero_addr1       VX(zero_addr1)
#define krmlinit_globals VX(krmlinit_globals)

#include "GC_Pages_Spec.c"
#include "GC_Pages.c"
#include "krmlinit.c"

#define PAGE_BYTES ((uint64_t)PAGES_KB * 1024ULL)
/* GC.Impl.Pages.State's word array: the class lists and their tails, list
 * 0's head, the hint, the epoch and the three class tables (272 words at
 * both sizes); with room to spare. */
#define TW_WORDS 1024

static heap_t   pheap;
static pstate_t pst;

/* After zero_addr and heap_size_u64 are set: the extracted code's copies of
 * them, the state, and the heap laid out as free pages (GC.Impl.Pages.Init). */
void VP(setup)(uint64_t heap_bytes) {
    krmlinit_globals();
    if (getWosize(page_hdr_u640()) + 1ULL != PAGE_BYTES / 8ULL) {
        fprintf(stderr, "verified gen GC: the %d KB page allocator was built from "
                        "an extraction with %llu-word pages\n", PAGES_KB,
                (unsigned long long)(getWosize(page_hdr_u640()) + 1ULL));
        exit(2);
    }
    uint64_t n_pages = heap_bytes / PAGE_BYTES;
    if (n_pages == 0) {
        fprintf(stderr, "verified gen GC: the major heap is smaller than one page\n");
        exit(2);
    }
    pst.tpm = (prec *)calloc((size_t)n_pages, sizeof(prec));
    pst.tw = (uint64_t *)calloc(TW_WORDS, sizeof(uint64_t));
    if (!pst.tpm || !pst.tw) {
        fprintf(stderr, "verified gen GC: cannot allocate the page map\n");
        exit(2);
    }
    pheap.data = NULL;           /* the NULL-base trick, as the major heap */
    pheap.size = (size_t)heap_bytes;
    init(pheap, pst);
}

uint64_t VP(alloc_white)(uint64_t wz) { return alloc_white(pheap, pst, wz); }

void VP(sweep)(void) { sweep(pheap, pst); }
