/* pages_redirect.c - the extracted page allocator (../GC_Pages.c) as one
 * translation unit beside main's generational collector, for the redirect
 * build of bench_promo.c (-DREDIRECT): akhil's extracted Cheney promotion
 * (generational/snapshot/GC_Gen_Impl.c), its `allocate` sent here, as on
 * sheera/pages-runtime (verified_gc/pages/pages_unit.c, hook_allocate.py).
 * Unverified glue, for the benchmark only.
 *
 * The extracted files are #included unchanged; the names they share with
 * main's (its minor_collect, its copies of the heap bounds, krmlinit_globals)
 * are renamed here.  The heap record and the page state live here; the
 * interface is the rp_* functions. */

#define minor_collect    rp_x_minor_collect
#define zero_addr0       rp_x_zero_addr0
#define zero_addr1       rp_x_zero_addr1
#define heap_size_u640   rp_x_heap_size_u640
#define krmlinit_globals rp_x_krmlinit_globals

#include "GC_Pages_Spec.c"
#include "GC_Pages.c"
#include "krmlinit.c"

#define NCLS 31
#define NL 17
#define W_LEN ((2 * NCLS + NL) + 2 + 129 + 2 * NCLS)
#define RP_MAX_PAGES 1024

static heap_t   pheap;
static pstate_t pst;
static prec     pm[RP_MAX_PAGES];
static uint64_t tw[W_LEN];

/* After zero_addr and heap_size_u64 are set: the heap laid out as free pages. */
void rp_init(uint8_t *mem, size_t bytes) {
    krmlinit_globals();
    pheap.data = mem; pheap.size = bytes;
    pst.tpm = pm; pst.tw = tw;
    init(pheap, pst);
}

/* The allocation the verified Idle promotion makes (alloc_ph, not marking). */
uint64_t rp_alloc(uint64_t wz, uint64_t tag) { return alloc_ph(pheap, pst, wz, tag, false); }

/* As sheera/pages-runtime's vergc_pages_allocate: alloc_white, the tag ORed in. */
uint64_t rp_alloc_white(uint64_t wz, uint64_t tag) {
    uint64_t o = alloc_white(pheap, pst, wz);
    if (o != 0) { uint64_t h; memcpy(&h, pheap.data + o - 8, 8); h |= tag; memcpy(pheap.data + o - 8, &h, 8); }
    return o;
}

void rp_sweep(void) { start_sweep(pst); sweep_all(pheap, pst); }
