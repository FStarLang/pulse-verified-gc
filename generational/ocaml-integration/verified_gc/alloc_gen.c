/* alloc_gen.c — Bridge between OCaml 4.14 runtime and the verified
 *               generational GC (Cheney minor + mark-and-sweep major).
 *
 * Provides:
 *   verified_allocate(wosize, tag)    — called from OCaml's Alloc_small / caml_alloc_shr
 *   caml_trigger_verified_gc(unit)    — OCaml-callable full GC trigger
 *
 * Uses:
 *   gen_alloc()       from GC_Gen_Impl.c — bump alloc (minor) or free-list (major)
 *   minor_collect()   from GC_Gen_Impl.c — Cheney BFS promotion
 *   collect()         from GC_Gen_Impl.c — mark-and-sweep on major heap
 *
 * NULL-base trick (major heap only):
 *   major.data = NULL so that byte offsets become absolute virtual addresses.
 *   Patches to GC_Gen_Impl.c:
 *     1. zero_addr       — non-static, set to heap_base absolute address
 *     2. is_pointer      — lower-bound check (v >= zero_addr + 8)
 *     3. update_all_objects — start at zero_addr instead of 0
 *     4. rescan_heap_impl  — start at zero_addr instead of 0
 *     5. is_valid_fp      — use zero_addr for lower bound
 *     6. darken_if_white_bounded — non-static for root darkening
 *
 * Minor heap:
 *   Uses a real data pointer (minor.data = calloc'd buffer).
 *   Minor offsets are 0-based.  The bridge translates between absolute
 *   OCaml pointers and minor offsets at allocation and collection boundaries.
 *
 * Inter-generational pointers:
 *   Uses OCaml's caml_ref_table (populated by caml_modify).  Before minor
 *   collection, the bridge translates ref_table entries from absolute minor
 *   pointers to minor offsets in-place.  After minor_collect, update_all_objects
 *   rewrites them to major addresses (absolute with NULL-base).
 */

#include "GC_Gen_Impl.h"
#include "internal/GC_Gen_Impl.h"
#include "internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h"
#include "krmlinit.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#ifndef CAML_INTERNALS
#define CAML_INTERNALS
#endif
#include <caml/misc.h>
#include <caml/mlvalues.h>
#include <caml/roots.h>
#include <caml/minor_gc.h>  /* for struct caml_ref_table */
#include <caml/domain_state.h>  /* for Caml_state */
#include <caml/address_class.h> /* for In_heap, caml_page_table_add */

/* --- Patched externs from GC_Gen_Impl.c --- */
extern uint64_t zero_addr;
extern uint64_t major_alloc_hwm;
extern bool update_scan_base;
extern size_t queue_size_sz;
extern void darken_if_white_bounded(heap_t heap, gray_stack_rec st, uint64_t h_addr);

/* --- Globals --- */
static gen_heap_t   gc_gen_heap;
static uint64_t    *gc_fwd_arr;
static uint8_t     *minor_base;      /* absolute address of minor heap buffer */
static int          heap_initialized = 0;

/* Inline fast-path globals for Alloc_small_aux (memory.h) */
uint64_t *vergc_minor_bump_ref;
uint8_t  *vergc_minor_base;
uint64_t  vergc_minor_size;

/* Root scanning: parallel arrays for roots and writeback locations */
#define MAX_ROOTS  (1 << 18)  /* 256K root slots */
static uint64_t   root_values[MAX_ROOTS];
static value      *root_locs[MAX_ROOTS];
static size_t      root_count;

/* --- Heap initialization --- */

static void ensure_heap(void) {
    if (heap_initialized) return;
    heap_initialized = 1;

    /* --- Major heap --- */
    size_t major_words = 32 * 1024 * 1024;  /* 256 MB / 8 = 32M words */
    const char *env = getenv("MIN_EXPANSION_WORDSIZE");
    if (env) {
        size_t w = (size_t)atoll(env);
        if (w > 0) major_words = w;
    }
    size_t major_bytes = major_words * 8;

    uint8_t *major_base = (uint8_t *)calloc(1, major_bytes);
    if (!major_base)
        caml_fatal_error("verified gen GC: cannot allocate major heap");

    /* NULL-base trick: GC offsets become absolute addresses */
    zero_addr = (uint64_t)(uintptr_t)major_base;
    heap_size_u64 = (uint64_t)(uintptr_t)(major_base + major_bytes);

    gc_gen_heap.major.data = NULL;
    gc_gen_heap.major.size = major_bytes;

    /* Initialize major free list: one big blue block */
    uint64_t total_words_u64 = (uint64_t)major_words;
    uint64_t wosize = total_words_u64 - 1;
    uint64_t blue_hdr = (wosize << 10) | (2ULL << 8) | 0ULL;  /* blue, tag 0 */
    *(uint64_t *)major_base = blue_hdr;
    *(uint64_t *)(major_base + 8) = 0;  /* free list terminator */

    uint64_t initial_fp = zero_addr + 8;

    /* fp_ref */
    uint64_t *fp_ref = (uint64_t *)malloc(sizeof(uint64_t));
    if (!fp_ref) caml_fatal_error("verified gen GC: malloc fp_ref");
    *fp_ref = initial_fp;
    gc_gen_heap.fp_ref = fp_ref;

    /* --- Minor heap --- */
    /* Override the verified constant (2048B) with a production-sized minor heap.
     * OCaml default is 256K words = 2MB.  We use 256KB (32K words) as a
     * reasonable default, overridable via environment variable. */
    size_t minor_words = 32 * 1024;  /* 256 KB / 8 */
    const char *minor_env = getenv("MINOR_HEAP_WORDS");
    if (minor_env) {
        size_t w = (size_t)atoll(minor_env);
        if (w >= 256) minor_words = w;
    }
    size_t minor_sz = minor_words * 8;
    minor_heap_size_u64 = (uint64_t)minor_sz;
    max_young_wosize_u64 = (uint64_t)(minor_words / 2);  /* max alloc = half minor heap */

    /* Re-derive constants that depend on minor_heap_size */
    krmlinit_globals();
    uint8_t *minor_data = (uint8_t *)calloc(1, minor_sz);
    if (!minor_data)
        caml_fatal_error("verified gen GC: cannot allocate minor heap");
    minor_base = minor_data;

    gc_gen_heap.minor.data = minor_data;
    gc_gen_heap.minor.size = minor_sz;

    uint64_t *bump_ref = (uint64_t *)calloc(1, sizeof(uint64_t));
    if (!bump_ref) caml_fatal_error("verified gen GC: malloc bump_ref");
    gc_gen_heap.minor.bump_ref = bump_ref;

    /* Initialize inline fast-path globals for Alloc_small_aux */
    vergc_minor_bump_ref = bump_ref;
    vergc_minor_base     = minor_data;
    vergc_minor_size     = (uint64_t)minor_sz;

    /* --- Forwarding array --- */
    gc_fwd_arr = (uint64_t *)calloc((size_t)queue_size_sz, sizeof(uint64_t));
    if (!gc_fwd_arr)
        caml_fatal_error("verified gen GC: cannot allocate fwd array");

    /* Register our minor heap with OCaml's domain state so that
     * Is_young() recognizes minor pointers.  Without this, the write
     * barrier in caml_modify / caml_initialize never records
     * major→minor pointers in the ref_table, leaving stale minor
     * addresses in major objects after minor GC. */
    Caml_state->_young_start = (value *)minor_data;
    Caml_state->_young_end   = (value *)(minor_data + minor_sz);
    Caml_state->_young_ptr   = Caml_state->_young_end;
    Caml_state->_young_alloc_start = Caml_state->_young_start;
    Caml_state->_young_alloc_end   = Caml_state->_young_end;

    /* Register our major heap in OCaml's page table so that Is_in_heap()
     * returns true for addresses inside it.  Without this, the write
     * barrier in caml_modify / caml_initialize skips the ref_table update
     * for stores into major-heap objects, leaving inter-generational
     * pointers untracked and causing stale minor addresses after GC. */
    if (caml_page_table_add(In_heap, major_base, major_base + major_bytes) != 0)
        caml_fatal_error("verified gen GC: page table registration failed");

    caml_gc_message(0x20, "Verified gen GC: major=%luMB minor=%luKB\n",
                    (unsigned long)(major_bytes / (1024*1024)),
                    (unsigned long)(minor_sz / 1024));
}

/* --- Address translation helpers --- */

static inline int is_minor_absolute(value v) {
    return (uint64_t)(uintptr_t)v >= (uint64_t)(uintptr_t)minor_base &&
           (uint64_t)(uintptr_t)v < (uint64_t)(uintptr_t)minor_base + minor_heap_size_u64;
}

static inline uint64_t abs_to_minor_offset(value v) {
    return (uint64_t)((uintptr_t)v - (uintptr_t)minor_base);
}

static inline value minor_offset_to_abs(uint64_t off) {
    return (value)((uintptr_t)minor_base + (uintptr_t)off);
}

/* --- Root scanning callback for minor collection --- */

static void scan_minor_root(value root, value *root_ptr) {
    if (root_count >= MAX_ROOTS) return;

    /* Only collect block roots (not integers) */
    if (!Is_block(root) || Wosize_val(root) == 0) return;

    uint64_t translated;
    if (is_minor_absolute(root)) {
        /* Minor pointer: translate absolute → offset */
        translated = abs_to_minor_offset(root);
    } else {
        /* Major pointer or non-heap: pass through */
        translated = (uint64_t)(uintptr_t)root;
    }

    root_values[root_count] = translated;
    root_locs[root_count] = root_ptr;
    root_count++;
}

/* --- Minor collection --- */

static void do_minor_gc(void) {
    ensure_heap();
    Caml_state->_stat_minor_collections++;

    /* 1. Collect roots */
    root_count = 0;
    caml_do_roots(scan_minor_root, 1);

    /* 2. Translate inter-generational pointers (ref_table entries). */
    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        value **r;
        for (r = tbl->base; r < tbl->ptr; r++) {
            value v = **r;
            if (Is_block(v) && is_minor_absolute(v)) {
                **r = (value)(uintptr_t)abs_to_minor_offset(v);
            }
        }
    }

    /* 3. Also add ref_table entries as roots */
    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        value **r;
        for (r = tbl->base; r < tbl->ptr; r++) {
            value v = (value)(uintptr_t)(**r);
            uint64_t v64 = (uint64_t)(uintptr_t)v;
            if (v64 >= 8 && v64 < minor_heap_size_u64 && v64 % 8 == 0) {
                if (root_count >= MAX_ROOTS)
                    caml_fatal_error("verified gen GC: root overflow (ref_table)");
                root_values[root_count] = v64;
                root_locs[root_count] = NULL;
                root_count++;
            }
        }
    }

    /* 4. Zero forwarding array */
    memset(gc_fwd_arr, 0, (size_t)queue_size_sz * sizeof(uint64_t));

    /* 4.1. Infix closure fixup: find closures with embedded infix headers
     * and add their parent addresses as additional roots for Cheney. */
    {
        size_t infix_parents_added = find_infix_parents(
            gc_gen_heap.minor, root_values, root_count, MAX_ROOTS);
        root_count += infix_parents_added;
        /* root_locs for infix parents are unused (NULL) — fill them */
        for (size_t k = root_count - infix_parents_added; k < root_count; k++)
            root_locs[k] = NULL;
        if (infix_parents_added > 0)
            caml_gc_message(0x20, "[gen-gc] infix: added %zu parent roots\n", infix_parents_added);
    }

    /* 4.5. Translate minor heap fields: absolute → offset.
     * OCaml stores absolute addresses in object fields, but the verified GC
     * uses offset-based minor addressing.  The Cheney algorithm needs offsets
     * to discover child objects during BFS.  Without this translation,
     * scan_loop can't follow inter-minor pointers and only root objects
     * get promoted, leaving dangling absolute pointers after reset. */
    translate_minor_fields(gc_gen_heap.minor,
                           (uint64_t)(uintptr_t)minor_base);

    /* 4.6. Set up update_all_objects to only scan newly-promoted objects.
     * Pre-existing major objects' inter-generational pointers are handled
     * via ref_table iteration after minor_collect (step 5.5 below).
     *
     * IMPORTANT: fp is an OBJECT address (header + 8). The scan needs the
     * HEADER address (fp - 8) because update_all_objects reads headers at
     * each scan position. */
    {
        uint64_t fp_pre = *gc_gen_heap.fp_ref;
        major_alloc_hwm = (fp_pre >= 8) ? (fp_pre - 8) : 0ULL;
        update_scan_base = true;
    }

    /* 5. Phased minor collection (replaces single minor_collect call).
     * Split into individual phases so we can insert infix forwarding
     * between promote and update. */

    /* 5a. Cheney BFS: promote reachable minor objects to major heap */
    cheney_promote_phase(gc_gen_heap.minor, gc_gen_heap.major,
                         gc_gen_heap.fp_ref, gc_fwd_arr,
                         root_values, (size_t)root_count);

    /* 5b. Infix forwarding fixup: synthesize forwarding entries for infix
     * sub-objects inside promoted closures. */
    synthesize_infix_forwarding(gc_gen_heap.minor, gc_fwd_arr);

    /* 5c. Rewrite major heap fields: replace minor pointers with forwarded addresses */
    update_all_objects(gc_gen_heap.major, gc_fwd_arr);
    update_scan_base = false;  /* reset for next time */

    /* 5d. Rewrite root array */
    rewrite_roots_impl(root_values, gc_fwd_arr, (size_t)root_count);
    /* 5e. Reset minor heap */
    minor_heap_reset(gc_gen_heap.minor);

    /* 5.5. Ref_table-based pointer rewriting using verified rewrite_heap_slots.
     * Extract field byte-addresses from ref_table entries, then call the
     * verified function to apply forwarding.  This replaces the full major-heap
     * scan that update_all_objects used to do for pre-existing major objects. */
    {
        struct caml_ref_table *tbl = Caml_state->_ref_table;
        size_t n_slots = (size_t)(tbl->ptr - tbl->base);
        if (n_slots > 0) {
            uint64_t *slot_addrs = (uint64_t *)malloc(n_slots * sizeof(uint64_t));
            if (!slot_addrs)
                caml_fatal_error("verified gen GC: cannot allocate slot_addrs");
            size_t k = 0;
            value **r;
            for (r = tbl->base; r < tbl->ptr; r++) {
                uint64_t addr = (uint64_t)(uintptr_t)(*r);
                if (addr < heap_size_u64 && addr % 8 == 0)
                    slot_addrs[k++] = addr;
            }
            if (k > 0)
                rewrite_heap_slots(gc_gen_heap.major, gc_fwd_arr, slot_addrs, k);
            free(slot_addrs);
        }
    }

    /* Tag patching is done INSIDE minor_collect (before update_all_objects)
     * so that no-scan objects (tag >= 251) are correctly skipped. */

    /* 6. Write back rewritten roots to OCaml locations. */
    {
        size_t i;
        for (i = 0; i < root_count; i++) {
            if (root_locs[i] != NULL) {
                uint64_t rewritten = root_values[i];
                if (rewritten != 0) {
                    *root_locs[i] = (value)(uintptr_t)rewritten;
                }
            }
        }
    }

    /* 7. Clear ref_table */
    Caml_state->_ref_table->ptr = Caml_state->_ref_table->base;
}

/* --- Full GC (minor + major) --- */

static void do_full_gc(void) {
    ensure_heap();
    caml_gc_message(0x20, "Verified gen GC: full collection\n");
    Caml_state->_stat_major_collections++;

    /* Phase 1: Minor collection to promote live young objects */
    do_minor_gc();

    /* Phase 2: Major mark-and-sweep */

    /* Allocate gray stack */
    size_t gray_cap = gc_gen_heap.major.size / 64;
    if (gray_cap < 4096) gray_cap = 4096;
    uint64_t *gray_storage = (uint64_t *)calloc(gray_cap, sizeof(uint64_t));
    if (!gray_storage)
        caml_fatal_error("verified gen GC: cannot allocate gray stack");

    size_t gray_top = gray_cap;  /* stack grows downward; cap = empty */
    gray_stack_rec gc_stack;
    gc_stack.storage = gray_storage;
    gc_stack.top = &gray_top;
    gc_stack.cap = gray_cap;

    /* Scan roots again — darken live major objects into gray stack */
    root_count = 0;
    caml_do_roots(scan_minor_root, 1);
    {
        size_t i;
        for (i = 0; i < root_count; i++) {
            uint64_t root = root_values[i];
            /* After minor GC, all roots should be major addresses (absolute) */
            if (root >= zero_addr + 8 && root < heap_size_u64 &&
                root % 8 == 0)
            {
                uint64_t h_addr = root - 8;
                darken_if_white_bounded(gc_gen_heap.major, gc_stack, h_addr);
            }
        }
    }

    /* Run verified mark-and-sweep on major heap */
    uint64_t fp = *gc_gen_heap.fp_ref;
    uint64_t new_fp = collect(gc_gen_heap.major, gc_stack, fp);
    *gc_gen_heap.fp_ref = new_fp;

    free(gray_storage);
}

/* --- Allocation entry point --- */

void *verified_allocate(mlsize_t wosize, uint8_t tag) {
    ensure_heap();

    /* Trigger minor GC when minor heap cannot fit this allocation, BEFORE
     * calling gen_alloc.  Without this, gen_alloc's minor_alloc fails and
     * falls back to the major heap.  Objects allocated on the major heap
     * via Alloc_small_aux have their fields set via Field() (not caml_modify),
     * creating untracked major→minor pointers that our GC can't rewrite. */
    {
        uint64_t bump = *gc_gen_heap.minor.bump_ref;
        uint64_t needed = ((uint64_t)wosize + 1) * 8;
        if ((uint64_t)wosize <= max_young_wosize_u64 && bump + needed > minor_heap_size_u64) {
            do_minor_gc();
        }
    }

    uint64_t result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);

    if (result == 0) {
        /* gen_alloc failed — collect and retry. */
        do_minor_gc();
        result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);
    }

    if (result == 0) {
        /* Major heap also full — full GC and retry */
        do_full_gc();
        result = gen_alloc(gc_gen_heap, (uint64_t)wosize, (uint64_t)tag);
    }

    if (result == 0) {
        caml_fatal_error("verified gen GC: out of memory after collection");
        return NULL;  /* unreachable */
    }

    /* gen_alloc returns the object address (first field = header + 8).
     * OCaml's Alloc_small_aux expects an HP (header pointer).
     * It writes the header at hp[0] and derives val = hp + 8.
     * For minor: result is a minor offset → translate to absolute HP.
     * For major: result is already absolute (NULL-base trick). */
    uint64_t hdr_addr = result - 8;  /* header offset/address */
    if (result < minor_heap_size_u64) {
        /* Minor heap allocation — translate offset to absolute HP */
        return (void *)((uintptr_t)minor_base + (uintptr_t)hdr_addr);
    } else {
        /* Major heap allocation (absolute address with NULL-base) */
        void *ret = (void *)(uintptr_t)hdr_addr;
        /* The verified allocate() sets tag=0; patch in the correct tag. */
        uint8_t *hdr_ptr = (uint8_t *)ret;
        hdr_ptr[0] = tag;  /* tag is in lowest byte of header */
        /* Track high-water mark so update_all_objects only scans used portion */
        uint64_t obj_end = result + (uint64_t)wosize * 8;
        if (obj_end > major_alloc_hwm)
            major_alloc_hwm = obj_end;
        return ret;
    }
}

/* --- OCaml primitive --- */

CAMLprim value caml_trigger_verified_gc(value v) {
    (void)v;
    do_full_gc();
    return Val_unit;
}

/* Called by caml_minor_collection() in minor_gc.c.
 * Some C primitives (e.g., caml_make_vect for large arrays) force a minor
 * collection to promote a young value before using it without write barriers.
 * We must actually run our verified minor GC so that (a) the value gets
 * promoted to major and (b) the ref_table isn't silently cleared. */
void verified_do_minor_gc(void) {
    ensure_heap();
    if (*gc_gen_heap.minor.bump_ref > 0) {
        do_minor_gc();
    }
}
